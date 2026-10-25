//! The pager over the store API (streams-guest-api v9 §14, fork changes
//! 1–5). Only reached when the pager was opened with a [`StreamDb`].
//!
//! - Page buffers are slots of the guest's arena; there is no other source
//!   (change 5). A cache miss first makes a slot free: evict a clean page
//!   (from any connection's cache: they share the arena), else spill dirty
//!   pages into the open transaction's current part, else park until the
//!   next run gives lent slots back.
//! - A slot staged this run is lent to the host until the run ends: it is
//!   never evicted (change 2), and a page that is dirtied while its slot is
//!   lent moves to a fresh slot (copy-on-write) so the host copies the bytes
//!   it was given.
//! - The statement subjournal is the transaction's scratch range: a record
//!   is the page's pre-image staged at `SCRATCH_BASE + i` (it is the old
//!   slot itself; the page continues in a fresh slot), and `index[i]` names
//!   the page (change 4). Savepoint offsets count records.
//! - Savepoint rollback restores the first record of each page from scratch
//!   over later runs; until it is done every page access waits (the gate),
//!   and so does the next `ROLLBACK TO` or `RELEASE`. Grown pages are
//!   discarded from the transaction (change 3).
//! - A rollback that cannot finish, or a staged part the quota refuses,
//!   dooms the transaction: it is aborted on the store at once, every later
//!   access fails, and the statement's abort rolls the connection's
//!   transaction back whole (§14 "A rollback that can't finish aborts the
//!   transaction").
//! - Commit stages the dirty pages that are not already staged (change 1)
//!   and commits the transaction, or writes one plain batch.
//! - Reserve-before-mutate: code that dirties pages first makes sure the
//!   slots, quota, scratch and op credits it will need are there, at a point
//!   where it can still return IO; `add_dirty` itself never waits, and if it
//!   finds no slot it fails SQLITE_FULL (and counts it) rather than use the
//!   heap. Slot reservations are counted over every connection, and the
//!   credits a mutation's records will stage are held from reads and spills.

use super::*;
use crate::storage::stream::{
    self, ReadAt, StreamDb, MAX_PART_PAGES, MAX_READ_PAGES, SCRATCH_BASE,
};
use crate::storage::wal::Wal;

pub(crate) struct StreamPager {
    pub(crate) db: Arc<StreamDb>,
    st: Mutex<StreamPagerState>,
}

#[derive(Default)]
struct StreamPagerState {
    /// Record `i` (scratch page `SCRATCH_BASE + i`) holds this db page.
    index: Vec<u32>,
    /// Slots the current mutation was promised (see `stream_reserve`); also
    /// counted in the database's total over every connection.
    reserved: u32,
    restore: Option<Restore>,
    /// The transaction is aborted on the store; the connection must roll
    /// it back (see `stream_doom`).
    doomed: Option<Doom>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Doom {
    Full,
    Io,
}

impl Doom {
    fn of(e: &LimboError) -> Self {
        match e {
            LimboError::DatabaseFull => Doom::Full,
            _ => Doom::Io,
        }
    }

    fn error(self) -> LimboError {
        match self {
            Doom::Full => stream::full(),
            Doom::Io => LimboError::CompletionError(CompletionError::IOError(
                std::io::ErrorKind::Other,
                "stream transaction aborted",
            )),
        }
    }
}

/// A savepoint rollback still restoring pre-images (§14 RollbackState).
struct Restore {
    /// (db page, record) for the first record of each page, in order.
    todo: Vec<(u32, u32)>,
    next: usize,
    inflight: Vec<Completion>,
}

impl StreamPager {
    pub(crate) fn new(db: Arc<StreamDb>) -> Self {
        Self {
            db,
            st: Mutex::new(StreamPagerState::default()),
        }
    }
}

impl Drop for StreamPager {
    fn drop(&mut self) {
        // A connection closed mid-mutation gives its slots back.
        let reserved = self.st.lock().reserved;
        self.db.move_reserved(reserved, 0);
    }
}

impl Pager {
    pub(crate) fn set_stream(&mut self, db: Arc<StreamDb>) {
        db.register_cache(&self.page_cache);
        self.stream = Some(StreamPager::new(db));
    }

    pub fn stream_db(&self) -> Option<&Arc<StreamDb>> {
        self.stream.as_ref().map(|s| &s.db)
    }

    #[inline]
    pub(crate) fn is_stream(&self) -> bool {
        self.stream.is_some()
    }

    fn sp(&self) -> &StreamPager {
        self.stream.as_ref().expect("stream pager")
    }

    /// The stream transaction was aborted under this connection: its
    /// statement's abort must roll the whole transaction back.
    pub fn stream_doomed(&self) -> bool {
        self.stream
            .as_ref()
            .is_some_and(|s| s.st.lock().doomed.is_some())
    }

    fn doomed_error(&self) -> Option<LimboError> {
        self.sp().st.lock().doomed.map(Doom::error)
    }

    /// Give up the transaction (§14): abort it on the store now, so the
    /// stream holds no part of it, and fail everything until the connection
    /// rolls back. Returns `e` for the caller to raise.
    fn stream_doom(&self, e: LimboError) -> LimboError {
        let db = &self.sp().db;
        {
            let mut st = self.sp().st.lock();
            if st.doomed.is_none() {
                st.doomed = Some(Doom::of(&e));
                st.restore = None;
                db.bump(|s| s.doomed += 1);
            }
        }
        db.txn_abort();
        self.stream_set_reserved(0);
        db.set_hold(0);
        e
    }

    fn stream_set_reserved(&self, n: u32) {
        let mut st = self.sp().st.lock();
        let old = st.reserved;
        st.reserved = n;
        self.sp().db.move_reserved(old, n);
    }

    /// Would `add_dirty(page)` write a subjournal record?
    fn stream_record_needed(&self, page: &Page) -> bool {
        if self.subjournal.read().is_none() {
            return false;
        }
        let savepoints = self.savepoints.read();
        let Some(sp) = savepoints.last() else {
            return false;
        };
        let id = page.get().id() as u32;
        id <= sp.db_size.load(Ordering::Acquire) && !sp.has_dirty_page(id)
    }

    /// (fresh slots, records) `add_dirty(page)` takes.
    pub(crate) fn stream_need(&self, page: &Page) -> (u32, u32) {
        let rec = self.stream_record_needed(page);
        let cow = rec || page.buffer_lent();
        (u32::from(cow), u32::from(rec))
    }

    fn records_used(&self) -> u32 {
        self.savepoints
            .read()
            .last()
            .map_or(0, |sp| sp.write_offset() as u32)
    }

    fn has_savepoint(&self) -> bool {
        self.subjournal.read().is_some() && !self.savepoints.read().is_empty()
    }

    /// The page size and reserved bytes of a stream database. Both are set
    /// when the pager is created (or at page-1 init); unset is a fork bug,
    /// not a reason to guess.
    pub(crate) fn stream_usable_space(&self) -> Result<usize> {
        // A stream database has one page size.
        let page_size = self
            .get_page_size()
            .map_or(stream::PAGE_SIZE, |s| s.get() as usize);
        if page_size != stream::PAGE_SIZE {
            return Err(LimboError::InternalError(format!(
                "stream: page size {page_size}, the store's is {}",
                stream::PAGE_SIZE
            )));
        }
        let reserved = match self.get_reserved_space() {
            Some(r) => r,
            None if !self.db_initialized() => self.io_ctx.read().get_reserved_space_bytes(),
            None => {
                // Byte 20 of a resident page 1; no IO here.
                let r = self
                    .page_cache
                    .write()
                    .peek(&PageCacheKey::new(DatabaseHeader::PAGE_ID), false)
                    .filter(|p| p.is_loaded())
                    .and_then(|p| p.get().buffer().map(|b| b.as_slice()[20]))
                    .ok_or_else(|| {
                        LimboError::InternalError(
                            "stream: reserved space unknown and page 1 not resident".into(),
                        )
                    })?;
                self.set_reserved_space(r);
                r
            }
        };
        Ok(page_size - reserved as usize)
    }

    /// `R = 5 * depth + overflow + 2` (§14 change 4): the pages one b-tree
    /// operation can newly dirty. `depth` comes from the database size in
    /// the cached page 1 (no IO here); with page 1 not resident it assumes
    /// twice the last size seen, or a 2^32-page database.
    pub fn stream_op_slots(&self, payload: usize) -> Result<u32> {
        let db_size = self
            .page_cache
            .write()
            .peek(&PageCacheKey::new(DatabaseHeader::PAGE_ID), false)
            .filter(|p| p.is_loaded())
            .and_then(|p| {
                let inner = p.get();
                let buf = inner.buffer()?;
                let b = buf.as_slice();
                Some(u32::from_be_bytes([b[28], b[29], b[30], b[31]]))
            })
            .inspect(|&n| self.sp().db.set_size_hint(n));
        // Page 1 not resident: the size another reserve saw (an upper
        // bound is what matters, and a write grows it by at most R).
        let db_size = db_size
            .or_else(|| {
                Some(self.sp().db.size_hint())
                    .filter(|&n| n > 0)
                    .map(|n| n.saturating_mul(2))
            })
            .unwrap_or(u32::MAX)
            .max(4);
        // Interior fan-out is at least 4: depth <= log4(pages) + 2.
        let depth = (32 - (db_size - 1).leading_zeros()).div_ceil(2) + 2;
        let usable = self.stream_usable_space()?;
        let overflow = if payload == 0 {
            0
        } else {
            payload / (usable - 4) + 1
        };
        Ok((5 * depth).saturating_add(u32::try_from(overflow).unwrap_or(u32::MAX)) + 2)
    }

    /// Reserve for one b-tree mutation opcode (Insert, Delete, IdxInsert,
    /// IdxDelete): `slots` fresh slots, and as many records if a savepoint
    /// is open. Replaces any earlier reserve.
    pub fn stream_reserve_op(&self, slots: u32) -> IOResultOr<()> {
        if self.stream.is_none() {
            return Ok(IOResult::Done(()));
        }
        self.stream_set_reserved(0);
        self.sp().db.set_hold(0);
        let records = if self.has_savepoint() { slots } else { 0 };
        self.stream_reserve(slots, records)
    }

    /// The statement ended: its reservation (slots and held credits) is
    /// over. Reserves are an upper bound, so some are always left.
    pub(crate) fn stream_end_statement(&self) {
        if self.stream.is_some() {
            self.stream_set_reserved(0);
            self.sp().db.set_hold(0);
        }
    }

    /// Make sure `slots` fresh slots are free, `records` subjournal records
    /// fit (scratch and quota) and the credits that staging them takes are
    /// held. Scratch or quota short: SQLITE_FULL now, before anything is
    /// mutated. Slots or credits short: evict, spill or park.
    pub(crate) fn stream_reserve(&self, slots: u32, records: u32) -> IOResultOr<()> {
        return_if_io!(self.stream_gate());
        let db = self.sp().db.clone();
        if records > 0 {
            if self.records_used() + records > db.config().scratch_pages {
                db.bump(|s| {
                    s.scratch_full += 1;
                    s.reserve_full += 1;
                });
                return Err(stream::full().into());
            }
            if db.quota_left() < records as u64 {
                db.bump(|s| {
                    s.quota_full += 1;
                    s.reserve_full += 1;
                });
                return Err(stream::full().into());
            }
        }
        let want = slots.max(self.sp().st.lock().reserved);
        return_if_io!(self.stream_ensure_slots(want));
        self.stream_set_reserved(want);
        if records > 0 {
            // BEGIN, and the closing op of each part the records open.
            let need = db.hold_credits(records as u64);
            if db.credits() < need {
                io_yield_one!(db.park());
            }
            db.raise_hold(need);
        }
        Ok(IOResult::Done(()))
    }

    /// Reserve what `add_dirty(page)` needs (F5: re-checked after every
    /// yield, right before the `add_dirty`).
    pub(crate) fn stream_check_page(&self, page: &Page) -> IOResultOr<()> {
        if self.stream.is_none() {
            return Ok(IOResult::Done(()));
        }
        let (slots, records) = self.stream_need(page);
        if slots == 0 {
            return Ok(IOResult::Done(()));
        }
        self.stream_reserve(slots, records)
    }

    /// One fresh slot of the reserve was used.
    fn stream_take_reserved(&self) {
        let r = self.sp().st.lock().reserved;
        if r > 0 {
            self.stream_set_reserved(r - 1);
        }
    }

    /// At least `n` free slots for this connection on top of what the other
    /// connections were promised, or IO (parked until the next run), or
    /// SQLITE_FULL when nothing can ever come back.
    pub(crate) fn stream_ensure_slots(&self, n: u32) -> IOResultOr<()> {
        let db = self.sp().db.clone();
        let pool = db.pool().clone();
        let (total, free, _) = pool.page_slots();
        let own = self.sp().st.lock().reserved;
        let others = db.reserved_slots().saturating_sub(own);
        let want = n.saturating_add(others);
        if free >= want {
            return Ok(IOResult::Done(()));
        }
        if n > total {
            db.bump(|s| s.reserve_full += 1);
            return Err(stream::full().into());
        }
        {
            let mut cache = self.page_cache.write();
            while pool.page_slots().1 < want && cache.evict_one_page() {
                db.bump(|s| s.evictions += 1);
            }
        }
        if pool.page_slots().1 >= want {
            return Ok(IOResult::Done(()));
        }
        db.evict_others(&self.page_cache, want);
        if pool.page_slots().1 >= want {
            return Ok(IOResult::Done(()));
        }
        let spilled = self.stream_spill()?;
        let (_, free, lent) = pool.page_slots();
        if free >= want {
            return Ok(IOResult::Done(()));
        }
        // Lent slots come back at the end of the run; another connection's
        // reservation ends with its statement.
        if lent > 0 || spilled > 0 || others > 0 {
            io_yield_one!(db.park());
        }
        db.bump(|s| s.reserve_full += 1);
        Err(stream::full().into())
    }

    /// Stage dirty pages into the open transaction (opening it), marking
    /// them spilled: their slots are lent until the run ends, then they are
    /// evictable. Returns pages staged. A page the quota refuses dooms the
    /// transaction (a `Full` at `part`, §14).
    fn stream_stage_spilled(&self, pages: &[PageRef]) -> Result<u32> {
        let db = &self.sp().db;
        let mut n = 0;
        for page in pages {
            let Some(buf) = page.get().buffer().cloned() else {
                continue;
            };
            let id = page.get().id() as u64;
            match db.stage_write(id - 1, &buf) {
                Ok(true) => {}
                Ok(false) => return Err(self.stream_doom(stream::full())),
                Err(e) => return Err(self.stream_doom(e)),
            }
            page.set_spilled();
            self.page_cache
                .write()
                .notify_page_spilled(PageCacheKey::new(id as usize));
            n += 1;
        }
        Ok(n)
    }

    /// Spill what the free credits (past the hold) allow, at most one part.
    /// No subjournal record is written at spill: records are taken at
    /// `add_dirty`, before the page changes, and a staged part is only ever
    /// overwritten by a later one, never rewound.
    fn stream_spill(&self) -> Result<u32> {
        let db = &self.sp().db;
        let room = db
            .writes_within(db.free_credits())
            .min(MAX_PART_PAGES as u64) as usize;
        if room == 0 {
            return Ok(0);
        }
        let pages: Vec<PageRef> = self
            .page_cache
            .read()
            .spillable_pages(room)
            .into_iter()
            .map(|g| g.to_page())
            .collect();
        let n = self.stream_stage_spilled(&pages)?;
        db.bump(|s| s.spilled_pages += n as u64);
        Ok(n)
    }

    /// Before a cache miss: no restore pending, credits for the read (and a
    /// pin) past the hold, a slot for it on top of every reservation.
    pub(super) fn stream_before_miss(&self) -> IOResultOr<()> {
        return_if_io!(self.stream_gate());
        let db = &self.sp().db;
        if db.free_credits() < 2 {
            io_yield_one!(db.park());
        }
        let reserved = self.sp().st.lock().reserved;
        self.stream_ensure_slots(1 + reserved)
    }

    /// `add_dirty` in stream mode, before the page is marked dirty: write
    /// the record if one is due and move the page off a lent or recorded
    /// slot. Never waits.
    pub(super) fn stream_prepare_dirty(&self, page: &Page) -> Result<()> {
        if let Some(e) = self.doomed_error() {
            return Err(e);
        }
        let (cow, rec) = self.stream_need(page);
        if cow == 0 {
            return Ok(());
        }
        let db = self.sp().db.clone();
        let mut rec_at = None;
        if rec == 1 {
            let i = self.records_used();
            if i >= db.config().scratch_pages {
                db.bump(|s| s.scratch_full += 1);
                return Err(stream::full());
            }
            if db.quota_left() == 0 {
                db.bump(|s| s.quota_full += 1);
                return Err(stream::full());
            }
            rec_at = Some(i);
        }
        let Some(fresh) = db.pool().try_get_page() else {
            // Reserve-before-mutate should have made room. Never fall back
            // to the heap (§14 add_dirty hard rule).
            db.bump(|s| s.hard_rule_full += 1);
            return Err(stream::full());
        };
        let inner = page.get();
        let old = inner.take_buffer().expect("add_dirty on a loaded page");
        fresh.as_mut_slice().copy_from_slice(old.as_slice());
        inner.set_buffer(Arc::new(fresh));
        db.bump(|s| s.cow_pages += 1);
        let id = page.get().id() as u32;
        if let Some(i) = rec_at {
            // The old slot is the pre-image: stage it as record i.
            match db.stage_write(SCRATCH_BASE + i as u64, &old) {
                Ok(true) => {}
                Ok(false) => return Err(self.stream_doom(stream::full())),
                Err(e) => return Err(self.stream_doom(e)),
            }
            {
                let mut st = self.sp().st.lock();
                st.index.truncate(i as usize);
                st.index.push(id);
            }
            let savepoints = self.savepoints.read();
            let sp = savepoints.last().expect("a record implies a savepoint");
            sp.add_dirty_page(id);
            sp.write_offset.fetch_add(1, Ordering::SeqCst);
            db.bump(|s| s.records += 1);
        } else {
            // Keep the old bytes alive until the run ends: the host is
            // copying them, and code that read the page before this call
            // may still look at them.
            db.keep(old);
        }
        self.stream_take_reserved();
        Ok(())
    }

    /// A fresh page buffer for a new page (`allocate_new_page`).
    pub(super) fn stream_new_buffer(&self) -> Result<Buffer> {
        let db = &self.sp().db;
        match db.pool().try_get_page() {
            Some(b) => {
                self.stream_take_reserved();
                Ok(b)
            }
            None => {
                db.bump(|s| s.hard_rule_full += 1);
                Err(stream::full())
            }
        }
    }

    /// Wait for a pending savepoint restore. A restore that fails dooms the
    /// transaction.
    pub(crate) fn stream_gate(&self) -> IOResultOr<()> {
        let Some(sp) = &self.stream else {
            return Ok(IOResult::Done(()));
        };
        if let Some(e) = self.doomed_error() {
            return Err(e.into());
        }
        let Some(mut r) = sp.st.lock().restore.take() else {
            return Ok(IOResult::Done(()));
        };
        match self.stream_drive_restore(&mut r) {
            Ok(IOResult::Done(())) => Ok(IOResult::Done(())),
            Ok(IOResult::IO(c)) => {
                sp.st.lock().restore = Some(r);
                Ok(IOResult::IO(c))
            }
            Err(e) => Err(self.stream_doom(*e).into()),
        }
    }

    fn stream_drive_restore(&self, r: &mut Restore) -> IOResultOr<()> {
        let db = self.sp().db.clone();
        for c in &r.inflight {
            if let Some(e) = c.get_error() {
                return Err(LimboError::from(e).into());
            }
        }
        r.inflight.retain(|c| !c.finished());
        while r.next < r.todo.len() && r.inflight.len() < MAX_READ_PAGES {
            if db.free_credits() < 1 {
                break;
            }
            match self.stream_ensure_slots(1)? {
                IOResult::Done(()) => {}
                IOResult::IO(c) => {
                    if r.inflight.is_empty() {
                        return Ok(IOResult::IO(c));
                    }
                    break;
                }
            }
            let (id, rec) = r.todo[r.next];
            let buf = Arc::new(db.pool().try_get_page().ok_or_else(stream::full)?);
            let page = Arc::new(Page::new(id as i64));
            page.set_locked();
            let c = stream::page_read_completion(page.clone(), id as usize, buf.clone());
            let Some(c) = db.read(ReadAt::Latest, SCRATCH_BASE + rec as u64, &buf, c)? else {
                // Checked above; the hold cannot have grown since.
                page.clear_locked();
                break;
            };
            page.set_dirty();
            self.dirty_pages.write().insert(id);
            self.page_cache
                .write()
                .force_upsert_page(PageCacheKey::new(id as usize), page)
                .map_err(|e| LimboError::InternalError(format!("restore page {id}: {e:?}")))?;
            r.inflight.push(c);
            r.next += 1;
            db.bump(|s| s.restored_pages += 1);
        }
        // Wait on the run's notify, not on a restore read itself: the step
        // loop raises a failed completion it waited on before calling back
        // in, and a restore read's failure must reach this gate (it dooms
        // the transaction), not end just the statement.
        if r.next < r.todo.len() || r.inflight.iter().any(|c| !c.finished()) {
            io_yield_one!(db.park());
        }
        for c in &r.inflight {
            if let Some(e) = c.get_error() {
                return Err(LimboError::from(e).into());
            }
        }
        Ok(IOResult::Done(()))
    }

    /// `rollback_to_snapshot` in stream mode (fork change 3).
    pub(super) fn stream_rollback_to_snapshot(
        &self,
        savepoint: &SavepointSnapshot,
        end: u64,
    ) -> Result<()> {
        self.reset_internal_states();
        let db = self.sp().db.clone();
        // A mutation that was going on is over.
        self.stream_set_reserved(0);
        db.set_hold(0);
        if self.doomed_error().is_some() {
            // The transaction is gone; its rollback restores nothing.
            return Ok(());
        }
        let db_size = savepoint.db_size;
        let start = savepoint.start_offset as usize;
        let end = end as usize;
        // This savepoint's records are the source of truth: the first
        // record of a page at or after `start` is its image when the
        // savepoint was taken.
        let mut seen = RoaringBitmap::new();
        let mut todo = Vec::new();
        {
            let st = self.sp().st.lock();
            for i in start..end.min(st.index.len()) {
                let id = st.index[i];
                if id > db_size || !seen.insert(id) {
                    continue;
                }
                todo.push((id, i as u32));
            }
        }
        // A restore still pending (a nested savepoint's, when no gate ran
        // in between: a statement rollback at Halt) keeps the pages this
        // range does not cover. Such a page was not changed between this
        // savepoint and the nested one (it has no record here), so the
        // nested image is this savepoint's image too. A page this range
        // does cover is restored again from this range's record, which
        // supersedes the nested one whether or not that one landed.
        let earlier = self.sp().st.lock().restore.take();
        let mut inflight = Vec::new();
        if let Some(e) = earlier {
            for &(id, rec) in &e.todo[e.next..] {
                if id <= db_size && seen.insert(id) {
                    todo.push((id, rec));
                }
            }
            inflight = e.inflight;
        }
        // Shrink: pages past the savepoint's size go away.
        {
            let mut dirty_pages = self.dirty_pages.write();
            let mut cache = self.page_cache.write();
            for page_id in dirty_pages.iter().filter(|&id| id > db_size) {
                if let Some(page) = cache.peek(&PageCacheKey::new(page_id as usize), false) {
                    page.clear_dirty();
                    page.try_unpin();
                }
            }
            dirty_pages.remove_range((db_size + 1)..);
            cache.truncate(db_size as usize)?;
            // Pages being restored: drop the current versions now so nothing
            // reads them before the restore lands.
            for &(id, _) in &todo {
                if let Some(page) = cache.peek(&PageCacheKey::new(id as usize), false) {
                    if page.get().id() != DatabaseHeader::PAGE_ID {
                        page.clear_dirty();
                    }
                }
            }
        }
        // Rewind: grown pages that were spilled must not be committed.
        if db.txn_open() {
            db.stage_discard(db_size as u64, SCRATCH_BASE);
        }
        if !todo.is_empty() || !inflight.is_empty() {
            self.sp().st.lock().restore = Some(Restore {
                todo,
                next: 0,
                inflight,
            });
        }
        self.invalidate_all_cursors();
        Ok(())
    }

    /// Records past `len` are gone (a savepoint was released at the root or
    /// the transaction ended).
    pub(super) fn stream_truncate_records(&self, len: usize) {
        if let Some(sp) = &self.stream {
            sp.st.lock().index.truncate(len);
        }
    }

    /// Commit (fork change 1): stage the dirty pages not already staged, then
    /// commit the transaction, or write one plain batch when nothing was
    /// staged before. It waits, before touching anything, for a pending
    /// restore or for credits; when a run's credits cannot cover every part,
    /// it stages what they do cover (as a spill) and finishes in a later run.
    pub(super) fn stream_commit(&self) -> IOResultOr<()> {
        return_if_io!(self.stream_gate());
        let db = self.sp().db.clone();
        db.set_hold(0);
        let mut pages = Vec::new();
        {
            let dirty = self.dirty_pages.read();
            let mut cache = self.page_cache.write();
            for id in dirty.iter() {
                // Not resident, or resident and spilled: its current bytes
                // are already in a staged part.
                if let Some(page) = cache.peek(&PageCacheKey::new(id as usize), false) {
                    if page.is_dirty() && !page.is_spilled() {
                        pages.push(page);
                    }
                }
            }
        }
        let txn = db.txn_open();
        if pages.is_empty() && !txn {
            self.stream_after_commit();
            return Ok(IOResult::Done(()));
        }
        if !txn && pages.len() <= MAX_PART_PAGES as usize {
            // One plain batch: one credit, quota for every page. Checked
            // first, so a refusal changes nothing.
            if db.credits() < 1 {
                io_yield_one!(db.park());
            }
            if db.quota_left() < pages.len() as u64 {
                db.bump(|s| s.quota_full += 1);
                return Err(stream::full().into());
            }
            for page in &pages {
                let buf = page.get().buffer().cloned().expect("dirty page is loaded");
                if !db.batch_write(page.get().id() as u64 - 1, &buf)? {
                    db.batch_cancel();
                    return Err(stream::full().into());
                }
            }
            db.batch_commit()?;
        } else {
            let fresh = db.fresh_pages(pages.iter().map(|p| p.get().id() as u64 - 1));
            if db.quota_left() < fresh {
                db.bump(|s| s.quota_full += 1);
                if txn {
                    // Parts are already staged: give the transaction up.
                    return Err(self.stream_doom(stream::full()).into());
                }
                return Err(stream::full().into());
            }
            // Every page, the scratch discard, and COMMIT's own credit if the
            // last part ends exactly full.
            let need = db.stage_credits(pages.len() as u64 + 1) + 1;
            if db.credits() < need {
                let room = (db.writes_within(db.credits()) as usize).min(pages.len());
                if room > 0 {
                    self.stream_stage_spilled(&pages[..room])?;
                }
                io_yield_one!(db.park());
            }
            for page in &pages {
                let buf = page.get().buffer().cloned().expect("dirty page is loaded");
                match db.stage_write(page.get().id() as u64 - 1, &buf) {
                    Ok(true) => {}
                    Ok(false) => return Err(self.stream_doom(stream::full()).into()),
                    Err(e) => return Err(self.stream_doom(e).into()),
                }
            }
            let scratch = db.config().scratch_pages as u64;
            db.stage_discard(SCRATCH_BASE, SCRATCH_BASE + scratch);
            if let Err(e) = db.txn_commit() {
                return Err(self.stream_doom(e).into());
            }
        }
        {
            let mut cache = self.page_cache.write();
            for id in self.dirty_pages.read().iter() {
                if let Some(page) = cache.peek(&PageCacheKey::new(id as usize), false) {
                    page.clear_dirty();
                    page.clear_spilled();
                }
            }
        }
        self.dirty_pages.write().clear();
        self.stream_after_commit();
        Ok(IOResult::Done(()))
    }

    fn stream_after_commit(&self) {
        {
            let mut st = self.sp().st.lock();
            st.index.clear();
            st.restore = None;
        }
        self.stream_set_reserved(0);
        self.sp().db.set_hold(0);
    }

    /// The write transaction rolled back (whole).
    pub(super) fn stream_on_rollback(&self) {
        if let Some(sp) = &self.stream {
            {
                let mut st = sp.st.lock();
                st.index.clear();
                st.restore = None;
                st.doomed = None;
            }
            self.stream_set_reserved(0);
            sp.db.set_hold(0);
        }
    }

    /// Before page-1 init on an empty stream (`allocate_page1` at Start):
    /// the BATCH's credit and one page of quota, so the write can't fail.
    pub(super) fn stream_page1_ready(&self) -> IOResultOr<()> {
        let db = &self.sp().db;
        if db.free_credits() < 1 {
            io_yield_one!(db.park());
        }
        if db.quota_left() < 1 {
            db.bump(|s| s.quota_full += 1);
            return Err(stream::full().into());
        }
        Ok(IOResult::Done(()))
    }

    /// Page 1 of a new database: written as its own batch (version 1),
    /// which is what a fresh SQLite file write of page 1 is.
    pub(super) fn stream_write_page1(&self, page: &PageRef) -> Result<()> {
        let db = &self.sp().db;
        let buf = page.get().buffer().cloned().expect("page 1 is loaded");
        if !db.batch_write(0, &buf)? {
            db.batch_cancel();
            return Err(stream::full());
        }
        db.batch_commit()?;
        Ok(())
    }

    /// `cache_insert` in stream mode. The slot was made free before the
    /// read, so the cache never decides capacity, the arena does. The page
    /// must not already be cached as a different object: two `Page`s for
    /// one page id would let a write land on the one the cache doesn't
    /// hold.
    pub(super) fn stream_cache_insert(&self, page_idx: usize, page: PageRef) -> Result<()> {
        let mut cache = self.page_cache.write();
        let key = PageCacheKey::new(page_idx);
        if let Some(cached) = cache.peek(&key, false) {
            if Arc::ptr_eq(&cached, &page) {
                return Ok(());
            }
            // A failed read (unloaded, unlocked) is replaced below; any
            // other page is live.
            if cached.is_loaded() || cached.is_locked() {
                return Err(LimboError::InternalError(format!(
                    "stream: page {page_idx} is already cached as another page"
                )));
            }
        }
        match cache.force_insert_page(key, page) {
            Ok(_) | Err(CacheError::KeyExists) => Ok(()),
            Err(e) => Err(LimboError::from(e)),
        }
    }

    /// A cached page whose stream read failed (unloaded, not locked):
    /// drop it so the next access reads again instead of waiting forever.
    pub(super) fn stream_drop_failed_read(&self, page: &PageRef) -> bool {
        if page.is_loaded() || page.is_locked() {
            return false;
        }
        let key = PageCacheKey::new(page.get().id());
        self.page_cache.write().delete(key).is_ok()
    }

    /// Test hook: `free_page`'s state, as a name.
    #[cfg(test)]
    pub(crate) fn stream_test_free_page_state(&self) -> &'static str {
        match &*self.free_page_state.read() {
            FreePageState::Start => "Start",
            FreePageState::AddToTrunk { .. } => "AddToTrunk",
            FreePageState::NewTrunk { .. } => "NewTrunk",
        }
    }

    /// Test hook: is page `id` resident and loaded?
    #[cfg(test)]
    pub(crate) fn stream_test_loaded(&self, id: usize) -> bool {
        self.page_cache
            .write()
            .peek(&PageCacheKey::new(id), false)
            .is_some_and(|p| p.is_loaded())
    }

    /// Test hook: what "another statement in the run took the slots" looks
    /// like: evict every evictable page except `keep`, then lend every free
    /// slot until the run ends. Returns the slots taken.
    #[cfg(test)]
    pub(crate) fn stream_test_squeeze(&self, keep: Option<usize>) -> u32 {
        {
            let kept =
                keep.and_then(|id| self.page_cache.write().peek(&PageCacheKey::new(id), false));
            if let Some(p) = &kept {
                p.pin();
            }
            // What eviction can take (not page 1, pinned, locked, lent, or
            // pages a state machine still holds).
            let mut cache = self.page_cache.write();
            while cache.evict_one_page() {}
            if let Some(p) = &kept {
                p.unpin();
            }
        }
        let db = self.sp().db.clone();
        let mut n = 0;
        while let Some(b) = db.pool().try_get_page() {
            db.keep(Arc::new(b));
            n += 1;
        }
        n
    }

    /// Test hook: the cached page `id`.
    #[cfg(test)]
    pub(crate) fn stream_test_cached(&self, id: usize) -> Option<PageRef> {
        self.page_cache.write().peek(&PageCacheKey::new(id), false)
    }

    /// Test hook: `cache_insert` in stream mode.
    #[cfg(test)]
    pub(crate) fn stream_test_cache_insert(&self, id: usize, page: PageRef) -> Result<()> {
        self.stream_cache_insert(id, page)
    }

    #[cfg(any(test, feature = "test_helper"))]
    pub fn stream_records(&self) -> usize {
        self.stream.as_ref().map_or(0, |s| s.st.lock().index.len())
    }

    /// The WAL as a `StreamWal`, for the open path.
    #[allow(dead_code)]
    pub(crate) fn stream_wal(&self) -> Option<&Arc<dyn Wal>> {
        self.wal.as_ref()
    }
}
