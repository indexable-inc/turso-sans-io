//! The pager over the store API (streams-guest-api v9 §14, fork changes
//! 1–5). Only reached when the pager was opened with a [`StreamDb`].
//!
//! - Page buffers are slots of the guest's arena; there is no other source
//!   (change 5). A cache miss first makes a slot free: evict a clean page,
//!   else spill dirty pages into the open transaction's current part, else
//!   park until the next run gives lent slots back.
//! - A slot staged this run is lent to the host until the run ends: it is
//!   never evicted (change 2), and a page that is dirtied while its slot is
//!   lent moves to a fresh slot (copy-on-write) so the host copies the bytes
//!   it was given.
//! - The statement subjournal is the transaction's scratch range: a record
//!   is the page's pre-image staged at `SCRATCH_BASE + i` (it is the old
//!   slot itself; the page continues in a fresh slot), and `index[i]` names
//!   the page (change 4). Savepoint offsets count records.
//! - Savepoint rollback restores the first record of each page from scratch
//!   over later runs; until it is done every page access waits (the gate).
//!   Grown pages are discarded from the transaction (change 3).
//! - Commit stages the dirty pages that are not already staged (change 1)
//!   and commits the transaction, or writes one plain batch.
//! - Reserve-before-mutate: code that dirties pages first makes sure the
//!   slots, quota and scratch it will need are there, at a point where it
//!   can still return IO; `add_dirty` itself never waits, and if it finds no
//!   slot it fails SQLITE_FULL (and counts it) rather than use the heap.

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
    /// Slots the current mutation was promised (see `stream_reserve`).
    reserved: u32,
    restore: Option<Restore>,
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

impl Pager {
    pub(crate) fn set_stream(&mut self, db: Arc<StreamDb>) {
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

    /// `R = 5 * depth + overflow + 2` (§14 change 4): the pages one b-tree
    /// operation can newly dirty. `depth` comes from the database size in
    /// the cached page 1 (no IO here); with page 1 not resident it assumes
    /// a 2^32-page database.
    pub fn stream_op_slots(&self, payload: usize) -> u32 {
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
        let usable = self
            .get_page_size()
            .map_or(stream::PAGE_SIZE, |s| s.get() as usize)
            - self.get_reserved_space().unwrap_or(0) as usize;
        let overflow = if payload == 0 {
            0
        } else {
            payload / (usable - 4) + 1
        };
        5 * depth + overflow as u32 + 2
    }

    /// Reserve for one b-tree mutation opcode (Insert, Delete, IdxInsert,
    /// IdxDelete): `slots` fresh slots, and as many records if a savepoint
    /// is open. Replaces any earlier reserve.
    pub fn stream_reserve_op(&self, slots: u32) -> IOResultOr<()> {
        if self.stream.is_none() {
            return Ok(IOResult::Done(()));
        }
        self.sp().st.lock().reserved = 0;
        let records = if self.has_savepoint() { slots } else { 0 };
        self.stream_reserve(slots, records)
    }

    /// Make sure `slots` fresh slots are free and `records` subjournal
    /// records fit (scratch and quota). Scratch or quota short: SQLITE_FULL
    /// now, before anything is mutated. Slots short: evict, spill or park.
    pub(crate) fn stream_reserve(&self, slots: u32, records: u32) -> IOResultOr<()> {
        return_if_io!(self.stream_gate());
        let db = &self.sp().db;
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
        self.sp().st.lock().reserved = want;
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
        let mut st = self.sp().st.lock();
        st.reserved = st.reserved.saturating_sub(1);
    }

    /// At least `n` free slots, or IO (parked until the next run), or
    /// SQLITE_FULL when nothing can ever come back.
    pub(crate) fn stream_ensure_slots(&self, n: u32) -> IOResultOr<()> {
        let db = self.sp().db.clone();
        let pool = db.pool().clone();
        let (total, free, _) = pool.page_slots();
        if free >= n {
            return Ok(IOResult::Done(()));
        }
        if n > total {
            db.bump(|s| s.reserve_full += 1);
            return Err(stream::full().into());
        }
        {
            let mut cache = self.page_cache.write();
            while pool.page_slots().1 < n && cache.evict_one_page() {
                db.bump(|s| s.evictions += 1);
            }
        }
        if pool.page_slots().1 >= n {
            return Ok(IOResult::Done(()));
        }
        let spilled = self.stream_spill()?;
        let (_, free, lent) = pool.page_slots();
        if free >= n {
            return Ok(IOResult::Done(()));
        }
        if lent > 0 || spilled > 0 {
            io_yield_one!(db.park());
        }
        db.bump(|s| s.reserve_full += 1);
        Err(stream::full().into())
    }

    /// Stage spillable dirty pages into the open transaction (opening it).
    /// Their slots are lent until the run ends; then they are evictable.
    /// No subjournal record is written at spill: records are taken at
    /// `add_dirty`, before the page changes, and a staged part is only ever
    /// overwritten by a later one, never rewound.
    fn stream_spill(&self) -> Result<u32> {
        let db = &self.sp().db;
        if db.credits() < 2 {
            return Ok(0);
        }
        let pages = self
            .page_cache
            .read()
            .spillable_pages(MAX_PART_PAGES as usize);
        let mut n = 0;
        for guard in pages {
            let page = guard.to_page();
            let Some(buf) = page.get().buffer().cloned() else {
                continue;
            };
            let id = page.get().id() as u64;
            if !db.stage_write(id - 1, &buf)? {
                return Err(stream::full());
            }
            page.set_spilled();
            self.page_cache
                .write()
                .notify_page_spilled(PageCacheKey::new(id as usize));
            n += 1;
        }
        db.bump(|s| s.spilled_pages += n as u64);
        Ok(n)
    }

    /// Before a cache miss: no restore pending, a credit for the read, a
    /// slot for it on top of the reserve.
    pub(super) fn stream_before_miss(&self) -> IOResultOr<()> {
        return_if_io!(self.stream_gate());
        let db = &self.sp().db;
        if db.credits() < 3 {
            io_yield_one!(db.park());
        }
        let reserved = self.sp().st.lock().reserved;
        self.stream_ensure_slots(1 + reserved)
    }

    /// `add_dirty` in stream mode, before the page is marked dirty: write
    /// the record if one is due and move the page off a lent or recorded
    /// slot. Never waits.
    pub(super) fn stream_prepare_dirty(&self, page: &Page) -> Result<()> {
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
            if !db.stage_write(SCRATCH_BASE + i as u64, &old)? {
                return Err(stream::full());
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

    /// Wait for a pending savepoint restore.
    pub(crate) fn stream_gate(&self) -> IOResultOr<()> {
        let Some(sp) = &self.stream else {
            return Ok(IOResult::Done(()));
        };
        let Some(mut r) = sp.st.lock().restore.take() else {
            return Ok(IOResult::Done(()));
        };
        let res = self.stream_drive_restore(&mut r);
        match res {
            Ok(IOResult::Done(())) => Ok(IOResult::Done(())),
            other => {
                sp.st.lock().restore = Some(r);
                other
            }
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
            if db.credits() < 2 {
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
            let c = db
                .read(ReadAt::Latest, SCRATCH_BASE + rec as u64, &buf, c)?
                .expect("a credit was checked above");
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
        if let Some(c) = r.inflight.iter().find(|c| !c.finished()) {
            io_yield_one!(c.clone());
        }
        if r.next < r.todo.len() {
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
        let db_size = savepoint.db_size;
        let start = savepoint.start_offset as usize;
        let end = end as usize;
        // A restore still pending (an error between it and this rollback)
        // continues as part of this one: nothing could change a page while
        // it was pending, so its images are this savepoint's images too.
        let earlier = self.sp().st.lock().restore.take();
        let mut seen = RoaringBitmap::new();
        let mut todo = Vec::new();
        let mut inflight = Vec::new();
        if let Some(e) = earlier {
            for &(id, rec) in &e.todo[e.next..] {
                if id <= db_size && seen.insert(id) {
                    todo.push((id, rec));
                }
            }
            for &(id, _) in &e.todo[..e.next] {
                seen.insert(id);
            }
            inflight = e.inflight;
        }
        {
            let st = self.sp().st.lock();
            for i in start..end.min(st.index.len()) {
                let id = st.index[i];
                if id > db_size || seen.contains(id) {
                    continue;
                }
                seen.insert(id);
                todo.push((id, i as u32));
            }
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
            db.stage_discard(db_size as u64, SCRATCH_BASE)?;
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
    /// staged before. Runs in one go once it starts (it only waits, before
    /// touching anything, for a pending restore or for credits).
    pub(super) fn stream_commit(&self) -> IOResultOr<()> {
        return_if_io!(self.stream_gate());
        let db = self.sp().db.clone();
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
        if db.credits() < db.commit_credits(pages.len() as u32) {
            io_yield_one!(db.park());
        }
        if !txn && pages.len() <= MAX_PART_PAGES as usize {
            for page in &pages {
                let buf = page.get().buffer().cloned().expect("dirty page is loaded");
                if !db.batch_write(page.get().id() as u64 - 1, &buf)? {
                    db.batch_cancel();
                    return Err(stream::full().into());
                }
            }
            db.batch_commit()?;
        } else {
            for page in &pages {
                let buf = page.get().buffer().cloned().expect("dirty page is loaded");
                if !db.stage_write(page.get().id() as u64 - 1, &buf)? {
                    // The rollback that follows aborts the transaction.
                    return Err(stream::full().into());
                }
            }
            let scratch = db.config().scratch_pages as u64;
            db.stage_discard(SCRATCH_BASE, SCRATCH_BASE + scratch)?;
            db.txn_commit()?;
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
        let mut st = self.sp().st.lock();
        st.index.clear();
        st.reserved = 0;
        st.restore = None;
    }

    /// The write transaction rolled back.
    pub(super) fn stream_on_rollback(&self) {
        if let Some(sp) = &self.stream {
            let mut st = sp.st.lock();
            st.index.clear();
            st.reserved = 0;
            st.restore = None;
        }
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
