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
//!   heap. A reserve is a claim of the statement that made it (keyed by
//!   connection and statement, so one statement ending never clears
//!   another's): its slots are kept from every connection, and the credits
//!   its records will stage are held from reads and spills. A statement
//!   whose claim's records could not stage in this run (a later run's
//!   grant is smaller, or reads in flight hold credits) waits at its next
//!   step instead of staging them short.

use super::*;
use crate::storage::stream::{
    self, Claim, ClaimKey, ReadAt, StreamDb, MAX_PART_PAGES, MAX_READ_PAGES, SCRATCH_BASE,
};
use crate::storage::wal::Wal;
use crate::sync::atomic::{AtomicBool, AtomicU32, AtomicU64};
use crate::sync::MutexGuard;

/// The pager's stream state. The fields only the stepping statement's own
/// thread touches between its calls (the owner, the park count, the restore
/// and mutation marks, the pending records) are atomics with `Relaxed`
/// order: a connection is stepped by one thread at a time, and handing it to
/// another thread already orders everything before. The rest is behind
/// `state`, whose guard ([`StreamPager::lock`]) also republishes the two
/// "anything to do?" flags (`gate`, `nested`) as it unlocks, so the per-page
/// and per-step checks are one load each.
pub(crate) struct StreamPager {
    pub(crate) db: Arc<StreamDb>,
    /// This connection's id in claim keys.
    conn: u64,
    state: Mutex<StreamPagerState>,
    /// `doomed.is_some() || restore.is_some()` as of the last unlock: false
    /// means `stream_gate` has nothing to do.
    gate: AtomicBool,
    /// `!parents.is_empty()` as of the last unlock.
    nested: AtomicBool,
    /// The atomics below are per connection and only its own statements
    /// (one thread at a time) touch them: they are atomics for `Sync`, and
    /// are read and written with plain loads and stores, no RMWs.
    ///
    /// The statement stepping now (its claims are `(conn, owner)`); set at
    /// every step. 0: no statement (open, connect).
    owner: AtomicU64,
    /// Records the reserve in progress will claim once it has made room:
    /// a spill there leaves their quota (they are not claimed yet, so
    /// their credits stay free for the spill).
    pending_records: AtomicU64,
    /// A b-tree mutation opcode (Insert, Delete, IdxInsert, IdxDelete) is
    /// running: no nested statement may step inside it (see
    /// [`Pager::stream_swap_owner`]).
    in_mutation: AtomicBool,
    /// Credit parks in a row (a run's credits short of what a run with the
    /// largest grant seen would have) since the last reserve that finished.
    credit_parks: AtomicU32,
    /// A savepoint restore is being driven (see `stream_gate`).
    restoring: AtomicBool,
}

/// [`StreamPager::state`] locked; unlocking republishes `gate` and `nested`.
struct StreamGuard<'a> {
    sp: &'a StreamPager,
    g: MutexGuard<'a, StreamPagerState>,
}

impl std::ops::Deref for StreamGuard<'_> {
    type Target = StreamPagerState;
    fn deref(&self) -> &StreamPagerState {
        &self.g
    }
}

impl std::ops::DerefMut for StreamGuard<'_> {
    fn deref_mut(&mut self) -> &mut StreamPagerState {
        &mut self.g
    }
}

impl Drop for StreamGuard<'_> {
    fn drop(&mut self) {
        // Still under the lock: every change to these fields is published
        // before the next locker (or flag reader on this thread) runs.
        let gate = self.g.doomed.is_some() || self.g.restore.is_some();
        self.sp.gate.store(gate, Ordering::Release);
        self.sp
            .nested
            .store(!self.g.parents.is_empty(), Ordering::Release);
    }
}

/// Credit parks in a row before a reserve gives up (SQLITE_FULL): about
/// this many runs with a grant too small for what the statement holds.
const CREDIT_PARK_LIMIT: u32 = 64;
/// The same while a savepoint restore is pending.
const RESTORE_CREDIT_PARK_LIMIT: u32 = 1024;

#[derive(Default)]
struct StreamPagerState {
    /// Record `i` (scratch page `SCRATCH_BASE + i`) holds this db page.
    index: Vec<u32>,
    /// (child, parent) for every nested statement that stepped inside its
    /// parent's step and stopped mid-opcode (a trigger waiting on IO, a
    /// nested ParseSchema): its claim ends when it finishes, or when the
    /// parent's statement ends (reset or drop mid-IO).
    parents: Vec<(u64, u64)>,
    /// The store transaction this connection last staged into. Ownership
    /// of the open transaction is the write lock (`stream_owns_txn`: only
    /// the writer opens one, and `begin_write_tx` aborts any a gone writer
    /// left), so a reader's rollback or doom never touches it. This is
    /// only checked at commit: if the open transaction is not the one we
    /// staged into (ours was aborted under us and a new one opened), the
    /// commit would land a partial transaction, so it dooms instead.
    txn: Option<u32>,
    restore: Option<Restore>,
    /// The transaction is aborted on the store; the connection must roll
    /// it back (see `stream_doom`).
    doomed: Option<Doom>,
}

/// See [`Pager::stream_mutation`].
pub struct StreamMutation {
    pager: Arc<Pager>,
    was: bool,
}

impl Drop for StreamMutation {
    fn drop(&mut self) {
        if let Some(sp) = &self.pager.stream {
            sp.in_mutation.store(self.was, Ordering::Relaxed);
        }
    }
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
        let conn = db.new_conn();
        Self {
            db,
            conn,
            state: Mutex::new(StreamPagerState::default()),
            gate: AtomicBool::new(false),
            nested: AtomicBool::new(false),
            owner: AtomicU64::new(0),
            pending_records: AtomicU64::new(0),
            in_mutation: AtomicBool::new(false),
            credit_parks: AtomicU32::new(0),
            restoring: AtomicBool::new(false),
        }
    }

    fn lock(&self) -> StreamGuard<'_> {
        StreamGuard {
            sp: self,
            g: self.state.lock(),
        }
    }

    /// Is a doom or a pending restore there (`stream_gate` has work)?
    #[inline]
    fn gated(&self) -> bool {
        self.gate.load(Ordering::Acquire)
    }

    #[inline]
    fn key(&self) -> ClaimKey {
        (self.conn, self.owner.load(Ordering::Relaxed))
    }
}

impl Drop for StreamPager {
    fn drop(&mut self) {
        // A connection closed mid-mutation gives its slots and credits back.
        self.db.clear_conn_claims(self.conn);
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

    /// Tell the stream WAL how many root statements the connection has
    /// active (it keeps the connection's version while any is).
    pub(crate) fn stream_root_statements(&self, active: i32) {
        if self.stream.is_some() {
            if let Some(wal) = self.wal.as_ref() {
                wal.stream_root_statements(active);
            }
        }
    }

    /// The connection holds a stream version older than the head: a read
    /// transaction (or one kept for the connection's running statements)
    /// that new statements rejoin. Its schema is that version's, so a newer
    /// shared schema must not be adopted until the hold is gone, and a
    /// write on it fails BUSY_SNAPSHOT for good (a retry rejoins it).
    pub(crate) fn stream_snapshot_stale(&self) -> bool {
        self.stream.is_some()
            && self
                .wal
                .as_ref()
                .is_some_and(|wal| wal.stream_snapshot_stale())
    }

    /// The stream transaction was aborted under this connection: its
    /// statement's abort must roll the whole transaction back.
    pub fn stream_doomed(&self) -> bool {
        self.stream
            .as_ref()
            .is_some_and(|s| s.gated() && s.lock().doomed.is_some())
    }

    fn doomed_error(&self) -> Option<LimboError> {
        let sp = self.sp();
        // The lock-free `gate` is only right if every change to `doomed`
        // or `restore` went through `StreamPager::lock` (whose guard
        // republishes it): a direct `state.lock()` that changed either would
        // leave it stale. Checked under the raw lock, so the check itself
        // republishes nothing.
        #[cfg(debug_assertions)]
        {
            let st = sp.state.lock();
            debug_assert_eq!(
                sp.gated(),
                st.doomed.is_some() || st.restore.is_some(),
                "stream gate flag is stale: state was changed without StreamPager::lock"
            );
        }
        if !sp.gated() {
            return None;
        }
        sp.lock().doomed.map(Doom::error)
    }

    /// Give up the transaction (§14): abort it on the store now, so the
    /// stream holds no part of it, and fail everything until the connection
    /// rolls back. Returns `e` for the caller to raise.
    fn stream_doom(&self, e: LimboError) -> LimboError {
        let db = &self.sp().db;
        let owns = self.stream_owns_txn();
        {
            let mut st = self.sp().lock();
            if st.doomed.is_none() {
                st.doomed = Some(Doom::of(&e));
                st.restore = None;
                db.bump(|s| s.doomed += 1);
            }
            st.txn = None;
        }
        // Only this connection's own transaction; another connection's
        // (the writer's, when a reader is doomed) is not ours to abort.
        if owns {
            db.txn_abort();
        }
        // The transaction is gone: so is every claim made for it.
        db.clear_conn_claims(self.sp().conn);
        e
    }

    /// Is the store's open transaction the one this connection opened?
    fn stream_owns_txn(&self) -> bool {
        // The store's one transaction is the write-lock holder's, whether
        // or not this connection noted it (a commit that opened it and
        // failed still owns it).
        self.holds_write_lock() && self.sp().db.txn_open()
    }

    /// A stage went into the store's open transaction: it is this
    /// connection's.
    fn stream_note_txn(&self) {
        let id = self.sp().db.txn_id();
        self.sp().lock().txn = id;
    }

    /// Park for credits a later run will have, at most
    /// [`CREDIT_PARK_LIMIT`] times in a row: `max_credits` only ever grows,
    /// so a grant that shrank for good would otherwise park for ever.
    /// Past the limit, SQLITE_FULL.
    fn stream_credit_park(&self) -> IOResultOr<()> {
        self.stream_credit_park_or(|| stream::full())
    }

    /// [`Self::stream_credit_park`], failing with `give_up()` past the
    /// limit. A pending savepoint restore gets a larger limit: giving it up
    /// dooms the whole transaction.
    fn stream_credit_park_or(&self, give_up: impl FnOnce() -> LimboError) -> IOResultOr<()> {
        let db = &self.sp().db;
        let sp = self.sp();
        // Plain load and store, not an RMW: only this connection's own
        // statements touch these per-connection fields, one at a time.
        let n = sp.credit_parks.load(Ordering::Relaxed) + 1;
        sp.credit_parks.store(n, Ordering::Relaxed);
        let limit = if sp.restoring.load(Ordering::Relaxed) {
            RESTORE_CREDIT_PARK_LIMIT
        } else {
            CREDIT_PARK_LIMIT
        };
        if n > limit {
            sp.credit_parks.store(0, Ordering::Relaxed);
            db.bump(|s| s.reserve_full += 1);
            return Err(give_up().into());
        }
        db.bump_credit_wait();
        io_yield_one!(db.park());
    }

    fn stream_credit_parks_reset(&self) {
        self.sp().credit_parks.store(0, Ordering::Relaxed);
    }

    /// The claim key of the statement stepping now.
    fn stream_key(&self) -> ClaimKey {
        self.sp().key()
    }

    /// Statement `owner` starts a step: reserves and the slots and records
    /// they promise are its own until the step returns. Returns the owner
    /// it replaces (a trigger or nested statement steps inside its
    /// parent's step), for [`Self::stream_step_end`].
    ///
    /// A nested step (the old owner is a statement mid-step: owners are
    /// put back to 0 between top-level steps) drops whatever the parent
    /// still claims, or the child would count it as another statement's
    /// and wait for it for ever. That is only sound because every nested
    /// step starts from an opcode of the parent that is not a b-tree
    /// mutation (Program for triggers and FK actions, ParseSchema,
    /// InitCdcVersion, PopulateMaterializedViews, Vacuum, the sequence
    /// functions, index-method DDL), so the parent's claim is a finished
    /// opcode's leftover. Balance's `add_dirty`s are not re-checked one by
    /// one (they rely on the opcode's claim), so a nested step started
    /// inside Insert/Delete/IdxInsert/IdxDelete would let the child take
    /// the parent's slots and the parent hit the hard rule mid-balance:
    /// keep nested statements out of mutation opcodes.
    pub fn stream_swap_owner(&self, owner: u64) -> u64 {
        let Some(sp) = &self.stream else {
            return 0;
        };
        // Load and store, not a swap (see `stream_credit_park_or`).
        let prev = sp.owner.load(Ordering::Relaxed);
        sp.owner.store(owner, Ordering::Relaxed);
        if prev != 0 && prev != owner {
            debug_assert!(
                !sp.in_mutation.load(Ordering::Relaxed),
                "stream: a nested statement stepped inside a b-tree mutation opcode"
            );
            let mut st = sp.lock();
            if !st.parents.iter().any(|&(c, _)| c == owner) {
                st.parents.push((owner, prev));
            }
            drop(st);
            sp.db.clear_claim((sp.conn, prev));
        }
        prev
    }

    /// Statement `owner`'s step returned. Unless it stopped inside an
    /// opcode (IO or a yield, `mid_op`), no opcode of it is running, so its
    /// claim is over: a statement handing out rows, or a trigger that
    /// finished, keeps nothing from its connection's other statements.
    /// The parent's owner (`prev`) is back.
    pub fn stream_step_end(&self, owner: u64, prev: u64, mid_op: bool) {
        if let Some(sp) = &self.stream {
            if !mid_op {
                // Reserves made between top-level steps (a halt run by
                // reset, schema-version writes) are under owner 0: a
                // top-level step's end clears them too (one lock for both).
                let top = (prev == 0).then_some((sp.conn, 0));
                sp.db.clear_claims((sp.conn, owner), top);
                if sp.nested.load(Ordering::Acquire) {
                    sp.lock().parents.retain(|&(c, _)| c != owner);
                }
                sp.credit_parks.store(0, Ordering::Relaxed);
            }
            sp.owner.store(prev, Ordering::Relaxed);
        }
    }

    /// At a statement's step, before it runs anything: if its claim holds
    /// records that this run's credits could not stage (a run after the
    /// one that reserved them, with a smaller grant or reads in flight),
    /// wait for a run that can. The reserve checked them only in its own
    /// run.
    pub fn stream_resume_gate(&self) -> Result<Option<Completion>> {
        let Some(sp) = self.stream.as_ref() else {
            return Ok(None);
        };
        if !sp.db.claim_short(self.stream_key()) {
            return Ok(None);
        }
        match self.stream_credit_park() {
            Ok(IOResult::IO(IOCompletions(c))) => Ok(Some(c)),
            Ok(IOResult::Done(())) => Ok(None),
            Err(e) => Err(*e),
        }
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
    /// Final review C2: a stream's slots are its page size. Any other size
    /// (or reserved bytes a codec needs that leave too little usable space)
    /// would write a page 1 bigger than its slot.
    pub(crate) fn stream_check_page_size(&self, size: PageSize) -> Result<()> {
        if size.get() as usize != stream::PAGE_SIZE {
            return Err(LimboError::InvalidArgument(format!(
                "stream: page size {} is not supported, the store's is {}",
                size.get(),
                stream::PAGE_SIZE
            )));
        }
        let reserved = self.io_ctx.read().get_reserved_space_bytes();
        if !size.has_valid_reserved_space(reserved) {
            return Err(LimboError::InvalidArgument(format!(
                "stream: reserved space {reserved} leaves less than {} usable bytes",
                PageSize::MIN_USABLE_SPACE
            )));
        }
        Ok(())
    }

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
        let Some(sp) = &self.stream else {
            return Ok(IOResult::Done(()));
        };
        let key = sp.key();
        let records = if self.has_savepoint() { slots } else { 0 };
        // Fast path: no records, no gate work, and the slots already free.
        // It does what the clear plus `stream_reserve` below would.
        if records == 0 && !sp.gated() && sp.db.try_claim_free_slots(key, slots, true) {
            self.stream_credit_parks_reset();
            return Ok(IOResult::Done(()));
        }
        sp.db.clear_claim(key);
        self.stream_reserve(slots, records)
    }

    /// Statement `owner` ended: its claim (slots and held credits) is over.
    /// Reserves are an upper bound, so some are always left. Only its own:
    /// another statement on this connection, or any statement of another
    /// connection, keeps what it was promised.
    pub(crate) fn stream_end_statement(&self, owner: u64) {
        if let Some(sp) = &self.stream {
            sp.db.clear_claims((sp.conn, owner), Some((sp.conn, 0)));
            if !sp.nested.load(Ordering::Acquire) {
                // No nested statement is registered under anyone.
                return;
            }
            // Nested statements still mid-IO under this one (a trigger, a
            // nested ParseSchema) end with it.
            let mut ended = vec![owner];
            let mut st = sp.lock();
            while let Some(i) = st.parents.iter().position(|(_, p)| ended.contains(p)) {
                let (child, _) = st.parents.swap_remove(i);
                ended.push(child);
            }
            st.parents.retain(|&(c, _)| c != owner);
            drop(st);
            for &child in &ended[1..] {
                sp.db.clear_claim((sp.conn, child));
            }
        }
    }

    /// A b-tree mutation opcode starts; the guard ends it. Nested steps
    /// inside one are a fork bug (see [`Self::stream_swap_owner`]).
    pub fn stream_mutation(self: &Arc<Self>) -> Option<StreamMutation> {
        let sp = self.stream.as_ref()?;
        let was = sp.in_mutation.load(Ordering::Relaxed);
        sp.in_mutation.store(true, Ordering::Relaxed);
        Some(StreamMutation {
            pager: self.clone(),
            was,
        })
    }

    /// Make sure `slots` fresh slots are free, `records` subjournal records
    /// fit (scratch and quota) and the credits that staging them takes are
    /// held. Scratch or quota short: SQLITE_FULL now, before anything is
    /// mutated. Slots or credits short: evict, spill or park.
    pub(crate) fn stream_reserve(&self, slots: u32, records: u32) -> IOResultOr<()> {
        return_if_io!(self.stream_gate());
        let db = &self.sp().db;
        let key = self.stream_key();
        // Fast path: no records asked for or held, and the slots already
        // free. It does what the full path below would in that case.
        if records == 0 && db.try_claim_free_slots(key, slots, false) {
            self.stream_credit_parks_reset();
            return Ok(IOResult::Done(()));
        }
        let own = db.claim(key);
        // A nested reserve (free_page inside an opcode's) asks for part of
        // what the outer one claimed: the claim is the larger of the two.
        let records = records.max(own.records);
        if records > 0 {
            if self.records_used() + records > db.config().scratch_pages {
                db.bump(|s| {
                    s.scratch_full += 1;
                    s.reserve_full += 1;
                });
                return Err(stream::full().into());
            }
            let others = db.claimed_records() - u64::from(own.records);
            if db.quota_left() < others + u64::from(records) {
                db.bump(|s| {
                    s.quota_full += 1;
                    s.reserve_full += 1;
                });
                return Err(stream::full().into());
            }
            // A hold no run's credits could meet would park for ever.
            if !db.hold_can_fit(u64::from(records)) {
                db.bump(|s| s.reserve_full += 1);
                return Err(stream::full().into());
            }
        }
        let want = slots.max(own.slots);
        // Make room before claiming (the claim's hold would take the
        // credits a spill needs), but tell the spill what quota these
        // records will take.
        let sp = self.sp();
        sp.pending_records
            .store(u64::from(records - own.records), Ordering::Relaxed);
        let room = self.stream_ensure_slots(want);
        sp.pending_records.store(0, Ordering::Relaxed);
        return_if_io!(room);
        db.set_claim(
            key,
            Claim {
                slots: want,
                records,
            },
        );
        // BEGIN (until one is open) and the closing op of each part the
        // records open, over every claim.
        if records > 0 && db.credits() < db.held_credits() {
            return self.stream_credit_park();
        }
        self.stream_credit_parks_reset();
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

    /// One fresh slot of the claim was used, and a record if `record`.
    fn stream_take_reserved(&self, record: bool) {
        self.sp().db.use_claim(self.stream_key(), true, record);
    }

    /// At least `n` free slots for this connection on top of what the other
    /// connections were promised, or IO (parked until the next run), or
    /// SQLITE_FULL when nothing can ever come back.
    pub(crate) fn stream_ensure_slots(&self, n: u32) -> IOResultOr<()> {
        let db = &self.sp().db;
        let pool = db.pool();
        let (total, free, _) = pool.page_slots();
        let (own, reserved) = db.claim_slots(self.stream_key());
        let others = reserved.saturating_sub(own);
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
        // Final review C3: dirty pages could spill, and would in a run with
        // more free credits (the grant less in-flight reads and the holds
        // was 0 this run, not for ever): wait for that run.
        if self.stream_spill_quota() > 0
            && db.spill_credit_short()
            && !self.page_cache.read().spillable_pages(1).is_empty()
        {
            return self.stream_credit_park();
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
                Ok(true) => self.stream_note_txn(),
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

    /// Spill what the free credits (past the holds) and the quota (past
    /// what the claimed records will take) allow, at most one part. Every
    /// page is counted as new to the escrow, so a spill never takes quota a
    /// claimed record needs, and never meets a refusal it would have to
    /// doom the transaction for. No subjournal record is written at spill:
    /// records are taken at `add_dirty`, before the page changes, and a
    /// staged part is only ever overwritten by a later one, never rewound.
    /// Quota a spill may take: what is left past every claim's records and
    /// those of the reserve in progress.
    fn stream_spill_quota(&self) -> u64 {
        let db = &self.sp().db;
        let pending = self.sp().pending_records.load(Ordering::Relaxed);
        db.quota_left()
            .saturating_sub(db.claimed_records() + pending)
    }

    fn stream_spill(&self) -> Result<u32> {
        let db = &self.sp().db;
        let quota = self.stream_spill_quota();
        let room = db
            .writes_within(db.free_credits())
            .min(MAX_PART_PAGES as u64)
            .min(quota) as usize;
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
    /// pin, if its version has none yet) past the holds, a slot for it on
    /// top of every claim.
    pub(super) fn stream_before_miss(&self) -> IOResultOr<()> {
        return_if_io!(self.stream_gate());
        let db = &self.sp().db;
        let at = self
            .wal
            .as_ref()
            .and_then(|w| w.stream_read_at())
            .unwrap_or(ReadAt::Latest);
        if !db.can_read(at) {
            // Bounded like the other credit parks; a read that can never
            // go out fails SQLITE_BUSY (nothing is lost, retry later).
            return self.stream_credit_park_or(|| LimboError::Busy);
        }
        let own = db.claim(self.stream_key()).slots;
        return_if_io!(self.stream_ensure_slots(1 + own));
        self.stream_credit_parks_reset();
        Ok(IOResult::Done(()))
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
                Ok(true) => self.stream_note_txn(),
                Ok(false) => return Err(self.stream_doom(stream::full())),
                Err(e) => return Err(self.stream_doom(e)),
            }
            {
                let mut st = self.sp().lock();
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
        self.stream_take_reserved(rec_at.is_some());
        Ok(())
    }

    /// A fresh page buffer for a new page (`allocate_new_page`).
    pub(super) fn stream_new_buffer(&self) -> Result<Buffer> {
        let db = &self.sp().db;
        match db.pool().try_get_page() {
            Some(b) => {
                self.stream_take_reserved(false);
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
    #[inline]
    pub(crate) fn stream_gate(&self) -> IOResultOr<()> {
        match &self.stream {
            // No doom and no restore: nothing to wait for.
            Some(sp) if sp.gated() => self.stream_gate_slow(sp),
            _ => Ok(IOResult::Done(())),
        }
    }

    #[cold]
    #[inline(never)]
    fn stream_gate_slow(&self, sp: &StreamPager) -> IOResultOr<()> {
        if let Some(e) = self.doomed_error() {
            return Err(e.into());
        }
        let Some(mut r) = sp.lock().restore.take() else {
            return Ok(IOResult::Done(()));
        };
        sp.restoring.store(true, Ordering::Relaxed);
        let res = self.stream_drive_restore(&mut r);
        sp.restoring.store(false, Ordering::Relaxed);
        match res {
            Ok(IOResult::Done(())) => Ok(IOResult::Done(())),
            Ok(IOResult::IO(c)) => {
                sp.lock().restore = Some(r);
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
        let issued_before = r.next;
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
            if r.next == issued_before && r.inflight.is_empty() {
                // Nothing went out and nothing is in flight: the run's
                // credits were short. A counted park (the restore limit,
                // `restoring` is set): past it the gate dooms the
                // transaction rather than wait forever.
                return self.stream_credit_park();
            }
            if r.next > issued_before {
                self.stream_credit_parks_reset();
            }
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
        // Final review C1: a rollback that fails part way (the cache can't
        // drop a grown page that is locked by a read in flight, or pinned)
        // has trimmed the dirty set and taken the pending restore, but has
        // staged no rewind and queued no restore. Committing after that
        // would persist the rolled-back pages, so the transaction is gone.
        self.stream_rollback_inner(savepoint, end)
            .map_err(|e| self.stream_doom(e))
    }

    fn stream_rollback_inner(&self, savepoint: &SavepointSnapshot, end: u64) -> Result<()> {
        self.reset_internal_states();
        // Final review C1: a connection without the write lock changed
        // nothing (no dirty pages, no records), and the store's open
        // transaction, if any, is the writer's: nothing to undo here.
        if !self.holds_write_lock() {
            self.invalidate_all_cursors();
            return Ok(());
        }
        let db = self.sp().db.clone();
        // The claim of the statement rolling back ends with its step (or
        // its reset), under its own key.
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
            let st = self.sp().lock();
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
        let earlier = self.sp().lock().restore.take();
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
            // A grown page with a read in flight is detached, not refused.
            cache.truncate_detaching_locked(db_size as usize)?;
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
        if self.stream_owns_txn() {
            db.stage_discard(db_size as u64, SCRATCH_BASE);
        }
        if !todo.is_empty() || !inflight.is_empty() {
            self.sp().lock().restore = Some(Restore {
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
            sp.lock().index.truncate(len);
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
        // Final review C2: the store's open transaction must be the one this
        // connection staged into (none if it staged nothing). If it is gone
        // (aborted under us), committing the rest as a plain batch would ack
        // a partial transaction.
        let mine = self.sp().lock().txn;
        if db.txn_id() != mine {
            return Err(self
                .stream_doom(Doom::Io.error())
                .into());
        }
        // The transaction is ending: its statements' claims are over (an
        // autocommit statement commits before its own end).
        db.clear_conn_claims(self.sp().conn);
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
                    Ok(true) => self.stream_note_txn(),
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
            let mut st = self.sp().lock();
            st.index.clear();
            st.restore = None;
            st.txn = None;
        }
        self.sp().credit_parks.store(0, Ordering::Relaxed);
        self.sp().db.clear_conn_claims(self.sp().conn);
    }

    /// The write transaction rolled back (whole).
    pub(super) fn stream_on_rollback(&self) {
        if let Some(sp) = &self.stream {
            {
                let mut st = sp.lock();
                st.index.clear();
                st.restore = None;
                st.doomed = None;
                st.txn = None;
            }
            sp.credit_parks.store(0, Ordering::Relaxed);
            sp.db.clear_conn_claims(sp.conn);
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
    /// A page that can't be dropped is never read again over itself: a
    /// dirty one (a restore's page) lost bytes the transaction needs, which
    /// dooms it; a pinned one is still someone's, which fails this access.
    pub(super) fn stream_take_failed_read(&self, page: &PageRef) -> Result<()> {
        if page.is_loaded() || page.is_locked() {
            return Ok(());
        }
        let id = page.get().id();
        let deleted = self.page_cache.write().delete(PageCacheKey::new(id));
        match deleted {
            Ok(()) => Ok(()),
            Err(CacheError::Dirty { .. }) => Err(self.stream_doom(LimboError::CompletionError(
                CompletionError::IOError(
                    std::io::ErrorKind::Other,
                    "stream: a dirty page's read failed",
                ),
            ))),
            Err(e) => Err(LimboError::InternalError(format!(
                "stream: page {id} failed its read and can't be dropped: {e:?}"
            ))),
        }
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

    /// Test hook: lock (`on`) or unlock resident page `id`, as a read in
    /// flight does. False if it is not resident.
    #[cfg(test)]
    pub(crate) fn stream_test_lock(&self, id: usize, on: bool) -> bool {
        let Some(page) = self.page_cache.write().peek(&PageCacheKey::new(id), false) else {
            return false;
        };
        if on {
            page.set_locked();
        } else {
            page.clear_locked();
        }
        true
    }

    /// Test hook: pin (twice, so a rollback's own unpin leaves it pinned)
    /// the highest cached page above `min`, as a PinGuard does.
    #[cfg(test)]
    pub(crate) fn stream_test_pin_above(&self, min: usize) -> Option<PageRef> {
        let mut cache = self.page_cache.write();
        let top = (min + 1..min + 100_000)
            .rev()
            .find_map(|id| cache.peek(&PageCacheKey::new(id), false))?;
        top.pin();
        top.pin();
        Some(top)
    }

    /// Test hook: give this connection's transaction up, as a failed
    /// rollback or a refused stage does.
    #[cfg(test)]
    pub(crate) fn stream_test_doom(&self) {
        let _ = self.stream_doom(stream::full());
    }

    /// Test hook: nested statements still registered under a parent.
    #[cfg(test)]
    pub(crate) fn stream_test_parents(&self) -> usize {
        self.sp().lock().parents.len()
    }

    /// Test hook: a dirty page's read failed (it is unloaded, as a failed
    /// restore read leaves it): what `stream_take_failed_read` does. The
    /// page is loaded again afterwards so the rollback finds it intact.
    #[cfg(test)]
    pub(crate) fn stream_test_fail_dirty_read(&self) -> Result<()> {
        let id = self
            .dirty_pages
            .read()
            .iter()
            .find(|&id| id != DatabaseHeader::PAGE_ID as u32)
            .expect("a dirty page") as usize;
        let page = self
            .page_cache
            .write()
            .peek(&PageCacheKey::new(id), false)
            .expect("the dirty page is resident");
        page.clear_loaded();
        let res = self.stream_take_failed_read(&page);
        page.set_loaded();
        res
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
        self.stream.as_ref().map_or(0, |s| s.lock().index.len())
    }

    /// The WAL as a `StreamWal`, for the open path.
    #[allow(dead_code)]
    pub(crate) fn stream_wal(&self) -> Option<&Arc<dyn Wal>> {
        self.wal.as_ref()
    }
}
