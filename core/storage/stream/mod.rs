//! Turso storage over the wasmworld store API (streams-guest-api v9, §14).
//!
//! The database is a stream of 4 KiB pages (db page `n` is stream page
//! `n - 1`). Every page buffer is a slot of a caller-owned arena (the
//! guest's `FrameArena`), and every store call is an entry in an op list
//! the embedder drains at the end of each run. Nothing here blocks: a read
//! returns a completion that the embedder finishes in a later run, and code
//! that has to wait for slots, credits or a lent slot to come back parks on
//! the run's notify completion, which the embedder finishes at the start of
//! the next run.
//!
//! [`StreamDb`] is that op list plus the state shared by every connection
//! (head version, the write lock, the open transaction, quota). The pager
//! side (page table, spill, subjournal in scratch, reserves) lives in
//! `pager/stream_ext.rs`; [`StreamWal`] and [`StreamStorage`] plug it into
//! Turso's `Wal` and `DatabaseStorage` seams.

pub mod io;
pub mod mem;
mod storage;
#[cfg(test)]
mod tests;
mod wal;

pub use io::StreamIo;
pub use storage::StreamStorage;
pub(crate) use wal::page_read_completion;
pub use wal::StreamWal;

use crate::io::{Buffer, Completion};
use crate::storage::buffer_pool::BufferPool;
use crate::storage::page_cache::PageCache;
use crate::sync::{Arc, Mutex, RwLock, Weak};
use crate::{CompletionError, LimboError, Result};
use roaring::RoaringTreemap;
use std::collections::{BTreeMap, HashMap};
use std::ptr::NonNull;

/// The store's page size; the only page size a stream database has.
pub const PAGE_SIZE: usize = 4096;
/// Pages one read may cover (`read_arena`/`readv` limit).
pub const MAX_READ_PAGES: usize = 16;
/// Pages one staged part (or one plain batch) may hold.
pub const MAX_PART_PAGES: u32 = 1024;
/// Op credits per run unless the embedder says otherwise.
pub const DEFAULT_CREDITS: u32 = 256;
/// The fewest op credits a run's grant must be for writes to make progress.
/// With no transaction open a mutation holds a BEGIN and one part's closing
/// op for its records, and a spill past that hold takes another BEGIN and
/// closing op (the BEGIN is then shared: the hold drops it): 4. With one
/// open the host keeps one credit for the BEGIN until the COMMIT (ABI.md
/// "Transactions span runs"), leaving 3 for a hold of 1 plus a read, a
/// spill's closing op or the commit's last part and COMMIT. Reads in flight
/// hold credits too; they come back as the reads complete.
pub const MIN_CREDITS: u32 = 4;
/// First stream page of the scratch region (subjournal records). It is the
/// tail of every transaction's page range, never part of the database.
pub const SCRATCH_BASE: u64 = 1 << 32;

/// Op kinds in [`StreamOp::kind`].
pub mod op {
    /// Read `count` pages from `page` into `ptr..ptr+len`. At `at` with
    /// [`super::FLAG_AT_VERSION`], else at `Latest` (the writer's staged
    /// parts included). Completes with the byte count.
    pub const READ: u32 = 1;
    /// Pin version `at`. Completes with 0, or with [`super::err::LOST`]
    /// if the version was released before the pin landed (`TRIMMED`).
    pub const PIN: u32 = 2;
    pub const UNPIN: u32 = 3;
    /// Open transaction `txn` over pages `[page, page + count)`.
    pub const BEGIN: u32 = 4;
    /// Write one page from `ptr` (an arena slot, valid until the run ends).
    /// `txn == 0`: part of the next [`BATCH`]; else part of the
    /// transaction's current part.
    pub const WRITE: u32 = 5;
    /// Discard pages `[page, page + count)` in transaction `txn`'s current part.
    pub const DISCARD: u32 = 6;
    /// Stage transaction `txn`'s current part. [`super::FLAG_NOTIFY`]: the
    /// embedder also completes `tag` with 0 at the start of the next run.
    pub const STAGE: u32 = 7;
    /// Commit transaction `txn`; its current part is the last part. The
    /// version is `at`.
    pub const COMMIT: u32 = 8;
    /// Commit the pending `txn == 0` writes as one batch at version `at`.
    pub const BATCH: u32 = 9;
    pub const ABORT: u32 = 10;
    /// Complete `tag` with 0 at the start of the next run.
    pub const NOTIFY: u32 = 11;
}

pub const FLAG_AT_VERSION: u32 = 1;
pub const FLAG_NOTIFY: u32 = 2;

/// Completion results below zero.
pub mod err {
    /// The read's version is gone (`LostSuffix`/`Trimmed`).
    pub const LOST: i64 = -1;
    /// Any other store failure. The handle is unusable after it.
    pub const IO: i64 = -2;
    /// The writer was fenced.
    pub const FENCED: i64 = -3;
}

/// One store call, in the flat form the embedder (host shim or the native
/// driver) reads. `ptr` is an address in the guest's memory.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct StreamOp {
    pub kind: u32,
    pub flags: u32,
    pub tag: u64,
    pub txn: u32,
    pub count: u32,
    pub page: u64,
    pub at: u64,
    pub ptr: u64,
    pub len: u64,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct StreamConfig {
    /// Scratch pages per transaction (`S`): the bound on subjournal records.
    pub scratch_pages: u32,
    /// Quota allowance in pages (what the host granted the handle).
    pub quota_pages: u64,
}

/// Counters for tests, benches and the host's metrics.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct StreamStats {
    pub runs: u64,
    pub reads: u64,
    pub read_pages: u64,
    pub pins: u64,
    pub writes: u64,
    pub parts: u64,
    pub discards: u64,
    pub txn_commits: u64,
    pub batches: u64,
    pub aborts: u64,
    /// Times code parked on the run's notify (waiting for slots/credits).
    pub parks: u64,
    pub evictions: u64,
    pub spilled_pages: u64,
    /// Copy-on-write of a page whose slot was lent or recorded.
    pub cow_pages: u64,
    pub records: u64,
    pub restored_pages: u64,
    /// `add_dirty` found no free slot: reserve-before-mutate failed to
    /// cover it. Must stay 0.
    pub hard_rule_full: u64,
    /// SQLITE_FULL raised by a reserve (slots, quota or scratch).
    pub reserve_full: u64,
    pub scratch_full: u64,
    pub quota_full: u64,
    /// `IO::step` (or anything else that would block) was called.
    pub blocking_calls: u64,
    /// An op that needed a credit its reserve should have kept found none.
    /// Must stay 0.
    pub credit_short: u64,
    /// Transactions aborted because a rollback or a staged part could not
    /// finish (the statement got SQLITE_FULL or SQLITE_IOERR).
    pub doomed: u64,
    /// Times a statement waited for a run whose credits cover what its
    /// claim's records will stage (or a read on top of the holds).
    pub credit_waits: u64,
}

pub(crate) enum Pending {
    Read(Completion),
    Notify(Completion),
    /// A PIN of this version. It fails (`err::LOST`) if the version was
    /// released before the pin landed (§4: retention 0 keeps only the head).
    Pin(u64),
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum PinState {
    /// No PIN went out yet (it goes out at the first read at the version).
    #[default]
    Unsent,
    /// The PIN went out and its completion has not come back. If the last
    /// holder leaves meanwhile the entry stays, and the completion decides:
    /// UNPIN after a success, nothing after a refusal (the host never
    /// pinned it, and an UNPIN of an unpinned version is `Invalid`).
    Pending,
    /// The PIN landed: the last holder's release sends UNPIN.
    Held,
    /// The PIN was refused (`TRIMMED`): reads at the version fail
    /// SQLITE_BUSY, and no UNPIN goes out for it.
    Lost,
}

#[derive(Default)]
struct Pin {
    holders: u32,
    state: PinState,
}

/// What one statement (`owner`) on one connection was promised by a
/// reserve: fresh arena slots, and subjournal records whose stages need op
/// credits. Keyed by (connection, owner), so a statement ending clears only
/// its own claim, never another statement's or another connection's.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Claim {
    pub(crate) slots: u32,
    pub(crate) records: u32,
}

/// (connection id, statement id).
pub(crate) type ClaimKey = (u64, u64);

struct Txn {
    id: u32,
    /// Stream pages debited from the escrow in this transaction.
    ever: RoaringTreemap,
    /// Stream pages written and not discarded since: what commit keeps.
    live: RoaringTreemap,
}

/// A page cache of one connection, for eviction across connections (they
/// share the arena).
pub(crate) type SharedCache = RwLock<PageCache>;

struct Inner {
    head: u64,
    ops: Vec<StreamOp>,
    pending: HashMap<u64, Pending>,
    next_tag: u64,
    /// Op credits left in this run.
    credits: u32,
    /// The largest credits any run reported (the handle's grant, less
    /// nothing in flight): a hold above it can never be met.
    max_credits: u32,
    /// Every statement's reservation. The slots they claim are kept free
    /// from everyone else; the credits their records' stages will take
    /// (`held`) are kept from reads and spills.
    claims: BTreeMap<ClaimKey, Claim>,
    next_conn: u64,
    notify: Option<(u64, Completion)>,
    /// Unstaged writes in the open transaction's current part. While it is
    /// above 0 the credit of the op that closes the part (its STAGE, or the
    /// COMMIT) is already taken.
    part_writes: u32,
    /// Writes waiting for a BATCH. While above 0 the BATCH's credit is
    /// already taken.
    batch_writes: u32,
    /// A discard that waits for the next part (a rollback ran with no
    /// part open and possibly no credit to open one). It goes out first in
    /// that part, before any write that could land in its range.
    pending_discard: Option<(u64, u64)>,
    txn: Option<Txn>,
    next_txn: u32,
    /// Quota pages this instance may still write: the batch header's
    /// `quota_pages` at the start of the run, less what this run wrote.
    quota_left: u64,
    pins: BTreeMap<u64, Pin>,
    writer: bool,
    failed: Option<String>,
    /// Buffers staged (or replaced) this run: alive until the host copied
    /// them, whatever happens to their pages meanwhile.
    keep: Vec<Arc<Buffer>>,
    stats: StreamStats,
    /// The database size in pages, last seen in a loaded page 1 (0: never).
    size_hint: u32,
}

/// The op list and the state every connection of one database shares.
pub struct StreamDb {
    pool: Arc<BufferPool>,
    cfg: StreamConfig,
    inner: Mutex<Inner>,
    /// Every connection's page cache (they all hold slots of one arena).
    caches: Mutex<Vec<Weak<SharedCache>>>,
}

impl std::fmt::Debug for StreamDb {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StreamDb").field("cfg", &self.cfg).finish()
    }
}

/// Which version a read reads at.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReadAt {
    /// The writer: the head plus its staged parts.
    Latest,
    /// A reader's snapshot (pinned on first use).
    Version(u64),
}

impl StreamDb {
    /// A database over the arena at `base` (`slots` 4 KiB slots) whose
    /// stream is at `head` (0: empty).
    ///
    /// # Safety
    /// `base` must point to `slots * PAGE_SIZE` writable bytes that outlive
    /// the database and that nothing else touches.
    pub unsafe fn new(base: NonNull<u8>, slots: u32, head: u64, cfg: StreamConfig) -> Arc<Self> {
        let pool = unsafe { BufferPool::new_external(base, slots, PAGE_SIZE) };
        Arc::new(Self {
            pool,
            cfg,
            inner: Mutex::new(Inner {
                head,
                ops: Vec::new(),
                pending: HashMap::new(),
                next_tag: 1,
                credits: DEFAULT_CREDITS,
                max_credits: 0,
                claims: BTreeMap::new(),
                next_conn: 1,
                notify: None,
                part_writes: 0,
                batch_writes: 0,
                pending_discard: None,
                txn: None,
                next_txn: 1,
                quota_left: cfg.quota_pages,
                pins: BTreeMap::new(),
                writer: false,
                failed: None,
                keep: Vec::new(),
                stats: StreamStats::default(),
                size_hint: 0,
            }),
            caches: Mutex::new(Vec::new()),
        })
    }

    pub fn pool(&self) -> &Arc<BufferPool> {
        &self.pool
    }

    pub fn config(&self) -> StreamConfig {
        self.cfg
    }

    pub fn head(&self) -> u64 {
        self.inner.lock().head
    }

    pub fn stats(&self) -> StreamStats {
        self.inner.lock().stats
    }

    pub fn quota_left(&self) -> u64 {
        self.inner.lock().quota_left
    }

    pub(crate) fn bump(&self, f: impl FnOnce(&mut StreamStats)) {
        f(&mut self.inner.lock().stats)
    }

    // ---- embedder side -------------------------------------------------

    /// Start a run with the batch header's `credits` (free op credits) and
    /// `quota_pages` (pages this instance may still write; `u64::MAX`: no
    /// quota). Both are re-read every run: the host tops the grant up, and
    /// staged parts already left it. Call before delivering the previous
    /// run's completions.
    pub fn begin_run(&self, credits: u32, quota_pages: u64) {
        let mut g = self.inner.lock();
        g.credits = credits;
        g.max_credits = g.max_credits.max(credits);
        g.quota_left = quota_pages;
        g.stats.runs += 1;
    }

    /// Deliver the completion of op `tag`. A negative `result` is an error
    /// (see [`err`]).
    pub fn complete(&self, tag: u64, result: i64) {
        let p = self.inner.lock().pending.remove(&tag);
        match p {
            Some(Pending::Read(c)) => {
                if result >= 0 {
                    c.complete(result as i32);
                } else if result == err::LOST {
                    c.error(CompletionError::SnapshotLost);
                } else {
                    c.error(CompletionError::IOError(
                        std::io::ErrorKind::Other,
                        "stream read failed",
                    ));
                }
            }
            Some(Pending::Notify(c)) => c.complete(0),
            Some(Pending::Pin(v)) => {
                let mut g = self.inner.lock();
                let Some(p) = g.pins.get_mut(&v) else {
                    return;
                };
                let orphan = p.holders == 0;
                if result < 0 {
                    // The version is gone; only statements reading at it
                    // fail (SQLITE_BUSY), the handle is fine. Nothing was
                    // pinned, so nothing is unpinned.
                    p.state = PinState::Lost;
                    if orphan {
                        g.pins.remove(&v);
                    }
                } else if orphan {
                    // Every holder left while the PIN was in flight: let go
                    // now that the host holds it.
                    g.pins.remove(&v);
                    Self::push_unpin(&mut g, v);
                } else {
                    p.state = PinState::Held;
                }
            }
            None => {
                if result < 0 {
                    // A write-side op failed: the store fails the handle
                    // closed; so do we.
                    self.inner.lock().failed = Some(format!("store op {tag} failed ({result})"));
                }
            }
        }
    }

    /// Move this run's ops into `out`, ending the current part with a stage
    /// (and the run's notify, if anything parked). The pointers in `out`
    /// stay valid until [`StreamDb::release_run`].
    pub fn take_ops(&self, out: &mut Vec<StreamOp>) {
        let mut g = self.inner.lock();
        let notify = g.notify.take();
        let notify_tag = notify.as_ref().map(|(t, _)| *t);
        if let Some((tag, c)) = notify {
            g.pending.insert(tag, Pending::Notify(c));
        }
        let mut notified = false;
        if g.part_writes > 0 {
            if let Some(txn) = g.txn.as_ref().map(|t| t.id) {
                let (flags, tag) = match notify_tag {
                    Some(t) => (FLAG_NOTIFY, t),
                    None => (0, 0),
                };
                notified = notify_tag.is_some();
                // Its credit was taken when the part opened.
                g.ops.push(StreamOp {
                    kind: op::STAGE,
                    flags,
                    tag,
                    txn,
                    ..Default::default()
                });
                g.part_writes = 0;
                g.stats.parts += 1;
            }
        }
        if let (Some(tag), false) = (notify_tag, notified) {
            g.ops.push(StreamOp {
                kind: op::NOTIFY,
                tag,
                ..Default::default()
            });
        }
        out.append(&mut g.ops);
    }

    /// The embedder has copied every write's bytes: lent slots come back.
    pub fn release_run(&self) {
        let keep = std::mem::take(&mut self.inner.lock().keep);
        drop(keep);
        self.pool.end_run();
    }

    /// Keep `buf` alive until the run ends.
    pub(crate) fn keep(&self, buf: Arc<Buffer>) {
        self.pool.lend(&buf);
        self.inner.lock().keep.push(buf);
    }

    /// Ops issued and not yet completed (reads, pins and the notify).
    pub fn in_flight(&self) -> usize {
        let g = self.inner.lock();
        g.pending.len() + usize::from(g.notify.is_some())
    }

    // ---- engine side ---------------------------------------------------

    fn check_failed(g: &Inner) -> Result<()> {
        match &g.failed {
            Some(m) => Err(LimboError::InternalError(m.clone())),
            None => Ok(()),
        }
    }

    pub(crate) fn credits(&self) -> u32 {
        self.inner.lock().credits
    }

    /// Credits a read or a spill may use: what is left past the holds.
    pub(crate) fn free_credits(&self) -> u32 {
        let g = self.inner.lock();
        g.credits.saturating_sub(Self::held(&g))
    }

    /// Credits kept for the claimed records' stages: a BEGIN if no
    /// transaction is open (none once one is), and the closing op of every
    /// part they open. The open part's room is not counted: a `Latest`
    /// read may stage that part first.
    fn held(g: &Inner) -> u32 {
        let records: u64 = g.claims.values().map(|c| u64::from(c.records)).sum();
        if records == 0 {
            return 0;
        }
        Self::hold_for(g, records)
    }

    fn hold_for(g: &Inner, records: u64) -> u32 {
        let writes = records + u64::from(g.pending_discard.is_some());
        let begin = u32::from(g.txn.is_none());
        begin + u32::try_from(writes.div_ceil(u64::from(MAX_PART_PAGES))).unwrap_or(u32::MAX)
    }

    /// Take `n` credits for an op the caller was promised (or checked
    /// for). Short: a reserve missed it (a fork bug), counted, SQLITE_FULL.
    fn take_credits(g: &mut Inner, n: u32) -> Result<()> {
        if g.credits < n {
            g.stats.credit_short += 1;
            return Err(full());
        }
        g.credits -= n;
        Ok(())
    }

    /// Credits that `writes` more page writes (or discards) into the
    /// transaction's parts take: its BEGIN if none is open, and the closing
    /// op of every part they open. The pending discard counts as a write.
    fn credits_for(g: &Inner, writes: u64) -> u32 {
        let writes = writes + u64::from(g.pending_discard.is_some());
        let begin = u32::from(g.txn.is_none());
        if writes == 0 {
            return begin;
        }
        let room = if g.part_writes > 0 {
            u64::from(MAX_PART_PAGES - g.part_writes)
        } else {
            0
        };
        let rest = writes.saturating_sub(room);
        begin + u32::try_from(rest.div_ceil(u64::from(MAX_PART_PAGES))).unwrap_or(u32::MAX)
    }

    pub(crate) fn stage_credits(&self, writes: u64) -> u32 {
        Self::credits_for(&self.inner.lock(), writes)
    }

    /// Credits every claim's records hold, now (see [`Self::held`]).
    pub(crate) fn held_credits(&self) -> u32 {
        Self::held(&self.inner.lock())
    }

    /// Writes that `budget` credits can stage now.
    pub(crate) fn writes_within(&self, budget: u32) -> u64 {
        let g = self.inner.lock();
        let mut b = budget;
        if g.txn.is_none() {
            if b == 0 {
                return 0;
            }
            b -= 1;
        }
        let room = if g.part_writes > 0 {
            u64::from(MAX_PART_PAGES - g.part_writes)
        } else {
            0
        };
        let writes = room + u64::from(b) * u64::from(MAX_PART_PAGES);
        writes.saturating_sub(u64::from(g.pending_discard.is_some()))
    }

    // ---- claims: what each statement's reserve was promised -------------

    /// A new connection's id for its claim keys.
    pub(crate) fn new_conn(&self) -> u64 {
        let mut g = self.inner.lock();
        let id = g.next_conn;
        g.next_conn += 1;
        id
    }

    pub(crate) fn claim(&self, key: ClaimKey) -> Claim {
        self.inner
            .lock()
            .claims
            .get(&key)
            .copied()
            .unwrap_or_default()
    }

    /// Replace `key`'s claim (an empty one is removed).
    pub(crate) fn set_claim(&self, key: ClaimKey, c: Claim) {
        let mut g = self.inner.lock();
        if c == Claim::default() {
            g.claims.remove(&key);
        } else {
            g.claims.insert(key, c);
        }
    }

    /// One of `key`'s claimed slots (`slot`) or records was used.
    pub(crate) fn use_claim(&self, key: ClaimKey, slot: bool, record: bool) {
        let mut g = self.inner.lock();
        let Some(c) = g.claims.get_mut(&key) else {
            return;
        };
        if slot {
            c.slots = c.slots.saturating_sub(1);
        }
        if record {
            c.records = c.records.saturating_sub(1);
        }
        if *c == Claim::default() {
            g.claims.remove(&key);
        }
    }

    /// Drop `key`'s claim: its statement ended.
    pub(crate) fn clear_claim(&self, key: ClaimKey) {
        self.inner.lock().claims.remove(&key);
    }

    /// Drop every claim of connection `conn` (its transaction ended, or it
    /// closed).
    pub(crate) fn clear_conn_claims(&self, conn: u64) {
        self.inner.lock().claims.retain(|k, _| k.0 != conn);
    }

    /// Records claimed over every statement (quota they will take).
    pub(crate) fn claimed_records(&self) -> u64 {
        let g = self.inner.lock();
        g.claims.values().map(|c| u64::from(c.records)).sum()
    }

    /// Can `key`'s claimed records all stage in this run? (The open part's
    /// room counts: nothing but this statement's own records goes into it
    /// while reads see no free credit.) Counted when not.
    pub(crate) fn claim_short(&self, key: ClaimKey) -> bool {
        let mut g = self.inner.lock();
        let records = g.claims.get(&key).map_or(0, |c| c.records);
        if records == 0 {
            return false;
        }
        let short = g.credits < Self::credits_for(&g, u64::from(records));
        if short {
            g.stats.credit_waits += 1;
        }
        short
    }

    /// Could the credits a claim of `records` records holds ever be met,
    /// with two left for a read (a PIN and the READ)? Judged against the
    /// largest credits any run reported (a claim past that parks for
    /// ever); reported credits already leave out what the host holds (an
    /// open transaction's BEGIN), so nothing more is taken off. Other
    /// claims' holds end, so only this one counts.
    pub(crate) fn hold_can_fit(&self, records: u64) -> bool {
        let g = self.inner.lock();
        if g.max_credits == 0 {
            return true;
        }
        Self::hold_for(&g, records).saturating_add(2) <= g.max_credits
    }

    /// This run's free credits stage no spill, but a run granted the most
    /// credits seen would (past today's holds): a short-term shortage.
    pub(crate) fn spill_credit_short(&self) -> bool {
        if self.writes_within(self.free_credits()) > 0 {
            return false;
        }
        let best = {
            let g = self.inner.lock();
            g.max_credits.saturating_sub(Self::held(&g))
        };
        self.writes_within(best) > 0
    }

    pub(crate) fn bump_credit_wait(&self) {
        self.inner.lock().stats.credit_waits += 1;
    }

    // ---- slots shared by every connection --------------------------------

    pub(crate) fn register_cache(&self, cache: &Arc<SharedCache>) {
        let mut caches = self.caches.lock();
        caches.retain(|w| w.strong_count() > 0);
        caches.push(Arc::downgrade(cache));
    }

    /// Evict clean pages from the other connections' caches until `want`
    /// slots are free. Returns pages evicted.
    pub(crate) fn evict_others(&self, own: &Arc<SharedCache>, want: u32) -> u64 {
        let caches: Vec<Arc<SharedCache>> = {
            let mut caches = self.caches.lock();
            caches.retain(|w| w.strong_count() > 0);
            caches.iter().filter_map(Weak::upgrade).collect()
        };
        let mut n = 0;
        for c in caches {
            if Arc::ptr_eq(&c, own) {
                continue;
            }
            // A cache locked further up this call stack is skipped.
            let Some(mut cache) = c.try_write() else {
                continue;
            };
            while self.pool.page_slots().1 < want && cache.evict_one_page() {
                n += 1;
            }
            if self.pool.page_slots().1 >= want {
                break;
            }
        }
        self.bump(|s| s.evictions += n);
        n
    }

    /// Arena slots claimed over every statement of every connection.
    pub(crate) fn reserved_slots(&self) -> u32 {
        let g = self.inner.lock();
        g.claims.values().map(|c| c.slots).sum()
    }

    /// A completion finished at the start of the next run (the store's
    /// NOTIFY). Every park in one run shares it.
    pub(crate) fn park(&self) -> Completion {
        let mut g = self.inner.lock();
        g.stats.parks += 1;
        if let Some((_, c)) = &g.notify {
            return c.clone();
        }
        let tag = g.next_tag;
        g.next_tag += 1;
        let c = Completion::new_wait();
        g.notify = Some((tag, c.clone()));
        c
    }

    /// Credits a read at `at` takes now (the read, and a pin first).
    fn read_need(g: &Inner, at: ReadAt) -> u32 {
        1 + u32::from(matches!(at, ReadAt::Version(v) if Self::pin_unsent(g, v)))
    }

    fn pin_unsent(g: &Inner, v: u64) -> bool {
        g.pins.get(&v).is_none_or(|p| p.state == PinState::Unsent)
    }

    /// Can a read at `at` go out now, past every hold?
    pub(crate) fn can_read(&self, at: ReadAt) -> bool {
        let g = self.inner.lock();
        g.credits >= Self::read_need(&g, at) + Self::held(&g)
    }

    /// Issue a read of one page (`page` is the stream page) into `buf`.
    /// `None`: no credit left this run past the hold (the caller parks).
    pub(crate) fn read(
        &self,
        at: ReadAt,
        page: u64,
        buf: &Buffer,
        c: Completion,
    ) -> Result<Option<Completion>> {
        let mut g = self.inner.lock();
        Self::check_failed(&g)?;
        if let ReadAt::Version(v) = at {
            if g.pins.get(&v).is_some_and(|p| p.state == PinState::Lost) {
                // The snapshot is gone: this statement fails SQLITE_BUSY.
                return Err(LimboError::CompletionError(CompletionError::SnapshotLost));
            }
        }
        let need = Self::read_need(&g, at);
        if g.credits < need + Self::held(&g) {
            return Ok(None);
        }
        match at {
            ReadAt::Latest => {
                if g.part_writes > 0 {
                    // Read-your-staged-writes covers staged parts only. The
                    // stage's credit was taken when the part opened.
                    let txn = g
                        .txn
                        .as_ref()
                        .map(|t| t.id)
                        .expect("part writes imply a txn");
                    g.ops.push(StreamOp {
                        kind: op::STAGE,
                        txn,
                        ..Default::default()
                    });
                    g.part_writes = 0;
                    g.stats.parts += 1;
                }
            }
            ReadAt::Version(v) => {
                if Self::pin_unsent(&g, v) {
                    Self::take_credits(&mut g, 1)?;
                    let tag = g.next_tag;
                    g.next_tag += 1;
                    g.ops.push(StreamOp {
                        kind: op::PIN,
                        tag,
                        at: v,
                        ..Default::default()
                    });
                    g.pending.insert(tag, Pending::Pin(v));
                    g.pins.entry(v).or_default().state = PinState::Pending;
                    g.stats.pins += 1;
                }
            }
        }
        Self::take_credits(&mut g, 1)?;
        let tag = g.next_tag;
        g.next_tag += 1;
        let (flags, at) = match at {
            ReadAt::Latest => (0, 0),
            ReadAt::Version(v) => (FLAG_AT_VERSION, v),
        };
        g.ops.push(StreamOp {
            kind: op::READ,
            flags,
            tag,
            count: 1,
            page,
            at,
            ptr: buf.as_ptr() as u64,
            len: buf.len() as u64,
            ..Default::default()
        });
        g.pending.insert(tag, Pending::Read(c.clone()));
        g.stats.reads += 1;
        g.stats.read_pages += 1;
        Ok(Some(c))
    }

    /// A reader holds version `v` (pinned lazily at its first read).
    pub(crate) fn hold(&self, v: u64) {
        self.inner.lock().pins.entry(v).or_default().holders += 1;
    }

    pub(crate) fn release(&self, v: u64) {
        let mut g = self.inner.lock();
        let Some(p) = g.pins.get_mut(&v) else {
            return;
        };
        p.holders = p.holders.saturating_sub(1);
        if p.holders > 0 {
            return;
        }
        match p.state {
            PinState::Unsent | PinState::Lost => {
                g.pins.remove(&v);
            }
            PinState::Held => {
                g.pins.remove(&v);
                Self::push_unpin(&mut g, v);
            }
            // The completion decides (see `PinState::Pending`).
            PinState::Pending => {}
        }
    }

    /// UNPIN needs no credit (it never completes, and a guest must always
    /// be able to let go).
    fn push_unpin(g: &mut Inner, v: u64) {
        g.ops.push(StreamOp {
            kind: op::UNPIN,
            at: v,
            ..Default::default()
        });
    }

    /// Test hook: every claim now.
    #[cfg(test)]
    pub(crate) fn test_claims(&self) -> Vec<(ClaimKey, Claim)> {
        let g = self.inner.lock();
        g.claims.iter().map(|(k, c)| (*k, *c)).collect()
    }

    /// Test hook: the credit state, for a stuck test's message.
    #[cfg(test)]
    pub(crate) fn test_credit_state(&self) -> String {
        let g = self.inner.lock();
        format!(
            "credits {} held {} txn {} part_writes {} pending_discard {:?} claims {:?} pins {:?}",
            g.credits,
            Self::held(&g),
            g.txn.is_some(),
            g.part_writes,
            g.pending_discard,
            g.claims,
            g.pins
                .iter()
                .map(|(v, p)| (*v, p.holders, p.state))
                .collect::<Vec<_>>()
        )
    }

    /// Test hook: (version, holders, PIN in flight) of every pin entry.
    #[cfg(test)]
    pub(crate) fn test_pins(&self) -> Vec<(u64, u32, bool)> {
        let g = self.inner.lock();
        g.pins
            .iter()
            .map(|(v, p)| (*v, p.holders, p.state == PinState::Pending))
            .collect()
    }

    /// Database size in pages last seen by any connection (0: unknown).
    pub(crate) fn size_hint(&self) -> u32 {
        self.inner.lock().size_hint
    }

    pub(crate) fn set_size_hint(&self, pages: u32) {
        self.inner.lock().size_hint = pages;
    }

    pub(crate) fn try_lock_writer(&self) -> bool {
        let mut g = self.inner.lock();
        if g.writer {
            return false;
        }
        g.writer = true;
        true
    }

    pub(crate) fn unlock_writer(&self) {
        self.inner.lock().writer = false;
    }

    pub(crate) fn txn_open(&self) -> bool {
        self.inner.lock().txn.is_some()
    }

    /// Stream pages among `pages` this transaction has not debited yet
    /// (what staging them costs in quota).
    pub(crate) fn fresh_pages(&self, pages: impl Iterator<Item = u64>) -> u64 {
        let g = self.inner.lock();
        match &g.txn {
            Some(t) => pages.filter(|p| !t.ever.contains(*p)).count() as u64,
            None => pages.count() as u64,
        }
    }

    /// Make room in the current part for one more write: BEGIN the
    /// transaction if none is open, take the closing op's credit if the part
    /// is new, and put a pending discard first in it.
    fn open_part(&self, g: &mut Inner) -> Result<u32> {
        loop {
            let begin = g.txn.is_none();
            let need = u32::from(begin) + u32::from(g.part_writes == 0);
            Self::take_credits(g, need)?;
            if begin {
                let id = g.next_txn;
                g.next_txn += 1;
                let end = SCRATCH_BASE + self.cfg.scratch_pages as u64;
                g.ops.push(StreamOp {
                    kind: op::BEGIN,
                    txn: id,
                    page: 0,
                    count: 0,
                    at: end,
                    ..Default::default()
                });
                g.txn = Some(Txn {
                    id,
                    ever: RoaringTreemap::new(),
                    live: RoaringTreemap::new(),
                });
            }
            let txn = g.txn.as_ref().expect("opened above").id;
            let Some((start, end)) = g.pending_discard.take() else {
                return Ok(txn);
            };
            Self::push_discard(g, txn, start, end);
            if g.part_writes > 0 {
                return Ok(txn);
            }
            // The discard filled the part; open the next one.
        }
    }

    /// Count one op into the current part; a full part is staged (its
    /// credit was taken when it opened).
    fn part_count(g: &mut Inner, txn: u32) {
        g.part_writes += 1;
        if g.part_writes >= MAX_PART_PAGES {
            g.ops.push(StreamOp {
                kind: op::STAGE,
                txn,
                ..Default::default()
            });
            g.part_writes = 0;
            g.stats.parts += 1;
        }
    }

    fn push_discard(g: &mut Inner, txn: u32, start: u64, end: u64) {
        if let Some(t) = g.txn.as_mut() {
            t.live.remove_range(start..end);
        }
        let count = u32::try_from(end - start).unwrap_or(u32::MAX);
        g.ops.push(StreamOp {
            kind: op::DISCARD,
            txn,
            page: start,
            count,
            ..Default::default()
        });
        g.stats.discards += 1;
        Self::part_count(g, txn);
    }

    /// Stage one page write in the open transaction (opening it first).
    /// `Ok(false)`: the quota allowance is spent (SQLITE_FULL), nothing
    /// was written. The credits it takes were reserved by the caller.
    pub(crate) fn stage_write(&self, page: u64, buf: &Arc<Buffer>) -> Result<bool> {
        let mut g = self.inner.lock();
        Self::check_failed(&g)?;
        let fresh = !g.txn.as_ref().is_some_and(|t| t.ever.contains(page));
        if fresh && g.quota_left == 0 {
            g.stats.quota_full += 1;
            return Ok(false);
        }
        let txn = self.open_part(&mut g)?;
        let t = g.txn.as_mut().expect("opened above");
        if fresh {
            t.ever.insert(page);
        }
        t.live.insert(page);
        if fresh {
            g.quota_left -= 1;
        }
        self.pool.lend(buf);
        g.keep.push(buf.clone());
        g.ops.push(StreamOp {
            kind: op::WRITE,
            txn,
            count: 1,
            page,
            ptr: buf.as_ptr() as u64,
            len: buf.len() as u64,
            ..Default::default()
        });
        g.stats.writes += 1;
        Self::part_count(&mut g, txn);
        Ok(true)
    }

    /// Discard stream pages `[start, end)` in the open transaction. With no
    /// part open it waits for the next one (it needs no credit now, so a
    /// synchronous rollback can always issue it).
    pub(crate) fn stage_discard(&self, start: u64, end: u64) {
        if start >= end {
            return;
        }
        let mut g = self.inner.lock();
        let Some(txn) = g.txn.as_ref().map(|t| t.id) else {
            return;
        };
        if g.part_writes > 0 {
            if let Some((s, e)) = g.pending_discard.take() {
                Self::push_discard(&mut g, txn, s, e);
            }
            if g.part_writes > 0 {
                Self::push_discard(&mut g, txn, start, end);
                return;
            }
        }
        if let Some(t) = g.txn.as_mut() {
            t.live.remove_range(start..end);
        }
        g.pending_discard = Some(match g.pending_discard {
            Some((s, e)) => (s.min(start), e.max(end)),
            None => (start, end),
        });
    }

    /// Commit the open transaction (its current part is the last part).
    /// Returns the new version. The caller checked the credits
    /// (`stage_credits` + 1).
    pub(crate) fn txn_commit(&self) -> Result<u64> {
        let mut g = self.inner.lock();
        Self::check_failed(&g)?;
        if g.pending_discard.is_some() {
            self.open_part(&mut g)?;
        }
        if g.part_writes == 0 {
            // No part open: the COMMIT takes its own credit.
            Self::take_credits(&mut g, 1)?;
        }
        let t = g.txn.take().expect("txn_commit without a transaction");
        let v = g.head + 1;
        g.head = v;
        // Pages a later part discarded are refunded, like the store does.
        let refund = t.ever.len() - t.ever.intersection_len(&t.live);
        g.quota_left = g.quota_left.saturating_add(refund);
        g.ops.push(StreamOp {
            kind: op::COMMIT,
            txn: t.id,
            at: v,
            ..Default::default()
        });
        g.part_writes = 0;
        g.stats.txn_commits += 1;
        Ok(v)
    }

    /// Abort the open transaction (ABORT never completes and needs no
    /// credit: a guest can always give up a transaction).
    pub(crate) fn txn_abort(&self) {
        let mut g = self.inner.lock();
        g.pending_discard = None;
        if let Some(t) = g.txn.take() {
            g.quota_left = g.quota_left.saturating_add(t.ever.len());
            g.ops.push(StreamOp {
                kind: op::ABORT,
                txn: t.id,
                ..Default::default()
            });
            g.part_writes = 0;
            g.stats.aborts += 1;
        }
    }

    /// Queue a page for the next plain batch. `Ok(false)`: no quota. The
    /// first write of a batch takes the BATCH's credit (checked by the
    /// caller).
    pub(crate) fn batch_write(&self, page: u64, buf: &Arc<Buffer>) -> Result<bool> {
        let mut g = self.inner.lock();
        Self::check_failed(&g)?;
        if g.quota_left == 0 {
            g.stats.quota_full += 1;
            return Ok(false);
        }
        if g.batch_writes == 0 {
            Self::take_credits(&mut g, 1)?;
        }
        g.quota_left -= 1;
        self.pool.lend(buf);
        g.keep.push(buf.clone());
        g.ops.push(StreamOp {
            kind: op::WRITE,
            txn: 0,
            count: 1,
            page,
            ptr: buf.as_ptr() as u64,
            len: buf.len() as u64,
            ..Default::default()
        });
        g.batch_writes += 1;
        g.stats.writes += 1;
        Ok(true)
    }

    /// Undo the writes queued for the next batch (a commit that failed on
    /// quota midway). Only the writes after this run's last BATCH: earlier
    /// ones belong to a batch already committed (the page-1 init is
    /// version 1, often in the same run as the first commit).
    pub(crate) fn batch_cancel(&self) {
        let mut g = self.inner.lock();
        let from = g
            .ops
            .iter()
            .rposition(|o| o.kind == op::BATCH)
            .map_or(0, |i| i + 1);
        let mut n = 0u64;
        let mut i = 0usize;
        g.ops.retain(|o| {
            let drop = i >= from && o.kind == op::WRITE && o.txn == 0;
            i += 1;
            n += u64::from(drop);
            !drop
        });
        g.quota_left = g.quota_left.saturating_add(n);
        if g.batch_writes > 0 {
            // The BATCH's credit, taken by the first write.
            g.credits += 1;
        }
        g.batch_writes = 0;
    }

    pub(crate) fn batch_commit(&self) -> Result<u64> {
        let mut g = self.inner.lock();
        Self::check_failed(&g)?;
        if g.batch_writes == 0 {
            Self::take_credits(&mut g, 1)?;
        }
        let v = g.head + 1;
        g.head = v;
        g.ops.push(StreamOp {
            kind: op::BATCH,
            at: v,
            ..Default::default()
        });
        g.batch_writes = 0;
        g.stats.batches += 1;
        Ok(v)
    }
}

/// Ordinary SQLITE_FULL.
pub(crate) fn full() -> LimboError {
    LimboError::DatabaseFull
}
