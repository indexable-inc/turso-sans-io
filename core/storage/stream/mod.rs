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
mod wal;

pub use io::StreamIo;
pub use storage::StreamStorage;
pub(crate) use wal::page_read_completion;
pub use wal::StreamWal;

use crate::io::{Buffer, Completion};
use crate::storage::buffer_pool::BufferPool;
use crate::sync::{Arc, Mutex};
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
/// First stream page of the scratch region (subjournal records). It is the
/// tail of every transaction's page range, never part of the database.
pub const SCRATCH_BASE: u64 = 1 << 32;

/// Op kinds in [`StreamOp::kind`].
pub mod op {
    /// Read `count` pages from `page` into `ptr..ptr+len`. At `at` with
    /// [`super::FLAG_AT_VERSION`], else at `Latest` (the writer's staged
    /// parts included). Completes with the byte count.
    pub const READ: u32 = 1;
    /// Pin version `at` (never fails for a retained version).
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
}

pub(crate) enum Pending {
    Read(Completion),
    Notify(Completion),
}

#[derive(Default)]
struct Pin {
    holders: u32,
    /// The PIN op went out (at the first read at this version).
    sent: bool,
}

struct Txn {
    id: u32,
    /// Stream pages debited from the escrow in this transaction.
    ever: RoaringTreemap,
    /// Stream pages written and not discarded since: what commit keeps.
    live: RoaringTreemap,
}

struct Inner {
    head: u64,
    ops: Vec<StreamOp>,
    pending: HashMap<u64, Pending>,
    next_tag: u64,
    credits: u32,
    notify: Option<(u64, Completion)>,
    /// Unstaged writes in the open transaction's current part.
    part_writes: u32,
    /// Writes waiting for a BATCH.
    batch_writes: u32,
    txn: Option<Txn>,
    next_txn: u32,
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
                notify: None,
                part_writes: 0,
                batch_writes: 0,
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

    /// Start a run with `credits` op credits. Call before delivering the
    /// previous run's completions.
    pub fn begin_run(&self, credits: u32) {
        let mut g = self.inner.lock();
        g.credits = credits;
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
                } else {
                    let msg = if result == err::LOST {
                        "stream version lost"
                    } else {
                        "stream read failed"
                    };
                    c.error(CompletionError::IOError(std::io::ErrorKind::Other, msg));
                }
            }
            Some(Pending::Notify(c)) => c.complete(0),
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

    /// Ops issued and not yet completed (reads and the notify).
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

    fn take_credit(g: &mut Inner) -> bool {
        if g.credits == 0 {
            return false;
        }
        g.credits -= 1;
        true
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

    /// Issue a read of one page (`page` is the stream page) into `buf`.
    /// `None`: no credit left this run (the caller parks).
    pub(crate) fn read(
        &self,
        at: ReadAt,
        page: u64,
        buf: &Buffer,
        c: Completion,
    ) -> Result<Option<Completion>> {
        let mut g = self.inner.lock();
        Self::check_failed(&g)?;
        // A pin and a stage may go first.
        let unpinned = |g: &Inner, v: u64| !g.pins.get(&v).is_some_and(|p| p.sent);
        let need = 1
            + u32::from(matches!(at, ReadAt::Version(v) if unpinned(&g, v)))
            + u32::from(matches!(at, ReadAt::Latest) && g.part_writes > 0);
        if g.credits < need {
            return Ok(None);
        }
        match at {
            ReadAt::Latest => {
                if g.part_writes > 0 {
                    // Read-your-staged-writes covers staged parts only.
                    let txn = g
                        .txn
                        .as_ref()
                        .map(|t| t.id)
                        .expect("part writes imply a txn");
                    Self::take_credit(&mut g);
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
                if unpinned(&g, v) {
                    Self::take_credit(&mut g);
                    g.ops.push(StreamOp {
                        kind: op::PIN,
                        at: v,
                        ..Default::default()
                    });
                    g.pins.entry(v).or_default().sent = true;
                    g.stats.pins += 1;
                }
            }
        }
        Self::take_credit(&mut g);
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
        if p.holders == 0 {
            let sent = p.sent;
            g.pins.remove(&v);
            if sent {
                g.ops.push(StreamOp {
                    kind: op::UNPIN,
                    at: v,
                    ..Default::default()
                });
            }
        }
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

    /// Credits a commit of `pages` pages needs (begin, stages, commit).
    pub(crate) fn commit_credits(&self, pages: u32) -> u32 {
        let g = self.inner.lock();
        let parts = (g.part_writes + pages).div_ceil(MAX_PART_PAGES);
        parts + 2
    }

    fn ensure_txn(&self, g: &mut Inner) -> Result<u32> {
        if let Some(t) = &g.txn {
            return Ok(t.id);
        }
        if !Self::take_credit(g) {
            return Err(LimboError::InternalError(
                "stream: no credit to begin a transaction".into(),
            ));
        }
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
        Ok(id)
    }

    /// Stage one page write in the open transaction (opening it first).
    /// `Ok(false)`: the quota allowance is spent (SQLITE_FULL), nothing
    /// was written.
    pub(crate) fn stage_write(&self, page: u64, buf: &Arc<Buffer>) -> Result<bool> {
        let mut g = self.inner.lock();
        Self::check_failed(&g)?;
        let txn = self.ensure_txn(&mut g)?;
        let t = g.txn.as_mut().expect("opened above");
        let fresh = !t.ever.contains(page);
        if fresh {
            if g.quota_left == 0 {
                g.stats.quota_full += 1;
                return Ok(false);
            }
            g.quota_left -= 1;
            let t = g.txn.as_mut().expect("opened above");
            t.ever.insert(page);
        }
        g.txn.as_mut().expect("opened above").live.insert(page);
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
        g.part_writes += 1;
        g.stats.writes += 1;
        if g.part_writes >= MAX_PART_PAGES {
            // Staging costs a credit; the part closes even without one at
            // the end of the run (take_ops), so this never fails.
            if Self::take_credit(&mut g) {
                g.ops.push(StreamOp {
                    kind: op::STAGE,
                    txn,
                    ..Default::default()
                });
                g.part_writes = 0;
                g.stats.parts += 1;
            }
        }
        Ok(true)
    }

    /// Discard stream pages `[start, end)` in the open transaction.
    pub(crate) fn stage_discard(&self, start: u64, end: u64) -> Result<()> {
        if start >= end {
            return Ok(());
        }
        let mut g = self.inner.lock();
        let Some(t) = g.txn.as_mut() else {
            return Ok(());
        };
        t.live.remove_range(start..end);
        let txn = t.id;
        let count = u32::try_from(end - start).unwrap_or(u32::MAX);
        g.ops.push(StreamOp {
            kind: op::DISCARD,
            txn,
            page: start,
            count,
            ..Default::default()
        });
        g.part_writes += 1;
        g.stats.discards += 1;
        Ok(())
    }

    /// Commit the open transaction (its current part is the last part).
    /// Returns the new version.
    pub(crate) fn txn_commit(&self) -> Result<u64> {
        let mut g = self.inner.lock();
        Self::check_failed(&g)?;
        let t = g.txn.take().expect("txn_commit without a transaction");
        let v = g.head + 1;
        g.head = v;
        // Pages a later part discarded are refunded, like the store does.
        g.quota_left += t.ever.len() - t.ever.intersection_len(&t.live);
        let _ = Self::take_credit(&mut g);
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

    pub(crate) fn txn_abort(&self) {
        let mut g = self.inner.lock();
        if let Some(t) = g.txn.take() {
            g.quota_left += t.ever.len();
            g.ops.push(StreamOp {
                kind: op::ABORT,
                txn: t.id,
                ..Default::default()
            });
            g.part_writes = 0;
            g.stats.aborts += 1;
        }
    }

    /// Queue a page for the next plain batch. `Ok(false)`: no quota.
    pub(crate) fn batch_write(&self, page: u64, buf: &Arc<Buffer>) -> Result<bool> {
        let mut g = self.inner.lock();
        Self::check_failed(&g)?;
        if g.quota_left == 0 {
            g.stats.quota_full += 1;
            return Ok(false);
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

    /// Undo queued batch writes (a commit that failed on quota midway).
    pub(crate) fn batch_cancel(&self) {
        let mut g = self.inner.lock();
        let mut n = 0u64;
        g.ops.retain(|o| {
            let drop = o.kind == op::WRITE && o.txn == 0;
            n += u64::from(drop);
            !drop
        });
        g.quota_left += n;
        g.batch_writes = 0;
    }

    pub(crate) fn batch_commit(&self) -> Result<u64> {
        let mut g = self.inner.lock();
        Self::check_failed(&g)?;
        let v = g.head + 1;
        g.head = v;
        let _ = Self::take_credit(&mut g);
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
