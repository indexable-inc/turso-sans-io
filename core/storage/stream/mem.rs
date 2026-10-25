//! An in-process store and run loop for a [`StreamDb`]: what the host does,
//! in memory. Tests and native benches use it; it is also the reference for
//! what an embedder does with the op list.
//!
//! The store keeps every committed version of every page, the open
//! transaction's staged parts (which `Latest` reads see) and its current,
//! unstaged part (which they don't). Completions are delivered at the start
//! of a later run, never within the run that issued the op; with
//! [`MemStore::read_delay`] > 0, reads complete that many runs later still,
//! which is how tests make a yield land between a reserve and the
//! `add_dirty` it covers.
//!
//! Quota is an escrow like the host's: a staged part debits the pages the
//! transaction had not written before, a batch debits every write, and
//! commit (pages a later part discarded) or abort refunds. An overdraft is
//! a guest bug and panics. The runner passes what is left as each run's
//! `quota_pages`.
//!
//! Credits are the host's: each run reports the grant minus the credited
//! ops (READ, PIN, STAGE with notify) still in flight, minus one while a
//! transaction is open (BEGIN "takes the credit the commit will use"), and
//! checks that the run issues no more credited ops (READ, PIN, BEGIN,
//! STAGE, COMMIT, BATCH) than that. An UNPIN of a version this stream has
//! not pinned panics, as the host fails it `Invalid`.

use super::{op, StreamDb, StreamOp, FLAG_AT_VERSION, FLAG_NOTIFY, PAGE_SIZE};
use crate::sync::Arc;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::ptr::NonNull;

#[repr(C, align(4096))]
#[derive(Clone, Copy)]
struct Slot([u8; PAGE_SIZE]);

/// Page-aligned memory for the guest arena.
pub struct MemArena {
    slots: Box<[Slot]>,
}

impl MemArena {
    pub fn new(slots: u32) -> Self {
        Self {
            slots: vec![Slot([0; PAGE_SIZE]); slots as usize].into_boxed_slice(),
        }
    }

    pub fn base(&mut self) -> NonNull<u8> {
        NonNull::new(self.slots.as_mut_ptr().cast::<u8>()).expect("non-empty arena")
    }

    pub fn slots(&self) -> u32 {
        self.slots.len() as u32
    }
}

type PageBytes = Arc<[u8]>;
/// `None`: discarded (reads as zeros), as the store's `Op::Discard`.
type Version = Option<PageBytes>;

enum Edit {
    Write(u64, PageBytes),
    Discard(u64, u64),
}

struct MemTxn {
    end: u64,
    /// Last staged write or discard of each page the parts wrote.
    staged: BTreeMap<u64, Version>,
    /// Ranges the staged parts discarded (pages not in `staged` read as
    /// zeros inside them).
    discards: Vec<(u64, u64)>,
    current: Vec<Edit>,
    /// Pages debited from the escrow.
    debited: BTreeSet<u64>,
}

impl MemTxn {
    /// Stage the current part; returns the pages it newly debits.
    fn stage(&mut self) -> u64 {
        let mut debit = 0;
        for e in self.current.drain(..) {
            match e {
                Edit::Write(p, b) => {
                    if self.debited.insert(p) {
                        debit += 1;
                    }
                    self.staged.insert(p, Some(b));
                }
                Edit::Discard(s, e) => {
                    for (_, v) in self.staged.range_mut(s..e) {
                        *v = None;
                    }
                    self.discards.push((s, e));
                }
            }
        }
        debit
    }
}

struct Due {
    run: u64,
    tag: u64,
    result: i64,
    copy: Option<(u64, PageBytes)>,
    /// Holds a credit until it completes.
    credited: bool,
}

/// The store side of one stream, in memory.
#[derive(Default)]
pub struct MemStore {
    /// page -> (version, bytes), versions ascending.
    pages: BTreeMap<u64, Vec<(u64, Version)>>,
    head: u64,
    txns: HashMap<u32, MemTxn>,
    batch: Vec<(u64, PageBytes)>,
    pins: HashMap<u64, u32>,
    due: Vec<Due>,
    run: u64,
    /// Extra runs before a read completes (0: the next run).
    pub read_delay: u64,
    pub ops_applied: u64,
    pub max_txn_pages: usize,
    /// Escrow pages left (`None`: no quota).
    pub allowance: Option<u64>,
    /// Versions below this are trimmed: a PIN or read at one completes
    /// LOST.
    pub trimmed_below: u64,
    /// Reads of scratch pages fail (a restore that cannot finish).
    pub fail_scratch_reads: bool,
}

impl MemStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn head(&self) -> u64 {
        self.head
    }

    /// What the next run's batch header says the instance may write.
    pub fn quota_pages(&self) -> u64 {
        self.allowance.unwrap_or(u64::MAX)
    }

    fn debit(&mut self, n: u64) {
        if let Some(a) = self.allowance.as_mut() {
            assert!(*a >= n, "escrow overdraft: {n} pages, {a} left");
            *a -= n;
        }
    }

    fn refund(&mut self, n: u64) {
        if let Some(a) = self.allowance.as_mut() {
            *a += n;
        }
    }

    fn at_version(&self, page: u64, v: u64) -> Option<PageBytes> {
        let hist = self.pages.get(&page)?;
        let i = hist.partition_point(|(ver, _)| *ver <= v);
        if i == 0 {
            return None;
        }
        hist[i - 1].1.clone()
    }

    fn read_latest(&self, page: u64) -> Option<PageBytes> {
        // The writer's staged parts first (there is at most one open txn).
        for t in self.txns.values() {
            if let Some(b) = t.staged.get(&page) {
                return b.clone();
            }
            if t.discards.iter().any(|&(s, e)| s <= page && page < e) {
                return None;
            }
        }
        self.at_version(page, self.head)
    }

    /// Committed bytes of `page` at `v` (zeros if never written).
    pub fn page_at(&self, page: u64, v: u64) -> Vec<u8> {
        self.at_version(page, v)
            .map_or_else(|| vec![0; PAGE_SIZE], |b| b.to_vec())
    }

    fn bytes(o: &StreamOp) -> PageBytes {
        // SAFETY: the guest keeps `ptr..ptr+len` alive (lent) until the
        // run ends, and `apply` runs before `release_run`.
        let s = unsafe { std::slice::from_raw_parts(o.ptr as *const u8, o.len as usize) };
        Arc::from(s)
    }

    fn complete_later(
        &mut self,
        tag: u64,
        result: i64,
        delay: u64,
        copy: Option<(u64, PageBytes)>,
    ) {
        self.due.push(Due {
            run: self.run + 1 + delay,
            tag,
            result,
            copy,
            credited: true,
        });
    }

    /// Credits the store holds now: credited ops in flight, plus one per
    /// open transaction.
    pub fn held_credits(&self) -> u32 {
        (self.due.iter().filter(|d| d.credited).count() + self.txns.len()) as u32
    }

    /// Versions pinned now, with their pin counts.
    pub fn pins(&self) -> &HashMap<u64, u32> {
        &self.pins
    }

    fn commit(&mut self, v: u64, writes: impl IntoIterator<Item = (u64, Version)>) {
        assert_eq!(v, self.head + 1, "versions are dense");
        for (p, b) in writes {
            self.pages.entry(p).or_default().push((v, b));
        }
        self.head = v;
    }

    /// Apply one op the guest issued this run.
    pub fn apply(&mut self, o: StreamOp) {
        self.ops_applied += 1;
        match o.kind {
            op::READ => {
                let n = o.count.max(1) as u64;
                assert_eq!(n, 1, "the guest reads one page per op");
                if self.fail_scratch_reads && o.page >= super::SCRATCH_BASE {
                    self.complete_later(o.tag, super::err::IO, 0, None);
                    return;
                }
                if o.flags & FLAG_AT_VERSION != 0 && o.at < self.trimmed_below {
                    self.complete_later(o.tag, super::err::LOST, 0, None);
                    return;
                }
                let data = if o.flags & FLAG_AT_VERSION != 0 {
                    assert!(o.at <= self.head, "read of a future version");
                    self.at_version(o.page, o.at)
                } else {
                    self.read_latest(o.page)
                };
                let data = data.unwrap_or_else(|| Arc::from(vec![0u8; PAGE_SIZE]));
                // The header read's buffer is shorter than a page.
                let data: PageBytes = Arc::from(&data[..(o.len as usize).min(data.len())]);
                self.complete_later(o.tag, o.len as i64, self.read_delay, Some((o.ptr, data)));
            }
            op::PIN => {
                if o.at < self.trimmed_below {
                    self.complete_later(o.tag, super::err::LOST, 0, None);
                } else {
                    *self.pins.entry(o.at).or_default() += 1;
                    self.complete_later(o.tag, 0, 0, None);
                }
            }
            op::UNPIN => {
                let n = self
                    .pins
                    .get_mut(&o.at)
                    .unwrap_or_else(|| panic!("UNPIN of version {} not pinned", o.at));
                *n -= 1;
                if *n == 0 {
                    self.pins.remove(&o.at);
                }
            }
            op::BEGIN => {
                assert!(self.txns.is_empty(), "one writer");
                self.txns.insert(
                    o.txn,
                    MemTxn {
                        end: o.at,
                        staged: BTreeMap::new(),
                        discards: Vec::new(),
                        current: Vec::new(),
                        debited: BTreeSet::new(),
                    },
                );
            }
            op::WRITE => {
                let b = Self::bytes(&o);
                if o.txn == 0 {
                    self.batch.push((o.page, b));
                } else {
                    let t = self.txns.get_mut(&o.txn).expect("write in an open txn");
                    assert!(o.page < t.end, "write outside the txn's range");
                    t.current.push(Edit::Write(o.page, b));
                }
            }
            op::DISCARD => {
                let t = self.txns.get_mut(&o.txn).expect("discard in an open txn");
                t.current
                    .push(Edit::Discard(o.page, o.page + o.count as u64));
            }
            op::STAGE => {
                let t = self.txns.get_mut(&o.txn).expect("stage of an open txn");
                let debit = t.stage();
                self.debit(debit);
                self.max_txn_pages = self.max_txn_pages.max(self.txns[&o.txn].staged.len());
                if o.flags & FLAG_NOTIFY != 0 {
                    self.complete_later(o.tag, 0, 0, None);
                }
            }
            op::COMMIT => {
                let mut t = self.txns.remove(&o.txn).expect("commit of an open txn");
                let debit = t.stage();
                self.debit(debit);
                let mut staged = std::mem::take(&mut t.staged);
                // Scratch never reaches a version: the guest discards it in
                // the last part; check that it did.
                assert!(
                    staged
                        .iter()
                        .all(|(p, b)| *p < super::SCRATCH_BASE || b.is_none()),
                    "a committed version holds scratch pages"
                );
                staged.retain(|p, b| *p < super::SCRATCH_BASE || b.is_some());
                // Debited pages the version does not keep come back.
                let kept = t
                    .debited
                    .iter()
                    .filter(|p| staged.get(p).is_some_and(|b| b.is_some()))
                    .count() as u64;
                self.refund(t.debited.len() as u64 - kept);
                // Committed pages inside a discarded range read as zeros.
                for &(s, e) in &t.discards {
                    let hit: Vec<u64> = self
                        .pages
                        .range(s..e)
                        .filter(|(p, h)| {
                            !staged.contains_key(p) && h.last().is_some_and(|(_, b)| b.is_some())
                        })
                        .map(|(p, _)| *p)
                        .collect();
                    for p in hit {
                        staged.insert(p, None);
                    }
                }
                self.commit(o.at, staged);
            }
            op::BATCH => {
                let writes = std::mem::take(&mut self.batch);
                self.debit(writes.len() as u64);
                self.commit(o.at, writes.into_iter().map(|(p, b)| (p, Some(b))));
            }
            op::ABORT => {
                if let Some(t) = self.txns.remove(&o.txn) {
                    self.refund(t.debited.len() as u64);
                }
            }
            op::NOTIFY => {
                self.complete_later(o.tag, 0, 0, None);
                self.due.last_mut().expect("just pushed").credited = false;
            }
            k => panic!("unknown stream op kind {k}"),
        }
    }

    /// Completions due at the start of the run that is beginning: copies
    /// read data into the arena and returns `(tag, result)`.
    fn take_due(&mut self) -> Vec<(u64, i64)> {
        self.run += 1;
        let run = self.run;
        let mut out = Vec::new();
        let mut keep = Vec::new();
        for d in self.due.drain(..) {
            if d.run > run {
                keep.push(d);
                continue;
            }
            if let Some((ptr, data)) = &d.copy {
                // SAFETY: the read's buffer is a slot the guest gave this
                // read; it stays the read's until the completion runs.
                unsafe {
                    std::ptr::copy_nonoverlapping(data.as_ptr(), *ptr as *mut u8, data.len())
                };
            }
            out.push((d.tag, d.result));
        }
        self.due = keep;
        out
    }

    pub fn has_due(&self) -> bool {
        !self.due.is_empty()
    }
}

/// The run loop: what `ix_run` is for a guest.
pub struct MemRunner {
    pub db: Arc<StreamDb>,
    pub store: MemStore,
    pub credits: u32,
    ops: Vec<StreamOp>,
    pub runs: u64,
    /// Runs whose reported credits were below the grant (the store held
    /// some).
    pub short_runs: u64,
    /// Called with `true` when guest code starts running and `false` when
    /// the store's does (heap accounting in tests).
    pub scope: fn(bool),
}

impl MemRunner {
    pub fn new(db: Arc<StreamDb>, store: MemStore) -> Self {
        Self {
            db,
            store,
            credits: super::DEFAULT_CREDITS,
            ops: Vec::new(),
            runs: 0,
            short_runs: 0,
            scope: |_| {},
        }
    }

    /// One run: deliver what is due, run `f`, hand this run's ops to the
    /// store, give lent slots back.
    pub fn run<T>(&mut self, f: impl FnOnce() -> T) -> T {
        self.runs += 1;
        (self.scope)(false);
        let due = self.store.take_due();
        let credits = self.credits.saturating_sub(self.store.held_credits());
        self.short_runs += u64::from(credits < self.credits);
        (self.scope)(true);
        self.db.begin_run(credits, self.store.quota_pages());
        for (tag, res) in due {
            self.db.complete(tag, res);
        }
        let out = f();
        self.db.take_ops(&mut self.ops);
        (self.scope)(false);
        let credited = self
            .ops
            .iter()
            .filter(|o| {
                matches!(
                    o.kind,
                    op::READ | op::PIN | op::BEGIN | op::STAGE | op::COMMIT | op::BATCH
                )
            })
            .count();
        assert!(
            credited <= credits as usize,
            "run {} issued {credited} credited ops with {credits} credits (grant {})",
            self.runs,
            self.credits
        );
        for o in self.ops.drain(..) {
            self.store.apply(o);
        }
        (self.scope)(true);
        self.db.release_run();
        out
    }
}
