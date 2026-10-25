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

use super::{op, StreamDb, StreamOp, FLAG_AT_VERSION, FLAG_NOTIFY, PAGE_SIZE};
use crate::sync::Arc;
use std::collections::{BTreeMap, HashMap};
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
}

impl MemTxn {
    fn stage(&mut self) {
        for e in self.current.drain(..) {
            match e {
                Edit::Write(p, b) => {
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
    }
}

struct Due {
    run: u64,
    tag: u64,
    result: i64,
    copy: Option<(u64, PageBytes)>,
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
}

impl MemStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn head(&self) -> u64 {
        self.head
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
        });
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
            op::PIN => *self.pins.entry(o.at).or_default() += 1,
            op::UNPIN => {
                if let Some(n) = self.pins.get_mut(&o.at) {
                    *n -= 1;
                    if *n == 0 {
                        self.pins.remove(&o.at);
                    }
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
                t.stage();
                self.max_txn_pages = self.max_txn_pages.max(self.txns[&o.txn].staged.len());
                if o.flags & FLAG_NOTIFY != 0 {
                    self.complete_later(o.tag, 0, 0, None);
                }
            }
            op::COMMIT => {
                let mut t = self.txns.remove(&o.txn).expect("commit of an open txn");
                t.stage();
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
                self.commit(o.at, writes.into_iter().map(|(p, b)| (p, Some(b))));
            }
            op::ABORT => {
                self.txns.remove(&o.txn);
            }
            op::NOTIFY => self.complete_later(o.tag, 0, 0, None),
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
            scope: |_| {},
        }
    }

    /// One run: deliver what is due, run `f`, hand this run's ops to the
    /// store, give lent slots back.
    pub fn run<T>(&mut self, f: impl FnOnce() -> T) -> T {
        self.runs += 1;
        self.db.begin_run(self.credits);
        (self.scope)(false);
        let due = self.store.take_due();
        (self.scope)(true);
        for (tag, res) in due {
            self.db.complete(tag, res);
        }
        let out = f();
        self.db.take_ops(&mut self.ops);
        (self.scope)(false);
        for o in self.ops.drain(..) {
            self.store.apply(o);
        }
        (self.scope)(true);
        self.db.release_run();
        out
    }
}
