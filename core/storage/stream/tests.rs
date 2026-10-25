//! Fork tests for the stream storage layer (streams-guest-api v9 §14 and
//! §16). Every test runs over [`MemStore`] with reads that complete one run
//! late, so any yield between a reserve and the `add_dirty` it covers is
//! exercised, and every test checks the two invariants: nothing blocked
//! (`blocking_calls == 0`) and `add_dirty` never hit its hard rule
//! (`hard_rule_full == 0`).

use super::mem::{MemArena, MemRunner, MemStore};
use super::{StreamConfig, StreamDb, StreamIo, StreamStats, StreamStorage};
use crate::types::IOResult;
use crate::{
    ConnectAsyncState, ConnectOpts, Connection, Database, LimboError, OpenDbAsyncState,
    OpenOptions, SqliteDialect, StepResult, Value, IO,
};
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::sync::Arc;

// ---- heap accounting -------------------------------------------------------

thread_local! {
    static COUNT: Cell<bool> = const { Cell::new(false) };
    static CUR: Cell<isize> = const { Cell::new(0) };
    static PEAK: Cell<isize> = const { Cell::new(0) };
}

/// Counts heap bytes allocated by guest code on this thread (allocations
/// made while `COUNT` is set carry their size in a prefix, so frees made
/// anywhere are matched). The in-memory store's own pages are not counted:
/// on wasm they live in the host.
struct Counting;

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let pre = l.align().max(16);
        let full = unsafe { Layout::from_size_align_unchecked(l.size() + pre, l.align().max(16)) };
        let p = unsafe { System.alloc(full) };
        if p.is_null() {
            return p;
        }
        let counted = COUNT.try_with(Cell::get).unwrap_or(false);
        let tag = if counted { l.size() } else { 0 };
        unsafe { (p.add(pre - 8) as *mut usize).write(tag) };
        if counted {
            let _ = CUR.try_with(|c| {
                let v = c.get() + l.size() as isize;
                c.set(v);
                let _ = PEAK.try_with(|p| p.set(p.get().max(v)));
            });
        }
        unsafe { p.add(pre) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, l: Layout) {
        let pre = l.align().max(16);
        let base = unsafe { ptr.sub(pre) };
        let tag = unsafe { (base.add(pre - 8) as *const usize).read() };
        if tag != 0 {
            let _ = CUR.try_with(|c| c.set(c.get() - tag as isize));
        }
        let full = unsafe { Layout::from_size_align_unchecked(l.size() + pre, l.align().max(16)) };
        unsafe { System.dealloc(base, full) }
    }
}

#[global_allocator]
static ALLOC: Counting = Counting;

fn guest_scope(on: bool) {
    COUNT.with(|c| c.set(on));
}

fn heap_now() -> isize {
    CUR.with(Cell::get)
}

fn heap_reset_peak() -> isize {
    let now = heap_now();
    PEAK.with(|p| p.set(now));
    now
}

fn heap_peak() -> isize {
    PEAK.with(Cell::get)
}

// ---- harness ---------------------------------------------------------------

const MAX_RUNS: u64 = 1_000_000;

struct H {
    r: MemRunner,
    sdb: Arc<StreamDb>,
    db: Arc<Database>,
    conn: Arc<Connection>,
    /// Every this many runs, another statement takes every free slot for
    /// the run (`stream_test_squeeze`) before this one steps. 0: never.
    squeeze_every: u64,
    // Last: the arena outlives everything that points into it.
    _arena: MemArena,
}

#[derive(Clone, Copy)]
struct Cfg {
    slots: u32,
    scratch: u32,
    quota: u64,
    read_delay: u64,
    count_heap: bool,
    /// Op credits per run.
    credits: u32,
}

impl Default for Cfg {
    fn default() -> Self {
        Self {
            slots: 256,
            scratch: 65_536,
            quota: u64::MAX / 2,
            read_delay: 1,
            count_heap: false,
            credits: super::DEFAULT_CREDITS,
        }
    }
}

/// Re-enter `f` only once the IO it returned has finished: the open and
/// connect state machines assume their caller waits.
fn drive<T>(
    r: &mut MemRunner,
    mut f: impl FnMut() -> crate::Result<IOResult<T>, Box<LimboError>>,
) -> T {
    let mut wait: Option<crate::types::IOCompletions> = None;
    for _ in 0..MAX_RUNS {
        let out = r.run(|| {
            if wait.as_ref().is_some_and(|c| !c.finished()) {
                return None;
            }
            Some(f())
        });
        match out {
            None => {}
            Some(Ok(IOResult::Done(v))) => return v,
            Some(Ok(IOResult::IO(c))) => wait = Some(c),
            Some(Err(e)) => panic!("open/connect failed: {e}"),
        }
    }
    panic!("no progress after {MAX_RUNS} runs");
}

impl H {
    fn open(cfg: Cfg) -> H {
        let mut arena = MemArena::new(cfg.slots);
        let sdb = unsafe {
            StreamDb::new(
                arena.base(),
                cfg.slots,
                0,
                StreamConfig {
                    scratch_pages: cfg.scratch,
                    quota_pages: cfg.quota,
                },
            )
        };
        let io: Arc<dyn IO> = StreamIo::new(sdb.clone(), 7);
        let mut store = MemStore::new();
        store.read_delay = cfg.read_delay;
        store.allowance = (cfg.quota < u64::MAX / 2).then_some(cfg.quota);
        let mut r = MemRunner::new(sdb.clone(), store);
        r.credits = cfg.credits;
        if cfg.count_heap {
            r.scope = guest_scope;
        }
        let opts = OpenOptions::new(Arc::new(SqliteDialect))
            .storage(Arc::new(StreamStorage::new(sdb.clone())));
        let mut st = OpenDbAsyncState::new();
        let db = drive(&mut r, || {
            Database::open_async(&mut st, io.clone(), ":memory:stream", &opts)
        });
        let mut cst = ConnectAsyncState::new();
        let conn = drive(&mut r, || db.connect_async(ConnectOpts::new(), &mut cst));
        let h = H {
            r,
            sdb,
            db,
            conn,
            squeeze_every: 0,
            _arena: arena,
        };
        h.check_invariants();
        h
    }

    fn connect(&mut self) -> Arc<Connection> {
        let mut cst = ConnectAsyncState::new();
        let db = self.db.clone();
        drive(&mut self.r, || {
            db.connect_async(ConnectOpts::new(), &mut cst)
        })
    }

    fn stats(&self) -> StreamStats {
        self.sdb.stats()
    }

    fn check_invariants(&self) {
        let s = self.stats();
        assert_eq!(s.blocking_calls, 0, "something blocked: {s:?}");
        assert_eq!(s.hard_rule_full, 0, "add_dirty hit the hard rule: {s:?}");
        assert_eq!(
            s.credit_short, 0,
            "an op found no credit it was promised: {s:?}"
        );
    }

    /// Run `sql` on `conn` to completion, one step loop per run (a run ends
    /// at the first IO). Returns the rows.
    fn exec_on(
        &mut self,
        conn: &Arc<Connection>,
        sql: &str,
        params: &[Value],
    ) -> crate::Result<Vec<Vec<Value>>> {
        let mut stmt = self.r.run(|| conn.prepare(sql))?;
        for (i, p) in params.iter().enumerate() {
            stmt.bind_at(std::num::NonZero::new(i + 1).unwrap(), p.clone())?;
        }
        let mut rows = Vec::new();
        let squeeze = self.squeeze_every;
        for _ in 0..MAX_RUNS {
            let squeeze_now = squeeze > 0 && self.r.runs % squeeze == 0;
            let done = self.r.run(|| -> crate::Result<bool> {
                if squeeze_now {
                    conn.pager.load().stream_test_squeeze(None);
                }
                loop {
                    match stmt.step()? {
                        StepResult::Row => {
                            let row = stmt.row().expect("row");
                            rows.push(row.get_values().cloned().collect());
                        }
                        StepResult::Done => return Ok(true),
                        StepResult::IO => return Ok(false),
                        StepResult::Yield => return Ok(false),
                        other => panic!("unexpected step result {other:?}"),
                    }
                }
            })?;
            if done {
                self.check_invariants();
                return Ok(rows);
            }
        }
        let pager = conn.pager.load().clone();
        panic!(
            "statement made no progress after {MAX_RUNS} runs: {sql}\n{:?}\n{}\nstore holds {}\nslots {:?}, free_page {}, due {}",
            self.stats(),
            self.sdb.test_credit_state(),
            self.r.store.held_credits(),
            self.sdb.pool().page_slots(),
            pager.stream_test_free_page_state(),
            self.r.store.has_due()
        );
    }

    fn exec(&mut self, sql: &str) -> crate::Result<Vec<Vec<Value>>> {
        let conn = self.conn.clone();
        self.exec_on(&conn, sql, &[])
    }

    fn ok(&mut self, sql: &str) {
        if let Err(e) = self.exec(sql) {
            panic!(
                "{sql}: {e}\n{:?}\nslots (total, free, lent): {:?}",
                self.stats(),
                self.sdb.pool().page_slots()
            );
        }
    }

    fn one(&mut self, sql: &str) -> i64 {
        let rows = self.exec(sql).unwrap_or_else(|e| panic!("{sql}: {e}"));
        match &rows[..] {
            [row] => int(&row[0]),
            _ => panic!("{sql}: {} rows", rows.len()),
        }
    }

    /// A table `name` of about `pages` leaf pages: 4 rows of ~900 bytes per
    /// page, `n` = 0 in every row.
    fn fill(&mut self, name: &str, pages: u64) {
        let rows = pages * 4;
        self.ok(&format!(
            "CREATE TABLE {name}(id INTEGER PRIMARY KEY, n INTEGER NOT NULL, v BLOB)"
        ));
        self.ok(&format!(
            "INSERT INTO {name}(id, n, v) WITH RECURSIVE c(i) AS (SELECT 1 UNION ALL SELECT i + 1 FROM c WHERE i < {rows}) \
             SELECT i, 0, zeroblob(900) FROM c"
        ));
    }

    fn integrity(&mut self) {
        let rows = self
            .exec("PRAGMA integrity_check")
            .expect("integrity_check");
        let text: Vec<String> = rows.iter().map(|r| format!("{:?}", r[0])).collect();
        assert!(
            text.len() == 1 && text[0].contains("ok"),
            "integrity_check: {text:?}"
        );
    }
}

fn int(v: &Value) -> i64 {
    match v {
        Value::Null => 0,
        v => v
            .as_int()
            .unwrap_or_else(|| panic!("not an integer: {v:?}")),
    }
}

fn is_full(e: &LimboError) -> bool {
    e.sqlite_result_code() == 13
}

// ---- tests -----------------------------------------------------------------

#[test]
fn insert_and_lookup_roundtrip() {
    let mut h = H::open(Cfg::default());
    h.ok("CREATE TABLE t(k INTEGER, v TEXT)");
    h.ok("CREATE INDEX tk ON t(k)");
    h.ok("BEGIN");
    let conn = h.conn.clone();
    for i in 0..2_000i64 {
        h.exec_on(
            &conn,
            "INSERT INTO t(k, v) VALUES (?1, ?2)",
            &[
                Value::from_i64((i * 7919) % 2_000),
                Value::from_text(format!("value-{i:026}")),
            ],
        )
        .unwrap();
    }
    h.ok("COMMIT");
    assert_eq!(h.one("SELECT count(*) FROM t"), 2_000);
    assert_eq!(h.one("SELECT count(*) FROM t WHERE k = 1234"), 1);
    // A second connection reads the committed state from the stream.
    let c2 = h.connect();
    let rows = h.exec_on(&c2, "SELECT count(*) FROM t", &[]).unwrap();
    assert_eq!(int(&rows[0][0]), 2_000);
    h.integrity();
    h.check_invariants();
}

/// §14 change 1 + 2: an explicit transaction far larger than the arena
/// spills into staged parts and commits; the guest heap stays bounded.
#[test]
fn explicit_txn_large_update_stays_in_arena() {
    let mut h = H::open(Cfg {
        slots: 256,
        count_heap: true,
        ..Cfg::default()
    });
    h.fill("t", 4_000);
    let before = h.stats();
    let base = heap_reset_peak();
    h.ok("BEGIN");
    h.ok("UPDATE t SET n = n + 1");
    h.ok("COMMIT");
    let peak = heap_peak() - base;
    let s = h.stats();
    assert!(
        s.spilled_pages - before.spilled_pages >= 3_000,
        "the update spilled: {s:?}"
    );
    assert!(s.parts > before.parts);
    assert_eq!(h.one("SELECT sum(n) FROM t"), 16_000);
    // Arena is caller memory; the heap holds the index (4 B per record),
    // the dirty set and a constant. 16k pages of heap would be 64 MiB.
    let bound = 4 * 16_000 + 8 * 1024 * 1024;
    eprintln!(
        "explicit_txn_large_update_stays_in_arena: heap peak {peak} B (bound {bound}), {s:?}"
    );
    assert!(peak < bound as isize, "heap peak {peak} over {bound}");
    h.integrity();
}

/// §14 change 3: `ROLLBACK TO` after pages past the savepoint's size were
/// spilled discards them from the transaction, and restores pre-images of
/// the pages that existed.
#[test]
fn rollback_to_after_spill_discards_grown_pages() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 40);
    let size_before = h.one("PRAGMA page_count");
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    h.ok("UPDATE t SET n = 7");
    h.ok(
        "INSERT INTO t(id, n, v) WITH RECURSIVE c(i) AS (SELECT 1000 UNION ALL SELECT i + 1 FROM c WHERE i < 2200) \
         SELECT i, 1, zeroblob(900) FROM c",
    );
    let grown = h.one("PRAGMA page_count");
    assert!(grown > size_before + 200, "grew: {size_before} -> {grown}");
    assert!(h.stats().spilled_pages > 0);
    h.ok("ROLLBACK TO a");
    assert_eq!(h.one("SELECT count(*) FROM t"), 160);
    assert_eq!(h.one("SELECT sum(n) FROM t"), 0);
    h.ok("COMMIT");
    let s = h.stats();
    assert!(s.discards > 0 && s.restored_pages > 0, "{s:?}");
    // The committed version holds nothing past the old size.
    let head = h.r.store.head();
    for p in size_before as u64..grown as u64 {
        assert!(
            h.r.store.page_at(p, head).iter().all(|b| *b == 0),
            "page {} committed after rollback",
            p + 1
        );
    }
    assert_eq!(h.one("PRAGMA page_count"), size_before);
    h.integrity();
}

/// §14 change 4 (v8 index check): nested savepoints whose records add up
/// past the scratch range fail SQLITE_FULL at the reserve, never at the
/// hard rule, and the transaction stays usable.
#[test]
fn nested_savepoint_subjournal_past_scratch_fails_full() {
    let mut h = H::open(Cfg {
        slots: 512,
        scratch: 160,
        ..Cfg::default()
    });
    h.fill("t", 200);
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    h.ok("UPDATE t SET n = 1 WHERE id <= 200");
    h.ok("SAVEPOINT b");
    let err = h
        .exec("UPDATE t SET n = 2 WHERE id > 200")
        .expect_err("records past S");
    assert!(is_full(&err), "expected SQLITE_FULL, got {err}");
    let s = h.stats();
    assert!(s.scratch_full > 0, "{s:?}");
    // The failed statement was rolled back; the transaction is intact.
    assert_eq!(h.one("SELECT sum(n) FROM t"), 200);
    h.ok("ROLLBACK TO a");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 0);
    h.ok("UPDATE t SET n = 3 WHERE id <= 4");
    h.ok("COMMIT");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 12);
    h.integrity();
    h.check_invariants();
}

/// §14 change 4 (v8): `DELETE FROM t` (ClearBtree → free_page per page) in
/// a transaction, with an arena far smaller than the table and other
/// statements taking the free slots every third run (reads complete two
/// runs after they are issued, so every other run would never coincide
/// with a read), parks in the reserves
/// and resumes run after run instead of reaching the hard rule; `ROLLBACK`
/// restores every page and the heap stays bounded.
#[test]
fn delete_all_in_txn_small_arena_parks() {
    let mut h = H::open(Cfg {
        slots: 48,
        count_heap: true,
        ..Cfg::default()
    });
    h.fill("t", 2_000);
    let pages = h.one("PRAGMA page_count");
    let before = h.stats();
    h.ok("BEGIN");
    let base = heap_reset_peak();
    h.squeeze_every = 3;
    h.ok("DELETE FROM t");
    h.squeeze_every = 0;
    let peak = heap_peak() - base;
    let s = h.stats();
    assert!(s.parks > before.parks, "parked: {s:?}");
    assert_eq!(h.one("SELECT count(*) FROM t"), 0);
    h.ok("ROLLBACK");
    assert_eq!(h.one("SELECT count(*) FROM t"), 8_000);
    assert_eq!(h.one("PRAGMA page_count"), pages);
    let bound = 4 * 65_536 + 8 * 1024 * 1024;
    eprintln!(
        "delete_all: heap peak {peak} B (bound {bound}), parks {}, {s:?}",
        s.parks - before.parks
    );
    assert!(peak < bound as isize, "heap peak {peak} over {bound}");
    h.integrity();
    h.check_invariants();
}

/// The same with `DROP TABLE t` (`Destroy`), then `COMMIT`: the freelist
/// holds the table's pages.
#[test]
fn drop_table_in_txn_small_arena_parks() {
    let mut h = H::open(Cfg {
        slots: 48,
        ..Cfg::default()
    });
    h.fill("t", 2_000);
    h.fill("u", 10);
    let before = h.stats();
    h.ok("BEGIN");
    h.squeeze_every = 3;
    let runs0 = h.r.runs;
    h.ok("DROP TABLE t");
    h.squeeze_every = 0;
    let mid = h.stats();
    eprintln!(
        "drop_table: {} runs, reads {}, parks {}, evictions {}",
        h.r.runs - runs0,
        mid.reads - before.reads,
        mid.parks - before.parks,
        mid.evictions - before.evictions
    );
    h.ok("COMMIT");
    let s = h.stats();
    assert!(s.parks > before.parks, "parked: {s:?}");
    assert_eq!(
        h.one("SELECT count(*) FROM sqlite_schema WHERE name = 't'"),
        0
    );
    assert_eq!(h.one("SELECT count(*) FROM u"), 40);
    assert!(h.one("PRAGMA freelist_count") >= 2_000);
    h.integrity();
    h.check_invariants();
}

/// F5: `free_page` reserves at `Start`, then `AddToTrunk` reads the
/// (uncached) trunk and yields; meanwhile the slots go to another
/// statement. The re-check after the read parks (state unchanged, no new
/// read), and the next run finishes the free. To force the re-check, the
/// squeeze here also takes claimed slots, which no real statement can.
#[test]
fn free_page_first_trunk_uncached_one_slot_parks() {
    // R for a 25-page database is 27 slots: 64 leaves room for cursors.
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 20);
    h.ok("DELETE FROM t WHERE id <= 40");
    assert!(h.one("PRAGMA freelist_count") > 0);
    // A fresh connection: nothing cached, the trunk included.
    let c2 = h.connect();
    h.exec_on(&c2, "BEGIN", &[]).unwrap();
    h.exec_on(&c2, "SAVEPOINT s", &[]).unwrap();
    h.exec_on(&c2, "UPDATE t SET n = 1 WHERE id = 80", &[])
        .unwrap();
    let pager = c2.pager.load().clone();
    let pager1 = h.conn.pager.load().clone();
    let free_id = int(&h.exec_on(&c2, "PRAGMA page_count", &[]).unwrap()[0][0]) as usize;
    let trunk_id = {
        // Page 1 is cached and loaded on c2 now; read the trunk pointer.
        let mut id = 0usize;
        h.r.run(|| {
            id = pager
                .with_header(|hd| hd.freelist_trunk_page.get() as usize)
                .ok()
                .and_then(|r| match r {
                    IOResult::Done(v) => Some(v),
                    IOResult::IO(_) => None,
                })
                .expect("page 1 cached");
        });
        id
    };
    assert!(trunk_id > 0);
    assert!(
        !pager.stream_test_loaded(trunk_id),
        "trunk must start uncached"
    );
    let mut squeezed_recheck = false;
    let mut done = false;
    for _ in 0..10_000 {
        let reads_before = h.stats().reads;
        let parks_before = h.stats().parks;
        let res = h.r.run(|| {
            let mut squeezed = false;
            if !squeezed_recheck
                && pager.stream_test_free_page_state() == "AddToTrunk"
                && pager.stream_test_loaded(trunk_id)
            {
                // The trunk read finished: give the slots away now. The
                // arena is shared, so empty the other connection's cache
                // too (a reserve evicts from it).
                pager1.stream_test_squeeze_claimed(None);
                pager.stream_test_squeeze_claimed(Some(trunk_id));
                squeezed = true;
            }
            let r = pager.free_page(None, free_id);
            (squeezed, r)
        });
        let (squeezed, r) = res;
        match r {
            Ok(IOResult::Done(())) => {
                done = true;
                break;
            }
            Ok(IOResult::IO(_)) => {
                if squeezed {
                    assert_eq!(
                        pager.stream_test_free_page_state(),
                        "AddToTrunk",
                        "state unchanged on the re-check"
                    );
                    let s = h.stats();
                    assert_eq!(s.reads, reads_before, "the re-check issues no read");
                    assert!(s.parks > parks_before, "the re-check parks");
                    squeezed_recheck = true;
                }
            }
            Err(e) => panic!("free_page failed: {e}"),
        }
    }
    assert!(
        squeezed_recheck,
        "the yield between the Start reserve and add_dirty(trunk) was exercised"
    );
    assert!(done, "free_page finished after the park");
    h.check_invariants();
    h.exec_on(&c2, "ROLLBACK", &[]).unwrap();
    h.integrity();
}

/// §14 fork test `update_50k_pages_fails_constraint_in_1024_slot_arena`:
/// an UPDATE over 50k pages inside a transaction, in a 1,024-slot arena,
/// that violates a constraint near its end. The statement fails with
/// SQLITE_CONSTRAINT, the rollback restores 50k pre-images from scratch
/// over many runs, the transaction stays usable, and the heap stays under
/// the arena plus the index plus a constant.
#[test]
fn update_50k_pages_fails_constraint_in_1024_slot_arena() {
    let mut h = H::open(Cfg {
        slots: 1024,
        count_heap: true,
        ..Cfg::default()
    });
    h.fill("t", 50_000);
    let rows = 200_000;
    let before = h.stats();
    h.ok("BEGIN");
    let base = heap_reset_peak();
    let err = h
        .exec(&format!(
            "UPDATE t SET n = CASE WHEN id = {} THEN NULL ELSE n + 1 END",
            rows - 10
        ))
        .expect_err("NOT NULL violated near the end");
    let peak = heap_peak() - base;
    assert_eq!(err.sqlite_result_code(), 19, "SQLITE_CONSTRAINT, got {err}");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 0, "pre-statement state");
    h.ok("COMMIT");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 0);
    let s = h.stats();
    assert!(s.records - before.records >= 49_000, "{s:?}");
    assert!(s.restored_pages - before.restored_pages >= 49_000, "{s:?}");
    // Arena slots are caller memory; heap: index (4 B/record) + constant.
    let bound = 4 * 65_536 + 16 * 1024 * 1024;
    eprintln!(
        "update_50k: heap peak {peak} B (bound {bound}), runs {}, {s:?}",
        h.r.runs
    );
    assert!(peak < bound as isize, "heap peak {peak} over {bound}");
    h.check_invariants();
}

/// Review C1: `ROLLBACK TO b` then `ROLLBACK TO a` over the same page puts
/// back the image from when `a` was taken, not the one from `b`. Both the
/// SQL path (the second rollback waits for the first restore) and two
/// rollbacks in one run with no gate in between (the pending restore is
/// merged into the new one).
#[test]
fn nested_rollback_to_same_page_restores_outer_image() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 40);
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    h.ok("UPDATE t SET n = 1 WHERE id = 5");
    h.ok("SAVEPOINT b");
    h.ok("UPDATE t SET n = 2 WHERE id = 5");
    h.ok("ROLLBACK TO b");
    h.ok("ROLLBACK TO a");
    h.ok("COMMIT");
    assert_eq!(h.one("SELECT n FROM t WHERE id = 5"), 0);

    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    h.ok("UPDATE t SET n = 1 WHERE id = 5");
    h.ok("SAVEPOINT b");
    h.ok("UPDATE t SET n = 2 WHERE id = 5");
    let pager = h.conn.pager.load().clone();
    h.r.run(|| {
        pager
            .rollback_to_named_savepoint("b")
            .expect("b")
            .expect("b exists");
        pager
            .rollback_to_named_savepoint("a")
            .expect("a")
            .expect("a exists");
    });
    assert_eq!(h.one("SELECT n FROM t WHERE id = 5"), 0);
    h.ok("COMMIT");
    assert_eq!(h.one("SELECT n FROM t WHERE id = 5"), 0);
    assert_eq!(h.one("SELECT sum(n) FROM t"), 0);
    h.integrity();
}

/// Review M1/M4: a savepoint restore that runs out of slots every other
/// run parks and resumes (the page-1 header read re-entered before its
/// read landed included) instead of asserting.
#[test]
fn rollback_parks_and_resumes_without_assert() {
    let mut h = H::open(Cfg {
        slots: 48,
        ..Cfg::default()
    });
    h.fill("t", 200);
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    h.ok("UPDATE t SET n = n + 1");
    let before = h.stats();
    h.squeeze_every = 2;
    h.ok("ROLLBACK TO a");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 0);
    h.squeeze_every = 0;
    let s = h.stats();
    assert!(s.restored_pages > before.restored_pages, "{s:?}");
    assert!(s.parks > before.parks, "parked: {s:?}");
    h.ok("COMMIT");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 0);
    h.integrity();
}

/// Review C7: a savepoint restore that cannot finish (the store fails its
/// scratch reads) aborts the transaction on the store and rolls the
/// connection back whole; nothing of it commits.
#[test]
fn rollback_that_cannot_finish_aborts_the_txn() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 40);
    let head = h.r.store.head();
    h.ok("BEGIN");
    h.ok("UPDATE t SET n = 5 WHERE id <= 8");
    h.ok("SAVEPOINT a");
    h.ok("UPDATE t SET n = n + 1");
    h.r.store.fail_scratch_reads = true;
    let before = h.stats();
    // The rollback itself only queues the restore; the statement that
    // next touches a page finds the restore failed.
    let res = h
        .exec("ROLLBACK TO a")
        .and_then(|_| h.exec("SELECT sum(n) FROM t"));
    let err = res.expect_err("the restore fails");
    h.r.store.fail_scratch_reads = false;
    assert!(
        err.to_string().contains("stream"),
        "the restore's read error, got {err}"
    );
    let s = h.stats();
    assert!(
        s.doomed > before.doomed && s.aborts > before.aborts,
        "{s:?}"
    );
    assert!(h.conn.get_auto_commit(), "the transaction was rolled back");
    assert_eq!(h.r.store.head(), head, "nothing committed");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 0);
    // The connection writes again.
    h.ok("UPDATE t SET n = 1 WHERE id = 1");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 1);
    h.integrity();
}

/// Review C3: a reader whose version was trimmed before its pin landed
/// fails that statement with SQLITE_BUSY; the handle (and the writer) is
/// fine and the reader's next statement reads the new head.
#[test]
fn trimmed_pin_fails_only_that_statement_busy() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 10);
    let c2 = h.connect();
    h.r.store.trimmed_below = h.r.store.head() + 1;
    let err = h
        .exec_on(&c2, "SELECT count(*) FROM t", &[])
        .expect_err("the version is gone");
    assert_eq!(err.sqlite_result_code(), 5, "SQLITE_BUSY, got {err}");
    h.r.store.trimmed_below = 0;
    h.ok("UPDATE t SET n = 1 WHERE id = 1");
    let rows = h.exec_on(&c2, "SELECT sum(n) FROM t", &[]).unwrap();
    assert_eq!(int(&rows[0][0]), 1);
    assert_eq!(h.one("SELECT count(*) FROM t"), 40);
    h.check_invariants();
}

/// Review: `cache_insert` in stream mode accepts the page already cached
/// (a re-entry) and refuses a second `Page` for the same id.
#[test]
fn stream_cache_insert_refuses_a_second_page_object() {
    let mut h = H::open(Cfg::default());
    h.fill("t", 2);
    let pager = h.conn.pager.load().clone();
    let cached = pager.stream_test_cached(1).expect("page 1 is cached");
    assert!(pager.stream_test_cache_insert(1, cached).is_ok());
    let other = Arc::new(crate::storage::pager::Page::new(1));
    assert!(pager.stream_test_cache_insert(1, other).is_err());
}

/// Review C4/C5: with the fewest credits writes need, and an escrow that
/// is topped up only a little at a time and then shrinks, every run stays
/// within its credits (the runner checks), the store is never overdrawn
/// (it panics), and a transaction past the grant fails SQLITE_FULL and
/// leaves the committed state alone.
#[test]
fn low_credits_and_shrinking_grant() {
    let mut h = H::open(Cfg {
        slots: 64,
        credits: super::MIN_CREDITS,
        quota: 4_000,
        ..Cfg::default()
    });
    h.fill("t", 100);
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    h.ok("UPDATE t SET n = n + 1");
    h.ok("ROLLBACK TO a");
    h.ok("UPDATE t SET n = 2 WHERE id <= 40");
    h.ok("COMMIT");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 80);
    let head = h.r.store.head();
    // The grant shrinks to a few pages: a large transaction cannot fit.
    h.r.store.allowance = Some(8);
    h.ok("BEGIN");
    let res = h.exec("UPDATE t SET n = 9").and_then(|_| h.exec("COMMIT"));
    let err = res.expect_err("past the grant");
    assert!(is_full(&err), "expected SQLITE_FULL, got {err}");
    if !h.conn.get_auto_commit() {
        h.ok("ROLLBACK");
    }
    assert_eq!(h.r.store.head(), head, "nothing committed");
    h.r.store.allowance = Some(4_000);
    assert_eq!(h.one("SELECT sum(n) FROM t"), 80);
    h.ok("UPDATE t SET n = 0");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 0);
    h.integrity();
    // The runner reported the grant less the held BEGIN and the reads in
    // flight, as the host does (round-2 M2: the writer used to park
    // forever at the minimum once it did).
    assert!(
        h.r.short_runs > 0,
        "no run saw fewer credits than the grant"
    );
}

// ---- round-2 review --------------------------------------------------------

/// A standalone database over its own arena (no SQL), for op-level tests.
fn bare(slots: u32, quota: u64) -> (Arc<StreamDb>, MemArena) {
    let mut arena = MemArena::new(slots);
    let db = unsafe {
        StreamDb::new(
            arena.base(),
            slots,
            0,
            StreamConfig {
                scratch_pages: 1024,
                quota_pages: quota,
            },
        )
    };
    (db, arena)
}

fn page_buf(db: &StreamDb) -> Arc<crate::io::Buffer> {
    Arc::new(db.pool().try_get_page().expect("a free slot"))
}

/// Round-2 H1: a reader's statement, and a sibling statement on the
/// writer's own connection, finishing between the writer's yields leave
/// the writer's claim (slots and held credits) alone. Every run steps the
/// writer's UPDATE and the other statement, as a guest's scheduler does.
#[test]
fn other_statements_ending_keep_the_writers_claim() {
    let mut h = H::open(Cfg {
        slots: 64,
        credits: super::MIN_CREDITS,
        ..Cfg::default()
    });
    h.fill("t", 300);
    let reader = h.connect();
    let conn = h.conn.clone();
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    let mut update = h.r.run(|| conn.prepare("UPDATE t SET n = n + 1")).unwrap();
    // (statement, its connection is the writer's, rows seen)
    let mut other: Option<(crate::Statement, bool, i64)> = None;
    let (mut ended, mut sibling_ended) = (0u32, 0u32);
    // Ends of the other statement while the writer held a claim; the
    // claim must still be there after.
    let mut ended_under_claim = 0u32;
    let sdb = h.sdb.clone();
    let mut update_done = false;
    for i in 0.. {
        assert!(i < MAX_RUNS, "no progress: {}", h.sdb.test_credit_state());
        let step = |s: &mut crate::Statement, rows: &mut i64| -> bool {
            loop {
                match s.step().expect("step") {
                    StepResult::Row => *rows += 1,
                    StepResult::Done => return true,
                    StepResult::IO | StepResult::Yield => return false,
                    o => panic!("unexpected step result {o:?}"),
                }
            }
        };
        let finished = h.r.run(|| {
            if !update_done {
                update_done = step(&mut update, &mut 0);
            }
            if other.is_none() && !update_done {
                let sibling = (ended + sibling_ended) % 2 == 1;
                let (c, sql) = if sibling {
                    (&conn, "SELECT count(*) FROM t WHERE id <= 8")
                } else {
                    (&reader, "SELECT count(*) FROM t")
                };
                other = Some((c.prepare(sql).expect("prepare"), sibling, 0));
            }
            if let Some((s, sibling, rows)) = other.as_mut() {
                let claims_before = sdb.test_claims();
                if step(s, rows) {
                    if !claims_before.is_empty() {
                        let after = sdb.test_claims();
                        for (k, _) in &claims_before {
                            assert!(
                                after.iter().any(|(k2, _)| k2 == k),
                                "claim {k:?} cleared by another statement's end"
                            );
                        }
                        ended_under_claim += 1;
                    }
                    assert_eq!(*rows, 1);
                    if *sibling {
                        sibling_ended += 1;
                    } else {
                        ended += 1;
                    }
                    other = None;
                }
            }
            update_done && other.is_none()
        });
        h.check_invariants();
        if finished {
            break;
        }
    }
    drop(update);
    assert!(
        ended > 0 && sibling_ended > 0,
        "statements ended mid-update: reader {ended}, sibling {sibling_ended}"
    );
    assert!(
        ended_under_claim > 0,
        "no statement ended under the writer's claim"
    );
    h.ok("COMMIT");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 1200);
    let rows = h.exec_on(&reader, "SELECT sum(n) FROM t", &[]).unwrap();
    assert_eq!(int(&rows[0][0]), 1200);
    h.integrity();
}

/// Round-2 M1: the last holder of a version leaving while its PIN is in
/// flight sends UNPIN only once the PIN succeeds; a PIN refused (the
/// version trimmed) is never unpinned. The store panics on an UNPIN of a
/// version it did not pin.
#[test]
fn release_while_pin_in_flight_unpins_only_after_success() {
    for trimmed in [false, true] {
        let (db, _arena) = bare(16, u64::MAX / 2);
        let mut store = MemStore::new();
        store.read_delay = 0;
        if trimmed {
            store.trimmed_below = 1;
        }
        let mut r = MemRunner::new(db.clone(), store);
        let page = Arc::new(crate::storage::pager::Page::new(1));
        r.run(|| {
            db.hold(0);
            let buf = page_buf(&db);
            let c = super::wal::page_read_completion(page.clone(), 1, buf.clone());
            let issued = db.read(super::ReadAt::Version(0), 0, &buf, c).unwrap();
            assert!(issued.is_some(), "the read goes out");
            db.keep(buf);
            db.release(0);
            assert_eq!(db.test_pins(), vec![(0, 0, true)], "the PIN decides");
        });
        assert_eq!(r.store.pins().len(), usize::from(!trimmed));
        // The PIN's completion lands: success lets go, LOST forgets.
        r.run(|| {});
        assert!(db.test_pins().is_empty(), "trimmed={trimmed}");
        r.run(|| {});
        assert!(
            r.store.pins().is_empty(),
            "trimmed={trimmed}: {:?}",
            r.store.pins()
        );
    }
}

/// Round-2 C2: cancelling a batch after the page-1 init committed in the
/// same run keeps the init's WRITE and BATCH, and gives back only the
/// cancelled writes' quota and credit.
#[test]
fn batch_cancel_keeps_the_page1_init() {
    let (db, _arena) = bare(16, 100);
    db.begin_run(16, 100);
    let p1 = page_buf(&db);
    assert!(db.batch_write(0, &p1).unwrap());
    assert_eq!(db.batch_commit().unwrap(), 1);
    let (a, b) = (page_buf(&db), page_buf(&db));
    assert!(db.batch_write(1, &a).unwrap());
    assert!(db.batch_write(2, &b).unwrap());
    db.batch_cancel();
    assert_eq!(db.quota_left(), 99, "only the init's page is spent");
    assert_eq!(db.credits(), 15, "only the init's BATCH credit is spent");
    let mut ops = Vec::new();
    db.take_ops(&mut ops);
    let kinds: Vec<(u32, u64)> = ops.iter().map(|o| (o.kind, o.page)).collect();
    assert_eq!(kinds, vec![(super::op::WRITE, 0), (super::op::BATCH, 0)]);
    assert_eq!(ops[1].at, 1);
    drop(ops);
    db.release_run();
}

/// Round-2 C8: a read that fails to go out (the handle failed) unlocks
/// the page it locked.
#[test]
fn read_frame_error_unlocks_the_page() {
    use crate::storage::wal::Wal;
    let (db, _arena) = bare(16, u64::MAX / 2);
    db.begin_run(16, u64::MAX / 2);
    // A write-side op failing fails the handle closed.
    db.complete(999, super::err::IO);
    let wal = super::wal::StreamWal::new(db.clone());
    let page = Arc::new(crate::storage::pager::Page::new(1));
    let res = wal.read_frame(1, page.clone(), db.pool().clone(), None);
    assert!(res.is_err(), "the failed handle refuses the read");
    assert!(!page.is_locked(), "the page is unlocked again");
    db.release_run();
}

/// Round-2 C9: a second `begin_read_tx` across a head move holds only
/// the new version; `end_read_tx` lets go of it.
#[test]
fn begin_read_tx_twice_moves_the_hold() {
    use crate::storage::wal::Wal;
    let (db, _arena) = bare(16, u64::MAX / 2);
    db.begin_run(16, u64::MAX / 2);
    let wal = super::wal::StreamWal::new(db.clone());
    wal.begin_read_tx().unwrap();
    assert_eq!(db.test_pins(), vec![(0, 1, false)]);
    let p1 = page_buf(&db);
    assert!(db.batch_write(0, &p1).unwrap());
    assert_eq!(db.batch_commit().unwrap(), 1);
    assert!(wal.begin_read_tx().unwrap(), "the head moved");
    assert_eq!(db.test_pins(), vec![(1, 1, false)], "only the new version");
    wal.end_read_tx();
    assert!(db.test_pins().is_empty());
    let mut ops = Vec::new();
    db.take_ops(&mut ops);
    assert!(
        ops.iter().all(|o| o.kind != super::op::UNPIN),
        "nothing was pinned"
    );
    drop(ops);
    db.release_run();
}

/// Round-2 C7 (spec case): with no quota left, a savepoint restore can't
/// make room (the spill cap allows no page out, so its `ensure_slots`
/// fails SQLITE_FULL). The transaction is doomed and aborted on the
/// store, the statement fails SQLITE_FULL, and nothing of it commits.
#[test]
fn quota_refusing_a_restore_dooms_the_txn() {
    let mut h = H::open(Cfg {
        slots: 64,
        quota: 100_000,
        ..Cfg::default()
    });
    h.fill("t", 100);
    let head = h.r.store.head();
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    h.ok("UPDATE t SET n = n + 1");
    let before = h.stats();
    h.r.store.allowance = Some(0);
    let res = h
        .exec("ROLLBACK TO a")
        .and_then(|_| h.exec("SELECT sum(n) FROM t"));
    let err = res.expect_err("the restore cannot spill");
    assert!(is_full(&err), "expected SQLITE_FULL, got {err}");
    let s = h.stats();
    assert!(
        s.doomed > before.doomed && s.aborts > before.aborts,
        "{s:?}"
    );
    assert!(h.conn.get_auto_commit(), "the transaction was rolled back");
    assert_eq!(h.r.store.head(), head, "nothing committed");
    h.r.store.allowance = Some(100_000);
    assert_eq!(h.one("SELECT sum(n) FROM t"), 0);
    h.ok("UPDATE t SET n = 1 WHERE id = 1");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 1);
    h.integrity();
}

/// Round-3 B1: a trigger steps inside its parent's step. The parent's
/// reserves after the trigger are its own again, and the trigger's claim
/// ends with its step: a small arena makes progress and no claim is left.
#[test]
fn trigger_inside_a_writer_keeps_claims_apart() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 100);
    h.ok("CREATE TABLE log(x INTEGER)");
    h.ok("CREATE TRIGGER tr BEFORE UPDATE ON t BEGIN INSERT INTO log VALUES (old.id); END");
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    h.ok("UPDATE t SET n = n + 1");
    assert!(h.sdb.test_claims().is_empty(), "{:?}", h.sdb.test_claims());
    h.ok("COMMIT");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 400);
    assert_eq!(h.one("SELECT count(*) FROM log"), 400);
    h.integrity();
}

/// Round-3 B2: a writer handing out rows (RETURNING runs all its DML
/// first) holds no claim, so a query on its own connection, run to the
/// end before the writer is stepped again, makes progress.
#[test]
fn returning_rows_hold_no_claim() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 100);
    let conn = h.conn.clone();
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    let mut stmt =
        h.r.run(|| conn.prepare("UPDATE t SET n = n + 1 RETURNING id"))
            .unwrap();
    let mut rows = 0i64;
    let mut first = true;
    for i in 0.. {
        assert!(i < MAX_RUNS, "the update made no progress");
        let st = h.r.run(|| loop {
            match stmt.step().expect("step") {
                StepResult::Row => return Some(true),
                StepResult::Done => return None,
                StepResult::IO | StepResult::Yield => return Some(false),
                o => panic!("unexpected step result {o:?}"),
            }
        });
        match st {
            None => break,
            Some(false) => {}
            Some(true) => {
                rows += 1;
                if first {
                    first = false;
                    assert!(h.sdb.test_claims().is_empty(), "{:?}", h.sdb.test_claims());
                    let got = h.exec_on(&conn, "SELECT sum(n) FROM t", &[]).unwrap();
                    assert_eq!(int(&got[0][0]), 400);
                }
            }
        }
    }
    drop(stmt);
    assert_eq!(rows, 400);
    h.ok("COMMIT");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 400);
    h.integrity();
}

/// Round-3 C9: a second `begin_read_tx` across a head move after the old
/// version was pinned sends exactly one UNPIN of it (the store panics on
/// an UNPIN it did not pin) and holds only the new version.
#[test]
fn begin_read_tx_twice_unpins_the_old_version() {
    use crate::storage::wal::Wal;
    let (db, _arena) = bare(16, u64::MAX / 2);
    let mut store = MemStore::new();
    store.read_delay = 0;
    let mut r = MemRunner::new(db.clone(), store);
    let wal = super::wal::StreamWal::new(db.clone());
    let page = Arc::new(crate::storage::pager::Page::new(1));
    r.run(|| {
        wal.begin_read_tx().unwrap();
        let buf = page_buf(&db);
        let c = super::wal::page_read_completion(page.clone(), 1, buf.clone());
        assert!(db
            .read(super::ReadAt::Version(0), 0, &buf, c)
            .unwrap()
            .is_some());
        db.keep(buf);
    });
    r.run(|| {});
    assert_eq!(db.test_pins(), vec![(0, 1, false)]);
    assert_eq!(r.store.pins().get(&0), Some(&1));
    r.run(|| {
        let p1 = page_buf(&db);
        assert!(db.batch_write(0, &p1).unwrap());
        assert_eq!(db.batch_commit().unwrap(), 1);
        assert!(wal.begin_read_tx().unwrap(), "the head moved");
    });
    assert_eq!(db.test_pins(), vec![(1, 1, false)], "only the new version");
    assert!(
        r.store.pins().is_empty(),
        "version 0 unpinned once: {:?}",
        r.store.pins()
    );
    r.run(|| wal.end_read_tx());
    assert!(db.test_pins().is_empty());
}

// ---- final review ----------------------------------------------------------

/// Run `sql` on `conn` for at most `runs` runs. `Ok(true)`: it finished.
fn step_for(
    h: &mut H,
    stmt: &mut crate::Statement,
    runs: u64,
) -> crate::Result<bool> {
    for _ in 0..runs {
        let done = h.r.run(|| -> crate::Result<bool> {
            loop {
                match stmt.step()? {
                    StepResult::Row => {}
                    StepResult::Done => return Ok(true),
                    StepResult::IO | StepResult::Yield => return Ok(false),
                    o => panic!("unexpected step result {o:?}"),
                }
            }
        })?;
        if done {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Final review C1: a ROLLBACK TO that fails part way (a grown page is
/// locked by a read in flight, so the cache can't drop it) dooms the
/// transaction: a COMMIT after it persists none of the rolled-back pages.
#[test]
fn failed_rollback_dooms_the_txn() {
    let mut h = H::open(Cfg::default());
    h.fill("t", 10);
    let size = h.one("PRAGMA page_count");
    let head = h.r.store.head();
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    h.ok(
        "INSERT INTO t(id, n, v) WITH RECURSIVE c(i) AS (SELECT 1000 UNION ALL SELECT i + 1 FROM c WHERE i < 1080) \
         SELECT i, 1, zeroblob(900) FROM c",
    );
    let grown = h.one("PRAGMA page_count");
    assert!(grown > size + 10, "grew: {size} -> {grown}");
    let pager = h.conn.pager.load().clone();
    let pinned = pager
        .stream_test_pin_above(size as usize)
        .expect("a grown page is resident");
    let before = h.stats();
    let err = h.exec("ROLLBACK TO a").expect_err("the cache can't drop it");
    // The rollback may have dropped the pins with the page.
    pinned.try_unpin();
    pinned.try_unpin();
    assert!(h.stats().doomed > before.doomed, "{err}: {:?}", h.stats());
    let _ = h.exec("COMMIT");
    if !h.conn.get_auto_commit() {
        h.ok("ROLLBACK");
    }
    assert_eq!(h.r.store.head(), head, "nothing committed");
    assert_eq!(h.one("PRAGMA page_count"), size);
    assert_eq!(h.one("SELECT count(*) FROM t"), 40);
    h.integrity();
}

/// Final review C2: a stream has one page size. Any other one is refused
/// on an empty database, and the database is created at 4096.
#[test]
fn stream_refuses_other_page_sizes() {
    let mut h = H::open(Cfg::default());
    for size in [8192, 1024, 65536, 1000] {
        let err = h
            .exec(&format!("PRAGMA page_size = {size}"))
            .expect_err("only 4096");
        assert!(err.to_string().contains("page size"), "{size}: {err}");
    }
    h.ok("PRAGMA page_size = 4096");
    h.fill("t", 4);
    assert_eq!(h.one("PRAGMA page_size"), 4096);
    h.integrity();
}

/// Final review C3: a run whose free credits stage no spill (here the
/// grant itself is 1) parks the writer instead of failing it SQLITE_FULL;
/// a later run with the full grant finishes it.
#[test]
fn short_credit_spill_parks_not_full() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 100);
    let conn = h.conn.clone();
    h.ok("BEGIN");
    let mut stmt = h.r.run(|| conn.prepare("UPDATE t SET n = 1")).unwrap();
    let waits = h.stats().credit_waits;
    h.r.credits = 1;
    let done = step_for(&mut h, &mut stmt, 20).expect("parks, not FULL");
    assert!(!done, "can't finish on one credit a run");
    assert!(h.stats().credit_waits > waits, "{:?}", h.stats());
    h.r.credits = super::DEFAULT_CREDITS;
    assert!(step_for(&mut h, &mut stmt, MAX_RUNS).unwrap());
    drop(stmt);
    h.ok("COMMIT");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 400);
    h.integrity();
}

/// Final review M1 (and reset ending a claim): a trigger waiting on IO
/// inside its parent's step holds a claim under its own owner; resetting
/// the parent ends it, so the connection's next writer is not starved.
#[test]
fn parent_reset_ends_its_triggers_claim() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 4);
    h.fill("big", 100);
    h.ok("CREATE TABLE log(x INTEGER, v BLOB)");
    h.ok("CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log SELECT id, v FROM big; END");
    let conn = h.conn.clone();
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    let mut stmt = h
        .r
        .run(|| conn.prepare("UPDATE t SET n = 1 WHERE id = 1"))
        .unwrap();
    let pager = conn.pager.load().clone();
    let mut nested = false;
    for _ in 0..MAX_RUNS {
        assert!(!step_for(&mut h, &mut stmt, 1).unwrap(), "finished first");
        if pager.stream_test_parents() > 0 && !h.sdb.test_claims().is_empty() {
            nested = true;
            break;
        }
    }
    assert!(nested, "the trigger never stopped mid-IO with a claim");
    // Its IO may still be in flight: a stream reset does not wait for it.
    h.r.run(|| stmt.reset()).unwrap();
    assert!(h.sdb.test_claims().is_empty(), "{:?}", h.sdb.test_claims());
    assert_eq!(pager.stream_test_parents(), 0);
    drop(stmt);
    h.ok("UPDATE big SET n = 2");
    h.ok("ROLLBACK");
    h.integrity();
}

/// An error part way through a step ends that statement's claim.
#[test]
fn error_mid_step_clears_the_claim() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.ok("CREATE TABLE u(id INTEGER PRIMARY KEY, n INTEGER CHECK (n < 300), v BLOB)");
    h.ok(
        "INSERT INTO u WITH RECURSIVE c(i) AS (SELECT 1 UNION ALL SELECT i + 1 FROM c WHERE i < 400) \
         SELECT i, 0, zeroblob(900) FROM c",
    );
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    let err = h.exec("UPDATE u SET n = id").expect_err("CHECK fails at 300");
    assert!(!is_full(&err), "{err}");
    assert!(h.sdb.test_claims().is_empty(), "{:?}", h.sdb.test_claims());
    h.ok("UPDATE u SET n = 1 WHERE id <= 200");
    h.ok("COMMIT");
    assert_eq!(h.one("SELECT sum(n) FROM u"), 200);
    h.integrity();
}

/// `hold_can_fit`: a claim whose hold, plus a read and a pin, fits no
/// run's credits is refused.
#[test]
fn hold_can_fit_is_bounded_by_the_grant() {
    let (db, _arena) = bare(16, u64::MAX / 2);
    let mut r = MemRunner::new(db.clone(), MemStore::new());
    assert!(db.hold_can_fit(1 << 20), "no run seen yet");
    r.credits = super::MIN_CREDITS;
    r.run(|| {});
    // BEGIN + one part's closing op + 2 = 4.
    assert!(db.hold_can_fit(1));
    assert!(db.hold_can_fit(1024));
    assert!(!db.hold_can_fit(1025));
    r.credits = 8;
    r.run(|| {});
    assert!(db.hold_can_fit(4 * 1024));
    assert!(!db.hold_can_fit(5 * 1024 + 1));
}

/// A reserve makes room before it claims: with the fewest credits and a
/// small arena, a savepoint's records and the spills that make room for
/// them share every run, and nothing fails SQLITE_FULL.
#[test]
fn reserve_makes_room_before_claiming() {
    let mut h = H::open(Cfg {
        slots: 64,
        credits: super::MIN_CREDITS,
        ..Cfg::default()
    });
    h.fill("t", 100);
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    h.ok("UPDATE t SET n = n + 1");
    h.ok("COMMIT");
    let s = h.stats();
    assert!(s.spilled_pages > 0 && s.records > 0, "{s:?}");
    assert_eq!(s.reserve_full, 0, "{s:?}");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 400);
    h.integrity();
}

/// Round-2 M5: a dirty page whose read failed dooms the transaction (its
/// bytes are lost); the rollback leaves the committed state alone.
#[test]
fn failed_read_of_a_dirty_page_dooms_the_txn() {
    let mut h = H::open(Cfg::default());
    h.fill("t", 10);
    let head = h.r.store.head();
    h.ok("BEGIN");
    h.ok("UPDATE t SET n = 3 WHERE id = 1");
    let pager = h.conn.pager.load().clone();
    let before = h.stats();
    let err = h.r.run(|| pager.stream_test_fail_dirty_read()).expect_err("dooms");
    assert!(err.to_string().contains("dirty page"), "{err}");
    assert!(h.stats().doomed > before.doomed);
    assert!(h.exec("SELECT sum(n) FROM t").is_err(), "doomed");
    if !h.conn.get_auto_commit() {
        h.ok("ROLLBACK");
    }
    assert_eq!(h.r.store.head(), head, "nothing committed");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 0);
    h.integrity();
}

// ---- final review, round 2 -------------------------------------------------

fn integrity_on(h: &mut H, conn: &Arc<Connection>) {
    let rows = h
        .exec_on(conn, "PRAGMA integrity_check", &[])
        .expect("integrity_check");
    let text: Vec<String> = rows.iter().map(|r| format!("{:?}", r[0])).collect();
    assert!(
        text.len() == 1 && text[0].contains("ok"),
        "integrity_check: {text:?}"
    );
}

const BIG_INSERT: &str = "INSERT INTO t(id, n, v) WITH RECURSIVE c(i) AS (SELECT 1000 UNION ALL SELECT i + 1 FROM c WHERE i < 2200) \
     SELECT i, 1, zeroblob(900) FROM c";

/// C1/S1: a reader's ROLLBACK TO (its savepoint saw an old size) while a
/// writer's transaction has spilled parts leaves that transaction alone:
/// the writer's COMMIT is whole and a fresh connection reads it intact.
#[test]
fn reader_rollback_to_keeps_the_writers_txn() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 10);
    let c2 = h.connect();
    h.exec_on(&c2, "SAVEPOINT r", &[]).unwrap();
    h.exec_on(&c2, "SELECT count(*) FROM t", &[]).unwrap();
    h.ok("BEGIN");
    h.ok(BIG_INSERT);
    assert!(h.stats().spilled_pages > 0, "{:?}", h.stats());
    let discards = h.stats().discards;
    h.exec_on(&c2, "ROLLBACK TO r", &[]).unwrap();
    h.exec_on(&c2, "ROLLBACK", &[]).unwrap();
    assert_eq!(h.stats().discards, discards, "the reader discarded nothing");
    assert!(h.sdb.txn_open(), "the writer's transaction is still open");
    h.ok("COMMIT");
    let c3 = h.connect();
    let rows = h.exec_on(&c3, "SELECT count(*) FROM t", &[]).unwrap();
    assert_eq!(int(&rows[0][0]), 40 + 1201);
    integrity_on(&mut h, &c3);
    h.integrity();
}

/// C2: a reader that is doomed gives up only itself; the writer's
/// transaction stays open and commits whole.
#[test]
fn a_doomed_reader_leaves_the_writers_txn() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 10);
    let c2 = h.connect();
    h.exec_on(&c2, "BEGIN", &[]).unwrap();
    h.exec_on(&c2, "SELECT count(*) FROM t", &[]).unwrap();
    h.ok("BEGIN");
    h.ok(BIG_INSERT);
    assert!(h.sdb.txn_open());
    let aborts = h.stats().aborts;
    c2.pager.load().stream_test_doom();
    assert!(h.sdb.txn_open(), "the reader aborted the writer's transaction");
    assert_eq!(h.stats().aborts, aborts);
    assert!(h.exec_on(&c2, "SELECT count(*) FROM t", &[]).is_err());
    if !c2.get_auto_commit() {
        h.exec_on(&c2, "ROLLBACK", &[]).unwrap();
    }
    h.ok("COMMIT");
    let rows = h.exec_on(&c2, "SELECT count(*) FROM t", &[]).unwrap();
    assert_eq!(int(&rows[0][0]), 40 + 1201);
    integrity_on(&mut h, &c2);
}

/// C2: a writer whose store transaction was aborted under it (its staged
/// parts are gone) fails its COMMIT; it never commits the rest as a
/// plain batch.
#[test]
fn an_aborted_txn_is_never_acked_as_a_batch() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 10);
    let head = h.r.store.head();
    h.ok("BEGIN");
    h.ok(BIG_INSERT);
    assert!(h.stats().spilled_pages > 0);
    h.r.run(|| h.sdb.txn_abort());
    let batches = h.stats().batches;
    h.exec("COMMIT").expect_err("its parts are gone");
    assert_eq!(h.stats().batches, batches, "no plain batch went out");
    if !h.conn.get_auto_commit() {
        h.ok("ROLLBACK");
    }
    assert_eq!(h.r.store.head(), head, "nothing committed");
    assert_eq!(h.one("SELECT count(*) FROM t"), 40);
    h.integrity();
}

/// C3: resetting a writer mid-IO whose statement rollback fails (a grown
/// page is pinned) dooms the transaction, and the abort rolls it back
/// whole: the connection is in autocommit again with nothing committed.
#[test]
fn reset_mid_io_rolls_back_a_doomed_txn() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 10);
    let size = h.one("PRAGMA page_count") as usize;
    let head = h.r.store.head();
    let conn = h.conn.clone();
    h.ok("BEGIN");
    h.ok("UPDATE t SET n = 1 WHERE id = 1");
    let mut stmt = h.r.run(|| conn.prepare(BIG_INSERT)).unwrap();
    let pager = conn.pager.load().clone();
    let mut pinned = None;
    for _ in 0..MAX_RUNS {
        assert!(!step_for(&mut h, &mut stmt, 1).unwrap(), "finished first");
        pinned = pager.stream_test_pin_above(size);
        if pinned.is_some() {
            break;
        }
    }
    let pinned = pinned.expect("the insert grew the database");
    let doomed = h.stats().doomed;
    let _ = h.r.run(|| stmt.reset());
    // The rollback may have dropped the pins with the page.
    pinned.try_unpin();
    pinned.try_unpin();
    drop(stmt);
    assert!(h.stats().doomed > doomed, "{:?}", h.stats());
    assert!(conn.get_auto_commit(), "abort rolled the transaction back");
    assert_eq!(h.r.store.head(), head, "nothing committed");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 0);
    assert_eq!(h.one("SELECT count(*) FROM t"), 40);
    h.integrity();
}

/// C4: credit parks are bounded. With a grant that never comes back the
/// writer fails SQLITE_FULL after about `CREDIT_PARK_LIMIT` runs instead
/// of parking for ever, and nothing is committed.
#[test]
fn credit_parks_are_bounded() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 100);
    let head = h.r.store.head();
    let conn = h.conn.clone();
    h.ok("BEGIN");
    let mut stmt = h.r.run(|| conn.prepare("UPDATE t SET n = 1")).unwrap();
    h.r.credits = 1;
    let start = h.r.runs;
    let mut err = None;
    for _ in 0..1_000 {
        match step_for(&mut h, &mut stmt, 1) {
            Ok(false) => {}
            Ok(true) => panic!("finished on one credit a run"),
            Err(e) => {
                err = Some(e);
                break;
            }
        }
    }
    let used = h.r.runs - start;
    let err = err.expect("the parks are bounded");
    assert!(is_full(&err), "expected SQLITE_FULL, got {err}");
    assert!(used <= 4 * 64, "gave up after {used} runs");
    drop(stmt);
    h.r.credits = super::DEFAULT_CREDITS;
    if !h.conn.get_auto_commit() {
        h.ok("ROLLBACK");
    }
    assert_eq!(h.r.store.head(), head);
    assert_eq!(h.one("SELECT sum(n) FROM t"), 0);
    h.integrity();
}

/// C5: a grown page with a read in flight (locked) at ROLLBACK TO is
/// detached from the cache, not a reason to fail the rollback.
#[test]
fn rollback_detaches_a_locked_grown_page() {
    let mut h = H::open(Cfg::default());
    h.fill("t", 10);
    let size = h.one("PRAGMA page_count");
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    h.ok(BIG_INSERT);
    let grown = h.one("PRAGMA page_count");
    let pager = h.conn.pager.load().clone();
    assert!(pager.stream_test_lock(grown as usize, true), "last page resident");
    let doomed = h.stats().doomed;
    h.ok("ROLLBACK TO a");
    assert!(!pager.stream_test_lock(grown as usize, false), "detached");
    assert_eq!(h.stats().doomed, doomed);
    h.ok("COMMIT");
    assert_eq!(h.one("PRAGMA page_count"), size);
    assert_eq!(h.one("SELECT count(*) FROM t"), 40);
    h.integrity();
}

// ---- final review, round 3 (reviewer repros) -------------------------------

const BIG_INSERT2: &str = "INSERT INTO t(id, n, v) WITH RECURSIVE c(i) AS (SELECT 5000 UNION ALL SELECT i + 1 FROM c WHERE i < 6200) \
     SELECT i, 7, zeroblob(900) FROM c";

/// Step `sql` on `conn` to the end; `Err` names the failure.
fn rv_step_all(h: &mut H, conn: &Arc<Connection>, sql: &str) -> std::result::Result<(), String> {
    let mut stmt = h.r.run(|| conn.prepare(sql)).map_err(|e| e.to_string())?;
    for _ in 0..100_000 {
        let r = h.r.run(|| -> crate::Result<Option<StepResult>> {
            loop {
                match stmt.step()? {
                    StepResult::Row => {}
                    StepResult::IO | StepResult::Yield => return Ok(None),
                    o => return Ok(Some(o)),
                }
            }
        });
        match r {
            Ok(None) => {}
            Ok(Some(StepResult::Done)) => return Ok(()),
            Ok(Some(o)) => return Err(format!("{o:?}")),
            Err(e) => return Err(e.to_string()),
        }
    }
    Err("no progress".into())
}

/// A connection dropped (not closed) inside BEGIN after it spilled.
fn drop_a_spilled_writer(h: &mut H, sql: &str) {
    let c2 = h.connect();
    h.exec_on(&c2, "BEGIN", &[]).unwrap();
    h.exec_on(&c2, sql, &[]).unwrap();
    assert!(h.stats().spilled_pages > 0, "{:?}", h.stats());
    assert!(h.sdb.txn_open());
    drop(c2);
}

/// Rows of `t` with ids in `[lo, hi]`, read by a fresh connection.
fn fresh_count(h: &mut H, lo: i64, hi: i64) -> i64 {
    let c = h.connect();
    let rows = h
        .exec_on(&c, &format!("SELECT count(*) FROM t WHERE id BETWEEN {lo} AND {hi}"), &[])
        .unwrap();
    int(&rows[0][0])
}

/// Round 3 C1: a writer dropped mid-transaction leaves no store
/// transaction open, and the next writer (recording, in BEGIN) commits
/// only its own change.
#[test]
fn rv_dropped_writer_then_recording_writer() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 10);
    drop_a_spilled_writer(&mut h, BIG_INSERT);
    assert!(!h.sdb.txn_open(), "a dropped writer left its store txn open");
    h.ok("BEGIN");
    h.ok("UPDATE t SET n = 1 WHERE id = 1");
    h.ok("COMMIT");
    assert_eq!(fresh_count(&mut h, 1, 1_000_000), 40);
    assert_eq!(h.one("SELECT sum(n) FROM t"), 1);
    h.integrity();
}

/// The next writer after a dropped one is a plain autocommit statement.
#[test]
fn rv_dropped_writer_then_autocommit_writer() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 10);
    drop_a_spilled_writer(&mut h, BIG_INSERT);
    h.ok("UPDATE t SET n = 1 WHERE id = 1");
    h.ok("UPDATE t SET n = 1 WHERE id = 2");
    assert_eq!(fresh_count(&mut h, 1000, 2200), 0);
    assert_eq!(h.one("SELECT sum(n) FROM t"), 2);
    h.integrity();
}

/// Contrast: close() aborts the transaction too.
#[test]
fn rv_closed_writer_aborts_its_txn() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 10);
    let c2 = h.connect();
    h.exec_on(&c2, "BEGIN", &[]).unwrap();
    h.exec_on(&c2, BIG_INSERT, &[]).unwrap();
    h.r.run(|| c2.close()).unwrap();
    drop(c2);
    assert!(!h.sdb.txn_open(), "close left the store txn open");
    h.ok("BEGIN");
    h.ok("UPDATE t SET n = 1 WHERE id = 1");
    h.ok("COMMIT");
    assert_eq!(h.one("SELECT count(*) FROM t"), 40);
    h.integrity();
}

/// A dropped writer, then a writer that spills too: only the second
/// transaction's rows are committed.
#[test]
fn rv_dropped_writer_then_spilling_writer() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 10);
    drop_a_spilled_writer(&mut h, BIG_INSERT);
    h.ok("BEGIN");
    h.ok(BIG_INSERT2);
    h.ok("COMMIT");
    assert_eq!(fresh_count(&mut h, 1000, 2200), 0);
    assert_eq!(fresh_count(&mut h, 5000, 6200), 1201);
    h.integrity();
}

/// A dropped writer, then an autocommit insert of more than one part.
#[test]
fn rv_dropped_writer_then_autocommit_spill() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 10);
    drop_a_spilled_writer(&mut h, BIG_INSERT);
    h.ok(BIG_INSERT2);
    assert_eq!(fresh_count(&mut h, 1000, 2200), 0);
    assert_eq!(fresh_count(&mut h, 5000, 6200), 1201);
    h.integrity();
}

/// The reviewer's repro: a dropped writer's spilled UPDATE of existing
/// pages must not reach another writer's acked commit.
#[test]
fn rv_dropped_updater_leaks_into_next_commit() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 100);
    drop_a_spilled_writer(&mut h, "UPDATE t SET n = 5");
    h.ok("BEGIN");
    h.ok(BIG_INSERT2);
    h.ok("COMMIT");
    let c = h.connect();
    let rows = h
        .exec_on(&c, "SELECT count(*), sum(n) FROM t WHERE id <= 400", &[])
        .unwrap();
    assert_eq!(int(&rows[0][0]), 400);
    assert_eq!(
        int(&rows[0][1]),
        0,
        "a dropped connection's uncommitted UPDATE was committed by another writer"
    );
    integrity_on(&mut h, &c);
}

/// A reader's SAVEPOINT / ROLLBACK TO / ROLLBACK between the steps of a
/// writer's statement that is spilling.
#[test]
fn rv_reader_rollback_mid_writer_statement() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 10);
    let c2 = h.connect();
    let w = h.conn.clone();
    h.ok("BEGIN");
    h.ok("SAVEPOINT w");
    let mut stmt = h.r.run(|| w.prepare(BIG_INSERT)).unwrap();
    let mut rounds = 0;
    while !step_for(&mut h, &mut stmt, 3).unwrap() {
        rounds += 1;
        h.exec_on(&c2, "SAVEPOINT r", &[]).unwrap();
        h.exec_on(&c2, "SELECT count(*) FROM t", &[]).unwrap();
        h.exec_on(&c2, "ROLLBACK TO r", &[]).unwrap();
        h.exec_on(&c2, "ROLLBACK", &[]).unwrap();
    }
    drop(stmt);
    assert!(rounds > 0 && h.stats().spilled_pages > 0);
    h.ok("COMMIT");
    assert_eq!(h.one("SELECT count(*) FROM t"), 40 + 1201);
    h.integrity();
    integrity_on(&mut h, &c2);
}

/// A trigger spills from a nested statement in autocommit while a reader
/// rolls back savepoints between the writer's steps.
#[test]
fn rv_trigger_spill_with_reader_rollbacks() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 10);
    h.ok("CREATE TABLE u(id INTEGER PRIMARY KEY, v BLOB)");
    h.ok("CREATE TRIGGER tr AFTER INSERT ON t BEGIN INSERT INTO u(v) VALUES (zeroblob(900)); END");
    let c2 = h.connect();
    let w = h.conn.clone();
    let mut stmt = h.r.run(|| w.prepare(BIG_INSERT)).unwrap();
    while !step_for(&mut h, &mut stmt, 2).unwrap() {
        h.exec_on(&c2, "SAVEPOINT r", &[]).unwrap();
        h.exec_on(&c2, "SELECT count(*) FROM u", &[]).unwrap();
        h.exec_on(&c2, "ROLLBACK TO r", &[]).unwrap();
        h.exec_on(&c2, "RELEASE r", &[]).unwrap();
    }
    drop(stmt);
    assert_eq!(h.one("SELECT count(*) FROM t"), 40 + 1201);
    assert_eq!(h.one("SELECT count(*) FROM u"), 1201);
    h.integrity();
}

/// Resetting a writer's statement while its reads are in flight, then
/// using the connection again and committing; and dropping a reader
/// with reads in flight.
#[test]
fn rv_reset_mid_io_then_continue() {
    let mut h = H::open(Cfg {
        slots: 64,
        read_delay: 3,
        ..Cfg::default()
    });
    h.fill("t", 30);
    let w = h.conn.clone();
    h.ok("BEGIN");
    h.ok("UPDATE t SET n = 2 WHERE id = 1");
    for k in 0..5 {
        let mut stmt = h.r.run(|| w.prepare("UPDATE t SET n = n + 1")).unwrap();
        let _ = step_for(&mut h, &mut stmt, 2 + k).unwrap();
        let _ = h.r.run(|| stmt.reset());
        drop(stmt);
    }
    let c2 = h.connect();
    h.exec_on(&c2, "BEGIN", &[]).unwrap();
    {
        let mut s2 = h.r.run(|| c2.prepare("SELECT sum(length(v)) FROM t")).unwrap();
        let _ = step_for(&mut h, &mut s2, 1);
        drop(s2);
    }
    drop(c2);
    if !h.conn.get_auto_commit() {
        h.ok("COMMIT");
    }
    for _ in 0..8 {
        h.r.run(|| {});
    }
    assert_eq!(fresh_count(&mut h, 1, 1_000_000), 120);
    h.integrity();
}

/// A losing writer (Busy) rolls back while the winner has spilled parts:
/// the winner's transaction is untouched and commits whole.
#[test]
fn rv_losing_writer_rollback_keeps_winner2() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 10);
    let c2 = h.connect();
    rv_step_all(&mut h, &c2, "BEGIN").unwrap();
    rv_step_all(&mut h, &c2, "SELECT count(*) FROM t").unwrap();
    h.ok("BEGIN");
    h.ok(BIG_INSERT);
    let aborts = h.stats().aborts;
    let _ = rv_step_all(&mut h, &c2, "INSERT INTO t(id, n, v) VALUES (99999, 0, 1)");
    let _ = rv_step_all(&mut h, &c2, "ROLLBACK");
    let _ = rv_step_all(&mut h, &c2, "BEGIN IMMEDIATE");
    if !c2.get_auto_commit() {
        let _ = rv_step_all(&mut h, &c2, "ROLLBACK");
    }
    assert_eq!(h.stats().aborts, aborts, "the loser aborted the winner's txn");
    assert!(h.sdb.txn_open());
    h.ok("COMMIT");
    assert_eq!(h.one("SELECT count(*) FROM t"), 40 + 1201);
    h.integrity();
}

// ---- final review, round 4 (reviewer repros) -------------------------------

/// Step `stmt` for at most `runs` runs, collecting column `col` of each row.
/// Returns (done, rows, other step result if any).
fn r4_step_rows(
    h: &mut H,
    stmt: &mut crate::Statement,
    runs: u64,
    max_rows: usize,
) -> (bool, Vec<i64>, Option<String>) {
    let mut out = Vec::new();
    for _ in 0..runs {
        let r = h.r.run(|| -> crate::Result<Option<Option<String>>> {
            loop {
                match stmt.step()? {
                    StepResult::Row => {
                        let row = stmt.row().expect("row");
                        let v: Vec<Value> = row.get_values().cloned().collect();
                        out.push(int(&v[1]));
                        if out.len() >= max_rows {
                            return Ok(None);
                        }
                    }
                    StepResult::Done => return Ok(Some(None)),
                    StepResult::IO | StepResult::Yield => return Ok(None),
                    o => return Ok(Some(Some(format!("{o:?}")))),
                }
            }
        });
        match r {
            Ok(None) => {
                if out.len() >= max_rows {
                    return (false, out, None);
                }
            }
            Ok(Some(None)) => return (true, out, None),
            Ok(Some(Some(o))) => return (false, out, Some(o)),
            Err(e) => return (false, out, Some(format!("error {e}"))),
        }
    }
    (false, out, None)
}

/// D1: a read statement keeps stepping after its connection's read
/// transaction ended (a sibling autocommit write on the same connection
/// committed). Its misses then read at Latest and see another
/// connection's staged, uncommitted (later rolled back) pages.
#[test]
fn r4_sibling_reader_after_own_commit_sees_uncommitted() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 100);
    h.ok("CREATE TABLE u(x)");
    let c = h.conn.clone();
    let mut s = h.r.run(|| c.prepare("SELECT id, n FROM t")).unwrap();
    let (done, first, other) = r4_step_rows(&mut h, &mut s, 1000, 4);
    assert!(!done && other.is_none(), "{other:?}");
    // Sibling autocommit write on the same connection: commits and ends
    // the connection's read transaction while `s` is still mid-scan.
    h.ok("INSERT INTO u VALUES (1)");
    let w = c.pager.load().holds_read_lock();
    eprintln!("r4 D1: conn holds read lock after sibling commit: {w}");
    // Another connection writes every row and spills.
    let d = h.connect();
    h.exec_on(&d, "BEGIN", &[]).unwrap();
    h.exec_on(&d, "UPDATE t SET n = 7", &[]).unwrap();
    eprintln!("r4 D1: spilled {}", h.stats().spilled_pages);
    let (_, rest, other) = r4_step_rows(&mut h, &mut s, 100_000, usize::MAX);
    drop(s);
    let sevens = rest.iter().filter(|&&n| n == 7).count();
    eprintln!(
        "r4 D1: first {} rows, rest {} rows, {} rows with n=7 (uncommitted), other {:?}",
        first.len(),
        rest.len(),
        sevens,
        other
    );
    h.exec_on(&d, "ROLLBACK", &[]).unwrap();
    // The connection's cache after the other writer rolled back.
    let after = h.one("SELECT sum(n) FROM t");
    eprintln!("r4 D1: after rollback, conn sees sum(n) = {after}");
    let fresh = h.connect();
    let rows = h.exec_on(&fresh, "SELECT sum(n) FROM t", &[]).unwrap();
    eprintln!("r4 D1: fresh conn sees sum(n) = {}", int(&rows[0][0]));
    assert_eq!(sevens, 0, "a reader saw another connection's uncommitted rows");
    assert_eq!(after, 0, "the connection's cache kept rolled-back pages");
    assert_eq!(other, None);
    assert_eq!(first.len() + rest.len(), 400, "the scan ended early");
}

/// D1b: the same through BEGIN; SELECT (partly); COMMIT.
#[test]
fn r4_reader_after_explicit_commit_sees_uncommitted() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 100);
    let c = h.conn.clone();
    h.ok("BEGIN");
    let mut s = h.r.run(|| c.prepare("SELECT id, n FROM t")).unwrap();
    let (done, first, other) = r4_step_rows(&mut h, &mut s, 1000, 4);
    assert!(!done && other.is_none(), "{other:?}");
    let commit = h.exec("COMMIT");
    eprintln!("r4 D1b: COMMIT with a reader mid-scan: {:?}", commit.as_ref().map(|_| ()));
    let d = h.connect();
    h.exec_on(&d, "BEGIN", &[]).unwrap();
    h.exec_on(&d, "UPDATE t SET n = 7", &[]).unwrap();
    let (_, rest, other) = r4_step_rows(&mut h, &mut s, 100_000, usize::MAX);
    drop(s);
    let sevens = rest.iter().filter(|&&n| n == 7).count();
    eprintln!("r4 D1b: rest {} rows, {} with n=7, other {:?}", rest.len(), sevens, other);
    h.exec_on(&d, "ROLLBACK", &[]).unwrap();
    let after = h.one("SELECT sum(n) FROM t");
    eprintln!("r4 D1b: after rollback conn sees sum(n) = {after}");
    assert_eq!(sevens, 0, "a reader saw another connection's uncommitted rows");
    assert_eq!(after, 0, "the connection's cache kept rolled-back pages");
    assert_eq!(other, None);
    assert_eq!(first.len() + rest.len(), 400, "the scan ended early");
}

/// D1c: the contaminated cache is then written on: C commits a change on
/// top of pages it read from D's rolled-back transaction.
#[test]
fn r4_contaminated_cache_then_commit() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 100);
    h.ok("CREATE TABLE u(x)");
    let c = h.conn.clone();
    let mut s = h.r.run(|| c.prepare("SELECT id, n FROM t")).unwrap();
    let _ = r4_step_rows(&mut h, &mut s, 1000, 4);
    h.ok("INSERT INTO u VALUES (1)");
    let d = h.connect();
    h.exec_on(&d, "BEGIN", &[]).unwrap();
    h.exec_on(&d, "UPDATE t SET n = 7", &[]).unwrap();
    let _ = r4_step_rows(&mut h, &mut s, 100_000, usize::MAX);
    drop(s);
    h.exec_on(&d, "ROLLBACK", &[]).unwrap();
    drop(d);
    h.ok("UPDATE t SET v = zeroblob(901) WHERE id % 4 = 0");
    let fresh = h.connect();
    let rows = h.exec_on(&fresh, "SELECT sum(n) FROM t", &[]).unwrap();
    eprintln!("r4 D1c: fresh conn after C's commit sees sum(n) = {}", int(&rows[0][0]));
    assert_eq!(int(&rows[0][0]), 0, "a rolled-back UPDATE reached a commit");
    integrity_on(&mut h, &fresh);
}

/// P1 regression probe: an autocommit writer's read misses get no credit
/// past the park limit, so it returns Busy mid-opcode (x6's recipe: 6
/// runs in, then 0 credits). Resumed with a normal grant it finishes, and
/// either all of it lands or none.
#[test]
fn r4_busy_read_mid_statement_then_continue() {
    let mut h = H::open(Cfg {
        slots: 64,
        read_delay: 2,
        ..Cfg::default()
    });
    h.fill("t", 100);
    let w = h.connect();
    let mut s = h
        .r
        .run(|| w.prepare("UPDATE t SET n = n + 1, v = zeroblob(950)"))
        .unwrap();
    assert!(!step_for(&mut h, &mut s, 6).unwrap(), "finished before the squeeze");
    h.r.credits = 0;
    let mut outcome = String::from("none");
    let mut busy = 0;
    for _ in 0..400 {
        let r = h.r.run(|| -> crate::Result<Option<String>> {
            loop {
                match s.step()? {
                    StepResult::Row => {}
                    StepResult::Done => return Ok(Some("done".into())),
                    StepResult::IO | StepResult::Yield => return Ok(None),
                    o => return Ok(Some(format!("{o:?}"))),
                }
            }
        });
        match r {
            Ok(None) => {}
            Ok(Some(x)) if x == "Busy" => {
                busy += 1;
                outcome = "busy".into();
                break;
            }
            Ok(Some(x)) => {
                outcome = x;
                break;
            }
            Err(e) => {
                outcome = format!("err {e}");
                break;
            }
        }
    }
    h.r.credits = super::DEFAULT_CREDITS;
    assert!(busy > 0, "never reached BUSY: {outcome}");
    // Resume the same statement with a normal grant.
    let (done, _, other) = r4_step_rows(&mut h, &mut s, 10_000, usize::MAX);
    drop(s);
    let st = h.stats();
    eprintln!(
        "r4 P1: outcome {outcome}, resumed done={done} other={other:?}, hard_rule_full {} credit_short {} doomed {}",
        st.hard_rule_full, st.credit_short, st.doomed
    );
    assert_eq!(st.hard_rule_full, 0, "{st:?}");
    assert_eq!(st.credit_short, 0, "{st:?}");
    assert!(h.sdb.test_claims().is_empty(), "claims left");
    let fresh = h.connect();
    let rows = h
        .exec_on(&fresh, "SELECT count(*), sum(n) FROM t", &[])
        .unwrap();
    let (count, sum) = (int(&rows[0][0]), int(&rows[0][1]));
    eprintln!("r4 P1: fresh {count} rows sum {sum}");
    assert_eq!(count, 400);
    if done {
        assert_eq!(sum, 400, "a resumed update lost rows");
    } else {
        assert_eq!(sum, 0, "partial update, sum {sum}");
    }
    integrity_on(&mut h, &fresh);
}

/// C: drop the connection while its COMMIT is parked part way (credits
/// short, some pages staged by the commit loop). Nothing may land.
#[test]
fn r4_drop_mid_commit_is_atomic() {
    for credits in [4u32, 5, 6, 8] {
        let mut h = H::open(Cfg {
            slots: 64,
            ..Cfg::default()
        });
        h.fill("t", 10);
        let c2 = h.connect();
        h.exec_on(&c2, "BEGIN", &[]).unwrap();
        h.exec_on(&c2, BIG_INSERT, &[]).unwrap();
        let commits = h.stats().txn_commits;
        h.r.credits = credits;
        let mut stmt = h.r.run(|| c2.prepare("COMMIT")).unwrap();
        let done = step_for(&mut h, &mut stmt, 1).unwrap_or(false);
        let parts = h.stats().parts;
        drop(stmt);
        drop(c2);
        h.r.credits = super::DEFAULT_CREDITS;
        for _ in 0..4 {
            h.r.run(|| {});
        }
        let n = h.one("SELECT count(*) FROM t");
        eprintln!(
            "r4 C credits={credits}: commit done in one run {done}, parts {parts}, txn_commits {} -> {}, txn_open {}, rows {n}",
            commits,
            h.stats().txn_commits,
            h.sdb.txn_open()
        );
        if !done {
            assert_eq!(n, 40, "a dropped COMMIT landed part of its transaction");
        }
        h.ok("INSERT INTO t(id, n, v) VALUES (99999, 0, 1)");
        h.integrity();
    }
}

/// C': a COMMIT statement reset while parked, then the connection keeps
/// writing and COMMITs again: the commit is whole.
#[test]
fn r4_reset_parked_commit_then_commit() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 10);
    let w = h.conn.clone();
    h.ok("BEGIN");
    h.ok(BIG_INSERT);
    h.r.credits = 5;
    let mut stmt = h.r.run(|| w.prepare("COMMIT")).unwrap();
    let done = step_for(&mut h, &mut stmt, 1).unwrap_or(false);
    let _ = h.r.run(|| stmt.reset());
    drop(stmt);
    h.r.credits = super::DEFAULT_CREDITS;
    eprintln!("r4 C': first COMMIT done {done}, autocommit {}", w.get_auto_commit());
    if !w.get_auto_commit() {
        h.ok("UPDATE t SET n = 3 WHERE id = 1");
        h.ok("COMMIT");
    } else {
        h.ok("UPDATE t SET n = 3 WHERE id = 1");
    }
    let fresh = h.connect();
    let rows = h
        .exec_on(&fresh, "SELECT count(*), sum(n) FROM t", &[])
        .unwrap();
    eprintln!("r4 C': fresh {} rows sum {}", int(&rows[0][0]), int(&rows[0][1]));
    integrity_on(&mut h, &fresh);
}

/// Two writers and a reader with savepoints, with the losing writer
/// dropped at every step of the winner's transaction.
#[test]
fn r4_drop_loser_and_reader_each_step() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 10);
    let w = h.conn.clone();
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    let mut stmt = h.r.run(|| w.prepare(BIG_INSERT)).unwrap();
    let mut rounds = 0;
    while !step_for(&mut h, &mut stmt, 2).unwrap() {
        rounds += 1;
        let l = h.connect();
        let _ = rv_step_all(&mut h, &l, "BEGIN");
        let _ = rv_step_all(&mut h, &l, "INSERT INTO t(id, n, v) VALUES (88888, 0, 1)");
        drop(l);
        let r = h.connect();
        h.exec_on(&r, "BEGIN", &[]).unwrap();
        h.exec_on(&r, "SAVEPOINT s", &[]).unwrap();
        let rows = h.exec_on(&r, "SELECT count(*) FROM t", &[]).unwrap();
        assert_eq!(int(&rows[0][0]), 40, "reader saw uncommitted rows");
        h.exec_on(&r, "ROLLBACK TO s", &[]).unwrap();
        drop(r);
    }
    drop(stmt);
    assert!(rounds > 0);
    h.ok("RELEASE a");
    h.ok("COMMIT");
    let fresh = h.connect();
    let rows = h.exec_on(&fresh, "SELECT count(*) FROM t", &[]).unwrap();
    assert_eq!(int(&rows[0][0]), 40 + 1201);
    integrity_on(&mut h, &fresh);
}


/// C with a large arena: the COMMIT loop stages part of the dirty set
/// (credits short) and parks; then the connection is dropped, or the
/// statement reset and the transaction committed later.
#[test]
fn r4_big_arena_partial_commit() {
    for mode in ["drop", "reset_then_commit"] {
        let mut h = H::open(Cfg {
            slots: 4096,
            ..Cfg::default()
        });
        h.fill("t", 10);
        let c2 = h.connect();
        h.exec_on(&c2, "BEGIN", &[]).unwrap();
        h.exec_on(&c2, "INSERT INTO t(id, n, v) WITH RECURSIVE c(i) AS (SELECT 1000 UNION ALL SELECT i + 1 FROM c WHERE i < 7000) SELECT i, 1, zeroblob(900) FROM c", &[]).unwrap();
        let spilled = h.stats().spilled_pages;
        h.r.credits = 2;
        let mut stmt = h.r.run(|| c2.prepare("COMMIT")).unwrap();
        let done = step_for(&mut h, &mut stmt, 3).unwrap_or(false);
        let st = h.stats();
        eprintln!("r4 C2 {mode}: spilled before commit {spilled}, commit done {done}, parts {}, txn_open {}, txn_commits {}", st.parts, h.sdb.txn_open(), st.txn_commits);
        h.r.credits = super::DEFAULT_CREDITS;
        if mode == "drop" {
            drop(stmt);
            drop(c2);
            for _ in 0..4 { h.r.run(|| {}); }
            let n = h.one("SELECT count(*) FROM t");
            eprintln!("r4 C2 drop: rows {n} txn_open {}", h.sdb.txn_open());
            assert!(n == 40 || (done && n == 40 + 6001), "partial commit: {n}");
        } else {
            let _ = h.r.run(|| stmt.reset());
            drop(stmt);
            eprintln!("r4 C2 reset: autocommit {}", c2.get_auto_commit());
            let r = if c2.get_auto_commit() { Ok(vec![]) } else { h.exec_on(&c2, "COMMIT", &[]) };
            eprintln!("r4 C2 reset: second commit {:?}", r.map(|_| ()));
            let n = h.one("SELECT count(*) FROM t");
            eprintln!("r4 C2 reset: rows {n}");
            assert!(n == 40 || n == 40 + 6001, "partial commit: {n}");
        }
        h.integrity();
    }
}

/// Round 4: `begin_write_tx` aborts a store transaction a gone writer
/// left open. The hook skips the writer's own aborts (rollback and
/// `end_write_tx`), so the dropped writer's transaction is still open when
/// the next writer begins.
#[test]
fn begin_write_tx_aborts_a_leftover_txn() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 10);
    h.sdb.test_set_skip_end_abort(true);
    drop_a_spilled_writer(&mut h, BIG_INSERT);
    h.sdb.test_set_skip_end_abort(false);
    assert!(h.sdb.txn_open(), "the hook left the dropped writer's txn open");
    let aborts = h.stats().aborts;
    h.ok("BEGIN");
    h.ok("UPDATE t SET n = 1 WHERE id = 1");
    assert!(h.stats().aborts > aborts, "the leftover was not aborted");
    h.ok("COMMIT");
    assert_eq!(fresh_count(&mut h, 1000, 2200), 0, "the leftover committed");
    assert_eq!(fresh_count(&mut h, 1, 1_000_000), 40);
    assert_eq!(h.one("SELECT sum(n) FROM t"), 1);
    h.integrity();
}

/// Round 4: a read whose credits never come (one credit a run, a read at
/// a fresh version needs a pin and the read) fails SQLITE_BUSY after the
/// read-park limit, not never. The statement then resumes at the same PC
/// with a normal grant and reads the right answer.
#[test]
fn read_parks_are_bounded_busy() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 30);
    h.ok("UPDATE t SET n = 1");
    let r = h.connect();
    let mut stmt = h.r.run(|| r.prepare("SELECT id, n FROM t")).unwrap();
    h.r.credits = 1;
    let start = h.r.runs;
    let (done, rows, other) = r4_step_rows(&mut h, &mut stmt, 4 * 64 + 16, usize::MAX);
    let used = h.r.runs - start;
    assert!(!done, "finished on one credit a run");
    assert_eq!(other.as_deref(), Some("Busy"), "rows {}", rows.len());
    assert!(used <= 4 * 64 + 8, "gave up after {used} runs");
    h.r.credits = super::DEFAULT_CREDITS;
    let (done, rest, other) = r4_step_rows(&mut h, &mut stmt, 10_000, usize::MAX);
    assert!(done, "{other:?}");
    assert_eq!(rows.len() + rest.len(), 120);
    assert!(rows.iter().chain(&rest).all(|&n| n == 1));
    drop(stmt);
    h.check_invariants();
    assert!(h.sdb.test_claims().is_empty(), "{:?}", h.sdb.test_claims());
}

/// Round 4: a savepoint restore that never gets a credit is bounded too,
/// by the larger restore limit (past the plain one), and then dooms the
/// transaction: nothing commits and the connection recovers.
#[test]
fn restore_parks_are_bounded() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 100);
    let head = h.r.store.head();
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    h.ok("UPDATE t SET n = n + 1");
    let before = h.stats();
    let conn = h.conn.clone();
    h.r.credits = 0;
    let start = h.r.runs;
    let mut err = None;
    for sql in ["ROLLBACK TO a", "SELECT sum(n) FROM t"] {
        let mut stmt = h.r.run(|| conn.prepare(sql)).unwrap();
        let mut finished = false;
        for _ in 0..8 * 1024 {
            match step_for(&mut h, &mut stmt, 1) {
                Ok(false) => {}
                Ok(true) => {
                    finished = true;
                    break;
                }
                Err(e) => {
                    err = Some(e);
                    break;
                }
            }
        }
        assert!(finished || err.is_some(), "{sql}: no end after {} runs", h.r.runs - start);
        if err.is_some() {
            break;
        }
    }
    let used = h.r.runs - start;
    h.r.credits = super::DEFAULT_CREDITS;
    let err = err.expect("the restore parks are bounded");
    assert!(is_full(&err), "expected SQLITE_FULL, got {err}");
    assert!(used > 2 * 64, "gave up after {used} runs: the plain limit");
    assert!(used <= 4 * 1024, "gave up after {used} runs");
    let s = h.stats();
    assert!(s.doomed > before.doomed, "{s:?}");
    if !h.conn.get_auto_commit() {
        h.ok("ROLLBACK");
    }
    assert_eq!(h.r.store.head(), head, "nothing committed");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 0);
    h.ok("UPDATE t SET n = 1 WHERE id = 1");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 1);
    h.integrity();
}

// ---- review round 5 C1: one snapshot per connection while statements run --

/// Step `stmt` for at most `runs` runs, collecting (col0, col1) of each row,
/// up to `max` rows; with `stop_at_io` return at the first run that ends in
/// IO. Returns (done, rows, other step result or error if any).
fn x_step(
    h: &mut H,
    stmt: &mut crate::Statement,
    runs: u64,
    max: usize,
    stop_at_io: bool,
) -> (bool, Vec<(i64, i64)>, Option<String>) {
    let mut out = Vec::new();
    for _ in 0..runs {
        let r = h.r.run(|| -> crate::Result<Option<Option<String>>> {
            loop {
                match stmt.step()? {
                    StepResult::Row => {
                        let row = stmt.row().expect("row");
                        let v: Vec<Value> = row.get_values().cloned().collect();
                        out.push((int(&v[0]), int(&v[1])));
                        if out.len() >= max {
                            return Ok(None);
                        }
                    }
                    StepResult::Done => return Ok(Some(None)),
                    StepResult::IO | StepResult::Yield => return Ok(None),
                    o => return Ok(Some(Some(format!("{o:?}")))),
                }
            }
        });
        match r {
            Ok(None) => {
                if out.len() >= max || stop_at_io {
                    return (false, out, None);
                }
            }
            Ok(Some(None)) => return (true, out, None),
            Ok(Some(Some(o))) => return (false, out, Some(o)),
            Err(e) => return (false, out, Some(format!("error {e}"))),
        }
    }
    (false, out, None)
}

/// Copy one row into `u` on `conn` (autocommit). `Err` is the step result
/// or error that stopped it.
fn c1_insert(h: &mut H, conn: &Arc<Connection>, id: i64, n: i64) -> std::result::Result<(), String> {
    rv_step_all(h, conn, &format!("INSERT INTO u VALUES ({id}, {n})"))
}

/// The write upgrade on a stale snapshot the connection keeps for its
/// running statements fails SQLITE_BUSY_SNAPSHOT, not the retryable BUSY of
/// a plain autocommit upgrade (`fail_step`): every retry would rejoin the
/// same snapshot.
fn is_busy_snapshot(msg: &str) -> bool {
    msg.contains(&LimboError::BusySnapshot.to_string())
}

/// C1 (x1): a long read on C outlives the read transaction a sibling
/// reader's halt ended; another connection commits; a later statement on C
/// starts a read transaction. Like SQLite (one read transaction while any
/// statement runs) it rejoins C's version: the long scan is neither cut
/// short nor mixed, and C's hold is gone once its last statement ends.
#[test]
fn c1_long_read_keeps_its_snapshot_across_sibling_statements() {
    for park in [false, true] {
        let mut h = H::open(Cfg {
            slots: 64,
            read_delay: 3,
            ..Cfg::default()
        });
        h.fill("t", 100);
        h.ok("CREATE TABLE u(x)");
        let c = h.conn.clone();
        let mut s = h.r.run(|| c.prepare("SELECT id, n FROM t")).unwrap();
        let (_, mut rows, o) = x_step(&mut h, &mut s, 1000, 8, false);
        assert!(o.is_none(), "{o:?}");
        h.exec_on(&c, "SELECT count(*) FROM u", &[]).unwrap();
        let d = h.connect();
        h.exec_on(&d, "UPDATE t SET n = 7", &[]).unwrap();
        if park {
            // Leave a read of the long statement in flight at the old version.
            let (_, more, o) = x_step(&mut h, &mut s, 1, usize::MAX, true);
            assert!(o.is_none(), "park={park}: {o:?}");
            rows.extend(more);
        }
        h.exec_on(&c, "SELECT count(*) FROM u", &[]).unwrap();
        // A sibling read sees C's snapshot too, not D's commit.
        let sib = h.exec_on(&c, "SELECT sum(n) FROM t", &[]).unwrap();
        assert_eq!(int(&sib[0][0]), 0, "park={park}: a sibling read left C's snapshot");
        let (done, rest, o) = x_step(&mut h, &mut s, 100_000, usize::MAX, false);
        rows.extend(rest);
        drop(s);
        let mut ids: Vec<i64> = rows.iter().map(|r| r.0).collect();
        ids.sort();
        ids.dedup();
        let sevens = rows.iter().filter(|r| r.1 == 7).count();
        assert!(done && o.is_none(), "park={park}: done {done} {o:?}");
        assert_eq!(rows.len(), 400, "park={park}: the scan ended early");
        assert_eq!(ids.len(), 400, "park={park}: duplicate rows");
        assert_eq!(sevens, 0, "park={park}: the scan saw a later commit");
        assert!(
            h.sdb.test_pins().is_empty(),
            "park={park}: holds left with no statement running: {:?}",
            h.sdb.test_pins()
        );
        // With no statement left C reads the head again.
        assert_eq!(h.one("SELECT sum(n) FROM t"), 7 * 400);
        h.check_invariants();
        integrity_on(&mut h, &d);
    }
}

/// C1 (x2): an app copies t into u row by row on C (autocommit INSERT per
/// row) while the scan runs, and another connection commits once. The
/// INSERT after that commit fails SQLITE_BUSY_SNAPSHOT (C's snapshot is
/// stale); nothing mixed is committed.
#[test]
fn c1_app_copy_after_foreign_commit_is_busy_snapshot() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    h.fill("t", 100);
    h.ok("CREATE TABLE u(id INTEGER PRIMARY KEY, n INTEGER)");
    let c = h.conn.clone();
    let d = h.connect();
    let mut s = h.r.run(|| c.prepare("SELECT id, n FROM t")).unwrap();
    let mut copied = 0;
    let mut insert_err = None;
    let mut seen = Vec::new();
    'scan: loop {
        let (done, rows, o) = x_step(&mut h, &mut s, 100_000, 1, false);
        assert!(o.is_none(), "scan: {o:?}");
        for (id, n) in rows {
            seen.push(n);
            if let Err(e) = c1_insert(&mut h, &c, id, n) {
                insert_err = Some(e);
                break 'scan;
            }
            copied += 1;
            if copied == 20 {
                h.exec_on(&d, "UPDATE t SET n = 7", &[]).unwrap();
            }
        }
        if done {
            break;
        }
    }
    drop(s);
    let fresh = h.connect();
    let rows = h
        .exec_on(&fresh, "SELECT count(*), sum(n = 7) FROM u", &[])
        .unwrap();
    let (cnt, sev) = (int(&rows[0][0]), int(&rows[0][1]));
    // With the scan gone C reads the head again, and the write goes in.
    c1_insert(&mut h, &c, 100_000, 1).unwrap();
    eprintln!("c1 x2: copied {copied}, insert error {insert_err:?}; u has {cnt} rows, {sev} with n=7");
    let err = insert_err.expect("the copy after the foreign commit succeeded");
    assert!(is_busy_snapshot(&err), "{err}");
    assert_eq!(copied, 20);
    assert_eq!(cnt, 20);
    assert_eq!(sev, 0, "a mixed copy was committed");
    assert!(!seen.contains(&7), "the scan saw the later commit");
    assert!(h.sdb.test_pins().is_empty(), "{:?}", h.sdb.test_pins());
    integrity_on(&mut h, &fresh);
}

/// C1 (x7): the same with a materialized outer loop and re-seeks of `t`
/// (or a correlated subquery): the outer rows and the inner lookups read
/// one version, and the copy stops at BUSY_SNAPSHOT.
#[test]
fn c1_materialized_outer_loop_reads_one_version() {
    for (i, sql) in [
        "SELECT s.id, t.n FROM (SELECT id FROM t ORDER BY -id) AS s JOIN t ON t.id = s.id",
        "WITH s AS MATERIALIZED (SELECT id FROM t ORDER BY -id) SELECT s.id, t.n FROM s JOIN t ON t.id = s.id",
        "SELECT id, (SELECT n FROM t AS t2 WHERE t2.id = t.id) FROM t ORDER BY -id",
    ]
    .iter()
    .enumerate()
    {
        let mut h = H::open(Cfg {
            slots: 64,
            ..Cfg::default()
        });
        h.fill("t", 100);
        h.ok("CREATE TABLE u(id INTEGER PRIMARY KEY, n INTEGER)");
        let c = h.conn.clone();
        let d = h.connect();
        let mut s = match h.r.run(|| c.prepare(sql)) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("c1 x7[{i}] prepare failed: {e}");
                continue;
            }
        };
        let mut copied = 0;
        let mut seen = Vec::new();
        let mut err = None;
        loop {
            let (done, rows, o) = x_step(&mut h, &mut s, 100_000, 1, false);
            assert!(o.is_none(), "x7[{i}] scan: {o:?}");
            for (id, n) in rows {
                seen.push(n);
                if let Err(e) = c1_insert(&mut h, &c, id, n) {
                    err = Some(e);
                    break;
                }
                copied += 1;
                if copied == 20 {
                    h.exec_on(&d, "UPDATE t SET n = 7", &[]).unwrap();
                }
            }
            if done || err.is_some() {
                break;
            }
        }
        drop(s);
        let fresh = h.connect();
        let rows = h
            .exec_on(&fresh, "SELECT count(*), sum(n = 7) FROM u", &[])
            .unwrap();
        let (cnt, sev) = (int(&rows[0][0]), int(&rows[0][1]));
        eprintln!("c1 x7[{i}]: err {err:?}; u has {cnt} rows, {sev} with n=7");
        let err = err.unwrap_or_else(|| panic!("x7[{i}]: the copy after the foreign commit succeeded"));
        assert!(is_busy_snapshot(&err), "x7[{i}]: {err}");
        assert_eq!(cnt, 20, "x7[{i}]");
        assert_eq!(sev, 0, "x7[{i}]: a mixed copy was committed");
        assert!(!seen.contains(&7), "x7[{i}]: the query mixed versions");
        assert!(h.sdb.test_pins().is_empty(), "x7[{i}]: {:?}", h.sdb.test_pins());
        integrity_on(&mut h, &fresh);
    }
}

/// C1, on the WAL itself: a read transaction that ends while another
/// statement is active keeps its hold; the next one rejoins that version
/// (cache kept) and a write on it is BUSY_SNAPSHOT; the last statement's
/// end releases it. With one statement it starts at the head as before.
#[test]
fn c1_wal_keeps_the_hold_while_statements_run() {
    use crate::storage::wal::{Wal, WalAutoActions};
    let (db, _arena) = bare(16, u64::MAX / 2);
    db.begin_run(16, u64::MAX / 2);
    let wal = super::wal::StreamWal::new(db.clone());
    let commit_one = || {
        let p = page_buf(&db);
        assert!(db.batch_write(0, &p).unwrap());
        db.batch_commit().unwrap()
    };
    // Past version 1 (the page-1 init, which `begin_write_tx` lets a
    // reader of version 0 through).
    assert_eq!(commit_one(), 1);
    wal.stream_root_statements(1);
    wal.begin_read_tx().unwrap();
    wal.stream_root_statements(2);
    wal.end_read_tx();
    assert_eq!(db.test_pins(), vec![(1, 1, false)], "kept for the running statement");
    assert_eq!(commit_one(), 2);
    assert!(wal.stream_snapshot_stale());
    assert!(!wal.begin_read_tx().unwrap(), "rejoined: the cache stays");
    assert_eq!(db.test_pins(), vec![(1, 1, false)]);
    assert!(matches!(
        wal.begin_write_tx(WalAutoActions::empty()),
        Err(LimboError::BusySnapshot)
    ));
    wal.end_read_tx();
    wal.stream_root_statements(1);
    assert_eq!(db.test_pins(), vec![(1, 1, false)], "one statement still runs");
    wal.stream_root_statements(0);
    assert!(db.test_pins().is_empty(), "the last statement released it");
    assert!(!wal.stream_snapshot_stale());
    // One statement: a new read transaction starts at the head.
    wal.stream_root_statements(1);
    assert!(wal.begin_read_tx().unwrap(), "the head moved");
    assert_eq!(db.test_pins(), vec![(2, 1, false)]);
    wal.end_read_tx();
    assert!(db.test_pins().is_empty());
    // A hold kept past the transaction for the one statement still
    // running: a read transaction begun outside any statement (a schema
    // probe) rejoins it too, and its end keeps it for that statement.
    wal.stream_root_statements(2);
    wal.begin_read_tx().unwrap();
    wal.end_read_tx();
    wal.stream_root_statements(1);
    assert!(!wal.stream_snapshot_stale());
    assert_eq!(commit_one(), 3);
    assert!(wal.stream_snapshot_stale(), "kept at 2 with the head at 3");
    assert!(
        !wal.begin_read_tx().unwrap(),
        "rejoined, not moved to the head"
    );
    assert_eq!(
        db.test_pins(),
        vec![(2, 1, false)],
        "still the running statement's version"
    );
    wal.end_read_tx();
    assert_eq!(
        db.test_pins(),
        vec![(2, 1, false)],
        "kept for the running statement"
    );
    wal.stream_root_statements(0);
    assert!(db.test_pins().is_empty());
    assert!(!wal.stream_snapshot_stale());
    // With nothing kept a lone statement starts at the head.
    wal.stream_root_statements(1);
    assert!(wal.begin_read_tx().unwrap(), "the head moved");
    assert_eq!(db.test_pins(), vec![(3, 1, false)], "only the new version");
    wal.end_read_tx();
    assert!(db.test_pins().is_empty());
    wal.stream_root_statements(0);
    let mut ops = Vec::new();
    db.take_ops(&mut ops);
    drop(ops);
    db.release_run();
}

// ---- review round 6: schema, BUSY_SNAPSHOT and outside reads on a kept
// snapshot --

/// Step `stmt` (any columns) to the end. Returns (rows, the error or step
/// result that stopped it, sleeps seen). A `Sleep` (busy handler) waits
/// 5 ms before the next step.
fn y_step_all(h: &mut H, stmt: &mut crate::Statement) -> (usize, Option<String>, usize) {
    let mut rows = 0;
    let mut sleeps = 0;
    for _ in 0..100_000 {
        let r = h.r.run(|| -> crate::Result<Option<String>> {
            loop {
                match stmt.step()? {
                    StepResult::Row => rows += 1,
                    StepResult::Done => return Ok(Some("Done".into())),
                    StepResult::IO | StepResult::Yield => return Ok(None),
                    o => return Ok(Some(format!("{o:?}"))),
                }
            }
        });
        match r {
            Ok(None) => {}
            Ok(Some(o)) if o == "Done" => return (rows, None, sleeps),
            Ok(Some(o)) if o.starts_with("Sleep") => {
                sleeps += 1;
                std::thread::sleep(std::time::Duration::from_millis(5));
            }
            Ok(Some(o)) => return (rows, Some(o), sleeps),
            Err(e) => return (rows, Some(e.to_string()), sleeps),
        }
    }
    (rows, Some("no progress".into()), sleeps)
}

/// A table `t` of 80 rows and an empty `u` on `h.conn`; a long scan of `t`
/// on it stepped 4 rows in. With `halt_first` a sibling statement on C
/// then runs to its end (its halt ends C's read transaction while the
/// scan still runs; the hold is kept).
fn r6_long_scan(h: &mut H, halt_first: bool) -> (crate::Statement, Vec<(i64, i64)>) {
    h.fill("t", 20);
    h.ok("CREATE TABLE u(x)");
    let c = h.conn.clone();
    let mut s = h.r.run(|| c.prepare("SELECT id, n FROM t")).unwrap();
    let (_, rows, o) = x_step(h, &mut s, 1000, 4, false);
    assert!(o.is_none(), "{o:?}");
    if halt_first {
        h.exec_on(&c, "SELECT count(*) FROM u", &[]).unwrap();
    }
    (s, rows)
}

/// Finish the long scan: all 80 rows, none of another connection's later
/// commit (n = 7), and no hold left once it is gone.
fn r6_finish_scan(h: &mut H, mut s: crate::Statement, mut rows: Vec<(i64, i64)>, what: &str) {
    let (done, rest, o) = x_step(h, &mut s, 100_000, usize::MAX, false);
    rows.extend(rest);
    drop(s);
    assert!(done && o.is_none(), "{what}: long scan done {done} {o:?}");
    assert_eq!(rows.len(), 80, "{what}: the scan ended early");
    assert_eq!(
        rows.iter().filter(|r| r.1 == 7).count(),
        0,
        "{what}: the scan saw a later commit"
    );
    assert!(
        h.sdb.test_pins().is_empty(),
        "{what}: holds left: {:?}",
        h.sdb.test_pins()
    );
}

/// C1 (review z1): D's DDL (after an UPDATE) while C keeps its snapshot
/// for a long scan, a sibling having ended C's read transaction. A new
/// statement on C compiles against its snapshot's schema, as SQLite does:
/// a table D's DDL did not touch reads fine (it used to fail "Database
/// schema changed" after 50 reprepares), the new table is not there yet,
/// and a write is BUSY_SNAPSHOT. Once the scan ends C takes the shared
/// schema again.
#[test]
fn r6_foreign_ddl_on_rejoined_snapshot() {
    for variant in [
        "SELECT count(*) FROM u",
        "SELECT count(*) FROM z",
        "INSERT INTO u VALUES (1)",
        "PREPARED-BEFORE",
    ] {
        let mut h = H::open(Cfg {
            slots: 64,
            ..Cfg::default()
        });
        let (s, rows) = r6_long_scan(&mut h, false);
        let c = h.conn.clone();
        let mut pre = h.r.run(|| c.prepare("SELECT count(*), 0 FROM u")).unwrap();
        h.exec_on(&c, "SELECT count(*) FROM u", &[]).unwrap();
        let d = h.connect();
        h.exec_on(&d, "UPDATE t SET n = 7", &[]).unwrap();
        h.exec_on(&d, "CREATE TABLE z(y)", &[]).unwrap();
        let r = if variant == "PREPARED-BEFORE" {
            let (rows, o, _) = y_step_all(&mut h, &mut pre);
            assert_eq!(rows, 1, "{variant}: {o:?}");
            o.map_or(Ok(()), Err)
        } else {
            drop(pre);
            rv_step_all(&mut h, &c, variant)
        };
        eprintln!("r6 z1 {variant}: {r:?}");
        match variant {
            "SELECT count(*) FROM z" => {
                let e = r.expect_err("z is not in C's snapshot");
                assert!(e.contains("no such table"), "{variant}: {e}");
            }
            "INSERT INTO u VALUES (1)" => {
                let e = r.expect_err("a write on a stale snapshot went in");
                assert!(is_busy_snapshot(&e), "{variant}: {e}");
            }
            _ => r.unwrap_or_else(|e| panic!("{variant}: {e}")),
        }
        assert_eq!(h.stats().blocking_calls, 0);
        r6_finish_scan(&mut h, s, rows, variant);
        // Back on the shared schema and the head.
        rv_step_all(&mut h, &c, "SELECT count(*) FROM z").unwrap();
        assert_eq!(h.one("SELECT sum(n) FROM t"), 7 * 80, "{variant}");
        c1_insert_u(&mut h, &c);
        h.check_invariants();
        integrity_on(&mut h, &d);
    }
}

fn c1_insert_u(h: &mut H, c: &Arc<Connection>) {
    rv_step_all(h, c, "INSERT INTO u VALUES (2)").unwrap();
}

/// C1 (review z5): D's DDL with and without a sibling's halt first, and a
/// statement prepared before it: all of it reads C's snapshot.
#[test]
fn r6_foreign_ddl_variants() {
    for (variant, halt_first) in [(0, false), (1, true), (2, false), (3, true)] {
        let mut h = H::open(Cfg {
            slots: 64,
            ..Cfg::default()
        });
        let (s, rows) = r6_long_scan(&mut h, halt_first);
        let c = h.conn.clone();
        let mut pre = h.r.run(|| c.prepare("SELECT count(*), 0 FROM u")).unwrap();
        let d = h.connect();
        h.exec_on(&d, "CREATE TABLE z(y)", &[]).unwrap();
        if variant % 2 == 1 {
            let (n, o, _) = y_step_all(&mut h, &mut pre);
            assert_eq!(
                (n, o.as_deref()),
                (1, None),
                "z5[{variant}] prepared before"
            );
        } else {
            drop(pre);
            rv_step_all(&mut h, &c, "SELECT count(*) FROM u")
                .unwrap_or_else(|e| panic!("z5[{variant}]: {e}"));
        }
        r6_finish_scan(&mut h, s, rows, &format!("z5[{variant}]"));
        rv_step_all(&mut h, &c, "SELECT count(*) FROM z").unwrap();
    }
}

/// W2 (review z2): a read transaction begun outside any statement
/// (`maybe_reparse_schema`) while the one statement left still runs on a
/// kept hold rejoins it: the scan neither moves to D's commit nor loses
/// its hold.
#[test]
fn r6_outside_read_while_one_statement_runs() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    let (s, rows) = r6_long_scan(&mut h, true);
    let c = h.conn.clone();
    let d = h.connect();
    h.exec_on(&d, "UPDATE t SET n = 7", &[]).unwrap();
    h.r.run(|| c.maybe_reparse_schema()).unwrap();
    assert!(
        c.pager.load().stream_snapshot_stale(),
        "the outside read released the hold"
    );
    r6_finish_scan(&mut h, s, rows, "z2");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 7 * 80);
}

/// Hold accounting (review z3): close with a live statement, an error
/// mid-scan, reset and re-step, and an own commit mid-scan, each with a
/// foreign commit in between: no hold outlives the statements.
#[test]
fn r6_hold_accounting_paths() {
    // Close with a live statement.
    {
        let mut h = H::open(Cfg {
            slots: 64,
            ..Cfg::default()
        });
        h.fill("t", 20);
        h.ok("CREATE TABLE u(x)");
        let c2 = h.connect();
        let mut s = h.r.run(|| c2.prepare("SELECT id, n FROM t")).unwrap();
        let _ = x_step(&mut h, &mut s, 1000, 4, false);
        h.exec_on(&c2, "SELECT count(*) FROM u", &[]).unwrap();
        let cl = h.r.run(|| c2.close());
        eprintln!("r6 z3 close with a live statement: {cl:?}");
        drop(s);
        drop(c2);
        assert!(
            h.sdb.test_pins().is_empty(),
            "close: {:?}",
            h.sdb.test_pins()
        );
    }
    // An error mid-scan on the long statement.
    {
        let mut h = H::open(Cfg {
            slots: 64,
            ..Cfg::default()
        });
        h.fill("t", 20);
        h.ok("CREATE TABLE u(x)");
        let c = h.conn.clone();
        let mut s = h
            .r
            .run(|| {
                c.prepare(
                    "SELECT id, CASE WHEN id = 30 THEN abs(-9223372036854775807 - 1) ELSE n END FROM t",
                )
            })
            .unwrap();
        let _ = x_step(&mut h, &mut s, 1000, 4, false);
        h.exec_on(&c, "SELECT count(*) FROM u", &[]).unwrap();
        let d = h.connect();
        h.exec_on(&d, "UPDATE t SET n = 7", &[]).unwrap();
        let (done, _, o) = x_step(&mut h, &mut s, 100_000, usize::MAX, false);
        assert!(
            !done && o.as_deref().is_some_and(|o| o.contains("overflow")),
            "err: {o:?}"
        );
        assert_eq!(
            h.one("SELECT sum(n) FROM t"),
            7 * 80,
            "the failed scan's snapshot stuck"
        );
        drop(s);
        assert!(h.sdb.test_pins().is_empty(), "err: {:?}", h.sdb.test_pins());
    }
    // Two long scans, an own commit mid-scan, a foreign commit, reset and
    // re-step one of them.
    {
        let mut h = H::open(Cfg {
            slots: 64,
            ..Cfg::default()
        });
        h.fill("t", 20);
        h.ok("CREATE TABLE u(x)");
        let c = h.conn.clone();
        let d = h.connect();
        let mut a = h.r.run(|| c.prepare("SELECT id, n FROM t")).unwrap();
        let mut b =
            h.r.run(|| c.prepare("SELECT id, n FROM t ORDER BY id DESC"))
                .unwrap();
        let _ = x_step(&mut h, &mut a, 1000, 4, false);
        let _ = x_step(&mut h, &mut b, 1000, 4, false);
        h.exec_on(&c, "UPDATE t SET n = 1 WHERE id = 1", &[])
            .unwrap();
        h.exec_on(&d, "UPDATE t SET n = 7 WHERE id > 1", &[])
            .unwrap();
        a.reset().unwrap();
        let (done, rows, o) = x_step(&mut h, &mut a, 100_000, usize::MAX, false);
        let sevens = rows.iter().filter(|r| r.1 == 7).count();
        eprintln!(
            "r6 z3 re-step a: done {done} rows {} sevens {sevens} {o:?}",
            rows.len()
        );
        assert!(done && o.is_none(), "a: {o:?}");
        assert_eq!(rows.len(), 80);
        assert_eq!(
            sevens, 0,
            "a re-stepped statement left the connection's snapshot"
        );
        let (done, rows, o) = x_step(&mut h, &mut b, 100_000, usize::MAX, false);
        assert!(done && o.is_none(), "b: {o:?}");
        assert_eq!(
            rows.iter().filter(|r| r.1 == 7).count(),
            0,
            "b saw the later commit"
        );
        drop(a);
        drop(b);
        assert!(h.sdb.test_pins().is_empty(), "{:?}", h.sdb.test_pins());
        assert_eq!(h.one("SELECT sum(n) FROM t"), 1 + 7 * 79);
    }
}

/// W1 (review z4, z6): a write on C's kept, stale snapshot under
/// busy_timeout fails BUSY_SNAPSHOT at once, whether C's read transaction
/// is still the long scan's or a sibling's halt ended it first; the busy
/// handler never sleeps on it.
#[test]
fn r6_stale_snapshot_write_fails_fast_under_busy_timeout() {
    for halt_first in [false, true] {
        let mut h = H::open(Cfg {
            slots: 64,
            ..Cfg::default()
        });
        let c = h.conn.clone();
        h.exec_on(&c, "PRAGMA busy_timeout = 2000", &[]).unwrap();
        let (s, rows) = r6_long_scan(&mut h, halt_first);
        let d = h.connect();
        h.exec_on(&d, "UPDATE t SET n = 7", &[]).unwrap();
        let mut ins = h.r.run(|| c.prepare("INSERT INTO u VALUES (1)")).unwrap();
        let t0 = std::time::Instant::now();
        let (_, o, sleeps) = y_step_all(&mut h, &mut ins);
        let took = t0.elapsed();
        drop(ins);
        eprintln!("r6 z6 halt_first={halt_first}: {o:?} sleeps {sleeps} after {took:?}");
        let e = o.expect("a write on a stale snapshot went in");
        assert!(is_busy_snapshot(&e), "halt_first={halt_first}: {e}");
        assert_eq!(
            sleeps, 0,
            "halt_first={halt_first}: the busy handler waited"
        );
        assert!(
            took < std::time::Duration::from_millis(1000),
            "halt_first={halt_first}: {took:?}"
        );
        r6_finish_scan(&mut h, s, rows, &format!("z6 halt_first={halt_first}"));
        // With the scan gone the write goes in.
        c1_insert_u(&mut h, &c);
    }
}

/// The P1 probe in its first form (explicit BEGIN, a first UPDATE, then a
/// full UPDATE squeezed to 2-6 credits), kept beside the x6 recipe of
/// `r4_busy_read_mid_statement_then_continue`.
#[test]
fn r4_busy_read_mid_statement_explicit_begin_sweep() {
    for credits in [2u32, 3, 4, 5, 6] {
        let mut h = H::open(Cfg {
            slots: 64,
            read_delay: 2,
            ..Cfg::default()
        });
        h.fill("t", 30);
        let w = h.conn.clone();
        h.ok("BEGIN");
        h.ok("UPDATE t SET n = 1 WHERE id = 1");
        let mut s =
            h.r.run(|| w.prepare("UPDATE t SET n = n + 1, v = zeroblob(950)"))
                .unwrap();
        let mut outcome = String::from("none");
        let mut busy = 0;
        h.r.credits = credits;
        for _ in 0..400 {
            let r = h.r.run(|| -> crate::Result<Option<String>> {
                loop {
                    match s.step()? {
                        StepResult::Row => {}
                        StepResult::Done => return Ok(Some("done".into())),
                        StepResult::IO | StepResult::Yield => return Ok(None),
                        o => return Ok(Some(format!("{o:?}"))),
                    }
                }
            });
            match r {
                Ok(None) => {}
                Ok(Some(x)) if x == "Busy" => {
                    busy += 1;
                    outcome = "busy".into();
                    break;
                }
                Ok(Some(x)) => {
                    outcome = x;
                    break;
                }
                Err(e) => {
                    outcome = format!("err {e}");
                    break;
                }
            }
        }
        h.r.credits = super::DEFAULT_CREDITS;
        let claims_after = h.sdb.test_claims();
        let mut fin = String::new();
        if busy > 0 {
            // Resume the same statement with a normal grant.
            let (done, _, other) = r4_step_rows(&mut h, &mut s, 10_000, usize::MAX);
            fin = format!("resumed done={done} other={other:?}");
        }
        drop(s);
        let st = h.stats();
        eprintln!(
            "r4 P1 credits={credits}: outcome {outcome}, claims after busy {claims_after:?}, {fin}, hard_rule_full {} credit_short {} doomed {}",
            st.hard_rule_full, st.credit_short, st.doomed
        );
        let commit = h.exec("COMMIT");
        eprintln!(
            "r4 P1 credits={credits}: commit {:?}",
            commit.as_ref().map(|_| ())
        );
        assert_eq!(st.hard_rule_full, 0, "credits={credits}: {st:?}");
        assert_eq!(st.credit_short, 0, "credits={credits}: {st:?}");
        let committed = commit.is_ok();
        let fresh = h.connect();
        let rows = h
            .exec_on(&fresh, "SELECT count(*), sum(n) FROM t", &[])
            .unwrap();
        let (count, sum) = (int(&rows[0][0]), int(&rows[0][1]));
        eprintln!("r4 P1 credits={credits}: fresh {count} rows sum {sum}");
        assert_eq!(count, 120);
        if committed {
            // The whole UPDATE (resumed to the end) or none of it.
            assert!(
                sum == 1 || sum == 121,
                "credits={credits}: partial update, sum {sum}"
            );
            if fin.starts_with("resumed done=true") {
                assert_eq!(sum, 121, "credits={credits}: a resumed update lost rows");
            }
        } else {
            assert_eq!(sum, 0, "credits={credits}: a failed commit landed");
        }
        integrity_on(&mut h, &fresh);
    }
}

// ---- review round 6 (tswr11): schema on a kept snapshot ----------------------

fn s7_rows(
    h: &mut H,
    c: &Arc<Connection>,
    sql: &str,
) -> std::result::Result<Vec<Vec<Value>>, String> {
    h.exec_on(c, sql, &[]).map_err(|e| e.to_string())
}

fn ints(v: &[i64]) -> Vec<Vec<Value>> {
    vec![v.iter().map(|&i| Value::from_i64(i)).collect()]
}

/// `r6_long_scan` with three rows in `u`.
fn s7_long_scan(h: &mut H, halt_first: bool) -> (crate::Statement, Vec<(i64, i64)>) {
    h.fill("t", 20);
    h.ok("CREATE TABLE u(x)");
    h.ok("INSERT INTO u VALUES (1), (2), (3)");
    let c = h.conn.clone();
    let mut s = h.r.run(|| c.prepare("SELECT id, n FROM t")).unwrap();
    let (_, rows, o) = x_step(h, &mut s, 1000, 4, false);
    assert!(o.is_none(), "{o:?}");
    if halt_first {
        h.exec_on(&c, "SELECT count(*) FROM u", &[]).unwrap();
    }
    (s, rows)
}

/// Step a statement of any columns to the end, collecting its rows.
fn s7_collect(
    h: &mut H,
    stmt: &mut crate::Statement,
) -> std::result::Result<Vec<Vec<Value>>, String> {
    let mut got = Vec::new();
    for _ in 0..100_000 {
        let r = h.r.run(|| -> crate::Result<Option<StepResult>> {
            loop {
                match stmt.step()? {
                    StepResult::Row => {
                        got.push(stmt.row().unwrap().get_values().cloned().collect())
                    }
                    StepResult::IO | StepResult::Yield => return Ok(None),
                    o => return Ok(Some(o)),
                }
            }
        });
        match r {
            Ok(None) => {}
            Ok(Some(StepResult::Done)) => return Ok(got),
            Ok(Some(o)) => return Err(format!("{o:?}")),
            Err(e) => return Err(e.to_string()),
        }
    }
    Err("no progress".into())
}

/// D's UPDATE then CREATE INDEX while C keeps its snapshot: C's reads
/// neither see the update nor know the index; a statement C prepared during
/// the hold runs on the shared schema once the scan is gone.
#[test]
fn s7_foreign_create_index_on_kept_snapshot() {
    for halt_first in [false, true] {
        let mut h = H::open(Cfg {
            slots: 64,
            ..Cfg::default()
        });
        let (s, rows) = s7_long_scan(&mut h, halt_first);
        let c = h.conn.clone();
        let d = h.connect();
        h.exec_on(&d, "UPDATE t SET n = 7 WHERE id <= 10", &[])
            .unwrap();
        h.exec_on(&d, "CREATE INDEX tn ON t(n)", &[]).unwrap();
        let what = format!("hf={halt_first}");
        assert_eq!(
            s7_rows(&mut h, &c, "SELECT count(*) FROM t WHERE n = 7"),
            Ok(ints(&[0])),
            "{what}: the held read saw D's update"
        );
        let e = s7_rows(
            &mut h,
            &c,
            "SELECT count(*) FROM t INDEXED BY tn WHERE n = 0",
        )
        .expect_err("the index is not in C's snapshot");
        assert!(e.contains("no such index"), "{what}: {e}");
        let mut pre =
            h.r.run(|| c.prepare("SELECT count(*) FROM t WHERE n = 7"))
                .unwrap();
        r6_finish_scan(&mut h, s, rows, &what);
        assert_eq!(s7_collect(&mut h, &mut pre), Ok(ints(&[10])), "{what}");
        drop(pre);
        assert_eq!(
            s7_rows(
                &mut h,
                &c,
                "SELECT count(*) FROM t INDEXED BY tn WHERE n = 7"
            ),
            Ok(ints(&[10])),
            "{what}"
        );
        assert_eq!(h.stats().blocking_calls, 0);
        h.check_invariants();
        integrity_on(&mut h, &c);
    }
}

/// D drops `u` and a new table reuses its pages while C keeps its
/// snapshot: C still reads `u` whole (a statement prepared before the DDL
/// too) and knows no `w`; afterwards it has the shared schema.
#[test]
fn s7_foreign_drop_and_page_reuse_on_kept_snapshot() {
    for halt_first in [false, true] {
        let mut h = H::open(Cfg {
            slots: 64,
            ..Cfg::default()
        });
        let (s, rows) = s7_long_scan(&mut h, halt_first);
        let c = h.conn.clone();
        let mut pre =
            h.r.run(|| c.prepare("SELECT count(*), sum(x) FROM u"))
                .unwrap();
        let d = h.connect();
        h.exec_on(&d, "DROP TABLE u", &[]).unwrap();
        h.exec_on(&d, "CREATE TABLE w(a)", &[]).unwrap();
        h.exec_on(&d, "INSERT INTO w SELECT 100 FROM t", &[])
            .unwrap();
        let what = format!("hf={halt_first}");
        assert_eq!(
            s7_rows(&mut h, &c, "SELECT count(*), sum(x) FROM u"),
            Ok(ints(&[3, 6])),
            "{what}"
        );
        let e =
            s7_rows(&mut h, &c, "SELECT count(*) FROM w").expect_err("w is not in C's snapshot");
        assert!(e.contains("no such table"), "{what}: {e}");
        assert_eq!(
            s7_collect(&mut h, &mut pre),
            Ok(ints(&[3, 6])),
            "{what}: prepared before"
        );
        drop(pre);
        r6_finish_scan(&mut h, s, rows, &what);
        let e = s7_rows(&mut h, &c, "SELECT count(*) FROM u").expect_err("u is gone");
        assert!(e.contains("no such table"), "{what}: {e}");
        assert_eq!(
            s7_rows(&mut h, &c, "SELECT count(*), sum(a) FROM w"),
            Ok(ints(&[80, 8000])),
            "{what}"
        );
        h.check_invariants();
        integrity_on(&mut h, &c);
    }
}

/// D's ALTER TABLE ADD COLUMN and an insert while C keeps its snapshot: C
/// reads the old one-column `u`; a statement C prepared during the hold
/// reprepares onto the new columns once the scan is gone.
#[test]
fn s7_foreign_alter_add_column_on_kept_snapshot() {
    for halt_first in [false, true] {
        let mut h = H::open(Cfg {
            slots: 64,
            ..Cfg::default()
        });
        let (s, rows) = s7_long_scan(&mut h, halt_first);
        let c = h.conn.clone();
        let d = h.connect();
        h.exec_on(&d, "ALTER TABLE u ADD COLUMN y DEFAULT 5", &[])
            .unwrap();
        h.exec_on(&d, "INSERT INTO u VALUES (4, 9)", &[]).unwrap();
        let what = format!("hf={halt_first}");
        let one = |x: i64| vec![Value::from_i64(x)];
        let two = |x: i64, y: i64| vec![Value::from_i64(x), Value::from_i64(y)];
        assert_eq!(
            s7_rows(&mut h, &c, "SELECT * FROM u"),
            Ok(vec![one(1), one(2), one(3)]),
            "{what}: the held read used the new schema"
        );
        let mut during = h.r.run(|| c.prepare("SELECT * FROM u")).unwrap();
        assert_eq!(during.num_columns(), 1, "{what}");
        r6_finish_scan(&mut h, s, rows, &what);
        let want = vec![two(1, 5), two(2, 5), two(3, 5), two(4, 9)];
        assert_eq!(s7_collect(&mut h, &mut during), Ok(want.clone()), "{what}");
        assert_eq!(
            during.num_columns(),
            2,
            "{what}: a statement compiled during the hold kept a stale schema"
        );
        drop(during);
        assert_eq!(s7_rows(&mut h, &c, "SELECT * FROM u"), Ok(want), "{what}");
        h.check_invariants();
        integrity_on(&mut h, &c);
    }
}

/// DDL on C itself while its own long scan runs: the DDL commits, C sees
/// its own schema at once, the scan reads neither the DDL nor D's later
/// update. Dropping the table being scanned fails the scan (as on plain
/// WAL, where turso lets the DROP free the pages under the cursor; SQLite
/// refuses the DROP with SQLITE_LOCKED instead) and leaves the database
/// intact.
#[test]
fn s7_own_ddl_mid_scan() {
    for ddl in [
        "CREATE INDEX tn2 ON t(n)",
        "ALTER TABLE t ADD COLUMN q DEFAULT 1",
        "CREATE TABLE k(a)",
        "DROP TABLE u",
        "DROP TABLE t",
    ] {
        for halt_first in [false, true] {
            let mut h = H::open(Cfg {
                slots: 64,
                ..Cfg::default()
            });
            let (mut s, mut rows) = s7_long_scan(&mut h, halt_first);
            let c = h.conn.clone();
            let what = format!("{ddl} hf={halt_first}");
            s7_rows(&mut h, &c, ddl).unwrap_or_else(|e| panic!("{what}: {e}"));
            let u = s7_rows(&mut h, &c, "SELECT count(*) FROM u");
            let d = h.connect();
            let dw = s7_rows(&mut h, &d, "UPDATE t SET n = 7 WHERE id > 70");
            let ct = s7_rows(&mut h, &c, "SELECT count(*) FROM t");
            if ddl == "DROP TABLE u" {
                assert!(u.unwrap_err().contains("no such table"), "{what}");
            } else {
                assert_eq!(u, Ok(ints(&[3])), "{what}");
            }
            if ddl == "DROP TABLE t" {
                assert!(dw.unwrap_err().contains("no such table"), "{what}");
                assert!(ct.unwrap_err().contains("no such table"), "{what}");
                let (done, rest, o) = x_step(&mut h, &mut s, 100_000, usize::MAX, false);
                rows.extend(rest);
                drop(s);
                assert!(
                    !done && o.is_some(),
                    "{what}: the scan of a dropped table ran on: {o:?}"
                );
                assert!(rows.iter().all(|r| r.1 != 7), "{what}");
                assert!(
                    h.sdb.test_pins().is_empty(),
                    "{what}: {:?}",
                    h.sdb.test_pins()
                );
            } else {
                dw.unwrap_or_else(|e| panic!("{what}: D's update: {e}"));
                assert_eq!(ct, Ok(ints(&[80])), "{what}");
                r6_finish_scan(&mut h, s, rows, &what);
                assert_eq!(h.one("SELECT count(*) FROM t WHERE n = 7"), 10, "{what}");
            }
            h.check_invariants();
            let fresh = h.connect();
            integrity_on(&mut h, &fresh);
        }
    }
}

/// An explicit BEGIN on C while it keeps a snapshot D has moved past (D
/// created a table and updated `t`): C's reads in the transaction see its
/// snapshot, its write fails BUSY_SNAPSHOT (not "Database schema changed"
/// after the reprepare limit), the read-only COMMIT succeeds, and once the
/// scan is gone C reads D's table and writes.
#[test]
fn s7_explicit_begin_on_kept_snapshot() {
    for halt_first in [false, true] {
        let mut h = H::open(Cfg {
            slots: 64,
            ..Cfg::default()
        });
        let (s, rows) = s7_long_scan(&mut h, halt_first);
        let c = h.conn.clone();
        let d = h.connect();
        h.exec_on(&d, "CREATE TABLE z(y)", &[]).unwrap();
        h.exec_on(&d, "UPDATE t SET n = 7", &[]).unwrap();
        let what = format!("hf={halt_first}");
        s7_rows(&mut h, &c, "BEGIN").unwrap();
        assert_eq!(
            s7_rows(&mut h, &c, "SELECT count(*) FROM u"),
            Ok(ints(&[3])),
            "{what}"
        );
        assert_eq!(
            s7_rows(&mut h, &c, "SELECT count(*) FROM t WHERE n = 7"),
            Ok(ints(&[0])),
            "{what}"
        );
        let e = s7_rows(&mut h, &c, "INSERT INTO u VALUES (9)").expect_err("a stale write went in");
        assert!(is_busy_snapshot(&e), "{what}: {e}");
        s7_rows(&mut h, &c, "COMMIT").unwrap_or_else(|e| panic!("{what}: commit: {e}"));
        r6_finish_scan(&mut h, s, rows, &what);
        assert_eq!(
            s7_rows(&mut h, &c, "SELECT count(*) FROM z"),
            Ok(ints(&[0])),
            "{what}"
        );
        s7_rows(&mut h, &c, "INSERT INTO u VALUES (10)").unwrap_or_else(|e| panic!("{what}: {e}"));
        assert_eq!(h.one("SELECT count(*) FROM u WHERE x = 9"), 0, "{what}");
        assert_eq!(h.one("SELECT count(*) FROM u WHERE x = 10"), 1, "{what}");
        h.check_invariants();
        integrity_on(&mut h, &c);
    }
}

/// A write on C meets D's open write transaction (BUSY) while C's scan
/// holds; the scan ends and D commits; the retry of the same statement
/// fails BUSY_SNAPSHOT once (its read transaction is the old version), the
/// next retry goes in, and nothing is held after.
#[test]
fn s7_busy_then_scan_ends_then_retry() {
    let mut h = H::open(Cfg {
        slots: 64,
        ..Cfg::default()
    });
    let (s, rows) = s7_long_scan(&mut h, true);
    let c = h.conn.clone();
    let d = h.connect();
    h.exec_on(&d, "BEGIN", &[]).unwrap();
    h.exec_on(&d, "UPDATE t SET n = 7 WHERE id = 1", &[])
        .unwrap();
    let mut x = h.r.run(|| c.prepare("INSERT INTO u VALUES (50)")).unwrap();
    let (_, o, _) = y_step_all(&mut h, &mut x);
    assert_eq!(o.as_deref(), Some("Busy"), "first try");
    r6_finish_scan_keeping(&mut h, s, rows, "s7 busy");
    h.exec_on(&d, "COMMIT", &[]).unwrap();
    let (_, o, _) = y_step_all(&mut h, &mut x);
    let e = o.expect("the retry on the old version went in");
    assert!(is_busy_snapshot(&e), "retry: {e}");
    let (_, o, _) = y_step_all(&mut h, &mut x);
    assert_eq!(o, None, "second retry");
    drop(x);
    assert!(h.sdb.test_pins().is_empty(), "{:?}", h.sdb.test_pins());
    s7_rows(&mut h, &c, "INSERT INTO u VALUES (51)").unwrap();
    assert_eq!(h.one("SELECT count(*) FROM u WHERE x >= 50"), 2);
    assert_eq!(h.one("SELECT count(*) FROM t WHERE n = 7"), 1);
    h.check_invariants();
    integrity_on(&mut h, &c);
}

/// `r6_finish_scan` for a connection whose other statement (a write that
/// got BUSY) still holds its read version: the scan is whole and saw no
/// later commit; the hold may stay.
fn r6_finish_scan_keeping(
    h: &mut H,
    mut s: crate::Statement,
    mut rows: Vec<(i64, i64)>,
    what: &str,
) {
    let (done, rest, o) = x_step(h, &mut s, 100_000, usize::MAX, false);
    rows.extend(rest);
    drop(s);
    assert!(done && o.is_none(), "{what}: long scan done {done} {o:?}");
    assert_eq!(rows.len(), 80, "{what}: the scan ended early");
    assert!(
        rows.iter().all(|r| r.1 != 7),
        "{what}: the scan saw a later commit"
    );
}
