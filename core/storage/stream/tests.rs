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
/// read), and the next run finishes the free.
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
                pager1.stream_test_squeeze(None);
                pager.stream_test_squeeze(Some(trunk_id));
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
    h.fill("t", 100);
    let reader = h.connect();
    let conn = h.conn.clone();
    h.ok("BEGIN");
    h.ok("SAVEPOINT a");
    let mut update = h.r.run(|| conn.prepare("UPDATE t SET n = n + 1")).unwrap();
    // (statement, its connection is the writer's, rows seen)
    let mut other: Option<(crate::Statement, bool, i64)> = None;
    let (mut ended, mut sibling_ended) = (0u32, 0u32);
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
                if step(s, rows) {
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
    h.ok("COMMIT");
    assert_eq!(h.one("SELECT sum(n) FROM t"), 400);
    let rows = h.exec_on(&reader, "SELECT sum(n) FROM t", &[]).unwrap();
    assert_eq!(int(&rows[0][0]), 400);
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

/// Round-2 C7 (spec case): the store's quota refuses the spill a
/// savepoint restore needs. The transaction is doomed and aborted on the
/// store, the statement fails SQLITE_FULL, and nothing of it commits.
#[test]
fn quota_refusing_a_restore_spill_dooms_the_txn() {
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
