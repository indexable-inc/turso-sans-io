//! `Wal` over the stream (§14 mapping table).
//!
//! There is no log: a committed page is a page of the stream at some
//! version, and an uncommitted page the writer spilled is in a staged part
//! of its open transaction. So `find_frame` answers "yes" for every page
//! (the frame id is the page id) and `read_frame` reads the stream at the
//! connection's version: `Latest` for the writer (staged parts included),
//! the pinned snapshot for a reader. Commit, spill and savepoint rollback
//! are the pager's (`pager/stream_ext.rs`); the log-shaped methods are
//! no-ops or unreachable.

use super::{ReadAt, StreamDb};
use crate::io::{Buffer, Completion, CompletionGroup, File, FileSyncType};
use crate::storage::buffer_pool::BufferPool;
use crate::storage::database::IOContext;
use crate::storage::pager::{PageRef, Pager};
use crate::storage::sqlite3_ondisk::{finish_read_page, PageSize};
use crate::storage::wal::{
    CheckpointMode, CheckpointResult, PreparedFrames, RollbackTo, Wal, WalAutoActions,
};
use crate::sync::atomic::{AtomicBool, AtomicI32, AtomicU64, Ordering};
use crate::sync::Arc;
use crate::types::{IOResult, IOResultOr};
use crate::{CompletionError, LimboError, Result, SyncMode};

#[derive(Debug)]
pub struct StreamWal {
    db: Arc<StreamDb>,
    read_version: AtomicU64,
    /// Head this connection's cache matches.
    seen: AtomicU64,
    reading: AtomicBool,
    writing: AtomicBool,
    /// This connection holds `read_version` (one `StreamDb::hold`). A read
    /// transaction implies it; it outlives the transaction while other
    /// statements on the connection are still active (`end_read_tx`).
    holding: AtomicBool,
    /// The connection's active root statements, as last told by
    /// `stream_root_statements`.
    statements: AtomicI32,
}

impl StreamWal {
    pub fn new(db: Arc<StreamDb>) -> Self {
        let head = db.head();
        Self {
            db,
            read_version: AtomicU64::new(head),
            seen: AtomicU64::new(head),
            reading: AtomicBool::new(false),
            writing: AtomicBool::new(false),
            holding: AtomicBool::new(false),
            statements: AtomicI32::new(0),
        }
    }

    pub fn db(&self) -> &Arc<StreamDb> {
        &self.db
    }

    /// The writer reads `Latest` (its staged parts included); everyone
    /// else reads its snapshot. With no read transaction open (a sibling
    /// statement's autocommit ended it while this one is still stepping)
    /// that is still the connection's last read version, which is what its
    /// page cache holds and what the connection still holds (`holding`):
    /// never `Latest`, which would show another connection's staged,
    /// uncommitted pages. A read with no hold left takes a pin of its own
    /// (0 holders, unpinned when it completes); a version the store has
    /// dropped fails the statement SQLITE_BUSY.
    fn read_at(&self) -> ReadAt {
        if self.writing.load(Ordering::Acquire) {
            ReadAt::Latest
        } else {
            ReadAt::Version(self.read_version.load(Ordering::Acquire))
        }
    }

    /// Give up the hold on `read_version`, if it is still taken.
    fn release_hold(&self) {
        if self.holding.swap(false, Ordering::AcqRel) {
            self.db.release(self.read_version.load(Ordering::Acquire));
        }
    }

    /// The writer gives up its own store transaction (rollback, end of
    /// the write). A test can skip it to leave a transaction behind, as a
    /// writer gone without either would; `begin_write_tx`'s abort of a
    /// leftover is never skipped.
    fn abort_own(&self) {
        if !self.db.test_skips_end_abort() {
            self.db.txn_abort();
        }
    }

    fn unreached(what: &str) -> LimboError {
        LimboError::InternalError(format!("stream wal: {what} is not on the stream path"))
    }

    fn done() -> Completion {
        Completion::new_yield()
    }
}

/// A read completion that installs `buf` into `page` (the read lands in
/// the slot itself; there is no copy).
pub(crate) fn page_read_completion(page: PageRef, page_idx: usize, buf: Arc<Buffer>) -> Completion {
    let complete = Box::new(
        move |res: std::result::Result<(Arc<Buffer>, i32), CompletionError>| {
            let Ok((buf, n)) = res else {
                page.clear_locked();
                return None;
            };
            if n as usize != buf.len() {
                page.clear_locked();
                return Some(CompletionError::ShortRead {
                    page_idx,
                    expected: buf.len(),
                    actual: n as usize,
                });
            }
            finish_read_page(page_idx, buf, page.clone());
            None
        },
    );
    Completion::new_read(buf, complete)
}

impl Wal for StreamWal {
    /// A read transaction that starts while another statement on the
    /// connection is still active (the caller is one of `statements`) and
    /// the connection still holds its last version rejoins that version, as
    /// SQLite keeps one read transaction while `nVdbeRead > 0`: the running
    /// statement's cursors and the page cache stay valid, and every
    /// statement on the connection reads one snapshot. A write on it after
    /// another connection committed fails SQLITE_BUSY_SNAPSHOT
    /// (`begin_write_tx`). Otherwise it starts at the head.
    fn begin_read_tx(&self) -> Result<bool> {
        if !self.reading.load(Ordering::Acquire)
            && self.holding.load(Ordering::Acquire)
            && self.statements.load(Ordering::Acquire) > 1
        {
            self.reading.store(true, Ordering::Release);
            let rv = self.read_version.load(Ordering::Acquire);
            return Ok(self.seen.swap(rv, Ordering::AcqRel) != rv);
        }
        let head = self.db.head();
        let old = self.read_version.swap(head, Ordering::AcqRel);
        if !self.holding.swap(true, Ordering::AcqRel) {
            self.db.hold(head);
        } else if old != head {
            // Already holding `old` (reading, or kept past the last read
            // transaction): move the hold, or `old` stays held (and pinned)
            // forever while `end_read_tx` releases `head`.
            self.db.hold(head);
            self.db.release(old);
        }
        self.reading.store(true, Ordering::Release);
        let changed = self.seen.swap(head, Ordering::AcqRel) != head;
        Ok(changed)
    }

    fn stream_root_statements(&self, active: i32) {
        self.statements.store(active, Ordering::Release);
        // The last statement is gone: a hold kept past the read
        // transaction has no reader left.
        if active <= 0 && !self.reading.load(Ordering::Acquire) {
            self.release_hold();
        }
    }

    fn mvcc_refresh_if_db_changed(&self) -> bool {
        false
    }

    fn stream_read_at(&self) -> Option<ReadAt> {
        Some(self.read_at())
    }

    fn begin_write_tx(&self, _allowed: WalAutoActions) -> Result<()> {
        if self.writing.load(Ordering::Acquire) {
            return Ok(());
        }
        if !self.db.try_lock_writer() {
            return Err(LimboError::Busy);
        }
        let rv = self.read_version.load(Ordering::Acquire);
        let head = self.db.head();
        if self.reading.load(Ordering::Acquire) && rv != head {
            // Version 1 is the page-1 init batch (`allocate_page1`), which
            // the first writer issues inside its own write; to a reader of
            // the empty version 0 it changes nothing it could have read.
            if rv == 0 && head == 1 {
                self.db.hold(1);
                self.db.release(0);
                self.read_version.store(1, Ordering::Release);
                self.seen.store(1, Ordering::Release);
            } else {
                self.db.unlock_writer();
                return Err(LimboError::BusySnapshot);
            }
        }
        self.writing.store(true, Ordering::Release);
        // Only a writer opens a store transaction, and none holds the lock
        // now: one still open is a gone writer's (a connection dropped
        // mid-transaction). It must never carry into this one.
        self.db.txn_abort();
        Ok(())
    }

    /// The hold stays while another statement than the one ending (the
    /// caller is one of `statements`) is still active: it may still be
    /// stepping at this version (upstream ends the connection's read
    /// transaction when a sibling halts), and a later statement rejoins it
    /// (`begin_read_tx`). The last statement's end releases it
    /// (`stream_root_statements`).
    fn end_read_tx(&self) {
        if self.reading.swap(false, Ordering::AcqRel)
            && self.statements.load(Ordering::Acquire) <= 1
        {
            self.release_hold();
        }
    }

    fn end_write_tx(&self) {
        if self.writing.swap(false, Ordering::AcqRel) {
            // A write transaction that ends without its commit (a dropped
            // connection, a rollback) leaves nothing open on the store.
            self.abort_own();
            // The head is ours (we hold the writer lock): our commit's, or
            // unchanged after a rollback. The cache matches it (the pager
            // clears it on rollback), so it is the version this
            // connection's statements read at from here, moving the hold
            // with it if a read transaction is still open.
            let head = self.db.head();
            let old = self.read_version.swap(head, Ordering::AcqRel);
            if old != head && self.holding.load(Ordering::Acquire) {
                self.db.hold(head);
                self.db.release(old);
            }
            self.seen.store(head, Ordering::Release);
            self.db.unlock_writer();
        }
    }

    fn holds_read_lock(&self) -> bool {
        self.reading.load(Ordering::Acquire)
    }

    fn holds_write_lock(&self) -> bool {
        self.writing.load(Ordering::Acquire)
    }

    fn should_checkpoint_on_close(&self) -> bool {
        false
    }

    fn find_frame(&self, page_id: u64, _frame_watermark: Option<u64>) -> Result<Option<u64>> {
        Ok(Some(page_id))
    }

    fn read_frame(
        &self,
        frame_id: u64,
        page: PageRef,
        buffer_pool: Arc<BufferPool>,
        group: Option<&mut CompletionGroup>,
    ) -> Result<Completion> {
        // The pager made room (a free slot and a credit) before the miss.
        let Some(buf) = buffer_pool.try_get_page() else {
            self.db.bump(|s| s.hard_rule_full += 1);
            return Err(super::full());
        };
        let buf = Arc::new(buf);
        page.set_locked();
        let c = page_read_completion(page.clone(), frame_id as usize, buf.clone());
        // The op only goes out at the end of the run, so adding it to the
        // group after it is queued is still before it is submitted; a read
        // that was never queued must not sit in the group.
        match self.db.read(self.read_at(), frame_id - 1, &buf, c) {
            Ok(Some(c)) => {
                if let Some(group) = group {
                    group.add(&c);
                }
                Ok(c)
            }
            Ok(None) => {
                page.clear_locked();
                Err(LimboError::InternalError(
                    "stream: page read with no op credit".into(),
                ))
            }
            Err(e) => {
                page.clear_locked();
                Err(e)
            }
        }
    }

    fn read_frames_batch(
        &self,
        _start_frame: u64,
        _pages: &[PageRef],
        _buffer_pool: Arc<BufferPool>,
        _scratch_buf: Option<Arc<Buffer>>,
        _group: Option<&mut CompletionGroup>,
    ) -> Result<Completion> {
        Err(Self::unreached("read_frames_batch (VACUUM)"))
    }

    fn read_frame_raw(&self, _frame_id: u64, _frame: &mut [u8]) -> Result<Completion> {
        Err(Self::unreached("read_frame_raw"))
    }

    fn write_frame_raw(
        &self,
        _buffer_pool: Arc<BufferPool>,
        _frame_id: u64,
        _page_id: u64,
        _db_size: u64,
        _page: &[u8],
        _sync_type: FileSyncType,
    ) -> Result<()> {
        Err(Self::unreached("write_frame_raw"))
    }

    fn prepare_wal_start(&self, _page_sz: PageSize) -> Result<Option<Completion>> {
        Ok(None)
    }

    fn prepare_wal_finish(&self, _sync_type: FileSyncType) -> Result<Completion> {
        Ok(Self::done())
    }

    fn prepare_frames(
        &self,
        _pages: &[PageRef],
        _page_sz: PageSize,
        _db_size_on_commit: Option<u32>,
        _prev: Option<&PreparedFrames>,
    ) -> Result<PreparedFrames> {
        Err(Self::unreached("prepare_frames"))
    }

    fn commit_prepared_frames(&self, _prepared: &[PreparedFrames]) {}

    fn finalize_committed_pages(&self, _prepared: &[PreparedFrames]) {}

    fn wal_file(&self) -> Result<Arc<dyn File>> {
        Err(Self::unreached("wal_file"))
    }

    fn append_frames_vectored(
        &self,
        _pages: Vec<PageRef>,
        _page_sz: PageSize,
    ) -> Result<Completion> {
        Err(Self::unreached("append_frames_vectored"))
    }

    fn finish_append_frames_commit(&self) -> Result<()> {
        Ok(())
    }

    fn should_checkpoint(&self, _checkpoint_threshold: u32) -> bool {
        false
    }

    fn checkpoint(
        &self,
        _pager: &Pager,
        _mode: CheckpointMode,
        _sync_mode: SyncMode,
    ) -> IOResultOr<CheckpointResult> {
        Ok(IOResult::Done(CheckpointResult::new(0, 0, 0)))
    }

    fn install_durable_backfill_proof(
        &self,
        _max_frame: u64,
        _db_size_pages: u32,
        _db_header_crc32c: u32,
        _sync_type: FileSyncType,
    ) -> Result<Option<Completion>> {
        Ok(None)
    }

    fn publish_backfill(&self, _max_frame: u64) {}

    fn sync(&self, _sync_type: FileSyncType) -> Result<Completion> {
        Ok(Self::done())
    }

    fn is_syncing(&self) -> bool {
        false
    }

    fn is_dirty(&self) -> bool {
        false
    }

    fn get_max_frame_in_wal(&self) -> u64 {
        0
    }

    fn get_checkpoint_seq(&self) -> u32 {
        0
    }

    fn get_max_frame(&self) -> u64 {
        0
    }

    fn connection_wal_pos(&self) -> (u32, u64) {
        (0, 0)
    }

    fn min_pinned_read_frame(&self) -> Option<u64> {
        None
    }

    fn get_min_frame(&self) -> u64 {
        0
    }

    fn backfill_frame(&self) -> u64 {
        0
    }

    fn rollback(&self, rollback_to: Option<RollbackTo>) {
        // A savepoint rollback keeps the staged parts: the pager discards
        // the grown range and restores pre-images over them (fork change 3).
        // Only the writer's transaction is open on the store; a reader's
        // rollback must not abort it.
        if rollback_to.is_none() && self.writing.load(Ordering::Acquire) {
            self.abort_own();
        }
    }

    fn abort_checkpoint(&self) {}

    fn get_last_checksum(&self) -> (u32, u32) {
        (0, 0)
    }

    fn changed_pages_after(&self, _frame_watermark: u64) -> Result<Vec<u32>> {
        Ok(Vec::new())
    }

    fn set_io_context(&self, _ctx: IOContext) {}

    fn update_max_frame(&self) {}

    fn truncate_wal(
        &self,
        _result: &mut CheckpointResult,
        _sync_type: FileSyncType,
    ) -> IOResultOr<()> {
        Ok(IOResult::Done(()))
    }

    fn try_begin_vacuum_checkpoint_lock(&self) -> Result<()> {
        Err(Self::unreached("VACUUM"))
    }

    fn release_vacuum_checkpoint_lock(&self) {}

    fn begin_vacuum_blocking_tx(&self) -> Result<()> {
        Err(Self::unreached("VACUUM"))
    }

    fn vacuum_checkpoint_with_held_lock(
        &self,
        _pager: &Pager,
        _sync_mode: SyncMode,
    ) -> IOResultOr<CheckpointResult> {
        Err(Box::new(Self::unreached("VACUUM")))
    }

    fn release_vacuum_lock(&self) {}

    #[cfg(any(test, debug_assertions))]
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}
