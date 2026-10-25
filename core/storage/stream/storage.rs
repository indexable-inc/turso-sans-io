//! `DatabaseStorage` over the stream. Only the open path reads through it
//! (the header, page 1); every other page read goes through
//! [`super::StreamWal::read_frame`], and nothing writes through it: commits
//! are store transactions issued by the pager.

use super::{ReadAt, StreamDb, PAGE_SIZE};
use crate::io::{Buffer, Completion, FileSyncType};
use crate::storage::database::{DatabaseStorage, IOContext};
use crate::sync::Arc;
use crate::{LimboError, Result};

pub struct StreamStorage {
    db: Arc<StreamDb>,
}

impl StreamStorage {
    pub fn new(db: Arc<StreamDb>) -> Self {
        Self { db }
    }

    fn read(&self, page: u64, c: Completion) -> Result<Completion> {
        let buf: Arc<Buffer> = c.as_read().buf_arc();
        match self.db.read(ReadAt::Latest, page, &buf, c)? {
            Some(c) => Ok(c),
            None => Err(LimboError::InternalError(
                "stream: no op credit for a storage read".into(),
            )),
        }
    }

    fn unreached(what: &str) -> LimboError {
        LimboError::InternalError(format!("stream storage: {what} is not on the stream path"))
    }
}

impl DatabaseStorage for StreamStorage {
    fn read_header(&self, c: Completion) -> Result<Completion> {
        self.read(0, c)
    }

    fn read_page(&self, page_idx: usize, _io_ctx: &IOContext, c: Completion) -> Result<Completion> {
        if page_idx == 0 {
            return Err(LimboError::Corrupt(
                "attempted to read page 0 (page numbers start at 1)".into(),
            ));
        }
        self.read(page_idx as u64 - 1, c)
    }

    fn write_page(
        &self,
        _: usize,
        _: Arc<Buffer>,
        _: &IOContext,
        _: Completion,
    ) -> Result<Completion> {
        Err(Self::unreached("write_page"))
    }

    fn write_pages(
        &self,
        _: usize,
        _: usize,
        _: Vec<Arc<Buffer>>,
        _: &IOContext,
        _: Completion,
    ) -> Result<Completion> {
        Err(Self::unreached("write_pages"))
    }

    fn sync(&self, c: Completion, _: FileSyncType) -> Result<Completion> {
        // Durability is the store's: a sync has nothing to wait for.
        c.complete(0);
        Ok(c)
    }

    fn size(&self) -> Result<u64> {
        // Only "empty or not" is asked of it (database init, orphan-WAL
        // check); the page count lives in the header.
        Ok(if self.db.head() == 0 {
            0
        } else {
            PAGE_SIZE as u64
        })
    }

    fn truncate(&self, _: usize, _: Completion) -> Result<Completion> {
        Err(Self::unreached("truncate"))
    }

    fn stream_db(&self) -> Option<Arc<StreamDb>> {
        Some(self.db.clone())
    }
}
