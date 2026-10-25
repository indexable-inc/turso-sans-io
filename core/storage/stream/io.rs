//! The `IO` a stream database runs on. It owns no files: database pages go
//! through [`super::StreamStorage`] and [`super::StreamWal`], and temporary
//! files (sorters, ephemeral tables) live in memory. It never blocks:
//! `step` is the only way Turso waits synchronously, so it fails, and
//! counts the call, instead of spinning.

use super::StreamDb;
use crate::io::{Clock, File, MemoryIO, OpenFlags, IO};
use crate::sync::atomic::{AtomicU64, Ordering};
use crate::sync::Arc;
use crate::{LimboError, MonotonicInstant, Result, WallClockInstant};

pub struct StreamIo {
    db: Arc<StreamDb>,
    temp: MemoryIO,
    /// Embedder clock, milliseconds since the Unix epoch.
    now_ms: AtomicU64,
    rng: AtomicU64,
}

impl StreamIo {
    pub fn new(db: Arc<StreamDb>, seed: u64) -> Arc<Self> {
        Arc::new(Self {
            db,
            temp: MemoryIO::new(),
            now_ms: AtomicU64::new(0),
            rng: AtomicU64::new(seed | 1),
        })
    }

    pub fn db(&self) -> &Arc<StreamDb> {
        &self.db
    }

    /// The embedder's clock (call at the start of each run).
    pub fn set_time_ms(&self, ms: u64) {
        self.now_ms.store(ms, Ordering::Relaxed);
    }

    fn next_u64(&self) -> u64 {
        // splitmix64 over an atomic counter: deterministic per seed.
        let x = self.rng.fetch_add(0x9E37_79B9_7F4A_7C15, Ordering::Relaxed);
        let mut z = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

impl Clock for StreamIo {
    fn current_time_monotonic(&self) -> MonotonicInstant {
        MonotonicInstant::from_nanos(self.now_ms.load(Ordering::Relaxed) as u128 * 1_000_000)
    }

    fn current_time_wall_clock(&self) -> WallClockInstant {
        let ms = self.now_ms.load(Ordering::Relaxed);
        WallClockInstant {
            secs: (ms / 1000) as i64,
            micros: ((ms % 1000) * 1000) as u32,
        }
    }
}

impl IO for StreamIo {
    fn open_file(&self, path: &str, flags: OpenFlags, direct: bool) -> Result<Arc<dyn File>> {
        self.temp.open_file(path, flags, direct)
    }

    fn remove_file(&self, path: &str) -> Result<()> {
        self.temp.remove_file(path)
    }

    fn step(&self) -> Result<()> {
        self.db.bump(|s| s.blocking_calls += 1);
        Err(LimboError::InternalError(
            "stream IO never blocks: a caller waited synchronously (IO::step)".into(),
        ))
    }

    fn generate_random_number(&self) -> i64 {
        self.next_u64() as i64
    }

    fn fill_bytes(&self, dest: &mut [u8]) {
        for chunk in dest.chunks_mut(8) {
            let v = self.next_u64().to_le_bytes();
            chunk.copy_from_slice(&v[..chunk.len()]);
        }
    }

    fn yield_now(&self) {
        self.db.bump(|s| s.blocking_calls += 1);
    }

    fn sleep(&self, _duration: std::time::Duration) {
        self.db.bump(|s| s.blocking_calls += 1);
    }

    fn file_id(&self, path: &str) -> Result<crate::io::FileId> {
        self.temp.file_id(path)
    }
}
