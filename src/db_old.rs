// db.rs

use std::sync::Arc;

use anyhow::{Context, Result};
use bincode::deserialize;

use alloy::eips::BlockId;
use alloy::network::Ethereum;
use alloy::providers::RootProvider;

use revm::database::{AlloyDB, CacheDB, EmptyDB, WrapDatabaseAsync};

use crate::EVMSimulatorSnapshot;

/// Offline backend that never performs network fetches.
/// Using `EmptyDB` ensures the enclave run has no RPC access.
pub type NoFetchDB = EmptyDB;

/// Build a fetching database backed by Alloy + WrapDatabaseAsync (host-side).
/// This is your current online DB that can lazily load from the RPC.
pub fn make_fetching_db(
    provider: &Arc<RootProvider<Ethereum>>,
    block_id: BlockId,
) -> Result<CacheDB<WrapDatabaseAsync<AlloyDB<Ethereum, Arc<RootProvider<Ethereum>>>>>> {
    let alloy_db = AlloyDB::new(provider.clone(), block_id);
    let wrapped_db = WrapDatabaseAsync::new(alloy_db)
        .context("Failed to wrap AlloyDB with WrapDatabaseAsync")?;
    Ok(CacheDB::new(wrapped_db))
}

/// Build an offline database that will never perform network fetches.
/// Use this in the enclave when you *don’t* need preloaded state.
pub fn make_offline_db() -> CacheDB<NoFetchDB> {
    let nofetch = NoFetchDB::default();
    CacheDB::new(nofetch)
}

/// Build an offline database from a pre-warmed snapshot (enclave-side).
/// Restores the `CacheDB.cache` from `EVMSimulatorSnapshot.db` so the enclave
/// can simulate entirely offline (no RPC).
pub fn make_offline_db_from_snapshot(
    snapshot: &EVMSimulatorSnapshot,
) -> Result<CacheDB<NoFetchDB>> {
    let mut cache_db = make_offline_db();

    if snapshot.db.is_empty() {
        // Nothing to load — caller may still proceed, but simulation will
        // only succeed if the cache already contains everything needed.
        return Ok(cache_db);
    }

    // The blob was produced by `bincode::serialize(&self.db.cache)`
    // in EVMSimulator::to_snapshot().
    let restored_cache =
        deserialize(&snapshot.db).context("Failed to deserialize snapshot DB cache")?;

    cache_db.cache = restored_cache;
    Ok(cache_db)
}
