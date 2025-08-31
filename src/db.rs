use std::sync::Arc;

use anyhow::{Context, Result};

use bincode::deserialize;

use alloy::eips::BlockId;
use alloy::network::Ethereum;
use alloy::providers::RootProvider;

use revm::database::{AlloyDB, CacheDB, EmptyDB, WrapDatabaseAsync};
use crate::simulator::EVMSimulatorSnapshot;

// DB for the host, which can access an RPC provider.
pub type OnlineDB = WrapDatabaseAsync<AlloyDB<Ethereum, Arc<RootProvider<Ethereum>>>>;

// DB for the enclave, which cannot access an RPC provider.
pub type OfflineDB = EmptyDB;

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
pub fn make_offline_db() -> CacheDB<OfflineDB> {
    let nofetch = OfflineDB::default();
    CacheDB::new(nofetch)
}

/// Build an offline database from a pre-warmed snapshot. This is meant for the enclave.
/// Restores the `CacheDB.cache` from `EVMSimulatorSnapshot.db` so the enclave
/// can simulate entirely offline (no RPC).
pub fn make_offline_db_from_snapshot(
    snapshot: &EVMSimulatorSnapshot,
) -> Result<CacheDB<OfflineDB>> {
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
