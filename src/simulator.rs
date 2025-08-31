use std::sync::Arc;
use std::collections::{HashMap, HashSet};

use bincode::serialize;

use anyhow::{Result, anyhow};

use serde::{Deserialize, Serialize};

use alloy::eips::BlockId;
use alloy::network::Ethereum;
use alloy::consensus::Account;
use alloy::providers::{Provider, RootProvider};
use alloy::rpc::types::EIP1186AccountProofResponse;
use alloy::primitives::{
    Address, B256, Bytes, KECCAK256_EMPTY, U256, aliases::StorageKey, keccak256,
};
use alloy_trie::{Nibbles, proof::verify_proof};

use revm::ExecuteCommitEvm;
use revm::{Context, Database, InspectEvm, MainBuilder, MainContext};
use revm::database::{CacheDB, DatabaseRef, DBTransportError};
use revm::primitives::{TxKind, hash_map::Entry};
use revm::state::AccountInfo;

use revm_context::result::ExecutionResult;
use revm_context::result::EVMError;

use revm_inspectors::tracing::{
    CallTraceArena, StackSnapshotType, TracingInspector, TracingInspectorConfig,
};

use crate::db::{make_fetching_db, OnlineDB, OfflineDB};

const TRANSFER_GAS_COST: u64 = 21_000; // Standard gas cost for an ETH transfer
                                       //
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct ProofData {
    pub account_proofs: Vec<EIP1186AccountProofResponse>,
    pub storage_proofs: HashMap<Address, EIP1186AccountProofResponse>,
}

pub struct EVMSimulator<ExtDB: DatabaseRef> {
    pub provider: Option<Arc<RootProvider<Ethereum>>>,
    pub provider_url: Option<String>,
    pub chain_id: u64,
    pub block_num: u64,
    pub block_hash: B256,
    pub state_root: B256,
    pub db: CacheDB<ExtDB>,
    pub account_proofs: HashMap<Address, EIP1186AccountProofResponse>,
    pub storage_proofs: HashMap<Address, HashMap<StorageKey, EIP1186AccountProofResponse>>,
}

pub type EVMSimulatorOnline = EVMSimulator<OnlineDB>;
pub type EVMSimulatorOffline = EVMSimulator<OfflineDB>;

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct EVMSimulatorSnapshot {
    pub provider: String,
    pub chain_id: u64,
    pub block_num: u64,
    pub block_hash: B256,
    pub state_root: B256,
    pub db: Vec<u8>,
    pub account_proofs: HashMap<Address, EIP1186AccountProofResponse>,
    pub storage_proofs: HashMap<Address, HashMap<StorageKey, EIP1186AccountProofResponse>>,
}

impl EVMSimulatorOnline {
    pub async fn new(
        rpc_url: String,
        chain_id: Option<u64>,
        block_id: Option<BlockId>,
    ) -> Result<Self> {
        let provider = RootProvider::<Ethereum>::connect(&rpc_url).await?;

        let provider_cid = provider.get_chain_id().await?;

        // If the chain ID is provided, check if it matches the provider's chain ID
        let cid = if chain_id.is_none() {
            provider_cid
        } else {
            let given_cid = chain_id.unwrap();
            if given_cid != provider_cid {
                return Err(anyhow!(
                    "Chain ID mismatch: expected {}, got {}",
                    provider_cid,
                    given_cid
                ));
            }
            given_cid
        };

        let block_id = if let Some(bid) = block_id {
            bid
        } else {
            BlockId::latest()
        };

        // Fetch the block
        let block_info = provider
            .get_block(block_id)
            .await?
            .ok_or_else(|| anyhow!("Block not found for ID: {:?}", block_id))?;

        let block_hash = block_info.header.hash;
        let block_num = block_info.header.number;
        let state_root = block_info.header.state_root;

        // Set up the DB
        let provider_arc = Arc::new(provider);
        let cache_db =
            make_fetching_db(&provider_arc, block_id).expect("Failed to create fetching DB");

        Ok(EVMSimulator {
            provider: Some(provider_arc),
            provider_url: Some(rpc_url),
            chain_id: cid,
            block_num,
            block_hash,
            state_root,
            db: cache_db,
            account_proofs: HashMap::new(),
            storage_proofs: HashMap::new(),
        })
    }

    // Convert the current state of the simulator into a serializable snapshot
    pub fn to_snapshot(&self) -> EVMSimulatorSnapshot {
        let db = serialize(&self.db.cache).expect("Failed to serialize DB cache");

        EVMSimulatorSnapshot {
            provider: self.provider_url.clone().unwrap_or(String::new()),
            chain_id: self.chain_id,
            block_num: self.block_num,
            block_hash: self.block_hash,
            state_root: self.state_root,
            db,
            account_proofs: self.account_proofs.clone(),
            storage_proofs: self.storage_proofs.clone(),
        }
    }

    pub async fn get_account_proofs(
        &mut self,
        accounts: &Vec<Address>,
    ) -> HashMap<Address, EIP1186AccountProofResponse> {
        let mut account_proofs = HashMap::new();

        for address in accounts {
            account_proofs.insert(
                *address,
                self.provider
                    .as_mut()
                    .expect("No provider set")
                    .get_proof(*address, vec![])
                    .block_id(BlockId::Hash(self.block_hash.into()))
                    .await
                    .unwrap(),
            );
        }
        account_proofs
    }

    pub async fn get_storage_proofs(
        &mut self,
        storage_accesses: &HashMap<Address, HashSet<U256>>,
    ) -> HashMap<Address, EIP1186AccountProofResponse> {
        let mut storage_proofs = HashMap::new();
        for (address, keys) in storage_accesses {
            let keys_vec: Vec<StorageKey> = keys.into_iter().map(|key| (*key).into()).collect();
            let proof = self
                .provider
                .as_mut()
                .expect("No provider set")
                .get_proof(*address, keys_vec)
                .block_id(BlockId::Hash(self.block_hash.into()))
                .await
                .unwrap();
            storage_proofs.insert(*address, proof);
        }
        storage_proofs
    }

    // Get the account and storage proofs for all touched accounts during the simulation
    pub async fn get_account_and_storage_proofs(
        &mut self,
        account_accesses: Vec<HashSet<Address>>,
        storage_accesses: Vec<HashMap<Address, HashSet<U256>>>,
    ) -> ProofData {
        let mut account_proofs = vec![];
        let mut storage_proofs = HashMap::new();

        // Combine all account accesses
        let mut all_account_accesses: HashSet<Address> = HashSet::new();
        for a in account_accesses {
            for addr in a {
                all_account_accesses.insert(addr);
            }
        }

        // Combine all storage accesses
        let mut all_storage_accesses: HashMap<Address, HashSet<U256>> = HashMap::new();
        for s in storage_accesses {
            for (addr, keys) in s {
                all_storage_accesses
                    .entry(addr)
                    .or_insert_with(HashSet::new)
                    .extend(keys);
            }
        }

        // Get account proofs
        for address in all_account_accesses {
            account_proofs.push(
                self.provider
                    .as_mut()
                    .expect("No provider set")
                    .get_proof(address, vec![])
                    .block_id(BlockId::Hash(self.block_hash.into()))
                    .await
                    .unwrap(),
            );
        }

        // Get storage proofs
        for (address, keys) in all_storage_accesses {
            let keys_vec: Vec<StorageKey> = keys.into_iter().map(|key| key.into()).collect();
            let proof = self
                .provider
                .as_mut()
                .expect("No provider set")
                .get_proof(address, keys_vec)
                .block_id(BlockId::Hash(self.block_hash.into()))
                .await
                .unwrap();
            storage_proofs.insert(address, proof);
        }

        ProofData {
            account_proofs,
            storage_proofs,
        }
    }
}

impl EVMSimulatorOffline {
    /// Restore from a snapshot without any RPC access.
    pub async fn from_snapshot(
        snapshot: EVMSimulatorSnapshot,
    ) -> Result<Self> {
        let db = crate::db::make_offline_db_from_snapshot(&snapshot)?;
        Ok(Self {
            provider: None,
            provider_url: None,
            chain_id: snapshot.chain_id,
            block_num: snapshot.block_num,
            block_hash: snapshot.block_hash,
            state_root: snapshot.state_root,
            db,
            account_proofs: snapshot.account_proofs,
            storage_proofs: snapshot.storage_proofs,
        })
    }

    pub async fn get_balance_offline(&mut self, address: Address) -> Result<U256> {
        let db = &mut self.db;

        Ok(db.basic(address).unwrap().map(|i| i.balance).unwrap_or_default())
    }
}

impl<ExtDB: DatabaseRef> EVMSimulator<ExtDB> {
    /// Only for functions that use self.db and not self.provider
    pub async fn contract_view_call(
        &mut self,
        contract_address: Address,
        call_data: Vec<u8>,
    ) -> Result<(ExecutionResult, CallTraceArena), EVMError<DBTransportError>> {
        let db = &mut self.db;

        let tracer = TracingInspector::new(tracer_config());

        let mut evm = Context::mainnet()
            .with_db(db)
            .build_mainnet_with_inspector(tracer);

        // Set up transaction for view call
        evm.ctx.tx.caller = Address::ZERO; // Use zero address as caller for view calls
        evm.ctx.tx.kind = TxKind::Call(contract_address);
        evm.ctx.tx.value = U256::ZERO;
        evm.ctx.tx.data = Bytes::from(call_data);
        evm.ctx.tx.gas_limit = 100_000; // Sufficient gas for view calls
        evm.ctx.tx.gas_price = 0; // No gas price needed for view calls
        evm.ctx.tx.nonce = 0;
        evm.ctx.tx.chain_id = Some(self.chain_id);

        // Execute the transaction with inspection
        let res = evm.inspect_tx(evm.ctx.tx.clone()).unwrap();

        let traces = evm.inspector.into_traces();

        Ok((res.result, traces))
    }

    pub async fn contract_execute(
        &mut self,
        contract_address: Address,
        call_data: Vec<u8>,
        caller: Address,
        nonce: Option<u64>,
        gas_limit: u64,
        gas_price: u128,
    ) -> Result<(ExecutionResult, CallTraceArena), EVMError<DBTransportError>> {
        self.contract_execute_optional_commit(
            contract_address,
            call_data,
            caller,
            nonce,
            gas_limit,
            gas_price,
            true,
        )
        .await
    }

    pub async fn contract_execute_optional_commit(
        &mut self,
        contract_address: Address,
        call_data: Vec<u8>,
        caller: Address,
        nonce: Option<u64>,
        gas_limit: u64,
        gas_price: u128,
        commit: bool,
    ) -> Result<(ExecutionResult, CallTraceArena), EVMError<DBTransportError>> {
        // Get caller's nonce if not provided
        let caller_nonce = if let Some(n) = nonce {
            n
        } else {
            let caller_info = self.query_rpc_or_retrieve(caller).unwrap();
            caller_info.nonce
        };

        let db = &mut self.db;
        let tracer = TracingInspector::new(tracer_config());

        let mut evm = Context::mainnet()
            .with_db(db)
            .build_mainnet_with_inspector(tracer);

        // Set up transaction to call approve
        evm.ctx.tx.caller = caller;
        evm.ctx.tx.kind = TxKind::Call(contract_address);
        evm.ctx.tx.value = U256::ZERO;
        evm.ctx.tx.data = Bytes::from(call_data);
        evm.ctx.tx.gas_limit = gas_limit;
        evm.ctx.tx.gas_price = gas_price;
        evm.ctx.tx.nonce = caller_nonce;
        evm.ctx.tx.chain_id = Some(self.chain_id);

        // Execute the transaction with inspection
        let res = evm.inspect_tx(evm.ctx.tx.clone()).unwrap();

        if commit {
            // Commit the resulting state
            evm.commit(res.state);
        }

        let traces = evm.inspector.into_traces();

        Ok((res.result, traces))
    }

    fn query_rpc_or_retrieve(&mut self, address: Address) -> Result<AccountInfo> {
        let db = &mut self.db;
        Ok(db.basic(address).unwrap().unwrap())
    }

    pub async fn get_balance(&mut self, address: Address) -> Result<U256> {
        let db = &mut self.db;

        // TODO: handle get_balance and set_balance in a neater way...
        // Fetch the balance proof
        let proof = self
            .provider
            .as_mut()
            .expect("No provider set")
            .get_proof(address, vec![])
            .block_id(BlockId::Hash(self.block_hash.into()))
            .await
            .unwrap();

        // Store the proof
        self.account_proofs.insert(address, proof);

        Ok(db.basic(address).unwrap().map(|i| i.balance).unwrap_or_default())
    }

    fn insert_account_info(&mut self, address: Address, info: AccountInfo) {
        let db = &mut self.db;
        db.cache.accounts.insert(address, info.into());
    }

    pub fn set_balance(&mut self, address: Address, balance: U256) -> Result<()> {
        let db = &mut self.db;

        match db.cache.accounts.entry(address) {
            Entry::Occupied(mut entry) => {
                // If the address is already in the DB, update the balance.
                let account = entry.get_mut();
                account.info.balance = balance;
            }
            // If the address is not in the DB, fetch it and update the balance.
            Entry::Vacant(_) => {
                // Fetch the account info from the provider
                let mut info = db.basic(address).unwrap().unwrap_or_default();
                info.balance = balance;
                db.cache.accounts.insert(address, info.into());
            }
        }

        let mut info = self.query_rpc_or_retrieve(address)?;
        info.balance = balance;

        self.insert_account_info(address, info);
        Ok(())
    }

    pub fn is_account_vacant(&mut self, address: Address) -> Result<bool> {
        let db = &mut self.db;
        let x = match db.cache.accounts.entry(address) {
            Entry::Occupied(_) => false,
            Entry::Vacant(_) => {
                // It is currently vacant in the local DB, which means that it has either not been
                // fetched, or it is actually vacant on-chain. So, we need to fetch the account
                // info and check the balance, nonce, and code hash.
                //let info = db.basic(address)?.unwrap();
                let info = match db.basic(address) {
                    Ok(Some(info)) => info,
                    Ok(None) => return Ok(true), // Account doesn't exist, so it's vacant
                    Err(_) => return Err(anyhow!("Failed to fetch account info for address: {:?}", address)),
                };

                info.code_hash == KECCAK256_EMPTY && info.nonce == 0 && info.balance == U256::ZERO
            }
        };
        Ok(x)
    }

    // TODO: implement a way to specify either gas_price or EIP1559 parameters
    // TODO: implement a way to mark the account proof as modified-in-simulation
    pub fn transfer_eth(
        &mut self,
        from: Address,
        to: Address,
        value: U256,
        gas_price: u128,
    ) -> Result<(ExecutionResult, CallTraceArena), EVMError<DBTransportError>> {
        // Get balances and nonce before transaction (will lazy load from RPC)
        let sender_info = self.query_rpc_or_retrieve(from).unwrap();
        let sender_nonce = sender_info.nonce;

        let db = &mut self.db;
        let tracer = TracingInspector::new(tracer_config());

        let mut evm = Context::mainnet()
            .with_db(db)
            .build_mainnet_with_inspector(tracer);

        // Update transaction in the same EVM instance
        evm.ctx.tx.caller = from;
        evm.ctx.tx.kind = TxKind::Call(to);
        evm.ctx.tx.value = value;
        evm.ctx.tx.gas_limit = TRANSFER_GAS_COST;
        evm.ctx.tx.gas_price = gas_price;
        evm.ctx.tx.nonce = sender_nonce;
        evm.ctx.tx.chain_id = Some(1);
        let res = evm.inspect_tx(evm.ctx.tx.clone()).unwrap();
        evm.commit(res.state);

        let traces = evm.inspector.into_traces();

        Ok((res.result, traces))
    }

    pub fn verify_account_proof(
        &self,
        account_proof: &EIP1186AccountProofResponse,
    ) -> Result<bool> {
        let account = Account {
            nonce: account_proof.nonce,
            balance: account_proof.balance,
            storage_root: account_proof.storage_hash,
            code_hash: account_proof.code_hash,
        };

        // RLP-encode the account data (aka the MPT leaf)
        let expected_account_rlp = alloy::rlp::encode(&account);

        // Verify the account proof against the state root
        let key = keccak256(account_proof.address);
        let verification_result = verify_proof(
            self.state_root.into(),
            Nibbles::unpack(&key),
            Some(expected_account_rlp),
            &account_proof.account_proof,
        );
        Ok(verification_result.is_ok())
    }

    pub fn verify_storage_proof(
        &self,
        storage_proof: &EIP1186AccountProofResponse,
    ) -> Result<bool> {
        // Verify each storage proof entry
        for storage_item in &storage_proof.storage_proof {
            // Storage trie key = keccak256(slot) where slot is the storage key
            let slot_key_b256 = storage_item.key.as_b256();
            let slot_hashed = keccak256(slot_key_b256);

            // RLP-encode the storage value if non-zero
            let expected_storage_rlp = if storage_item.value.is_zero() {
                None // Empty storage slots are not stored in the trie
            } else {
                Some(alloy::rlp::encode(&storage_item.value))
            };

            // Verify the storage proof against the storage root
            let verification_result = verify_proof(
                storage_proof.storage_hash.into(),
                Nibbles::unpack(&slot_hashed),
                expected_storage_rlp,
                &storage_item.proof,
            );

            if verification_result.is_err() {
                return Ok(false);
            }
        }

        Ok(true)
    }
}

//impl<ExtDB: DatabaseRef> EVMSimulatorOnline<ExtDB> {
//}

fn tracer_config() -> TracingInspectorConfig {
    TracingInspectorConfig {
        record_steps: true,
        record_memory_snapshots: false,
        record_stack_snapshots: StackSnapshotType::All,
        record_state_diff: false,
        record_returndata_snapshots: false,
        record_opcodes_filter: None,
        exclude_precompile_calls: false,
        record_logs: false,
        record_immediate_bytes: true,
    }
}

pub fn extract_accesses_from_traces(
    traces: &CallTraceArena,
) -> (HashSet<Address>, HashSet<Address>, HashMap<Address, HashSet<U256>>) {
    let nodes = traces.nodes();
    let mut accounts = HashSet::<Address>::new();
    let mut balance_accesses = HashSet::<Address>::new();
    let mut storage_accesses = HashMap::<Address, HashSet<U256>>::new();

    for node in nodes {
        for step in &node.trace.steps {
            let addr = step.contract;
            match step.op.get() {
                0x31 => {
                    // BALANCE
                    balance_accesses.insert(addr);
                    accounts.insert(addr);
                }
                0x47 => {
                    // SELFBALANCE
                    balance_accesses.insert(addr);
                    accounts.insert(addr);
                }
                0x54 => {
                    // SLOAD
                    if step.depth == 1 {
                        let key = step.push_stack.clone().unwrap()[0];
                        storage_accesses
                            .entry(addr)
                            .or_insert_with(HashSet::new)
                            .insert(key);
                    }
                    accounts.insert(addr);
                }
                _ => {}
            };
        }
    }

    (accounts, balance_accesses, storage_accesses)
}
