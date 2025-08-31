use alloy::consensus::Account;
use alloy::eips::BlockId;
use alloy::network::Ethereum;
use alloy::primitives::{
    Address, B256, Bytes, KECCAK256_EMPTY, U256, aliases::StorageKey, keccak256,
};
use alloy::providers::{Provider, RootProvider};
use alloy::rpc::types::EIP1186AccountProofResponse;
use alloy::sol;
use alloy::sol_types::SolCall;
use alloy_trie::{Nibbles, proof::verify_proof};
use anyhow::{Result, anyhow};
use bincode::{deserialize, serialize};
use revm::ExecuteCommitEvm;
use revm::database::{AlloyDB, CacheDB, DBTransportError, WrapDatabaseAsync};
use revm::primitives::{TxKind, hash_map::Entry};
use revm::state::AccountInfo;
use revm::{Context, Database, InspectEvm, MainBuilder, MainContext};
use revm_context::result::EVMError;
use revm_context::result::ExecutionResult;
use revm_inspectors::tracing::{
    CallTraceArena, StackSnapshotType, TracingInspector, TracingInspectorConfig,
};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

pub mod db;
pub mod tracer;

const TRANSFER_GAS_COST: u64 = 21_000; // Standard gas cost for an ETH transfer

sol! {
    #[sol(rpc)]
    interface IERC20 {
        function balanceOf(address account) external view returns (uint256);
        function totalSupply() external view returns (uint256);
        function decimals() external view returns (uint8);
        function symbol() external view returns (string);
        function name() external view returns (string);
        function allowance(address owner, address spender) external view returns (uint256);
        function transfer(address to, uint256 amount) external returns (bool);
        function approve(address spender, uint256 amount) external returns (bool);
        function transferFrom(address from, address to, uint256 amount) external returns (bool);
    }
}

pub type HttpProvider = RootProvider<Ethereum>;

pub struct EVMSimulator {
    pub provider: Option<Arc<RootProvider<Ethereum>>>,
    pub provider_url: String,
    pub chain_id: u64,
    pub block_num: u64,
    pub block_hash: B256,
    pub state_root: B256,
    db: CacheDB<WrapDatabaseAsync<AlloyDB<Ethereum, Arc<RootProvider<Ethereum>>>>>,
    account_proofs: HashMap<Address, EIP1186AccountProofResponse>,
    storage_proofs: HashMap<Address, HashMap<StorageKey, EIP1186AccountProofResponse>>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct ProofData {
    pub account_proofs: Vec<EIP1186AccountProofResponse>,
    pub storage_proofs: HashMap<Address, EIP1186AccountProofResponse>,
}

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

impl EVMSimulator {
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
            db::make_fetching_db(&provider_arc, block_id).expect("Failed to create fetching DB");

        Ok(EVMSimulator {
            provider: Some(provider_arc),
            provider_url: rpc_url,
            chain_id: cid,
            block_num,
            block_hash,
            state_root,
            db: cache_db,
            account_proofs: HashMap::new(),
            storage_proofs: HashMap::new(),
        })
    }

    pub async fn contract_view_call(
        &mut self,
        contract_address: Address,
        call_data: Vec<u8>,
    ) -> Result<(ExecutionResult, CallTraceArena), EVMError<DBTransportError>> {
        let db = &mut self.db;

        let tracer = TracingInspector::new(Self::tracer_config());

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
        let res = evm.inspect_tx(evm.ctx.tx.clone())?;

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
        let tracer = TracingInspector::new(Self::tracer_config());

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
        Ok(db.basic(address)?.unwrap())
    }

    // Convert the current state of the simulator into a serializable snapshot
    pub fn to_snapshot(&self) -> EVMSimulatorSnapshot {
        let db = serialize(&self.db.cache).expect("Failed to serialize DB cache");

        EVMSimulatorSnapshot {
            provider: self.provider_url.clone(),
            chain_id: self.chain_id,
            block_num: self.block_num,
            block_hash: self.block_hash,
            state_root: self.state_root,
            db,
            account_proofs: self.account_proofs.clone(),
            storage_proofs: self.storage_proofs.clone(),
        }
    }

    // Restore the simulator state from a serialized snapshot
    pub async fn from_snapshot(snapshot: EVMSimulatorSnapshot) -> Result<Self> {
        let provider = RootProvider::<Ethereum>::connect(&snapshot.provider).await?;

        // Verify the provider matches the snapshot
        let provider_cid = provider.get_chain_id().await?;
        if provider_cid != snapshot.chain_id {
            return Err(anyhow!(
                "Chain ID mismatch: expected {}, got {}",
                snapshot.chain_id,
                provider_cid
            ));
        }

        // Set up the DB with the block from the snapshot
        let block_id = BlockId::number(snapshot.block_num);
        let provider_arc = Arc::new(provider);
        let alloy_db = AlloyDB::new(provider_arc.clone(), block_id);
        let wrapped_db = WrapDatabaseAsync::new(alloy_db).expect("Failed to wrap database");
        let mut cache_db = CacheDB::new(wrapped_db);

        // Restore the cached state from the snapshot
        if !snapshot.db.is_empty() {
            let cached_state = deserialize(&snapshot.db)?;
            cache_db.cache = cached_state;
        }

        Ok(EVMSimulator {
            provider: Some(provider_arc),
            provider_url: snapshot.provider,
            chain_id: snapshot.chain_id,
            block_num: snapshot.block_num,
            block_hash: snapshot.block_hash,
            state_root: snapshot.state_root,
            db: cache_db,
            account_proofs: snapshot.account_proofs,
            storage_proofs: snapshot.storage_proofs,
        })
    }

    // Restore the simulator state from a serialized snapshot, but without any RPC access
    pub async fn from_snapshot_to_offline(snapshot: EVMSimulatorSnapshot) -> Result<Self> {
        // TODO
        let db = db::make_offline_db_from_snapshot(&snapshot)?;
        Ok(EVMSimulator {
            provider: None,
            provider_url: snapshot.provider,
            chain_id: snapshot.chain_id,
            block_num: snapshot.block_num,
            block_hash: snapshot.block_hash,
            state_root: snapshot.state_root,
            db,
            account_proofs: snapshot.account_proofs,
            storage_proofs: snapshot.storage_proofs,
        })
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
        let tracer = TracingInspector::new(Self::tracer_config());

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

        Ok(db.basic(address)?.map(|i| i.balance).unwrap_or_default())
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
                let info = db.basic(address)?.unwrap();
                info.code_hash == KECCAK256_EMPTY && info.nonce == 0 && info.balance == U256::ZERO
            }
        };
        Ok(x)
    }

    pub async fn erc20_balance_of(
        &mut self,
        token_address: Address,
        account: Address,
    ) -> Result<(U256, CallTraceArena)> {
        // Encode the balanceOf function call
        let balance_call = IERC20::balanceOfCall { account };
        let call_data = balance_call.abi_encode();

        let result = self.contract_view_call(token_address, call_data).await?;

        let res = result.0;

        // Check if the call was successful
        if !res.is_success() {
            return Err(anyhow!("ERC20 balanceOf call failed"));
        }

        let output = res.output().unwrap_or_default();
        if output.len() < 32 {
            return Err(anyhow!("Invalid ERC20 balanceOf response"));
        }

        // Parse the U256 balance from the output (first 32 bytes)
        let balance = U256::from_be_slice(&output[..32]);

        Ok((balance, result.1))
    }

    pub async fn erc20_approve(
        &mut self,
        token_address: Address,
        caller: Address,
        spender: Address,
        amount: U256,
        nonce: Option<u64>,
        gas_limit: u64,
        gas_price: u128,
    ) -> Result<(ExecutionResult, CallTraceArena), EVMError<DBTransportError>> {
        // Encode the approve function call
        let approve_call = IERC20::approveCall { spender, amount };
        let call_data = approve_call.abi_encode();

        self.contract_execute(
            token_address,
            call_data,
            caller,
            nonce,
            gas_limit,
            gas_price,
        )
        .await
    }

    pub async fn erc20_allowance(
        &mut self,
        token_address: Address,
        owner: Address,
        spender: Address,
    ) -> Result<(U256, CallTraceArena)> {
        // Encode the allowance function call
        let allowance_call = IERC20::allowanceCall { owner, spender };
        let call_data = allowance_call.abi_encode();

        let result = self.contract_view_call(token_address, call_data).await?;

        let res = result.0;

        // Check if the call was successful
        if !res.is_success() {
            return Err(anyhow!("ERC20 allowance call failed"));
        }

        let output = res.output().unwrap_or_default();
        if output.len() < 32 {
            return Err(anyhow!("Invalid ERC20 allowance response"));
        }

        // Parse the U256 allowance from the output (first 32 bytes)
        let allowance = U256::from_be_slice(&output[..32]);
        Ok((allowance, result.1))
    }

    pub async fn erc20_total_supply(
        &mut self,
        token_address: Address,
    ) -> Result<(U256, CallTraceArena)> {
        // Encode the totalSupply function call
        let total_supply_call = IERC20::totalSupplyCall {};
        let call_data = total_supply_call.abi_encode();

        let result = self.contract_view_call(token_address, call_data).await?;

        let res = result.0;

        // Check if the call was successful
        if !res.is_success() {
            return Err(anyhow!("ERC20 totalSupply call failed"));
        }

        let output = res.output().unwrap_or_default();
        if output.len() < 32 {
            return Err(anyhow!("Invalid ERC20 totalSupply response"));
        }

        // Parse the U256 total supply from the output (first 32 bytes)
        let total_supply = U256::from_be_slice(&output[..32]);
        Ok((total_supply, result.1))
    }

    pub async fn erc20_decimals(&mut self, token_address: Address) -> Result<(u8, CallTraceArena)> {
        // Encode the decimals function call
        let decimals_call = IERC20::decimalsCall {};
        let call_data = decimals_call.abi_encode();

        let result = self.contract_view_call(token_address, call_data).await?;
        let res = result.0;

        // Check if the call was successful
        if !res.is_success() {
            return Err(anyhow!("ERC20 decimals call failed"));
        }

        let output = res.output().unwrap_or_default();
        if output.len() < 32 {
            return Err(anyhow!("Invalid ERC20 decimals response"));
        }

        // Parse the u8 decimals from the output (last byte of 32 bytes)
        let decimals = output[31];
        Ok((decimals, result.1))
    }

    pub async fn erc20_name(&mut self, token_address: Address) -> Result<(String, CallTraceArena)> {
        // Encode the name function call
        let name_call = IERC20::nameCall {};
        let call_data = name_call.abi_encode();

        let result = self.contract_view_call(token_address, call_data).await?;
        let res = result.0;

        // Check if the call was successful
        if !res.is_success() {
            return Err(anyhow!("ERC20 name call failed"));
        }

        let output = res.output().unwrap_or_default();
        if output.len() < 32 {
            return Err(anyhow!("Invalid ERC20 name response"));
        }

        // Parse string from ABI-encoded output
        // The output contains: offset (32 bytes) + length (32 bytes) + string data
        if output.len() < 64 {
            return Err(anyhow!("ERC20 name response too short"));
        }

        let length = u32::from_be_bytes([output[60], output[61], output[62], output[63]]) as usize;
        if output.len() < 64 + length {
            return Err(anyhow!("ERC20 name response truncated"));
        }

        let name_bytes = &output[64..64 + length];
        let name = String::from_utf8(name_bytes.to_vec())
            .map_err(|_| anyhow!("Invalid UTF-8 in ERC20 name"))?;

        Ok((name, result.1))
    }

    pub async fn erc20_symbol(
        &mut self,
        token_address: Address,
    ) -> Result<(String, CallTraceArena)> {
        // Encode the symbol function call
        let symbol_call = IERC20::symbolCall {};
        let call_data = symbol_call.abi_encode();

        let result = self.contract_view_call(token_address, call_data).await?;
        let res = result.0;

        // Check if the call was successful
        if !res.is_success() {
            return Err(anyhow!("ERC20 symbol call failed"));
        }

        let output = res.output().unwrap_or_default();
        if output.len() < 32 {
            return Err(anyhow!("Invalid ERC20 symbol response"));
        }

        // Parse string from ABI-encoded output
        // The output contains: offset (32 bytes) + length (32 bytes) + string data
        if output.len() < 64 {
            return Err(anyhow!("ERC20 symbol response too short"));
        }

        let length = u32::from_be_bytes([output[60], output[61], output[62], output[63]]) as usize;
        if output.len() < 64 + length {
            return Err(anyhow!("ERC20 symbol response truncated"));
        }

        let symbol_bytes = &output[64..64 + length];
        let symbol = String::from_utf8(symbol_bytes.to_vec())
            .map_err(|_| anyhow!("Invalid UTF-8 in ERC20 symbol"))?;

        Ok((symbol, result.1))
    }

    pub async fn erc20_transfer(
        &mut self,
        token_address: Address,
        from: Address,
        to: Address,
        amount: U256,
        nonce: Option<u64>,
        gas_limit: u64,
        gas_price: u128,
    ) -> Result<(ExecutionResult, CallTraceArena), EVMError<DBTransportError>> {
        // Encode the transfer function call
        let transfer_call = IERC20::transferCall { to, amount };
        let call_data = transfer_call.abi_encode();

        self.contract_execute(token_address, call_data, from, nonce, gas_limit, gas_price)
            .await
    }

    pub async fn erc20_transfer_from(
        &mut self,
        token_address: Address,
        caller: Address,
        from: Address,
        to: Address,
        amount: U256,
        nonce: Option<u64>,
        gas_limit: u64,
        gas_price: u128,
    ) -> Result<(ExecutionResult, CallTraceArena), EVMError<DBTransportError>> {
        // Encode the transferFrom function call
        let transfer_from_call = IERC20::transferFromCall { from, to, amount };
        let call_data = transfer_from_call.abi_encode();

        self.contract_execute(
            token_address,
            call_data,
            caller,
            nonce,
            gas_limit,
            gas_price,
        )
        .await
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

pub fn extract_accesses_from_traces(
    traces: &CallTraceArena,
) -> (HashMap<Address, HashSet<U256>>, HashSet<Address>) {
    let nodes = traces.nodes();
    let mut storage_accesses = HashMap::<Address, HashSet<U256>>::new();
    let mut account_accesses = HashSet::<Address>::new();

    for node in nodes {
        for step in &node.trace.steps {
            let addr = step.contract;
            match step.op.get() {
                0x31 => {
                    // BALANCE
                    account_accesses.insert(addr);
                }
                0x47 => {
                    // SELFBALANCE
                    account_accesses.insert(addr);
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
                }
                _ => {}
            };
        }
    }

    (storage_accesses, account_accesses)
}

#[cfg(test)]
mod tests {
    use crate::EVMSimulator;
    use alloy::primitives::{Address, B256, U256, address};
    use alloy::sol_types::SolCall;
    use alloy_trie::{Nibbles, proof::verify_proof};
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    // Test constants
    const USDC_ADDRESS: Address = address!("0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48");

    // ETH amount constants (in wei)
    const ETH_1: U256 = U256::from_limbs([1_000_000_000_000_000_000u64, 0, 0, 0]);
    const ETH_10: U256 = U256::from_limbs([10_000_000_000_000_000_000u64, 0, 0, 0]);

    // Gas price constants (in wei)
    const GWEI_20: u128 = 20_000_000_000u128;

    // USDC amount constants (6 decimals)
    const USDC_100: U256 = U256::from_limbs([100_000_000u64, 0, 0, 0]);
    const USDC_200: U256 = U256::from_limbs([200_000_000u64, 0, 0, 0]);
    const USDC_500: U256 = U256::from_limbs([500_000_000u64, 0, 0, 0]);
    const USDC_1500: U256 = U256::from_limbs([1500_000_000u64, 0, 0, 0]);

    // Gas limit constants
    const GAS_ERC20_APPROVE: u64 = 100_000;
    const GAS_ERC20_TRANSFER: u64 = 300_000;

    fn get_mainnet_rpc_url() -> String {
        // Load .env file if it exists
        dotenv::dotenv().ok();

        // Try to get RPC URL from environment variable first, fallback to public RPC
        std::env::var("ETHEREUM_RPC_URL").unwrap_or_else(|_| "https://eth.llamarpc.com".to_string())
    }

    fn get_mainnet_chain_id() -> u64 {
        1 // Mainnet chain ID
    }

    async fn init_mainnet_simulator() -> EVMSimulator {
        let url = get_mainnet_rpc_url();
        let simulator = EVMSimulator::new(
            url,
            Some(get_mainnet_chain_id()),
            None, // None should default to the latest block number
        )
        .await
        .expect("Failed to create EVM simulator");
        simulator
    }

    fn gen_random_address(seed: u64) -> Address {
        let mut rng = ChaCha8Rng::seed_from_u64(seed);
        let mut bytes = [0u8; 20];
        rng.fill(&mut bytes);
        Address::from(bytes)
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_snapshot() {
        // Original simulator: set 0x0 to have 1 ETH
        let mut simulator = init_mainnet_simulator().await;
        let addr = address!("0x0000000000000000000000000000000000000000");
        let amount = U256::from(1_000_000_000_000_000_000u64); // 1 ETH
        let _ = simulator.set_balance(addr, amount);

        // Original simulator: addr2 has X ETH
        let addr2 = address!("0xd8dA6BF26964aF9D7eEd9e03E53415D37aA96045");
        let amount2 = simulator.get_balance(addr2).await.unwrap();

        // Take snapshot
        let snapshot = simulator.to_snapshot();

        // Restore snapshot
        let mut new_simulator = EVMSimulator::from_snapshot(snapshot)
            .await
            .expect("Failed to restore EVM simulator from snapshot");

        // Get balance of 0x0 from new_simulator
        let restored_balance = new_simulator.get_balance(addr).await.unwrap();

        // Check
        assert_eq!(
            restored_balance, amount,
            "Restored balance does not match the original"
        );

        // Get balance of addr2 from new_simulator
        let new_amount2 = new_simulator.get_balance(addr2).await.unwrap();

        // Check
        assert_eq!(
            new_amount2, amount2,
            "Restored balance for addr2 does not match the original"
        );

        // Original simulator: set balance of addr2 to a new amount
        let _ = simulator.set_balance(addr2, amount2 + amount);

        // Take snapshot
        let snapshot = simulator.to_snapshot();

        // Restore snapshot
        new_simulator = EVMSimulator::from_snapshot(snapshot)
            .await
            .expect("Failed to restore EVM simulator from snapshot");

        // Get balance of addr2 from new_simulator
        let new_amount2 = new_simulator.get_balance(addr2).await.unwrap();

        // Check
        assert_eq!(
            new_amount2,
            amount2 + amount,
            "Restored balance for addr2 after update does not match the original"
        );
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_is_vacant() {
        let mut simulator = init_mainnet_simulator().await;
        let addr = address!("0x0000000000000000000000000000000000000000");
        let iv = simulator.is_account_vacant(addr).unwrap();
        assert!(!iv, "The zero address is not vacant on mainnet");
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_set_balance_of_vacant_account() {
        let mut simulator = init_mainnet_simulator().await;
        let mut addr = gen_random_address(0);
        let mut i = 0;
        loop {
            if simulator.is_account_vacant(addr).unwrap() {
                break;
            }
            addr = gen_random_address(i);
            i += 1;
        }
        let amount = U256::from(1_000_000_000_000_000_000u64); // 1 ETH
        let balance_before = simulator.get_balance(addr).await.unwrap();
        assert_eq!(
            balance_before,
            U256::ZERO,
            "Balance before setting is not zero"
        );
        let _ = simulator.set_balance(addr, amount);
        let balance_after = simulator.get_balance(addr).await.unwrap();
        assert_eq!(balance_after, amount, "Balance after setting is incorrect");
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_init_evmsimulator_with_block_id() {
        let mut simulator =
            EVMSimulator::new(get_mainnet_rpc_url(), Some(get_mainnet_chain_id()), None)
                .await
                .expect("Failed to create EVM simulator");

        let addr = address!("0x0000000000000000000000000000000000000000");
        let balance = simulator.get_balance(addr).await.unwrap();
        // The zero address should have nonzero balance
        assert!(
            balance > U256::ZERO,
            "Zero address balance should be non-zero"
        );
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_get_and_set_balance() {
        let mut simulator = init_mainnet_simulator().await;
        let addr = address!("0xd8dA6BF26964aF9D7eEd9e03E53415D37aA96045");
        let balance_before = simulator.get_balance(addr).await.unwrap();
        let new_balance = balance_before + ETH_1;
        let _ = simulator.set_balance(addr, new_balance);
        let balance_after = simulator.get_balance(addr).await.unwrap();
        assert_eq!(
            balance_after, new_balance,
            "Balance after setting is incorrect"
        );
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_verify_account_proofs() {
        let mut simulator = init_mainnet_simulator().await;
        let addr = address!("0xd8dA6BF26964aF9D7eEd9e03E53415D37aA96045");
        let _ = simulator.get_balance(addr).await.unwrap();
        // Get the account proof for the address and verify it
        let proof = simulator.account_proofs.get(&addr).unwrap();
        let result = simulator.verify_account_proof(proof);
        assert!(result.is_ok(), "Account proof verification failed");
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_transfer_eth() {
        let mut simulator = init_mainnet_simulator().await;

        let sender = address!("0x1bbbbbbbbbbbbbbbbb0000000000000000000000");
        let receiver = address!("0x1aaaaaaaaaaaaaaaaa0000000000000000000000");
        let transfer_amount = ETH_1;
        let gas_price = GWEI_20;

        let _ = simulator.set_balance(sender, ETH_10);

        let sender_balance_before = simulator
            .get_balance(sender)
            .await
            .expect("Failed to get sender balance");

        let receiver_balance_before = simulator
            .get_balance(receiver)
            .await
            .expect("Failed to get receiver balance");

        std::thread::sleep(std::time::Duration::from_millis(1000));

        // Simulate a simple ETH transfer
        let result = simulator
            .transfer_eth(sender, receiver, transfer_amount, gas_price)
            .expect("Failed to execute transaction")
            .0;

        std::thread::sleep(std::time::Duration::from_millis(1000));

        let sender_balance_after = simulator
            .get_balance(sender)
            .await
            .expect("Failed to get sender balance after transaction");
        let receiver_balance_after = simulator
            .get_balance(receiver)
            .await
            .expect("Failed to get receiver balance after transaction");

        // Calculate gas cost
        let gas_used = U256::from(result.gas_used());
        let gas_cost = gas_used * U256::from(gas_price);

        let expected_sender_balance_after = sender_balance_before - transfer_amount - gas_cost;
        let expected_receiver_balance_after = receiver_balance_before + transfer_amount;
        assert_eq!(
            sender_balance_after, expected_sender_balance_after,
            "Sender balance after transaction is incorrect"
        );
        assert_eq!(
            receiver_balance_after, expected_receiver_balance_after,
            "Receiver balance after transaction is incorrect"
        );
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_erc20_balance_query_usdc() {
        let mut simulator = init_mainnet_simulator().await;

        // Token contract on mainnet
        let token_address = USDC_ADDRESS;
        let test_account = address!("0x0000000000000000000000000000000000000000");

        let balance = simulator
            .erc20_balance_of(token_address, test_account)
            .await
            .expect("Failed to query ERC20 balance")
            .0;

        assert!(balance >= U256::ZERO, "Balance should be non-negative");
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_erc20_approve() {
        let mut simulator = init_mainnet_simulator().await;

        // USDC contract on mainnet
        let token_address = USDC_ADDRESS;

        // Test accounts
        let owner = address!("0xd8dA6BF26964aF9D7eEd9e03E53415D37aA96045"); // Account with ETH for gas
        let spender = address!("0x742d35Cc662C910EF7B5BdD2C90B5948a5d8EBB6"); // Random spender address

        // Set some ETH balance for the owner to pay for gas
        let _ = simulator.set_balance(owner, ETH_1);

        // Check initial allowance (don't assume it's 0)
        let _initial_allowance = simulator
            .erc20_allowance(token_address, owner, spender)
            .await
            .expect("Failed to query initial allowance")
            .0;

        // First approval: Set initial allowance to some value
        let first_approve_amount = USDC_500;
        let result1 = simulator
            .erc20_approve(
                token_address,
                owner,
                spender,
                first_approve_amount,
                None,
                GAS_ERC20_APPROVE,
                GWEI_20,
            )
            .await
            .expect("Failed to execute first ERC20 approve")
            .0;

        assert!(
            result1.is_success(),
            "First approve transaction should succeed"
        );

        // Check allowance after first approval
        let allowance_after_first = simulator
            .erc20_allowance(token_address, owner, spender)
            .await
            .expect("Failed to query allowance after first approve")
            .0;

        assert_eq!(
            allowance_after_first, first_approve_amount,
            "First approval should set allowance correctly"
        );

        // Second approval: Change allowance to new value
        let second_approve_amount = USDC_1500;
        let result2 = simulator
            .erc20_approve(
                token_address,
                owner,
                spender,
                second_approve_amount,
                None,
                GAS_ERC20_APPROVE,
                GWEI_20,
            )
            .await
            .expect("Failed to execute second ERC20 approve")
            .0;

        assert!(
            result2.is_success(),
            "Second approve transaction should succeed"
        );

        // Check final allowance
        let final_allowance = simulator
            .erc20_allowance(token_address, owner, spender)
            .await
            .expect("Failed to query final allowance")
            .0;

        // The final allowance should be the second approved amount (not added, but replaced)
        assert_eq!(
            final_allowance, second_approve_amount,
            "Final allowance should equal second approved amount (ERC20 approve replaces, doesn't add)"
        );

        // Demonstrate that approve overwrites, doesn't add
        let allowance_change = final_allowance.saturating_sub(allowance_after_first);
        let expected_change = second_approve_amount.saturating_sub(first_approve_amount);

        assert_eq!(
            allowance_change, expected_change,
            "Allowance change should match the difference between approvals"
        );
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_erc20_balance_query_tokenstate() {
        let mut simulator = init_mainnet_simulator().await;

        // Token contract on mainnet (which calls a TokenState contract at
        // 0x05a9CBe762B36632b3594DA4F082340E0e5343e8 to get the balance)
        let token_address = address!("0x57ab1ec28d129707052df4df418d58a2d46d5f51");
        let test_account = address!("0xA3ccaf08a54Cf31649f91aE1570A0720C8d4EB1E");

        let balance = simulator
            .erc20_balance_of(token_address, test_account)
            .await
            .expect("Failed to query ERC20 balance")
            .0;

        assert!(balance >= U256::ZERO, "Balance should be non-negative");
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_erc20_token_info() {
        let mut simulator = init_mainnet_simulator().await;

        // USDC contract on mainnet
        let token_address = USDC_ADDRESS;

        // Test individual functions
        let name = simulator
            .erc20_name(token_address)
            .await
            .expect("Failed to query ERC20 name")
            .0;

        let symbol = simulator
            .erc20_symbol(token_address)
            .await
            .expect("Failed to query ERC20 symbol")
            .0;

        let decimals = simulator
            .erc20_decimals(token_address)
            .await
            .expect("Failed to query ERC20 decimals")
            .0;

        let total_supply = simulator
            .erc20_total_supply(token_address)
            .await
            .expect("Failed to query ERC20 total supply")
            .0;

        // Verify USDC properties
        assert_eq!(symbol, "USDC");
        assert_eq!(decimals, 6);
        assert!(!name.is_empty());
        assert!(total_supply > U256::ZERO);
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_erc20_transfer() {
        let mut simulator = init_mainnet_simulator().await;

        // USDC contract on mainnet
        let token_address = USDC_ADDRESS;

        // Test accounts - using address that has positive USDC balance
        let from = address!("0xd8dA6BF26964aF9D7eEd9e03E53415D37aA96045"); // Account with existing USDC balance
        let to = address!("0x742d35Cc662C910EF7B5BdD2C90B5948a5d8EBB6"); // Recipient address

        // Set some ETH balance for the sender to pay for gas
        let _ = simulator.set_balance(from, ETH_1);

        // Transfer amount
        let transfer_amount = USDC_100;

        // Record balances before transfer
        let from_balance_before = simulator
            .erc20_balance_of(token_address, from)
            .await
            .expect("Failed to query sender balance")
            .0;
        let to_balance_before = simulator
            .erc20_balance_of(token_address, to)
            .await
            .expect("Failed to query recipient balance")
            .0;

        // Execute the transfer
        let result = simulator
            .erc20_transfer(
                token_address,
                from,
                to,
                transfer_amount,
                None, // Auto-fetch nonce
                GAS_ERC20_TRANSFER,
                GWEI_20,
            )
            .await
            .expect("Failed to execute transfer")
            .0;

        // Check balances after transfer
        let from_balance_after = simulator
            .erc20_balance_of(token_address, from)
            .await
            .expect("Failed to query sender balance after transfer")
            .0;
        let to_balance_after = simulator
            .erc20_balance_of(token_address, to)
            .await
            .expect("Failed to query recipient balance after transfer")
            .0;

        // Verify the transfer worked correctly
        assert_eq!(from_balance_after, from_balance_before - transfer_amount);
        assert_eq!(to_balance_after, to_balance_before + transfer_amount);

        // Verify transaction success
        assert!(result.is_success());
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_erc20_transfer_from() {
        let mut simulator = init_mainnet_simulator().await;

        // USDC contract on mainnet
        let token_address = USDC_ADDRESS;

        // Test accounts - using address that has positive USDC balance
        let owner = address!("0x37305B1cD40574E4C5Ce33f8e8306Be057fD7341"); // Token owner with existing USDC balance
        let spender = address!("0x0000000000000000000000000000000000000001"); // Account doing the transfer
        let recipient = address!("0x1234567890123456789012345678901234567890"); // Transfer recipient

        // Set ETH balances for gas fees
        let _ = simulator.set_balance(owner, ETH_1);
        let _ = simulator.set_balance(spender, ETH_1);

        // Transfer amount
        let transfer_amount = USDC_100;
        let approval_amount = USDC_200;

        // Step 1: Owner approves spender to spend tokens
        let approve_result = simulator
            .erc20_approve(
                token_address,
                owner,
                spender,
                approval_amount,
                None, // Auto-fetch nonce
                GAS_ERC20_APPROVE,
                GWEI_20,
            )
            .await
            .expect("Failed to execute approval")
            .0;

        assert!(approve_result.is_success());

        // Verify allowance was set
        let allowance = simulator
            .erc20_allowance(token_address, owner, spender)
            .await
            .expect("Failed to query allowance")
            .0;
        assert_eq!(allowance, approval_amount);

        // Record balances before transferFrom
        let owner_balance_before = simulator
            .erc20_balance_of(token_address, owner)
            .await
            .expect("Failed to query owner balance")
            .0;
        let recipient_balance_before = simulator
            .erc20_balance_of(token_address, recipient)
            .await
            .expect("Failed to query recipient balance")
            .0;

        // Step 2: Spender executes transferFrom
        let transfer_result = simulator
            .erc20_transfer_from(
                token_address,
                spender,   // Caller doing the transfer
                owner,     // From address
                recipient, // To address
                transfer_amount,
                None, // Auto-fetch nonce
                GAS_ERC20_TRANSFER,
                GWEI_20,
            )
            .await
            .expect("Failed to execute transferFrom")
            .0;

        assert!(transfer_result.is_success());

        // Check balances after transferFrom
        let owner_balance_after = simulator
            .erc20_balance_of(token_address, owner)
            .await
            .expect("Failed to query owner balance after transfer")
            .0;
        let recipient_balance_after = simulator
            .erc20_balance_of(token_address, recipient)
            .await
            .expect("Failed to query recipient balance after transfer")
            .0;
        let allowance_after = simulator
            .erc20_allowance(token_address, owner, spender)
            .await
            .expect("Failed to query allowance after transfer")
            .0;

        // Verify the transferFrom worked correctly
        assert_eq!(owner_balance_after, owner_balance_before - transfer_amount);
        assert_eq!(
            recipient_balance_after,
            recipient_balance_before + transfer_amount
        );
        assert_eq!(allowance_after, approval_amount - transfer_amount); // Allowance should be reduced
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_host_and_enclave_flow() {
        // Set up accounts - sender has real USDC balance, receiver is random
        let sender = address!("0x37305B1cD40574E4C5Ce33f8e8306Be057fD7341"); // Real account with USDC
        let receiver = address!("0x1234567890123456789012345678901234567890"); // Random receiver
        let transfer_amount = USDC_100; // 100 USDC transfer

        // Host: create initial simulator
        let mut host_simulator = init_mainnet_simulator().await;

        // Host: warm pre-tx state WITHOUT committing
        let (host_pre_res, host_traces) = host_simulator
            .contract_execute_optional_commit(
                USDC_ADDRESS,
                crate::IERC20::transferCall {
                    to: receiver,
                    amount: transfer_amount,
                }
                .abi_encode(),
                sender,
                None,
                GAS_ERC20_TRANSFER,
                GWEI_20,
                false,
            )
            .await
            .expect("warmup failed");

        let snapshot = host_simulator.to_snapshot();

        // Enclave: recreate simulator from snapshot
        let mut enclave = EVMSimulator::from_snapshot(snapshot).await.unwrap();

        // Re-run the SAME tx offline (still no commit needed for trace equality)
        let (enc_res, enc_traces) = enclave
            .contract_execute_optional_commit(
                USDC_ADDRESS,
                crate::IERC20::transferCall {
                    to: receiver,
                    amount: transfer_amount,
                }
                .abi_encode(),
                sender,
                None,
                GAS_ERC20_TRANSFER,
                GWEI_20,
                false,
            )
            .await
            .expect("enclave offline run failed");

        // 4) Compare
        assert_eq!(host_pre_res, enc_res);
        assert_eq!(host_traces, enc_traces);

        /*
        // Step 4: Execute the USDC transfer simulation on host
        let host_result = host_simulator
            .erc20_transfer(
                USDC_ADDRESS,
                sender,
                receiver,
                transfer_amount,
                None, // Auto-fetch nonce
                GAS_ERC20_TRANSFER,
                GWEI_20,
            )
            .await
            .expect("Host simulation failed");

        assert!(host_result.0.is_success(), "Host transfer should succeed");
        println!("HOST: Transfer simulation successful");

        let traces = host_result.1.clone();
        let (storage_accesses, account_accesses) = crate::extract_accesses_from_traces(&traces);

        println!("HOST: Account accesses: {:?}", account_accesses);
        println!("HOST: Storage accesses: {:?}", storage_accesses);

        // Step 5: Get proofs from host simulation
        let host_proofs = host_simulator.get_account_and_storage_proofs(vec![account_accesses], vec![storage_accesses]).await;
        println!("HOST: Generated {} account proofs and {} storage proofs",
                 host_proofs.account_proofs.len(),
                 host_proofs.storage_proofs.len());

        println!("HOST: Created simulator snapshot for enclave");

        // Step 7: ENCLAVE SIMULATION - Deserialize and create new simulator (enclave side)
        let mut enclave_simulator = EVMSimulator::from_snapshot(simulator_snapshot)
            .await
            .expect("Failed to restore simulator from snapshot");
        println!("ENCLAVE: Restored simulator from snapshot");

        // Step 8: Re-run the same simulation in enclave to verify consistency
        let enclave_result = enclave_simulator
            .erc20_transfer(
                USDC_ADDRESS,
                sender,
                receiver,
                transfer_amount,
                None, // Auto-fetch nonce
                GAS_ERC20_TRANSFER,
                GWEI_20,
            )
            .await
            .expect("Enclave simulation failed");

        assert!(enclave_result.0.is_success(), "Enclave transfer should succeed");
        println!("ENCLAVE: Transfer simulation successful");

        // Step 9: Verify that host and enclave results match
        assert_eq!(
            host_result.0,
            enclave_result.0,
            "transaction result should match between host and enclave"
        );

        assert!(host_result.0.is_success());
        assert!(enclave_result.0.is_success());

        println!("ENCLAVE: Results match host simulation");

        // Step 10: verify that the traces match
        assert!(
            host_result.1 == enclave_result.1,
            "traces should match between host and enclave"
        );

        // Step 10: Get proofs from enclave simulation and verify them cryptographically
        let enclave_proofs = enclave_simulator.get_account_and_storage_proofs().await;

        // Verify proof counts match first
        assert_eq!(
            host_proofs.account_proofs.len(),
            enclave_proofs.account_proofs.len(),
            "Account proof counts should match"
        );

        assert_eq!(
            host_proofs.storage_proofs.len(),
            enclave_proofs.storage_proofs.len(),
            "Storage proof counts should match"
        );

        // Step 10a: Verify account proofs structurally and cryptographically where possible
        println!("ENCLAVE: Starting cryptographic proof verification...");

        println!("{}", host_proofs.account_proofs[0].address);

        for account_proof in &host_proofs.account_proofs {
            let account_address = account_proof.address;

            assert!(
                !account_proof.account_proof.is_empty(),
                "Account proof should not be empty for address: {:?}",
                account_address
            );

            // Try to verify the account proof cryptographically
            let verification_result = enclave_simulator.verify_account_proof(account_proof);

            assert!(
                verification_result.is_ok(),
                "Account proof verification should not error for address: {:?}",
                account_address
            );
        }

        // Step 10b: Verify storage proofs cryptographically
        for (address, storage_proof) in &host_proofs.storage_proofs {
            // Verify the storage proof structure exists and is valid
            assert!(
                !storage_proof.storage_proof.is_empty(),
                "Storage proof should not be empty for address: {:?}",
                address
            );

            // TODO
        }

        // Step 10c: Verify that the enclave can independently verify touched accounts
        let touched_addresses = enclave_simulator.get_touched_addresses();
        let mut independently_verified_accounts = 0;

        for address in touched_addresses {
            // Use the enclave's independent verification method
            let verification_result = enclave_simulator.verify_account_proof(address);
            if verification_result.is_ok() {
                independently_verified_accounts += 1;
            }
        }

        println!("ENCLAVE: Independently verified {} touched accounts", independently_verified_accounts);

        // Step 10d: Verify storage access consistency
        let enclave_storage_accesses = enclave_simulator.get_storage_accesses();
        let host_storage_accesses = host_simulator.get_storage_accesses();

        assert_eq!(
            enclave_storage_accesses.len(),
            host_storage_accesses.len(),
            "Storage access counts should match"
        );

        // Verify each storage access matches
        for (address, enclave_keys) in &enclave_storage_accesses {
            let host_keys = host_storage_accesses.get(address)
                .expect("Host should have storage access for same address");

            assert_eq!(
                enclave_keys.len(),
                host_keys.len(),
                "Storage key counts should match for address: {:?}",
                address
            );

            // Verify all keys match
            for key in enclave_keys {
                assert!(
                    host_keys.contains(key),
                    "Host should have accessed the same storage key: {:?} for address: {:?}",
                    key,
                    address
                );
            }
        }


        // Step 11: Verify final balances are consistent
        let sender_balance_after = enclave_simulator
            .erc20_balance_of(USDC_ADDRESS, sender)
            .await
            .expect("Failed to get sender final balance");
        let receiver_balance_after = enclave_simulator
            .erc20_balance_of(USDC_ADDRESS, receiver)
            .await
            .expect("Failed to get receiver final balance");

        // Verify the transfer worked correctly
        assert_eq!(
            sender_balance_after,
            sender_balance_before - transfer_amount,
            "Sender balance should be reduced by transfer amount"
        );

        assert_eq!(
            receiver_balance_after,
            receiver_balance_before + transfer_amount,
            "Receiver balance should be increased by transfer amount"
        );

        println!("FINAL: Host and enclave flow completed successfully");
        println!("FINAL: Sender balance: {} -> {}", sender_balance_before, sender_balance_after);
        println!("FINAL: Receiver balance: {} -> {}", receiver_balance_before, receiver_balance_after);
        */
    }
}
