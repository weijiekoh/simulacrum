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
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;

pub mod tracer;

const TRANSFER_GAS_COST: u64 = 21_000; // Standard gas cost for an ETH transfer

/* TODO:
- [ ] Arbitrary contract calls
- [ ] Arbitrary transaction execution
*/

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
    pub provider: Arc<RootProvider<Ethereum>>,
    pub provider_url: String,
    pub chain_id: u64,
    pub block_num: u64,
    pub block_hash: B256,
    pub state_root: B256,
    tracer: tracer::AccessTracer,
    db: CacheDB<WrapDatabaseAsync<AlloyDB<Ethereum, Arc<RootProvider<Ethereum>>>>>,
    account_proofs: HashMap<Address, EIP1186AccountProofResponse>,
    storage_proofs: HashMap<Address, HashMap<StorageKey, EIP1186AccountProofResponse>>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct EVMSimulatorSnapshot {
    pub provider: String,
    pub chain_id: u64,
    pub block_num: u64,
    pub block_hash: B256,
    pub state_root: B256,
    pub db_snapshot: Vec<u8>,
    pub account_proofs: HashMap<Address, EIP1186AccountProofResponse>,
    pub storage_proofs: HashMap<Address, HashMap<StorageKey, EIP1186AccountProofResponse>>,
}

impl EVMSimulator {
    // Helper function for ERC20 view calls
    async fn erc20_view_call(
        &mut self,
        token_address: Address,
        call_data: Vec<u8>,
    ) -> Result<ExecutionResult, EVMError<DBTransportError>> {
        let db = &mut self.db;
        let mut evm = Context::mainnet()
            .with_db(db)
            .build_mainnet_with_inspector(&mut self.tracer);

        // Set up transaction for view call
        evm.ctx.tx.caller = Address::ZERO; // Use zero address as caller for view calls
        evm.ctx.tx.kind = TxKind::Call(token_address);
        evm.ctx.tx.value = U256::ZERO;
        evm.ctx.tx.data = Bytes::from(call_data);
        evm.ctx.tx.gas_limit = 100_000; // Sufficient gas for view calls
        evm.ctx.tx.gas_price = 0; // No gas price needed for view calls
        evm.ctx.tx.nonce = 0;
        evm.ctx.tx.chain_id = Some(self.chain_id);

        // Execute the transaction with inspection
        let result = evm.inspect_tx(evm.ctx.tx.clone())?;

        Ok(result.result)
    }
    fn insert_account_info(&mut self, address: Address, info: AccountInfo) {
        let db = &mut self.db;
        db.cache.accounts.insert(address, info.into());
    }

    fn query_rpc_or_retrieve(&mut self, address: Address) -> Result<AccountInfo> {
        let db = &mut self.db;
        Ok(db.basic(address)?.unwrap())
    }

    pub fn to_snapshot(&self) -> EVMSimulatorSnapshot {
        let db_snapshot = serialize(&self.db.cache).expect("Failed to serialize DB cache");

        EVMSimulatorSnapshot {
            provider: self.provider_url.clone(),
            chain_id: self.chain_id,
            block_num: self.block_num,
            block_hash: self.block_hash,
            state_root: self.state_root,
            db_snapshot,
            account_proofs: self.account_proofs.clone(),
            storage_proofs: self.storage_proofs.clone(),
        }
    }

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
        if !snapshot.db_snapshot.is_empty() {
            let cached_state = deserialize(&snapshot.db_snapshot)?;
            cache_db.cache = cached_state;
        }

        let tracer = tracer::AccessTracer::default();

        Ok(EVMSimulator {
            provider: provider_arc,
            provider_url: snapshot.provider,
            chain_id: snapshot.chain_id,
            block_num: snapshot.block_num,
            block_hash: snapshot.block_hash,
            state_root: snapshot.state_root,
            db: cache_db,
            tracer,
            account_proofs: snapshot.account_proofs,
            storage_proofs: snapshot.storage_proofs,
        })
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
        let alloy_db = AlloyDB::new(provider_arc.clone(), block_id);
        let wrapped_db = WrapDatabaseAsync::new(alloy_db).expect("Failed to wrap database");
        let cache_db = CacheDB::new(wrapped_db);
        let tracer = tracer::AccessTracer::default();

        Ok(EVMSimulator {
            provider: provider_arc,
            provider_url: rpc_url,
            chain_id: cid,
            block_num,
            block_hash,
            state_root,
            db: cache_db,
            tracer,
            account_proofs: HashMap::new(),
            storage_proofs: HashMap::new(),
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
    ) -> Result<ExecutionResult, EVMError<DBTransportError>> {
        // Get balances and nonce before transaction (will lazy load from RPC)
        let sender_info = self.query_rpc_or_retrieve(from).unwrap();
        let sender_nonce = sender_info.nonce;

        let db = &mut self.db;
        let mut evm = Context::mainnet()
            .with_db(db)
            .build_mainnet_with_inspector(&mut self.tracer);

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
        Ok(res.result)
    }

    pub fn verify_account_proof(&mut self, address: Address) -> Result<bool> {
        let account_proof = match self.account_proofs.get(&address) {
            Some(proof) => proof,
            None => return Err(anyhow!("Account proof for address {} not found", address)),
        };

        let account = Account {
            nonce: account_proof.nonce,
            balance: account_proof.balance,
            storage_root: account_proof.storage_hash,
            code_hash: account_proof.code_hash,
        };

        // RLP-encode the account data (aka the MPT leaf)
        let expected_account_rlp = alloy::rlp::encode(&account);

        // Verify the account proof against the state root
        let key = keccak256(address);
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
            .get_proof(address, vec![])
            .block_id(BlockId::Hash(self.block_hash.into()))
            .await
            .unwrap();

        // Store the proof
        self.account_proofs.insert(address, proof);

        Ok(db.basic(address)?.map(|i| i.balance).unwrap_or_default())
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
    ) -> Result<U256> {
        // Encode the balanceOf function call
        let balance_call = IERC20::balanceOfCall { account };
        let call_data = balance_call.abi_encode();

        let result = self.erc20_view_call(token_address, call_data).await?;

        // Check if the call was successful
        if !result.is_success() {
            return Err(anyhow!("ERC20 balanceOf call failed"));
        }

        // Decode the result
        let output = result.output().unwrap_or_default();
        if output.len() < 32 {
            return Err(anyhow!("Invalid ERC20 balanceOf response"));
        }

        // Parse the U256 balance from the output (first 32 bytes)
        let balance = U256::from_be_slice(&output[..32]);
        Ok(balance)
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
    ) -> Result<ExecutionResult, EVMError<DBTransportError>> {
        // Encode the approve function call
        let approve_call = IERC20::approveCall { spender, amount };
        let call_data = approve_call.abi_encode();

        // Get caller's nonce if not provided
        let caller_nonce = if let Some(n) = nonce {
            n
        } else {
            let caller_info = self.query_rpc_or_retrieve(caller).unwrap();
            caller_info.nonce
        };

        let db = &mut self.db;
        let mut evm = Context::mainnet()
            .with_db(db)
            .build_mainnet_with_inspector(&mut self.tracer);

        // Set up transaction to call approve
        evm.ctx.tx.caller = caller;
        evm.ctx.tx.kind = TxKind::Call(token_address);
        evm.ctx.tx.value = U256::ZERO;
        evm.ctx.tx.data = Bytes::from(call_data);
        evm.ctx.tx.gas_limit = gas_limit;
        evm.ctx.tx.gas_price = gas_price;
        evm.ctx.tx.nonce = caller_nonce;
        evm.ctx.tx.chain_id = Some(self.chain_id);

        // Execute the transaction with inspection
        let res = evm.inspect_tx(evm.ctx.tx.clone()).unwrap();
        evm.commit(res.state);

        Ok(res.result)
    }

    pub async fn erc20_allowance(
        &mut self,
        token_address: Address,
        owner: Address,
        spender: Address,
    ) -> Result<U256> {
        // Encode the allowance function call
        let allowance_call = IERC20::allowanceCall { owner, spender };
        let call_data = allowance_call.abi_encode();

        let result = self.erc20_view_call(token_address, call_data).await?;

        // Check if the call was successful
        if !result.is_success() {
            return Err(anyhow!("ERC20 allowance call failed"));
        }

        // Decode the result
        let output = result.output().unwrap_or_default();
        if output.len() < 32 {
            return Err(anyhow!("Invalid ERC20 allowance response"));
        }

        // Parse the U256 allowance from the output (first 32 bytes)
        let allowance = U256::from_be_slice(&output[..32]);
        Ok(allowance)
    }

    pub async fn erc20_total_supply(&mut self, token_address: Address) -> Result<U256> {
        // Encode the totalSupply function call
        let total_supply_call = IERC20::totalSupplyCall {};
        let call_data = total_supply_call.abi_encode();

        let result = self.erc20_view_call(token_address, call_data).await?;

        // Check if the call was successful
        if !result.is_success() {
            return Err(anyhow!("ERC20 totalSupply call failed"));
        }

        // Decode the result
        let output = result.output().unwrap_or_default();
        if output.len() < 32 {
            return Err(anyhow!("Invalid ERC20 totalSupply response"));
        }

        // Parse the U256 total supply from the output (first 32 bytes)
        let total_supply = U256::from_be_slice(&output[..32]);
        Ok(total_supply)
    }

    pub async fn erc20_decimals(&mut self, token_address: Address) -> Result<u8> {
        // Encode the decimals function call
        let decimals_call = IERC20::decimalsCall {};
        let call_data = decimals_call.abi_encode();

        let result = self.erc20_view_call(token_address, call_data).await?;

        // Check if the call was successful
        if !result.is_success() {
            return Err(anyhow!("ERC20 decimals call failed"));
        }

        // Decode the result
        let output = result.output().unwrap_or_default();
        if output.len() < 32 {
            return Err(anyhow!("Invalid ERC20 decimals response"));
        }

        // Parse the u8 decimals from the output (last byte of 32 bytes)
        let decimals = output[31];
        Ok(decimals)
    }

    pub async fn erc20_name(&mut self, token_address: Address) -> Result<String> {
        // Encode the name function call
        let name_call = IERC20::nameCall {};
        let call_data = name_call.abi_encode();

        let result = self.erc20_view_call(token_address, call_data).await?;

        // Check if the call was successful
        if !result.is_success() {
            return Err(anyhow!("ERC20 name call failed"));
        }

        // Decode the result
        let output = result.output().unwrap_or_default();
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
        Ok(name)
    }

    pub async fn erc20_symbol(&mut self, token_address: Address) -> Result<String> {
        // Encode the symbol function call
        let symbol_call = IERC20::symbolCall {};
        let call_data = symbol_call.abi_encode();

        let result = self.erc20_view_call(token_address, call_data).await?;

        // Check if the call was successful
        if !result.is_success() {
            return Err(anyhow!("ERC20 symbol call failed"));
        }

        // Decode the result
        let output = result.output().unwrap_or_default();
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
        Ok(symbol)
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
    ) -> Result<ExecutionResult, EVMError<DBTransportError>> {
        // Encode the transfer function call
        let transfer_call = IERC20::transferCall { to, amount };
        let call_data = transfer_call.abi_encode();

        // Get caller's nonce if not provided
        let caller_nonce = if let Some(n) = nonce {
            n
        } else {
            let caller_info = self.query_rpc_or_retrieve(from).unwrap();
            caller_info.nonce
        };

        let db = &mut self.db;
        let mut evm = Context::mainnet()
            .with_db(db)
            .build_mainnet_with_inspector(&mut self.tracer);

        // Set up transaction to call transfer
        evm.ctx.tx.caller = from;
        evm.ctx.tx.kind = TxKind::Call(token_address);
        evm.ctx.tx.value = U256::ZERO;
        evm.ctx.tx.data = Bytes::from(call_data);
        evm.ctx.tx.gas_limit = gas_limit;
        evm.ctx.tx.gas_price = gas_price;
        evm.ctx.tx.nonce = caller_nonce;
        evm.ctx.tx.chain_id = Some(self.chain_id);

        // Execute the transaction with inspection
        let res = evm.inspect_tx(evm.ctx.tx.clone()).unwrap();
        evm.commit(res.state);

        Ok(res.result)
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
    ) -> Result<ExecutionResult, EVMError<DBTransportError>> {
        // Encode the transferFrom function call
        let transfer_from_call = IERC20::transferFromCall { from, to, amount };
        let call_data = transfer_from_call.abi_encode();

        // Get caller's nonce if not provided
        let caller_nonce = if let Some(n) = nonce {
            n
        } else {
            let caller_info = self.query_rpc_or_retrieve(caller).unwrap();
            caller_info.nonce
        };

        let db = &mut self.db;
        let mut evm = Context::mainnet()
            .with_db(db)
            .build_mainnet_with_inspector(&mut self.tracer);

        // Set up transaction to call transferFrom
        evm.ctx.tx.caller = caller;
        evm.ctx.tx.kind = TxKind::Call(token_address);
        evm.ctx.tx.value = U256::ZERO;
        evm.ctx.tx.data = Bytes::from(call_data);
        evm.ctx.tx.gas_limit = gas_limit;
        evm.ctx.tx.gas_price = gas_price;
        evm.ctx.tx.nonce = caller_nonce;
        evm.ctx.tx.chain_id = Some(self.chain_id);

        // Execute the transaction with inspection
        let res = evm.inspect_tx(evm.ctx.tx.clone()).unwrap();
        evm.commit(res.state);

        Ok(res.result)
    }
}

#[cfg(test)]
mod tests {
    use crate::EVMSimulator;
    use alloy::primitives::{Address, U256, address};
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha8Rng;

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
        let new_balance = balance_before + U256::from(1_000_000_000_000_000_000u64); // Add 1 ETH
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
        let result = simulator.verify_account_proof(addr);
        assert!(result.is_ok(), "Account proof verification failed");
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_transfer_eth() {
        let mut simulator = init_mainnet_simulator().await;

        let sender = address!("0xd8dA6BF26964aF9D7eEd9e03E53415D37aA96045");
        let receiver = address!("0x1aaaaaaaaaaaaaaaaa0000000000000000000000");
        let transfer_amount = U256::from(1_000_000_000_000_000_000u64); // 1 ETH
        let gas_price = 20_000_000_000u128; // 20 gwei

        let sender_balance_before = simulator
            .get_balance(sender)
            .await
            .expect("Failed to get sender balance");

        let receiver_balance_before = simulator
            .get_balance(receiver)
            .await
            .expect("Failed to get receiver balance");

        // Simulate a simple ETH transfer
        let result = simulator
            .transfer_eth(sender, receiver, transfer_amount, gas_price)
            .expect("Failed to execute transaction");

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
        let token_address = address!("0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48");
        let test_account = address!("0x0000000000000000000000000000000000000000");

        let balance = simulator
            .erc20_balance_of(token_address, test_account)
            .await
            .expect("Failed to query ERC20 balance");

        assert!(balance >= U256::ZERO, "Balance should be non-negative");
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_erc20_approve() {
        let mut simulator = init_mainnet_simulator().await;

        // USDC contract on mainnet
        let token_address = address!("0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48");

        // Test accounts
        let owner = address!("0xd8dA6BF26964aF9D7eEd9e03E53415D37aA96045"); // Account with ETH for gas
        let spender = address!("0x742d35Cc662C910EF7B5BdD2C90B5948a5d8EBB6"); // Random spender address

        // Set some ETH balance for the owner to pay for gas
        let _ = simulator.set_balance(owner, U256::from(1_000_000_000_000_000_000u64)); // 1 ETH

        // Check initial allowance (don't assume it's 0)
        let _initial_allowance = simulator
            .erc20_allowance(token_address, owner, spender)
            .await
            .expect("Failed to query initial allowance");

        // First approval: Set initial allowance to some value
        let first_approve_amount = U256::from(500_000_000u64); // 500 USDC
        let result1 = simulator
            .erc20_approve(
                token_address,
                owner,
                spender,
                first_approve_amount,
                None,
                100_000,
                20_000_000_000u128,
            )
            .await
            .expect("Failed to execute first ERC20 approve");

        assert!(
            result1.is_success(),
            "First approve transaction should succeed"
        );

        // Check allowance after first approval
        let allowance_after_first = simulator
            .erc20_allowance(token_address, owner, spender)
            .await
            .expect("Failed to query allowance after first approve");

        assert_eq!(
            allowance_after_first, first_approve_amount,
            "First approval should set allowance correctly"
        );

        // Second approval: Change allowance to new value
        let second_approve_amount = U256::from(1500_000_000u64); // 1500 USDC
        let result2 = simulator
            .erc20_approve(
                token_address,
                owner,
                spender,
                second_approve_amount,
                None,
                100_000,
                20_000_000_000u128,
            )
            .await
            .expect("Failed to execute second ERC20 approve");

        assert!(
            result2.is_success(),
            "Second approve transaction should succeed"
        );

        // Check final allowance
        let final_allowance = simulator
            .erc20_allowance(token_address, owner, spender)
            .await
            .expect("Failed to query final allowance");

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
            .expect("Failed to query ERC20 balance");

        assert!(balance >= U256::ZERO, "Balance should be non-negative");
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_erc20_token_info() {
        let mut simulator = init_mainnet_simulator().await;

        // USDC contract on mainnet
        let token_address = address!("0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48");

        // Test individual functions
        let name = simulator
            .erc20_name(token_address)
            .await
            .expect("Failed to query ERC20 name");

        let symbol = simulator
            .erc20_symbol(token_address)
            .await
            .expect("Failed to query ERC20 symbol");

        let decimals = simulator
            .erc20_decimals(token_address)
            .await
            .expect("Failed to query ERC20 decimals");

        let total_supply = simulator
            .erc20_total_supply(token_address)
            .await
            .expect("Failed to query ERC20 total supply");

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
        let token_address = address!("0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48");

        // Test accounts - using address that has positive USDC balance
        let from = address!("0xd8dA6BF26964aF9D7eEd9e03E53415D37aA96045"); // Account with existing USDC balance
        let to = address!("0x742d35Cc662C910EF7B5BdD2C90B5948a5d8EBB6"); // Recipient address

        // Set some ETH balance for the sender to pay for gas
        let _ = simulator.set_balance(from, U256::from(1_000_000_000_000_000_000u64)); // 1 ETH

        // Transfer amount (100 USDC = 100 * 10^6)
        let transfer_amount = U256::from(100_000_000u64);

        // Record balances before transfer
        let from_balance_before = simulator
            .erc20_balance_of(token_address, from)
            .await
            .expect("Failed to query sender balance");
        let to_balance_before = simulator
            .erc20_balance_of(token_address, to)
            .await
            .expect("Failed to query recipient balance");

        // Execute the transfer
        let result = simulator
            .erc20_transfer(
                token_address,
                from,
                to,
                transfer_amount,
                None,               // Auto-fetch nonce
                300_000,            // Gas limit
                20_000_000_000u128, // Gas price (20 gwei)
            )
            .await
            .expect("Failed to execute transfer");

        // Check balances after transfer
        let from_balance_after = simulator
            .erc20_balance_of(token_address, from)
            .await
            .expect("Failed to query sender balance after transfer");
        let to_balance_after = simulator
            .erc20_balance_of(token_address, to)
            .await
            .expect("Failed to query recipient balance after transfer");

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
        let token_address = address!("0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48");

        // Test accounts - using address that has positive USDC balance
        let owner = address!("0xd8dA6BF26964aF9D7eEd9e03E53415D37aA96045"); // Token owner with existing USDC balance
        let spender = address!("0x742d35Cc662C910EF7B5BdD2C90B5948a5d8EBB6"); // Account doing the transfer
        let recipient = address!("0x1234567890123456789012345678901234567890"); // Transfer recipient

        // Set ETH balances for gas fees
        let _ = simulator.set_balance(owner, U256::from(1_000_000_000_000_000_000u64)); // 1 ETH
        let _ = simulator.set_balance(spender, U256::from(1_000_000_000_000_000_000u64)); // 1 ETH

        // Transfer amount (100 USDC = 100 * 10^6)
        let transfer_amount = U256::from(100_000_000u64);
        let approval_amount = U256::from(200_000_000u64); // Approve 200 USDC

        // Step 1: Owner approves spender to spend tokens
        let approve_result = simulator
            .erc20_approve(
                token_address,
                owner,
                spender,
                approval_amount,
                None,               // Auto-fetch nonce
                100_000,            // Gas limit
                20_000_000_000u128, // Gas price (20 gwei)
            )
            .await
            .expect("Failed to execute approval");

        assert!(approve_result.is_success());

        // Verify allowance was set
        let allowance = simulator
            .erc20_allowance(token_address, owner, spender)
            .await
            .expect("Failed to query allowance");
        assert_eq!(allowance, approval_amount);

        // Record balances before transferFrom
        let owner_balance_before = simulator
            .erc20_balance_of(token_address, owner)
            .await
            .expect("Failed to query owner balance");
        let recipient_balance_before = simulator
            .erc20_balance_of(token_address, recipient)
            .await
            .expect("Failed to query recipient balance");

        // Step 2: Spender executes transferFrom
        let transfer_result = simulator
            .erc20_transfer_from(
                token_address,
                spender,   // Caller doing the transfer
                owner,     // From address
                recipient, // To address
                transfer_amount,
                None,               // Auto-fetch nonce
                300_000,            // Gas limit
                20_000_000_000u128, // Gas price (20 gwei)
            )
            .await
            .expect("Failed to execute transferFrom");

        assert!(transfer_result.is_success());

        // Check balances after transferFrom
        let owner_balance_after = simulator
            .erc20_balance_of(token_address, owner)
            .await
            .expect("Failed to query owner balance after transfer");
        let recipient_balance_after = simulator
            .erc20_balance_of(token_address, recipient)
            .await
            .expect("Failed to query recipient balance after transfer");
        let allowance_after = simulator
            .erc20_allowance(token_address, owner, spender)
            .await
            .expect("Failed to query allowance after transfer");

        // Verify the transferFrom worked correctly
        assert_eq!(owner_balance_after, owner_balance_before - transfer_amount);
        assert_eq!(
            recipient_balance_after,
            recipient_balance_before + transfer_amount
        );
        assert_eq!(allowance_after, approval_amount - transfer_amount); // Allowance should be reduced
    }
}
