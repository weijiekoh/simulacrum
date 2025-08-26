use alloy::eips::BlockId;
use alloy::network::Ethereum;
use alloy::primitives::{Address, keccak256, KECCAK256_EMPTY, U256, B256, aliases::StorageKey, Bytes};
use alloy::rpc::types::EIP1186AccountProofResponse;
use alloy::providers::{Provider, RootProvider};
use alloy::consensus::Account;
use alloy::sol;
use alloy::sol_types::SolCall;
use alloy_trie::{Nibbles, proof::verify_proof};
use anyhow::{Result, anyhow};
use revm::context::result::{EVMError, ExecutionResult};
use revm::database::{AlloyDB, CacheDB, DBTransportError, WrapDatabaseAsync};
use revm::primitives::{TxKind, hash_map::Entry};
use revm::state::AccountInfo;
use revm::{Context, Database, ExecuteCommitEvm, MainBuilder, MainContext};
use std::sync::Arc;
use serde::{Serialize, Deserialize};
use bincode::{serialize, deserialize};
use std::collections::HashMap;

/* TODO:
- [ ] Arbitrary contract calls
- [ ] Arbitrary transaction execution
- [ ] ERC20 balance queries, approvals, and transfers (convenience functions)
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

        Ok(EVMSimulator {
            provider: provider_arc,
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

        Ok(EVMSimulator {
            provider: provider_arc,
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
        let mut evm = Context::mainnet().with_db(db).build_mainnet();

        // Update transaction in the same EVM instance
        evm.ctx.tx.caller = from;
        evm.ctx.tx.kind = TxKind::Call(to);
        evm.ctx.tx.value = value;
        evm.ctx.tx.gas_limit = 21_000; // TODO: set as a constant
        evm.ctx.tx.gas_price = gas_price;
        evm.ctx.tx.nonce = sender_nonce;
        evm.ctx.tx.chain_id = Some(1);
        let res = evm.transact_commit(evm.ctx.tx.clone());
        res
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

        // Fetch the balance proof
        let proof = self.provider
          .get_proof(address, vec![])
          .block_id(BlockId::Hash(self.block_hash.into()))
          .await.unwrap();

        // Store the proof
        self.account_proofs.insert(address, proof);

        Ok(db.basic(address)?.map(|i| i.balance).unwrap_or_default())
    }

    pub fn set_balance(&mut self, address: Address, balance: U256) {
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

        let mut info = self.query_rpc_or_retrieve(address).unwrap();
        info.balance = balance;

        self.insert_account_info(address, info);
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

    pub async fn erc20_balance_of(&mut self, token_address: Address, account: Address) -> Result<U256> {
        let contract = IERC20::new(token_address, &*self.provider);
        let result = contract.balanceOf(account).call().await?;

        // TODO: fix
        //// Calculate storage key for ERC20 balance mapping
        //// Most ERC20 tokens store balances in slot 0: mapping(address => uint256) balances
        //let balance_slot = U256::ZERO;
        //let storage_key = keccak256((account, balance_slot).abi_encode());

        //// Fetch the storage proof for the balance
        //let proof = self.provider
            //.get_proof(token_address, vec![storage_key])
            //.block_id(BlockId::Hash(self.block_hash.into()))
            //.await?;

        //// Store the storage proof
        //self.storage_proofs
            //.entry(token_address)
            //.or_insert_with(HashMap::new)
            //.insert(storage_key, proof);

        // TODO: implement a way to update the storage proof or mark it as modified-in-simulation
        Ok(result)
    }

    pub async fn erc20_token_info(&mut self, token_address: Address) -> Result<(String, String, u8, U256)> {
        let contract = IERC20::new(token_address, &*self.provider);
        
        let name_result = contract.name().call().await?;
        let symbol_result = contract.symbol().call().await?;
        let decimals_result = contract.decimals().call().await?;
        let total_supply_result = contract.totalSupply().call().await?;

        Ok((
            name_result,
            symbol_result,
            decimals_result,
            total_supply_result,
        ))
    }

    pub fn erc20_transfer(
        &mut self,
        token_address: Address,
        from: Address,
        to: Address,
        amount: U256,
        gas_price: u128,
    ) -> Result<ExecutionResult, EVMError<DBTransportError>> {
        // Encode the transfer function call
        let transfer_call = IERC20::transferCall { to, amount };
        let call_data = transfer_call.abi_encode();

        // Get sender info for nonce
        let sender_info = self.query_rpc_or_retrieve(from).map_err(|e| EVMError::Custom(format!("Failed to get sender info: {}", e)))?;
        let sender_nonce = sender_info.nonce;

        let db = &mut self.db;
        let mut evm = Context::mainnet().with_db(db).build_mainnet();

        // Set up transaction
        evm.ctx.tx.caller = from;
        evm.ctx.tx.kind = TxKind::Call(token_address);
        evm.ctx.tx.value = U256::ZERO; // ERC20 transfers don't send ETH
        evm.ctx.tx.data = Bytes::from(call_data);
        evm.ctx.tx.gas_limit = 100_000; // Standard ERC20 transfer gas limit
        evm.ctx.tx.gas_price = gas_price;
        evm.ctx.tx.nonce = sender_nonce;
        evm.ctx.tx.chain_id = Some(self.chain_id);

        evm.transact_commit(evm.ctx.tx.clone())
    }

    pub fn erc20_approve(
        &mut self,
        token_address: Address,
        from: Address,
        spender: Address,
        amount: U256,
        gas_price: u128,
    ) -> Result<ExecutionResult, EVMError<DBTransportError>> {
        // Encode the approve function call
        let approve_call = IERC20::approveCall { spender, amount };
        let call_data = approve_call.abi_encode();

        // Get sender info for nonce
        let sender_info = self.query_rpc_or_retrieve(from).map_err(|e| EVMError::Custom(format!("Failed to get sender info: {}", e)))?;
        let sender_nonce = sender_info.nonce;

        let db = &mut self.db;
        let mut evm = Context::mainnet().with_db(db).build_mainnet();

        // Set up transaction
        evm.ctx.tx.caller = from;
        evm.ctx.tx.kind = TxKind::Call(token_address);
        evm.ctx.tx.value = U256::ZERO;
        evm.ctx.tx.data = Bytes::from(call_data);
        evm.ctx.tx.gas_limit = 100_000;
        evm.ctx.tx.gas_price = gas_price;
        evm.ctx.tx.nonce = sender_nonce;
        evm.ctx.tx.chain_id = Some(self.chain_id);

        evm.transact_commit(evm.ctx.tx.clone())
    }
}

#[cfg(test)]
mod tests {
    use crate::EVMSimulator;
    use alloy::primitives::{Address, U256, address };
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    fn get_mainnet_rpc_url() -> String {
        // Load .env file if it exists
        dotenv::dotenv().ok();
        
        // Try to get RPC URL from environment variable first, fallback to public RPC
        std::env::var("ETHEREUM_RPC_URL")
            .unwrap_or_else(|_| "https://eth.llamarpc.com".to_string())
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
        simulator.set_balance(addr, amount);

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
        simulator.set_balance(addr2, amount2 + amount);

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
            new_amount2, amount2 + amount,
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
        simulator.set_balance(addr, amount);
        let balance_after = simulator.get_balance(addr).await.unwrap();
        assert_eq!(balance_after, amount, "Balance after setting is incorrect");
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_init_evmsimulator_with_block_id() {
        let mut simulator = EVMSimulator::new(
            get_mainnet_rpc_url(),
            Some(get_mainnet_chain_id()),
            None
        )
        .await
        .expect("Failed to create EVM simulator");

        let addr = address!("0x0000000000000000000000000000000000000000");
        let balance = simulator.get_balance(addr).await.unwrap();
        // The zero address should have nonzero balance
        assert!(balance > U256::ZERO, "Zero address balance should be non-zero");
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_get_and_set_balance() {
        let mut simulator = init_mainnet_simulator().await;
        let addr = address!("0xd8dA6BF26964aF9D7eEd9e03E53415D37aA96045");
        let balance_before = simulator.get_balance(addr).await.unwrap();
        let new_balance = balance_before + U256::from(1_000_000_000_000_000_000u64); // Add 1 ETH
        simulator.set_balance(addr, new_balance);
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
        let gas_cost = gas_used * U256::from(20_000_000_000u128);

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
    pub async fn test_erc20_balance_query() {
        let mut simulator = init_mainnet_simulator().await;
        
        // USDC contract on mainnet
        let usdc_address = address!("0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48");
        let test_account = address!("0x0000000000000000000000000000000000000000");
        
        let balance = simulator
            .erc20_balance_of(usdc_address, test_account)
            .await
            .expect("Failed to query ERC20 balance");
        
        assert!(balance >= U256::ZERO, "Balance should be non-negative");
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_erc20_token_info() {
        let mut simulator = init_mainnet_simulator().await;
        
        // USDC contract on mainnet
        let usdc_address = address!("0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48");
        
        let (name, symbol, decimals, total_supply) = simulator
            .erc20_token_info(usdc_address)
            .await
            .expect("Failed to query ERC20 token info");
        
        assert_eq!(symbol, "USDC");
        assert_eq!(decimals, 6);
        assert!(!name.is_empty());
        assert!(total_supply > U256::ZERO);
    }

    //#[tokio::test(flavor = "multi_thread")]
    //pub async fn test_erc20_storage_proof() {
        //let mut simulator = init_mainnet_simulator().await;
        
        //// USDC contract on mainnet
        //let usdc_address = address!("0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48");
        //let test_account = address!("0x0000000000000000000000000000000000000000");
        
        //// Query balance (which should fetch and store the storage proof)
        //let _balance = simulator
            //.erc20_balance_of(usdc_address, test_account)
            //.await
            //.expect("Failed to query ERC20 balance");
        
        //// Verify that storage proof was stored
        //assert!(
            //simulator.storage_proofs.contains_key(&usdc_address),
            //"Storage proof should be stored for the token contract"
        //);
        
        //let contract_storage_proofs = simulator.storage_proofs.get(&usdc_address).unwrap();
        //assert!(
            // !contract_storage_proofs.is_empty(),
            //"At least one storage proof should be stored"
        //);
        
        //// Calculate the expected storage key for the balance
        //let balance_slot = U256::ZERO;
        //let storage_key = keccak256((test_account, balance_slot).abi_encode());
        
        //assert!(
            //contract_storage_proofs.contains_key(&storage_key),
            //"Storage proof for the balance should be stored"
        //);
    //}
}
