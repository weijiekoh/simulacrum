use alloy::eips::BlockId;
use alloy::network::Ethereum;
use alloy::primitives::{Address, KECCAK256_EMPTY, U256, Uint};
use alloy::providers::{Provider, RootProvider};
use anyhow::Result;
use revm::context::result::{EVMError, ExecutionResult};
use revm::database::{AlloyDB, CacheDB, DBTransportError, WrapDatabaseAsync};
use revm::primitives::{TxKind, hash_map::Entry};
use revm::state::AccountInfo;
use revm::{Context, Database, ExecuteCommitEvm, MainBuilder, MainContext};
use std::sync::Arc;

/* TODO:
- [ ] Arbitrary contract calls
- [ ] Arbitrary transaction execution
- [ ] ERC20 balance queries, approvals, and transfers (convenience functions)
*/

pub type HttpProvider = RootProvider<Ethereum>;

pub struct EVMSimulator {
    pub provider: Arc<RootProvider<Ethereum>>,
    pub chain_id: u64,
    pub block_number: u64,
    db: Option<CacheDB<WrapDatabaseAsync<AlloyDB<Ethereum, Arc<RootProvider<Ethereum>>>>>>,
}

impl EVMSimulator {
    fn insert_account_info(&mut self, address: Address, info: AccountInfo) {
        let db = self.db.as_mut().expect("DB missing");
        db.cache.accounts.insert(address, info.into());
    }

    fn query_rpc_or_retrive(&mut self, address: Address) -> Result<AccountInfo> {
        let db = self.db.as_mut().expect("DB missing");
        // TODO: Handle the case where the account is not found in the local cache
        Ok(db.basic(address)?.unwrap())
    }

    pub async fn new(
        rpc_url: String,
        chain_id: Option<u64>,
        block_number: Option<u64>,
    ) -> Result<Self> {
        let provider = RootProvider::<Ethereum>::connect(&rpc_url).await?;

        let provider_cid = provider.get_chain_id().await?;

        // If the chain ID is provided, check if it matches the provider's chain ID
        let cid = if chain_id.is_none() {
            provider_cid
        } else {
            let given_cid = chain_id.unwrap();
            if given_cid != provider_cid {
                return Err(anyhow::anyhow!(
                    "Chain ID mismatch: expected {}, got {}",
                    provider_cid,
                    given_cid
                ));
            }
            given_cid
        };

        // If the block number is not provided, use the latest block number from the provider
        let latest_block_number = provider.get_block_number().await?;
        let bn = if block_number.is_none() {
            latest_block_number
        } else {
            let given_bn = block_number.unwrap();
            if given_bn > latest_block_number {
                return Err(anyhow::anyhow!(
                    "Block number mismatch: expected at most {}, got {}",
                    latest_block_number,
                    given_bn
                ));
            }
            given_bn
        };
        let block_id = BlockId::number(bn);

        // Set up the DB
        let provider_arc = Arc::new(provider);
        let alloy_db = AlloyDB::new(provider_arc.clone(), block_id);
        let wrapped_db = WrapDatabaseAsync::new(alloy_db).expect("Failed to wrap database");
        let cache_db = CacheDB::new(wrapped_db);

        Ok(EVMSimulator {
            provider: provider_arc,
            chain_id: cid,
            block_number: bn,
            db: Some(cache_db),
        })
    }

    // TODO: implement a way to specify either gas_price or EIP1559 parameters
    pub fn transfer_eth(
        &mut self,
        from: Address,
        to: Address,
        value: Uint<256, 4>, // in wei
        gas_price: u128,
    ) -> Result<ExecutionResult, EVMError<DBTransportError>> {
        // Get balances and nonce before transaction (will lazy load from RPC)
        let sender_info = self.query_rpc_or_retrive(from).unwrap();
        let sender_nonce = sender_info.nonce;

        let mut db = self.db.as_mut().expect("DB missing");
        let mut evm = Context::mainnet().with_db(&mut db).build_mainnet();

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

    pub fn get_balance(&mut self, address: Address) -> Result<U256> {
        let mut db = self.db.take().expect("DB missing");
        let account_info = db.basic(address)?;
        self.db = Some(db); // Restore the DB after use
        match account_info {
            Some(info) => Ok(info.balance),
            None => Ok(U256::ZERO),
        }
    }

    pub fn set_balance(&mut self, address: Address, balance: U256) {
        let db = self.db.as_mut().expect("DB missing");

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

        let mut info = self.query_rpc_or_retrive(address).unwrap();
        info.balance = balance;

        self.insert_account_info(address, info);
    }

    pub fn is_account_vacant(&mut self, address: Address) -> Result<bool> {
        let db = self.db.as_mut().expect("DB missing");
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
}

#[cfg(test)]
mod tests {
    use crate::EVMSimulator;
    use alloy::primitives::{Address, U256, address};
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    fn get_mainnet_rpc_url() -> String {
        "https://eth.llamarpc.com".to_string()
    }

    fn get_mainnet_chain_id() -> u64 {
        1 // Mainnet chain ID
    }

    async fn init_mainnet_simulator() -> EVMSimulator {
        let simulator = EVMSimulator::new(
            get_mainnet_rpc_url(),
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
        let balance_before = simulator.get_balance(addr).unwrap();
        assert_eq!(
            balance_before,
            U256::ZERO,
            "Balance before setting is not zero"
        );
        simulator.set_balance(addr, amount);
        let balance_after = simulator.get_balance(addr).unwrap();
        assert_eq!(balance_after, amount, "Balance after setting is incorrect");
    }

    #[tokio::test(flavor = "multi_thread")]
    pub async fn test_get_and_set_balance() {
        let mut simulator = init_mainnet_simulator().await;
        let addr = address!("0xd8dA6BF26964aF9D7eEd9e03E53415D37aA96045");
        let balance_before = simulator.get_balance(addr).unwrap();
        let new_balance = balance_before + U256::from(1_000_000_000_000_000_000u64); // Add 1 ETH
        simulator.set_balance(addr, new_balance);
        let balance_after = simulator.get_balance(addr).unwrap();
        assert_eq!(
            balance_after, new_balance,
            "Balance after setting is incorrect"
        );
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
            .expect("Failed to get sender balance");

        let receiver_balance_before = simulator
            .get_balance(receiver)
            .expect("Failed to get receiver balance");

        // Simulate a simple ETH transfer
        let result = simulator
            .transfer_eth(sender, receiver, transfer_amount, gas_price)
            .expect("Failed to execute transaction");

        let sender_balance_after = simulator
            .get_balance(sender)
            .expect("Failed to get sender balance after transaction");
        let receiver_balance_after = simulator
            .get_balance(receiver)
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
}
