use crate::simulator::EVMSimulatorOnline;
use alloy::primitives::{Address, U256, address};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;

#[cfg(test)]
pub mod simulator;

#[cfg(test)]
pub mod eth;

#[cfg(test)]
pub mod erc20;

#[cfg(test)]
pub mod host_and_enclave;

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

pub fn get_mainnet_rpc_url() -> String {
    // Load .env file if it exists
    dotenv::dotenv().ok();

    // Try to get RPC URL from environment variable first, fallback to public RPC
    std::env::var("ETHEREUM_RPC_URL").unwrap_or_else(|_| "https://eth.llamarpc.com".to_string())
}

fn get_mainnet_chain_id() -> u64 {
    1 // Mainnet chain ID
}

pub async fn init_mainnet_simulator_online() -> EVMSimulatorOnline {
    let url = get_mainnet_rpc_url();
    let simulator = EVMSimulatorOnline::new(
        url,
        Some(get_mainnet_chain_id()),
        None, // None should default to the latest block number
        )
        .await
        .expect("Failed to create EVM simulator");
    simulator
}

pub fn gen_random_address(seed: u64) -> Address {
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let mut bytes = [0u8; 20];
    rng.fill(&mut bytes);
    Address::from(bytes)
}

