use crate::simulator::{EVMSimulatorOffline, EVMSimulatorOnline};
use alloy::primitives::address;
use alloy::primitives::U256;
use crate::tests::{
    init_mainnet_simulator_online,
    get_mainnet_chain_id,
    get_mainnet_rpc_url,
    gen_random_address,
    ETH_1,
};

#[tokio::test(flavor = "multi_thread")]
pub async fn test_snapshot() {
    // Original simulator: set 0x0 to have 1 ETH
    let mut simulator = init_mainnet_simulator_online().await;
    let addr = address!("0x0000000000000000000000000000000000000000");
    let amount = simulator.get_balance(addr).await.unwrap();

    // Original simulator: addr2 has X ETH
    let addr2 = address!("0xd8dA6BF26964aF9D7eEd9e03E53415D37aA96045");
    let amount2 = simulator.get_balance(addr2).await.unwrap();

    // Take snapshot
    let snapshot = simulator.to_snapshot();

    // Create an offline simulator from the snapshot
    let mut new_simulator = EVMSimulatorOffline::from_snapshot(snapshot)
        .await
        .expect("Failed to restore EVM simulator from snapshot");

    // Get balance of 0x0 from new_simulator
    let restored_balance = new_simulator.get_balance_offline(addr).await.unwrap();

    // Check
    assert_eq!(
        restored_balance, amount,
        "Restored balance does not match the original"
    );

    // Get balance of addr2 from new_simulator
    let new_amount2 = new_simulator.get_balance_offline(addr2).await.unwrap();

    // Check
    assert_eq!(
        new_amount2, amount2,
        "Restored balance for addr2 does not match the original"
    );
}

#[tokio::test(flavor = "multi_thread")]
pub async fn test_is_vacant() {
    let mut simulator = init_mainnet_simulator_online().await;
    let addr = address!("0x0000000000000000000000000000000000000000");
    let iv = simulator.is_account_vacant(addr).unwrap();
    assert!(!iv, "The zero address is not vacant on mainnet");
}

#[tokio::test(flavor = "multi_thread")]
pub async fn test_set_balance_of_vacant_account() {
    let mut simulator = init_mainnet_simulator_online().await;
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
        EVMSimulatorOnline::new(get_mainnet_rpc_url(), Some(get_mainnet_chain_id()), None)
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
    let mut simulator = init_mainnet_simulator_online().await;
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
