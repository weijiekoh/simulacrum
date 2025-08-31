use alloy::primitives::address;
use revm::primitives::U256;
use crate::tests::{
    init_mainnet_simulator_online,
    ETH_1,
    ETH_10,
    GWEI_20
};

#[tokio::test(flavor = "multi_thread")]
pub async fn test_transfer_eth() {
    let mut simulator = init_mainnet_simulator_online().await;

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
