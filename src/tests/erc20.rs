use alloy::primitives::address;
use alloy::primitives::U256;
use crate::erc20::ERC20Operations;
use crate::tests::{
    init_mainnet_simulator_online,
    ETH_1,
    GWEI_20,
    GAS_ERC20_APPROVE,
    GAS_ERC20_TRANSFER,
    USDC_100,
    USDC_200,
    USDC_500,
    USDC_1500,
    USDC_ADDRESS,
};

#[tokio::test(flavor = "multi_thread")]
pub async fn test_erc20_balance_query_usdc() {
    let mut simulator = init_mainnet_simulator_online().await;

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
    let mut simulator = init_mainnet_simulator_online().await;

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
            true,
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
            true,
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
    let mut simulator = init_mainnet_simulator_online().await;

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
    let mut simulator = init_mainnet_simulator_online().await;

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
    let mut simulator = init_mainnet_simulator_online().await;

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
            true,
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
    let mut simulator = init_mainnet_simulator_online().await;

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
            true,
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
            true,
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

