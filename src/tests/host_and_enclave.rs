use alloy::primitives::address;

use crate::simulator::{extract_accesses_from_traces, EVMSimulatorOffline};
use crate::erc20::ERC20Operations;
use crate::tests::{
    init_mainnet_simulator_online,
    GWEI_20,
    GAS_ERC20_TRANSFER,
    USDC_100,
    USDC_ADDRESS,
};

#[tokio::test(flavor = "multi_thread")]
pub async fn test_host_and_enclave_flow() {
    // Set up accounts - sender has real USDC balance, receiver is random
    let sender = address!("0x37305B1cD40574E4C5Ce33f8e8306Be057fD7341"); // Real account with USDC
    let receiver = address!("0x1234567890123456789012345678901234567890"); // Random receiver
    let transfer_amount = USDC_100; // 100 USDC transfer

    // Host: create initial simulator
    let mut host_simulator = init_mainnet_simulator_online().await;

    // Host: warm pre-tx state without committing
    let (host_pre_res, host_traces) = host_simulator
        .erc20_transfer(
            USDC_ADDRESS,
            sender,
            receiver,
            transfer_amount,
            None,
            GAS_ERC20_TRANSFER,
            GWEI_20,
            false,
        )
        .await
        .expect("warmup failed");

    let snapshot = host_simulator.to_snapshot();

    // Enclave: recreate simulator from snapshot
    let mut enclave = EVMSimulatorOffline::from_snapshot(snapshot).await.unwrap();

    // Re-run the same tx offline (still no commit needed for trace equality)
    let (enc_res, enc_traces) = enclave
        .erc20_transfer(
            USDC_ADDRESS,
            sender,
            receiver,
            transfer_amount,
            None,
            GAS_ERC20_TRANSFER,
            GWEI_20,
            false,
        )
        .await
        .expect("enclave offline run failed");

    assert_eq!(host_pre_res, enc_res);
    assert_eq!(host_traces, enc_traces);

    // Get the accounts accessed during the transaction. These include:
    // - balance accesses
    // - storage accesses
    // For each balance access, we need an account proof.
    // For each storage access, we need an account proof and a storage proof.
    let (accounts, balance_accesses, storage_accesses) =
        extract_accesses_from_traces(&host_traces);

    let mut accounts_to_get_proofs = vec![];
    for account in &accounts {
        accounts_to_get_proofs.push(*account);
    }
    for account in &balance_accesses {
        accounts_to_get_proofs.push(*account);
    }
    for (account, _) in &storage_accesses {
        accounts_to_get_proofs.push(*account);
    }

    let account_proofs = host_simulator.get_account_proofs(&accounts_to_get_proofs).await;

    let storage_proofs = host_simulator
        .get_storage_proofs(&storage_accesses)
        .await;

    // Enclave: verify each account proof
    for (account_address, account_proof) in &account_proofs {
        assert!(
            !account_proof.is_empty(),
            "Account proof should not be empty for address: {:?}",
            account_address
        );

        // Verify the account proof cryptographically
        let verification_result = enclave.verify_account_proof(account_proof);

        assert!(
            verification_result.is_ok(),
            "Account proof verification should not error for address: {:?}",
            account_address
        );
    }

    // Enclave: verify each storage proof
    for (address, storage_proof) in &storage_proofs {
        // Verify the storage proof structure exists and is valid
        assert!(
            !storage_proof.is_empty(),
            "Empty storage proof for address: {:?}",
            address
        );

        // Verify the storage proof cryptographically
        let verification_result = enclave.verify_storage_proof(storage_proof);

        assert!(verification_result.is_ok(), "Invalid storage proof {:?}", storage_proof);
    }
}
