use alloy::primitives::{Address, U256};
use alloy::sol;
use alloy::sol_types::SolCall;
use anyhow::{anyhow, Result};
use revm::database::{DatabaseRef, DBTransportError};
use revm_context::result::{EVMError, ExecutionResult};
use revm_inspectors::tracing::CallTraceArena;

use crate::simulator::EVMSimulator;

// Solidity interface definition for ERC20
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

/// Trait for ERC20 token operations
#[allow(async_fn_in_trait)]
pub trait ERC20Operations {
    /// Query the balance of an account for a specific ERC20 token
    async fn erc20_balance_of(
        &mut self,
        token_address: Address,
        account: Address,
    ) -> Result<(U256, CallTraceArena)>;

    /// Approve a spender to spend tokens on behalf of the caller
    async fn erc20_approve(
        &mut self,
        token_address: Address,
        caller: Address,
        spender: Address,
        amount: U256,
        nonce: Option<u64>,
        gas_limit: u64,
        gas_price: u128,
        do_commit: bool,
    ) -> Result<(ExecutionResult, CallTraceArena), EVMError<DBTransportError>>;

    /// Query the allowance between owner and spender for a specific ERC20 token
    async fn erc20_allowance(
        &mut self,
        token_address: Address,
        owner: Address,
        spender: Address,
    ) -> Result<(U256, CallTraceArena)>;

    /// Query the total supply of an ERC20 token
    async fn erc20_total_supply(
        &mut self,
        token_address: Address,
    ) -> Result<(U256, CallTraceArena)>;

    /// Query the decimals of an ERC20 token
    async fn erc20_decimals(&mut self, token_address: Address) -> Result<(u8, CallTraceArena)>;

    /// Query the name of an ERC20 token
    async fn erc20_name(&mut self, token_address: Address) -> Result<(String, CallTraceArena)>;

    /// Query the symbol of an ERC20 token
    async fn erc20_symbol(&mut self, token_address: Address) -> Result<(String, CallTraceArena)>;

    /// Transfer tokens from the caller to another address
    async fn erc20_transfer(
        &mut self,
        token_address: Address,
        from: Address,
        to: Address,
        amount: U256,
        nonce: Option<u64>,
        gas_limit: u64,
        gas_price: u128,
        do_commit: bool,
    ) -> Result<(ExecutionResult, CallTraceArena), EVMError<DBTransportError>>;

    /// Transfer tokens from one address to another using allowance
    async fn erc20_transfer_from(
        &mut self,
        token_address: Address,
        caller: Address,
        from: Address,
        to: Address,
        amount: U256,
        nonce: Option<u64>,
        gas_limit: u64,
        gas_price: u128,
        do_commit: bool,
    ) -> Result<(ExecutionResult, CallTraceArena), EVMError<DBTransportError>>;
}

/// Implementation of ERC20Operations for EVMSimulator
impl<ExtDB: DatabaseRef> ERC20Operations for EVMSimulator<ExtDB> {
    async fn erc20_balance_of(
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

    async fn erc20_approve(
        &mut self,
        token_address: Address,
        caller: Address,
        spender: Address,
        amount: U256,
        nonce: Option<u64>,
        gas_limit: u64,
        gas_price: u128,
        do_commit: bool,
    ) -> Result<(ExecutionResult, CallTraceArena), EVMError<DBTransportError>> {
        // Encode the approve function call
        let approve_call = IERC20::approveCall { spender, amount };
        let call_data = approve_call.abi_encode();

        self.contract_execute_optional_commit(
            token_address,
            call_data,
            caller,
            nonce,
            gas_limit,
            gas_price,
            do_commit,
        )
        .await
    }

    async fn erc20_allowance(
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

    async fn erc20_total_supply(
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

    async fn erc20_decimals(&mut self, token_address: Address) -> Result<(u8, CallTraceArena)> {
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

    async fn erc20_name(&mut self, token_address: Address) -> Result<(String, CallTraceArena)> {
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

    async fn erc20_symbol(&mut self, token_address: Address) -> Result<(String, CallTraceArena)> {
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

    async fn erc20_transfer(
        &mut self,
        token_address: Address,
        from: Address,
        to: Address,
        amount: U256,
        nonce: Option<u64>,
        gas_limit: u64,
        gas_price: u128,
        do_commit: bool,
    ) -> Result<(ExecutionResult, CallTraceArena), EVMError<DBTransportError>> {
        // Encode the transfer function call
        let transfer_call = IERC20::transferCall { to, amount };
        let call_data = transfer_call.abi_encode();

        self.contract_execute_optional_commit(token_address, call_data, from, nonce, gas_limit, gas_price, do_commit)
            .await
    }

    async fn erc20_transfer_from(
        &mut self,
        token_address: Address,
        caller: Address,
        from: Address,
        to: Address,
        amount: U256,
        nonce: Option<u64>,
        gas_limit: u64,
        gas_price: u128,
        do_commit: bool,
    ) -> Result<(ExecutionResult, CallTraceArena), EVMError<DBTransportError>> {
        // Encode the transferFrom function call
        let transfer_from_call = IERC20::transferFromCall { from, to, amount };
        let call_data = transfer_from_call.abi_encode();

        self.contract_execute_optional_commit(
            token_address,
            call_data,
            caller,
            nonce,
            gas_limit,
            gas_price,
            do_commit,
        )
        .await
    }
}
