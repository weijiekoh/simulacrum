use revm::Context;
use revm::context::{BlockEnv, CfgEnv, TxEnv};
use revm::interpreter::interpreter_types::Jumps;
use revm::interpreter::interpreter_types::StackTr;
use revm::interpreter::{
    CallInputs, CallOutcome, CreateInputs, CreateOutcome, Interpreter, InterpreterTypes,
};
use revm::{
    Inspector,
    primitives::{Address, Log, U256},
};
use std::collections::{HashMap, HashSet};

#[derive(Default, Debug)]
pub struct AccessTracer {
    // Track storage slots accessed per address
    pub storage_accesses: HashMap<Address, HashSet<U256>>,
    pub account_accesses: HashSet<Address>,

    // The address of the contract currently being called or executed
    current_target: Option<Address>,
}

// Implementation for any context that implements the Context trait
impl AccessTracer {
    // Helper function to track storage access for a given address and key
    fn track_storage_access(&mut self, addr: Address, key: U256) {
        self.storage_accesses
            .entry(addr)
            .or_insert_with(HashSet::new)
            .insert(key);
    }
}

impl<DB, INTR: InterpreterTypes> Inspector<Context<BlockEnv, TxEnv, CfgEnv, DB>, INTR>
    for AccessTracer
where
    DB: revm::Database + std::fmt::Debug,
{
    // Called when a contract call is made
    fn call(
        &mut self,
        _context: &mut Context<BlockEnv, TxEnv, CfgEnv, DB>,
        inputs: &mut CallInputs,
    ) -> Option<CallOutcome> {
        self.current_target = Some(inputs.target_address);
        self.account_accesses.insert(inputs.target_address);
        None // Don't override the call
    }

    // Called before each opcode execution
    fn step(
        &mut self,
        interp: &mut Interpreter<INTR>,
        _context: &mut Context<BlockEnv, TxEnv, CfgEnv, DB>,
    ) {
        assert!(
            self.current_target.is_some(),
            "Current target address should be set during a call"
        );

        let addr = self.current_target.unwrap();

        let opcode = interp.bytecode.opcode();

        match opcode {
            0x31 => {
                // BALANCE
                self.account_accesses.insert(addr);
            }
            0x47 => {
                // SELFBALANCE
                self.account_accesses.insert(addr);
            }
            0x54 => {
                // SLOAD
                let key = *interp.stack.top().unwrap();
                self.track_storage_access(addr, key);
            }
            0x55 => {
                // SSTORE
                let key = *interp.stack.top().unwrap();
                self.track_storage_access(addr, key);
            }
            _ => {}
        }
    }

    fn call_end(
        &mut self,
        _context: &mut Context<BlockEnv, TxEnv, CfgEnv, DB>,
        _inputs: &CallInputs,
        _outcome: &mut CallOutcome,
    ) {
    }

    // Called when a contract is created
    fn create(
        &mut self,
        _context: &mut Context<BlockEnv, TxEnv, CfgEnv, DB>,
        _inputs: &mut CreateInputs,
    ) -> Option<CreateOutcome> {
        None // Don't override the creation
    }

    fn create_end(
        &mut self,
        _context: &mut Context<BlockEnv, TxEnv, CfgEnv, DB>,
        _inputs: &CreateInputs,
        _outcome: &mut CreateOutcome,
    ) {
    }

    // Called when a log is emitted
    fn log(
        &mut self,
        _interp: &mut Interpreter<INTR>,
        _context: &mut Context<BlockEnv, TxEnv, CfgEnv, DB>,
        _log: Log,
    ) {
    }

    // Called when a contract self-destructs
    fn selfdestruct(&mut self, _contract: Address, _target: Address, _value: U256) {}
}
