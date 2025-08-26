# REVM Transaction Tracing Guide

## Using REVM's Inspector for Transaction Tracing

REVM provides a powerful `Inspector` trait that allows you to trace transaction execution and capture all touched addresses and storage slots. Here's how to implement it:

### 1. Create a Custom Inspector

```rust
use revm::{Inspector, CallInputs, CreateInputs, Log};
use alloy::primitives::{Address, U256};
use std::collections::{HashMap, HashSet};

#[derive(Default, Debug)]
struct AccessTracer {
    // Track all addresses that were called or created
    touched_addresses: HashSet<Address>,
    
    // Track storage slots accessed per address
    storage_accesses: HashMap<Address, HashSet<U256>>,
    
    // Track call stack for context
    call_stack: Vec<Address>,
    
    // Track logs emitted
    logs: Vec<Log>,
}

impl<CTX, INTR: InterpreterTypes> Inspector<CTX, INTR> for AccessTracer {
    // Called before each opcode execution
    fn step(&mut self, interp: &mut Interpreter<INTR>, context: &mut CTX) {
        let opcode = interp.bytecode.opcode();
        let current_address = interp.contract_address();
        
        self.touched_addresses.insert(current_address);
        
        // Track storage access opcodes
        match opcode {
            0x54 => { // SLOAD
                if let Ok(key) = interp.stack.peek(0) {
                    self.storage_accesses
                        .entry(current_address)
                        .or_default()
                        .insert(key);
                }
            }
            0x55 => { // SSTORE
                if let Ok(key) = interp.stack.peek(0) {
                    self.storage_accesses
                        .entry(current_address)
                        .or_default()
                        .insert(key);
                }
            }
            _ => {}
        }
    }
    
    // Called when a contract call is made
    fn call(&mut self, context: &mut CTX, inputs: &mut CallInputs) -> Option<CallOutcome> {
        // Track the target address being called
        self.touched_addresses.insert(inputs.target_address);
        self.call_stack.push(inputs.target_address);
        
        println!("CALL to: {:?}", inputs.target_address);
        println!("Value: {}", inputs.call_value);
        println!("Input data length: {}", inputs.input.len());
        
        None // Don't override the call
    }
    
    fn call_end(&mut self, context: &mut CTX, inputs: &CallInputs, outcome: &mut CallOutcome) {
        self.call_stack.pop();
    }
    
    // Called when a contract is created
    fn create(&mut self, context: &mut CTX, inputs: &mut CreateInputs) -> Option<CreateOutcome> {
        println!("CREATE with value: {}", inputs.value);
        println!("Init code length: {}", inputs.init_code.len());
        
        None // Don't override the creation
    }
    
    fn create_end(&mut self, context: &mut CTX, inputs: &CreateInputs, outcome: &mut CreateOutcome) {
        if let Some(address) = outcome.address {
            self.touched_addresses.insert(address);
            println!("Contract created at: {:?}", address);
        }
    }
    
    // Called when a log is emitted
    fn log(&mut self, interp: &mut Interpreter<INTR>, context: &mut CTX, log: Log) {
        self.touched_addresses.insert(log.address);
        self.logs.push(log.clone());
        
        println!("LOG emitted from: {:?}", log.address);
        println!("Topics: {:?}", log.topics());
    }
    
    // Called when a contract self-destructs
    fn selfdestruct(&mut self, contract: Address, target: Address, value: U256) {
        self.touched_addresses.insert(contract);
        self.touched_addresses.insert(target);
        
        println!("SELFDESTRUCT: {} -> {} (value: {})", contract, target, value);
    }
}
```

### 2. Use the Inspector with REVM

```rust
use revm::{Context, Evm};

// Create your custom tracer
let tracer = AccessTracer::default();

// Build EVM with inspector
let mut evm = Context::mainnet()
    .with_db(database)
    .build_mainnet()
    .with_inspector(tracer);

// Execute transaction with tracing
let result = evm.inspect_tx(transaction)?;

// Access traced data
println!("Touched addresses: {:?}", evm.inspector.touched_addresses);
println!("Storage accesses: {:?}", evm.inspector.storage_accesses);
println!("Logs emitted: {}", evm.inspector.logs.len());
```

### 3. Enhanced Storage Slot Tracking

For more detailed storage slot tracking, you can enhance the inspector to capture both reads and writes:

```rust
#[derive(Default, Debug)]
struct DetailedAccessTracer {
    touched_addresses: HashSet<Address>,
    storage_reads: HashMap<Address, HashMap<U256, U256>>,  // address -> slot -> value
    storage_writes: HashMap<Address, HashMap<U256, (U256, U256)>>, // address -> slot -> (old, new)
    call_trace: Vec<CallInfo>,
}

#[derive(Debug)]
struct CallInfo {
    from: Address,
    to: Address,
    value: U256,
    gas: u64,
    input_len: usize,
}

impl<CTX, INTR: InterpreterTypes> Inspector<CTX, INTR> for DetailedAccessTracer {
    fn step(&mut self, interp: &mut Interpreter<INTR>, context: &mut CTX) {
        let opcode = interp.bytecode.opcode();
        let address = interp.contract_address();
        
        self.touched_addresses.insert(address);
        
        match opcode {
            0x54 => { // SLOAD
                if let (Ok(key), Ok(value)) = (interp.stack.peek(0), context.sload(address, key)) {
                    self.storage_reads
                        .entry(address)
                        .or_default()
                        .insert(key, value);
                }
            }
            0x55 => { // SSTORE  
                if let (Ok(key), Ok(new_value)) = (interp.stack.peek(0), interp.stack.peek(1)) {
                    // Get current value before write
                    let old_value = context.sload(address, key).unwrap_or_default();
                    
                    self.storage_writes
                        .entry(address)
                        .or_default()
                        .insert(key, (old_value, new_value));
                }
            }
            _ => {}
        }
    }
    
    fn call(&mut self, context: &mut CTX, inputs: &mut CallInputs) -> Option<CallOutcome> {
        self.touched_addresses.insert(inputs.caller);
        self.touched_addresses.insert(inputs.target_address);
        
        self.call_trace.push(CallInfo {
            from: inputs.caller,
            to: inputs.target_address,
            value: inputs.call_value,
            gas: inputs.gas_limit,
            input_len: inputs.input.len(),
        });
        
        None
    }
}
```

### 4. Integration Example

Here's how to integrate this into your existing EVMSimulator:

```rust
impl EVMSimulator {
    pub fn trace_transaction(
        &mut self, 
        tx: TxEnv
    ) -> Result<(ExecutionResult, AccessTracer), EVMError<DBTransportError>> {
        let tracer = AccessTracer::default();
        
        let mut evm = Context::mainnet()
            .with_db(&mut self.db)
            .build_mainnet()
            .with_inspector(tracer);
            
        // Set transaction parameters
        evm.ctx.tx = tx;
        
        let result = evm.inspect_tx(evm.ctx.tx.clone())?;
        
        Ok((result, evm.inspector))
    }
}
```

### Key Benefits

1. **Complete Access Tracking**: Captures all addresses touched through calls, creates, and storage access
2. **Storage Slot Monitoring**: Tracks both reads and writes to storage slots
3. **Call Stack Tracing**: Maintains context of nested calls
4. **Event Capture**: Records all emitted logs and events
5. **Minimal Overhead**: Inspector callbacks have very low performance impact

This approach gives you complete visibility into transaction execution, making it perfect for building debuggers, analyzers, or compliance tools that need to know exactly which addresses and storage slots a transaction interacts with.