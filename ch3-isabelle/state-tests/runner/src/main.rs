use std::env;
use std::rc::Rc;
use num_bigint::BigInt;
use isabelle_exported::EVM_Execute::{
    self, Bit0, Bit1, ConstantCtxExt, ContractAction, FailureReason, InstructionResult, List,
    Network, Num1, ProgramExt, Unit, VariableCtxExt, Word,
};

type U8 = Word<Bit0<Bit0<Bit0<Num1>>>>;
type U160 = Word<Bit0<Bit0<Bit0<Bit0<Bit0<Bit1<Bit0<Num1>>>>>>>>;
type U256 = Word<Bit0<Bit0<Bit0<Bit0<Bit0<Bit0<Bit0<Bit0<Num1>>>>>>>>>;

#[derive(Clone)]
struct BlockConfig {
    coinbase: BigInt,
    timestamp: BigInt,
    number: BigInt,
    difficulty: BigInt,
    gaslimit: BigInt,
    basefee: BigInt,
    blobbasefee: BigInt,
    prevrandao: BigInt,
}

impl Default for BlockConfig {
    fn default() -> Self {
        Self {
            coinbase: BigInt::from(0u64),
            timestamp: BigInt::from(0u64),
            number: BigInt::from(0u64),
            difficulty: BigInt::from(0u64),
            gaslimit: BigInt::from(0u64),
            basefee: BigInt::from(0u64),
            blobbasefee: BigInt::from(0u64),
            prevrandao: BigInt::from(0u64),
        }
    }
}

#[derive(Clone)]
struct RunConfig {
    code_hex: String,
    address: BigInt,
    gas: BigInt,
    data_hex: String,
    value: BigInt,
    caller: BigInt,
    origin: BigInt,
    gasprice: BigInt,
    chainid: BigInt,
    network: Network,
    storage: Vec<(BigInt, BigInt)>,
    balances: Vec<(BigInt, BigInt)>,
    nonces: Vec<(BigInt, BigInt)>,
    account_codes: Vec<(BigInt, String)>,
    warm_storage: Vec<BigInt>,
    access_list_addresses: Vec<BigInt>,
    blob_hashes: Vec<BigInt>,
    block: BlockConfig,
    storage_checks: Vec<(BigInt, BigInt)>,
    balance_checks: Vec<(BigInt, BigInt)>,
    nonce_checks: Vec<(BigInt, BigInt)>,
}

impl Default for RunConfig {
    fn default() -> Self {
        Self {
            code_hex: String::new(),
            address: BigInt::from(0u64),
            gas: BigInt::from(100_000u64),
            data_hex: "0x".to_string(),
            value: BigInt::from(0u64),
            caller: BigInt::from(0u64),
            origin: BigInt::from(0u64),
            gasprice: BigInt::from(0u64),
            chainid: BigInt::from(0u64),
            network: Network::Cancun,
            storage: Vec::new(),
            balances: Vec::new(),
            nonces: Vec::new(),
            account_codes: Vec::new(),
            warm_storage: Vec::new(),
            access_list_addresses: Vec::new(),
            blob_hashes: Vec::new(),
            block: BlockConfig::default(),
            storage_checks: Vec::new(),
            balance_checks: Vec::new(),
            nonce_checks: Vec::new(),
        }
    }
}

fn strip_0x(text: &str) -> &str {
    text.strip_prefix("0x").unwrap_or(text)
}

fn parse_hex_bigint(text: &str) -> BigInt {
    let hex = strip_0x(text);
    if hex.is_empty() {
        BigInt::from(0u64)
    } else {
        BigInt::parse_bytes(hex.as_bytes(), 16).expect("invalid hex integer")
    }
}

fn parse_bigint_value(text: &str) -> BigInt {
    if let Some(hex) = text.strip_prefix("0x") {
        if hex.is_empty() {
            BigInt::from(0u64)
        } else {
            BigInt::parse_bytes(hex.as_bytes(), 16).expect("invalid hex integer")
        }
    } else {
        BigInt::from(text.parse::<u64>().expect("invalid decimal integer"))
    }
}

fn parse_pair(text: &str) -> (BigInt, BigInt) {
    let (left, right) = text.split_once('=').expect("expected key=value");
    (parse_bigint_value(left), parse_bigint_value(right))
}

fn parse_address_pair(text: &str) -> (BigInt, BigInt) {
    let (left, right) = text.split_once('=').expect("expected address=value");
    (parse_hex_bigint(left), parse_bigint_value(right))
}

fn parse_code_pair(text: &str) -> (BigInt, String) {
    let (left, right) = text.split_once('=').expect("expected address=code");
    (parse_hex_bigint(left), right.to_string())
}

fn u256(value: &BigInt) -> U256 {
    EVM_Execute::of_int::<Bit0<Bit0<Bit0<Bit0<Bit0<Bit0<Bit0<Bit0<Num1>>>>>>>>>(value.clone())
}

fn u160(value: &BigInt) -> U160 {
    EVM_Execute::of_int::<Bit0<Bit0<Bit0<Bit0<Bit0<Bit1<Bit0<Num1>>>>>>>>(value.clone())
}

fn u8_word(value: u8) -> U8 {
    EVM_Execute::of_int::<Bit0<Bit0<Bit0<Num1>>>>(BigInt::from(value))
}

fn hex_pad(value: &BigInt, bytes: usize) -> String {
    let mut hex = value.to_str_radix(16);
    if hex.len() % 2 != 0 {
        hex.insert(0, '0');
    }
    format!("{hex:0>width$}", width = bytes * 2)
}

fn address_hex(addr: U160) -> String {
    hex_pad(&EVM_Execute::the_int(addr), 20)
}

fn bytes_to_list(bytes: &[u8]) -> List<U8> {
    let mut tail: List<U8> = List::Nil;
    for byte in bytes.iter().rev() {
        tail = List::Cons(u8_word(*byte), Box::new(tail));
    }
    tail
}

fn parse_hex_bytes(text: &str) -> Vec<u8> {
    let hex = strip_0x(text);
    if hex.is_empty() {
        return Vec::new();
    }
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).expect("invalid hex byte"))
        .collect()
}

fn char_of_byte(byte: u8) -> EVM_Execute::Char {
    let mut bits = [false; 8];
    for i in 0..8 {
        bits[i] = (byte & (1u8 << i)) != 0;
    }
    EVM_Execute::Char::Char(
        bits[0], bits[1], bits[2], bits[3], bits[4], bits[5], bits[6], bits[7],
    )
}

fn char_list_from_hex(text: &str) -> List<EVM_Execute::Char> {
    let hex = strip_0x(text);
    let mut tail: List<EVM_Execute::Char> = List::Nil;
    for byte in hex.as_bytes().iter().rev() {
        tail = List::Cons(char_of_byte(*byte), Box::new(tail));
    }
    tail
}

fn byte_list_hex(data: &List<U8>) -> String {
    let mut bytes = Vec::new();
    let mut cur = data;
    loop {
        match cur {
            List::Nil => break,
            List::Cons(head, tail) => {
                let value = EVM_Execute::the_int((*head).clone());
                let (_, be_bytes) = value.to_bytes_be();
                bytes.push(if be_bytes.is_empty() {
                    0
                } else {
                    be_bytes[be_bytes.len() - 1]
                });
                cur = tail.as_ref();
            }
        }
    }
    bytes.iter().map(|b| format!("{b:02x}")).collect::<String>()
}

fn list_len<A>(xs: &List<A>) -> usize {
    match xs {
        List::Nil => 0,
        List::Cons(_, tail) => 1 + list_len(tail),
    }
}

fn program_from_code(code_hex: &str) -> ProgramExt<Unit> {
    let byte_list = bytes_to_list(&parse_hex_bytes(code_hex));
    let insts = EVM_Execute::parse_bytes(byte_list.clone());
    let tree = EVM_Execute::program_avl_of_lst(BigInt::from(0u64), insts.clone());
    let program = EVM_Execute::program_of_lst(
        &insts,
        Rc::new(move |_, pc| EVM_Execute::lookup(tree.clone(), &pc)),
    );
    EVM_Execute::program_byte_content_update(
        Rc::new(move |_: List<U8>| byte_list.clone()) as Rc<dyn Fn(List<U8>) -> List<U8>>,
        program,
    )
}

fn network_from_name(name: &str) -> Network {
    match name {
        "Frontier" => Network::Frontier,
        "Homestead" => Network::Homestead,
        "EIP150" => Network::EIP150,
        "EIP158" => Network::EIP158,
        "Metropolis" => Network::Metropolis,
        "Byzantium" => Network::Byzantium,
        "Constantinople" => Network::Constantinople,
        "Petersburg" => Network::Petersburg,
        "Istanbul" => Network::Istanbul,
        "Berlin" => Network::Berlin,
        "London" => Network::London,
        "Paris" => Network::Paris,
        "Shanghai" => Network::Shanghai,
        "Prague" => Network::Cancun,
        _ => Network::Cancun,
    }
}

fn build_context(config: &RunConfig) -> VariableCtxExt<Unit> {
    let storage_map = config.storage.clone();
    let storage: Rc<dyn Fn(U256) -> U256> = Rc::new(move |key| {
        let key_int = EVM_Execute::the_int(key);
        let value = storage_map
            .iter()
            .find(|(candidate, _)| candidate == &key_int)
            .map(|(_, value)| (*value).clone())
            .unwrap_or_else(|| BigInt::from(0u64));
        u256(&value)
    });

    let balance_map = config.balances.clone();
    let balance: Rc<dyn Fn(U160) -> U256> = Rc::new(move |addr| {
        let addr_int = EVM_Execute::the_int(addr);
        let value = balance_map
            .iter()
            .find(|(candidate, _)| candidate == &addr_int)
            .map(|(_, value)| (*value).clone())
            .unwrap_or_else(|| BigInt::from(0u64));
        u256(&value)
    });

    let memory: Rc<dyn Fn(U256) -> U8> = Rc::new(move |_| u8_word(0u8));

    let codes = config.account_codes.clone();
    let ext_program: Rc<dyn Fn(U160) -> ProgramExt<Unit>> = Rc::new(move |addr| {
        let addr_int = EVM_Execute::the_int(addr);
        if let Some((_, code)) = codes.iter().find(|(candidate, _)| candidate == &addr_int) {
            program_from_code(code)
        } else {
            EVM_Execute::empty_program()
        }
    });

    let blockhash: Rc<dyn Fn(U256) -> U256> =
        Rc::new(move |_| u256(&BigInt::from(0u64)));
    let block = EVM_Execute::BlockInfoExt::BlockInfoExt(
        blockhash,
        u160(&config.block.coinbase),
        u256(&config.block.timestamp),
        u256(&config.block.number),
        u256(&config.block.difficulty),
        u256(&config.block.gaslimit),
        u256(&config.block.basefee),
        u256(&config.block.blobbasefee),
        u256(&config.block.prevrandao),
        Unit::Unity,
    );

    let existing_accounts = config.account_codes.clone();
    let account_existence: Rc<dyn Fn(U160) -> bool> = Rc::new(move |addr| {
        let addr_int = EVM_Execute::the_int(addr);
        existing_accounts.iter().any(|(candidate, _)| candidate == &addr_int)
    });

    let mut touched: List<U256> = List::Nil;
    for key in config.warm_storage.iter().rev() {
        touched = List::Cons(u256(key), Box::new(touched));
    }

    let mut warm_unique = vec![
        config.caller.clone(),
        config.address.clone(),
        config.block.coinbase.clone(),
    ];
    for addr in config.access_list_addresses.iter() {
        if !warm_unique.contains(addr) {
            warm_unique.push(addr.clone());
        }
    }
    let mut warm_addresses: List<U160> = List::Nil;
    for addr in warm_unique.iter().rev() {
        warm_addresses = List::Cons(u160(addr), Box::new(warm_addresses));
    }

    let mut blob_hashes: List<U256> = List::Nil;
    for hash in config.blob_hashes.iter().rev() {
        blob_hashes = List::Cons(u256(hash), Box::new(blob_hashes));
    }

    let transient_storage: Rc<dyn Fn(U256) -> U256> =
        Rc::new(move |_| u256(&BigInt::from(0u64)));

    VariableCtxExt::VariableCtxExt(
        List::Nil,
        memory,
        BigInt::from(0u64),
        storage.clone(),
        BigInt::from(0u64),
        balance.clone(),
        u160(&config.caller),
        u256(&config.value),
        bytes_to_list(&parse_hex_bytes(&config.data_hex)),
        storage.clone(),
        balance,
        u160(&config.origin),
        ext_program,
        block,
        config.gas.clone(),
        account_existence,
        touched,
        warm_addresses,
        List::Nil,
        BigInt::from(0u64),
        u256(&config.gasprice),
        List::Nil,
        u256(&config.chainid),
        blob_hashes,
        transient_storage,
        false,
        Unit::Unity,
    )
}

fn build_constant_context(config: &RunConfig) -> ConstantCtxExt<Unit> {
    let hash_filter: Rc<dyn Fn(List<U8>) -> bool> = Rc::new(move |_| true);
    ConstantCtxExt::ConstantCtxExt(
        EVM_Execute::empty_program(),
        u160(&config.address),
        hash_filter,
        Unit::Unity,
    )
}

fn failure_reason_name(reason: &FailureReason) -> &'static str {
    match reason {
        FailureReason::OutOfGas => "OutOfGas",
        FailureReason::TooLongStack => "TooLongStack",
        FailureReason::TooShortStack => "TooShortStack",
        FailureReason::InvalidJumpDestination => "InvalidJumpDestination",
        FailureReason::ShouldNotHappen => "ShouldNotHappen",
        FailureReason::CodeStoreOutOfGas => "CodeStoreOutOfGas",
        FailureReason::DepthExceeded => "DepthExceeded",
        FailureReason::InsufficientBalance => "InsufficientBalance",
        FailureReason::ContractAddressCollision => "ContractAddressCollision",
        FailureReason::ExecutionReverted => "ExecutionReverted",
        FailureReason::MaxCodeSizeExceeded => "MaxCodeSizeExceeded",
        FailureReason::MaxInitCodeSizeExceeded => "MaxInitCodeSizeExceeded",
        FailureReason::WriteProtection => "WriteProtection",
        FailureReason::ReturnDataOutOfBounds => "ReturnDataOutOfBounds",
        FailureReason::GasUintOverflow => "GasUintOverflow",
        FailureReason::InvalidCode => "InvalidCode",
        FailureReason::NonceUintOverflow => "NonceUintOverflow",
        FailureReason::InvalidOpcode => "InvalidOpcode",
    }
}

fn print_failure_reasons(reasons: &List<FailureReason>) {
    let mut names = Vec::new();
    let mut cursor = reasons;
    loop {
        match cursor {
            List::Nil => break,
            List::Cons(reason, tail) => {
                names.push(failure_reason_name(reason));
                cursor = tail.as_ref();
            }
        }
    }
    println!("failure_reasons=[{}]", names.join(", "));
}

fn print_storage(ctx: &VariableCtxExt<Unit>, checks: &[(BigInt, BigInt)]) {
    let storage = EVM_Execute::vctx_storage(ctx);
    for (key, _) in checks {
        let actual = (*storage)(u256(key));
        println!("storage[{}]={}", key, EVM_Execute::the_int(actual));
    }
}

fn print_balance(ctx: &VariableCtxExt<Unit>, checks: &[(BigInt, BigInt)]) {
    let balance = EVM_Execute::vctx_balance(ctx);
    for (addr, _) in checks {
        let actual = (*balance)(u160(addr));
        println!(
            "balance[0x{}]={}",
            hex_pad(addr, 20),
            EVM_Execute::the_int(actual)
        );
    }
}

fn print_nonce(config: &RunConfig, checks: &[(BigInt, BigInt)]) {
    for (addr, _) in checks {
        let actual = config
            .nonces
            .iter()
            .find(|(candidate, _)| candidate == addr)
            .map(|(_, value)| (*value).clone())
            .unwrap_or_else(|| BigInt::from(0u64));
        println!("nonce[0x{}]={}", hex_pad(addr, 20), actual);
    }
}

fn print_logs(ctx: &VariableCtxExt<Unit>) {
    let logs = EVM_Execute::vctx_logs(ctx);
    println!("logs={}", list_len(&logs));
    let mut cursor = &logs;
    let mut index = 0usize;
    loop {
        match cursor {
            List::Nil => break,
            List::Cons(entry, tail) => {
                match entry {
                    EVM_Execute::LogEntryExt::LogEntryExt(addr, topics, data, _) => {
                        println!("log[{}] address=0x{}", index, address_hex((*addr).clone()));
                        println!("log[{}] topics={}", index, list_len(topics));
                        println!("log[{}] data=0x{}", index, byte_list_hex(data));
                    }
                }
                cursor = tail.as_ref();
                index += 1;
            }
        }
    }
}

fn print_state(ctx: &VariableCtxExt<Unit>, config: &RunConfig) {
    println!("gas={}", EVM_Execute::vctx_gas(ctx));
    println!("pc={}", EVM_Execute::vctx_pc(ctx));
    print_storage(ctx, &config.storage_checks);
    print_balance(ctx, &config.balance_checks);
    print_nonce(config, &config.nonce_checks);
    print_logs(ctx);
}

fn run(config: &RunConfig) -> i32 {
    let bytecode = char_list_from_hex(&config.code_hex);
    let variable_ctx = build_context(config);
    let constant_ctx = build_constant_context(config);
    let result = EVM_Execute::execute_evm_bytecode(
        bytecode,
        &variable_ctx,
        constant_ctx,
        config.network,
        config.gas.clone(),
    );

    match &result {
        InstructionResult::InstructionContinue(_) => {
            println!("result=InstructionContinue");
            println!("return_data=0x");
        }
        InstructionResult::InstructionToEnvironment(action, _, _) => match action {
            ContractAction::ContractReturn(data) => {
                println!("result=ContractReturn");
                println!("return_data=0x{}", byte_list_hex(data));
            }
            ContractAction::ContractFail(reasons) => {
                println!("result=ContractFail");
                println!("return_data=0x");
                print_failure_reasons(reasons);
            }
            ContractAction::ContractCall(_) => {
                println!("result=ContractCall");
                println!("return_data=0x");
            }
            ContractAction::ContractDelegateCall(_) => {
                println!("result=ContractDelegateCall");
                println!("return_data=0x");
            }
            ContractAction::ContractStaticCall(_) => {
                println!("result=ContractStaticCall");
                println!("return_data=0x");
            }
            ContractAction::ContractCreate(_) => {
                println!("result=ContractCreate");
                println!("return_data=0x");
            }
            ContractAction::ContractCreate2(_) => {
                println!("result=ContractCreate2");
                println!("return_data=0x");
            }
            ContractAction::ContractSuicide(_) => {
                println!("result=ContractSuicide");
                println!("return_data=0x");
            }
        },
    }

    // `execute_evm_bytecode` returns the in-progress context on failure; the
    // caller/transaction layer is what reverts it. At the top level an
    // exceptional halt therefore discards all state writes, so report the
    // pre-execution context for those results.
    let state_ctx = match &result {
        InstructionResult::InstructionToEnvironment(ContractAction::ContractFail(_), _, _) => {
            Some(&variable_ctx)
        }
        _ => result_context(&result),
    };
    if let Some(ctx) = state_ctx {
        print_state(ctx, config);
    }
    0
}

fn result_context(result: &InstructionResult) -> Option<&VariableCtxExt<Unit>> {
    match result {
        InstructionResult::InstructionContinue(ctx) => Some(ctx),
        InstructionResult::InstructionToEnvironment(_, ctx, _) => Some(ctx),
    }
}

fn parse_args() -> RunConfig {
    let mut config = RunConfig::default();
    let args: Vec<String> = env::args().skip(1).collect();
    let mut i = 0usize;
    while i < args.len() {
        match args[i].as_str() {
            "--code" => { i += 1; config.code_hex = args[i].clone(); }
            "--address" => { i += 1; config.address = parse_hex_bigint(&args[i]); }
            "--gas" => { i += 1; config.gas = parse_bigint_value(&args[i]); }
            "--fuel" => { i += 1; }
            "--data" => { i += 1; config.data_hex = args[i].clone(); }
            "--value" => { i += 1; config.value = parse_bigint_value(&args[i]); }
            "--caller" => { i += 1; config.caller = parse_hex_bigint(&args[i]); }
            "--origin" => { i += 1; config.origin = parse_hex_bigint(&args[i]); }
            "--gasprice" => { i += 1; config.gasprice = parse_bigint_value(&args[i]); }
            "--chainid" => { i += 1; config.chainid = parse_bigint_value(&args[i]); }
            "--network" => { i += 1; config.network = network_from_name(&args[i]); }
            "--storage" => { i += 1; config.storage.push(parse_pair(&args[i])); }
            "--balance" => { i += 1; config.balances.push(parse_address_pair(&args[i])); }
            "--nonce" => { i += 1; config.nonces.push(parse_address_pair(&args[i])); }
            "--account-code" => { i += 1; config.account_codes.push(parse_code_pair(&args[i])); }
            "--warm-storage" => { i += 1; config.warm_storage.push(parse_bigint_value(&args[i])); }
            "--access-list-address" => { i += 1; config.access_list_addresses.push(parse_hex_bigint(&args[i])); }
            "--block-coinbase" => { i += 1; config.block.coinbase = parse_hex_bigint(&args[i]); }
            "--block-timestamp" => { i += 1; config.block.timestamp = parse_bigint_value(&args[i]); }
            "--block-number" => { i += 1; config.block.number = parse_bigint_value(&args[i]); }
            "--block-difficulty" => { i += 1; config.block.difficulty = parse_bigint_value(&args[i]); }
            "--block-gaslimit" => { i += 1; config.block.gaslimit = parse_bigint_value(&args[i]); }
            "--block-basefee" => { i += 1; config.block.basefee = parse_bigint_value(&args[i]); }
            "--block-blobbasefee" => { i += 1; config.block.blobbasefee = parse_bigint_value(&args[i]); }
            "--block-random" => { i += 1; config.block.prevrandao = parse_bigint_value(&args[i]); }
            "--check-storage" => { i += 1; config.storage_checks.push(parse_pair(&args[i])); }
            "--check-balance" => { i += 1; config.balance_checks.push(parse_address_pair(&args[i])); }
            "--check-nonce" => { i += 1; config.nonce_checks.push(parse_address_pair(&args[i])); }
            "--priority-fee" => { i += 1; }
            "--blob-hash" => { i += 1; config.blob_hashes.push(parse_hex_bigint(&args[i])); }
            "--create-data" => { i += 1; }
            "--expect-out" => { i += 1; }
            "--expect-exception" => { i += 1; }
            "--create" => {}
            _ => {}
        }
        i += 1;
    }
    config
}

fn main() {
    let stack_size: usize = std::env::var("EVM_RUNNER_STACK_BYTES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1024 * 1024 * 1024);
    let code = std::thread::Builder::new()
        .stack_size(stack_size)
        .spawn(|| {
            let config = parse_args();
            run(&config)
        })
        .expect("failed to spawn runner thread")
        .join()
        .unwrap_or(1);
    std::process::exit(code);
}

