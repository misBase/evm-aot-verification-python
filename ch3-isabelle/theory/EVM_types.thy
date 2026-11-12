theory EVM_types
  imports
    Main
    EVMCommType
    WordOld
    EVM_syntax
    uint256
begin

(* Data structures for EVM execution *)
record call_env = 
  callenv_gaslimit :: "uint256"
  callenv_value :: "uint256"
  callenv_data :: "byte list"
  callenv_caller :: "address"
  callenv_timestamp :: "uint256"
  callenv_blocknum :: "uint256"
  callenv_balance :: "address \<Rightarrow> uint256"

record return_result = 
  return_data :: "byte list"
  return_balance :: "address \<Rightarrow> uint256"

datatype environment_action =
  EnvironmentCall "call_env"
| EnvironmentRet "return_result"
| EnvironmentFail

record call_arguments = 
  callarg_gas :: "uint256"
  callarg_code :: "address"
  callarg_recipient :: "address"
  callarg_value :: "uint256"
  callarg_data :: "byte list"
  callarg_output_begin :: "uint256"
  callarg_output_size :: "uint256"

record create_arguments = 
  createarg_value :: "uint256"
  createarg_code :: "byte list"

record create2_arguments = 
  create2arg_value :: "uint256"
  create2arg_salt :: "uint256"
  create2arg_code_hash :: "uint256"

datatype failure_reason =
  OutOfGas | TooLongStack | TooShortStack | InvalidJumpDestination | ShouldNotHappen |
  CodeStoreOutOfGas | DepthExceeded | InsufficientBalance | ContractAddressCollision |
  ExecutionReverted | MaxCodeSizeExceeded | MaxInitCodeSizeExceeded | WriteProtection |
  ReturnDataOutOfBounds | GasUintOverflow | InvalidCode | NonceUintOverflow | InvalidOpcode

datatype contract_action =
  ContractCall "call_arguments"
| ContractDelegateCall "call_arguments"
| ContractStaticCall "call_arguments"
| ContractCreate "create_arguments"
| ContractCreate2 "create2_arguments"
| ContractFail "failure_reason list"
| ContractSuicide "address"
| ContractReturn "byte list"

record block_info = 
  block_blockhash :: "uint256 \<Rightarrow> uint256" 
  block_coinbase :: "address" 
  block_timestamp :: "uint256" 
  block_number :: "uint256" 
  block_difficulty :: "uint256" 
  block_gaslimit :: "uint256" 
  block_basefee :: "uint256"
  block_blobbasefee :: "uint256"

record log_entry = 
  log_addr   :: "address" 
  log_topics :: "uint256 list" 
  log_data   :: "byte list" 

(* Data structures for function return values *)
datatype calculation_result = 
  CalculationSuccess "int"
  | CalcFailureReason "failure_reason"

datatype check_resources_result =
  CheckSuccess "bool"
  | CheckFailureReason "failure_reason"


end
