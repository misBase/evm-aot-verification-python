theory EVM_types
  imports
    Main
    EVMCommType
    WordOld
    EVM_syntax
begin

(* Data structures for EVM execution *)
record call_env = 
  callenv_gaslimit :: "w256"
  callenv_value :: "w256"
  callenv_data :: "byte list"
  callenv_caller :: "address"
  callenv_timestamp :: "w256"
  callenv_blocknum :: "w256"
  callenv_balance :: "address \<Rightarrow> w256"

record return_result = 
  return_data :: "byte list"
  return_balance :: "address \<Rightarrow> w256"

datatype environment_action =
  EnvironmentCall "call_env"
| EnvironmentRet "return_result"
| EnvironmentFail

record call_arguments = 
  callarg_gas :: "w256"
  callarg_code :: "address"
  callarg_recipient :: "address"
  callarg_value :: "w256"
  callarg_data :: "byte list"
  callarg_output_begin :: "w256"
  callarg_output_size :: "w256"

record create_arguments = 
  createarg_value :: "w256"
  createarg_code :: "byte list"

record create2_arguments = 
  create2arg_value :: "w256"
  create2arg_salt :: "w256"
  create2arg_code_hash :: "w256"

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
  block_blockhash :: "w256 \<Rightarrow> w256" 
  block_coinbase :: "address" 
  block_timestamp :: "w256" 
  block_number :: "w256" 
  block_difficulty :: "w256" 
  block_gaslimit :: "w256" 
  block_basefee :: "w256"
  block_blobbasefee :: "w256"
  block_prevrandao :: "w256"

record log_entry = 
  log_addr   :: "address" 
  log_topics :: "w256 list" 
  log_data   :: "byte list" 

(* Data structures for function return values *)
datatype calculation_result = 
  CalculationSuccess "int"
  | CalcFailureReason "failure_reason"

datatype check_resources_result =
  CheckSuccess "bool"
  | CheckFailureReason "failure_reason"


end
