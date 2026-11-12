theory EVM_state
  imports
    Main
    EVMCommType
    uint256
begin

(*
record evm_stack =
 estk_content :: "u256 list"
 estk_size    :: nat *)

type_synonym memory = "uint256 \<Rightarrow> byte"
type_synonym storage = "uint256 \<Rightarrow> uint256"  \<comment> \<open>add "lastGasCost" ?   \<close>
type_synonym evm_stack = "uint256 list"

definition evm_pop :: "evm_stack \<Rightarrow> (uint256 \<times> evm_stack) option" where
"evm_pop stk = (
  case stk of
  [] \<Rightarrow> None |
  h#t \<Rightarrow> Some (h, t)
)"

definition evm_push :: "evm_stack \<Rightarrow> uint256 \<Rightarrow> evm_stack option" where
"evm_push stk v = (
  if length stk + 1 < 1024 then
    Some (v#stk)
  else
    None
)"

datatype stop_state =
Halts | Reverts | Returns

datatype evm_state =
  NextState u64 (*pc*) nat (*gas*) evm_stack (*stack *)  |
  StopState stop_state

end