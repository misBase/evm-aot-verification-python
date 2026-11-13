theory EVM_semantics_test
    imports EVM_semantics
begin

(* Definitions for arithmetic instruction tests *)
definition test_arith :: "arith_inst \<Rightarrow> variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_arith inst v c net = instruction_sem v c (Arith inst) net"

definition test_add :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_add = test_arith ADD"

definition test_sub :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_sub = test_arith SUB"

definition test_mul :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_mul = test_arith MUL"

definition test_div :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_div = test_arith DIV"

definition test_mod :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_mod = test_arith MOD"

definition test_addmod :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_addmod = test_arith ADDMOD"

definition test_mulmod :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_mulmod = test_arith MULMOD"

definition test_exp :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_exp = test_arith EXP"

definition test_signextend :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_signextend v c net = instruction_sem v c (Sarith SIGNEXTEND) net"

(* Definitions for PUSH instruction tests *)
definition test_push :: "u256 \<Rightarrow> variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_push val v c net = instruction_sem v c (Stack (PUSH_N (word_rsplit val))) net"

(* Definitions for Sarith instruction tests *)
definition test_sarith :: "sarith_inst \<Rightarrow> variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_sarith inst v c net = instruction_sem v c (Sarith inst) net"

definition test_sdiv :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_sdiv = test_sarith SDIV"

definition test_smod :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_smod = test_sarith SMOD"

definition test_sgt :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_sgt = test_sarith SGT"

definition test_slt :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_slt = test_sarith SLT"

(* Example contexts *)
definition example_var_ctx :: variable_ctx where
  "example_var_ctx = \<lparr>
    vctx_stack = [3, 5], 
    vctx_memory = (\<lambda>_. 0), 
    vctx_memory_usage = 0, 
    vctx_storage = (\<lambda>_. 0), 
    vctx_pc = 0, 
    vctx_balance = (\<lambda>_. 0), 
    vctx_caller = 0, 
    vctx_value_sent = 0, 
    vctx_data_sent = [], 
    vctx_storage_at_call = (\<lambda>_. 0), 
    vctx_balance_at_call = (\<lambda>_. 0), 
    vctx_origin = 0, 
    vctx_ext_program = (\<lambda>_. empty_program), 
    vctx_block = \<lparr> 
      block_blockhash = (\<lambda>_. 0), 
      block_coinbase = 0, 
      block_timestamp = 0, 
      block_number = 0, 
      block_difficulty = 0, 
      block_gaslimit = 0,
      block_basefee = 0,
      block_blobbasefee = 0,
      block_prevrandao = 0
    \<rparr>,
    vctx_gas = 1000000,
    vctx_account_existence = (\<lambda>_. True),
    vctx_touched_storage_index = [],
    vctx_warm_addresses = [],
    vctx_logs = [], 
    vctx_refund = 0, 
    vctx_gasprice = 0,
    vctx_returned_data = [],
    vctx_chainid = 0,
    vctx_blobHashes = [],
    vctx_transient_storage = (\<lambda>_. 0),
    vctx_readonly = False
  \<rparr>"

definition example_const_ctx :: constant_ctx where
  "example_const_ctx = \<lparr>
    cctx_program = empty_program, 
    cctx_this = 0, 
    cctx_hash_filter = (\<lambda>_. True) 
  \<rparr>"

definition example_network :: network where
    "example_network = Cancun"

(* Test assertions for arithmetic operations *)
lemma test_add_correct: "case test_add example_var_ctx example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> vctx_stack v' = [8]
  | _ \<Rightarrow> False"
by eval

lemma test_sub_correct: "case test_sub example_var_ctx example_const_ctx example_network of 
    InstructionContinue v' \<Rightarrow> vctx_stack v' = [-2]  
  | _ \<Rightarrow> False"
by eval

lemma test_mul_correct: "case test_mul example_var_ctx example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> vctx_stack v' = [15] 
  | _ \<Rightarrow> False"
by eval

lemma test_div_correct: "case test_div example_var_ctx example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> vctx_stack v' = [0] 
  | _ \<Rightarrow> False"
by eval

(* Test with modified input stack *)
definition example_var_ctx2 :: variable_ctx where
"example_var_ctx2 = example_var_ctx\<lparr>vctx_stack := [10, 2]\<rparr>"

lemma test_div2_correct: "case test_div example_var_ctx2 example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> vctx_stack v' = [5]
  | _ \<Rightarrow> False" 
by eval

(* Test division by zero case *)
definition example_var_ctx3 :: variable_ctx where
"example_var_ctx3 = example_var_ctx\<lparr>vctx_stack := [5, 0]\<rparr>"

lemma test_div3_correct: "case test_div example_var_ctx3 example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> vctx_stack v' = [0]
  | _ \<Rightarrow> False"
by eval

(* Test stack underflow case *)
definition example_var_ctx4 :: variable_ctx where 
"example_var_ctx4 = example_var_ctx\<lparr>vctx_stack := [5]\<rparr>"

lemma test_add_underflow: "case test_add example_var_ctx4 example_const_ctx example_network of
    InstructionToEnvironment (ContractFail reasons) v _ \<Rightarrow> TooShortStack \<in> set reasons
  | _ \<Rightarrow> False"
by eval

(* Test MOD operation *)
lemma test_mod_correct: "case test_mod example_var_ctx example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> vctx_stack v' = [3]
  | _ \<Rightarrow> False"
by eval

(* Test ADDMOD operation *)
definition example_var_ctx_addmod :: variable_ctx where
"example_var_ctx_addmod = example_var_ctx\<lparr>vctx_stack := [5, 3, 2]\<rparr>"

lemma test_addmod_correct: "case test_addmod example_var_ctx_addmod example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> vctx_stack v' = [0]
  | _ \<Rightarrow> False"
by eval

(* Test MULMOD operation *)
definition example_var_ctx_mulmod :: variable_ctx where
"example_var_ctx_mulmod = example_var_ctx\<lparr>vctx_stack := [5, 3, 2]\<rparr>"

lemma test_mulmod_correct: "case test_mulmod example_var_ctx_mulmod example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> vctx_stack v' = [1]
  | _ \<Rightarrow> False"
by eval

(* Test EXP operation *)
lemma test_exp_correct: "case test_exp example_var_ctx example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> vctx_stack v' = [243]
  | _ \<Rightarrow> False"
by eval

(* Test SIGNEXTEND operation *)
lemma test_signextend_correct: "case test_signextend example_var_ctx example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> vctx_stack v' = [5]
  | _ \<Rightarrow> False"
by eval

(* Test PUSH operation *)
lemma test_push_correct: "case test_push 42 example_var_ctx example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> vctx_stack v' = [42, 3, 5]
  | _ \<Rightarrow> False"
by eval

(* Test SDIV operation *)
lemma test_sdiv_correct: "case test_sdiv example_var_ctx example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> vctx_stack v' = [0]
  | _ \<Rightarrow> False"
by eval

(* Test SMOD operation *)
lemma test_smod_correct: "case test_smod example_var_ctx example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> vctx_stack v' = [3]
  | _ \<Rightarrow> False"
by eval

(* Test SGT operation *)
lemma test_sgt_correct: "case test_sgt example_var_ctx example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> vctx_stack v' = [0]
  | _ \<Rightarrow> False"
by eval

(* Test SLT operation *)
lemma test_slt_correct: "case test_slt example_var_ctx example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> vctx_stack v' = [1]
  | _ \<Rightarrow> False"
by eval



chapter \<open>Test Bytecode Execution\<close>

(* Test execute_evm_bytecode *)
definition simple_bytecode :: "char list" where
"simple_bytecode = 
  ''60'' @ ''05'' @     \<comment> \<open> PUSH1 5 \<close>
  ''60'' @ ''03'' @     \<comment> \<open> PUSH1 3 \<close>
  ''01'' @              \<comment> \<open> ADD     \<close>
  ''60'' @ ''02'' @     \<comment> \<open> PUSH1 2 \<close>
  ''02'' @              \<comment> \<open> MUL     \<close>
  ''00''                \<comment> \<open> STOP    \<close>
  "

(* Test simple program *)
definition simple_program :: "program" where
"simple_program = \<lparr>
  program_content = (\<lambda>x. 
    if x = 0 then Some (Stack (PUSH_N [5]))
    else if x = 2 then Some (Stack (PUSH_N [3]))
    else if x = 4 then Some (Arith ADD)
    else if x = 5 then Some (Stack (PUSH_N [2]))
    else if x = 7 then Some (Arith MUL)
    else if x = 8 then Some (Misc STOP)
    else None),
  program_length = 7,
  program_byte_content = [0x60, 0x05, 0x60, 0x03, 0x01, 0x60, 0x02, 0x02, 0x00]
\<rparr>"

value "program_sem (example_const_ctx (| cctx_program := simple_program |)) 1000000 example_network (InstructionContinue example_var_ctx)"

value "parse_bytecode simple_bytecode"

(* Test bytecode execution *)
lemma test_simple_bytecode: "
  case execute_evm_bytecode simple_bytecode example_var_ctx example_const_ctx example_network 1000000 of
  InstructionToEnvironment (ContractReturn []) v _ \<Rightarrow> vctx_stack v = [16, 3, 5]
  | _ \<Rightarrow> False"
by eval

value "execute_evm_bytecode simple_bytecode example_var_ctx example_const_ctx example_network 5"

(* Test with insufficient fuel *)
lemma test_insufficient_fuel: "
  case execute_evm_bytecode simple_bytecode example_var_ctx example_const_ctx example_network 5 of
  InstructionToEnvironment (ContractFail reasons) v _ \<Rightarrow> (OutOfGas \<in> set reasons) \<and> (vctx_stack v = [5, 3, 5])
  | _ \<Rightarrow> False"
by eval

(* Test invalid opcode *)
definition invalid_bytecode :: "char list" where
"invalid_bytecode = ''0xfe''" (* Invalid opcode *)

value "execute_evm_bytecode invalid_bytecode example_var_ctx example_const_ctx example_network 100000"

lemma test_invalid_bytecode: "
  case execute_evm_bytecode invalid_bytecode example_var_ctx example_const_ctx example_network 100000 of
  InstructionToEnvironment (ContractFail reasons) _ _ \<Rightarrow> ShouldNotHappen \<in> set reasons
  | _ \<Rightarrow> False"
by eval

(* Test bytecode with RETURN *)
definition return_bytecode :: "char list" where
"return_bytecode = 
  ''60'' @ ''00'' @     \<comment> \<open> PUSH1 0 \<close>
  ''60'' @ ''00'' @     \<comment> \<open> PUSH1 0 \<close>
  ''f3''                \<comment> \<open> RETURN  \<close>
  "

value "execute_evm_bytecode return_bytecode example_var_ctx example_const_ctx example_network 1000000"

lemma test_return_bytecode: "
  case execute_evm_bytecode return_bytecode example_var_ctx example_const_ctx example_network 1000000 of
  InstructionToEnvironment (ContractReturn []) _ _ \<Rightarrow> True
  | _ \<Rightarrow> False"
by eval

(* Test CALLDATACOPY instruction *)
definition test_calldatacopy :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
    "test_calldatacopy v c net = instruction_sem v c (Memory CALLDATACOPY) net"

(* Test context with specific calldata *)
definition example_var_ctx_calldatacopy :: variable_ctx where
  "example_var_ctx_calldatacopy = example_var_ctx\<lparr>
    vctx_data_sent := [1, 2, 3, 4, 5, 6, 7, 8],
    vctx_stack := [0, 0, 4]  \<comment> \<open>destOffset=0, offset=0, size=4\<close>
  \<rparr>"

(* Test basic CALLDATACOPY operation *)
lemma test_calldatacopy_basic: "
  case test_calldatacopy example_var_ctx_calldatacopy example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> 
      vctx_memory v' 0 = 1 \<and>
      vctx_memory v' 1 = 2 \<and>
      vctx_memory v' 2 = 3 \<and>
      vctx_memory v' 3 = 4
  | _ \<Rightarrow> False"
by eval

(* Test CALLDATACOPY with offset *)
definition example_var_ctx_calldatacopy_offset :: variable_ctx where
  "example_var_ctx_calldatacopy_offset = example_var_ctx\<lparr>
    vctx_data_sent := [1, 2, 3, 4, 5, 6, 7, 8],
    vctx_stack := [10, 2, 3]  \<comment> \<open>destOffset=10, offset=2, size=3\<close>
  \<rparr>"

lemma test_calldatacopy_offset: "
  case test_calldatacopy example_var_ctx_calldatacopy_offset example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> 
      vctx_memory v' 10 = 3 \<and>
      vctx_memory v' 11 = 4 \<and>
      vctx_memory v' 12 = 5
  | _ \<Rightarrow> False"
by eval

(* Test CALLDATACOPY with out of bounds read *)
definition example_var_ctx_calldatacopy_oob :: variable_ctx where
  "example_var_ctx_calldatacopy_oob = example_var_ctx\<lparr>
    vctx_data_sent := [1, 2, 3, 4],
    vctx_stack := [0, 2, 5]  \<comment> \<open>destOffset=0, offset=2, size=5 (exceeds data length)\<close>
  \<rparr>"

lemma test_calldatacopy_oob: "
  case test_calldatacopy example_var_ctx_calldatacopy_oob example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> 
      vctx_memory v' 0 = 3 \<and>
      vctx_memory v' 1 = 4 \<and>
      vctx_memory v' 2 = 0 \<and>  \<comment> \<open>Out of bounds reads return 0\<close>
      vctx_memory v' 3 = 0 \<and>
      vctx_memory v' 4 = 0
  | _ \<Rightarrow> False"
by eval

(* Test CALLDATACOPY with zero size *)
definition example_var_ctx_calldatacopy_zero :: variable_ctx where
  "example_var_ctx_calldatacopy_zero = example_var_ctx\<lparr>
    vctx_data_sent := [1, 2, 3, 4],
    vctx_stack := [0, 0, 0]  \<comment> \<open>destOffset=0, offset=0, size=0\<close>
  \<rparr>"

lemma test_calldatacopy_zero: "
  case test_calldatacopy example_var_ctx_calldatacopy_zero example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> True  \<comment> \<open>Should succeed without modifying memory\<close>
  | _ \<Rightarrow> False"
by eval

(* Test CALLDATACOPY stack underflow *)
definition example_var_ctx_calldatacopy_underflow :: variable_ctx where
  "example_var_ctx_calldatacopy_underflow = example_var_ctx\<lparr>
    vctx_data_sent := [1, 2, 3, 4],
    vctx_stack := [0, 0]  \<comment> \<open>Missing one stack element\<close>
  \<rparr>"

lemma test_calldatacopy_underflow: "
  case test_calldatacopy example_var_ctx_calldatacopy_underflow example_const_ctx example_network of
    InstructionToEnvironment (ContractFail reasons) _ _ \<Rightarrow> TooShortStack \<in> set reasons
  | _ \<Rightarrow> False"
by eval

(* Test RETURNDATACOPY instruction *)
definition test_returndatacopy :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
  "test_returndatacopy v c net = instruction_sem v c (Memory RETURNDATACOPY) net"

(* Test context with specific return data *)
definition example_var_ctx_returndatacopy :: variable_ctx where
  "example_var_ctx_returndatacopy = example_var_ctx\<lparr>
  vctx_returned_data := [1, 2, 3, 4, 5, 6, 7, 8],
  vctx_stack := [0, 0, 4]  \<comment> \<open>destOffset=0, offset=0, size=4\<close>
  \<rparr>"

(* Test basic RETURNDATACOPY operation *)
lemma test_returndatacopy_basic: "
  case test_returndatacopy example_var_ctx_returndatacopy example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> 
    vctx_memory v' 0 = 1 \<and>
    vctx_memory v' 1 = 2 \<and>
    vctx_memory v' 2 = 3 \<and>
    vctx_memory v' 3 = 4
  | _ \<Rightarrow> False"
by eval

(* Test RETURNDATACOPY with offset *)
definition example_var_ctx_returndatacopy_offset :: variable_ctx where
  "example_var_ctx_returndatacopy_offset = example_var_ctx\<lparr>
  vctx_returned_data := [1, 2, 3, 4, 5, 6, 7, 8],
  vctx_stack := [10, 2, 3]  \<comment> \<open>destOffset=10, offset=2, size=3\<close>
  \<rparr>"

lemma test_returndatacopy_offset: "
  case test_returndatacopy example_var_ctx_returndatacopy_offset example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> 
    vctx_memory v' 10 = 3 \<and>
    vctx_memory v' 11 = 4 \<and>
    vctx_memory v' 12 = 5
  | _ \<Rightarrow> False"
by eval

(* Test RETURNDATACOPY stack underflow *)
definition example_var_ctx_returndatacopy_underflow :: variable_ctx where
  "example_var_ctx_returndatacopy_underflow = example_var_ctx\<lparr>
  vctx_returned_data := [1, 2, 3, 4],
  vctx_stack := [0, 0]  \<comment> \<open>Missing one stack element\<close>
  \<rparr>"

lemma test_returndatacopy_underflow: "
  case test_returndatacopy example_var_ctx_returndatacopy_underflow example_const_ctx example_network of
  InstructionToEnvironment (ContractFail reasons) _ _ \<Rightarrow> TooShortStack \<in> set reasons
  | _ \<Rightarrow> False"
by eval

(* Test RETURNDATACOPY with out of bounds access *)
definition example_var_ctx_returndatacopy_oob :: variable_ctx where
  "example_var_ctx_returndatacopy_oob = example_var_ctx\<lparr>
  vctx_returned_data := [1, 2, 3, 4],
  vctx_stack := [0, 2, 5]  \<comment> \<open>destOffset=0, offset=2, size=5 (exceeds data length)\<close>
  \<rparr>"

lemma test_returndatacopy_oob: "
  case test_returndatacopy example_var_ctx_returndatacopy_oob example_const_ctx example_network of
  InstructionToEnvironment (ContractFail reasons) _ _ \<Rightarrow> ReturnDataOutOfBounds \<in> set reasons
  | _ \<Rightarrow> False"
by eval


(* ------------------------------------------------------------------------- *)
(* Test for dynamic gas cost *)
(* ------------------------------------------------------------------------- *)

(* Test definitions for memory operations *)
definition test_mstore :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
  "test_mstore v c net = instruction_sem v c (Memory MSTORE) net"

definition test_mstore8 :: "variable_ctx ⇒ constant_ctx ⇒ network ⇒ instruction_result" where
  "test_mstore8 v c net = instruction_sem v c (Memory MSTORE8) net"

definition test_codecopy :: "variable_ctx ⇒ constant_ctx ⇒ network ⇒ instruction_result" where
  "test_codecopy v c net = instruction_sem v c (Memory CODECOPY) net"

definition test_mcopy :: "variable_ctx ⇒ constant_ctx ⇒ network ⇒ instruction_result" where
  "test_mcopy v c net = instruction_sem v c (Memory MCOPY) net"

definition test_revert :: "variable_ctx ⇒ constant_ctx ⇒ network ⇒ instruction_result" where
  "test_revert v c net = instruction_sem v c (Misc REVERT) net"

definition test_mload :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
  "test_mload v c net = instruction_sem v c (Memory MLOAD) net"

definition test_keccak256 :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
  "test_keccak256 v c net = instruction_sem v c (Arith KECCAK256) net"

definition test_calldatacopy_gas :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
  "test_calldatacopy_gas v c net = instruction_sem v c (Memory CALLDATACOPY) net"

definition test_return_gas :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
  "test_return_gas v c net = instruction_sem v c (Misc RETURN) net"

definition test_log :: "variable_ctx \<Rightarrow> log_inst \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
  "test_log v inst c net = instruction_sem v c (Log inst) net"

(* Test contexts with different memory parameters *)
definition gas_test_ctx :: "nat \<Rightarrow> u256 list \<Rightarrow> variable_ctx" where
"gas_test_ctx initial_gas stack = example_var_ctx\<lparr>
  vctx_gas := initial_gas,
  vctx_stack := stack,
  vctx_memory_usage := 0
\<rparr>"

(* Test MSTORE gas cost *)
lemma test_mstore_gas_small: "
  let v = gas_test_ctx 100000 [0, 1234] in
  case test_mstore v example_const_ctx example_network of
    InstructionContinue v' \<Rightarrow> 
      let mem_size = 0 + 32;
        new_mem_words = (mem_size + 31) div 32;
        square = new_mem_words * new_mem_words in
      vctx_gas v' = (100000 - (new_mem_words * MemoryGas + square div QuadCoeffDiv) - 3)
    | _ \<Rightarrow> False"
by eval

lemma test_mstore_gas_large: "
  let v = gas_test_ctx 100000 [0xfff0, 1234] in
  case test_mstore v example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> 
    let mem_size = 0xfff0 + 32;                                           \<comment> \<open>significantly more gas for larger memory\<close>
      new_mem_words = (mem_size + 31) div 32;
      square = new_mem_words * new_mem_words in
    vctx_gas v' = (100000 - (new_mem_words * MemoryGas + square div QuadCoeffDiv) - 3)
  | _ \<Rightarrow> False"
by eval

(* Test MLOAD gas cost *)
lemma test_mload_gas_small: "
  let v = gas_test_ctx 100000 [0] in
  case test_mload v example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 99994                                     
  | _ \<Rightarrow> False"
by eval

lemma test_mload_gas_large: "
  let v = gas_test_ctx 100000 [0xfff0] in
  case test_mload v example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 85650               \<comment> \<open>significantly more gas for larger memory access\<close>
  | _ \<Rightarrow> False"
by eval

(* Test KECCAK256 gas cost *) 
lemma test_keccak256_gas_small: "
  let v = gas_test_ctx 100000 [0, 32] in
  case test_keccak256 v example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 99961                                     
  | _ \<Rightarrow> False"
by eval

lemma test_keccak256_gas_large: "
  let v = gas_test_ctx 100000 [0, 0x100] in
  case test_keccak256 v example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 99898               \<comment> \<open>significantly more gas for larger input\<close>
  | _ \<Rightarrow> False"
by eval

(* Test CALLDATACOPY gas cost *)
lemma test_calldatacopy_gas_small: "
  let v = gas_test_ctx 100000 [0, 0, 32] in
  case test_calldatacopy_gas v example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 99991
  | _ \<Rightarrow> False"
by eval

lemma test_calldatacopy_gas_large: "
  let v = gas_test_ctx 100000 [0, 0, 0x100] in
  case test_calldatacopy_gas v example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 99949                \<comment> \<open>larger copy size\<close>
  | _ \<Rightarrow> False" 
by eval

(* Test RETURN gas cost *)
lemma test_return_gas_small: "
  let v = gas_test_ctx 100000 [0, 32] in
  case test_return_gas v example_const_ctx example_network of
  InstructionToEnvironment (ContractReturn _) v' _ \<Rightarrow> vctx_gas v' = 99997
  | _ \<Rightarrow> False"
by eval

lemma test_return_gas_large: "
  let v = gas_test_ctx 100000 [0, 0x1000] in
  case test_return_gas v example_const_ctx example_network of
  InstructionToEnvironment (ContractReturn _) v' _ \<Rightarrow> vctx_gas v' = 99584
  | _ \<Rightarrow> False"
by eval

(* Test MSTORE8 gas cost *)
lemma test_mstore8_gas_small: "
  let v = gas_test_ctx 100000 [0, 0xff] in 
  case test_mstore8 v example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 99994
  | _ \<Rightarrow> False"
by eval

lemma test_mstore8_gas_large: "
  let v = gas_test_ctx 100000 [0xfff0, 0xff] in
  case test_mstore8 v example_const_ctx example_network of 
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 85661                \<comment> \<open>larger memory offset\<close>
  | _ \<Rightarrow> False"
by eval

(* Test CODECOPY gas cost *)
lemma test_codecopy_gas_small: "
  let v = gas_test_ctx 100000 [0, 0, 32] in
  case test_codecopy v example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 99991
  | _ \<Rightarrow> False"
by eval

lemma test_codecopy_gas_large: "
  let v = gas_test_ctx 100000 [0, 0, 0x100] in
  case test_codecopy v example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 99949                \<comment> \<open>larger copy size\<close>
  | _ \<Rightarrow> False"
by eval

(* DEBUG for MCOPY *)

value "meter_gas (Memory EXTCODECOPY) (gas_test_ctx 100000 [0, 0, 0, 32]) example_const_ctx example_network"
value "handle_memory_copy_gas (gas_test_ctx 100000 [0, 0, 0, 32]) (Memory EXTCODECOPY) Gfasteststep 2 0"

(* Test MCOPY gas cost *)
lemma test_mcopy_gas_small: "
  let v = gas_test_ctx 100000 [0, 0, 32] in
  case test_mcopy v example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 99991
  | _ \<Rightarrow> False"
by eval

lemma test_mcopy_gas_large: "
  let v = gas_test_ctx 100000 [0, 0, 0x100] in
  case test_mcopy v example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 99949                \<comment> \<open>larger copy size\<close>
  | _ \<Rightarrow> False"
by eval

(* Test REVERT gas cost *)
lemma test_revert_gas_small: "
  let v = gas_test_ctx 100000 [0, 32] in
  case test_revert v example_const_ctx example_network of
  InstructionToEnvironment (ContractFail _) v' _ \<Rightarrow> vctx_gas v' = 99997
  | _ \<Rightarrow> False"
by eval

lemma test_revert_gas_large: "
  let v = gas_test_ctx 100000 [0, 0x1000] in
  case test_revert v example_const_ctx example_network of
  InstructionToEnvironment (ContractFail _) v' _ \<Rightarrow> vctx_gas v' = 99584
  | _ \<Rightarrow> False"
by eval

(* Test LOG0 gas cost *)
lemma test_log0_gas_small: "
  let v = gas_test_ctx 100000 [0, 32] in
  case test_log v LOG0 example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 99366 
  | _ \<Rightarrow> False"
by eval

(* Test LOG1 gas cost *)
lemma test_log1_gas_small: "
  let v = gas_test_ctx 100000 [0, 32, 1] in
  case test_log v LOG1 example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 98991
  | _ \<Rightarrow> False"  
by eval

(* Test LOG2 gas cost *)
lemma test_log2_gas_small: "
  let v = gas_test_ctx 100000 [0, 32, 1, 2] in
  case test_log v LOG2 example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 98616
  | _ \<Rightarrow> False"
by eval

(* Test LOG3 gas cost *)
lemma test_log3_gas_small: "
  let v = gas_test_ctx 100000 [0, 32, 1, 2, 3] in
  case test_log v LOG3 example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 98241
  | _ \<Rightarrow> False"
by eval

(* Test LOG4 gas cost *)
lemma test_log4_gas_small: "
  let v = gas_test_ctx 100000 [0, 32, 1, 2, 3, 4] in
  case test_log v LOG4 example_const_ctx example_network of
  InstructionContinue v' \<Rightarrow> vctx_gas v' = 97866
  | _ \<Rightarrow> False"
by eval


end
