theory EVM_semantics_fixes
  imports "EVM_AOT.EVM_semantics"
begin

(* Regression lemmas for the semantic errors found by the GeneralStateTests comparison
   (state-tests/FIXES.md), restated for the four-limb uint256 representation.
   Each lemma is checked by evaluation. *)

abbreviation U :: "int \<Rightarrow> uint256" where "U n \<equiv> int_to_uint256 n"

definition fix_block :: block_info where
  "fix_block = \<lparr>
      block_blockhash = (\<lambda>_. uint256_zero), block_coinbase = 0, block_timestamp = uint256_zero,
      block_number = uint256_zero, block_difficulty = U 456, block_gaslimit = uint256_zero,
      block_basefee = uint256_zero, block_blobbasefee = uint256_zero, block_prevrandao = U 123 \<rparr>"

definition fix_var_ctx :: variable_ctx where
  "fix_var_ctx = \<lparr>
      vctx_stack = [], vctx_memory = (\<lambda>_. 0), vctx_memory_usage = 0, vctx_storage = (\<lambda>_. uint256_zero),
      vctx_pc = 0, vctx_balance = (\<lambda>_. uint256_zero), vctx_caller = 0, vctx_value_sent = uint256_zero,
      vctx_data_sent = [], vctx_storage_at_call = (\<lambda>_. uint256_zero), vctx_balance_at_call = (\<lambda>_. uint256_zero),
      vctx_origin = 0, vctx_ext_program = (\<lambda>_. empty_program), vctx_block = fix_block,
      vctx_gas = 1000000, vctx_account_existence = (\<lambda>_. True), vctx_touched_storage_index = [],
      vctx_warm_addresses = [], vctx_logs = [], vctx_refund = 0, vctx_gasprice = uint256_zero,
      vctx_returned_data = [], vctx_chainid = uint256_zero, vctx_blobHashes = [],
      vctx_transient_storage = (\<lambda>_. uint256_zero), vctx_readonly = False \<rparr>"

definition fix_const_ctx :: constant_ctx where
  "fix_const_ctx = \<lparr> cctx_program = empty_program, cctx_this = 0, cctx_hash_filter = (\<lambda>_. True) \<rparr>"

definition three_byte_program :: program where
  "three_byte_program = \<lparr> program_content = (\<lambda>_. None), program_length = 3, program_byte_content = [1, 2, 3] \<rparr>"

(* SLOAD/SSTORE: EIP-2929 cold/warm storage access; SSTORE gas and refund state machine *)
lemma sstore_gas_cold_set:
  "sstore_gas Cancun (U 7) (U 0) (U 0) (U 9) fix_var_ctx = 22100"
  by eval

lemma sstore_gas_warm_noop:
  "sstore_gas Cancun (U 7) (U 9) (U 9) (U 9) (fix_var_ctx\<lparr>vctx_touched_storage_index := [U 7]\<rparr>) = 100"
  by eval

lemma sstore_refund_clear_nonzero:
  "sstore_refund Cancun (U 9) (U 9) (U 0) = SstoreClearsScheduleRefundEIP3529"
  by eval

lemma sstore_refund_reset_original_nonzero:
  "sstore_refund Cancun (U 9) (U 5) (U 9) = SstoreResetRefundEIP2929"
  by eval

lemma sstore_refund_dirty_to_zero:
  "sstore_refund Cancun (U 9) (U 5) (U 0) = SstoreClearsScheduleRefundEIP3529"
  by eval

lemma sload_gas_cold_then_warm:
  "meter_gas (Storage SLOAD) (fix_var_ctx\<lparr>vctx_stack := [U 7]\<rparr>) fix_const_ctx Cancun = CalculationSuccess 2100 \<and>
   meter_gas (Storage SLOAD) (fix_var_ctx\<lparr>vctx_stack := [U 7], vctx_touched_storage_index := [U 7]\<rparr>)
     fix_const_ctx Cancun = CalculationSuccess 100"
  by eval

(* PREVRANDAO: DIFFICULTY returns prevrandao from Paris on *)
lemma prevrandao_cancun:
  "case instruction_sem fix_var_ctx fix_const_ctx (Info DIFFICULTY) Cancun of
     InstructionContinue v' \<Rightarrow> vctx_stack v' = [U 123]
   | _ \<Rightarrow> False"
  by eval

lemma difficulty_before_paris:
  "case instruction_sem fix_var_ctx fix_const_ctx (Info DIFFICULTY) London of
     InstructionContinue v' \<Rightarrow> vctx_stack v' = [U 456]
   | _ \<Rightarrow> False"
  by eval

(* Implicit STOP at the end of the code *)
lemma implicit_stop:
  "case execute_evm_bytecode ''6000'' fix_var_ctx fix_const_ctx Cancun 1000000 of
     InstructionToEnvironment (ContractReturn []) _ _ \<Rightarrow> True
   | _ \<Rightarrow> False"
  by eval

(* SAR sign handling (the four-limb SAR is SRsh; same boundary cases as the word version) *)
lemma sar_negative_shift_one:
  "inst_sar (U 1) (U (2^255)) = U (2^255 + 2^254)"
  by eval

lemma sar_high_shift_256:
  "inst_sar (U 256) (U (2^255)) = U (2^256 - 1)"
  by eval

lemma sar_nonnegative_shift_256:
  "inst_sar (U 256) (U 1) = U 0"
  by eval

(* Memory expansion gas is monotone *)
lemma memory_expansion_does_not_shrink:
  "calc_memory_expansion_cost 64 32 = CalculationSuccess 0"
  by eval

lemma memory_expansion_incremental:
  "calc_memory_expansion_cost 32 64 = CalculationSuccess 3"
  by eval

(* MSIZE returns the byte size *)
lemma msize_uses_byte_size:
  "case instruction_sem (fix_var_ctx\<lparr>vctx_memory_usage := 32\<rparr>) fix_const_ctx (Memory MSIZE) Cancun of
     InstructionContinue v' \<Rightarrow> vctx_stack v' = [U 32]
   | _ \<Rightarrow> False"
  by eval

(* EXP gas: ceil(bit_length exponent / 8) bytes *)
lemma exp_gas_exponent_two:
  "meter_gas (Arith EXP) (fix_var_ctx\<lparr>vctx_stack := [U 3, U 2]\<rparr>) fix_const_ctx Cancun = CalculationSuccess 60"
  by eval

lemma exp_gas_exponent_256:
  "meter_gas (Arith EXP) (fix_var_ctx\<lparr>vctx_stack := [U 3, U 256]\<rparr>) fix_const_ctx Cancun = CalculationSuccess 110"
  by eval

(* Keccak absorbs every 136-byte block exactly once *)
lemma sha3_135_bytes_no_pad:
  "fst (sha3_update (replicate 135 (0 :: u8)) initial_pos initial_st) = 135"
  by eval

lemma sha3_136_bytes_absorbs_block:
  "fst (sha3_update (replicate 136 (0 :: u8)) initial_pos initial_st) = 0"
  by eval

lemma sha3_137_bytes_continues_next_block:
  "fst (sha3_update (replicate 137 (0 :: u8)) initial_pos initial_st) = 1"
  by eval

(* EIP-2929 account access: cold 2600, warm 100 *)
lemma account_access_cold_then_warm:
  "account_access_gas fix_var_ctx 0x100 = ColdAccountAccessCostEIP2929 \<and>
   account_access_gas (fix_var_ctx\<lparr>vctx_warm_addresses := [0x100]\<rparr>) 0x100 = WarmStorageReadCostEIP2929"
  by eval

lemma balance_gas_cold:
  "meter_gas (Info BALANCE) (fix_var_ctx\<lparr>vctx_stack := [U 256]\<rparr>) fix_const_ctx Cancun = CalculationSuccess 2600"
  by eval

(* CODESIZE/EXTCODESIZE return the byte length; EXTCODESIZE marks the address warm *)
lemma extcodesize_uses_byte_length:
  "case instruction_sem
        (fix_var_ctx\<lparr>vctx_stack := [U 256],
                     vctx_ext_program := (\<lambda>a. if a = 0x100 then three_byte_program else empty_program)\<rparr>)
        fix_const_ctx (Info EXTCODESIZE) Cancun of
     InstructionContinue v' \<Rightarrow> vctx_stack v' = [U 3] \<and> 0x100 \<in> set (vctx_warm_addresses v')
   | _ \<Rightarrow> False"
  by eval

(* SELFBALANCE charges the fast-step gas *)
lemma selfbalance_gas:
  "meter_gas (Info SELFBALANCE) fix_var_ctx fix_const_ctx Cancun = CalculationSuccess Gfaststep"
  by eval

end
