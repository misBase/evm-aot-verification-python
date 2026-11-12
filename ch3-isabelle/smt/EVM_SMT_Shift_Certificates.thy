theory EVM_SMT_Shift_Certificates
  imports EVM_SMT_Shift_Bridge EVM_SMT_Compare_Certificates
begin

text \<open>These certificates use the actual production Python shift ASTs.
  The Python API takes value before shift, whereas the HOL functions take shift
  before value. All shift guards inspect the complete packed operand.\<close>

lemma bv_shift_width [simp]: "bv_norm 256 256 = 256"
  by (simp add: bv_norm_def)

lemma bv_signed_packed:
  "bv_signed 256 (uint256_to_int x) = signed_take_bit 255 (uint256_to_int x)"
  using pack_range[of x]
  by (simp add: bv_signed_def signed_take_bit_eq_take_bit_minus
      take_bit_eq_mod packed_top_bit sign_is_negative_packed)

lemma packed_sign_extract:
  "(bv_norm 1 (uint256_to_int x div 2^255) = 1) = bit (uint256_to_int x) 255"
  by (simp add: bv_norm_def bit_iff_odd odd_iff_mod_2_eq_one)

lemmas packed_sign_extract_simp = packed_sign_extract[simplified]

lemma bv_signed_negative_packed:
  "(bv_signed 256 (uint256_to_int x) < 0) = bit (uint256_to_int x) 255"
  by (simp add: bv_signed_packed)

theorem exported_shl_correct:
  "smt_eval (evm_inputs x y) exported_shl =
    Some (BVV 256 (uint256_to_int (Lsh y x)))"
  by (simp add: generated_shl_defs evm_inputs_def lsh_packed)

theorem exported_shr_correct:
  "smt_eval (evm_inputs x y) exported_shr =
    Some (BVV 256 (uint256_to_int (Rsh y x)))"
  by (simp add: generated_shr_defs evm_inputs_def rsh_packed)

lemma shift_all_ones_normalized [simp]:
  "bv_norm 256
    115792089237316195423570985008687907853269984665640564039457584007913129639935 =
    bv_norm 256 (-1)"
  by (simp add: bv_norm_def)

theorem exported_sar_correct:
  "smt_eval (evm_inputs x y) exported_sar =
    Some (BVV 256 (uint256_to_int (SRsh y x)))"
  by (cases "256 \<le> uint256_to_int y"; cases "bit (uint256_to_int x) 255";
      simp add: generated_sar_defs evm_inputs_def srsh_packed
        packed_sign_extract packed_sign_extract_simp bv_signed_packed
        bv_signed_negative_packed drop_bit_eq_div)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
      @{thms exported_shl_correct exported_shr_correct exported_sar_correct})
    then () else error "Unexpected oracle in the production shift certificates"
\<close>

end
