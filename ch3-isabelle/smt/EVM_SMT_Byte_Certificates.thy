theory EVM_SMT_Byte_Certificates
  imports EVM_SMT_Bit_Representation Generated_EVM_Arithmetic
begin

text \<open>The certificate checks the finite byte-selection tree exported from
  production Python against the limb-based HOL helper, including the full-width
  out-of-range index guard.\<close>

lemma bv_norm_numeral [simp]:
  "bv_norm w (numeral n) = numeral n mod 2^w"
  by (simp add: bv_norm_def)

lemma limb_byte_bits:
  "bit (((w :: u64) >> m) AND 255) n = (n < 8 \<and> bit w (m+n))"
proof -
  have mask: "(255 :: u64) = mask 8" by code_simp
  show ?thesis
    by (auto simp: mask bit_and_iff bit_mask_iff limb_shr_bit
        dest: bit_imp_le_length)
qed

lemma bit_div_power:
  "bit ((a :: int) div 2^k) n = bit a (n+k)"
  by (simp add: drop_bit_eq_div[symmetric] bit_drop_bit_eq add.commute)

lemmas bit_div_byte_simps =
  bit_div_power[where k = "0", simplified]
  bit_div_power[where k = "8", simplified]
  bit_div_power[where k = "16", simplified]
  bit_div_power[where k = "24", simplified]
  bit_div_power[where k = "32", simplified]
  bit_div_power[where k = "40", simplified]
  bit_div_power[where k = "48", simplified]
  bit_div_power[where k = "56", simplified]
  bit_div_power[where k = "64", simplified]
  bit_div_power[where k = "72", simplified]
  bit_div_power[where k = "80", simplified]
  bit_div_power[where k = "88", simplified]
  bit_div_power[where k = "96", simplified]
  bit_div_power[where k = "104", simplified]
  bit_div_power[where k = "112", simplified]
  bit_div_power[where k = "120", simplified]
  bit_div_power[where k = "128", simplified]
  bit_div_power[where k = "136", simplified]
  bit_div_power[where k = "144", simplified]
  bit_div_power[where k = "152", simplified]
  bit_div_power[where k = "160", simplified]
  bit_div_power[where k = "168", simplified]
  bit_div_power[where k = "176", simplified]
  bit_div_power[where k = "184", simplified]
  bit_div_power[where k = "192", simplified]
  bit_div_power[where k = "200", simplified]
  bit_div_power[where k = "208", simplified]
  bit_div_power[where k = "216", simplified]
  bit_div_power[where k = "224", simplified]
  bit_div_power[where k = "232", simplified]
  bit_div_power[where k = "240", simplified]
  bit_div_power[where k = "248", simplified]

lemma byte_as_integer:
  assumes small: "uint256_to_int idx < 32"
  shows "Byte value idx = int_to_uint256
    (bv_norm 8 (uint256_to_int value div 2^(248 - 8 * nat (uint256_to_int idx))))"
proof -
  let ?i = "unat (z0 idx)"
  have small256: "uint256_to_int idx < 256" using small by linarith
  have idx: "nat (uint256_to_int idx) = ?i"
    by (rule low_shift_amount[OF small256])
  have ibound: "?i < 32" using small pack_nonnegative[of idx] idx by linarith
  have cases: "?i = 0 \<or> ?i = 1 \<or> ?i = 2 \<or> ?i = 3 \<or> ?i = 4 \<or> ?i = 5 \<or> ?i = 6 \<or> ?i = 7 \<or> ?i = 8 \<or> ?i = 9 \<or> ?i = 10 \<or> ?i = 11 \<or> ?i = 12 \<or> ?i = 13 \<or> ?i = 14 \<or> ?i = 15 \<or> ?i = 16 \<or> ?i = 17 \<or> ?i = 18 \<or> ?i = 19 \<or> ?i = 20 \<or> ?i = 21 \<or> ?i = 22 \<or> ?i = 23 \<or> ?i = 24 \<or> ?i = 25 \<or> ?i = 26 \<or> ?i = 27 \<or> ?i = 28 \<or> ?i = 29 \<or> ?i = 30 \<or> ?i = 31" using ibound by presburger
  have guard: "\<not> 32 \<le> uint256_to_int idx" using small by simp
  show ?thesis using cases
    by (elim disjE) (rule uint256.equality; (rule bit_word_eqI)?;
        simp add: Byte_def Let_def getword_def idx guard decode_bits
          bv_norm_eq_take_bit drop_bit_eq_div[symmetric] bit_take_bit_iff
          bit_drop_bit_eq bit_div_byte_simps limb_byte_bits packed_bit_all add.commute)+
qed

definition smt_byte_result :: "uint256 \<Rightarrow> uint256 \<Rightarrow> int" where
  "smt_byte_result idx value = (if uint256_to_int idx < 32 then
    bv_norm 8 (uint256_to_int value div 2^(248 - 8*nat (uint256_to_int idx)))
    else 0)"

lemma byte_integer_correct:
  "uint256_to_int (Byte value idx) = smt_byte_result idx value"
proof (cases "uint256_to_int idx < 32")
  case True
  show ?thesis
    by (simp add: byte_as_integer[OF True] smt_byte_result_def True
        smt_pack_int_to_uint256 bv_norm_nested)
next
  case False
  then show ?thesis
    by (simp add: smt_byte_result_def Byte_def uint256_zero_def pack_horner Let_def)
qed

lemma exported_byte_model:
  "smt_eval (evm_inputs x y) exported_byte = Some (BVV 256 (smt_byte_result x y))"
proof (cases "uint256_to_int x < 32")
  case False
  then show ?thesis
    by (simp add: generated_byte_defs evm_inputs_def smt_byte_result_def bv_norm_nested)
next
  case True
  have cases: "uint256_to_int x = 0 \<or> uint256_to_int x = 1 \<or> uint256_to_int x = 2 \<or> uint256_to_int x = 3 \<or> uint256_to_int x = 4 \<or> uint256_to_int x = 5 \<or> uint256_to_int x = 6 \<or> uint256_to_int x = 7 \<or> uint256_to_int x = 8 \<or> uint256_to_int x = 9 \<or> uint256_to_int x = 10 \<or> uint256_to_int x = 11 \<or> uint256_to_int x = 12 \<or> uint256_to_int x = 13 \<or> uint256_to_int x = 14 \<or> uint256_to_int x = 15 \<or> uint256_to_int x = 16 \<or> uint256_to_int x = 17 \<or> uint256_to_int x = 18 \<or> uint256_to_int x = 19 \<or> uint256_to_int x = 20 \<or> uint256_to_int x = 21 \<or> uint256_to_int x = 22 \<or> uint256_to_int x = 23 \<or> uint256_to_int x = 24 \<or> uint256_to_int x = 25 \<or> uint256_to_int x = 26 \<or> uint256_to_int x = 27 \<or> uint256_to_int x = 28 \<or> uint256_to_int x = 29 \<or> uint256_to_int x = 30 \<or> uint256_to_int x = 31"
    using True pack_nonnegative[of x] by presburger
  show ?thesis using cases
    by (elim disjE) (simp_all add: generated_byte_defs evm_inputs_def smt_byte_result_def bv_norm_nested)
qed

lemma exported_byte_correct:
  "smt_eval (evm_inputs x y) exported_byte =
    Some (BVV 256 (uint256_to_int (Byte y x)))"
  by (simp add: exported_byte_model byte_integer_correct)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms exported_byte_correct}) then ()
    else error "Byte certificate has oracle dependencies"
\<close>

end
