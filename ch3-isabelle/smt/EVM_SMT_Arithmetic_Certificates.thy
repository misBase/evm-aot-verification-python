theory EVM_SMT_Arithmetic_Certificates
  imports Generated_EVM_Arithmetic EVM_SMT_Representation EVM_Arithmetic_Bridge
begin

text \<open>These statements concern the generated, unsimplified production
  expressions, not handwritten replacements for the Python constructors.\<close>

lemma bv_norm65_uint [simp]: "bv_norm 65 (uint (x :: u64)) = uint x"
proof (rule bv_norm_small)
  show "0 \<le> uint x" by simp
  show "uint x < (2::int)^65"
    using limb_uint_range(2)[of x] by (simp_all; linarith)
qed

lemma bv_norm_add_left:
  "bv_norm w (bv_norm w a + b) = bv_norm w (a + b)"
  by (simp add: bv_norm_def mod_add_left_eq)

lemma bv_norm_sub_left:
  "bv_norm w (bv_norm w a - b) = bv_norm w (a - b)"
  by (simp add: bv_norm_def mod_diff_left_eq)

lemma word_of_norm64 [simp]:
  "(word_of_int (bv_norm 64 x) :: u64) = word_of_int x"
  by (simp add: word_of_int_eq_iff bv_norm_eq_take_bit take_bit_take_bit)

lemma smt_add64_normalized:
  "smt_add64 a b c =
    (bv_norm 64 (a + b + c), bv_norm 1 (bv_norm 65 (a + b + c) div 2^64))"
  by (simp add: smt_add64_def bv_norm_def)

lemma smt_sub64_normalized:
  "smt_sub64 a b c =
    (bv_norm 64 (a - b - c), bv_norm 1 (bv_norm 65 (a - b - c) div 2^64))"
  by (simp add: smt_sub64_def bv_norm_def)

lemma bv_norm64_as_word:
  "bv_norm 64 n = uint (word_of_int n :: u64)"
  by (simp add: bv_norm_def uint_word_of_int)

lemma four_normalized_concat:
  "bv_norm 256 (bv_norm 192 (bv_norm 128
      (bv_norm 64 d * 2^64 + bv_norm 64 c) * 2^64 + bv_norm 64 b)
      * 2^64 + bv_norm 64 a) =
    uint256_to_int \<lparr>z0 = word_of_int a, z1 = word_of_int b,
      z2 = word_of_int c, z3 = word_of_int d\<rparr>"
  by (simp only: bv_norm64_as_word) (rule four_limb_concat)

lemmas four_normalized_concat_simp = four_normalized_concat[simplified]

lemma exported_add_model:
  "smt_eval (evm_inputs x y) exported_add =
    Some (BVV 256 (uint256_to_int (smt_add256 x y)))"
  unfolding smt_add256_def
  by (simp add: generated_add_defs evm_inputs_def Let_def
      bv_norm_nested bv_norm_add_left four_normalized_concat
      four_normalized_concat_simp smt_add64_normalized)

lemma exported_sub_model:
  "smt_eval (evm_inputs x y) exported_sub =
    Some (BVV 256 (uint256_to_int (smt_sub256 x y)))"
  unfolding smt_sub256_def
  by (simp add: generated_sub_defs evm_inputs_def Let_def
      bv_norm_nested bv_norm_sub_left four_normalized_concat
      four_normalized_concat_simp smt_sub64_normalized)

theorem exported_add_correct:
  "smt_eval (evm_inputs x y) exported_add =
    Some (BVV 256 (uint256_to_int (uint256_add x y)))"
  by (simp add: exported_add_model smt_add256_correct)

theorem exported_sub_correct:
  "smt_eval (evm_inputs x y) exported_sub =
    Some (BVV 256 (uint256_to_int (uint256_sub x y)))"
  by (simp add: exported_sub_model smt_sub256_correct)

end
