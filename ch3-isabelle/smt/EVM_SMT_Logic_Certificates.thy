theory EVM_SMT_Logic_Certificates
  imports EVM_SMT_Representation Generated_EVM_Arithmetic
begin

text \<open>Each theorem below interprets the generated production AST, for
  arbitrary uint256 inputs, and compares it with the function used by the
  existing Isabelle instruction dispatcher. These are value-level certificates,
  not claims about stack bounds, gas, program counters, or exceptional states.\<close>

lemma uint256_eq_limbs:
  fixes x y :: uint256
  shows "(uint (z0 x) = uint (z0 y) \<and> uint (z1 x) = uint (z1 y) \<and>
     uint (z2 x) = uint (z2 y) \<and> uint (z3 x) = uint (z3 y)) = (x = y)"
  by (cases x; cases y) (simp flip: word_uint_eq_iff)

lemma uint256_zero_limbs:
  "(0 = uint (z0 x) \<and> 0 = uint (z1 x) \<and>
     0 = uint (z2 x) \<and> 0 = uint (z3 x)) = (x = uint256_zero)"
  by (cases x) (simp add: uint256_zero_def uint_0_iff)

lemma packed_boolean:
  "uint256_to_int (if b then uint256_one else uint256_zero) = (if b then 1 else 0)"
  by (cases b) (simp_all add: uint256_to_int_def uint256_one_def uint256_zero_def
      Let_def shiftl_def push_bit_eq_mult)

lemma exported_eq_correct:
  "smt_eval (evm_inputs x y) exported_eq =
    Some (BVV 256 (uint256_to_int (if x = y then uint256_one else uint256_zero)))"
  by (simp add: generated_eq_defs evm_inputs_def uint256_eq_limbs packed_boolean conj_assoc)

lemma exported_iszero_correct:
  "smt_eval (evm_inputs x y) exported_iszero =
    Some (BVV 256 (uint256_to_int (if x = uint256_zero then uint256_one else uint256_zero)))"
  by (cases x)
     (simp add: generated_iszero_defs evm_inputs_def uint256_zero_def
        uint_0_iff packed_boolean conj_assoc)

lemma exported_and_correct:
  "smt_eval (evm_inputs x y) exported_and =
    Some (BVV 256 (uint256_to_int (uint256_and x y)))"
  by (simp add: generated_and_defs evm_inputs_def four_limb_concat_simp uint256_and_def)

lemma exported_or_correct:
  "smt_eval (evm_inputs x y) exported_or =
    Some (BVV 256 (uint256_to_int (uint256_or x y)))"
  by (simp add: generated_or_defs evm_inputs_def four_limb_concat_simp uint256_or_def)

lemma exported_xor_correct:
  "smt_eval (evm_inputs x y) exported_xor =
    Some (BVV 256 (uint256_to_int (uint256_xor x y)))"
  by (simp add: generated_xor_defs evm_inputs_def four_limb_concat_simp uint256_xor_def)

lemma exported_not_correct:
  "smt_eval (evm_inputs x y) exported_not =
    Some (BVV 256 (uint256_to_int (uint256_not x)))"
  by (simp add: generated_not_defs evm_inputs_def four_limb_concat_simp uint256_not_def)

end
