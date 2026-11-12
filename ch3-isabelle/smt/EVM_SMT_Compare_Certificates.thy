theory EVM_SMT_Compare_Certificates
  imports EVM_SMT_Arithmetic_Certificates EVM_SMT_Logic_Certificates
begin

text \<open>The final borrow determines unsigned comparison. The same limb
  balance also proves modular subtraction and negation. Signed comparisons use
  the highest input bit and agree with the word-level predicate used by the
  instruction dispatcher.\<close>

definition smt_lt256 :: "uint256 \<Rightarrow> uint256 \<Rightarrow> bool" where
  "smt_lt256 x y = (let
     b0 = snd (smt_sub64 (uint (z0 x)) (uint (z0 y)) 0);
     b1 = snd (smt_sub64 (uint (z1 x)) (uint (z1 y)) b0);
     b2 = snd (smt_sub64 (uint (z2 x)) (uint (z2 y)) b1);
     b3 = snd (smt_sub64 (uint (z3 x)) (uint (z3 y)) b2)
   in b3 \<noteq> 0)"

lemma smt_lt256_correct:
  "smt_lt256 x y = uint256_lt x y"
  unfolding smt_lt256_def uint256_lt_def
  by (simp add: case_prod_unfold Let_def smt_sub64_zero smt_sub64_correct sub64_borrow_lt uint_0_iff)


lemma sub64_balance:
  assumes "uint c < 2"
  shows "uint x - uint y - uint c =
    uint (fst (Sub64_borrow x y c)) - uint (snd (Sub64_borrow x y c)) * 2^64"
proof -
  have int_cases: "uint c = 0 \<or> uint c = 1"
    using assms uint_nonnegative[of c] by linarith
  have c_cases: "c = 0 \<or> c = 1"
    using int_cases by (simp add: word_uint_eq_iff)
  have c_complement: "uint (1 - c) = 1 - uint c" "uint (1 - c) < 2"
    using c_cases by auto
  have borrow:
    "uint (snd (Sub64_borrow x y c)) =
      1 - (((2::int)^64 + (uint x - uint y - uint c)) div 2^64)"
    unfolding sub64_borrow_complement
    using add64_carry_quotient[OF c_complement(2), of x "NOT y"]
    by (simp add: uint_not_u64 c_complement algebra_simps)
  have quotient: "((2::int)^64 + (uint x - uint y - uint c)) div 2^64 =
      (uint x - uint y - uint c) div 2^64 + 1"
    by (rule div_add_self1) simp
  show ?thesis
    unfolding borrow sub64_result quotient
    using div_mult_mod_eq[of "uint x - uint y - uint c" "(2::int)^64"]
    by (simp_all; linarith)
qed

lemma uint256_sub_properties:
  "uint256_to_int (uint256_sub x y) = (uint256_to_int x - uint256_to_int y) mod 2^256"
  "uint256_lt x y = (uint256_to_int x < uint256_to_int y)"
proof -
  define p0 where "p0 = Sub64_borrow (z0 x) (z0 y) 0"
  define p1 where "p1 = Sub64_borrow (z1 x) (z1 y) (snd p0)"
  define p2 where "p2 = Sub64_borrow (z2 x) (z2 y) (snd p1)"
  define p3 where "p3 = Sub64_borrow (z3 x) (z3 y) (snd p2)"
  have b0: "uint (snd p0) < 2" by (simp add: p0_def sub64_borrow_lt)
  have b1: "uint (snd p1) < 2" by (simp add: p1_def sub64_borrow_lt)
  have b2: "uint (snd p2) < 2" by (simp add: p2_def sub64_borrow_lt)
  have b3: "uint (snd p3) < 2" by (simp add: p3_def sub64_borrow_lt)
  have eq0: "uint (z0 x) - uint (z0 y) = uint (fst p0) - uint (snd p0) * 2^64"
    using sub64_balance[of 0 "z0 x" "z0 y"] by (simp add: p0_def)
  have eq1: "uint (z1 x) - uint (z1 y) - uint (snd p0) =
    uint (fst p1) - uint (snd p1) * 2^64"
    using sub64_balance[OF b0, of "z1 x" "z1 y"] by (simp add: p1_def)
  have eq2: "uint (z2 x) - uint (z2 y) - uint (snd p1) =
    uint (fst p2) - uint (snd p2) * 2^64"
    using sub64_balance[OF b1, of "z2 x" "z2 y"] by (simp add: p2_def)
  have eq3: "uint (z3 x) - uint (z3 y) - uint (snd p2) =
    uint (fst p3) - uint (snd p3) * 2^64"
    using sub64_balance[OF b2, of "z3 x" "z3 y"] by (simp add: p3_def)
  let ?r = "uint256_to_int \<lparr>z0 = fst p0, z1 = fst p1, z2 = fst p2, z3 = fst p3\<rparr>"
  have balance: "uint256_to_int x - uint256_to_int y = ?r - uint (snd p3) * 2^256"
    using eq0 eq1 eq2 eq3 unfolding pack_horner by (simp_all; linarith)
  have bits: "uint (snd p3) = 0 \<or> uint (snd p3) = 1"
    using b3 uint_nonnegative[of "snd p3"] by linarith
  have lt: "(uint256_to_int x < uint256_to_int y) = (uint (snd p3) \<noteq> 0)"
    using balance bits pack_range[of "\<lparr>z0 = fst p0, z1 = fst p1, z2 = fst p2, z3 = fst p3\<rparr>"]
    by (elim disjE; simp_all; linarith)
  have result: "uint256_to_int (uint256_sub x y) = ?r"
    by (simp add: uint256_sub_def Let_def case_prod_unfold p0_def p1_def p2_def p3_def)
  show "uint256_to_int (uint256_sub x y) =
      (uint256_to_int x - uint256_to_int y) mod 2^256"
    unfolding result balance
    using pack_range[of "\<lparr>z0 = fst p0, z1 = fst p1, z2 = fst p2, z3 = fst p3\<rparr>"]
    by (subst mod_diff_eq[symmetric]) simp
  show "uint256_lt x y = (uint256_to_int x < uint256_to_int y)"
    unfolding lt uint256_lt_def
    by (simp add: case_prod_unfold Let_def p0_def p1_def p2_def p3_def uint_0_iff)
qed

lemmas uint256_sub_int = uint256_sub_properties(1)
lemmas uint256_lt_int = uint256_sub_properties(2)

lemma pack_neg:
  "uint256_to_int (Neg x) = bv_norm 256 (- uint256_to_int x)"
proof -
  have zero: "uint256_to_int uint256_zero = 0"
    by (simp add: pack_horner uint256_zero_def)
  show ?thesis unfolding Neg_def uint256_sub_int
    by (simp add: zero bv_norm_def)
qed

lemma limb_sign_bit:
  "(bv_norm 1 (uint (w :: u64) div 2^63) = 1) = (2^63 \<le> uint w)"
proof -
  have lo: "0 \<le> uint w div (2::int)^63" by (simp add: pos_imp_zdiv_nonneg_iff)
  have hi: "uint w div (2::int)^63 < 2"
    using uint_lt_2p64[of w] by (simp add: div_less_iff_less_mult)
  have pos: "(0 < uint w div (2::int)^63) = (2^63 \<le> uint w)"
    by (simp add: pos_imp_zdiv_pos_iff)
  have quo: "(uint w div (2::int)^63 = 1) = (2^63 \<le> uint w)"
    using lo hi pos by linarith
  show ?thesis using lo hi quo by (simp add: bv_norm_def)
qed

lemma sign_is_negative:
  "(Sign x < 0) = (2^63 \<le> uint (z3 x))"
proof -
  have iszero: "IsZero x \<Longrightarrow> z3 x = 0"
    by (simp add: IsZero_def or_eq_0_iff)
  show ?thesis
    unfolding Sign_def
    using iszero by (auto simp: word_less_alt)
qed


lemma sign_is_negative_packed:
  "(Sign x < 0) = (2^255 \<le> uint256_to_int x)"
  unfolding sign_is_negative pack_horner
  using limb_uint_range[of "z0 x"] limb_uint_range[of "z1 x"]
    limb_uint_range[of "z2 x"] limb_uint_range[of "z3 x"]
  by (simp_all; linarith)

lemma packed_top_bit:
  "bit (uint256_to_int x) 255 = (Sign x < 0)"
proof -
  let ?a = "uint256_to_int x"
  have lo: "0 \<le> ?a div (2::int)^255"
    using pack_nonnegative[of x] by (simp add: pos_imp_zdiv_nonneg_iff)
  have hi: "?a div (2::int)^255 < 2"
    using pack_less[of x] by (simp add: div_less_iff_less_mult)
  have pos: "(0 < ?a div (2::int)^255) = (2^255 \<le> ?a)"
    by (simp add: pos_imp_zdiv_pos_iff)
  have cases: "?a div (2::int)^255 = 0 \<or> ?a div (2::int)^255 = 1"
    using lo hi by linarith
  show ?thesis
    unfolding bit_iff_odd sign_is_negative_packed
    using cases pos by auto
qed

lemma packed_word_uint:
  "uint (uint256_to_word256 x) = uint256_to_int x"
  using pack_range[of x]
  by (simp add: uint256_to_word256_def uint_word_of_int)

lemma packed_word_sint:
  "sint (uint256_to_word256 x) =
    (if Sign x < 0 then uint256_to_int x - 2^256 else uint256_to_int x)"
  unfolding sint_uint packed_word_uint
  using pack_range[of x]
  by (simp add: signed_take_bit_eq_take_bit_minus take_bit_eq_mod packed_top_bit)

lemma uint256_slt_word_sless:
  "uint256_slt x y = word_sless (uint256_to_word256 x) (uint256_to_word256 y)"
proof -
  have signed_less: "word_sless (a :: u256) b = (sint a < sint b)" for a b
    by transfer simp
  show ?thesis
    unfolding signed_less packed_word_sint uint256_slt_def uint256_lt_int Let_def
    using pack_range[of x] pack_range[of y]
      sign_is_negative_packed[of x] sign_is_negative_packed[of y]
    by (auto split: if_splits; linarith)
qed

lemma uint256_sgt_word_sless:
  "uint256_sgt x y = word_sless (uint256_to_word256 y) (uint256_to_word256 x)"
  by (simp add: uint256_slt_word_sless[symmetric] uint256_sgt_def
      uint256_slt_def uint256_gt_def Let_def; auto)

lemmas limb_sign_bit_simp = limb_sign_bit[simplified]


lemma exported_lt_model:
  "smt_eval (evm_inputs x y) exported_lt =
    Some (BVV 256 (if smt_lt256 x y then 1 else 0))"
  unfolding smt_lt256_def
  by (simp add: generated_lt_defs evm_inputs_def Let_def
      bv_norm_nested bv_norm_sub_left smt_sub64_normalized)

lemma exported_gt_model:
  "smt_eval (evm_inputs x y) exported_gt =
    Some (BVV 256 (if smt_lt256 y x then 1 else 0))"
  unfolding smt_lt256_def
  by (simp add: generated_gt_defs evm_inputs_def Let_def
      bv_norm_nested bv_norm_sub_left smt_sub64_normalized)

lemma exported_lt_correct:
  "smt_eval (evm_inputs x y) exported_lt = Some (BVV 256
    (uint256_to_int (if uint256_lt x y then uint256_one else uint256_zero)))"
  by (simp add: exported_lt_model smt_lt256_correct packed_boolean)

lemma exported_gt_correct:
  "smt_eval (evm_inputs x y) exported_gt = Some (BVV 256
    (uint256_to_int (if uint256_gt x y then uint256_one else uint256_zero)))"
  by (simp add: exported_gt_model smt_lt256_correct uint256_gt_def packed_boolean)

lemma slt_sign_model:
  "uint256_slt x y =
    ((Sign x < 0 \<and> \<not> Sign y < 0) \<or>
     ((Sign x < 0) = (Sign y < 0) \<and> smt_lt256 x y))"
  by (auto simp: uint256_slt_def Let_def smt_lt256_correct)

lemma sgt_sign_model:
  "uint256_sgt x y =
    ((\<not> Sign x < 0 \<and> Sign y < 0) \<or>
     ((Sign x < 0) = (Sign y < 0) \<and> smt_lt256 y x))"
  by (auto simp: uint256_sgt_def uint256_gt_def Let_def smt_lt256_correct)

lemma exported_slt_correct:
  "smt_eval (evm_inputs x y) exported_slt = Some (BVV 256
    (uint256_to_int (if uint256_slt x y then uint256_one else uint256_zero)))"
  unfolding slt_sign_model smt_lt256_def
  by (simp add: generated_slt_defs evm_inputs_def Let_def packed_boolean
      bv_norm_nested bv_norm_sub_left smt_sub64_normalized sign_is_negative
      limb_sign_bit_simp)

lemma exported_sgt_correct:
  "smt_eval (evm_inputs x y) exported_sgt = Some (BVV 256
    (uint256_to_int (if uint256_sgt x y then uint256_one else uint256_zero)))"
  unfolding sgt_sign_model smt_lt256_def
  by (simp add: generated_sgt_defs evm_inputs_def Let_def packed_boolean
      bv_norm_nested bv_norm_sub_left smt_sub64_normalized sign_is_negative
      limb_sign_bit_simp)


lemma exported_slt_dispatch_correct:
  "smt_eval (evm_inputs x y) exported_slt = Some (BVV 256
    (uint256_to_int (if word_sless (uint256_to_word256 x) (uint256_to_word256 y)
      then uint256_one else uint256_zero)))"
  by (simp add: exported_slt_correct uint256_slt_word_sless)

lemma exported_sgt_dispatch_correct:
  "smt_eval (evm_inputs x y) exported_sgt = Some (BVV 256
    (uint256_to_int (if word_sless (uint256_to_word256 y) (uint256_to_word256 x)
      then uint256_one else uint256_zero)))"
  by (simp add: exported_sgt_correct uint256_sgt_word_sless)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms exported_lt_correct
    exported_gt_correct exported_slt_correct exported_sgt_correct
    uint256_lt_int uint256_slt_word_sless uint256_sgt_word_sless}) then ()
    else error "Comparison certificates have oracle dependencies"
\<close>

end
