theory Div_Comparison
  imports "EVM_SMT_Base.Exp"
begin

lemma add64_carry_quotient:
  assumes "uint c < 2"
  shows "uint (snd (Add64_carry x y c)) = (uint x + uint y + uint c) div 2^64"
proof -
  note eq = add64_carry_spec[OF assms, of x y]
  have low: "uint (fst (Add64_carry x y c)) div (2^64) = 0"
    using uint_nonnegative[of "fst (Add64_carry x y c)"]
      uint_lt_2p64[of "fst (Add64_carry x y c)"] by simp
  have total: "uint x + uint y + uint c =
      uint (fst (Add64_carry x y c)) + uint (snd (Add64_carry x y c)) * 2^64"
    using eq by simp
  show ?thesis
    using low by (simp add: total)
qed

lemma uint64_shr63_bound:
  "uint ((w :: u64) >> 63) < 2"
proof -
  have eq: "unat (w >> 63) = unat w div 2^63"
    by (metis drop_bit_eq_div shiftr_def unat_drop_bit_eq)
  have "unat w < 2 * 2^63"
    using unat_lt_2p64[of w] by (simp add: power_add)
  then have small: "unat (w >> 63) < 2"
    using eq by (simp add: div_less_iff_less_mult)
  have two_nat: "unat (2 :: u64) = 2" by code_simp
  have two_int: "uint (2 :: u64) = 2" by code_simp
  have "(w >> 63) < (2 :: u64)"
    unfolding word_less_nat_alt using small two_nat by simp
  then show ?thesis
    using two_int by (simp add: word_less_alt)
qed

lemma sub64_mask_complement:
  "(((NOT x) AND y) OR ((NOT (x XOR y)) AND (x - y - c))) =
    NOT ((x AND (NOT y)) OR ((x OR (NOT y)) AND (NOT (x + (NOT y) + (1 - c)))))"
  for x y c :: u64
proof -
  have eq: "x + (NOT y) + (1 - c) = x - y - c"
    by (simp add: not_eq_complement algebra_simps)
  show ?thesis
    unfolding eq
    by (rule bit_word_eqI) (auto simp: bit_simps)
qed

lemma uint_shiftr63_complement:
  "uint ((NOT w :: u64) >> 63) = 1 - uint (w >> 63)"
proof -
  have shift: "uint ((v :: u64) >> 63) = uint v div 2^63" for v
    by (simp add: shiftr_def drop_bit_eq_div uint_div uint_2p)
  have rem: "0 \<le> uint w mod (2::int)^63" "uint w mod (2::int)^63 < (2::int)^63"
    by simp_all
  have decomp: "(2::int)^64 - 1 - uint w =
      2^63 * (1 - uint w div 2^63) + (2^63 - 1 - uint w mod 2^63)"
    using div_mult_mod_eq[of "uint w" "(2::int)^63"]
    by (simp add: algebra_simps)
  have quotient: "((2::int)^64 - 1 - uint w) div 2^63 = 1 - uint w div 2^63"
    by (rule int_div_pos_eq[OF decomp]) (use rem in linarith)+
  show ?thesis
    unfolding shift uint_not_u64 by (rule quotient)
qed

lemma sub64_borrow_complement:
  "uint (snd (Sub64_borrow x y c)) =
    1 - uint (snd (Add64_carry x (NOT y) (1 - c)))"
  unfolding Sub64_borrow_def Add64_carry_def Let_def snd_conv
  by (simp only: sub64_mask_complement uint_shiftr63_complement)

lemma sub64_result:
  "uint (fst (Sub64_borrow x y c)) = (uint x - uint y - uint c) mod 2^64"
  by (simp add: Sub64_borrow_def Let_def uint_word_ariths mod_diff_left_eq)

lemma sub64_borrow_lt:
  "uint (snd (Sub64_borrow x y c)) < 2"
  unfolding Sub64_borrow_def Let_def snd_conv
  by (rule uint64_shr63_bound)

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


lemma sub64_borrow_lex:
  assumes "uint c < 2"
  shows "(snd (Sub64_borrow x y c) \<noteq> 0) =
    (uint x < uint y \<or> uint x = uint y \<and> c \<noteq> 0)"
proof -
  have balance: "uint x - uint y - uint c =
    uint (fst (Sub64_borrow x y c)) - uint (snd (Sub64_borrow x y c)) * 2^64"
    by (rule sub64_balance[OF assms])
  have cb: "uint c = 0 \<or> uint c = 1"
    using assms uint_nonnegative[of c] by linarith
  have bb: "uint (snd (Sub64_borrow x y c)) = 0 \<or>
      uint (snd (Sub64_borrow x y c)) = 1"
    using sub64_borrow_lt[of x y c] uint_nonnegative[of "snd (Sub64_borrow x y c)"]
    by linarith
  have r: "0 \<le> uint (fst (Sub64_borrow x y c))"
    "uint (fst (Sub64_borrow x y c)) < 2^64"
    by (rule uint_nonnegative, rule uint_lt_2p64)
  have neg: "(uint (snd (Sub64_borrow x y c)) \<noteq> 0) =
      (uint x - uint y - uint c < 0)"
    using balance bb r by (elim disjE; simp_all; linarith)
  show ?thesis using neg cb by (auto simp: uint_0_iff[symmetric]; linarith)
qed

lemma uint256_lt_iff_limb_lt:
  "x <\<^sub>u y \<longleftrightarrow>
    uint (z3 x) < uint (z3 y) \<or>
    uint (z3 x) = uint (z3 y) \<and> uint (z2 x) < uint (z2 y) \<or>
    uint (z3 x) = uint (z3 y) \<and> uint (z2 x) = uint (z2 y) \<and> uint (z1 x) < uint (z1 y) \<or>
    uint (z3 x) = uint (z3 y) \<and> uint (z2 x) = uint (z2 y) \<and> uint (z1 x) = uint (z1 y) \<and> uint (z0 x) < uint (z0 y)"
  by (auto simp: uint256_lt_def case_prod_unfold Let_def sub64_borrow_lex sub64_borrow_lt)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms uint256_lt_iff_limb_lt}) then ()
    else error "Unexpected oracle in order proof";
\<close>
end
