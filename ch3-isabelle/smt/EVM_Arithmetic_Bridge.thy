theory EVM_Arithmetic_Bridge
  imports "EVM_SMT_Base.Exp"
begin

text \<open>The integer functions below are the 65-bit limb operations emitted by
  the production Python arithmetic constructors.  The low result and the
  carry/borrow bit use the same modular arithmetic as SMT-LIB extraction.\<close>

definition smt_add64 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "smt_add64 a b c =
    ((a + b + c) mod 2^64, ((a + b + c) mod 2^65) div 2^64 mod 2)"

definition smt_sub64 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "smt_sub64 a b c =
    ((a - b - c) mod 2^64, ((a - b - c) mod 2^65) div 2^64 mod 2)"

lemma add64_result:
  "uint (fst (Add64_carry x y c)) = (uint x + uint y + uint c) mod 2^64"
  by (simp add: Add64_carry_def Let_def uint_word_ariths mod_add_left_eq)

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

text \<open>This bound is reproved without the evaluation oracle used by the
  corresponding legacy lemma in Exp.\<close>
lemma smt_uint_shiftr63_lt2:
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

lemma smt_add64_carry_lt2:
  "uint (snd (Add64_carry x y c)) < 2"
  unfolding Add64_carry_def Let_def snd_conv
  by (rule smt_uint_shiftr63_lt2)

lemma smt_add64_correct:
  assumes "uint c < 2"
  shows "smt_add64 (uint x) (uint y) (uint c) =
    (uint (fst (Add64_carry x y c)), uint (snd (Add64_carry x y c)))"
proof -
  have lo: "0 \<le> uint x + uint y + uint c" by simp
  have hi: "uint x + uint y + uint c < (2::int)^65"
    using uint_lt_2p64[of x] uint_lt_2p64[of y] assms by (simp_all; linarith)
  have carry: "(uint x + uint y + uint c) div (2::int)^64 < 2"
    using smt_add64_carry_lt2[of x y c] add64_carry_quotient[OF assms, of x y] by simp
  have nonneg: "0 \<le> (uint x + uint y + uint c) div (2::int)^64"
    using lo by (simp add: pos_imp_zdiv_nonneg_iff)
  show ?thesis
    unfolding smt_add64_def
    using lo hi carry nonneg add64_result[of x y c]
      add64_carry_quotient[OF assms, of x y]
    by simp
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
  by (rule smt_uint_shiftr63_lt2)

lemma smt_sub64_correct:
  assumes "uint c < 2"
  shows "smt_sub64 (uint x) (uint y) (uint c) =
    (uint (fst (Sub64_borrow x y c)), uint (snd (Sub64_borrow x y c)))"
proof -
  have int_cases: "uint c = 0 \<or> uint c = 1"
    using assms uint_nonnegative[of c] by linarith
  have c_cases: "c = 0 \<or> c = 1"
    using int_cases by (simp add: word_uint_eq_iff)
  have c_complement: "uint (1 - c) = 1 - uint c" "uint (1 - c) < 2"
    using c_cases by auto
  have borrow:
    "uint (snd (Sub64_borrow x y c)) =
      1 - ((2^64 + (uint x - uint y - uint c)) div 2^64)"
    unfolding sub64_borrow_complement
    using add64_carry_quotient[OF c_complement(2), of x "NOT y"]
    by (simp add: uint_not_u64 c_complement algebra_simps)
  have bounds: "- ((2::int)^64) \<le> uint x - uint y - uint c"
    "uint x - uint y - uint c < (2::int)^64"
    using uint_nonnegative[of x] uint_lt_2p64[of x]
      uint_nonnegative[of y] uint_lt_2p64[of y]
      uint_nonnegative[of c] assms by linarith+
  have powers: "(2::int)^65 = 2 * 2^64" by simp
  have positive: "0 < (2::int)^64" by simp
  have high:
    "((uint x - uint y - uint c) mod (2::int)^65) div 2^64 mod 2 =
      1 - ((2^64 + (uint x - uint y - uint c)) div 2^64)"
  proof (cases "uint x - uint y - uint c < 0")
    case False
    have low: "0 \<le> uint x - uint y - uint c" using False by simp
    have small: "uint x - uint y - uint c < (2::int)^65"
      using bounds by (simp_all; linarith)
    show ?thesis
      using low bounds small by (simp add: div_add_self1)
  next
    case True
    let ?d = "uint x - uint y - uint c"
    have rem: "?d mod (2::int)^65 = 2^65 + ?d"
      by (rule int_mod_pos_eq[where q = "-1"])
        (use bounds True powers positive in linarith)+
    have quot: "((2::int)^65 + ?d) div 2^64 = 1"
      by (rule int_div_pos_eq[where r = "2^64 + ?d"])
        (use bounds True powers positive in linarith)+
    have small: "0 \<le> (2::int)^64 + ?d" "(2::int)^64 + ?d < 2^64"
      using bounds True by linarith+
    show ?thesis using small rem quot by simp
  qed
  show ?thesis
    unfolding smt_sub64_def
    using sub64_result[of x y c] borrow high by simp
qed

lemma smt_add64_zero:
  "smt_add64 (uint x) (uint y) 0 =
    (uint (fst (Add64_carry x y 0)), uint (snd (Add64_carry x y 0)))"
  using smt_add64_correct[of "0 :: u64" x y] by simp

lemma smt_sub64_zero:
  "smt_sub64 (uint x) (uint y) 0 =
    (uint (fst (Sub64_borrow x y 0)), uint (snd (Sub64_borrow x y 0)))"
  using smt_sub64_correct[of "0 :: u64" x y] by simp

text \<open>Four-limb composition follows the production constructors.  The
  final carry or borrow is discarded, as in EVM arithmetic.\<close>

definition smt_add256 :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
  "smt_add256 x y = (
    let (r0, c0) = smt_add64 (uint (z0 x)) (uint (z0 y)) 0;
        (r1, c1) = smt_add64 (uint (z1 x)) (uint (z1 y)) c0;
        (r2, c2) = smt_add64 (uint (z2 x)) (uint (z2 y)) c1;
        (r3, c3) = smt_add64 (uint (z3 x)) (uint (z3 y)) c2
    in \<lparr>z0 = word_of_int r0, z1 = word_of_int r1,
          z2 = word_of_int r2, z3 = word_of_int r3\<rparr>)"

definition smt_sub256 :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
  "smt_sub256 x y = (
    let (r0, c0) = smt_sub64 (uint (z0 x)) (uint (z0 y)) 0;
        (r1, c1) = smt_sub64 (uint (z1 x)) (uint (z1 y)) c0;
        (r2, c2) = smt_sub64 (uint (z2 x)) (uint (z2 y)) c1;
        (r3, c3) = smt_sub64 (uint (z3 x)) (uint (z3 y)) c2
    in \<lparr>z0 = word_of_int r0, z1 = word_of_int r1,
          z2 = word_of_int r2, z3 = word_of_int r3\<rparr>)"

lemma smt_add256_correct:
  "smt_add256 x y = uint256_add x y"
  unfolding smt_add256_def uint256_add_def
  by (simp add: case_prod_unfold Let_def smt_add64_zero smt_add64_correct smt_add64_carry_lt2)

lemma smt_sub256_correct:
  "smt_sub256 x y = uint256_sub x y"
  unfolding smt_sub256_def uint256_sub_def
  by (simp add: case_prod_unfold Let_def smt_sub64_zero smt_sub64_correct sub64_borrow_lt)

end
