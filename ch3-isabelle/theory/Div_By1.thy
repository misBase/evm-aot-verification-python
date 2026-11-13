theory Div_By1
  imports Div64 Div_Reciprocal
begin

lemma reciprocal2by1_bounds:
  fixes d :: u64
  assumes normalized: "2^63 \<le> uint d"
  shows "(2^64+uint (reciprocal2by1 d))*uint d < (2^64)*(2^64)"
    and "(2^64)*(2^64) \<le> (2^64+uint (reciprocal2by1 d)+1)*uint d"
proof -
  let ?B = "(2::int)^64"
  let ?D = "uint d"
  let ?N = "uint (NOT d)*?B + uint ((2^64-1)::u64)"
  let ?q = "?N div ?D"
  have dpos: "0 < ?D" using normalized by (simp_all; linarith)
  have dnz: "d \<noteq> 0" using dpos by auto
  have not_d: "uint (NOT d) = ?B-1-?D"
  proof -
    have "uint (NOT d) = take_bit 64 (NOT (uint d))"
      by (simp add: unsigned_not_eq)
    also have "... = mask 64 - take_bit 64 (uint d)"
      by (rule take_bit_not_eq_mask_diff)
    also have "... = ?B-1-?D"
      using uint_nonnegative[of d] uint_lt2p[where 'a=64, of d]
      by (simp add: take_bit_int_eq_self mask_eq_exp_minus_1)
    finally show ?thesis .
  qed
  have maxval: "uint ((2^64-1)::u64) = ?B-1" by code_simp
  have hi: "uint (NOT d) < ?D" using not_d normalized by (simp_all; linarith)
  have hi_word: "NOT d < d" using hi by (simp add: word_less_alt)
  have div: "Div64 (NOT d) (2^64-1) d =
      Some (word_of_int ?q, word_of_int (?N mod ?D))"
    by (rule Div64_correct[OF dnz hi_word])
  have recip: "reciprocal2by1 d = word_of_int ?q"
    unfolding reciprocal2by1_def by (subst div) simp
  have n0: "0 \<le> ?N" by (simp add: uint_nonnegative)
  have nb: "?N < ?B*?D" using hi maxval by (simp_all; linarith)
  have q0: "0 \<le> ?q" using n0 dpos by (simp add: pos_imp_zdiv_nonneg_iff)
  have rm0: "0 \<le> ?N mod ?D" using dpos by (rule pos_mod_sign)
  have rmlt: "?N mod ?D < ?D" using dpos by (rule pos_mod_bound)
  have qr: "?q*?D + ?N mod ?D = ?N" by simp
  have "?q*?D < ?B*?D" using qr rm0 nb by linarith
  then have qb: "?q < ?B" using dpos by simp
  have uv: "uint (reciprocal2by1 d) = ?q"
    unfolding recip using q0 qb by (simp add: uint_word_of_int)
  show "(?B+uint (reciprocal2by1 d))*?D < ?B*?B"
    using qr rm0 unfolding uv not_d maxval by (simp only: algebra_simps; linarith)
  show "?B*?B \<le> (?B+uint (reciprocal2by1 d)+1)*?D"
    using qr rmlt unfolding uv not_d maxval by (simp only: algebra_simps; linarith)
qed

lemma uint_normalized_ge:
  fixes y :: u64
  assumes "y \<noteq> 0"
  shows "2^63 \<le> uint (y << LeadingZeros64 y)"
proof -
  have divbound: "2^31 \<le> unat (y << LeadingZeros64 y) div 2^32"
    using unat_yn1_ge_ax[OF assms] by (simp add: unat_shiftr_exact)
  have "(2::nat)^31 * 2^32 \<le> (unat (y << LeadingZeros64 y) div 2^32) * 2^32"
    by (rule mult_right_mono[OF divbound]) simp
  also have "... \<le> unat (y << LeadingZeros64 y)" by simp
  finally have b: "(2::nat)^63 \<le> unat (y << LeadingZeros64 y)" by simp
  have "int ((2::nat)^63) \<le> int (unat (y << LeadingZeros64 y))"
    using b by (simp only: of_nat_le_iff)
  then show ?thesis by (simp only: uint_nat of_nat_power of_nat_numeral)
qed


fun limb_list_value :: "u64 list \<Rightarrow> int" where
  "limb_list_value [] = 0"
| "limb_list_value (x # xs) = uint x + 2^64 * limb_list_value xs"

fun by1_digits :: "u64 list \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 list \<times> u64" where
  "by1_digits [] h d v = ([], h)"
| "by1_digits (x # xs) h d v =
    (let (qs, rh) = by1_digits xs h d v;
         (q, r) = udivrem2by1 rh x d v
     in (q # qs, r))"

lemma by1_digits_correct:
  assumes step: "\<And>h l. uint h < uint d \<Longrightarrow>
    uint h * 2^64 + uint l =
      uint (fst (udivrem2by1 h l d v)) * uint d + uint (snd (udivrem2by1 h l d v)) \<and>
    uint (snd (udivrem2by1 h l d v)) < uint d"
    and high: "uint h < uint d"
  shows "limb_list_value xs + (2^64) ^ length xs * uint h =
      limb_list_value (fst (by1_digits xs h d v)) * uint d + uint (snd (by1_digits xs h d v)) \<and>
    uint (snd (by1_digits xs h d v)) < uint d"
proof (induction xs)
  case Nil
  then show ?case using high by simp
next
  case (Cons l ls)
  obtain qs rh where tail: "by1_digits ls h d v = (qs, rh)"
    by (cases "by1_digits ls h d v") auto
  obtain q r where head: "udivrem2by1 rh l d v = (q, r)"
    by (cases "udivrem2by1 rh l d v") auto
  have tail_eq: "limb_list_value ls + (2^64) ^ length ls * uint h =
      limb_list_value qs * uint d + uint rh"
    and rh_lt: "uint rh < uint d"
    using Cons.IH unfolding tail by simp_all
  have head_eq: "uint rh * 2^64 + uint l = uint q * uint d + uint r"
    and r_lt: "uint r < uint d"
    using step[OF rh_lt, of l] unfolding head by simp_all
  have out: "by1_digits (l # ls) h d v = (q # qs, r)"
    by (simp add: tail head)
  show ?case
    using tail_eq head_eq r_lt
    unfolding out
    by (simp_all add: algebra_simps power_add; linarith)
qed


definition uint256_limbs :: "uint256 \<Rightarrow> u64 list" where
  "uint256_limbs x = [z0 x,z1 x,z2 x,z3 x]"

fun limb_nth :: "u64 list \<Rightarrow> nat \<Rightarrow> u64" where
  "limb_nth [] n = 0"
| "limb_nth (x # xs) 0 = x"
| "limb_nth (x # xs) (Suc n) = limb_nth xs n"

definition limbs_uint256 :: "u64 list \<Rightarrow> uint256" where
  "limbs_uint256 xs = \<lparr>z0=limb_nth xs 0, z1=limb_nth xs 1,
    z2=limb_nth xs 2, z3=limb_nth xs 3\<rparr>"

lemma by1_digits_length:
  "length (fst (by1_digits xs h d v)) = length xs"
  by (induction xs) (auto simp add: Let_def split: prod.splits)

lemma limbs_uint256_value:
  assumes "length xs \<le> 4"
  shows "uint256_to_int (limbs_uint256 xs) = limb_list_value xs"
  using assms
  by (cases xs; cases "tl xs"; cases "tl (tl xs)"; cases "tl (tl (tl xs))";
    cases "tl (tl (tl (tl xs)))";
    auto simp: limbs_uint256_def uint256_to_int_def Let_def int_shiftl_eq_mult algebra_simps numeral_eq_Suc)

lemma by1_loop_as_digits:
  assumes "n < 4"
  shows "udivremBy1_loop uint256_zero u n h d v =
    (limbs_uint256 (fst (by1_digits (take (Suc n) (uint256_limbs u)) h d v)),
      snd (by1_digits (take (Suc n) (uint256_limbs u)) h d v))"
proof -
  have "n=0 \<or> n=1 \<or> n=2 \<or> n=3" using assms by linarith
  then show ?thesis
    by (elim disjE; simp add: uint256_limbs_def limbs_uint256_def
      uint256_zero_def update_word_uint256_def getword_def Let_def split_def numeral_eq_Suc)
qed

lemma by1_input_representation:
  fixes u :: uint256 and u4 d :: u64 and n :: nat
  assumes count: "0 < n" "n \<le> 4"
    and bound: "uint256_to_int u + uint u4 * 2^256 < uint d * (2^64)^n"
  shows "uint256_to_int u + uint u4 * 2^256 =
      limb_list_value (take n (uint256_limbs u)) + (2^64)^n * uint (getword_u u n u4)"
    and "uint (getword_u u n u4) < uint d"
proof -
  have counts: "n=1 \<or> n=2 \<or> n=3 \<or> n=4" using count by linarith
  have nn: "0 \<le> uint (z0 u)" "0 \<le> uint (z1 u)" "0 \<le> uint (z2 u)"
    "0 \<le> uint (z3 u)" "0 \<le> uint u4" by (simp_all add: uint_nonnegative)
  have integral: "uint (z2 u) = 0 \<or> 1 \<le> uint (z2 u)"
    "uint (z3 u) = 0 \<or> 1 \<le> uint (z3 u)"
    "uint u4 = 0 \<or> 1 \<le> uint u4" using nn by presburger+
  have db: "uint d < 2^64" by (rule uint_lt_2p64)
  show "uint256_to_int u + uint u4 * 2^256 =
      limb_list_value (take n (uint256_limbs u)) + (2^64)^n * uint (getword_u u n u4)"
    using counts bound nn db
    unfolding uint256_to_int_def uint256_limbs_def getword_u_def getword_def Let_def
    apply (elim disjE)
    apply (simp_all add: int_shiftl_eq_mult algebra_simps numeral_eq_Suc)
    apply (insert nn integral)
    by ((elim disjE; linarith)+)
  show "uint (getword_u u n u4) < uint d"
    using counts bound nn db
    unfolding uint256_to_int_def getword_u_def getword_def Let_def
    apply (elim disjE)
    apply (simp_all add: int_shiftl_eq_mult algebra_simps numeral_eq_Suc)
    apply (insert nn integral)
    by ((elim disjE; linarith)+)
qed

lemma udivremBy1_correct_from_step:
  fixes u :: uint256 and u4 d v :: u64 and n :: nat
  assumes step: "\<And>h l. uint h < uint d \<Longrightarrow>
    uint h * 2^64 + uint l =
      uint (fst (udivrem2by1 h l d v)) * uint d + uint (snd (udivrem2by1 h l d v)) \<and>
    uint (snd (udivrem2by1 h l d v)) < uint d"
    and count: "0 < n" "n \<le> 4"
    and bound: "uint256_to_int u + uint u4 * 2^256 < uint d * (2^64)^n"
  shows "uint256_to_int (fst (udivremBy1_loop uint256_zero u (n-1) (getword_u u n u4) d v)) =
      (uint256_to_int u + uint u4 * 2^256) div uint d \<and>
    uint (snd (udivremBy1_loop uint256_zero u (n-1) (getword_u u n u4) d v)) =
      (uint256_to_int u + uint u4 * 2^256) mod uint d"
proof -
  let ?xs = "take n (uint256_limbs u)"
  let ?h = "getword_u u n u4"
  let ?N = "uint256_to_int u + uint u4 * 2^256"
  have len: "length ?xs = n" using count by (simp add: uint256_limbs_def)
  have rep: "?N = limb_list_value ?xs + (2^64)^n * uint ?h"
    and high: "uint ?h < uint d"
    using by1_input_representation[OF count bound] by auto
  have loop: "udivremBy1_loop uint256_zero u (n-1) ?h d v =
      (limbs_uint256 (fst (by1_digits ?xs ?h d v)), snd (by1_digits ?xs ?h d v))"
    using by1_loop_as_digits[of "n-1" u ?h d v] count by simp
  obtain qs r where out: "by1_digits ?xs ?h d v = (qs,r)"
    by (cases "by1_digits ?xs ?h d v") auto
  have qlen: "length qs \<le> 4" using by1_digits_length[of ?xs ?h d v] out len count by simp
  have qval: "uint256_to_int (limbs_uint256 qs) = limb_list_value qs"
    by (rule limbs_uint256_value[OF qlen])
  have equation: "?N = limb_list_value qs * uint d + uint r"
    and rem: "uint r < uint d"
    using by1_digits_correct[OF step high, of ?xs] rep len out by simp_all
  have nonneg: "0 \<le> uint r" by (rule uint_nonnegative)
  have rdiv: "uint r div uint d = 0" and rmod: "uint r mod uint d = uint r"
    using nonneg rem by (simp_all add: div_pos_pos_trivial mod_pos_pos_trivial)
  have dpos: "0 < uint d" using nonneg rem by linarith
  show ?thesis
    unfolding loop out
    using qval equation rdiv rmod dpos
    by (simp add: equation)
qed

ML \<open>
val _ = if null (Thm_Deps.all_oracles @{thms by1_digits_correct by1_loop_as_digits}) then () else error "oracle"
\<close>

lemma udivremBy1_correct:
  fixes un :: uint256 and u4 dn :: u64 and ulen :: nat
  assumes normalized: "2^63 \<le> uint dn"
    and count: "0 < ulen" "ulen \<le> 4"
    and bound: "uint256_to_int un + uint u4 * 2^256 < uint dn * (2^64)^ulen"
  shows "uint256_to_int (fst (udivremBy1 uint256_zero un ulen dn u4)) =
      (uint256_to_int un + uint u4 * 2^256) div uint dn \<and>
    uint (snd (udivremBy1 uint256_zero un ulen dn u4)) =
      (uint256_to_int un + uint u4 * 2^256) mod uint dn"
proof -
  let ?v = "reciprocal2by1 dn"
  have dpos: "0 < uint dn" using normalized by (simp_all; linarith)
  have lower: "(2^64+uint ?v)*uint dn < (2^64)*(2^64)"
    and upper: "(2^64)*(2^64) \<le> (2^64+uint ?v+1)*uint dn"
    using reciprocal2by1_bounds[OF normalized] by auto
  have step: "\<And>h l. uint h < uint dn \<Longrightarrow>
      uint h * 2^64 + uint l =
        uint (fst (udivrem2by1 h l dn ?v)) * uint dn + uint (snd (udivrem2by1 h l dn ?v)) \<and>
      uint (snd (udivrem2by1 h l dn ?v)) < uint dn"
  proof -
    fix h l :: u64
    assume high: "uint h < uint dn"
    have eq: "uint (fst (udivrem2by1 h l dn ?v)) = (uint h*2^64+uint l) div uint dn"
      and rm: "uint (snd (udivrem2by1 h l dn ?v)) = (uint h*2^64+uint l) mod uint dn"
      using udivrem2by1_correct_reciprocal[OF normalized high lower upper, of l] by auto
    show "uint h * 2^64 + uint l =
        uint (fst (udivrem2by1 h l dn ?v)) * uint dn + uint (snd (udivrem2by1 h l dn ?v)) \<and>
      uint (snd (udivrem2by1 h l dn ?v)) < uint dn"
      unfolding eq rm using dpos by simp
  qed
  show ?thesis
    using udivremBy1_correct_from_step[OF step count bound]
    by (simp add: udivremBy1_def Let_def)
qed

lemma udivremBy1_zero_counts:
  "udivremBy1 uint256_zero uint256_zero 0 d 0 =
    udivremBy1 uint256_zero uint256_zero 1 d 0"
  by (simp add: udivremBy1_def getword_u_def getword_def uint256_zero_def Let_def)

ML \<open>
val _ = if null (Thm_Deps.all_oracles @{thms udivremBy1_correct}) then () else error "By1 oracle"
\<close>
end
