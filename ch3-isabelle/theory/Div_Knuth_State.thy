theory Div_Knuth_State
  imports Div_Submul Div_Knuth_Arithmetic
begin

lemma getword_u_update_same:
  assumes "i \<le> 4"
  shows "getword_u (fst (update_word_u4 x x4 i w)) i (snd (update_word_u4 x x4 i w)) = w"
  using assms
  by (auto simp: update_word_u4_def update_word_uint256_def getword_u_def getword_def)

lemma getword_u_update_other:
  assumes "i \<le> 4" "k \<le> 4" "i \<noteq> k"
  shows "getword_u (fst (update_word_u4 x x4 i w)) k (snd (update_word_u4 x x4 i w)) = getword_u x k x4"
  using assms
  by (auto simp: update_word_u4_def update_word_uint256_def getword_u_def getword_def)

lemma subMulTo_aux_preserves_high:
  assumes "n \<le> dLen y" "j + dLen y \<le> k" "k \<le> 4"
  shows "getword_u (fst (snd (subMulTo_aux x x4 y q n j borrow))) k
       (snd (snd (subMulTo_aux x x4 y q n j borrow))) = getword_u x k x4"
  using assms
proof (induction n arbitrary: x x4 borrow)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?i = "dLen y - Suc n + j"
  let ?s = "fst (Sub64_borrow (getword_u x ?i x4) borrow 0)"
  let ?c1 = "snd (Sub64_borrow (getword_u x ?i x4) borrow 0)"
  let ?p = "mul64 (getword y (dLen y - Suc n)) q"
  let ?t = "fst (Sub64_borrow ?s (snd ?p) 0)"
  let ?c2 = "snd (Sub64_borrow ?s (snd ?p) 0)"
  let ?new = "update_word_u4 x x4 ?i ?t"
  have small: "?i < k" using Suc.prems by arith
  have same: "getword_u (fst ?new) k (snd ?new) = getword_u x k x4"
    by (rule getword_u_update_other) (use small Suc.prems in auto)
  have ih: "getword_u (fst (snd (subMulTo_aux (fst ?new) (snd ?new) y q n j (fst ?p + ?c1 + ?c2)))) k
       (snd (snd (subMulTo_aux (fst ?new) (snd ?new) y q n j (fst ?p + ?c1 + ?c2)))) = getword_u x k x4"
    using Suc.IH[of "fst ?new" "snd ?new" "fst ?p + ?c1 + ?c2"] Suc.prems same by simp
  show ?case
    using ih by (simp only: subMulTo_aux.simps Let_def case_prod_unfold)
qed

lemma addTo_aux_preserves_high:
  assumes "n \<le> dLen y" "j + dLen y \<le> k" "k \<le> 4"
  shows "getword_u (fst (snd (addTo_aux x x4 y n j carry))) k
       (snd (snd (addTo_aux x x4 y n j carry))) = getword_u x k x4"
  using assms
proof (induction n arbitrary: x x4 carry)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?i = "dLen y - Suc n + j"
  let ?sum = "Add64_carry (getword_u x ?i x4) (getword y (dLen y - Suc n)) carry"
  let ?new = "update_word_u4 x x4 ?i (fst ?sum)"
  have small: "?i < k" using Suc.prems by arith
  have same: "getword_u (fst ?new) k (snd ?new) = getword_u x k x4"
    by (rule getword_u_update_other) (use small Suc.prems in auto)
  have ih: "getword_u (fst (snd (addTo_aux (fst ?new) (snd ?new) y n j (snd ?sum)))) k
       (snd (snd (addTo_aux (fst ?new) (snd ?new) y n j (snd ?sum)))) = getword_u x k x4"
    using Suc.IH[of "fst ?new" "snd ?new" "snd ?sum"] Suc.prems same by simp
  show ?case
    using ih by (simp only: addTo_aux.simps Let_def case_prod_unfold)
qed

lemma subMulTo_preserves_high:
  assumes "j + dLen y \<le> k" "k \<le> 4" "subMulTo x x4 y j q = (b,x',x4')"
  shows "getword_u x' k x4' = getword_u x k x4"
  using subMulTo_aux_preserves_high[of "dLen y" y j k x x4 q 0] assms
  by (simp add: subMulTo_def)

lemma addTo_preserves_high:
  assumes "j + dLen y \<le> k" "k \<le> 4" "addTo x x4 y j = (b,x',x4')"
  shows "getword_u x' k x4' = getword_u x k x4"
  using addTo_aux_preserves_high[of "dLen y" y j k x x4 0] assms
  by (simp add: addTo_def)

lemma uint_radix_strip:
  fixes w :: u64 and t :: int
  shows "(uint w + 2^64 * t) div 2^64 = t"
  using uint_lt_2p64[of w] uint_nonnegative[of w]
  by (simp add: div_pos_pos_trivial)

lemma uint_radix_strip_power:
  fixes w :: u64 and t :: int
  shows "(uint w + 2^64 * t) div (2^64)^Suc k = t div (2^64)^k"
  apply (simp only: power_Suc)
  apply (subst zdiv_zmult2_eq)
   apply simp
  by (simp only: uint_radix_strip)

lemma uint256_u4_horner:
  "uint256_u4_to_int (x,x4) = uint (z0 x) + 2^64 *
       (uint (z1 x) + 2^64 * (uint (z2 x) + 2^64 * (uint (z3 x) + 2^64 * uint x4)))"
  by (simp add: uint256_u4_to_int_def uint256_to_int_def Let_def int_shiftl_eq_mult algebra_simps)

lemma uint256_u4_div_radix:
  assumes "k \<le> 4"
  shows "uint256_u4_to_int (x,x4) div (2^64)^k =
    (if k=0 then uint256_u4_to_int (x,x4)
     else if k=1 then uint (z1 x) + 2^64 * (uint (z2 x) + 2^64 * (uint (z3 x) + 2^64 * uint x4))
     else if k=2 then uint (z2 x) + 2^64 * (uint (z3 x) + 2^64 * uint x4)
     else if k=3 then uint (z3 x) + 2^64 * uint x4
     else uint x4)"
proof -
  have "k=0 \<or> k=Suc 0 \<or> k=Suc (Suc 0) \<or> k=Suc (Suc (Suc 0)) \<or> k=Suc (Suc (Suc (Suc 0)))" using assms by arith
  then show ?thesis
    by (elim disjE; simp only: uint256_u4_horner uint_radix_strip_power; simp)
qed

lemma uint256_u4_high_equal:
  assumes k: "k \<le> 4"
    and same: "\<And>i. k \<le> i \<Longrightarrow> i \<le> 4 \<Longrightarrow> getword_u x' i x4' = getword_u x i x4"
  shows "uint256_u4_to_int (x',x4') div (2^64)^k = uint256_u4_to_int (x,x4) div (2^64)^k"
proof -
  have "k=0 \<or> k=1 \<or> k=2 \<or> k=3 \<or> k=4" using k by arith
  then show ?thesis
    unfolding uint256_u4_div_radix[OF k]
    using same[of 0] same[of 1] same[of 2] same[of 3] same[of 4]
    by (elim disjE; simp add: getword_u_def getword_def uint256_u4_horner)
qed

lemma subMulTo_preserves_high_value:
  assumes index: "j + dLen y \<le> 4" and res: "subMulTo x x4 y j q = (b,x',x4')"
  shows "uint256_u4_to_int (x',x4') div (2^64)^(j+dLen y) =
         uint256_u4_to_int (x,x4) div (2^64)^(j+dLen y)"
proof (rule uint256_u4_high_equal[OF index])
  fix i
  assume "j + dLen y \<le> i" "i \<le> 4"
  then show "getword_u x' i x4' = getword_u x i x4"
    by (rule subMulTo_preserves_high[OF _ _ res])
qed

lemma addTo_preserves_high_value:
  assumes index: "j + dLen y \<le> 4" and res: "addTo x x4 y j = (b,x',x4')"
  shows "uint256_u4_to_int (x',x4') div (2^64)^(j+dLen y) =
         uint256_u4_to_int (x,x4) div (2^64)^(j+dLen y)"
proof (rule uint256_u4_high_equal[OF index])
  fix i
  assume "j + dLen y \<le> i" "i \<le> 4"
  then show "getword_u x' i x4' = getword_u x i x4"
    by (rule addTo_preserves_high[OF _ _ res])
qed


lemma uint_mod_radix:
  "uint (w::u64) mod 2^64 = uint w"
  using uint_lt_2p64[of w] uint_nonnegative[of w]
  by (simp add: mod_pos_pos_trivial)

lemma uint_radix_digit:
  fixes w :: u64 and t :: int
  shows "(uint w + 2^64 * t) mod 2^64 = uint w"
  by (simp only: mod_mult_self2 uint_mod_radix)

lemma uint256_u4_digit:
  assumes k: "k \<le> 4"
  shows "uint (getword_u x k x4) = (uint256_u4_to_int (x,x4) div (2^64)^k) mod 2^64"
proof -
  let ?V = "uint256_u4_to_int (x,x4)"
  have q0: "?V div (2^64)^0 = uint (z0 x) + 2^64 *
      (uint (z1 x) + 2^64 * (uint (z2 x) + 2^64 * (uint (z3 x) + 2^64 * uint x4)))"
    by (simp only: power_0 div_by_1 uint256_u4_horner)
  have q1: "?V div (2^64)^1 = uint (z1 x) + 2^64 * (uint (z2 x) + 2^64 * (uint (z3 x) + 2^64 * uint x4))"
    using uint256_u4_div_radix[of 1 x x4] by simp
  have q2: "?V div (2^64)^2 = uint (z2 x) + 2^64 * (uint (z3 x) + 2^64 * uint x4)"
    using uint256_u4_div_radix[of 2 x x4] by simp
  have q3: "?V div (2^64)^3 = uint (z3 x) + 2^64 * uint x4"
    using uint256_u4_div_radix[of 3 x x4] by simp
  have q4: "?V div (2^64)^4 = uint x4"
    using uint256_u4_div_radix[of 4 x x4] by simp
  have d0: "uint (z0 x) = (?V div (2^64)^0) mod 2^64"
    by (simp only: q0 uint_radix_digit)
  have d1: "uint (z1 x) = (?V div (2^64)^1) mod 2^64"
    by (simp only: q1 uint_radix_digit)
  have d2: "uint (z2 x) = (?V div (2^64)^2) mod 2^64"
    by (simp only: q2 uint_radix_digit)
  have d3: "uint (z3 x) = (?V div (2^64)^3) mod 2^64"
    by (simp only: q3 uint_radix_digit)
  have d4: "uint x4 = (?V div (2^64)^4) mod 2^64"
    by (simp only: q4 uint_mod_radix)
  have "k=0 \<or> k=1 \<or> k=2 \<or> k=3 \<or> k=4" using k by arith
  then show ?thesis
  proof (elim disjE)
    assume e: "k=0"
    have g: "getword_u x 0 x4 = z0 x" by (simp add: getword_u_def getword_def)
    show ?thesis unfolding e g by (rule d0)
  next
    assume e: "k=1"
    have g: "getword_u x 1 x4 = z1 x" by (simp add: getword_u_def getword_def)
    show ?thesis unfolding e g by (rule d1)
  next
    assume e: "k=2"
    have g: "getword_u x 2 x4 = z2 x" by (simp add: getword_u_def getword_def)
    show ?thesis unfolding e g by (rule d2)
  next
    assume e: "k=3"
    have g: "getword_u x 3 x4 = z3 x" by (simp add: getword_u_def getword_def)
    show ?thesis unfolding e g by (rule d3)
  next
    assume e: "k=4"
    have g: "getword_u x 4 x4 = x4" by (simp add: getword_u_def getword_def)
    show ?thesis unfolding e g by (rule d4)
  qed
qed

lemma uint256_u4_nonnegative:
  "0 \<le> uint256_u4_to_int (x,x4)"
  by (simp add: uint256_u4_horner)

lemma uint256_u4_high_zero:
  assumes bound: "uint256_u4_to_int (x,x4) < (2^64)^K"
    and Ki: "K \<le> i" and i: "i \<le> 4"
  shows "getword_u x i x4 = 0"
proof -
  have power: "((2::int)^64)^K \<le> (2^64)^i"
    by (rule power_increasing[OF Ki]) simp
  have high: "uint256_u4_to_int (x,x4) div (2^64)^i = 0"
    by (rule div_pos_pos_trivial[OF uint256_u4_nonnegative]) (use bound power in linarith)
  have "uint (getword_u x i x4) = 0"
    by (simp only: uint256_u4_digit[OF i] high; simp)
  then show ?thesis by (simp only: uint_0_iff)
qed

lemma uint256_u4_top_digit:
  assumes index: "i \<le> 4"
    and bound: "uint256_u4_to_int (x,x4) < (2^64)^Suc i"
  shows "uint (getword_u x i x4) = uint256_u4_to_int (x,x4) div (2^64)^i"
proof -
  have pos: "0 < ((2::int)^64)^i" by simp
  have high_lt: "uint256_u4_to_int (x,x4) div (2^64)^i < 2^64"
  proof (rule ccontr)
    assume "\<not> uint256_u4_to_int (x,x4) div (2^64)^i < 2^64"
    then have ge: "2^64 \<le> uint256_u4_to_int (x,x4) div (2^64)^i" by simp
    have mul: "2^64 * ((2::int)^64)^i \<le> (uint256_u4_to_int (x,x4) div (2^64)^i) * (2^64)^i"
      by (rule mult_right_mono[OF ge]) simp
    have rem_ge: "0 \<le> uint256_u4_to_int (x,x4) mod (2^64)^i" by simp
    have split: "(uint256_u4_to_int (x,x4) div (2^64)^i) * (2^64)^i + uint256_u4_to_int (x,x4) mod (2^64)^i = uint256_u4_to_int (x,x4)" by (rule div_mult_mod_eq)
    show False using bound mul rem_ge split unfolding power_Suc by linarith
  qed
  have high_ge: "0 \<le> uint256_u4_to_int (x,x4) div (2^64)^i"
    using uint256_u4_nonnegative[of x x4] pos by (simp add: pos_imp_zdiv_nonneg_iff)
  show ?thesis
    by (simp only: uint256_u4_digit[OF index] mod_pos_pos_trivial[OF high_ge high_lt])
qed

end
