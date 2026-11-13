theory Div_Knuth_Decomposition
  imports Div_Knuth_State
begin

lemma radix_two_split:
  fixes N B W :: int
  assumes B: "0 \<le> B"
  shows "N = ((N div (B*W))*B + (N div W) mod B)*W + N mod W"
proof -
  have outer: "(N div W)*W + N mod W=N" by simp
  have inner: "((N div W) div B)*B + (N div W) mod B=N div W" by simp
  have divide: "(N div W) div B = N div (B*W)"
    by (subst mult.commute) (rule zdiv_zmult2_eq[OF B, symmetric])
  show ?thesis by (simp only: inner[unfolded divide] outer)
qed

lemma radix_three_split:
  fixes N B W :: int
  assumes B: "0 \<le> B"
  shows "N = ((N div (B*B*W))*B + (N div (B*W)) mod B)*(B*W) +
    (N div W mod B)*W + N mod W"
proof -
  have split1: "N = (N div (B*W))*(B*W) + (N div W mod B)*W + N mod W"
    using radix_two_split[OF B, where N=N and W=W] by (simp add: algebra_simps)
  have divide: "N div (B*B*W) = (N div (B*W)) div B"
    using zdiv_zmult2_eq[OF B, of N "B*W"] by (simp only: mult_ac)
  have split2: "(N div (B*W)) = (N div (B*B*W))*B + (N div (B*W)) mod B"
    by (simp only: divide; simp)
  note scaled = arg_cong[where f="\<lambda>v::int. v*(B*W)", OF split2]
  show ?thesis using split1 scaled by linarith
qed
lemma uint256_u4_three_digits:
  assumes lo: "2 \<le> k" and hi: "k \<le> 4"
    and bound: "uint256_u4_to_int (x,x4) < (2^64)^Suc k"
  shows "uint256_u4_to_int (x,x4) =
    (uint (getword_u x k x4)*2^64 + uint (getword x (k-1)))*(2^64*(2^64)^(k-2)) +
    uint (getword x (k-2))*(2^64)^(k-2) +
    uint256_u4_to_int (x,x4) mod (2^64)^(k-2)"
proof -
  let ?N = "uint256_u4_to_int (x,x4)"
  let ?B = "(2::int)^64"
  have k1: "k-1 < 4" and k2: "k-2 < 4" using lo hi by arith+
  have e1: "k-1 = Suc (k-2)" and e2: "k = Suc (Suc (k-2))" using lo by arith+
  have p1: "?B*?B^(k-2) = ?B^(k-1)" by (simp only: e1 power_Suc)
  have p2: "?B*?B*?B^(k-2) = ?B^k" by (subst (2) e2) (simp only: power_Suc mult.assoc)
  have top: "uint (getword_u x k x4) = ?N div ?B^k"
    by (rule uint256_u4_top_digit[OF hi bound])
  have mid: "uint (getword x (k-1)) = (?N div ?B^(k-1)) mod ?B"
    using uint256_u4_digit[OF less_imp_le[OF k1], of x x4]
    by (simp only: getword_u_def if_P[OF k1])
  have low: "uint (getword x (k-2)) = (?N div ?B^(k-2)) mod ?B"
    using uint256_u4_digit[OF less_imp_le[OF k2], of x x4]
    by (simp only: getword_u_def if_P[OF k2])
  show ?thesis using radix_three_split[where N="?N" and B="?B" and W="?B^(k-2)"]
    by (simp only: p1 p2 top mid low; simp)
qed

lemma uint256_two_digits:
  assumes lo: "2 \<le> m" and hi: "m \<le> 4"
    and bound: "uint256_to_int d < (2^64)^m"
  shows "uint256_to_int d =
    (uint (getword d (m-1))*2^64 + uint (getword d (m-2)))*(2^64)^(m-2) +
    uint256_to_int d mod (2^64)^(m-2)"
proof -
  let ?D = "uint256_to_int d"
  let ?B = "(2::int)^64"
  have m1: "m-1 < 4" and m2: "m-2 < 4" using lo hi by arith+
  have e1: "m-1 = Suc (m-2)" and e2: "Suc (m-1)=m" using lo by arith+
  have p1: "?B*?B^(m-2) = ?B^(m-1)" by (simp only: e1 power_Suc)
  have ext: "uint256_u4_to_int (d,0) = ?D" by (simp add: uint256_u4_to_int_def)
  have db: "uint256_u4_to_int (d,0) < ?B^Suc (m-1)"
    using bound by (simp only: ext e2)
  have top: "uint (getword d (m-1)) = ?D div ?B^(m-1)"
    using uint256_u4_top_digit[OF less_imp_le[OF m1] db]
    by (simp only: getword_u_def if_P[OF m1] ext)
  have low: "uint (getword d (m-2)) = (?D div ?B^(m-2)) mod ?B"
    using uint256_u4_digit[OF less_imp_le[OF m2], of d 0]
    by (simp only: getword_u_def if_P[OF m2] ext)
  show ?thesis using radix_two_split[where N="?D" and B="?B" and W="?B^(m-2)"]
    by (simp only: p1 top low; simp)
qed

lemma knuth_divisor_digits:
  fixes m j :: nat and d :: uint256 and W dt :: int
  assumes lo: "2 \<le> m" and hi: "m \<le> 4"
    and bound: "uint256_to_int d < (2^64)^m"
  defines "W \<equiv> (2::int)^(64*(j+m-2))"
    and "dt \<equiv> (uint256_to_int d mod (2^64)^(m-2))*(2^64)^j"
  shows "uint256_to_int d*(2^64)^j =
      uint (getword d (m-1))*(2^64*W) + uint (getword d (m-2))*W + dt"
    and "0 \<le> dt" and "dt < W"
proof -
  let ?B = "(2::int)^64"
  have exp: "j+m-2 = (m-2)+j" using lo by arith
  have wp: "W = ?B^(m-2)*?B^j"
    unfolding W_def exp by (simp add: power_mult power_add)
  note split = arg_cong[where f="\<lambda>v::int. v*?B^j", OF uint256_two_digits[OF lo hi bound]]
  show "uint256_to_int d*?B^j = uint (getword d (m-1))*(?B*W) + uint (getword d (m-2))*W + dt"
    using split unfolding wp dt_def by (simp add: algebra_simps)
  have rg: "0 \<le> uint256_to_int d mod ?B^(m-2)" "uint256_to_int d mod ?B^(m-2) < ?B^(m-2)"
    by simp_all
  show "0 \<le> dt" unfolding dt_def using rg by simp
  show "dt < W" unfolding dt_def wp by (rule mult_strict_right_mono[OF rg(2)]) simp
qed

end
