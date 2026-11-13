theory Div_Denormalization
  imports Div_LenLower Div_Knuth_State
begin

lemma normalized_word_lower:
  fixes y :: u64
  assumes "y \<noteq> 0"
  shows "2^63 \<le> uint (y << LeadingZeros64 y)"
proof -
  have high: "2^31 \<le> unat (y << LeadingZeros64 y) div 2^32"
    using unat_yn1_ge_ax[OF assms] by (simp add: unat_shiftr_exact)
  have "(2::nat)^31 * 2^32 \<le> unat (y << LeadingZeros64 y) div 2^32 * 2^32"
    by (rule mult_right_mono[OF high]) simp
  also have "... \<le> unat (y << LeadingZeros64 y)" by simp
  finally have lower: "2^63 \<le> unat (y << LeadingZeros64 y)" by simp
  have "int (2^63) \<le> int (unat (y << LeadingZeros64 y))"
    using lower by (simp only: of_nat_le_iff)
  then show ?thesis by (simp only: of_nat_power of_nat_numeral uint_nat[symmetric])
qed

lemma normalized_join_lower:
  fixes hi lo :: u64
  assumes "hi \<noteq> 0"
  shows "2^63 \<le> uint ((hi << LeadingZeros64 hi) OR (lo >> (64-LeadingZeros64 hi)))"
  using normalized_word_lower[OF assms] uint_nonnegative[of "lo >> (64-LeadingZeros64 hi)"]
  by (simp only: uint_join_shift[OF LeadingZeros64_lt_64[OF assms]]; linarith)

lemma normalized_word_nonzero:
  fixes y :: u64
  assumes "y \<noteq> 0"
  shows "y << LeadingZeros64 y \<noteq> 0"
  using normalized_word_lower[OF assms] by auto

lemma normalized_join_nonzero:
  fixes hi lo :: u64
  assumes "hi \<noteq> 0"
  shows "(hi << LeadingZeros64 hi) OR (lo >> (64-LeadingZeros64 hi)) \<noteq> 0"
  using normalized_join_lower[OF assms, of lo] by auto

lemma dnStorage_length_and_top:
  assumes nz: "d \<noteq> uint256_zero"
    and s: "s = LeadingZeros64 (getword d (dLen d-1))"
  shows "dLen (dnStorage d (dLen d) s) = dLen d \<and>
    2^63 \<le> uint (getword (dnStorage d (dLen d) s) (dLen d-1))"
proof (cases "z3 d=0")
  case False
  show ?thesis using s normalized_join_lower[OF False, of "z2 d"]
      normalized_join_nonzero[OF False, of "z2 d"] False
    by (simp add: dLen_def dnStorage_def getword_def)
next
  case True
  note z3 = True
  show ?thesis
  proof (cases "z2 d=0")
    case False
    show ?thesis using s z3 normalized_join_lower[OF False, of "z1 d"]
        normalized_join_nonzero[OF False, of "z1 d"] False
      by (simp add: dLen_def dnStorage_def getword_def)
  next
    case True
    note z2 = True
    show ?thesis
    proof (cases "z1 d=0")
      case False
      show ?thesis using s z3 z2 normalized_join_lower[OF False, of "z0 d"]
          normalized_join_nonzero[OF False, of "z0 d"] False
        by (simp add: dLen_def dnStorage_def getword_def)
    next
      case True
      have z0: "z0 d \<noteq> 0"
        using nz z3 z2 True by (auto simp: uint256_zero_def uint256.equality)
      show ?thesis using s z3 z2 True z0 normalized_word_lower[OF z0]
          normalized_word_nonzero[OF z0]
        by (simp add: dLen_def dnStorage_def getword_def)
    qed
  qed
qed

lemma dnStorage_dLen:
  assumes "d \<noteq> uint256_zero" "s = LeadingZeros64 (getword d (dLen d-1))"
  shows "dLen (dnStorage d (dLen d) s) = dLen d"
  using dnStorage_length_and_top[OF assms] by blast

lemma dnStorage_top_lower:
  assumes "d \<noteq> uint256_zero" "s = LeadingZeros64 (getword d (dLen d-1))"
  shows "2^63 \<le> uint (getword (dnStorage d (dLen d) s) (dLen d-1))"
  using dnStorage_length_and_top[OF assms] by blast

lemma uint_right_join:
  fixes hi lo :: u64
  assumes s: "s < 64"
  shows "uint ((lo >> s) OR (hi << (64-s))) =
    uint lo div 2^s + uint hi*2^(64-s) - (uint hi div 2^s)*2^64"
proof (cases "s=0")
  case True
  then show ?thesis by (simp add: shiftl_def shiftr_def)
next
  case False
  have small: "64-s < 64" using s False by arith
  have back_shift: "64-(64-s)=s" using s by arith
  have join: "uint ((lo >> s) OR (hi << (64-s))) =
    uint (hi << (64-s)) + uint (lo >> s)"
    using uint_join_shift[OF small, of hi lo]
    by (simp add: back_shift or.commute)
  have split: "uint (hi << (64-s)) + uint (hi >> s)*2^64 = uint hi*2^(64-s)"
    using shift_split_uint[OF small, of hi] by (simp add: back_shift)
  show ?thesis using join split by (simp add: word_shiftr_uint; linarith)
qed


lemma rem_loop_1:
  "rem_loop rem un u4 1 cnt s =
    rem_loop (update_word_uint256 rem (cnt-1)
      ((getword_u un (cnt-1) u4 >> s) OR (getword_u un (cnt-1+1) u4 << (64-s))))
      un u4 0 cnt s"
proof -
  have num: "(1::nat)=Suc 0" by simp
  show ?thesis unfolding num
    by (subst rem_loop.simps(2)) (simp add: Let_def)
qed

lemma rem_loop_2:
  "rem_loop rem un u4 2 cnt s =
    rem_loop (update_word_uint256 rem (cnt-2)
      ((getword_u un (cnt-2) u4 >> s) OR (getword_u un (cnt-2+1) u4 << (64-s))))
      un u4 1 cnt s"
proof -
  have num: "(2::nat)=Suc 1" by simp
  show ?thesis unfolding num
    by (subst rem_loop.simps(2)) (simp add: Let_def)
qed

lemma rem_loop_3:
  "rem_loop rem un u4 3 cnt s =
    rem_loop (update_word_uint256 rem (cnt-3)
      ((getword_u un (cnt-3) u4 >> s) OR (getword_u un (cnt-3+1) u4 << (64-s))))
      un u4 2 cnt s"
proof -
  have num: "(3::nat)=Suc 2" by simp
  show ?thesis unfolding num
    by (subst rem_loop.simps(2)) (simp add: Let_def)
qed
lemma rem_loop_full:
  assumes s: "s < 64"
  shows "uint256_to_int (rem_loop uint256_zero x 0 3 3 s) = uint256_to_int x div 2^s"
proof -
  let ?P = "(2::int)^(64-s)"
  let ?S = "(2::int)^s"
  let ?B = "(2::int)^64"
  let ?Q = "uint (z1 x)*?P + uint (z2 x)*?P*?B + uint (z3 x)*?P*?B^2"
  have scale: "?S*?P = ?B" using s by (simp flip: power_add)
  have v1: "?S*(uint (z1 x)*?P) = uint (z1 x)*?B"
    using scale by (simp add: mult_ac)
  have v2: "?S*(uint (z2 x)*?P*?B) = uint (z2 x)*?B^2"
    using scale by (simp add: mult_ac power2_eq_square)
  have v3: "?S*(uint (z3 x)*?P*?B^2) = uint (z3 x)*?B^3"
    using scale by (simp add: mult_ac power3_eq_cube power2_eq_square)
  have xsplit: "uint256_to_int x = uint (z0 x) + ?S*?Q"
    by (simp only: distrib_left v1 v2 v3 uint256_to_int_def Let_def;
      simp add: int_shiftl_eq_mult)
  have quotient: "uint256_to_int x div ?S = uint (z0 x) div ?S + ?Q"
    by (subst xsplit) simp
  have result: "uint256_to_int (rem_loop uint256_zero x 0 3 3 s) = uint (z0 x) div ?S + ?Q"
    by (simp add: rem_loop_1 rem_loop_2 rem_loop_3 Let_def getword_u_def getword_def
      update_word_uint256_def uint256_zero_def uint256_to_int_def
      int_shiftl_eq_mult uint_right_join[OF s] word_shiftr_uint algebra_simps)
  show ?thesis using quotient result by simp
qed
lemma rem_loop_supported:
  assumes n: "n < 4" and s: "s < 64"
    and bound: "uint256_u4_to_int (x,x4) < (2^64)^(n+1)"
  shows "uint256_to_int (rem_loop uint256_zero x x4 n n s) =
    uint256_u4_to_int (x,x4) div 2^s"
proof -
  have h4: "getword_u x 4 x4 = 0"
    by (rule uint256_u4_high_zero[OF bound]) (use n in arith)+
  then have x4: "x4=0" by (simp add: getword_u_def)
  have h3: "n<3 \<Longrightarrow> z3 x=0"
    using uint256_u4_high_zero[OF bound, of 3]
    by (simp add: getword_u_def getword_def)
  have h2: "n<2 \<Longrightarrow> z2 x=0"
    using uint256_u4_high_zero[OF bound, of 2]
    by (simp add: getword_u_def getword_def)
  have h1: "n<1 \<Longrightarrow> z1 x=0"
    using uint256_u4_high_zero[OF bound, of 1]
    by (simp add: getword_u_def getword_def)
  have cases: "n=0 \<or> n=1 \<or> n=2 \<or> n=3" using n by arith
  have same: "rem_loop uint256_zero x x4 n n s = rem_loop uint256_zero x 0 3 3 s"
    using cases h1 h2 h3 x4
    by (elim disjE; simp add: rem_loop_1 rem_loop_2 rem_loop_3 Let_def getword_u_def
      getword_def update_word_uint256_def uint256_zero_def shiftl_def shiftr_def)
  show ?thesis
    using rem_loop_full[OF s, of x] same x4
    by (simp add: uint256_u4_to_int_def)
qed

end
