theory Div_LenLower
imports Div_Normalization
begin


lemma unat_shiftr_exact:
  "unat ((w :: u64) >> n) = unat w div 2^n"
  by (metis drop_bit_eq_div shiftr_def unat_drop_bit_eq)

lemma len8tab_lower:
  fixes w :: "8 word"
  assumes "w \<noteq> 0"
  shows "2 ^ (len8tab w - 1) \<le> unat w"
proof -
  have pos: "0 < unat w" using assms by (simp add: unat_gt_0)
  show ?thesis using assms pos unfolding len8tab_def
    by (auto simp: word_le_nat_alt split: if_splits)
qed

lemma Len64_decomp_nonzero:
  assumes "x \<noteq> 0"
  shows
  "\<exists>k x3. (x :: u64) >> k = x3 \<and> unat x3 < 256 \<and> x3 \<noteq> 0 \<and> Len64 x = k + len8tab (ucast x3)"
proof -
  define a1 :: nat where "a1 = (if (1 << 32) \<le> x then 32 else 0)"
  define b1 :: u64 where "b1 = (if (1 << 32) \<le> x then x >> 32 else x)"
  define a2 :: nat where "a2 = (if (1 << 16) \<le> b1 then 16 else 0)"
  define b2 :: u64 where "b2 = (if (1 << 16) \<le> b1 then b1 >> 16 else b1)"
  define a3 :: nat where "a3 = (if (1 << 8)  \<le> b2 then 8  else 0)"
  define b3 :: u64 where "b3 = (if (1 << 8)  \<le> b2 then b2 >> 8  else b2)"
  define k  :: nat where "k  = a1 + a2 + a3"

  have sh1: "x >> a1 = b1"
    unfolding a1_def b1_def by (simp add: shiftr_def split: if_splits)
  have sh2: "b1 >> a2 = b2"
    unfolding a2_def b2_def by (simp add: shiftr_def split: if_splits)
  have sh3: "b2 >> a3 = b3"
    unfolding a3_def b3_def by (simp add: shiftr_def split: if_splits)

    have shift: "x >> k = b3"
  proof -
    have "x >> k = x >> (a1 + a2 + a3)" unfolding k_def ..
    also have "... = (x >> a1) >> (a2 + a3)"
      by (simp add: shiftr_def add.commute add.left_commute)
    also have "... = (x >> a1 >> a2) >> a3"
      by (simp add: shiftr_def add.commute add.left_commute)
    also have "... = b1 >> a2 >> a3" unfolding sh1 ..
    also have "... = b2 >> a3" unfolding sh2 ..
    also have "... = b3" unfolding sh3 ..
    finally show ?thesis .
  qed

  have len_eq: "Len64 x = k + len8tab (ucast b3)"
    unfolding Len64_def Let_def a1_def b1_def a2_def b2_def a3_def b3_def k_def
    by (simp split: if_splits)

  have bound: "unat b3 < 256"
    using x3_lt_256[of x] unfolding b1_def b2_def b3_def by (simp add: Let_def)


  have x_pos: "0 < unat x" using assms by (simp add: unat_gt_0)
  have b1_pos: "0 < unat b1"
    using x_pos unfolding b1_def
    by (auto simp: pow32 word_le_nat_alt unat_shiftr_exact div_greater_zero_iff)
  have b2_pos: "0 < unat b2"
    using b1_pos unfolding b2_def
    by (auto simp: pow16 word_le_nat_alt unat_shiftr_exact div_greater_zero_iff)
  have b3_pos: "0 < unat b3"
    using b2_pos unfolding b3_def
    by (auto simp: pow8 word_le_nat_alt unat_shiftr_exact div_greater_zero_iff)
  show ?thesis using shift bound len_eq b3_pos by auto
qed


lemma len8tab_positive:
  fixes w :: "8 word"
  assumes "w \<noteq> 0"
  shows "0 < len8tab w"
  using assms unfolding len8tab_def by auto

lemma Len64_lower:
  fixes y :: u64
  assumes "y \<noteq> 0"
  shows "2^(Len64 y - 1) \<le> unat y"
proof -
  obtain k v where shift: "y >> k = v" and bound: "unat v < 256"
    and nz: "v \<noteq> 0" and len: "Len64 y = k + len8tab (ucast v)"
    using Len64_decomp_nonzero[OF assms] by blast
  have cast: "unat (ucast v :: 8 word) = unat v"
    by (rule unat_ucast_u64_to_u8[OF bound])
  have cast_nz: "(ucast v :: 8 word) \<noteq> 0"
    using cast nz by (auto simp: unat_eq_zero)
  have small: "2^(len8tab (ucast v) - 1) \<le> unat v"
    using len8tab_lower[OF cast_nz] cast by simp
  have pos: "0 < len8tab (ucast v)"
    by (rule len8tab_positive[OF cast_nz])
  have val: "unat v = unat y div 2^k"
    using arg_cong[where f=unat, OF shift] by (simp add: unat_shiftr_exact)
  have exp: "Len64 y - 1 = (len8tab (ucast v)-1) + k"
    using len pos by linarith
  have "(2::nat)^(Len64 y - 1) = 2^(len8tab (ucast v)-1) * 2^k"
    by (subst exp) (rule power_add)
  also have "... \<le> unat v * 2^k"
    by (rule mult_right_mono[OF small]) simp
  also have "... \<le> unat y"
    by (simp add: val)
  finally show ?thesis .
qed

lemma unat_yn1_ge_ax:
  fixes y :: u64
  assumes "y \<noteq> 0"
  shows "2^31 \<le> unat ((y << LeadingZeros64 y) >> 32)"
proof -
  let ?l = "Len64 y"
  let ?s = "LeadingZeros64 y"
  have lpos: "0 < ?l"
    using LeadingZeros64_lt_64[OF assms] unfolding LeadingZeros64_def by linarith
  have lbound: "?l \<le> 64" by (rule Len64_le_64)
  have exponents: "?l - 1 + ?s = 63"
    unfolding LeadingZeros64_def using lpos lbound by linarith
  have norm: "unat (y << ?s) = unat y * 2^?s"
    using arg_cong[where f=nat, OF shift_normalize_single[OF assms]]
    unfolding unat_eq_nat_uint
    by (simp add: nat_mult_distrib)
  have lower: "2^63 \<le> unat (y << ?s)"
  proof -
    have "2^63 = (2::nat)^(?l-1) * 2^?s"
      using exponents by (simp flip: power_add)
    also have "... \<le> unat y * 2^?s"
      by (rule mult_right_mono[OF Len64_lower[OF assms]]) simp
    finally show ?thesis by (simp add: norm)
  qed
  have "(2::nat)^63 div 2^32 \<le> unat (y << ?s) div 2^32"
    by (rule div_le_mono[OF lower])
  then show ?thesis
    by (simp add: unat_shiftr_exact)
qed

end
