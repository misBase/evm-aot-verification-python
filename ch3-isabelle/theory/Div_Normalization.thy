theory Div_Normalization
imports "EVM_SMT_Base.Exp"
begin

definition uint256_u4_to_int :: "uint256 \<times> u64 \<Rightarrow> int" where
  "uint256_u4_to_int p = uint256_to_int (fst p) + uint (snd p) * 2^256"

lemma LeadingZeros64_lt_64:
  fixes w :: u64
  assumes "w \<noteq> 0"
  shows "LeadingZeros64 w < 64"
proof -
  have len_pos: "0 < Len64 w"
  proof (rule ccontr)
    assume "\<not> 0 < Len64 w"
    then have len0: "Len64 w = 0"
      by simp
    have shifted_zero: "w >> Len64 w = 0"
      by (rule Len64_shift_zero)
    have "w >> 0 = 0"
      using shifted_zero len0
      by simp
    hence "w = 0"
      unfolding shiftr_def by simp
    with assms show False
      by simp
  qed
  have "LeadingZeros64 w = 64 - Len64 w"
    unfolding LeadingZeros64_def by simp
  then show ?thesis
    using len_pos by linarith
qed

lemma word_shiftr_uint:
  fixes w :: "'a::len word" and s :: nat
  shows "uint (w >> s) = uint w div 2 ^ s"
proof -
  have "uint (w >> s) = drop_bit s (take_bit LENGTH('a) (uint w))"
    by (simp add: shiftr_def unsigned_drop_bit_eq)
  also have "take_bit LENGTH('a) (uint w) = uint w"
    using uint_nonnegative[of w] uint_bounded[of w]
    by (simp add: take_bit_int_eq_self)
  also have "drop_bit s (uint w) = uint w div 2 ^ s"
    by (rule drop_bit_eq_div)
  finally show ?thesis .
qed

lemma shift_normalize_single:
  fixes w :: u64
  assumes "w \<noteq> 0"
  shows "uint (w << LeadingZeros64 w) = uint w * 2 ^ LeadingZeros64 w"
proof -
  let ?l = "Len64 w"
  let ?s = "LeadingZeros64 w"
  have s_eq: "?s = 64 - ?l"
    unfolding LeadingZeros64_def by simp
  have l_le: "?l \<le> 64"
    by (rule Len64_le_64)
  have shift_zero: "w >> ?l = 0"
    by (rule Len64_shift_zero)
  have uint_shift_zero: "uint (w >> ?l) = 0"
    using shift_zero by simp
  have uint_div: "uint w div 2 ^ ?l = 0"
  proof -
    have "uint (w >> ?l) = uint w div 2 ^ ?l"
      by (rule word_shiftr_uint)
    with uint_shift_zero show ?thesis by simp
  qed
  have w_bound: "uint w < 2 ^ ?l"
  proof -
    have u_nonneg: "0 \<le> uint w"
      by (rule uint_nonnegative)
    have "nat (uint w div 2 ^ ?l) = nat (uint w) div nat ((2::int) ^ ?l)"
      using u_nonneg by (rule nat_div_distrib)
    also have "... = nat (uint w) div (2::nat) ^ ?l"
      by (simp add: nat_power_eq)
    finally have nat_div: "nat (uint w) div 2 ^ ?l = 0"
      using uint_div by simp
    have pos: "0 < (2::nat) ^ ?l"
      by simp
    have nat_lt: "nat (uint w) < 2 ^ ?l"
      using pos nat_div by (auto simp add: div_eq_0_iff)
    have unat_lt: "unat w < 2 ^ ?l"
      unfolding unat_eq_nat_uint
      using nat_lt by simp
    have less_int: "int (unat w) < int (2 ^ ?l)"
      using unat_lt by (rule less_imp_of_nat_less)
    have less_int': "int (unat w) < (2::int) ^ ?l"
      using less_int by simp
    show ?thesis
      unfolding uint_nat
      using less_int' by simp
  qed
  have "uint (w << ?s) = uint (push_bit ?s w)"
    by (simp add: shiftl_def)
  also have "... = take_bit LENGTH(64) (push_bit ?s (uint w))"
    by (rule unsigned_push_bit_eq[where 'b=64])
  also have "... = take_bit LENGTH(64) (uint w * 2 ^ ?s)"
    by (simp add: push_bit_eq_mult)
  also have "... = uint w * 2 ^ ?s"
  proof -
    have prod_lt: "uint w * 2 ^ ?s < 2 ^ ?l * 2 ^ ?s"
      using w_bound by (rule mult_strict_right_mono) simp
    have sum_eq: "?l + ?s = 64"
      using s_eq l_le by linarith
    have "2 ^ ?l * 2 ^ ?s = (2::int) ^ (?l + ?s)"
      by (simp add: power_add)
    also have "... = (2::int) ^ 64"
      by (simp add: sum_eq)
    finally have prod_lt64: "uint w * 2 ^ ?s < (2::int) ^ 64"
      using prod_lt by simp
    have prod_nonneg: "0 \<le> uint w * 2 ^ ?s"
      by (simp add: uint_nonnegative)
    have len64: "LENGTH(64) = 64"
      by simp
    show ?thesis
      using prod_nonneg prod_lt64 len64 by (simp add: take_bit_int_eq_self)
  qed
  finally show ?thesis .
qed

lemma uint_shiftl_mod:
  fixes w :: u64 and s :: nat
  shows "uint (w << s) = (uint w * 2 ^ s) mod 2 ^ 64"
proof -
  have "uint (w << s) = uint (push_bit s w)"
    by (simp add: shiftl_def)
  also have "... = take_bit LENGTH(64) (push_bit s (uint w))"
    by (rule unsigned_push_bit_eq[where 'b=64])
  also have "... = take_bit 64 (push_bit s (uint w))"
    by simp
  also have "... = take_bit 64 (uint w * 2 ^ s)"
    by (simp add: push_bit_eq_mult)
  also have "... = (uint w * 2 ^ s) mod 2 ^ 64"
    by (simp add: take_bit_eq_mod)
  finally show ?thesis .
qed

lemma uint_shiftl_eq_bounded:
  fixes w :: u64 and s :: nat
  assumes "uint w * 2 ^ s < 2 ^ 64"
  shows "uint (w << s) = uint w * 2 ^ s"
proof -
  have "uint (w << s) = (uint w * 2 ^ s) mod 2 ^ 64"
    by (rule uint_shiftl_mod)
  also have "... = uint w * 2 ^ s"
  proof (rule mod_pos_pos_trivial)
    show "0 <= uint w * 2 ^ s"
      by (simp add: uint_nonnegative)
    show "uint w * 2 ^ s < 2 ^ 64"
      by (rule assms)
  qed
  finally show ?thesis .
qed

lemma un32_limbs_disjoint:
  fixes hi lo :: u64 and s :: nat
  assumes "s < 64"
  shows "((hi << s) AND (lo >> (64 - s))) = 0"
proof (rule bit_eqI)
  fix n
  show "bit ((hi << s) AND (lo >> (64 - s))) n = bit 0 n"
  proof (cases "n < s")
    case True
    have hi_bit: "\<not> bit (hi << s) n"
      using True by (simp add: bit_simps)
    show ?thesis
    proof -
      have "bit ((hi << s) AND (lo >> (64 - s))) n =
            (bit (hi << s) n \<and> bit (lo >> (64 - s)) n)"
        by (simp add: bit_and_iff)
      also have "... = False"
        using hi_bit by simp
      also have "... = bit 0 n"
        by simp
      finally show ?thesis .
    qed
  next
    case False
    have lo_bit: "\<not> bit (lo >> (64 - s)) n"
    proof
      assume "bit (lo >> (64 - s)) n"
      have shift: "bit (lo >> (64 - s)) n = bit lo (n + (64 - s))"
        by (simp add: shiftr_def bit_drop_bit_eq add.commute)
      with `bit (lo >> (64 - s)) n` have "bit lo (n + (64 - s))"
        by simp
      then have "n + (64 - s) < LENGTH(64)"
        by (rule bit_imp_le_length)
      moreover have "LENGTH(64) = 64"
        by simp
      ultimately have "n + (64 - s) < 64"
        by simp
      with False show False
        by linarith
    qed
    show ?thesis
    proof -
      have "bit ((hi << s) AND (lo >> (64 - s))) n =
            (bit (hi << s) n \<and> bit (lo >> (64 - s)) n)"
        by (simp add: bit_and_iff)
      also have "... = False"
        using lo_bit by simp
      also have "... = bit 0 n"
        by simp
      finally show ?thesis .
    qed
  qed
qed

lemma uint_or_eq_add:
  fixes a b :: u64
  assumes "a AND b = 0"
  shows "uint (a OR b) = uint a + uint b"
proof -
  have "uint a AND uint b = uint (a AND b)"
    by (rule uint_and[symmetric])
  also have "... = 0"
    using assms by simp
  finally have disjoint: "uint a AND uint b = 0" .
  have "uint a + uint b = uint a OR uint b"
    by (rule disjunctive_add_eq_or[OF disjoint])
  then have "uint a OR uint b = uint a + uint b"
    by simp
  then show ?thesis
    using uint_or[of a b] by simp
qed



lemma shift_split_uint:
  fixes w :: u64
  assumes "s < 64"
  shows "uint (w << s) + uint (w >> (64 - s)) * 2^64 = uint w * 2^s"
proof -
  have pow: "(2::int)^64 = 2^(64-s) * 2^s"
    using assms by (simp flip: power_add)
  have d: "uint w * 2^s div 2^64 = uint w div 2^(64-s)"
    by (subst pow) simp
  show ?thesis
    by (simp add: uint_shiftl_mod word_shiftr_uint flip: d)
qed

lemma uint_join_shift:
  fixes hi lo :: u64
  assumes "s < 64"
  shows "uint ((hi << s) OR (lo >> (64-s))) =
    uint (hi << s) + uint (lo >> (64-s))"
  by (rule uint_or_eq_add, rule un32_limbs_disjoint[OF assms])

lemma dnStorage_full_scale:
  assumes "s < 64"
  shows "uint256_to_int (dnStorage x 4 s) + uint (z3 x >> (64-s))*2^256 =
    uint256_to_int x * 2^s"
  using shift_split_uint[OF assms, of "z0 x"]
    shift_split_uint[OF assms, of "z1 x"]
    shift_split_uint[OF assms, of "z2 x"]
    shift_split_uint[OF assms, of "z3 x"]
  unfolding dnStorage_def uint256_to_int_def Let_def
  by (simp add: int_shiftl_eq_mult uint_join_shift[OF assms] algebra_simps; linarith)

lemma normalize_u_full:
  "normalize_u x (dLen x) s = (dnStorage x 4 s, z3 x >> (64-s))"
  by (cases "z3 x = 0"; cases "z2 x = 0"; cases "z1 x = 0"; cases "z0 x = 0";
    simp add: normalize_u_def dnStorage_def getword_def dLen_def shiftl_def shiftr_def)

lemma normalize_u_scale:
  assumes "s < 64"
  shows "uint256_u4_to_int (normalize_u x (dLen x) s) = uint256_to_int x * 2^s"
  using dnStorage_full_scale[OF assms, of x]
  by (simp add: normalize_u_full uint256_u4_to_int_def)

lemma normalization_carry_zero:
  fixes w :: u64
  shows "w >> (64 - LeadingZeros64 w) = 0"
  using Len64_le_64[of w] Len64_shift_zero[of w]
  by (simp add: LeadingZeros64_def)

lemma dnStorage_normalized_full:
  "dnStorage x (dLen x) (LeadingZeros64 (getword x (dLen x-1))) =
    dnStorage x 4 (LeadingZeros64 (getword x (dLen x-1)))"
  by (cases "z3 x = 0"; cases "z2 x = 0"; cases "z1 x = 0"; cases "z0 x = 0";
    simp add: dnStorage_def dLen_def getword_def normalization_carry_zero[unfolded shiftr_def] shiftl_def shiftr_def)

lemma dnStorage_scale:
  assumes nz: "x \<noteq> uint256_zero"
    and s: "s = LeadingZeros64 (getword x (dLen x - 1))"
  shows "uint256_to_int (dnStorage x (dLen x) s) = uint256_to_int x * 2^s"
proof -
  have top_nz: "getword x (dLen x - 1) \<noteq> 0"
    using nz unfolding getword_def dLen_def uint256_zero_def
    by (cases x; auto split: if_splits)
  have small: "s < 64" using LeadingZeros64_lt_64[OF top_nz] s by simp
  have top: "z3 x >> (64-s) = 0"
    using normalization_carry_zero[of "z3 x"] s
    by (cases "z3 x = 0"; cases "z2 x = 0"; cases "z1 x = 0"; cases "z0 x = 0";
      simp add: dLen_def getword_def shiftr_def)
  show ?thesis
    using dnStorage_full_scale[OF small, of x] dnStorage_normalized_full[of x] s top
    by simp
qed

end
