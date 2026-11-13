theory Div
  imports Div_Knuth Div_Denormalization
begin

section \<open>Top-level uint256 DIV/MOD correctness\<close>

lemma uint256_to_int_zero:
  "uint256_to_int uint256_zero = 0"
  unfolding uint256_to_int_def uint256_zero_def Let_def
  by (simp add: int_shiftl_eq_mult)

lemma uint256_to_int_Isuint64:
  fixes x :: uint256
  assumes "Isuint64 x"
  shows "uint256_to_int x = uint (z0 x)"
proof -
  have z1: "z1 x = 0" and z2: "z2 x = 0" and z3: "z3 x = 0"
    using assms unfolding Isuint64_def by simp_all
  show ?thesis
    unfolding uint256_to_int_def Let_def
    using z1 z2 z3
    by (simp add: int_shiftl_eq_mult)
qed

lemma uint256_to_int_dLen_upper:
  fixes x :: uint256
  shows "uint256_to_int x < 2 ^ (64 * dLen x)"
proof (cases x)
  case (fields a b c d)
  have val: "uint256_to_int x = uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192"
    unfolding fields uint256_to_int_def Let_def
    by (simp add: int_shiftl_eq_mult)
  show ?thesis
  proof (cases "d \<noteq> 0")
    case True
    have dlen4: "dLen x = 4"
      unfolding fields dLen_def using True by simp
    then show ?thesis
      using val dlen4 uint256_to_int_bound[of x] by simp
  next
    case False
    then have d0: "d = 0" by simp
    show ?thesis
    proof (cases "c \<noteq> 0")
      case True
      have dlen3: "dLen x = 3"
        unfolding fields dLen_def using d0 True by simp
      have sum3: "uint a + uint b * 2^64 + uint c * 2^128 < (2::int)^192"
        by (rule sum3_lt_2p192)
      then show ?thesis
        using val d0 dlen3 sum3 by simp
    next
      case False
      then have c0: "c = 0" by simp
      show ?thesis
      proof (cases "b \<noteq> 0")
        case True
        have dlen2: "dLen x = 2"
          unfolding fields dLen_def using d0 c0 True by simp
      have sum2: "uint a + uint b * 2^64 < (2::int)^128"
        by (rule sum2_lt_2p128)
        then show ?thesis
          using val c0 d0 dlen2 sum2 by simp
      next
        case False
        then have b0: "b = 0" by simp
        show ?thesis
        proof (cases "a \<noteq> 0")
          case True
          have dlen1: "dLen x = 1"
            unfolding fields dLen_def using b0 c0 d0 True by simp
          have is64: "Isuint64 x"
            unfolding fields Isuint64_def using b0 c0 d0 by simp
          have int_a: "uint256_to_int x = uint a"
            using val b0 c0 d0 by simp
          have a_lt: "uint a < 2^64"
            by (rule uint_lt_2p64)
          then show ?thesis
            using int_a dlen1 a_lt by simp
        next
          case False
          then have a0: "a = 0" by simp
          have dlen0: "dLen x = 0"
            unfolding fields dLen_def using a0 b0 c0 d0 by simp
          have x_zero: "x = uint256_zero"
            unfolding fields uint256_zero_def using a0 b0 c0 d0 by simp
          then show ?thesis
            using dlen0 uint256_to_int_zero by simp
        qed
      qed
    qed
  qed
qed

lemma uint256_to_int_dLen_lower:
  fixes x :: uint256
  assumes "0 < dLen x"
  shows "2 ^ (64 * (dLen x - 1)) \<le> uint256_to_int x"
proof (cases x)
  case (fields a b c d)
  have val: "uint256_to_int x = uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192"
    unfolding fields uint256_to_int_def Let_def
    by (simp add: int_shiftl_eq_mult)
  have nonneg_a: "0 \<le> uint a" by (rule uint_ge_0)
  have nonneg_b: "0 \<le> uint b" by (rule uint_ge_0)
  have nonneg_c: "0 \<le> uint c" by (rule uint_ge_0)
  have nonneg_d: "0 \<le> uint d" by (rule uint_ge_0)
  show ?thesis
  proof (cases "d \<noteq> 0")
    case True
    have dlen4: "dLen x = 4" unfolding fields dLen_def using True by simp
    have d_ge1: "1 \<le> uint d"
    proof -
      have "uint d \<noteq> 0"
      proof
        assume "uint d = 0"
        hence "d = 0" by (simp add: uint_0_iff)
        with True show False by simp
      qed
      with nonneg_d show ?thesis by linarith
    qed
    have pow192: "2^192 \<le> uint d * 2^192"
    proof -
      have "1 * 2^192 \<le> uint d * 2^192"
        using d_ge1 by (rule mult_right_mono) simp
      then show ?thesis by simp
    qed
    have d_sum_ge: "uint d * 2^192 \<le> uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192"
    proof -
      have nonneg_b64: "0 \<le> uint b * 2^64"
        by (rule mult_nonneg_nonneg) (simp_all add: nonneg_b)
      have nonneg_c128: "0 \<le> uint c * 2^128"
        by (rule mult_nonneg_nonneg) (simp_all add: nonneg_c)
      have nonneg_ab: "0 \<le> uint a + uint b * 2^64"
        using nonneg_a nonneg_b64 by (rule add_nonneg_nonneg)
      have nonneg_abc: "0 \<le> uint a + uint b * 2^64 + uint c * 2^128"
        using nonneg_ab nonneg_c128 by (rule add_nonneg_nonneg)
      have "uint d * 2^192 = uint d * 2^192 + 0" by simp
      also have "... \<le> uint d * 2^192 + (uint a + uint b * 2^64 + uint c * 2^128)"
        using nonneg_abc by (rule add_left_mono)
      also have "... = uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192"
        by (simp add: add.commute add.left_commute)
      finally show ?thesis .
    qed
    have "2 ^ (64 * (dLen x - 1)) = (2::int)^192" using dlen4 by simp
    also have "... \<le> uint d * 2^192" by (rule pow192)
    also have "... \<le> uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192"
      by (rule d_sum_ge)
    finally show ?thesis using val by simp
  next
    case False
    then have d0: "d = 0" by simp
    show ?thesis
    proof (cases "c \<noteq> 0")
      case True
      have dlen3: "dLen x = 3" unfolding fields dLen_def using d0 True by simp
      have c_ge1: "1 \<le> uint c"
      proof -
        have "uint c \<noteq> 0"
        proof
          assume "uint c = 0"
          hence "c = 0" by (simp add: uint_0_iff)
          with True show False by simp
        qed
        with nonneg_c show ?thesis by linarith
      qed
      have pow128: "2^128 \<le> uint c * 2^128"
      proof -
        have "1 * 2^128 \<le> uint c * 2^128"
          using c_ge1 by (rule mult_right_mono) simp
        then show ?thesis by simp
      qed
      have c_sum_ge: "uint c * 2^128 \<le> uint a + uint b * 2^64 + uint c * 2^128"
      proof -
        have nonneg_b64: "0 \<le> uint b * 2^64"
          by (rule mult_nonneg_nonneg) (simp_all add: nonneg_b)
        have nonneg_ab: "0 \<le> uint a + uint b * 2^64"
          using nonneg_a nonneg_b64 by (rule add_nonneg_nonneg)
        have "uint c * 2^128 = uint c * 2^128 + 0" by simp
        also have "... \<le> uint c * 2^128 + (uint a + uint b * 2^64)"
          using nonneg_ab by (rule add_left_mono)
        also have "... = uint a + uint b * 2^64 + uint c * 2^128"
          by (simp add: add.commute add.left_commute)
        finally show ?thesis .
      qed
      have "2 ^ (64 * (dLen x - 1)) = (2::int)^128" using dlen3 by simp
      also have "... \<le> uint c * 2^128" by (rule pow128)
      also have "... \<le> uint a + uint b * 2^64 + uint c * 2^128"
        by (rule c_sum_ge)
      also have "... = uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192"
        using d0 by simp
      finally show ?thesis using val by simp
    next
      case False
      then have c0: "c = 0" by simp
      show ?thesis
      proof (cases "b \<noteq> 0")
        case True
        have dlen2: "dLen x = 2" unfolding fields dLen_def using d0 c0 True by simp
        have b_ge1: "1 \<le> uint b"
        proof -
          have "uint b \<noteq> 0"
          proof
            assume "uint b = 0"
            hence "b = 0" by (simp add: uint_0_iff)
            with True show False by simp
          qed
          with nonneg_b show ?thesis by linarith
        qed
        have pow64: "2^64 \<le> uint b * 2^64"
        proof -
          have "1 * 2^64 \<le> uint b * 2^64"
            using b_ge1 by (rule mult_right_mono) simp
          then show ?thesis by simp
        qed
        have b_sum_ge: "uint b * 2^64 \<le> uint a + uint b * 2^64"
        proof -
          have "uint b * 2^64 = uint b * 2^64 + 0" by simp
          also have "... \<le> uint b * 2^64 + uint a"
            using nonneg_a by (rule add_left_mono)
          also have "... = uint a + uint b * 2^64"
            by (simp add: add.commute)
          finally show ?thesis .
        qed
        have "2 ^ (64 * (dLen x - 1)) = (2::int)^64" using dlen2 by simp
        also have "... \<le> uint b * 2^64" by (rule pow64)
        also have "... \<le> uint a + uint b * 2^64" by (rule b_sum_ge)
        also have "... = uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192"
          using c0 d0 by simp
        finally show ?thesis using val by simp
      next
        case False
        then have b0: "b = 0" by simp
        show ?thesis
        proof (cases "a \<noteq> 0")
          case True
          have dlen1: "dLen x = 1" unfolding fields dLen_def using b0 c0 d0 True by simp
          have a_ge1: "1 \<le> uint a"
          proof -
            have "uint a \<noteq> 0"
            proof
              assume "uint a = 0"
              hence "a = 0" by (simp add: uint_0_iff)
              with True show False by simp
            qed
            with nonneg_a show ?thesis by linarith
          qed
          have "2 ^ (64 * (dLen x - 1)) = (1::int)" using dlen1 by simp
          also have "... \<le> uint a"
            using a_ge1 by simp
          also have "... = uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192"
            using b0 c0 d0 by simp
          finally show ?thesis using val by simp
        next
          case False
          then have a0: "a = 0" by simp
          have "dLen x = 0" unfolding fields dLen_def using a0 b0 c0 d0 by simp
          with assms show ?thesis by simp
        qed
      qed
    qed
  qed
qed

lemma SetUint64_to_int:
  "uint256_to_int (SetUint64 w) = uint w"
  unfolding SetUint64_def uint256_to_int_def Let_def
  by (simp add: int_shiftl_eq_mult)

lemma shift_div_correct:
  fixes a b :: int and s :: nat
  assumes "0 < b"
  shows "(a * 2 ^ s) div (b * 2 ^ s) = a div b"
  using assms by simp

lemma shift_rem_correct:
  fixes a b :: int and s :: nat
  assumes "0 < b"
  shows "((a * 2 ^ s) mod (b * 2 ^ s)) div 2 ^ s = a mod b"
proof -
  have mod_eq: "((a * 2 ^ s) mod (b * 2 ^ s)) = (a mod b) * 2 ^ s"
    by (simp add: mod_mult_mult2)
  have "((a * 2 ^ s) mod (b * 2 ^ s)) div 2 ^ s = ((a mod b) * 2 ^ s) div 2 ^ s"
    using mod_eq by simp
  also have "... = a mod b"
    by simp
  finally show ?thesis .
qed

lemma udivremBy1_branch_correct:
  fixes u d q :: uint256 and r u4 :: u64
  assumes "d \<noteq> uint256_zero" and "dLen d = 1"
      and "shift = LeadingZeros64 (getword d (dLen d - 1))"
      and "dn = dnStorage d (dLen d) shift"
      and "un = fst (normalize_u u (dLen u) shift)"
      and "u4 = snd (normalize_u u (dLen u) shift)"
      and "udivremBy1 uint256_zero un (dLen u) (getword dn 0) u4 = (q, r)"
  shows "uint256_to_int q = uint256_to_int u div uint256_to_int d \<and>
         uint256_to_int (SetUint64 (r >> shift)) = uint256_to_int u mod uint256_to_int d"
proof -
  have d1: "dLen d = 1" using assms(2) by simp
  have shift_eq: "shift = LeadingZeros64 (getword d 0)"
    using assms(3) d1 by simp
  have shift_eq2: "shift = LeadingZeros64 (z0 d)"
    using shift_eq by (simp add: getword_def)
  have z3_zero: "z3 d = 0"
    using d1 unfolding dLen_def by (cases "z3 d = 0"; auto)
  have z2_zero: "z2 d = 0"
    using d1 z3_zero unfolding dLen_def by (cases "z2 d = 0"; auto)
  have z1_zero: "z1 d = 0"
    using d1 z3_zero z2_zero unfolding dLen_def by (cases "z1 d = 0"; auto)
  have is64: "Isuint64 d"
    using z1_zero z2_zero z3_zero unfolding Isuint64_def by simp
  have uint_d: "uint256_to_int d = uint (z0 d)"
    by (rule uint256_to_int_Isuint64[OF is64])
  have z0_ne: "z0 d \<noteq> 0"
    using d1 z1_zero z2_zero z3_zero unfolding dLen_def by auto
  have z0_uint_ne: "uint (z0 d) \<noteq> 0"
  proof
    assume "uint (z0 d) = 0"
    hence "z0 d = 0"
      by (simp add: uint_0_iff)
    with z0_ne show False by simp
  qed
  have z0_pos: "0 < uint (z0 d)"
    using z0_uint_ne uint_ge_0[of "z0 d"] by linarith
  have dn_word: "getword dn 0 = z0 d << shift"
  proof -
    have "getword dn 0 = getword (dnStorage d (dLen d) shift) 0"
      using assms(4) by simp
    also have "... = z0 d << shift"
      using d1 by (simp add: dnStorage_def getword_def)
    finally show ?thesis .
  qed
  have dn_uint: "uint (getword dn 0) = uint (z0 d) * 2 ^ shift"
  proof -
    have "uint (z0 d << LeadingZeros64 (z0 d)) =
          uint (z0 d) * 2 ^ LeadingZeros64 (z0 d)"
      using z0_ne by (rule shift_normalize_single)
    then show ?thesis using dn_word shift_eq2 by simp
  qed
  have pow_pos: "0 < (2::int) ^ shift" by simp
  have dn_pos: "0 < uint (getword dn 0)"
  proof -
    have "0 < uint (z0 d) * 2 ^ shift"
      using z0_pos pow_pos by (rule mult_pos_pos)
    with dn_uint show ?thesis by simp
  qed
  have dn_nonzero: "getword dn 0 \<noteq> 0"
  proof
    assume "getword dn 0 = 0"
    hence "uint (getword dn 0) = 0"
      by (simp add: uint_0_iff)
    with dn_pos show False by linarith
  qed
  have d_len_pos: "0 < dLen d" using d1 by simp
  have d_pos_int: "0 < uint256_to_int d"
    using uint_d z0_pos by simp
  have shift_lt64: "shift < 64"
  proof -
    have getword0_ne: "getword d 0 \<noteq> 0"
      by (simp add: getword_def z0_ne)
    have "shift = LeadingZeros64 (getword d 0)"
      using shift_eq by simp
    also have "... < 64"
      using getword0_ne by (rule LeadingZeros64_lt_64)
    finally show ?thesis .
  qed
  have un_int: "uint256_u4_to_int (un, u4) = uint256_to_int u * 2 ^ shift"
  proof -
    have "uint256_u4_to_int (normalize_u u (dLen u) shift) = uint256_to_int u * 2 ^ shift"
      using shift_lt64 by (rule normalize_u_scale)
    with assms(5) assms(6) show ?thesis by simp
  qed
  have normalized_dn: "2^63 \<le> uint (getword dn 0)"
    using uint_normalized_ge[OF z0_ne] dn_word shift_eq2 by simp
  have ulen_le: "dLen u \<le> 4" unfolding dLen_def by auto
  have udiv: "uint256_to_int (fst (udivremBy1 uint256_zero un (dLen u) (getword dn 0) u4)) =
              uint256_u4_to_int (un, u4) div uint (getword dn 0) \<and>
              uint (snd (udivremBy1 uint256_zero un (dLen u) (getword dn 0) u4)) =
              uint256_u4_to_int (un, u4) mod uint (getword dn 0)"
  proof (cases "u = uint256_zero")
    case True
    have norm_zero: "normalize_u uint256_zero (dLen uint256_zero) shift = (uint256_zero,0)"
      by (simp add: normalize_u_def dnStorage_def dLen_def uint256_zero_def shiftl_def shiftr_def)
    have un0: "un = uint256_zero" and u40: "u4 = 0"
      using assms(5,6) True norm_zero by simp_all
    have len0: "dLen u = 0" using True by (simp add: dLen_def uint256_zero_def)
    have one_pos: "0 < (1::nat)" and one_le: "(1::nat) \<le> 4" by simp_all
    have zero_bound: "uint256_to_int uint256_zero + uint (0::u64) * 2^256 <
        uint (getword dn 0) * (2^64)^1"
      using dn_pos by (simp add: uint256_to_int_zero)
    have zero_check:
      "uint256_to_int (fst (udivremBy1 uint256_zero uint256_zero 1 (getword dn 0) 0)) = 0 \<and>
       uint (snd (udivremBy1 uint256_zero uint256_zero 1 (getword dn 0) 0)) = 0"
      using udivremBy1_correct[OF normalized_dn one_pos one_le zero_bound]
      by (simp add: uint256_to_int_zero)
    show ?thesis using zero_check
      by (simp add: un0 u40 len0 uint256_u4_to_int_def uint256_to_int_zero udivremBy1_zero_counts)
  next
    case False
    have ulen_pos: "0 < dLen u"
      using False unfolding dLen_def uint256_zero_def by (cases u; auto split: if_splits)
    have ubound: "uint256_to_int u < ((2::int)^64)^(dLen u)"
      using uint256_to_int_dLen_upper[of u] by (simp add: power_mult)
    have digit_ge: "1 \<le> uint (z0 d)" using z0_pos by linarith
    have scale_le: "(2::int)^shift \<le> uint (getword dn 0)"
    proof -
      have "1 * (2::int)^shift \<le> uint (z0 d) * 2^shift"
        by (rule mult_right_mono[OF digit_ge]) simp
      then show ?thesis using dn_uint by simp
    qed
    have "uint256_to_int u * 2^shift < ((2::int)^64)^(dLen u) * 2^shift"
      by (rule mult_strict_right_mono[OF ubound]) simp
    also have "... \<le> ((2::int)^64)^(dLen u) * uint (getword dn 0)"
      by (rule mult_left_mono[OF scale_le]) simp
    finally have input_bound:
      "uint256_to_int un + uint u4 * 2^256 < uint (getword dn 0) * (2^64)^(dLen u)"
      using un_int by (simp add: uint256_u4_to_int_def mult.commute)
    show ?thesis
      using udivremBy1_correct[OF normalized_dn ulen_pos ulen_le input_bound]
      by (simp add: uint256_u4_to_int_def)
  qed
  have q_int: "uint256_to_int q = uint256_to_int u div uint256_to_int d"
  proof -
    have "uint256_to_int q = uint256_u4_to_int (un, u4) div uint (getword dn 0)"
      using assms(7) udiv by simp
    also have "... = (uint256_to_int u * 2 ^ shift) div (uint256_to_int d * 2 ^ shift)"
      using un_int uint_d dn_uint by simp
    also have "... = uint256_to_int u div uint256_to_int d"
      using d_pos_int by (rule shift_div_correct)
    finally show ?thesis .
  qed
  have r_int: "uint256_to_int (SetUint64 (r >> shift)) = uint256_to_int u mod uint256_to_int d"
  proof -
    have r_eq: "uint r = uint256_u4_to_int (un, u4) mod uint (getword dn 0)"
      using assms(7) udiv by simp
    have "uint256_to_int (SetUint64 (r >> shift)) = uint (r >> shift)"
      by (rule SetUint64_to_int)
    also have "... = uint r div 2 ^ shift"
      by (rule word_shiftr_uint)
    also have "... = (uint256_u4_to_int (un, u4) mod uint (getword dn 0)) div 2 ^ shift"
      using r_eq by simp
    also have "... = ((uint256_to_int u * 2 ^ shift) mod (uint256_to_int d * 2 ^ shift)) div 2 ^ shift"
      using un_int uint_d dn_uint by simp
    also have "... = uint256_to_int u mod uint256_to_int d"
      using d_pos_int by (rule shift_rem_correct)
    finally show ?thesis .
  qed
  show ?thesis using q_int r_int by simp
qed



lemma dLen_pos:
  fixes x :: uint256
  assumes "x \<noteq> uint256_zero"
  shows "0 < dLen x"
proof -
  have "z3 x \<noteq> 0 \<or> z2 x \<noteq> 0 \<or> z1 x \<noteq> 0 \<or> z0 x \<noteq> 0"
    using assms unfolding uint256_zero_def by (cases x) auto
  then show ?thesis unfolding dLen_def by auto
qed

lemma dLen_Isuint64_le1:
  fixes x :: uint256
  assumes "Isuint64 x"
  shows "dLen x \<le> 1"
  using assms unfolding Isuint64_def dLen_def by auto

lemma not_Isuint64_dLen_gt1:
  fixes y :: uint256
  assumes "y \<noteq> uint256_zero" and "\<not> Isuint64 y"
  shows "1 < dLen y"
proof -
  have high: "z1 y \<noteq> 0 \<or> z2 y \<noteq> 0 \<or> z3 y \<noteq> 0"
    using assms(2) unfolding Isuint64_def by auto
  show ?thesis unfolding dLen_def using high by auto
qed

lemma limb256_lt_iff_lex:
  fixes a0 a1 a2 a3 b0 b1 b2 b3 :: int
  assumes "0 \<le> a0" "a0 < 2^64"
      and "0 \<le> a1" "a1 < 2^64"
      and "0 \<le> a2" "a2 < 2^64"
      and "0 \<le> a3" "a3 < 2^64"
      and "0 \<le> b0" "b0 < 2^64"
      and "0 \<le> b1" "b1 < 2^64"
      and "0 \<le> b2" "b2 < 2^64"
      and "0 \<le> b3" "b3 < 2^64"
  shows "(a0 + a1 * 2^64 + a2 * 2^128 + a3 * 2^192 <
          b0 + b1 * 2^64 + b2 * 2^128 + b3 * 2^192) =
         (a3 < b3 \<or>
          a3 = b3 \<and> a2 < b2 \<or>
          a3 = b3 \<and> a2 = b2 \<and> a1 < b1 \<or>
          a3 = b3 \<and> a2 = b2 \<and> a1 = b1 \<and> a0 < b0)"
proof -
  let ?M = "(2::int)^64"
  have M_pos: "0 < ?M" by simp
  have M2_eq: "?M^2 = 2^128" by (simp add: power_add)
  have M3_eq: "?M^3 = 2^192" by (simp add: power_add)

  define low_a where "low_a = a0 + a1 * ?M + a2 * ?M^2"
  define low_b where "low_b = b0 + b1 * ?M + b2 * ?M^2"
  define two_a where "two_a = a0 + a1 * ?M"
  define two_b where "two_b = b0 + b1 * ?M"
  define X where "X = low_a + a3 * ?M^3"
  define Y where "Y = low_b + b3 * ?M^3"

  have X_orig: "a0 + a1 * 2^64 + a2 * 2^128 + a3 * 2^192 = X"
    unfolding X_def low_a_def by (simp add: power_add)
  have Y_orig: "b0 + b1 * 2^64 + b2 * 2^128 + b3 * 2^192 = Y"
    unfolding Y_def low_b_def by (simp add: power_add)

  have low_a_ge: "0 \<le> low_a"
    using assms unfolding low_a_def
    by (auto intro!: add_nonneg_nonneg mult_nonneg_nonneg)
  have low_b_ge: "0 \<le> low_b"
    using assms unfolding low_b_def
    by (auto intro!: add_nonneg_nonneg mult_nonneg_nonneg)

  have low_a_lt: "low_a < ?M^3"
  proof -
    have a0_le: "a0 \<le> ?M - 1" using assms by linarith
    have a1_le: "a1 \<le> ?M - 1" using assms by linarith
    have a2_le: "a2 \<le> ?M - 1" using assms by linarith
    have a1_prod: "a1 * ?M \<le> (?M - 1) * ?M"
      using a1_le by (rule mult_right_mono) simp
    have a2_prod: "a2 * ?M^2 \<le> (?M - 1) * ?M^2"
      using a2_le by (rule mult_right_mono) simp
    have ab_le: "a0 + a1 * ?M \<le> (?M - 1) + (?M - 1) * ?M"
      using a0_le a1_prod by (rule add_mono)
    have "low_a \<le> (?M - 1) + (?M - 1) * ?M + (?M - 1) * ?M^2"
      unfolding low_a_def using ab_le a2_prod by (rule add_mono)
    also have "... = ?M^3 - 1"
      by (simp add: algebra_simps power2_eq_square power3_eq_cube)
    finally show ?thesis by linarith
  qed

  have low_b_lt: "low_b < ?M^3"
  proof -
    have b0_le: "b0 \<le> ?M - 1" using assms by linarith
    have b1_le: "b1 \<le> ?M - 1" using assms by linarith
    have b2_le: "b2 \<le> ?M - 1" using assms by linarith
    have b1_prod: "b1 * ?M \<le> (?M - 1) * ?M"
      using b1_le by (rule mult_right_mono) simp
    have b2_prod: "b2 * ?M^2 \<le> (?M - 1) * ?M^2"
      using b2_le by (rule mult_right_mono) simp
    have ab_le: "b0 + b1 * ?M \<le> (?M - 1) + (?M - 1) * ?M"
      using b0_le b1_prod by (rule add_mono)
    have "low_b \<le> (?M - 1) + (?M - 1) * ?M + (?M - 1) * ?M^2"
      unfolding low_b_def using ab_le b2_prod by (rule add_mono)
    also have "... = ?M^3 - 1"
      by (simp add: algebra_simps power2_eq_square power3_eq_cube)
    finally show ?thesis by linarith
  qed

  have two_a_ge: "0 \<le> two_a"
    using assms unfolding two_a_def
    by (auto intro!: add_nonneg_nonneg mult_nonneg_nonneg)
  have two_b_ge: "0 \<le> two_b"
    using assms unfolding two_b_def
    by (auto intro!: add_nonneg_nonneg mult_nonneg_nonneg)
  have a0_lt_M: "a0 < ?M" using assms by simp
  have b0_lt_M: "b0 < ?M" using assms by simp

  have two_a_lt: "two_a < ?M^2"
  proof -
    have a0_le: "a0 \<le> ?M - 1" using assms by linarith
    have a1_le: "a1 \<le> ?M - 1" using assms by linarith
    have a1_prod: "a1 * ?M \<le> (?M - 1) * ?M"
      using a1_le by (rule mult_right_mono) simp
    have "two_a \<le> (?M - 1) + (?M - 1) * ?M"
      unfolding two_a_def using a0_le a1_prod by (rule add_mono)
    also have "... = ?M^2 - 1"
      by (simp add: algebra_simps power2_eq_square)
    finally show ?thesis by linarith
  qed

  have two_b_lt: "two_b < ?M^2"
  proof -
    have b0_le: "b0 \<le> ?M - 1" using assms by linarith
    have b1_le: "b1 \<le> ?M - 1" using assms by linarith
    have b1_prod: "b1 * ?M \<le> (?M - 1) * ?M"
      using b1_le by (rule mult_right_mono) simp
    have "two_b \<le> (?M - 1) + (?M - 1) * ?M"
      unfolding two_b_def using b0_le b1_prod by (rule add_mono)
    also have "... = ?M^2 - 1"
      by (simp add: algebra_simps power2_eq_square)
    finally show ?thesis by linarith
  qed

  let ?R = "a3 < b3 \<or>
            a3 = b3 \<and> a2 < b2 \<or>
            a3 = b3 \<and> a2 = b2 \<and> a1 < b1 \<or>
            a3 = b3 \<and> a2 = b2 \<and> a1 = b1 \<and> a0 < b0"
  have case3: "a3 < b3 \<Longrightarrow> X < Y"
  proof -
    assume a3_lt: "a3 < b3"
    have "a3 + 1 \<le> b3" using a3_lt by linarith
    have "X < ?M^3 + a3 * ?M^3"
      using add_strict_right_mono[OF low_a_lt, of "a3 * ?M^3"]
      by (simp add: X_def algebra_simps)
    also have "... = (a3 + 1) * ?M^3"
      by (simp add: algebra_simps)
    also have "... \<le> b3 * ?M^3"
      using `a3 + 1 \<le> b3` by (rule mult_right_mono) simp
    also have "... \<le> Y"
      unfolding Y_def using low_b_ge by (simp add: algebra_simps)
    finally show "X < Y" .
  qed

  have case2: "a3 = b3 \<Longrightarrow> a2 < b2 \<Longrightarrow> X < Y"
  proof -
    assume eq3: "a3 = b3" and a2_lt: "a2 < b2"
    have "a2 + 1 \<le> b2" using a2_lt by linarith
    have "low_a < ?M^2 + a2 * ?M^2"
      using add_strict_right_mono[OF two_a_lt, of "a2 * ?M^2"]
      by (simp add: low_a_def two_a_def algebra_simps)
    also have "... = (a2 + 1) * ?M^2"
      by (simp add: algebra_simps)
    also have "... \<le> b2 * ?M^2"
      using `a2 + 1 \<le> b2` by (rule mult_right_mono) simp
    also have "... \<le> low_b"
      unfolding low_b_def using two_b_ge[unfolded two_b_def] by (simp add: algebra_simps)
    finally have low_lt: "low_a < low_b" .
    show "X < Y" using low_lt eq3 by (simp add: X_def Y_def)
  qed

  have case1: "a3 = b3 \<Longrightarrow> a2 = b2 \<Longrightarrow> a1 < b1 \<Longrightarrow> X < Y"
  proof -
    assume eq3: "a3 = b3" and eq2: "a2 = b2" and a1_lt: "a1 < b1"
    have "a1 + 1 \<le> b1" using a1_lt by linarith
    have "two_a < ?M + a1 * ?M"
      using add_strict_right_mono[OF a0_lt_M, of "a1 * ?M"]
      by (simp add: two_a_def algebra_simps)
    also have "... = (a1 + 1) * ?M"
      by (simp add: algebra_simps)
    also have "... \<le> b1 * ?M"
      using `a1 + 1 \<le> b1` by (rule mult_right_mono) simp
    also have "... \<le> two_b"
      unfolding two_b_def using assms by (simp add: algebra_simps)
    finally have two_lt: "two_a < two_b" .
    have low_lt: "low_a < low_b"
      unfolding low_a_def low_b_def
      using eq2 add_strict_right_mono[OF two_lt, of "a2 * ?M^2"]
      by (simp add: two_a_def two_b_def)
    show "X < Y" using low_lt eq3 by (simp add: X_def Y_def)
  qed

  have case0: "a3 = b3 \<Longrightarrow> a2 = b2 \<Longrightarrow> a1 = b1 \<Longrightarrow> a0 < b0 \<Longrightarrow> X < Y"
  proof -
    assume eq3: "a3 = b3" and eq2: "a2 = b2" and eq1: "a1 = b1" and a0_lt: "a0 < b0"
    show "X < Y"
      using a0_lt eq3 eq2 eq1
      by (simp add: X_def Y_def low_a_def low_b_def two_a_def two_b_def)
  qed

  have "X < Y = ?R"
  proof
    assume L: "X < Y"
    show ?R
    proof (cases "a3 < b3")
      case True
      then show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "a3 = b3")
        case False
        then have b3_lt_a3: "b3 < a3"
          using `\<not> a3 < b3` by linarith
        have "Y < X"
        proof -
          have "b3 + 1 \<le> a3" using b3_lt_a3 by linarith
          have "Y = low_b + b3 * ?M^3" by (simp add: Y_def)
          have "Y < ?M^3 + b3 * ?M^3"
            using add_strict_right_mono[OF low_b_lt, of "b3 * ?M^3"]
            by (simp add: Y_def algebra_simps)
          also have "... = (b3 + 1) * ?M^3"
            by (simp add: algebra_simps)
          also have "... \<le> a3 * ?M^3"
            using `b3 + 1 \<le> a3` by (rule mult_right_mono) simp
          also have "... \<le> X"
            unfolding X_def
            using low_a_ge by (simp add: algebra_simps)
          finally show ?thesis .
        qed
        with L show ?thesis by linarith
      next
        case eq3: True
        have L2: "low_a + a3 * ?M^3 < low_b + b3 * ?M^3"
          using L by (simp add: X_def Y_def)
        have low_ineq: "low_a < low_b"
          using L2 eq3 by simp
        show ?thesis
        proof (cases "a2 < b2")
          case True
          then show ?thesis using eq3 by simp
        next
          case False
          show ?thesis
          proof (cases "a2 = b2")
            case False
            then have b2_lt_a2: "b2 < a2"
              using `\<not> a2 < b2` by linarith
            have "low_b < low_a"
            proof -
              have "b2 + 1 \<le> a2" using b2_lt_a2 by linarith
              have "low_b = two_b + b2 * ?M^2" by (simp add: low_b_def two_b_def algebra_simps)
              have "low_b < ?M^2 + b2 * ?M^2"
                using add_strict_right_mono[OF two_b_lt, of "b2 * ?M^2"]
                by (simp add: low_b_def two_b_def algebra_simps)
              also have "... = (b2 + 1) * ?M^2"
                by (simp add: algebra_simps)
              also have "... \<le> a2 * ?M^2"
                using `b2 + 1 \<le> a2` by (rule mult_right_mono) simp
              also have "... \<le> low_a"
                unfolding low_a_def
                using two_a_ge[unfolded two_a_def] by (simp add: algebra_simps)
              finally show ?thesis .
            qed
            with low_ineq show ?thesis by linarith
          next
            case eq2: True
            have L3: "two_a < two_b"
              using low_ineq[unfolded low_a_def low_b_def] eq2
              by (simp add: two_a_def two_b_def )
            show ?thesis
            proof (cases "a1 < b1")
              case True
              then show ?thesis using eq3 eq2 by simp
            next
              case False
              show ?thesis
              proof (cases "a1 = b1")
                case False
                then have b1_lt_a1: "b1 < a1"
                  using `\<not> a1 < b1` by linarith
                have "two_b < two_a"
                proof -
                  have "b1 + 1 \<le> a1" using b1_lt_a1 by linarith
                  have "two_b = b0 + b1 * ?M" by (simp add: two_b_def)
                  have "two_b < ?M + b1 * ?M"
                    using add_strict_right_mono[OF b0_lt_M, of "b1 * ?M"]
                    by (simp add: two_b_def algebra_simps)
                  also have "... = (b1 + 1) * ?M"
                    by (simp add: algebra_simps)
                  also have "... \<le> a1 * ?M"
                    using `b1 + 1 \<le> a1` by (rule mult_right_mono) simp
                  also have "... \<le> two_a"
                    unfolding two_a_def
                    using assms by (simp add: algebra_simps)
                  finally show ?thesis .
                qed
                with L3 show ?thesis by linarith
              next
                case eq1: True
                have L4: "a0 < b0"
                  using L3[unfolded two_a_def two_b_def] eq1
                  by simp
                then show ?thesis using eq3 eq2 eq1 by simp
              qed
            qed
          qed
        qed
      qed
    qed
  next
    assume R: ?R
    show "X < Y"
      using R by (elim disjE) (auto intro: case3 case2 case1 case0)
  qed
  then show ?thesis unfolding X_orig Y_orig by simp
qed

lemma uint256_to_int_lt_iff_limb_lt:
  fixes x y :: uint256
  shows "uint256_to_int x < uint256_to_int y \<longleftrightarrow>
         (uint (z3 x) < uint (z3 y) \<or>
          uint (z3 x) = uint (z3 y) \<and> uint (z2 x) < uint (z2 y) \<or>
          uint (z3 x) = uint (z3 y) \<and> uint (z2 x) = uint (z2 y) \<and> uint (z1 x) < uint (z1 y) \<or>
          uint (z3 x) = uint (z3 y) \<and> uint (z2 x) = uint (z2 y) \<and> uint (z1 x) = uint (z1 y) \<and> uint (z0 x) < uint (z0 y))"
proof -
  have x0_ge: "0 \<le> uint (z0 x)" by (rule uint_nonnegative)
  have x0_lt: "uint (z0 x) < 2^64" by (rule uint_lt_2p64)
  have x1_ge: "0 \<le> uint (z1 x)" by (rule uint_nonnegative)
  have x1_lt: "uint (z1 x) < 2^64" by (rule uint_lt_2p64)
  have x2_ge: "0 \<le> uint (z2 x)" by (rule uint_nonnegative)
  have x2_lt: "uint (z2 x) < 2^64" by (rule uint_lt_2p64)
  have x3_ge: "0 \<le> uint (z3 x)" by (rule uint_nonnegative)
  have x3_lt: "uint (z3 x) < 2^64" by (rule uint_lt_2p64)
  have y0_ge: "0 \<le> uint (z0 y)" by (rule uint_nonnegative)
  have y0_lt: "uint (z0 y) < 2^64" by (rule uint_lt_2p64)
  have y1_ge: "0 \<le> uint (z1 y)" by (rule uint_nonnegative)
  have y1_lt: "uint (z1 y) < 2^64" by (rule uint_lt_2p64)
  have y2_ge: "0 \<le> uint (z2 y)" by (rule uint_nonnegative)
  have y2_lt: "uint (z2 y) < 2^64" by (rule uint_lt_2p64)
  have y3_ge: "0 \<le> uint (z3 y)" by (rule uint_nonnegative)
  have y3_lt: "uint (z3 y) < 2^64" by (rule uint_lt_2p64)
  have lex:
    "uint (z0 x) + uint (z1 x) * 2^64 + uint (z2 x) * 2^128 + uint (z3 x) * 2^192 <
     uint (z0 y) + uint (z1 y) * 2^64 + uint (z2 y) * 2^128 + uint (z3 y) * 2^192 =
     (uint (z3 x) < uint (z3 y) \<or>
      uint (z3 x) = uint (z3 y) \<and> uint (z2 x) < uint (z2 y) \<or>
      uint (z3 x) = uint (z3 y) \<and> uint (z2 x) = uint (z2 y) \<and> uint (z1 x) < uint (z1 y) \<or>
      uint (z3 x) = uint (z3 y) \<and> uint (z2 x) = uint (z2 y) \<and> uint (z1 x) = uint (z1 y) \<and> uint (z0 x) < uint (z0 y))"
    by (rule limb256_lt_iff_lex[OF x0_ge x0_lt x1_ge x1_lt x2_ge x2_lt x3_ge x3_lt
                                  y0_ge y0_lt y1_ge y1_lt y2_ge y2_lt y3_ge y3_lt])
  have xval: "uint256_to_int x = uint (z0 x) + uint (z1 x) * 2^64 + uint (z2 x) * 2^128 + uint (z3 x) * 2^192"
    unfolding uint256_to_int_def Let_def by (simp add: int_shiftl_eq_mult)
  have yval: "uint256_to_int y = uint (z0 y) + uint (z1 y) * 2^64 + uint (z2 y) * 2^128 + uint (z3 y) * 2^192"
    unfolding uint256_to_int_def Let_def by (simp add: int_shiftl_eq_mult)
  show ?thesis
    unfolding xval yval
    using lex by simp
qed

lemma uint256_lt_iff_int_lt:
  fixes x y :: uint256
  shows "x <\<^sub>u y \<longleftrightarrow> uint256_to_int x < uint256_to_int y"
proof -
  have int_iff: "uint256_to_int x < uint256_to_int y \<longleftrightarrow>
         (uint (z3 x) < uint (z3 y) \<or>
          uint (z3 x) = uint (z3 y) \<and> uint (z2 x) < uint (z2 y) \<or>
          uint (z3 x) = uint (z3 y) \<and> uint (z2 x) = uint (z2 y) \<and> uint (z1 x) < uint (z1 y) \<or>
          uint (z3 x) = uint (z3 y) \<and> uint (z2 x) = uint (z2 y) \<and> uint (z1 x) = uint (z1 y) \<and> uint (z0 x) < uint (z0 y))"
    by (rule uint256_to_int_lt_iff_limb_lt)
  show ?thesis
    using int_iff uint256_lt_iff_limb_lt[of x y] by blast
qed

lemma uint256_lt_to_int:
  fixes x y :: uint256
  assumes "x <\<^sub>u y"
  shows "uint256_to_int x < uint256_to_int y"
  using assms uint256_lt_iff_int_lt by blast

lemma dLen_lt_imp_lt:
  fixes x y :: uint256
  assumes "dLen x < dLen y"
  shows "x <\<^sub>u y"
proof -
  have d_pos: "0 < dLen y"
    using assms by linarith
  have upper: "uint256_to_int x < 2 ^ (64 * dLen x)"
    by (rule uint256_to_int_dLen_upper)
  have lower: "2 ^ (64 * (dLen y - 1)) \<le> uint256_to_int y"
    using d_pos by (rule uint256_to_int_dLen_lower)
  have exp_le: "64 * dLen x \<le> 64 * (dLen y - 1)"
    using assms by linarith
  have pow_le: "(2::int) ^ (64 * dLen x) \<le> (2::int) ^ (64 * (dLen y - 1))"
    using exp_le by (rule power_increasing) simp
  have "uint256_to_int x < uint256_to_int y"
    using upper pow_le lower by linarith
  then show ?thesis
    using uint256_lt_iff_int_lt by blast
qed

lemma uint256_Isuint64_y:
  fixes x y :: uint256
  assumes "y \<noteq> uint256_zero" and "Isuint64 x" and "\<not> x <\<^sub>u y"
  shows "Isuint64 y"
proof (rule ccontr)
  assume not_y: "\<not> Isuint64 y"
  have x_len: "dLen x \<le> 1"
    using assms(2) by (rule dLen_Isuint64_le1)
  have y_len: "1 < dLen y"
    using assms(1) not_y by (rule not_Isuint64_dLen_gt1)
  have "dLen x < dLen y"
    using x_len y_len by linarith
  hence "x <\<^sub>u y"
    by (rule dLen_lt_imp_lt)
  with assms(3) show False by simp
qed

lemma dLen_lt_imp_int_lt:
  fixes u d :: uint256
  assumes "dLen u < dLen d"
  shows "uint256_to_int u < uint256_to_int d"
proof -
  have d_pos: "0 < dLen d"
    using assms by linarith
  have upper: "uint256_to_int u < 2 ^ (64 * dLen u)"
    by (rule uint256_to_int_dLen_upper)
  have lower: "2 ^ (64 * (dLen d - 1)) \<le> uint256_to_int d"
    using d_pos by (rule uint256_to_int_dLen_lower)
  have exp_le: "64 * dLen u \<le> 64 * (dLen d - 1)"
    using assms by linarith
  have pow_le: "(2::int) ^ (64 * dLen u) \<le> (2::int) ^ (64 * (dLen d - 1))"
    using exp_le by (rule power_increasing) simp
  show ?thesis
    using upper pow_le lower by linarith
qed

lemma uint256_div_mod_lt:
  fixes x y :: uint256
  assumes "y \<noteq> uint256_zero" and "x <\<^sub>u y"
  shows "uint256_to_int (x div\<^sub>u y) = uint256_to_int x div uint256_to_int y \<and>
         uint256_to_int (x mod\<^sub>u y) = uint256_to_int x mod uint256_to_int y"
proof -
  have x_lt: "uint256_to_int x < uint256_to_int y"
    using assms(2) by (rule uint256_lt_to_int)
  have y_pos: "0 < uint256_to_int y"
    using uint256_to_int_nonneg[of x] x_lt by linarith
  have x_nonneg: "0 \<le> uint256_to_int x"
    by (rule uint256_to_int_nonneg)
  have q1: "uint256_to_int (x div\<^sub>u y) = 0"
    by (metis uint256_div_lt[OF assms(2)] uint256_to_int_zero)
  have q2: "uint256_to_int x div uint256_to_int y = 0"
    using x_nonneg x_lt by simp
  have r1: "uint256_to_int (x mod\<^sub>u y) = uint256_to_int x"
    by (simp add: uint256_mod_lt[OF assms(2)])
  have r2: "uint256_to_int x mod uint256_to_int y = uint256_to_int x"
    using x_nonneg x_lt by simp
  show ?thesis
    using q1 q2 r1 r2 by simp
qed

lemma uint256_div_mod_u64:
  fixes x y :: uint256
  assumes "y \<noteq> uint256_zero" and "\<not> x <\<^sub>u y" and "Isuint64 x"
  shows "uint256_to_int (x div\<^sub>u y) = uint256_to_int x div uint256_to_int y \<and>
         uint256_to_int (x mod\<^sub>u y) = uint256_to_int x mod uint256_to_int y"
proof -
  have y64: "Isuint64 y"
    using assms by (metis uint256_Isuint64_y)
  have x_int: "uint256_to_int x = uint (z0 x)"
    using assms(3) by (rule uint256_to_int_Isuint64)
  have y_int: "uint256_to_int y = uint (z0 y)"
    using y64 by (rule uint256_to_int_Isuint64)

  have ynz: "z0 y \<noteq> 0"
    using y64 assms(1)
    by (cases y) (auto simp: Isuint64_def uint256_zero_def)
  have q: "uint256_to_int (x div\<^sub>u y) = uint256_to_int x div uint256_to_int y"
  proof -
    have div_body: "x div\<^sub>u y = \<lparr>z0 = z0 x div z0 y, z1 = 0, z2 = 0, z3 = 0\<rparr>"
      using assms ynz unfolding uint256_div_def uint256_one_def
      by (auto simp: div_word_self)
    have "uint256_to_int (x div\<^sub>u y) = uint (z0 x div z0 y)"
      using div_body unfolding uint256_to_int_def Let_def
      by (simp add: int_shiftl_eq_mult)
    also have "... = uint (z0 x) div uint (z0 y)"
      by (rule uint_div)
    also have "... = uint256_to_int x div uint256_to_int y"
      using x_int y_int by simp
    finally show ?thesis .
  qed

  have r: "uint256_to_int (x mod\<^sub>u y) = uint256_to_int x mod uint256_to_int y"
  proof (cases "x =\<^sub>u y")
    case True
    have xy: "x = y"
      using True by (simp add: uint256_eq_def)
    have r1: "uint256_to_int (x mod\<^sub>u y) = 0"
    proof -
      have "x mod\<^sub>u y = uint256_zero"
        unfolding Mod_def
        using True by simp
      then show ?thesis by (simp add: uint256_to_int_zero)
    qed
    have r2: "uint256_to_int x mod uint256_to_int y = 0"
      using xy by simp
    show ?thesis using r1 r2 by simp
  next
    case False
    have x_ne_y: "\<not> x =\<^sub>u y" using False by simp
    have mod_body: "x mod\<^sub>u y = \<lparr>z0 = z0 x mod z0 y, z1 = 0, z2 = 0, z3 = 0\<rparr>"
      unfolding Mod_def
      using assms(1) x_ne_y assms(2) assms(3)
      by (simp add: IsZero_eq_zero)
    have "uint256_to_int (x mod\<^sub>u y) = uint (z0 x mod z0 y)"
      using mod_body unfolding uint256_to_int_def Let_def
      by (simp add: int_shiftl_eq_mult)
    also have "... = uint (z0 x) mod uint (z0 y)"
      by (rule uint_mod)
    also have "... = uint256_to_int x mod uint256_to_int y"
      using x_int y_int by simp
    finally show ?thesis .
  qed

  show ?thesis using q r by simp
qed

lemma knuth_normalized_input:
  fixes u d dn un :: uint256 and u4 :: u64
  assumes nz: "d \<noteq> uint256_zero" and multi: "1 < dLen d"
    and guard: "dLen d \<le> dLen u"
    and shift: "s = LeadingZeros64 (getword d (dLen d - 1))"
    and dn: "dn = dnStorage d (dLen d) s"
    and un: "(un,u4) = normalize_u u (dLen u) s"
  shows "2 \<le> dLen dn"
    and "dLen dn \<le> dLen u"
    and "dLen u \<le> 4"
    and "2^63 \<le> uint (getword dn (dLen dn-1))"
    and "0 < uint256_to_int dn"
    and "uint256_to_int dn < (2^64)^(dLen dn)"
    and "uint256_u4_to_int (un,u4) < uint256_to_int dn * (2^64)^(dLen u-dLen dn+1)"
    and "s < 64"
    and "dLen dn = dLen d"
    and "uint256_to_int dn = uint256_to_int d * 2^s"
    and "uint256_u4_to_int (un,u4) = uint256_to_int u * 2^s"
    and "0 < uint256_to_int d"
proof -
  let ?B = "(2::int)^64"
  let ?P = "(2::int)^s"
  let ?m = "dLen d"
  let ?l = "dLen u"
  let ?k = "?l-?m+1"
  have mpos: "0 < ?m" using multi by arith
  have ml: "dLen dn = ?m" using dnStorage_dLen[OF nz shift] dn by simp
  show "2 \<le> dLen dn" using multi ml by arith
  show "dLen dn \<le> dLen u" using guard ml by simp
  show "dLen u \<le> 4" by (simp add: dLen_def)
  show "2^63 \<le> uint (getword dn (dLen dn-1))"
    using dnStorage_top_lower[OF nz shift] ml dn by simp
  have top_nz: "getword d (dLen d-1) \<noteq> 0"
    using nz unfolding getword_def dLen_def uint256_zero_def
    by (cases d; auto split: if_splits)
  have slt: "s < 64" using LeadingZeros64_lt_64[OF top_nz] shift by simp
  show "s < 64" by (rule slt)
  have dscale: "uint256_to_int dn = uint256_to_int d * ?P"
    using dnStorage_scale[OF nz shift] dn by simp
  have uscale: "uint256_u4_to_int (un,u4) = uint256_to_int u * ?P"
    using normalize_u_scale[OF slt, of u] un by simp
  have dlow: "?B^(?m-1) \<le> uint256_to_int d"
    using uint256_to_int_dLen_lower[OF mpos] by (simp add: power_mult)
  have powpos: "0 < ?B^(?m-1)" by simp
  have dpos: "0 < uint256_to_int d" using dlow powpos by linarith
  show "0 < uint256_to_int dn" using dpos dscale by simp
  show "uint256_to_int dn < ?B^(dLen dn)"
    using uint256_to_int_dLen_upper[of dn] by (simp add: power_mult)
  have up: "uint256_to_int u < ?B^?l"
    using uint256_to_int_dLen_upper[of u] by (simp add: power_mult)
  have exponent: "?m-1+?k = ?l" using guard mpos by arith
  have powers: "?B^(?m-1) * ?B^?k = ?B^?l" by (simp only: power_add[symmetric] exponent)
  have multlow: "?B^(?m-1) * ?B^?k \<le> uint256_to_int d * ?B^?k"
    by (rule mult_right_mono[OF dlow]) simp
  have up2: "?B^?l \<le> uint256_to_int d * ?B^?k"
    using multlow by (simp only: powers)
  have strict: "uint256_to_int u < uint256_to_int d * ?B^?k"
    using up up2 by linarith
  have scaled: "uint256_to_int u * ?P < (uint256_to_int d * ?B^?k) * ?P"
    by (rule mult_strict_right_mono[OF strict]) simp
  show "uint256_u4_to_int (un,u4) < uint256_to_int dn * ?B^(dLen u-dLen dn+1)"
    using scaled ml dscale uscale by (simp add: mult_ac)
  show "dLen dn = dLen d" by (rule ml)
  show "uint256_to_int dn = uint256_to_int d * 2^s" by (rule dscale)
  show "uint256_u4_to_int (un,u4) = uint256_to_int u * 2^s" by (rule uscale)
  show "0 < uint256_to_int d" by (rule dpos)
qed


lemma knuth_denormalized_result:
  fixes u d dn un q r rem un' :: uint256 and u4 u4' :: u64
  assumes nz: "d \<noteq> uint256_zero" and multi: "1 < dLen d"
    and guard: "dLen d \<le> dLen u"
    and shift: "s = LeadingZeros64 (getword d (dLen d-1))"
    and dn: "dn = dnStorage d (dLen d) s"
    and un: "(un,u4) = normalize_u u (dLen u) s"
    and rem: "rem = uint256_zero"
    and r: "r = rem_loop rem un' u4' (dLen d-1) (dLen d-1) s"
    and qvalue: "uint256_to_int q = uint256_u4_to_int (un,u4) div uint256_to_int dn"
    and rvalue: "uint256_u4_to_int (un',u4') = uint256_u4_to_int (un,u4) mod uint256_to_int dn"
  shows "uint256_to_int q = uint256_to_int u div uint256_to_int d \<and>
    uint256_to_int r = uint256_to_int u mod uint256_to_int d"
proof -
  note input = knuth_normalized_input[OF nz multi guard shift dn un]
  have mpos: "0<dLen d" using multi by arith
  have ml: "dLen d \<le> 4" using input(2,3,9) by arith
  have nlt: "dLen d-1 < 4" using ml mpos by arith
  have nSuc: "dLen d-1+1 = dLen dn" using mpos input(9) by arith
  have rlt: "uint256_u4_to_int (un',u4') < uint256_to_int dn"
    using rvalue pos_mod_bound[OF input(5), of "uint256_u4_to_int (un,u4)"] by simp
  have rbound: "uint256_u4_to_int (un',u4') < (2^64)^(dLen d-1+1)"
    using rlt input(6) by (simp only: nSuc; linarith)
  have denormalized: "uint256_to_int r = uint256_u4_to_int (un',u4') div 2^s"
    using rem_loop_supported[OF nlt input(8) rbound] rem r by simp
  have qfinal: "uint256_to_int q = uint256_to_int u div uint256_to_int d"
    using qvalue input(10,11) shift_div_correct[OF input(12), of "uint256_to_int u" s]
    by simp
  have rfinal: "uint256_to_int r = uint256_to_int u mod uint256_to_int d"
    using denormalized rvalue input(10,11)
      shift_rem_correct[OF input(12), of "uint256_to_int u" s]
    by simp
  show ?thesis using qfinal rfinal by simp
qed


lemma udivremKnuth_branch_correct:
  fixes u d dn un rem q un' r :: uint256 and u4 u4' :: u64
  assumes nz: "d \<noteq> uint256_zero" and multi: "1 < dLen d"
    and guard: "dLen d \<le> dLen u"
    and shift: "shift = LeadingZeros64 (getword d (dLen d-1))"
    and dn: "dn = dnStorage d (dLen d) shift"
    and norm: "(un,u4) = normalize_u u (dLen u) shift"
    and rem: "rem = uint256_zero"
    and knuth: "udivremKnuth uint256_zero un u4 dn (dLen u) = (q,un',u4')"
    and r: "r = rem_loop rem un' u4' (dLen d-1) (dLen d-1) shift"
  shows "uint256_to_int q = uint256_to_int u div uint256_to_int d \<and>
    uint256_to_int r = uint256_to_int u mod uint256_to_int d"
proof -
  note input = knuth_normalized_input[OF nz multi guard shift dn norm]
  have bound: "uint256_u4_to_int (un,u4) <
      uint256_to_int dn * (2^64)^Suc (dLen u-dLen dn)"
    using input(7) by simp
  have qvalue: "uint256_to_int q = uint256_u4_to_int (un,u4) div uint256_to_int dn"
    and rvalue: "uint256_u4_to_int (un',u4') = uint256_u4_to_int (un,u4) mod uint256_to_int dn"
    using udivremKnuth_correct[OF input(1-6) bound] knuth by simp_all
  show ?thesis
    by (rule knuth_denormalized_result[OF nz multi guard shift dn norm rem r qvalue rvalue])
qed


lemma udivrem_correct:
  fixes u d :: uint256
  assumes "d \<noteq> uint256_zero"
  shows "uint256_to_int (fst (udivrem uint256_zero u d)) = uint256_to_int u div uint256_to_int d \<and>
         uint256_to_int (snd (udivrem uint256_zero u d)) = uint256_to_int u mod uint256_to_int d"
proof (cases "dLen u < dLen d")
  case True
  have short: "udivrem uint256_zero u d = (uint256_zero, u)"
    unfolding udivrem_def
    using assms True by simp
  have u_lt_d: "uint256_to_int u < uint256_to_int d"
    using True by (rule dLen_lt_imp_int_lt)
  have u_nonneg: "0 \<le> uint256_to_int u"
    by (rule uint256_to_int_nonneg)
  have q: "uint256_to_int (fst (udivrem uint256_zero u d)) = 0"
    using short by (simp add: uint256_to_int_zero)
  have qr: "uint256_to_int u div uint256_to_int d = 0"
    using u_nonneg u_lt_d by simp
  have r: "uint256_to_int (snd (udivrem uint256_zero u d)) = uint256_to_int u"
    using short by simp
  have rr: "uint256_to_int u mod uint256_to_int d = uint256_to_int u"
    using u_nonneg u_lt_d by simp
  show ?thesis using q qr r rr by simp
next
  case False
  have not_short: "\<not> dLen u < dLen d" using False by simp
  show ?thesis
  proof (cases "dLen d = 1")
    case True
    have d1: "dLen d = 1" using True by simp
    define shift where "shift = LeadingZeros64 (getword d (dLen d - 1))"
    define dn where "dn = dnStorage d (dLen d) shift"
    define un where "un = fst (normalize_u u (dLen u) shift)"
    define u4 :: u64 where "u4 = snd (normalize_u u (dLen u) shift)"
    obtain q r where pair: "udivremBy1 uint256_zero un (dLen u) (getword dn 0) u4 = (q, r)"
      by (cases "udivremBy1 uint256_zero un (dLen u) (getword dn 0) u4") auto
    have body: "udivrem uint256_zero u d = (q, SetUint64 (r >> shift))"
    proof -
      have norm: "normalize_u u (dLen u) shift = (un, u4)"
        by (simp add: un_def u4_def surjective_pairing)
      show ?thesis
        unfolding udivrem_def
        using assms not_short True pair d1 norm
        by (simp add: shift_def dn_def Let_def)
    qed
    have branch: "uint256_to_int q = uint256_to_int u div uint256_to_int d \<and>
                  uint256_to_int (SetUint64 (r >> shift)) = uint256_to_int u mod uint256_to_int d"
      by (rule udivremBy1_branch_correct[OF assms d1 shift_def dn_def un_def u4_def pair])
    then show ?thesis
      using body branch by simp
  next
    case False
    have d_pos_nat: "0 < dLen d"
      using assms by (rule dLen_pos)
    have d_gt1: "1 < dLen d"
      using False d_pos_nat by linarith
    have len_guard: "dLen d \<le> dLen u" using not_short by arith
    define shift where "shift = LeadingZeros64 (getword d (dLen d - 1))"
    define dn where "dn = dnStorage d (dLen d) shift"
    define un where "un = fst (normalize_u u (dLen u) shift)"
    define u4 :: u64 where "u4 = snd (normalize_u u (dLen u) shift)"
    define rem where "rem = uint256_zero"
    obtain q un' u4' where knuth: "udivremKnuth uint256_zero un u4 dn (dLen u) = (q, un', u4')"
      by (cases "udivremKnuth uint256_zero un u4 dn (dLen u)") auto
    define r where "r = rem_loop rem un' u4' (dLen d - 1) (dLen d - 1) shift"
    have norm: "(un, u4) = normalize_u u (dLen u) shift"
      by (simp add: un_def u4_def surjective_pairing)
    have body: "udivrem uint256_zero u d = (q, r)"
    proof -
      have norm: "normalize_u u (dLen u) shift = (un, u4)"
        by (simp add: un_def u4_def surjective_pairing)
      show ?thesis
        unfolding udivrem_def
        using assms not_short False knuth norm
        by (simp add: shift_def dn_def rem_def r_def Let_def)
    qed
    have branch: "uint256_to_int q = uint256_to_int u div uint256_to_int d \<and>
                  uint256_to_int r = uint256_to_int u mod uint256_to_int d"
      by (rule udivremKnuth_branch_correct[OF assms d_gt1 len_guard shift_def dn_def norm rem_def knuth r_def])
    then show ?thesis
      using body branch by simp
  qed
qed

lemma uint256_div_mod_udivrem:
  fixes x y :: uint256
  assumes "y \<noteq> uint256_zero" and "\<not> x <\<^sub>u y" and "\<not> Isuint64 x"
  shows "uint256_to_int (x div\<^sub>u y) = uint256_to_int x div uint256_to_int y \<and>
         uint256_to_int (x mod\<^sub>u y) = uint256_to_int x mod uint256_to_int y"
proof -
  have q: "uint256_to_int (x div\<^sub>u y) = uint256_to_int x div uint256_to_int y"
  proof (cases "x = y")
    case True
    have ynz: "uint256_to_int y \<noteq> 0"
      using uint256_to_int_dLen_lower[OF dLen_pos[OF assms(1)]]
        zero_less_power[of "2::int" "64*(dLen y-1)"] by linarith
    show ?thesis using True assms ynz
      by (simp add: uint256_div_def uint256_one_def uint256_to_int_def Let_def int_shiftl_eq_mult)
  next
    case False
    have "x div\<^sub>u y = (case udivrem uint256_zero x y of (quot, rem) \<Rightarrow> quot)"
      unfolding uint256_div_def
      using assms False by simp
    also have "... = fst (udivrem uint256_zero x y)"
      by (cases "udivrem uint256_zero x y") simp
    finally have div_eq: "x div\<^sub>u y = fst (udivrem uint256_zero x y)" .
    have udivrem_eq: "uint256_to_int (fst (udivrem uint256_zero x y)) = uint256_to_int x div uint256_to_int y \<and>
                      uint256_to_int (snd (udivrem uint256_zero x y)) = uint256_to_int x mod uint256_to_int y"
      by (rule udivrem_correct[OF assms(1)])
    show ?thesis
      using div_eq udivrem_eq by simp
  qed
  have r: "uint256_to_int (x mod\<^sub>u y) = uint256_to_int x mod uint256_to_int y"
  proof (cases "x =\<^sub>u y")
    case True
    have xy: "x = y"
      using True by (simp add: uint256_eq_def)
    have r1: "uint256_to_int (x mod\<^sub>u y) = 0"
    proof -
      have "x mod\<^sub>u y = uint256_zero"
        unfolding Mod_def
        using True by simp
      then show ?thesis by (simp add: uint256_to_int_zero)
    qed
    have r2: "uint256_to_int x mod uint256_to_int y = 0"
      using xy by simp
    show ?thesis using r1 r2 by simp
  next
    case False
    have x_ne_y: "\<not> x =\<^sub>u y" using False by simp
    have "x mod\<^sub>u y = (case udivrem uint256_zero x y of (quot, rem) \<Rightarrow> rem)"
      unfolding Mod_def
      using assms(1) x_ne_y assms(2) assms(3)
      by (simp add: IsZero_eq_zero)
    also have "... = snd (udivrem uint256_zero x y)"
      by (cases "udivrem uint256_zero x y") simp
    finally have mod_eq: "x mod\<^sub>u y = snd (udivrem uint256_zero x y)" .
    have udivrem_eq: "uint256_to_int (fst (udivrem uint256_zero x y)) = uint256_to_int x div uint256_to_int y \<and>
                      uint256_to_int (snd (udivrem uint256_zero x y)) = uint256_to_int x mod uint256_to_int y"
      by (rule udivrem_correct[OF assms(1)])
    show ?thesis
      using mod_eq udivrem_eq by simp
  qed
  show ?thesis using q r by simp
qed

lemma uint256_div_mod_correct_ax:
  fixes x y :: uint256
  assumes "y \<noteq> uint256_zero"
  shows "uint256_to_int (x div\<^sub>u y) = uint256_to_int x div uint256_to_int y \<and>
         uint256_to_int (x mod\<^sub>u y) = uint256_to_int x mod uint256_to_int y"
proof (cases "x <\<^sub>u y")
  case True
  then show ?thesis
    using assms by (metis uint256_div_mod_lt)
next
  case False
  have nlt: "\<not> x <\<^sub>u y" using False by simp
  show ?thesis
  proof (cases "Isuint64 x")
    case True
    then show ?thesis
      using assms nlt by (metis uint256_div_mod_u64)
  next
    case False
    then have nis64: "\<not> Isuint64 x" by simp
    then show ?thesis
      using assms nlt nis64 by (metis uint256_div_mod_udivrem)
  qed
qed

lemma uint256_div_correct:
  fixes x y :: uint256
  assumes "y \<noteq> uint256_zero"
  shows "uint256_to_int (x div\<^sub>u y) = uint256_to_int x div uint256_to_int y"
  using assms uint256_div_mod_correct_ax by metis

lemma uint256_mod_correct:
  fixes x y :: uint256
  assumes "y \<noteq> uint256_zero"
  shows "uint256_to_int (x mod\<^sub>u y) = uint256_to_int x mod uint256_to_int y"
  using assms uint256_div_mod_correct_ax by metis


text \<open>The complete division proof adds only conservative definitions to
its arithmetic imports and uses no proof oracle.\<close>

ML \<open>
  val checked = @{thms Div64_correct udivremBy1_correct udivremKnuth_correct
    udivrem_correct uint256_div_correct uint256_mod_correct
    uint256_div_zero uint256_mod_zero};
  val _ = if forall (null o Thm.hyps_of) checked then ()
    else error "Division correctness contains undischarged hypotheses";
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Division correctness depends on a proof oracle";
  val inherited_axioms = Symtab.make_set
    (map #1 (Theory.all_axioms_of @{theory Exp}));
  val added_axioms = Theory.all_axioms_of @{theory}
    |> filter_out (fn (name, _) => Symtab.defined inherited_axioms name);
  val definitions = Theory.defs_of @{theory}
    |> Defs.all_specifications_of |> maps snd |> map_filter #def |> Symtab.make_set;
  val nondefinitional_axioms = added_axioms
    |> filter_out (fn (name, _) => Symtab.defined definitions name);
  val _ = if null nondefinitional_axioms then ()
    else error ("Division proof introduces axioms: " ^
      commas (map #1 nondefinitional_axioms));
\<close>

end
