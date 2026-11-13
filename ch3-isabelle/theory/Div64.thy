theory Div64
  imports Div_Comparison Div_LenLower
begin

section \<open>DIV/MOD wrapper proof: first lemmas\<close>

lemma uint256_div_zero:
  shows "x div\<^sub>u uint256_zero = uint256_zero"
  by (simp add: uint256_div_def)

lemma uint256_mod_zero:
  shows "x mod\<^sub>u uint256_zero = uint256_zero"
  by (simp add: Mod_def IsZero_def uint256_zero_def)

lemma Sub64_borrow_same:
  fixes x :: u64
  shows "snd (Sub64_borrow x x 0) = 0"
  unfolding Sub64_borrow_def Let_def
  by (simp add: word_bw_comms shiftr_def)

lemma Sub64_borrow_x_zero:
  fixes x :: u64
  shows "Sub64_borrow x 0 0 = (x, 0)"
  unfolding Sub64_borrow_def Let_def
  by (simp add: word_bw_comms shiftr_def or_eq_0_iff)

lemma uint256_lt_irrefl:
  shows "\<not> x <\<^sub>u x"
  by (simp add: uint256_lt_def Sub64_borrow_def Let_def word_bw_comms shiftr_def)

lemma uint256_not_lt_zero:
  shows "\<not> x <\<^sub>u uint256_zero"
proof -
  show ?thesis
    unfolding uint256_lt_def uint256_zero_def
    by (simp add: Sub64_borrow_x_zero)
qed

lemma IsZero_eq_zero:
  shows "IsZero z \<longleftrightarrow> z = uint256_zero"
proof
  assume "IsZero z"
  hence z0: "z0 z = 0" and z1: "z1 z = 0" and z2: "z2 z = 0" and z3: "z3 z = 0"
    unfolding IsZero_def
    by (auto simp add: or_eq_0_iff)
  show "z = uint256_zero"
    using z0 z1 z2 z3
    by (cases z) (simp add: uint256_zero_def)
next
  assume "z = uint256_zero"
  then show "IsZero z"
    unfolding IsZero_def uint256_zero_def
    by simp
qed

lemma uint256_lt_not_eq:
  assumes x_lt: "x <\<^sub>u y"
  shows "x \<noteq>\<^sub>u y"
  unfolding uint256_ne_def
proof (rule notI)
  assume eq: "x =\<^sub>u y"
  hence "x = y"
    unfolding uint256_eq_def
    by (cases x; cases y) auto
  with x_lt have "x <\<^sub>u x" by simp
  with uint256_lt_irrefl[of x] show False by simp
qed

lemma uint256_lt_imp_y_nonzero:
  assumes x_lt: "x <\<^sub>u y"
  shows "y \<noteq> uint256_zero"
proof (rule notI)
  assume y_eq: "y = uint256_zero"
  with x_lt have "x <\<^sub>u uint256_zero" by simp
  with uint256_not_lt_zero[of x] show False by simp
qed

lemma uint256_div_lt:
  assumes x_lt: "x <\<^sub>u y"
  shows "x div\<^sub>u y = uint256_zero"
  unfolding uint256_div_def
  using x_lt by simp

lemma uint256_mod_lt:
  assumes x_lt: "x <\<^sub>u y"
  shows "x mod\<^sub>u y = x"
proof -
  have not_zero: "y \<noteq> uint256_zero"
    by (rule uint256_lt_imp_y_nonzero[OF x_lt])
  have not_eq: "x \<noteq>\<^sub>u y"
    by (rule uint256_lt_not_eq[OF x_lt])
  have not_iszero: "\<not> IsZero y"
    using not_zero by (auto simp add: IsZero_eq_zero)
  show ?thesis
    unfolding Mod_def
    using x_lt not_iszero not_eq[unfolded uint256_ne_def]
    by simp
qed

section \<open>Div64 and reciprocal2by1: structural cases\<close>

lemma Div64_y_zero:
  shows "Div64 hi lo 0 = None"
  unfolding Div64_def
  by simp

lemma Div64_y_le_hi:
  assumes "uint y \<le> uint hi"
  shows "Div64 hi lo y = None"
proof -
  have "y \<le> hi"
    using assms by (simp add: word_le_def)
  then show ?thesis
    unfolding Div64_def
    by simp
qed

lemma Div64_hi_zero:
  assumes "y \<noteq> 0"
  shows "Div64 0 lo y = Some (lo div y, lo mod y)"
  unfolding Div64_def
  using assms
  by simp

lemma option_case_prod_not_None [simp]:
  "(\<And>a b. f a b \<noteq> None) \<Longrightarrow> (case p of (a, b) \<Rightarrow> f a b) \<noteq> None"
  by (cases p) simp

lemma reciprocal2by1_is_some:
  fixes d :: u64
  assumes "d \<noteq> 0" and "2^63 \<le> uint d"
  shows "Div64 (NOT d) (2^64 - 1) d \<noteq> None"
proof -
  have not_d_uint: "uint (NOT d) = 2^64 - 1 - uint d"
  proof -
    have "uint (NOT d) = take_bit 64 (NOT (uint d))"
      by (simp add: unsigned_not_eq)
    also have "... = mask 64 - take_bit 64 (uint d)"
      by (rule take_bit_not_eq_mask_diff)
    also have "... = 2^64 - 1 - uint d"
      using uint_nonnegative[of d] uint_lt2p[where 'a=64, of d]
      by (simp add: take_bit_int_eq_self mask_eq_exp_minus_1)
    finally show ?thesis .
  qed
  have not_le: "\<not> d \<le> NOT d"
  proof (rule notI)
    assume "d \<le> NOT d"
    hence "uint d \<le> uint (NOT d)"
      by (simp add: word_le_def)
    with not_d_uint have "uint d \<le> 2^64 - 1 - uint d"
      by simp
    moreover from assms(2) have "2^64 \<le> 2 * uint d"
      by auto
    ultimately show False
      by linarith
  qed
  show ?thesis
  proof (cases "Div64 (NOT d) (2^64 - 1) d")
    case None
    then show ?thesis
      using assms(1) not_le
      by (cases "NOT d = 0"; simp add: Div64_def Let_def)
  next
    case (Some p)
    then show ?thesis by simp
  qed
qed

lemma Div64_correct_hi_zero:
  fixes lo y :: u64
  assumes "y \<noteq> 0"
  shows "Div64 0 lo y =
         Some (word_of_int (uint lo div uint y),
               word_of_int (uint lo mod uint y))"
  by (simp add: Div64_hi_zero[OF assms] word_div_def word_mod_def)

lemma adjust_q_nat_fst_le:
  fixes r yn0 yn1 un two32 :: u64
  shows "unat (fst (adjust_q_nat n r yn0 yn1 un two32)) \<le> n"
proof (induct n arbitrary: r yn0 yn1 un two32)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have unat_suc: "unat (1 + word_of_nat n :: u64) = Suc n mod 2^64"
  proof -
    have "1 + word_of_nat n = word_of_nat (Suc n)"
      by (metis of_nat_Suc)
    then show ?thesis
      unfolding \<open>1 + word_of_nat n = word_of_nat (Suc n)\<close>
      by (simp add: unat_of_nat del: of_nat_Suc)
  qed
  have IH: "unat (fst (adjust_q_nat n (r + yn1) yn0 yn1 un two32)) \<le> n"
    using Suc by blast
  then show ?case
  proof (cases "of_nat (Suc n) < two32 \<and> of_nat (Suc n) * yn0 \<le> two32 * r + un")
    case True
    have eq: "fst (adjust_q_nat (Suc n) r yn0 yn1 un two32) = word_of_nat (Suc n)"
      using True by simp
    have val: "unat (word_of_nat (Suc n) :: u64) = Suc n mod 2^64"
      using unat_suc by (metis of_nat_Suc)
    show ?thesis
      using eq val by (metis mod_less_eq_dividend)
  next
    case False
    note outer_False = False
    then show ?thesis
    proof (cases "two32 \<le> r + yn1")
      case True
      have eq: "fst (adjust_q_nat (Suc n) r yn0 yn1 un two32) = word_of_nat n"
        using outer_False True by simp
      show ?thesis
        using eq by (metis le_SucI mod_less_eq_dividend unat_of_nat)
    next
      case False
      show ?thesis
        using IH outer_False False
        by auto
    qed
  qed
qed

lemma adjust_q_nat_quot:
  fixes n :: nat and r yn0 yn1 un two32 :: u64
  assumes T: "unat two32 = 2^32"
      and yn0_lt: "unat yn0 < 2^32"
      and un_lt: "unat un < 2^32"
      and r_lt: "unat r < 2^32"
      and yn1_ge: "2^31 \<le> unat yn1"
      and yn1_lt: "unat yn1 < 2^32"
      and n_lt: "n < 2^64"
      and q_lt: "((unat yn1 * n + unat r) * 2^32 + unat un) div (unat yn1 * 2^32 + unat yn0) < 2^32"
      and upper: "((unat yn1 * n + unat r) * 2^32 + unat un) < (n + 1) * (unat yn1 * 2^32 + unat yn0)"
  shows "unat (fst (adjust_q_nat n r yn0 yn1 un two32)) =
         ((unat yn1 * n + unat r) * 2^32 + unat un) div (unat yn1 * 2^32 + unat yn0)"
  using T yn0_lt un_lt r_lt yn1_ge yn1_lt n_lt q_lt upper
proof (induct n arbitrary: r rule: less_induct)
  case (less n)
  from less.prems have T: "unat two32 = 2^32"
    and yn0_lt: "unat yn0 < 2^32"
    and un_lt: "unat un < 2^32"
    and r_lt: "unat r < 2^32"
    and yn1_ge: "2^31 \<le> unat yn1"
    and yn1_lt: "unat yn1 < 2^32"
    and n_lt: "n < 2^64"
    and q_lt: "((unat yn1 * n + unat r) * 2^32 + unat un) div (unat yn1 * 2^32 + unat yn0) < 2^32"
    and upper: "((unat yn1 * n + unat r) * 2^32 + unat un) < (n + 1) * (unat yn1 * 2^32 + unat yn0)"
    by blast+
  define B where "B = (2::nat)^32"
  let ?T = "B"
  let ?Y = "unat yn1 * B + unat yn0"
  let ?N = "(unat yn1 * n + unat r) * B + unat un"
  let ?P = "?Y * n"
  let ?Q = "B * unat r + unat un"
  let ?R = "n * unat yn0"
  have N_eq: "?N = ?P + ?Q - ?R" by (auto simp: algebra_simps)
  have Tpos: "0 < B" unfolding B_def by simp
  have pow31_pos: "0 < (2::nat)^31" by simp
  have yn1_pos: "0 < unat yn1" using yn1_ge pow31_pos by linarith
  have prod_pos: "0 < unat yn1 * B" using yn1_pos Tpos by simp
  have Ypos: "0 < ?Y" using prod_pos by linarith
  have Ypos32: "0 < unat yn1 * 2^32 + unat yn0" using yn1_pos by simp
  have q_bound_upper: "?N < ?T * ?Y"
    using yn1_pos less.prems(8)
    by (auto simp add: B_def div_less_iff_less_mult)
  show "unat (fst (adjust_q_nat n r yn0 yn1 un two32)) =
        ((unat yn1 * n + unat r) * 2^32 + unat un) div (unat yn1 * 2^32 + unat yn0)"
  proof (cases n)
    case 0
    have n0: "n = 0" by fact
    have upper0: "(unat r * 2^32 + unat un) < (unat yn1 * 2^32 + unat yn0)"
    proof -
      from less.prems(9) have upper_n: "((unat yn1 * n + unat r) * 2^32 + unat un) < (n + 1) * (unat yn1 * 2^32 + unat yn0)"
        by assumption
      then show ?thesis using n0 by simp
    qed
    show ?thesis
      unfolding adjust_q_nat.simps
      using n0 upper0 Ypos32
      by simp
  next
    case (Suc m)
    have n_eq: "n = Suc m" by fact
    show ?thesis
    proof (cases "of_nat n < two32")
      case True
      have B_lt_len: "B < 2^64"
        unfolding B_def by simp
      have two32_eq: "two32 = of_nat B"
        using T B_lt_len B_def
        by (simp add: word_unat_eq_iff unat_of_nat)
      have n_take: "take_bit 64 n = n"
      proof -
        have n_mod: "n mod 2^64 = n"
        proof (rule Euclidean_Rings.mod_nat_eqI [of n "2^64" n])
          show "n < 2^64" by (rule less.prems(7))
          show "n \<le> n" by simp
          show "2^64 dvd n - n" by simp
        qed
        show ?thesis
          unfolding take_bit_eq_mod
          by (rule n_mod)
      qed
      have B_take: "take_bit 64 B = B"
      proof -
        have B_mod: "B mod 2^64 = B"
        proof (rule Euclidean_Rings.mod_nat_eqI [of B "2^64" B])
          show "B < 2^64" by (rule B_lt_len)
          show "B \<le> B" by simp
          show "2^64 dvd B - B" by simp
        qed
        show ?thesis
          unfolding take_bit_eq_mod
          by (rule B_mod)
      qed
      have n_lt_T: "n < ?T"
        using True two32_eq n_take B_take
        by (simp add: word_of_nat_less_iff)
      show ?thesis
      proof (cases "of_nat n * yn0 \<le> two32 * r + un")
        case True
        have prod_ineq: "?R \<le> ?Q"
        proof -
          have lhs_lt: "n * unat yn0 < 2^64"
          proof -
            have "n * unat yn0 < B * B"
            proof (rule mult_strict_mono)
              show "n < B" using n_lt_T by simp
              show "unat yn0 < B" using yn0_lt B_def by simp
              show "0 < B" unfolding B_def by simp
              show "0 \<le> unat yn0" by simp
            qed
            moreover have "B * B = 2^64"
              by (simp add: B_def power2_eq_square)
            ultimately show ?thesis by simp
          qed
          have rhs_lt: "B * unat r + unat un < 2^64"
          proof -
            have "B * unat r + unat un < B * B"
            proof -
              have r_succ: "Suc (unat r) \<le> B"
              proof -
                have "Suc (unat r) \<le> 2^32"
                  by (metis Nat.Suc_le_eq r_lt)
                then show ?thesis
                  unfolding B_def by assumption
              qed
              have "B * unat r + unat un < B * unat r + B"
              proof -
                show ?thesis
                  unfolding B_def
                  by (rule add_strict_left_mono [OF un_lt])
              qed
              also have "... = B * Suc (unat r)"
                by (simp add: algebra_simps)
              also have "... \<le> B * B"
                by (rule mult_le_mono2 [OF r_succ])
              finally show ?thesis .
            qed
            moreover have "B * B = 2^64"
              by (simp add: B_def power2_eq_square)
            ultimately show ?thesis by simp
          qed
          have two32_unat: "unat two32 = B"
            using T B_def by simp
          have n_mod: "n mod 2^64 = n"
          proof (rule Euclidean_Rings.mod_nat_eqI [of n "2^64" n])
            show "n < 2^64" by (rule less.prems(7))
            show "n \<le> n" by simp
            show "2^64 dvd n - n" by simp
          qed
          have unat_n: "unat (of_nat n :: u64) = n"
            using n_mod by (simp add: unat_of_nat)
          have lhs_eq: "unat (of_nat n * yn0) = n * unat yn0"
          proof -
            have len64: "LENGTH(64) = 64" by simp
            have uint_n: "uint ((of_nat n) :: u64) = int n"
              using unat_n by (simp add: uint_nat)
            have uint_y: "uint yn0 = int (unat yn0)"
              by (rule uint_nat)
            have uint_lt: "uint ((of_nat n) :: u64) * uint yn0 < 2 ^ LENGTH(64)"
            proof -
              have prod_eq: "uint ((of_nat n) :: u64) * uint yn0 = int n * int (unat yn0)"
                using uint_n uint_y by simp
              also have "... = int (n * unat yn0)"
                by (rule of_nat_mult [symmetric])
              also have "... < int (2^64)"
                using lhs_lt by (rule of_nat_less_iff [THEN iffD2])
              also have "... = 2 ^ LENGTH(64)"
                by (simp add: len64)
              finally show ?thesis .
            qed
            have uint_eq: "uint (of_nat n * yn0) = uint ((of_nat n) :: u64) * uint yn0"
            proof -
              have step: "uint (of_nat n * yn0) = uint ((of_nat n) :: u64) * uint yn0 mod 2 ^ LENGTH(64)"
                by (rule uint_word_ariths(3))
              have mod_eq: "uint ((of_nat n) :: u64) * uint yn0 mod 2 ^ LENGTH(64) = uint ((of_nat n) :: u64) * uint yn0"
              proof (rule mod_pos_pos_trivial)
                show "0 \<le> uint ((of_nat n) :: u64) * uint yn0"
                  by simp
                show "uint ((of_nat n) :: u64) * uint yn0 < 2 ^ LENGTH(64)"
                  by (rule uint_lt)
              qed
              then show ?thesis using step by simp
            qed
            have "unat (of_nat n * yn0) = nat (uint (of_nat n * yn0))"
              by simp
            also have "... = nat (uint ((of_nat n) :: u64) * uint yn0)"
              using uint_eq by (rule arg_cong[where f = nat])
            also have "... = nat (int n * int (unat yn0))"
              using uint_n uint_y by simp
            also have "... = n * unat yn0"
              by (simp add: nat_mult_distrib)
            finally show ?thesis .
          qed
          have prod_lt2: "B * unat r < 2^64"
          proof -
            have r_lt_B: "unat r < B"
              using r_lt B_def by simp
            have "B * unat r < B * B"
              using r_lt_B Tpos by (rule mult_strict_left_mono)
            moreover have "B * B = 2^64"
              by (simp add: B_def power2_eq_square)
            ultimately show ?thesis by simp
          qed
          have prod_eq2: "unat (two32 * r) = B * unat r"
          proof -
            have unat_mult_bound: "unat two32 * unat r < 2 ^ LENGTH(64)"
              using two32_unat prod_lt2 by simp
            have "unat (two32 * r) = unat two32 * unat r"
            proof (rule unat_mult_lem[THEN iffD1])
              show "unat two32 * unat r < 2 ^ LENGTH(64)"
                by (rule unat_mult_bound)
            qed
            then show ?thesis using two32_unat by simp
          qed
          have rhs_eq: "unat (two32 * r + un) = B * unat r + unat un"
          proof -
            have unat_add_bound: "unat (two32 * r) + unat un < 2 ^ LENGTH(64)"
              using rhs_lt prod_eq2 by simp
            have "unat (two32 * r + un) = unat (two32 * r) + unat un"
            proof (rule unat_add_lem[THEN iffD1])
              show "unat (two32 * r) + unat un < 2 ^ LENGTH(64)"
                by (rule unat_add_bound)
            qed
            then show ?thesis using prod_eq2 by simp
          qed
          from True have unat_le: "unat (of_nat n * yn0) \<le> unat (two32 * r + un)"
            by (simp add: word_le_nat_alt)
          show ?thesis
            using unat_le lhs_eq rhs_eq by simp
        qed
        have div_eq: "?N div ?Y = n"
        proof (rule div_nat_eqI)
          show "?Y * n \<le> ?N"
          proof -
            have diff_eq: "?P + ?Q - ?R = ?P + (?Q - ?R)"
              by (rule Nat.diff_add_assoc [OF prod_ineq])
            have N_eq': "?N = ?P + (?Q - ?R)"
              using N_eq diff_eq by simp
            show ?thesis
              unfolding N_eq'
              by (rule Nat.le_add1)
          qed
          show "?N < ?Y * Suc n"
          proof -
            have comm: "(n + 1) * (unat yn1 * 2^32 + unat yn0) =
                        (unat yn1 * 2^32 + unat yn0) * Suc n"
              by (subst Suc_eq_plus1) (rule mult.commute)
            show ?thesis
              unfolding B_def
              by (subst comm[symmetric]) (rule upper)
          qed
        qed
        then show ?thesis
        proof -
          have True_Suc: "of_nat (Suc m) * yn0 \<le> two32 * r + un"
            using True n_eq by simp
          have of_nat_lt_two32: "of_nat (Suc m) < two32"
          proof -
            have Suc_lt_B: "Suc m < B"
              using n_lt_T n_eq by simp
            have unat_Suc: "unat (of_nat (Suc m) :: u64) = Suc m"
              using Suc_lt_B B_lt_len by (simp add: unat_of_nat del: of_nat_Suc)
            have unat_two32: "unat two32 = B"
              using T B_def by simp
            have "unat (of_nat (Suc m) :: u64) < unat two32"
              using Suc_lt_B unat_Suc unat_two32 by simp
            then show ?thesis
              by (simp add: word_less_nat_alt)
          qed
          have adjust_fst_Suc: "fst (adjust_q_nat (Suc m) r yn0 yn1 un two32) = of_nat (Suc m)"
            using True_Suc of_nat_lt_two32 by simp
          have adjust_fst: "fst (adjust_q_nat n r yn0 yn1 un two32) = of_nat n"
            using adjust_fst_Suc n_eq by simp
          have unat_of_nat_n: "unat (of_nat n :: u64) = n"
            using n_lt by (simp add: unat_of_nat)
          have div_eq32: "((unat yn1 * n + unat r) * 2^32 + unat un) div
                          (unat yn1 * 2^32 + unat yn0) = n"
            using div_eq unfolding B_def by simp
          show ?thesis
            using adjust_fst unat_of_nat_n div_eq32 by simp
        qed
      next
        case False
        have prod_false: "\<not> of_nat n * yn0 \<le> two32 * r + un"
          using False by simp
        have prod_gt: "?Q < ?R"
        proof -
          have lhs_lt: "n * unat yn0 < 2^64"
          proof -
            have "n * unat yn0 < B * B"
            proof (rule mult_strict_mono)
              show "n < B" using n_lt_T by simp
              show "unat yn0 < B" using yn0_lt B_def by simp
              show "0 < B" unfolding B_def by simp
              show "0 \<le> unat yn0" by simp
            qed
            moreover have "B * B = 2^64"
              by (simp add: B_def power2_eq_square)
            ultimately show ?thesis by simp
          qed
          have rhs_lt: "B * unat r + unat un < 2^64"
          proof -
            have "B * unat r + unat un < B * B"
            proof -
              have r_succ: "Suc (unat r) \<le> B"
              proof -
                have "Suc (unat r) \<le> 2^32"
                  by (metis Nat.Suc_le_eq r_lt)
                then show ?thesis
                  unfolding B_def by assumption
              qed
              have "B * unat r + unat un < B * unat r + B"
              proof -
                show ?thesis
                  unfolding B_def
                  by (rule add_strict_left_mono [OF un_lt])
              qed
              also have "... = B * Suc (unat r)"
                by (simp add: algebra_simps)
              also have "... \<le> B * B"
                by (rule mult_le_mono2 [OF r_succ])
              finally show ?thesis .
            qed
            moreover have "B * B = 2^64"
              by (simp add: B_def power2_eq_square)
            ultimately show ?thesis by simp
          qed
          have two32_unat: "unat two32 = B"
            using T B_def by simp
          have n_mod: "n mod 2^64 = n"
          proof (rule Euclidean_Rings.mod_nat_eqI [of n "2^64" n])
            show "n < 2^64" by (rule less.prems(7))
            show "n \<le> n" by simp
            show "2^64 dvd n - n" by simp
          qed
          have unat_n: "unat (of_nat n :: u64) = n"
            using n_mod by (simp add: unat_of_nat)
          have lhs_eq: "unat (of_nat n * yn0) = n * unat yn0"
          proof -
            have len64: "LENGTH(64) = 64" by simp
            have uint_n: "uint ((of_nat n) :: u64) = int n"
              using unat_n by (simp add: uint_nat)
            have uint_y: "uint yn0 = int (unat yn0)"
              by (rule uint_nat)
            have uint_lt: "uint ((of_nat n) :: u64) * uint yn0 < 2 ^ LENGTH(64)"
            proof -
              have prod_eq: "uint ((of_nat n) :: u64) * uint yn0 = int n * int (unat yn0)"
                using uint_n uint_y by simp
              also have "... = int (n * unat yn0)"
                by (rule of_nat_mult [symmetric])
              also have "... < int (2^64)"
                using lhs_lt by (rule of_nat_less_iff [THEN iffD2])
              also have "... = 2 ^ LENGTH(64)"
                by (simp add: len64)
              finally show ?thesis .
            qed
            have uint_eq: "uint (of_nat n * yn0) = uint ((of_nat n) :: u64) * uint yn0"
            proof -
              have step: "uint (of_nat n * yn0) = uint ((of_nat n) :: u64) * uint yn0 mod 2 ^ LENGTH(64)"
                by (rule uint_word_ariths(3))
              have mod_eq: "uint ((of_nat n) :: u64) * uint yn0 mod 2 ^ LENGTH(64) = uint ((of_nat n) :: u64) * uint yn0"
              proof (rule mod_pos_pos_trivial)
                show "0 \<le> uint ((of_nat n) :: u64) * uint yn0"
                  by simp
                show "uint ((of_nat n) :: u64) * uint yn0 < 2 ^ LENGTH(64)"
                  by (rule uint_lt)
              qed
              then show ?thesis using step by simp
            qed
            have "unat (of_nat n * yn0) = nat (uint (of_nat n * yn0))"
              by simp
            also have "... = nat (uint ((of_nat n) :: u64) * uint yn0)"
              using uint_eq by (rule arg_cong[where f = nat])
            also have "... = nat (int n * int (unat yn0))"
              using uint_n uint_y by simp
            also have "... = n * unat yn0"
              by (simp add: nat_mult_distrib)
            finally show ?thesis .
          qed
          have prod_lt2: "B * unat r < 2^64"
          proof -
            have r_lt_B: "unat r < B"
              using r_lt B_def by simp
            have "B * unat r < B * B"
              using r_lt_B Tpos by (rule mult_strict_left_mono)
            moreover have "B * B = 2^64"
              by (simp add: B_def power2_eq_square)
            ultimately show ?thesis by simp
          qed
          have prod_eq2: "unat (two32 * r) = B * unat r"
          proof -
            have unat_mult_bound: "unat two32 * unat r < 2 ^ LENGTH(64)"
              using two32_unat prod_lt2 by simp
            have "unat (two32 * r) = unat two32 * unat r"
            proof (rule unat_mult_lem[THEN iffD1])
              show "unat two32 * unat r < 2 ^ LENGTH(64)"
                by (rule unat_mult_bound)
            qed
            then show ?thesis using two32_unat by simp
          qed
          have rhs_eq: "unat (two32 * r + un) = B * unat r + unat un"
          proof -
            have unat_add_bound: "unat (two32 * r) + unat un < 2 ^ LENGTH(64)"
              using rhs_lt prod_eq2 by simp
            have "unat (two32 * r + un) = unat (two32 * r) + unat un"
            proof (rule unat_add_lem[THEN iffD1])
              show "unat (two32 * r) + unat un < 2 ^ LENGTH(64)"
                by (rule unat_add_bound)
            qed
            then show ?thesis using prod_eq2 by simp
          qed
          from False have word_less: "two32 * r + un < of_nat n * yn0"
            by (simp add: not_le)
          then have unat_less: "unat (two32 * r + un) < unat (of_nat n * yn0)"
            by (simp add: word_less_nat_alt)
          show ?thesis
            using unat_less lhs_eq rhs_eq by simp
        qed
        have N_lt_P: "?N < ?P"
        proof -
          have R_le_P: "?R \<le> ?P"
          proof -
            have P_eq: "?P = n * unat yn1 * B + ?R"
              by (simp add: algebra_simps)
            show ?thesis
              unfolding P_eq
              by (rule Nat.le_add2)
          qed
          have P_le_PQ: "?P \<le> ?P + ?Q"
            by (rule Nat.le_add1)
          have le_R: "?R \<le> ?P + ?Q"
            using R_le_P P_le_PQ by (rule order_trans)
          have add_less: "?P + ?Q < ?P + ?R"
            using prod_gt by (rule add_strict_left_mono)
          have N_lt_P_body: "?P + ?Q - ?R < ?P"
            using add_less by (rule less_diff_conv2[OF le_R, THEN iffD2])
          show ?thesis
            using N_eq N_lt_P_body by simp
        qed
        show ?thesis
        proof (cases "two32 \<le> r + yn1")
          case True
          have r_new_ge: "?T \<le> unat r + unat yn1"
          proof -
            have unat_two32_B: "unat two32 = B"
              using T B_def by simp
            have unat_le: "unat two32 \<le> unat (r + yn1)"
              using True by (simp add: word_le_nat_alt)
            have add_bound: "unat r + unat yn1 < 2 ^ LENGTH(64)"
            proof -
              have r_lt_B: "unat r < B"
                using r_lt B_def by simp
              have yn1_lt_B: "unat yn1 < B"
                using yn1_lt B_def by simp
              have sum_lt: "unat r + unat yn1 < B + B"
                using r_lt_B yn1_lt_B by (rule add_less_mono)
              have len64: "LENGTH(64) = 64"
                by simp
              have Bsum_lt: "B + B < 2 ^ LENGTH(64)"
                using len64 by (simp add: B_def)
              show ?thesis
                using sum_lt Bsum_lt by (rule less_trans)
            qed
            have add_eq: "unat (r + yn1) = unat r + unat yn1"
              using add_bound by (rule unat_add_lem[THEN iffD1])
            show ?thesis
              using unat_le add_eq unat_two32_B by simp
          qed
          have m_yn0_lt: "m * unat yn0 < ?T * ?T"
          proof (rule mult_strict_mono)
            have m_lt_B: "m < B" using n_lt_T n_eq by linarith
            show "m < B" by fact
            show "unat yn0 < B" using yn0_lt B_def by simp
            show "0 < B" unfolding B_def by simp
            show "0 \<le> unat yn0" by simp
          qed
          have div_eq: "?N div ?Y = m"
          proof (rule div_nat_eqI)
            show "?Y * m \<le> ?N"
            proof -
              have R_le_YQ: "(Suc m) * unat yn0 \<le> ?Y + ?Q"
              proof -
                have B_times_le: "B * B \<le> B * (unat r + unat yn1)"
                  by (rule mult_le_mono2 [OF r_new_ge])
                have m_yn0_lt_Bsum: "m * unat yn0 < B * (unat r + unat yn1)"
                  using m_yn0_lt B_times_le by (rule less_le_trans)
                have m_yn0_le_Bsum: "m * unat yn0 \<le> B * (unat r + unat yn1)"
                  using m_yn0_lt_Bsum by (rule less_imp_le)
                have distrib: "B * (unat r + unat yn1) = B * unat r + B * unat yn1"
                  by (simp add: add_mult_distrib2)
                have m_yn0_le_Bs: "m * unat yn0 \<le> B * unat r + B * unat yn1"
                  using m_yn0_le_Bsum distrib by simp
                have Suc_mul: "(Suc m) * unat yn0 = m * unat yn0 + unat yn0"
                  by (subst Suc_eq_plus1) (simp add: add_mult_distrib)
                have S_low: "(Suc m) * unat yn0 \<le> B * unat r + B * unat yn1 + unat yn0"
                  unfolding Suc_mul
                  by (rule add_le_mono1 [OF m_yn0_le_Bs])
                have rhs_eq: "B * unat r + B * unat yn1 + unat yn0 + unat un =
                              unat yn1 * B + unat yn0 + (B * unat r + unat un)"
                  by (simp add: add.assoc mult.commute)
                have base_le: "B * unat r + B * unat yn1 + unat yn0 \<le>
                               B * unat r + B * unat yn1 + unat yn0 + unat un"
                  by (rule Nat.le_add1)
                have S_le_base: "(Suc m) * unat yn0 \<le>
                                  B * unat r + B * unat yn1 + unat yn0 + unat un"
                  using S_low base_le by (rule order_trans)
                show ?thesis
                  using S_le_base rhs_eq by simp
              qed
              have N_eq_goal: "?N = ?Y * m + (?Y + ?Q - (Suc m) * unat yn0)"
              proof -
                have N_Suc: "?N = ?Y * Suc m + ?Q - (Suc m) * unat yn0"
                  using N_eq n_eq by simp
                have Y_mul: "?Y * Suc m = ?Y * m + ?Y"
                  by (subst Suc_eq_plus1) (simp add: add_mult_distrib)
                have N_left: "?N = (?Y * m + ?Y) + ?Q - (Suc m) * unat yn0"
                  using N_Suc Y_mul by simp
                have add_assoc: "(?Y * m + ?Y) + ?Q = ?Y * m + (?Y + ?Q)"
                  by (simp add: add.assoc)
                have diff_assoc: "(?Y * m + (?Y + ?Q)) - (Suc m) * unat yn0 =
                                  ?Y * m + (?Y + ?Q - (Suc m) * unat yn0)"
                  by (rule Nat.diff_add_assoc [OF R_le_YQ])
                show ?thesis
                  using N_left add_assoc diff_assoc by simp
              qed
              show ?thesis
                unfolding N_eq_goal
                by (rule Nat.le_add1)
            qed
            show "?N < ?Y * Suc m"
              using N_lt_P n_eq by simp
          qed
          then show ?thesis
          proof -
            have False_Suc: "\<not> of_nat (Suc m) * yn0 \<le> two32 * r + un"
              using prod_false n_eq by simp
            have of_nat_lt_two32: "of_nat (Suc m) < two32"
            proof -
              have Suc_lt_B: "Suc m < B"
                using n_lt_T n_eq by simp
              have unat_Suc: "unat (of_nat (Suc m) :: u64) = Suc m"
                using Suc_lt_B B_lt_len by (simp add: unat_of_nat del: of_nat_Suc)
              have unat_two32: "unat two32 = B"
                using T B_def by simp
              have "unat (of_nat (Suc m) :: u64) < unat two32"
                using Suc_lt_B unat_Suc unat_two32 by simp
              then show ?thesis
                by (simp add: word_less_nat_alt)
            qed
            have adjust_fst_m: "fst (adjust_q_nat (Suc m) r yn0 yn1 un two32) = of_nat m"
              using False_Suc of_nat_lt_two32 True by simp
            have adjust_fst: "fst (adjust_q_nat n r yn0 yn1 un two32) = of_nat m"
              using adjust_fst_m n_eq by simp
            have m_lt: "m < 2^64"
              using n_lt n_eq by linarith
            have unat_of_nat_m: "unat (of_nat m :: u64) = m"
              using m_lt by (simp add: unat_of_nat)
            have div_eq32: "((unat yn1 * n + unat r) * 2^32 + unat un) div
                            (unat yn1 * 2^32 + unat yn0) = m"
              using div_eq unfolding B_def by simp
            show ?thesis
              using adjust_fst unat_of_nat_m div_eq32 by simp
          qed
        next
          case False
          have r_new_lt: "unat (r + yn1) < ?T"
          proof -
            have word_lt: "r + yn1 < two32"
              using False by (simp add: not_le)
            have "unat (r + yn1) < unat two32"
              using word_lt by (simp add: word_less_nat_alt)
            moreover have "unat two32 = B"
              using T B_def by simp
            ultimately show ?thesis by simp
          qed
          have IH: "unat (fst (adjust_q_nat m (r + yn1) yn0 yn1 un two32)) = ?N div ?Y"
          proof -
            have m_lt_n: "m < n"
              by (simp add: n_eq)
            have r_new_lt32: "unat (r + yn1) < 2^32"
              using r_new_lt by (simp add: B_def)
            have m_lt: "m < 2^64"
              using n_lt n_eq by linarith
            have r_add_eq: "unat (r + yn1) = unat r + unat yn1"
            proof -
              have r_lt_B: "unat r < B"
                using r_lt B_def by simp
              have yn1_lt_B: "unat yn1 < B"
                using yn1_lt B_def by simp
              have sum_lt: "unat r + unat yn1 < B + B"
                using r_lt_B yn1_lt_B by (rule add_less_mono)
              have len64: "LENGTH(64) = 64"
                by simp
              have Bsum_lt: "B + B < 2 ^ LENGTH(64)"
                using len64 by (simp add: B_def)
              have add_bound: "unat r + unat yn1 < 2 ^ LENGTH(64)"
                using sum_lt Bsum_lt by (rule less_trans)
              show ?thesis
                using add_bound by (rule unat_add_lem[THEN iffD1])
            qed
            have q_IH: "((unat yn1 * m + unat (r + yn1)) * 2^32 + unat un) div ?Y < 2^32"
            proof -
              have q_lt_m: "((unat yn1 * m + (unat r + unat yn1)) * 2^32 + unat un) div
                            (unat yn1 * 2^32 + unat yn0) < 2^32"
                using q_lt n_eq by (simp add: algebra_simps)
              show ?thesis
                unfolding B_def
                by (subst r_add_eq) (rule q_lt_m)
            qed
            have upper_IH: "((unat yn1 * m + unat (r + yn1)) * 2^32 + unat un) < (m + 1) * ?Y"
            proof -
              have upper_m: "((unat yn1 * m + (unat r + unat yn1)) * 2^32 + unat un) <
                            (m + 1) * (unat yn1 * 2^32 + unat yn0)"
                using N_lt_P n_eq unfolding B_def by (simp add: algebra_simps)
              show ?thesis
                unfolding B_def
                by (subst r_add_eq) (rule upper_m)
            qed
            show ?thesis
            proof -
              have ih_rule: "unat (fst (adjust_q_nat m (r + yn1) yn0 yn1 un two32)) =
                             ((unat yn1 * m + unat (r + yn1)) * 2^32 + unat un) div
                             (unat yn1 * 2^32 + unat yn0)"
              proof -
                have q_IH_32: "((unat yn1 * m + unat (r + yn1)) * 2^32 + unat un) div
                               (unat yn1 * 2^32 + unat yn0) < 2^32"
                  using q_IH unfolding B_def by simp
                have upper_IH_32: "((unat yn1 * m + unat (r + yn1)) * 2^32 + unat un) <
                                   (m + 1) * (unat yn1 * 2^32 + unat yn0)"
                  using upper_IH unfolding B_def by simp
                show ?thesis
                  using less(1)[of m "r + yn1"]
                        m_lt_n T yn0_lt un_lt r_new_lt32 yn1_ge yn1_lt m_lt q_IH_32 upper_IH_32
                  by blast
              qed
              have num_eq: "((unat yn1 * m + unat (r + yn1)) * 2^32 + unat un) =
                            ((unat yn1 * n + unat r) * B + unat un)"
                using n_eq r_add_eq by (simp add: B_def algebra_simps)
              have den_eq: "(unat yn1 * 2^32 + unat yn0) = (unat yn1 * B + unat yn0)"
                by (simp add: B_def)
              show ?thesis
                by (subst num_eq[symmetric], subst den_eq[symmetric], rule ih_rule)
            qed
          qed
          show ?thesis
          proof -
            have False_Suc: "\<not> of_nat (Suc m) * yn0 \<le> two32 * r + un"
              using prod_false n_eq by simp
            have of_nat_lt_two32: "of_nat (Suc m) < two32"
            proof -
              have Suc_lt_B: "Suc m < B"
                using n_lt_T n_eq by simp
              have unat_Suc: "unat (of_nat (Suc m) :: u64) = Suc m"
                using Suc_lt_B B_lt_len by (simp add: unat_of_nat del: of_nat_Suc)
              have unat_two32: "unat two32 = B"
                using T B_def by simp
              have "unat (of_nat (Suc m) :: u64) < unat two32"
                using Suc_lt_B unat_Suc unat_two32 by simp
              then show ?thesis
                by (simp add: word_less_nat_alt)
            qed
            have adjust_eq: "fst (adjust_q_nat (Suc m) r yn0 yn1 un two32) =
                             fst (adjust_q_nat m (r + yn1) yn0 yn1 un two32)"
              using False_Suc of_nat_lt_two32 False by simp
            have adjust_fst: "fst (adjust_q_nat n r yn0 yn1 un two32) =
                              fst (adjust_q_nat m (r + yn1) yn0 yn1 un two32)"
              using adjust_eq n_eq by simp
            have ih_goal: "unat (fst (adjust_q_nat m (r + yn1) yn0 yn1 un two32)) =
                           ((unat yn1 * n + unat r) * 2^32 + unat un) div
                           (unat yn1 * 2^32 + unat yn0)"
              using IH unfolding B_def by simp
            show ?thesis
              using adjust_fst ih_goal by simp
          qed
        qed
      qed
    next
      case False
      have n_ge_T: "?T \<le> n"
      proof -
        have unat_n: "unat (of_nat n :: u64) = n"
          using n_lt by (simp add: unat_of_nat)
        have unat_two32: "unat two32 = B"
          using T B_def by simp
        have ge: "unat two32 \<le> unat (of_nat n :: u64)"
          using False by (simp add: word_less_nat_alt not_less)
        then show ?thesis
          using unat_n unat_two32 by simp
      qed
      have N_lt_P: "?N < ?P"
      proof -
        have "?T * ?Y \<le> ?P" using n_ge_T Ypos by (simp add: mult_le_mono1)
        with q_bound_upper show ?thesis by linarith
      qed
      have n_le_T1: "n \<le> ?T + 1"
      proof -
        have A_lt_Y: "unat yn1 * n + unat r < ?Y"
        proof -
          have "(unat yn1 * n + unat r) * ?T \<le> ?N" by linarith
          then have "(unat yn1 * n + unat r) * ?T < ?T * ?Y"
            using q_bound_upper by linarith
          then show ?thesis
            using Tpos by simp
        qed
        have yn0_lt_T: "unat yn0 < ?T"
          using yn0_lt B_def by simp
        have "unat yn1 * n < unat yn1 * ?T + unat yn0"
          using A_lt_Y by linarith
        then have "unat yn1 * n < unat yn1 * ?T + ?T"
          using yn0_lt_T by linarith
        moreover have "unat yn1 * ?T + ?T \<le> unat yn1 * (?T + 2)"
        proof -
          have B_le_two_yn1: "?T \<le> 2 * unat yn1"
          proof -
            have "?T = 2 * 2^31"
              unfolding B_def by simp
            also have "... \<le> 2 * unat yn1"
              using yn1_ge by (rule mult_le_mono2)
            finally show ?thesis .
          qed
          have add_ge: "?T + unat yn1 * ?T \<le> 2 * unat yn1 + unat yn1 * ?T"
            using B_le_two_yn1 by (rule add_le_mono1)
          show ?thesis
            using add_ge by (simp add: add.commute add_mult_distrib2 mult.commute)
        qed
        ultimately have prod_less: "unat yn1 * n < unat yn1 * (?T + 2)"
          by linarith
        have yn1_pos: "0 < unat yn1"
          using yn1_ge by simp
        have prod_less_suc: "unat yn1 * n < unat yn1 * Suc (Suc ?T)"
          using prod_less by simp
        have n_less: "n < Suc (Suc ?T)"
          using prod_less_suc by (rule mult_less_cancel1[THEN iffD1, THEN conjunct2])
        then show ?thesis by simp
      qed
      show ?thesis
      proof (cases "two32 \<le> r + yn1")
        case True
          have r_new_ge: "?T \<le> unat r + unat yn1"
          proof -
            have unat_two32_B: "unat two32 = B"
              using T B_def by simp
            have unat_le: "unat two32 \<le> unat (r + yn1)"
              using True by (simp add: word_le_nat_alt)
            have add_bound: "unat r + unat yn1 < 2 ^ LENGTH(64)"
            proof -
              have r_lt_B: "unat r < B"
                using r_lt B_def by simp
              have yn1_lt_B: "unat yn1 < B"
                using yn1_lt B_def by simp
              have sum_lt: "unat r + unat yn1 < B + B"
                using r_lt_B yn1_lt_B by (rule add_less_mono)
              have len64: "LENGTH(64) = 64"
                by simp
              have Bsum_lt: "B + B < 2 ^ LENGTH(64)"
                using len64 by (simp add: B_def)
              show ?thesis
                using sum_lt Bsum_lt by (rule less_trans)
            qed
            have add_eq: "unat (r + yn1) = unat r + unat yn1"
              using add_bound by (rule unat_add_lem[THEN iffD1])
            show ?thesis
              using unat_le add_eq unat_two32_B by simp
          qed
        have m_le_T: "m \<le> ?T" using n_le_T1 n_eq by linarith
        have m_yn0_le: "m * unat yn0 \<le> ?T * unat yn0"
          using m_le_T yn0_lt by (intro mult_le_mono1) simp
        have yn0_lt_T: "unat yn0 < ?T"
          using yn0_lt B_def by simp
        have T_yn0_lt: "?T * unat yn0 < ?T * ?T"
          using yn0_lt_T Tpos by (rule mult_strict_left_mono)
        have m_yn0_lt: "m * unat yn0 < ?T * ?T"
          using m_yn0_le T_yn0_lt by linarith
        have div_eq: "?N div ?Y = m"
        proof (rule div_nat_eqI)
          show "?Y * m \<le> ?N"
          proof -
            have R_le_YQ: "(Suc m) * unat yn0 \<le> ?Y + ?Q"
            proof -
              have B_times_le: "B * B \<le> B * (unat r + unat yn1)"
                by (rule mult_le_mono2 [OF r_new_ge])
              have m_yn0_lt_Bsum: "m * unat yn0 < B * (unat r + unat yn1)"
                using m_yn0_lt B_times_le by (rule less_le_trans)
              have m_yn0_le_Bsum: "m * unat yn0 \<le> B * (unat r + unat yn1)"
                using m_yn0_lt_Bsum by (rule less_imp_le)
              have distrib: "B * (unat r + unat yn1) = B * unat r + B * unat yn1"
                by (simp add: add_mult_distrib2)
              have m_yn0_le_Bs: "m * unat yn0 \<le> B * unat r + B * unat yn1"
                using m_yn0_le_Bsum distrib by simp
              have Suc_mul: "(Suc m) * unat yn0 = m * unat yn0 + unat yn0"
                by (subst Suc_eq_plus1) (simp add: add_mult_distrib)
              have S_low: "(Suc m) * unat yn0 \<le> B * unat r + B * unat yn1 + unat yn0"
                unfolding Suc_mul
                by (rule add_le_mono1 [OF m_yn0_le_Bs])
              have rhs_eq: "B * unat r + B * unat yn1 + unat yn0 + unat un =
                            unat yn1 * B + unat yn0 + (B * unat r + unat un)"
                by (simp add: add.assoc mult.commute)
              have base_le: "B * unat r + B * unat yn1 + unat yn0 \<le>
                             B * unat r + B * unat yn1 + unat yn0 + unat un"
                by (rule Nat.le_add1)
              have S_le_base: "(Suc m) * unat yn0 \<le>
                                B * unat r + B * unat yn1 + unat yn0 + unat un"
                using S_low base_le by (rule order_trans)
              show ?thesis
                using S_le_base rhs_eq by simp
            qed
            have N_eq_goal: "?N = ?Y * m + (?Y + ?Q - (Suc m) * unat yn0)"
            proof -
              have N_Suc: "?N = ?Y * Suc m + ?Q - (Suc m) * unat yn0"
                using N_eq n_eq by simp
              have Y_mul: "?Y * Suc m = ?Y * m + ?Y"
                by (subst Suc_eq_plus1) (simp add: add_mult_distrib)
              have N_left: "?N = (?Y * m + ?Y) + ?Q - (Suc m) * unat yn0"
                using N_Suc Y_mul by simp
              have add_assoc: "(?Y * m + ?Y) + ?Q = ?Y * m + (?Y + ?Q)"
                by (simp add: add.assoc)
              have diff_assoc: "(?Y * m + (?Y + ?Q)) - (Suc m) * unat yn0 =
                                ?Y * m + (?Y + ?Q - (Suc m) * unat yn0)"
                by (rule Nat.diff_add_assoc [OF R_le_YQ])
              show ?thesis
                using N_left add_assoc diff_assoc by simp
            qed
            show ?thesis
              unfolding N_eq_goal
              by (rule Nat.le_add1)
          qed
          show "?N < ?Y * Suc m"
            using N_lt_P n_eq by simp
        qed
        then show ?thesis
        proof -
          have of_nat_ge_two32: "\<not> of_nat (Suc m) < two32"
          proof -
            have Suc_ge_B: "B \<le> Suc m"
              using n_ge_T n_eq by simp
            have unat_Suc: "unat (of_nat (Suc m) :: u64) = Suc m"
              using n_lt n_eq by (simp add: unat_of_nat del: of_nat_Suc)
            have unat_two32: "unat two32 = B"
              using T B_def by simp
            have "unat two32 \<le> unat (of_nat (Suc m) :: u64)"
              using Suc_ge_B unat_two32 unat_Suc by simp
            then show ?thesis
              by (simp add: word_less_nat_alt not_less)
          qed
          have adjust_Suc: "fst (adjust_q_nat (Suc m) r yn0 yn1 un two32) = of_nat m"
            using of_nat_ge_two32 True by simp
          have adjust_eq: "fst (adjust_q_nat n r yn0 yn1 un two32) = of_nat m"
            using adjust_Suc n_eq by simp
          have m_lt: "m < 2^64"
            using n_lt n_eq by linarith
          have unat_m: "unat (of_nat m :: u64) = m"
            using m_lt by (simp add: unat_of_nat)
          have div_eq32: "((unat yn1 * n + unat r) * 2^32 + unat un) div
                          (unat yn1 * 2^32 + unat yn0) = m"
            using div_eq unfolding B_def by simp
          show ?thesis
            using adjust_eq unat_m div_eq32 by simp
        qed
      next
        case False
        have r_new_lt: "unat (r + yn1) < ?T"
        proof -
          have word_lt: "r + yn1 < two32"
            using False by (simp add: not_le)
          have "unat (r + yn1) < unat two32"
            using word_lt by (simp add: word_less_nat_alt)
          moreover have "unat two32 = B"
            using T B_def by simp
          ultimately show ?thesis by simp
        qed
        have IH: "unat (fst (adjust_q_nat m (r + yn1) yn0 yn1 un two32)) = ?N div ?Y"
        proof -
          have m_lt_n: "m < n"
            by (simp add: n_eq)
          have r_new_lt32: "unat (r + yn1) < 2^32"
            using r_new_lt by (simp add: B_def)
          have m_lt: "m < 2^64"
            using n_lt n_eq by linarith
          have r_add_eq: "unat (r + yn1) = unat r + unat yn1"
          proof -
            have r_lt_B: "unat r < B"
              using r_lt B_def by simp
            have yn1_lt_B: "unat yn1 < B"
              using yn1_lt B_def by simp
            have sum_lt: "unat r + unat yn1 < B + B"
              using r_lt_B yn1_lt_B by (rule add_less_mono)
            have len64: "LENGTH(64) = 64"
              by simp
            have Bsum_lt: "B + B < 2 ^ LENGTH(64)"
              using len64 by (simp add: B_def)
            have add_bound: "unat r + unat yn1 < 2 ^ LENGTH(64)"
              using sum_lt Bsum_lt by (rule less_trans)
            show ?thesis
              using add_bound by (rule unat_add_lem[THEN iffD1])
          qed
          have q_IH: "((unat yn1 * m + unat (r + yn1)) * 2^32 + unat un) div ?Y < 2^32"
          proof -
            have q_lt_m: "((unat yn1 * m + (unat r + unat yn1)) * 2^32 + unat un) div
                          (unat yn1 * 2^32 + unat yn0) < 2^32"
              using q_lt n_eq by (simp add: algebra_simps)
            show ?thesis
              unfolding B_def
              by (subst r_add_eq) (rule q_lt_m)
          qed
          have upper_IH: "((unat yn1 * m + unat (r + yn1)) * 2^32 + unat un) < (m + 1) * ?Y"
          proof -
            have upper_m: "((unat yn1 * m + (unat r + unat yn1)) * 2^32 + unat un) <
                          (m + 1) * (unat yn1 * 2^32 + unat yn0)"
              using N_lt_P n_eq unfolding B_def by (simp add: algebra_simps)
            show ?thesis
              unfolding B_def
              by (subst r_add_eq) (rule upper_m)
          qed
          show ?thesis
          proof -
            have ih_rule: "unat (fst (adjust_q_nat m (r + yn1) yn0 yn1 un two32)) =
                           ((unat yn1 * m + unat (r + yn1)) * 2^32 + unat un) div
                           (unat yn1 * 2^32 + unat yn0)"
            proof -
              have q_IH_32: "((unat yn1 * m + unat (r + yn1)) * 2^32 + unat un) div
                             (unat yn1 * 2^32 + unat yn0) < 2^32"
                using q_IH unfolding B_def by simp
              have upper_IH_32: "((unat yn1 * m + unat (r + yn1)) * 2^32 + unat un) <
                                 (m + 1) * (unat yn1 * 2^32 + unat yn0)"
                using upper_IH unfolding B_def by simp
              show ?thesis
                using less(1)[of m "r + yn1"]
                      m_lt_n T yn0_lt un_lt r_new_lt32 yn1_ge yn1_lt m_lt q_IH_32 upper_IH_32
                by blast
            qed
            have num_eq: "((unat yn1 * m + unat (r + yn1)) * 2^32 + unat un) =
                          ((unat yn1 * n + unat r) * B + unat un)"
              using n_eq r_add_eq by (simp add: B_def algebra_simps)
            have den_eq: "(unat yn1 * 2^32 + unat yn0) = (unat yn1 * B + unat yn0)"
              by (simp add: B_def)
            show ?thesis
              by (subst num_eq[symmetric], subst den_eq[symmetric], rule ih_rule)
          qed
        qed
        show ?thesis
        proof -
          have of_nat_ge_two32: "\<not> of_nat (Suc m) < two32"
          proof -
            have Suc_ge_B: "B \<le> Suc m"
              using n_ge_T n_eq by simp
            have unat_Suc: "unat (of_nat (Suc m) :: u64) = Suc m"
              using n_lt n_eq by (simp add: unat_of_nat del: of_nat_Suc)
            have unat_two32: "unat two32 = B"
              using T B_def by simp
            have "unat two32 \<le> unat (of_nat (Suc m) :: u64)"
              using Suc_ge_B unat_two32 unat_Suc by simp
            then show ?thesis
              by (simp add: word_less_nat_alt not_less)
          qed
          have adjust_eq: "fst (adjust_q_nat (Suc m) r yn0 yn1 un two32) =
                           fst (adjust_q_nat m (r + yn1) yn0 yn1 un two32)"
            using of_nat_ge_two32 False by simp
          have adjust_fst: "fst (adjust_q_nat n r yn0 yn1 un two32) =
                            fst (adjust_q_nat m (r + yn1) yn0 yn1 un two32)"
            using adjust_eq n_eq by simp
          have ih_goal: "unat (fst (adjust_q_nat m (r + yn1) yn0 yn1 un two32)) =
                         ((unat yn1 * n + unat r) * 2^32 + unat un) div
                         (unat yn1 * 2^32 + unat yn0)"
            using IH unfolding B_def by simp
          show ?thesis
            using adjust_fst ih_goal by simp
        qed
      qed
    qed
  qed
qed

lemma Div64_hi_nonzero_unfold:
  fixes hi lo y :: u64
  assumes "y \<noteq> 0" and "hi \<noteq> 0" and "hi < y"
  shows "Div64 hi lo y =
    (let
      s = LeadingZeros64 y;
      y_shifted = y << s;
      two32 = 1 << 32;
      mask32 = two32 - 1;
      yn1 = y_shifted >> 32;
      yn0 = y_shifted AND mask32;
      un32 = (hi << s) OR (lo >> (64 - s));
      un10 = lo << s;
      un1 = un10 >> 32;
      un0 = un10 AND mask32;
      q1 = un32 div yn1;
      rhat = un32 - q1 * yn1;
      (q1_adj, _) = adjust_q q1 rhat yn0 yn1 un1 two32;
      un21 = un32 * two32 + un1 - q1_adj * y_shifted;
      q0 = un21 div yn1;
      rhat' = un21 - q0 * yn1;
      (q0_adj, _) = adjust_q q0 rhat' yn0 yn1 un0 two32
    in
      Some (q1_adj * two32 + q0_adj,
            (un21 * two32 + un0 - q0_adj * y_shifted) >> s))"
proof -
  have not_le: "\<not> y \<le> hi"
    using assms(3) by (simp add: linorder_not_le)
  show ?thesis
    unfolding Div64_def Let_def
    using assms(1) assms(2) not_le
    by simp
qed

definition Div64_nonzero_body :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<times> u64" where
  "Div64_nonzero_body hi lo y =
    (let
      s = LeadingZeros64 y;
      y_shifted = y << s;
      two32 = 1 << 32;
      mask32 = two32 - 1;
      yn1 = y_shifted >> 32;
      yn0 = y_shifted AND mask32;
      un32 = (hi << s) OR (lo >> (64 - s));
      un10 = lo << s;
      un1 = un10 >> 32;
      un0 = un10 AND mask32;
      q1 = un32 div yn1;
      rhat = un32 - q1 * yn1;
      (q1_adj, _) = adjust_q q1 rhat yn0 yn1 un1 two32;
      un21 = un32 * two32 + un1 - q1_adj * y_shifted;
      q0 = un21 div yn1;
      rhat' = un21 - q0 * yn1;
      (q0_adj, _) = adjust_q q0 rhat' yn0 yn1 un0 two32
    in
      (q1_adj * two32 + q0_adj,
       (un21 * two32 + un0 - q0_adj * y_shifted) >> s))"

definition Div64_nonzero_result :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<times> u64" where
  "Div64_nonzero_result hi lo y =
    (word_of_int ((uint hi * 2^64 + uint lo) div uint y),
     word_of_int ((uint hi * 2^64 + uint lo) mod uint y))"

lemma Some_case_prod:
  "Some (case p of (a, b) \<Rightarrow> f a b) = (case p of (a, b) \<Rightarrow> Some (f a b))"
  by (cases p) simp

lemma Some_case_prod_sym:
  "(case p of (a, b) \<Rightarrow> Some (f a b)) = Some (case p of (a, b) \<Rightarrow> f a b)"
  by (cases p) simp

lemma uint_hi_shift_eq:
  fixes hi y :: u64
  assumes "y \<noteq> 0" and "hi < y"
  shows "uint (hi << LeadingZeros64 y) = uint hi * 2 ^ LeadingZeros64 y"
proof -
  let ?s = "LeadingZeros64 y"
  have y_eq: "uint (y << ?s) = uint y * 2 ^ ?s"
    by (rule shift_normalize_single) (rule assms(1))
  have y_lt: "uint y * 2 ^ ?s < 2^64"
    using y_eq uint_lt_2p64[of "y << ?s"] by simp
  have hi_lt: "uint hi < uint y"
    using assms(2) by (simp add: word_less_alt)
  have prod_lt: "uint hi * 2 ^ ?s < 2^64"
  proof -
    have "uint hi * 2 ^ ?s < uint y * 2 ^ ?s"
      using hi_lt by (rule mult_strict_right_mono) simp
    with y_lt show ?thesis by linarith
  qed
  show ?thesis
    using prod_lt by (rule uint_shiftl_eq_bounded)
qed

lemma uint_un32_eq:
  fixes hi lo y :: u64
  assumes "y \<noteq> 0" and "hi < y"
  shows "uint ((hi << LeadingZeros64 y) OR (lo >> (64 - LeadingZeros64 y))) =
         (uint hi * 2^64 + uint lo) * 2 ^ LeadingZeros64 y div 2^64"
proof -
  let ?s = "LeadingZeros64 y"
  have s_lt: "?s < 64"
    using assms(1) by (rule LeadingZeros64_lt_64)
  have disjoint: "((hi << ?s) AND (lo >> (64 - ?s))) = 0"
    using s_lt by (rule un32_limbs_disjoint)
  have or_eq: "uint ((hi << ?s) OR (lo >> (64 - ?s))) =
               uint (hi << ?s) + uint (lo >> (64 - ?s))"
    by (rule uint_or_eq_add) (rule disjoint)
  have hi_eq: "uint (hi << ?s) = uint hi * 2 ^ ?s"
    using assms by (rule uint_hi_shift_eq)
  have lo_eq: "uint (lo >> (64 - ?s)) = uint lo div 2 ^ (64 - ?s)"
    by (rule word_shiftr_uint)
  have "uint hi * 2 ^ ?s + uint lo div 2 ^ (64 - ?s) =
        (uint hi * 2^64 + uint lo) * 2 ^ ?s div 2^64"
  proof -
    have hi_div: "uint hi * 2 ^ ?s = (uint hi * 2^64) * 2 ^ ?s div 2^64"
    proof -
      have "((uint hi * 2^64) * 2 ^ ?s) div 2^64 =
            ((uint hi * 2 ^ ?s) * 2^64) div 2^64"
        by (simp add: algebra_simps)
      also have "... = uint hi * 2 ^ ?s"
        by simp
      finally show ?thesis by simp
    qed
    have lo_div: "uint lo div 2 ^ (64 - ?s) = uint lo * 2 ^ ?s div 2^64"
    proof -
      have eq: "(2::int) ^ (64 - ?s) * (2::int) ^ ?s = (2::int)^64"
      proof -
        have sum: "(64 - ?s) + ?s = 64"
          using s_lt by linarith
        show ?thesis
        proof -
          have "(2::int) ^ (64 - ?s) * (2::int) ^ ?s =
                (2::int) ^ ((64 - ?s) + ?s)"
            by (simp add: power_add)
          also have "... = (2::int) ^ 64"
            using sum by simp
          finally show ?thesis .
        qed
      qed
      have "uint lo * 2 ^ ?s div 2^64 =
            uint lo * 2 ^ ?s div (2 ^ (64 - ?s) * 2 ^ ?s)"
        using eq[symmetric] by simp
      also have "... = uint lo div 2 ^ (64 - ?s)"
        by simp
      finally show ?thesis by simp
    qed
    have sum_div: "((uint hi * 2^64) * 2 ^ ?s) div 2^64 +
                   (uint lo * 2 ^ ?s) div 2^64 =
                   ((uint hi * 2^64) * 2 ^ ?s + uint lo * 2 ^ ?s) div 2^64"
      by simp
    have reorder: "((uint hi * 2^64) * 2 ^ ?s + uint lo * 2 ^ ?s) div 2^64 =
                   (uint hi * 2^64 + uint lo) * 2 ^ ?s div 2^64"
      by (simp add: algebra_simps)
    show ?thesis
      using hi_div lo_div sum_div reorder by presburger
  qed
  then show ?thesis
    using or_eq hi_eq lo_eq by simp
qed

lemma uint_ys_eq:
  fixes y :: u64
  assumes "y \<noteq> 0"
  shows "uint (y << LeadingZeros64 y) = uint y * 2 ^ LeadingZeros64 y"
  using assms by (rule shift_normalize_single)

lemma uint_yn1_eq:
  fixes y :: u64
  assumes "y \<noteq> 0"
  shows "uint ((y << LeadingZeros64 y) >> 32) =
         uint y * 2 ^ LeadingZeros64 y div 2^32"
proof -
  have ys_eq: "uint (y << LeadingZeros64 y) = uint y * 2 ^ LeadingZeros64 y"
    by (rule uint_ys_eq) (rule assms)
  show ?thesis
    using uint_shiftr32[of "y << LeadingZeros64 y"] ys_eq by simp
qed

lemma uint_yn0_eq:
  fixes y :: u64
  assumes "y \<noteq> 0"
  shows "uint ((y << LeadingZeros64 y) AND ((1 << 32) - 1)) =
         uint y * 2 ^ LeadingZeros64 y mod 2^32"
proof -
  have ys_eq: "uint (y << LeadingZeros64 y) = uint y * 2 ^ LeadingZeros64 y"
    by (rule uint_ys_eq) (rule assms)
  show ?thesis
    using uint_and_mask32[of "y << LeadingZeros64 y"] ys_eq by simp
qed

lemma uint_un1_eq:
  fixes hi lo y :: u64
  assumes "y \<noteq> 0" and "hi < y"
  shows "uint (((lo << LeadingZeros64 y) >> 32)) =
         ((uint hi * 2^64 + uint lo) * 2 ^ LeadingZeros64 y mod 2^64) div 2^32"
proof -
  let ?s = "LeadingZeros64 y"
  have XmodB: "((uint hi * 2^64 + uint lo) * 2 ^ ?s) mod 2^64 =
               (uint lo * 2 ^ ?s) mod 2^64"
  proof -
    have "((uint hi * 2^64 + uint lo) * 2 ^ ?s) =
          (uint hi * 2 ^ ?s) * 2^64 + uint lo * 2 ^ ?s"
      by (simp add: algebra_simps)
    then show ?thesis
      by simp
  qed
  have un10: "uint (lo << ?s) = (uint lo * 2 ^ ?s) mod 2^64"
    by (rule uint_shiftl_mod)
  have "uint ((lo << ?s) >> 32) = uint (lo << ?s) div 2^32"
    by (rule uint_shiftr32)
  also have "... = (uint lo * 2 ^ ?s) mod 2^64 div 2^32"
    using un10 by simp
  also have "... = ((uint hi * 2^64 + uint lo) * 2 ^ ?s mod 2^64) div 2^32"
    using XmodB[symmetric] by simp
  finally show ?thesis .
qed

lemma uint_un0_eq:
  fixes hi lo y :: u64
  assumes "y \<noteq> 0" and "hi < y"
  shows "uint ((lo << LeadingZeros64 y) AND ((1 << 32) - 1)) =
         ((uint hi * 2^64 + uint lo) * 2 ^ LeadingZeros64 y mod 2^64) mod 2^32"
proof -
  let ?s = "LeadingZeros64 y"
  have XmodB: "((uint hi * 2^64 + uint lo) * 2 ^ ?s) mod 2^64 =
               (uint lo * 2 ^ ?s) mod 2^64"
  proof -
    have "((uint hi * 2^64 + uint lo) * 2 ^ ?s) =
          (uint hi * 2 ^ ?s) * 2^64 + uint lo * 2 ^ ?s"
      by (simp add: algebra_simps)
    then show ?thesis
      by simp
  qed
  have un10: "uint (lo << ?s) = (uint lo * 2 ^ ?s) mod 2^64"
    by (rule uint_shiftl_mod)
  have "uint ((lo << ?s) AND ((1 << 32) - 1)) =
        uint (lo << ?s) mod 2^32"
    by (rule uint_and_mask32)
  also have "... = (uint lo * 2 ^ ?s) mod 2^64 mod 2^32"
    using un10 by simp
  also have "... = ((uint hi * 2^64 + uint lo) * 2 ^ ?s mod 2^64) mod 2^32"
    using XmodB[symmetric] by simp
  finally show ?thesis .
qed

lemma div_split_high:
  fixes a :: int and B :: int
  assumes "0 < B"
  shows "((a div (B * B)) * B + (a mod (B * B)) div B) = a div B"
proof -
  let ?M = "B * B"
  have decomp: "a = (a div ?M) * ?M + a mod ?M"
    by (rule div_mult_mod_eq[symmetric])
  have "a div B = ((a div ?M) * ?M + a mod ?M) div B"
    using decomp by simp
  also have "... = ((a div ?M) * B * B + a mod ?M) div B"
    by (simp add: algebra_simps)
  also have "... = ((a div ?M) * B + (a mod ?M) div B)"
    using assms by simp
  finally have eq: "a div B =
                    (a div (B * B)) * B + (a mod (B * B)) div B" .
  show ?thesis
    using eq by simp
qed

lemma div_split_high_nat:
  fixes A B :: nat
  assumes "0 < B"
  shows "A div (B * B) * B + A mod (B * B) div B = A div B"
proof -
  let ?M = "B * B"
  have decomp: "A = A div ?M * ?M + A mod ?M"
    by (rule div_mult_mod_eq[symmetric])
  have "A div B = (A div ?M * ?M + A mod ?M) div B"
    using decomp by simp
  also have "... = (A div ?M * B * B + A mod ?M) div B"
    by (simp add: algebra_simps)
  also have "... = (A div ?M * B + A mod ?M div B)"
    using assms by simp
  finally have eq: "A div B = A div (B * B) * B + A mod (B * B) div B" .
  show ?thesis
    using eq by simp
qed

lemma unat_un32_eq:
  fixes hi lo y :: u64
  assumes "y \<noteq> 0" and "hi < y"
  shows "unat ((hi << LeadingZeros64 y) OR (lo >> (64 - LeadingZeros64 y))) =
         nat ((uint hi * 2^64 + uint lo) * 2 ^ LeadingZeros64 y div 2^64)"
proof -
  show ?thesis
    unfolding unat_eq_nat_uint
    by (rule arg_cong[where f=nat, OF uint_un32_eq[OF assms]])
qed

lemma unat_un1_eq:
  fixes hi lo y :: u64
  assumes "y \<noteq> 0" and "hi < y"
  shows "unat (((lo << LeadingZeros64 y) >> 32)) =
         nat (((uint hi * 2^64 + uint lo) * 2 ^ LeadingZeros64 y mod 2^64) div 2^32)"
proof -
  show ?thesis
    unfolding unat_eq_nat_uint
    by (rule arg_cong[where f=nat, OF uint_un1_eq[OF assms]])
qed

lemma unat_yn1_eq:
  fixes y :: u64
  assumes "y \<noteq> 0"
  shows "unat ((y << LeadingZeros64 y) >> 32) =
         nat (uint y * 2 ^ LeadingZeros64 y div 2^32)"
proof -
  show ?thesis
    unfolding unat_eq_nat_uint
    by (rule arg_cong[where f=nat, OF uint_yn1_eq[OF assms]])
qed

lemma unat_yn0_eq:
  fixes y :: u64
  assumes "y \<noteq> 0"
  shows "unat ((y << LeadingZeros64 y) AND ((1 << 32) - 1)) =
         nat (uint y * 2 ^ LeadingZeros64 y mod 2^32)"
proof -
  show ?thesis
    unfolding unat_eq_nat_uint
    by (rule arg_cong[where f=nat, OF uint_yn0_eq[OF assms]])
qed

lemma unat_un0_eq:
  fixes hi lo y :: u64
  assumes "y \<noteq> 0" and "hi < y"
  shows "unat ((lo << LeadingZeros64 y) AND ((1 << 32) - 1)) =
         nat (((uint hi * 2^64 + uint lo) * 2 ^ LeadingZeros64 y mod 2^64) mod 2^32)"
proof -
  show ?thesis
    unfolding unat_eq_nat_uint
    by (rule arg_cong[where f=nat, OF uint_un0_eq[OF assms]])
qed

lemma unat_two32:
  "unat ((1 << 32) :: u64) = 2^32"
proof -
  have prod_lt: "uint (1::u64) * 2^32 < 2^64"
    by simp
  have uint_eq: "uint ((1 << 32) :: u64) = uint (1::u64) * 2^32"
    using prod_lt by (rule uint_shiftl_eq_bounded)
  have uint_one: "uint (1::u64) = 1"
    by simp
  show ?thesis
    unfolding unat_eq_nat_uint
    using uint_eq uint_one by simp
qed

lemma unat_and_mask32_lt:
  fixes w :: u64
  shows "unat (w AND ((1 << 32) - 1)) < 2^32"
proof -
  have "unat (w AND ((1 << 32) - 1)) =
        nat (uint w mod 2^32)"
    unfolding unat_eq_nat_uint
    by (rule arg_cong[where f=nat, OF uint_and_mask32[of w]])
  also have "... < 2^32"
  proof -
    have mod_nonneg: "0 <= uint w mod 2^32"
      by (rule pos_mod_sign) simp
    have mod_lt: "uint w mod 2^32 < 2^32"
      by (rule pos_mod_bound) simp
    from mod_nonneg show ?thesis
      using mod_lt by (simp add: nat_less_iff)
  qed
  finally show ?thesis .
qed

lemma unat_yn1_lt:
  fixes y :: u64
  shows "unat ((y << LeadingZeros64 y) >> 32) < 2^32"
  by (rule shift32_unat_lt)

lemma unat_yn0_lt:
  fixes y :: u64
  shows "unat ((y << LeadingZeros64 y) AND ((1 << 32) - 1)) < 2^32"
  by (rule unat_and_mask32_lt)

lemma unat_un1_lt:
  fixes lo y :: u64
  shows "unat ((lo << LeadingZeros64 y) >> 32) < 2^32"
  by (rule shift32_unat_lt)

lemma unat_un0_lt:
  fixes lo y :: u64
  shows "unat ((lo << LeadingZeros64 y) AND ((1 << 32) - 1)) < 2^32"
  by (rule unat_and_mask32_lt)

lemma unat_rhat_lt:
  fixes un32 yn1 :: u64
  assumes "yn1 \<noteq> 0"
  shows "unat (un32 - un32 div yn1 * yn1) < unat yn1"
proof -
  have eq: "un32 - un32 div yn1 * yn1 = un32 mod yn1"
    by (rule minus_div_mult_eq_mod)
  have "unat (un32 - un32 div yn1 * yn1) = unat (un32 mod yn1)"
    using eq by simp
  also have "... = unat un32 mod unat yn1"
    by (rule unat_mod_distrib)
  also have "... < unat yn1"
    using assms by (simp add: unat_gt_0)
  finally show ?thesis .
qed

lemma unat_rhat_lt_2p32:
  fixes un32 yn1 :: u64
  assumes "yn1 \<noteq> 0" and "unat yn1 < 2^32"
  shows "unat (un32 - un32 div yn1 * yn1) < 2^32"
  by (rule less_trans[OF unat_rhat_lt[OF assms(1)] assms(2)])

lemma adjust_q_digit:
  fixes u v1 v0 digit :: u64
  assumes v1_ge: "2^31 \<le> unat v1"
      and v1_lt: "unat v1 < 2^32"
      and v0_lt: "unat v0 < 2^32"
      and digit_lt: "unat digit < 2^32"
      and u_lt: "unat u < unat v1 * 2^32 + unat v0"
  shows "unat (fst (adjust_q (u div v1) (u - (u div v1) * v1) v0 v1 digit (1 << 32))) =
         (unat u * 2^32 + unat digit) div (unat v1 * 2^32 + unat v0)"
proof -
  let ?B = "(2::nat)^32"
  let ?V = "unat v1 * ?B + unat v0"
  let ?N = "unat u * ?B + unat digit"
  let ?q = "unat (u div v1)"
  let ?r = "u - (u div v1) * v1"
  have v1_pos: "0 < unat v1" using v1_ge by simp
  have v1_nz: "v1 \<noteq> 0" using v1_pos by auto
  have V_pos: "0 < ?V" using v1_pos by simp
  have r_eq: "unat ?r = unat u mod unat v1"
    by (simp add: minus_div_mult_eq_mod unat_mod_distrib)
  have q_eq: "?q = unat u div unat v1" by (rule unat_div)
  have r_lt: "unat ?r < unat v1" using v1_pos by (simp add: r_eq)
  have r_lt_B: "unat ?r < ?B" using r_lt v1_lt by linarith
  have split: "unat v1 * ?q + unat ?r = unat u"
    by (simp only: q_eq r_eq; simp add: div_mult_mod_eq mult.commute)
  have N_lt: "?N < ?B * ?V"
  proof -
    have "(unat u + 1) * ?B \<le> ?V * ?B"
      using u_lt by (intro mult_le_mono) auto
    moreover have "?N < (unat u + 1) * ?B"
      using digit_lt by (simp add: algebra_simps)
    ultimately show ?thesis by (simp add: mult.commute)
  qed
  have quot_lt: "?N div ?V < ?B"
    using N_lt V_pos by (simp add: div_less_iff_less_mult)
  have upper: "?N < (?q + 1) * ?V"
  proof -
    have u_bound: "unat u < (?q + 1) * unat v1"
      using split r_lt by (simp add: algebra_simps)
    have "(unat u + 1) * ?B \<le> ((?q + 1) * unat v1) * ?B"
      using u_bound by (intro mult_le_mono) auto
    moreover have "?N < (unat u + 1) * ?B"
      using digit_lt by (simp add: algebra_simps)
    ultimately have "?N < ((?q + 1) * unat v1) * ?B"
      by linarith
    also have "... \<le> (?q + 1) * ?V"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have q_lt: "?q < 2^64" using unsigned_less[of "u div v1", where 'a=nat] by simp
  note result = adjust_q_nat_quot[OF unat_two32 v0_lt digit_lt r_lt_B v1_ge v1_lt q_lt]
  show ?thesis
    unfolding adjust_q_def
    using result quot_lt upper by (simp add: split)
qed

lemma adjust_q_digit_remainder:
  fixes u v1 v0 digit y q :: u64
  assumes v1_ge: "2^31 \<le> unat v1"
      and v1_lt: "unat v1 < 2^32"
      and v0_lt: "unat v0 < 2^32"
      and digit_lt: "unat digit < 2^32"
      and u_lt: "unat u < unat v1 * 2^32 + unat v0"
      and y_eq: "unat y = unat v1 * 2^32 + unat v0"
  defines "q \<equiv> fst (adjust_q (u div v1) (u - (u div v1) * v1) v0 v1 digit (1 << 32))"
  shows "unat (u * (1 << 32) + digit - q * y) =
         (unat u * 2^32 + unat digit) mod unat y"
proof -
  let ?N = "unat u * 2^32 + unat digit"
  let ?Y = "unat y"
  have q_eq: "unat q = ?N div ?Y"
    unfolding q_def y_eq by (rule adjust_q_digit[OF v1_ge v1_lt v0_lt digit_lt u_lt])
  have vp: "0 < unat v1" using v1_ge by simp
  have Y_pos: "0 < ?Y" using vp by (simp add: y_eq)
  have rem_lt: "?N mod ?Y < 2^64"
    using mod_less_divisor[OF Y_pos, of ?N] unsigned_less[of y, where 'a=nat] by simp
  have word_eq: "u * (1 << 32) + digit - q * y = (of_nat (?N mod ?Y) :: u64)"
  proof -
    have N_eq: "?N = (?N div ?Y) * ?Y + ?N mod ?Y" by simp
    have cast_eq: "(of_nat ?N :: u64) = of_nat (?N div ?Y) * of_nat ?Y + of_nat (?N mod ?Y)"
      by (subst N_eq) (simp only: of_nat_add of_nat_mult)
    have T: "((1 << 32) :: u64) = of_nat ((2::nat)^32)"
      by (simp add: shiftl_def push_bit_eq_mult)
    have qword: "(of_nat (?N div ?Y) :: u64) = q"
      using arg_cong[where f="of_nat :: nat \<Rightarrow> u64", OF q_eq] by simp
    show ?thesis
      using cast_eq by (simp only: qword of_nat_add of_nat_mult of_nat_unat; simp add: T algebra_simps)
  qed
  show ?thesis using word_eq rem_lt by (simp add: unat_of_nat)
qed

lemma div_append_digit:
  fixes a b d B :: nat
  assumes "0 < d"
  shows "(a * B + b) div d = (a div d) * B + ((a mod d) * B + b) div d"
proof -
  have decomp: "a * B + b = ((a div d) * B) * d + ((a mod d) * B + b)"
    using arg_cong[where f="\<lambda>n::nat. n * B + b", OF div_mult_mod_eq[of a d]]
    by (simp only: algebra_simps)
  show ?thesis using assms by (simp add: decomp)
qed

lemma mod_append_digit:
  fixes a b d B :: nat
  shows "(a * B + b) mod d = ((a mod d) * B + b) mod d"
  by (metis mod_add_left_eq mod_mult_left_eq)

lemma Div64_digits_correct:
  fixes u v1 v0 d1 d0 y q1 r1 q0 r0 :: u64
    and X :: nat
  assumes v1_ge: "2^31 \<le> unat v1"
      and v1_lt: "unat v1 < 2^32"
      and v0_lt: "unat v0 < 2^32"
      and d1_lt: "unat d1 < 2^32"
      and d0_lt: "unat d0 < 2^32"
      and u_lt: "unat u < unat y"
      and y_eq: "unat y = unat v1 * 2^32 + unat v0"
  defines "q1 \<equiv> fst (adjust_q (u div v1) (u - (u div v1) * v1) v0 v1 d1 (1 << 32))"
      and "r1 \<equiv> u * (1 << 32) + d1 - q1 * y"
      and "q0 \<equiv> fst (adjust_q (r1 div v1) (r1 - (r1 div v1) * v1) v0 v1 d0 (1 << 32))"
      and "r0 \<equiv> r1 * (1 << 32) + d0 - q0 * y"
      and "X \<equiv> (unat u * 2^32 + unat d1) * 2^32 + unat d0"
  shows "(q1 * (1 << 32) + q0, r0) = (of_nat (X div unat y), of_nat (X mod unat y))"
proof -
  let ?Y = "unat y"
  let ?A = "unat u * 2^32 + unat d1"
  let ?C = "(?A mod ?Y) * 2^32 + unat d0"
  have Y_pos: "0 < ?Y" using u_lt by linarith
  have u_lt': "unat u < unat v1 * 2^32 + unat v0" using u_lt y_eq by simp
  have q1_eq: "unat q1 = ?A div ?Y"
    unfolding q1_def y_eq by (rule adjust_q_digit[OF v1_ge v1_lt v0_lt d1_lt u_lt'])
  have r1_eq: "unat r1 = ?A mod ?Y"
    unfolding r1_def q1_def
    by (rule adjust_q_digit_remainder[OF v1_ge v1_lt v0_lt d1_lt u_lt' y_eq])
  have r1_lt: "unat r1 < unat v1 * 2^32 + unat v0"
    by (simp only: r1_eq y_eq[symmetric]; rule mod_less_divisor[OF Y_pos])
  have q0_eq: "unat q0 = ?C div ?Y"
    unfolding q0_def
    using adjust_q_digit[OF v1_ge v1_lt v0_lt d0_lt r1_lt]
    by (simp add: r1_eq y_eq)
  have r0_eq: "unat r0 = ?C mod ?Y"
    unfolding r0_def q0_def
    using adjust_q_digit_remainder[OF v1_ge v1_lt v0_lt d0_lt r1_lt y_eq]
    by (simp add: r1_eq)
  have quotient: "X div ?Y = unat q1 * 2^32 + unat q0"
    using div_append_digit[OF Y_pos, where a="?A" and B="2^32" and b="unat d0"]
    by (simp add: X_def q1_eq q0_eq)
  have remainder: "X mod ?Y = unat r0"
    unfolding X_def r0_eq by (rule mod_append_digit)
  have T: "((1 << 32) :: u64) = of_nat ((2::nat)^32)"
    by (simp add: shiftl_def push_bit_eq_mult)
  show ?thesis
    by (simp add: quotient remainder of_nat_add of_nat_mult T)
qed

lemma unat_split32:
  fixes w :: u64
  shows "unat w = unat (w >> 32) * 2^32 + unat (w AND ((1 << 32) - 1))"
proof -
  have eq: "uint w = uint (w >> 32) * 2^32 + uint (w AND ((1 << 32) - 1))"
    by (simp add: uint_shiftr32 uint_and_mask32)
  have "int (unat w) = int (unat (w >> 32) * 2^32 + unat (w AND ((1 << 32) - 1)))"
    using eq by (simp only: of_nat_add of_nat_mult of_nat_power of_nat_numeral uint_nat[symmetric])
  then show ?thesis by (simp only: of_nat_eq_iff)
qed

lemma div64_recombine:
  fixes N :: int
  shows "((N div 2^64) * 2^32 + (N mod 2^64) div 2^32) * 2^32 +
      (N mod 2^64) mod 2^32 = N"
proof -
  have split: "(N div 2^64) * 2^32 + (N mod 2^64) div 2^32 = N div 2^32"
    using div_split_high[of "(2::int)^32" N] by simp
  show ?thesis by (simp add: split)
qed

lemma Div64_nonzero_body_correct_normalized:
  fixes hi lo y :: u64
  assumes y_nz: "y \<noteq> 0" and hi_lt: "hi < y"
      and norm_ge: "2^31 \<le> unat ((y << LeadingZeros64 y) >> 32)"
  shows "Div64_nonzero_body hi lo y = Div64_nonzero_result hi lo y"
proof -
  let ?s = "LeadingZeros64 y"
  let ?Y = "y << ?s"
  let ?v1 = "?Y >> 32"
  let ?v0 = "?Y AND ((1 << 32) - 1)"
  let ?u = "(hi << ?s) OR (lo >> (64 - ?s))"
  let ?d1 = "(lo << ?s) >> 32"
  let ?d0 = "(lo << ?s) AND ((1 << 32) - 1)"
  let ?N = "(uint hi * 2^64 + uint lo) * 2^?s"
  let ?X = "(unat ?u * 2^32 + unat ?d1) * 2^32 + unat ?d0"
  let ?q1 = "fst (adjust_q (?u div ?v1) (?u - (?u div ?v1) * ?v1) ?v0 ?v1 ?d1 (1 << 32))"
  let ?r1 = "?u * (1 << 32) + ?d1 - ?q1 * ?Y"
  let ?q0 = "fst (adjust_q (?r1 div ?v1) (?r1 - (?r1 div ?v1) * ?v1) ?v0 ?v1 ?d0 (1 << 32))"
  let ?r0 = "?r1 * (1 << 32) + ?d0 - ?q0 * ?Y"
  have Y_eq: "uint ?Y = uint y * 2^?s" by (rule uint_ys_eq[OF y_nz])
  have Yn_eq: "unat ?Y = unat y * 2^?s"
  proof -
    have "int (unat ?Y) = int (unat y * 2^?s)"
      using Y_eq by (simp only: of_nat_mult of_nat_power of_nat_numeral uint_nat[symmetric])
    then show ?thesis by (simp only: of_nat_eq_iff)
  qed
  have U_eq: "uint ?u = ?N div 2^64"
    by (rule uint_un32_eq[OF y_nz hi_lt])
  have D1_eq: "uint ?d1 = (?N mod 2^64) div 2^32"
    by (rule uint_un1_eq[OF y_nz hi_lt])
  have D0_eq: "uint ?d0 = (?N mod 2^64) mod 2^32"
    by (rule uint_un0_eq[OF y_nz hi_lt])
  have X_eq: "int ?X = ?N"
    using div64_recombine[of ?N]
    by (simp only: of_nat_add of_nat_mult of_nat_power of_nat_numeral uint_nat[symmetric] U_eq D1_eq D0_eq)
  have Xn_eq: "?X = (unat hi * 2^64 + unat lo) * 2^?s"
  proof -
    have "int ?X = int ((unat hi * 2^64 + unat lo) * 2^?s)"
      using X_eq by (simp only: of_nat_add of_nat_mult of_nat_power of_nat_numeral uint_nat[symmetric])
    then show ?thesis by (simp only: of_nat_eq_iff)
  qed
  have hi_int_lt: "uint hi < uint y" using hi_lt by (simp add: word_less_alt)
  have N_bound: "?N < uint ?Y * 2^64"
  proof -
    have lo_bound: "uint lo < 2^64" by (rule uint_lt_2p64)
    have base_bound: "uint hi * 2^64 + uint lo < uint y * 2^64"
      using hi_int_lt lo_bound by (simp_all; linarith)
    have "(uint hi * 2^64 + uint lo) * 2^?s < (uint y * 2^64) * 2^?s"
      by (rule mult_strict_right_mono[OF base_bound]) simp
    then show ?thesis by (simp add: Y_eq algebra_simps)
  qed
  have U_lt: "unat ?u < unat ?Y"
  proof -
    have "?N div 2^64 < uint ?Y"
      using N_bound by (simp add: div_less_iff_less_mult)
    then have "uint ?u < uint ?Y" by (simp add: U_eq)
    then show ?thesis by (simp only: uint_nat of_nat_less_iff)
  qed
  have digits: "(?q1 * (1 << 32) + ?q0, ?r0) =
      (of_nat (?X div unat ?Y), of_nat (?X mod unat ?Y))"
    by (rule Div64_digits_correct[OF norm_ge unat_yn1_lt unat_yn0_lt unat_un1_lt unat_un0_lt U_lt unat_split32])
  have body: "Div64_nonzero_body hi lo y = (?q1 * (1 << 32) + ?q0, ?r0 >> ?s)"
    by (simp add: Div64_nonzero_body_def Let_def case_prod_unfold)
  have q_eq: "?q1 * (1 << 32) + ?q0 = of_nat (?X div unat ?Y)"
    using digits by simp
  have r_eq: "?r0 = of_nat (?X mod unat ?Y)"
    using digits by simp
  let ?A = "unat hi * 2^64 + unat lo"
  have raw_div: "int (?A div unat y) = (uint hi * 2^64 + uint lo) div uint y"
    by (simp only: of_nat_div of_nat_add of_nat_mult of_nat_power of_nat_numeral uint_nat[symmetric])
  have raw_mod: "int (?A mod unat y) = (uint hi * 2^64 + uint lo) mod uint y"
    by (simp only: of_nat_mod of_nat_add of_nat_mult of_nat_power of_nat_numeral uint_nat[symmetric])
  have quotient: "of_nat (?X div unat ?Y) =
      (word_of_int ((uint hi * 2^64 + uint lo) div uint y) :: u64)"
    by (simp only: raw_div[symmetric] of_int_of_nat_eq Xn_eq Yn_eq; simp)
  have Y_pos: "0 < unat ?Y" using U_lt by linarith
  have rem_bound: "?X mod unat ?Y < 2^64"
    using mod_less_divisor[OF Y_pos, of ?X] unsigned_less[of ?Y, where 'a=nat] by simp
  have rem_nat: "(?X mod unat ?Y) div 2^?s = ?A mod unat y"
    by (simp only: Xn_eq Yn_eq; simp add: mod_mult_mult2)
  have original_bound: "?A mod unat y < 2^64"
    using div_le_dividend[of "?X mod unat ?Y" "2^?s"] rem_bound rem_nat by linarith
  have remainder: "(of_nat (?X mod unat ?Y) :: u64) >> ?s =
      word_of_int ((uint hi * 2^64 + uint lo) mod uint y)"
  proof (rule word_uint_eq_iff[THEN iffD2])
    have cast: "uint (of_nat (?X mod unat ?Y) :: u64) = int (?X mod unat ?Y)"
      using rem_bound by (simp only: uint_nat unat_of_nat; simp)
    have left: "uint ((of_nat (?X mod unat ?Y) :: u64) >> ?s) = int (?A mod unat y)"
      using arg_cong[where f=int, OF rem_nat]
      by (simp only: word_shiftr_uint cast of_nat_div of_nat_power of_nat_numeral)
    have rightword: "(word_of_int ((uint hi * 2^64 + uint lo) mod uint y) :: u64) = of_nat (?A mod unat y)"
      by (simp only: raw_mod[symmetric] of_int_of_nat_eq)
    have right: "uint (word_of_int ((uint hi * 2^64 + uint lo) mod uint y) :: u64) = int (?A mod unat y)"
      using original_bound unfolding rightword
      by (simp only: uint_nat unat_of_nat; simp)
    show "uint ((of_nat (?X mod unat ?Y) :: u64) >> ?s) =
          uint (word_of_int ((uint hi * 2^64 + uint lo) mod uint y) :: u64)"
      by (simp only: left right)
  qed
  show ?thesis
    by (simp only: body q_eq r_eq quotient remainder Div64_nonzero_result_def)
qed




lemma Div64_nonzero_q:
  fixes hi lo y :: u64
  assumes "y \<noteq> 0" and "hi \<noteq> 0" and "hi < y"
  shows "fst (Div64_nonzero_body hi lo y) = fst (Div64_nonzero_result hi lo y)"
  using Div64_nonzero_body_correct_normalized[OF assms(1,3) unat_yn1_ge_ax[OF assms(1)]]
  by simp

lemma Div64_nonzero_r:
  fixes hi lo y :: u64
  assumes "y \<noteq> 0" and "hi \<noteq> 0" and "hi < y"
  shows "snd (Div64_nonzero_body hi lo y) = snd (Div64_nonzero_result hi lo y)"
  using Div64_nonzero_body_correct_normalized[OF assms(1,3) unat_yn1_ge_ax[OF assms(1)]]
  by simp


lemma Div64_correct_nonzero:
  fixes hi lo y :: u64
  assumes "y \<noteq> 0" and "hi \<noteq> 0" and "hi < y"
  shows "Div64 hi lo y =
         Some (word_of_int ((uint hi * 2^64 + uint lo) div uint y),
               word_of_int ((uint hi * 2^64 + uint lo) mod uint y))"
proof -
  have "Div64 hi lo y = Some (Div64_nonzero_body hi lo y)"
    using Div64_hi_nonzero_unfold[OF assms(1) assms(2) assms(3)]
    unfolding Div64_nonzero_body_def Let_def
    by (simp add: Some_case_prod_sym)
  also have "... = Some (Div64_nonzero_result hi lo y)"
  proof -
    have "fst (Div64_nonzero_body hi lo y) = fst (Div64_nonzero_result hi lo y)"
      using assms by (rule Div64_nonzero_q)
    moreover have "snd (Div64_nonzero_body hi lo y) = snd (Div64_nonzero_result hi lo y)"
      using assms by (rule Div64_nonzero_r)
    ultimately show ?thesis by (simp add: prod_eqI)
  qed
  finally have "Div64 hi lo y = Some (Div64_nonzero_result hi lo y)" .
  then show ?thesis
    unfolding Div64_nonzero_result_def by simp
qed

lemma Div64_correct:
  fixes hi lo y :: u64
  assumes "y \<noteq> 0" and "hi < y"
  shows "Div64 hi lo y =
         Some (word_of_int ((uint hi * 2^64 + uint lo) div uint y),
               word_of_int ((uint hi * 2^64 + uint lo) mod uint y))"
proof (cases "hi = 0")
  case True
  then show ?thesis
    using assms(1) by (simp add: Div64_correct_hi_zero)
next
  case False
  then show ?thesis
    using assms False Div64_correct_nonzero by metis
qed


end
