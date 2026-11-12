theory Div
  imports Exp
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
              proof (rule Divides.mod_less)
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
              proof (rule Divides.mod_less)
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

axiomatization where
  Div64_nonzero_q:
    "\<And>hi lo y.
      y \<noteq> 0 \<Longrightarrow> hi \<noteq> 0 \<Longrightarrow> hi < y \<Longrightarrow>
      fst (Div64_nonzero_body hi lo y) = fst (Div64_nonzero_result hi lo y)"
  and
  Div64_nonzero_r:
    "\<And>hi lo y.
      y \<noteq> 0 \<Longrightarrow> hi \<noteq> 0 \<Longrightarrow> hi < y \<Longrightarrow>
      snd (Div64_nonzero_body hi lo y) = snd (Div64_nonzero_result hi lo y)"

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

section \<open>Top-level uint256 DIV/MOD correctness\<close>

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

axiomatization where
  uint256_lt_iff_limb_lt:
    "\<And>x y. x <\<^sub>u y \<longleftrightarrow>
      uint (z3 x) < uint (z3 y) \<or>
      uint (z3 x) = uint (z3 y) \<and> uint (z2 x) < uint (z2 y) \<or>
      uint (z3 x) = uint (z3 y) \<and> uint (z2 x) = uint (z2 y) \<and> uint (z1 x) < uint (z1 y) \<or>
      uint (z3 x) = uint (z3 y) \<and> uint (z2 x) = uint (z2 y) \<and> uint (z1 x) = uint (z1 y) \<and> uint (z0 x) < uint (z0 y)"
  and
  dnStorage_scale:
    "\<And>x s. x \<noteq> uint256_zero \<Longrightarrow>
       s = LeadingZeros64 (getword x (dLen x - 1)) \<Longrightarrow>
       uint256_to_int (dnStorage x (dLen x) s) = uint256_to_int x * 2 ^ s"
  and
  normalize_u_scale:
    "\<And>x s. s < 64 \<Longrightarrow>
       uint256_u4_to_int (normalize_u x (dLen x) s) = uint256_to_int x * 2 ^ s"
  and
  udivremBy1_correct:
    "\<And>un ulen dn u4. dn \<noteq> 0 \<Longrightarrow>
       uint256_to_int (fst (udivremBy1 uint256_zero un ulen dn u4)) =
         uint256_u4_to_int (un, u4) div uint dn \<and>
       uint (snd (udivremBy1 uint256_zero un ulen dn u4)) =
         uint256_u4_to_int (un, u4) mod uint dn"
  and
  udivremKnuth_branch_correct:
    "\<And>u d shift dn un u4 rem q un' u4' r.
       d \<noteq> uint256_zero \<Longrightarrow> 1 < dLen d \<Longrightarrow>
       shift = LeadingZeros64 (getword d (dLen d - 1)) \<Longrightarrow>
       dn = dnStorage d (dLen d) shift \<Longrightarrow>
       (un, u4) = normalize_u u (dLen u) shift \<Longrightarrow>
       rem = uint256_zero \<Longrightarrow>
       udivremKnuth uint256_zero un u4 dn (dLen u) = (q, un', u4') \<Longrightarrow>
       r = rem_loop rem un' u4' (dLen d - 1) (dLen d - 1) shift \<Longrightarrow>
       uint256_to_int q = uint256_to_int u div uint256_to_int d \<and>
       uint256_to_int r = uint256_to_int u mod uint256_to_int d"

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

axiomatization where
  unat_yn1_ge_ax:
    "\<And>y. y \<noteq> 0 \<Longrightarrow> 2^31 \<le> unat ((y << LeadingZeros64 y) >> 32)"

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
  proof -
    have lower: "2 ^ (64 * (dLen d - 1)) \<le> uint256_to_int d"
      using d_len_pos by (rule uint256_to_int_dLen_lower)
    have "2 ^ (64 * (dLen d - 1)) = (1::int)"
      using d1 by simp
    then have "1 \<le> uint256_to_int d"
      using lower by simp
    then show ?thesis by linarith
  qed
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
  have udiv: "uint256_to_int (fst (udivremBy1 uint256_zero un (dLen u) (getword dn 0) u4)) =
              uint256_u4_to_int (un, u4) div uint (getword dn 0) \<and>
              uint (snd (udivremBy1 uint256_zero un (dLen u) (getword dn 0) u4)) =
              uint256_u4_to_int (un, u4) mod uint (getword dn 0)"
    using dn_nonzero by (rule udivremBy1_correct)
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

  have q: "uint256_to_int (x div\<^sub>u y) = uint256_to_int x div uint256_to_int y"
  proof -
    have div_body: "x div\<^sub>u y = \<lparr>z0 = z0 x div z0 y, z1 = 0, z2 = 0, z3 = 0\<rparr>"
      using assms unfolding uint256_div_def by simp
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
      by (rule udivremKnuth_branch_correct[OF assms d_gt1 shift_def dn_def norm rem_def knuth r_def])
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
  proof -
    have "x div\<^sub>u y = (case udivrem uint256_zero x y of (quot, rem) \<Rightarrow> quot)"
      unfolding uint256_div_def
      using assms by simp
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


end
