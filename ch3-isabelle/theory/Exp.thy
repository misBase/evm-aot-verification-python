theory Exp
  imports uint256 "HOL-Library.Word"
begin

fun u256_sq :: "u256 \<Rightarrow> u256" where
  "u256_sq x = x * x"

fun u256_pow_aux :: "u256 \<Rightarrow> u256 \<Rightarrow> u64 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> u256 \<times> u256 \<times> nat" where
  "u256_pow_aux res mult word 0 curBit = (res, mult, curBit)" |
  "u256_pow_aux res mult word bits_to_process 0 = (res, mult, 0)" |
  "u256_pow_aux res mult word (Suc bits_to_process) (Suc curBit) = (
    let new_res = (if (word AND 1 = 1) then res * mult else res);
        new_mult = u256_sq mult;
        new_word = word >> 1
    in u256_pow_aux new_res new_mult new_word bits_to_process curBit)"

definition u256_pow :: "u256 \<Rightarrow> u256 \<Rightarrow> u256" (infix "pow\<^sub>2\<^sub>5\<^sub>6" 50) where
  "base pow\<^sub>2\<^sub>5\<^sub>6 exponent = (let
    res = 1; mult = base;
    expBitLen = BitLen (word256_to_uint256 exponent);
    even = (base AND 1 = 0)
  in if even \<and> expBitLen > 8 then 0
     else let w = word256_to_uint256 exponent;
              (r1,m1,c1) = u256_pow_aux res mult (z0 w) 64 expBitLen;
              (r2,m2,c2) = u256_pow_aux r1 m1 (z1 w) 64 c1;
              (r3,m3,c3) = u256_pow_aux r2 m2 (z2 w) 64 c2;
              (r4,_,_)  = u256_pow_aux r3 m3 (z3 w) 64 c3
          in r4)"

fun u64_nat_lower :: "u64 \<Rightarrow> nat \<Rightarrow> nat" where
  "u64_nat_lower w 0 = 0" |
  "u64_nat_lower w (Suc n) = unat (w AND 1) + 2 * u64_nat_lower (w >> 1) n"


section \<open>Axioms -- all intermediate lemmas assumed\<close>

lemma unat_256: "unat (1 << 8 :: u64) = 256"
  by code_simp




lemma mult_sq_pow: "((mult :: u256) * mult) ^ m = mult ^ (2 * m)"
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have "(mult * mult) ^ Suc m = (mult * mult) * (mult * mult) ^ m"
    by simp
  also have "... = (mult * mult) * mult ^ (2 * m)"
    using Suc by simp
  also have "... = mult * (mult * mult ^ (2 * m))"
    by (simp add: mult.assoc)
  also have "... = mult * mult ^ Suc (2 * m)"
    by simp
  also have "... = mult ^ Suc (Suc (2 * m))"
    by simp
  also have "... = mult ^ (2 * Suc m)"
    by simp
  finally show ?case .
qed

lemma mult_sq_pow_2n: "((mult :: u256) * mult) ^ (2 ^ n) = mult ^ (2 ^ Suc n)"
  by (simp add: mult_sq_pow mult_2)

lemma fst_combine: "(res :: u256) * (mult :: u256) ^ a * (mult * mult) ^ b = res * mult ^ (a + 2 * b)"
proof -
  have "res * mult ^ a * (mult * mult) ^ b = res * (mult ^ a * mult ^ (2 * b))"
    by (simp add: mult_sq_pow)
  also have "... = res * mult ^ (a + 2 * b)"
    by (simp add: power_add)
  finally show ?thesis .
qed


lemma word_and_1_cases:
  "(w :: u64) AND 1 = 0 \<or> (w :: u64) AND 1 = 1"
proof (cases "bit w 0")
  case True
  have "w AND 1 = 1"
  proof (rule bit_eqI)  
    fix n
    show "bit (w AND 1) n = bit (1 :: u64) n"
      using True by (cases n) (auto simp: bit_simps)
  qed
  then show ?thesis by simp
next
  case False
  have "w AND 1 = 0"
  proof (rule bit_eqI)
    fix n
    show "bit (w AND 1) n = bit (0 :: u64) n"
      using False by (cases n) (auto simp: bit_simps)
  qed
  then show ?thesis by simp
qed

lemma u256_pow_aux_step_general:
  "u256_pow_aux res mult (w :: u64) (Suc n) (Suc cur) =
   u256_pow_aux (res * mult ^ unat (w AND 1)) (u256_sq mult) (w >> 1) n cur"
proof -
  show ?thesis
  proof (cases "w AND 1 = 1")
    case True
    then show ?thesis
      unfolding u256_pow_aux.simps
      by (simp add: True)
  next
    case False
    then have zero: "w AND 1 = 0"
      using word_and_1_cases[of w] by blast
    then show ?thesis
      unfolding u256_pow_aux.simps
      by (simp add: False zero)
  qed
qed

lemma u256_pow_aux_invariant_enough:
  assumes "n \<le> k"
  shows "fst (u256_pow_aux res mult (w :: u64) n k) = res * mult ^ u64_nat_lower w n"
    and "fst (snd (u256_pow_aux res mult (w :: u64) n k)) = mult ^ (2 ^ n)"
    and "snd (snd (u256_pow_aux res mult (w :: u64) n k)) = k - n"
proof -
  have "u256_pow_aux res mult (w :: u64) n k =
        (res * mult ^ u64_nat_lower w n, mult ^ (2 ^ n), k - n)"
    using assms
  proof (induction n arbitrary: res mult w k)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    from Suc.prems obtain k' where k_eq: "k = Suc k'" and "n \<le> k'"
      using Suc_le_D by fastforce
    show ?case
    proof -
      have "u256_pow_aux res mult w (Suc n) k =
            u256_pow_aux res mult w (Suc n) (Suc k')"
        by (simp add: k_eq)
      also have "... = u256_pow_aux (res * mult ^ unat (w AND 1)) (u256_sq mult) (w >> 1) n k'"
        by (rule u256_pow_aux_step_general)
      also have "... = u256_pow_aux (res * mult ^ unat (w AND 1)) (mult * mult) (w >> 1) n k'"
        by simp
      also have "... = ((res * mult ^ unat (w AND 1)) * (mult * mult) ^ u64_nat_lower (w >> 1) n,
                         (mult * mult) ^ (2 ^ n), k' - n)"
        using Suc.IH[OF \<open>n \<le> k'\<close>, of "res * mult ^ unat (w AND 1)" "mult * mult" "w >> 1"]
        by simp
      also have "... = (res * mult ^ u64_nat_lower w (Suc n), mult ^ (2 ^ Suc n), k - Suc n)"
        using k_eq fst_combine[where a="unat (w AND 1)" and b="u64_nat_lower (w >> 1) n"]
              mult_sq_pow_2n
        by simp
      finally show ?thesis .
    qed
  qed
  then show
    "fst (u256_pow_aux res mult (w :: u64) n k) = res * mult ^ u64_nat_lower w n"
    "fst (snd (u256_pow_aux res mult (w :: u64) n k)) = mult ^ (2 ^ n)"
    "snd (snd (u256_pow_aux res mult (w :: u64) n k)) = k - n"
    by auto
qed       

lemma u256_pow_aux_invariant_short:
  assumes "k < n"
  shows "fst (u256_pow_aux res mult (w :: u64) n k) = res * mult ^ u64_nat_lower w k"
    and "fst (snd (u256_pow_aux res mult (w :: u64) n k)) = mult ^ (2 ^ k)"
    and "snd (snd (u256_pow_aux res mult (w :: u64) n k)) = 0"
proof -
  have "u256_pow_aux res mult (w :: u64) n k =
        (res * mult ^ u64_nat_lower w k, mult ^ (2 ^ k), 0)"
    using assms
  proof (induction k arbitrary: res mult w n)
    case 0
    show ?case
      using assms
    proof (cases n)
      case 0
      with assms show ?thesis by simp
    next
      case (Suc n')
      then show ?thesis by simp
    qed
  next
    case (Suc k)
    from Suc.prems obtain n' where n_eq: "n = Suc n'" and "k < n'"
      using Suc_lessE by blast
    show ?case
    proof -
      have "u256_pow_aux res mult w n (Suc k) =
            u256_pow_aux res mult w (Suc n') (Suc k)"
        by (simp add: n_eq)
      also have "... = u256_pow_aux (res * mult ^ unat (w AND 1)) (u256_sq mult) (w >> 1) n' k"
        by (rule u256_pow_aux_step_general)
      also have "... = u256_pow_aux (res * mult ^ unat (w AND 1)) (mult * mult) (w >> 1) n' k"
        by simp
      also have "... = ((res * mult ^ unat (w AND 1)) * (mult * mult) ^ u64_nat_lower (w >> 1) k,
                         (mult * mult) ^ (2 ^ k), 0)"
        using Suc.IH[OF \<open>k < n'\<close>, of "res * mult ^ unat (w AND 1)" "mult * mult" "w >> 1"]
        by simp
      also have "... = (res * mult ^ u64_nat_lower w (Suc k), mult ^ (2 ^ Suc k), 0)"
        using fst_combine[where a="unat (w AND 1)" and b="u64_nat_lower (w >> 1) k"]
              mult_sq_pow_2n
        by simp
      finally show ?thesis .
    qed
  qed
  then show
    "fst (u256_pow_aux res mult (w :: u64) n k) = res * mult ^ u64_nat_lower w k"
    "fst (snd (u256_pow_aux res mult (w :: u64) n k)) = mult ^ (2 ^ k)"
    "snd (snd (u256_pow_aux res mult (w :: u64) n k)) = 0"
    by auto
qed

corollary u256_pow_aux_invariant:
  "u256_pow_aux res mult (w :: u64) n n =
   (res * mult ^ u64_nat_lower w n, mult ^ (2 ^ n), 0)"
  using u256_pow_aux_invariant_enough[OF le_refl, of res mult w n]
  by (cases "u256_pow_aux res mult w n n"; simp)

lemmas inv_enough_fst = u256_pow_aux_invariant_enough(1)
lemmas inv_enough_snd = u256_pow_aux_invariant_enough(2)
lemmas inv_enough_cur = u256_pow_aux_invariant_enough(3)
lemmas inv_short_fst = u256_pow_aux_invariant_short(1)
lemmas inv_short_snd = u256_pow_aux_invariant_short(2)
lemmas inv_short_cur = u256_pow_aux_invariant_short(3)

lemma unat_word_of_int_bounded:
  fixes k :: int
  assumes "0 \<le> k" and "k < 2^256"
  shows "unat (word_of_int k :: u256) = nat k"
  using assms
  by (simp add: unat_eq_nat_uint uint_word_of_int)

lemma int_shiftl_eq_mult: "((a :: int) << n) = a * 2 ^ n"
  by (simp add: shiftl_def push_bit_eq_mult)

lemma unat_uint256_decomp:
  "unat (uint256_to_word256 y) = 
   unat (z0 y) + 2^64 * unat (z1 y) + 2^128 * unat (z2 y) + 2^192 * unat (z3 y)"
proof (cases y)
  case (fields a b c d)
  have bounds: "uint a < 2^64" "uint b < 2^64" "uint c < 2^64" "uint d < 2^64"
    using uint_lt2p[where 'a=64] by (simp_all add: word_size)
  have sum_bound: "uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192 < (2::int)^256"
  proof -
    have max_sum: "uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192
        \<le> (2^64 - 1) + (2^64 - 1) * 2^64 + (2^64 - 1) * 2^128 + (2^64 - 1) * 2^192"
      using bounds by (intro add_mono mult_right_mono) auto
    also have "... = (2^64 - 1) * (1 + 2^64 + 2^128 + 2^192)"
      by (simp add: algebra_simps)
    also have "... = 2^256 - 1"
      by (simp add: algebra_simps power_add eval_nat_numeral)
    also have "... < 2^256" by simp
    finally show ?thesis .
  qed
  define k where "k = uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192"
  have k_pos: "0 \<le> k"
    unfolding k_def
    by (intro add_nonneg_nonneg mult_nonneg_nonneg; simp)
  have k_bound: "k < 2^256"
    using sum_bound unfolding k_def by simp
  have "uint256_to_word256 (\<lparr>z0=a,z1=b,z2=c,z3=d\<rparr>) = word_of_int k"
    unfolding k_def
    by (simp add: uint256_to_word256_def uint256_to_int_def Let_def int_shiftl_eq_mult)
  then have lhs: "unat (uint256_to_word256 (\<lparr>z0=a,z1=b,z2=c,z3=d\<rparr>)) = nat k"
    using k_pos k_bound by (simp add: unat_word_of_int_bounded)
  have "nat k = nat (uint a) + nat (uint b * 2^64) + nat (uint c * 2^128) + nat (uint d * 2^192)"
    unfolding k_def by (simp add: nat_add_distrib)
  also have "... = nat (uint a) + nat (uint b) * 2^64 + nat (uint c) * 2^128 + nat (uint d) * 2^192"
    by (simp add: nat_mult_distrib)
  also have "... = unat a + 2^64 * unat b + 2^128 * unat c + 2^192 * unat d"
    by simp
  finally have rhs: "nat k = unat a + 2^64 * unat b + 2^128 * unat c + 2^192 * unat d" .
  show ?thesis
    unfolding fields
    by (simp add: lhs rhs)
qed


lemma u64_shift_ge_64: "64 \<le> n \<Longrightarrow> (w :: u64) >> n = 0"
  unfolding shiftr_def
  by (simp add: bit_eq_iff bit_simps)

lemma len8tab_shift_8_all: "\<forall>(w :: 8 word). w >> len8tab w = 0"
  by code_simp

lemma len8tab_shift_8: "((w :: 8 word) >> len8tab w) = 0"
  using len8tab_shift_8_all by blast

lemma uint_lt_2p64: "uint (w :: u64) < 2^64"
  using uint_lt2p[where 'a=64, of w] by simp

lemma unat_lt_2p64: "unat (w :: u64) < 2^64"
  using unsigned_less[where 'a = nat, of w] by simp

lemma shift32_unat_lt:           
  fixes w :: u64
  shows "unat (w >> 32) < 2^32"
proof -
  have "unat (w >> 32) = unat w div 2^32"
    by (metis drop_bit_eq_div shiftr_def unat_drop_bit_eq)
  also have "... < 2^32"
    using unat_lt_2p64[of w]
    by (simp add: power_add)
  finally show ?thesis .
qed

lemma shift16_of_lt32_unat:
  fixes w :: u64
  assumes "unat w < 2^32"
  shows "unat (w >> 16) < 2^16"
proof -
  have "unat (w >> 16) = unat w div 2^16"
    by (metis drop_bit_eq_div shiftr_def unat_drop_bit_eq)
  with assms show ?thesis
    by (simp add: power_add)
qed

lemma shift8_of_lt16_unat:
  fixes w :: u64
  assumes "unat w < 2^16"
  shows "unat (w >> 8) < 2^8"
proof -
  have "unat (w >> 8) = unat w div 2^8"
    by (metis drop_bit_eq_div shiftr_def unat_drop_bit_eq)
  with assms show ?thesis
    by (simp add: power_add)
qed



lemma pow8: "(1 << 8 :: u64) = 256" by code_simp
lemma pow16: "(1 << 16 :: u64) = 2^16" by code_simp
lemma pow32: "(1 << 32 :: u64) = 2^32" by code_simp


lemma lt_shift16_imp_unat_lt_2p16:
  fixes w :: u64
  assumes "w < (1 << 16)"
  shows "unat w < 2^16"
  using assms by (simp add: pow16 word_less_nat_alt)

lemma lt_shift32_imp_unat_lt_2p32:
  fixes w :: u64
  assumes "w < (1 << 32)"
  shows "unat w < 2^32"
  using assms by (simp add: pow32 word_less_nat_alt)

lemma lt_shift8_imp_unat_lt_256:
  fixes w :: u64
  assumes "w < (1 << 8)"
  shows "unat w < 256"
  using assms by (simp add: pow8 word_less_nat_alt)

lemma shift32_word_lt: "(w :: u64) >> 32 < 2^32"
  using shift32_unat_lt by (auto simp: pow32 word_less_nat_alt)

lemma shift16_of_lt32_word: "(w :: u64) < 2^32 \<Longrightarrow> w >> 16 < 2^16"
  using shift16_of_lt32_unat by (auto simp: pow32 pow16 word_less_nat_alt)

lemma shift8_of_lt16_word: "(w :: u64) < 2^16 \<Longrightarrow> w >> 8 < 256"
  using shift8_of_lt16_unat by (auto simp: pow16 pow8 word_less_nat_alt)


lemma x3_lt_256:
  fixes x :: u64
  shows "unat (let x1 = (if (1 << 32) \<le> x then x >> 32 else x);
                 x2 = (if (1 << 16) \<le> x1 then x1 >> 16 else x1)
             in if (1 << 8) \<le> x2 then x2 >> 8 else x2) < 256"
proof -
  define x1 where "x1 = (if (1 << 32) \<le> x then x >> 32 else x)"
  define x2 where "x2 = (if (1 << 16) \<le> x1 then x1 >> 16 else x1)"
  define x3 where "x3 = (if (1 << 8)  \<le> x2 then x2 >> 8  else x2)"
  have "unat x3 < 256"
  proof (cases "(1 << 32) \<le> x")
    case True
    hence x1_eq: "x1 = x >> 32" unfolding x1_def by simp
    show ?thesis
    proof (cases "(1 << 16) \<le> x1")
      case True
      hence x2_eq: "x2 = x1 >> 16" unfolding x2_def x1_eq by simp
      show ?thesis
      proof (cases "(1 << 8) \<le> x2")
        case True
        hence x3_eq: "x3 = x2 >> 8" unfolding x3_def by simp
        have a: "unat x1 < 2^32"
          using x1_eq shift32_unat_lt by presburger
        have b: "unat x2 < 2^16"
          using a x2_eq shift16_of_lt32_unat by presburger
        have c: "unat (x2 >> 8) < 256"
          using b shift8_of_lt16_unat by simp
        show ?thesis unfolding x3_eq by (rule c)
      next
        case False
        hence x3_eq: "x3 = x2" unfolding x3_def by simp
        from False have "x2 < (1 << 8)" by (simp add: not_le)
        with lt_shift8_imp_unat_lt_256 show ?thesis unfolding x3_eq by simp
      qed
    next
      case False
      hence x2_eq: "x2 = x1" unfolding x2_def x1_eq by simp
      from False have x1_bound: "unat x1 < 2^16"
        by (metis lt_shift16_imp_unat_lt_2p16 not_le)
      show ?thesis
      proof (cases "(1 << 8) \<le> x2")
        case True
        hence x3_eq: "x3 = x2 >> 8" unfolding x3_def by simp
        have c: "unat (x2 >> 8) < 256"
          using x1_bound x2_eq shift8_of_lt16_unat by simp
        show ?thesis unfolding x3_eq by (rule c)
      next
        case False
        hence x3_eq: "x3 = x2" unfolding x3_def by simp
        from False have "x2 < (1 << 8)" by (simp add: not_le)
        with lt_shift8_imp_unat_lt_256 show ?thesis unfolding x3_eq by simp
      qed
    qed
  next
    case False
    hence x1_eq: "x1 = x" unfolding x1_def by simp
    from False have x_bound: "unat x < 2^32"
      by (metis lt_shift32_imp_unat_lt_2p32 not_le)
    show ?thesis
    proof (cases "(1 << 16) \<le> x1")
      case True
      hence x2_eq: "x2 = x1 >> 16" unfolding x2_def x1_eq by simp
      have a: "unat x1 < 2^32" using x1_eq x_bound by simp
      have b: "unat x2 < 2^16" using a x2_eq shift16_of_lt32_unat by presburger
      show ?thesis
      proof (cases "(1 << 8) \<le> x2")
        case True
        hence x3_eq: "x3 = x2 >> 8" unfolding x3_def by simp
        have c: "unat (x2 >> 8) < 256"
          using b shift8_of_lt16_unat by simp
        show ?thesis unfolding x3_eq by (rule c)
      next
        case False
        hence x3_eq: "x3 = x2" unfolding x3_def by simp
        from False have "x2 < (1 << 8)" by (simp add: not_le)
        with lt_shift8_imp_unat_lt_256 show ?thesis unfolding x3_eq by simp
      qed
    next
      case False
      hence x2_eq: "x2 = x1" unfolding x2_def x1_eq by simp
      from False have x1_bound: "unat x1 < 2^16"
        by (metis lt_shift16_imp_unat_lt_2p16 not_le)
      show ?thesis
      proof (cases "(1 << 8) \<le> x2")
        case True
        hence x3_eq: "x3 = x2 >> 8" unfolding x3_def by simp
        have c: "unat (x2 >> 8) < 256"
          using x1_bound x2_eq shift8_of_lt16_unat by simp
        show ?thesis unfolding x3_eq by (rule c)
      next
        case False
        hence x3_eq: "x3 = x2" unfolding x3_def by simp
        from False have "x2 < (1 << 8)" by (simp add: not_le)
        with lt_shift8_imp_unat_lt_256 show ?thesis unfolding x3_eq by simp
      qed
    qed
  qed
  then show ?thesis unfolding x3_def x2_def x1_def Let_def .
qed

lemma uint_ucast_u64_to_u8:
  fixes w :: u64
  shows "uint (ucast w :: 8 word) = uint w mod 256"
  apply transfer
  by (simp add: take_bit_eq_mod)

lemma unat_ucast_u64_to_u8:
  fixes x :: u64
  assumes "unat x < 256"
  shows "unat (ucast x :: 8 word) = unat x"
proof -
  have uint_x: "uint x < 256"
  proof -
    have "nat (uint x) = unat x"
      by (metis unat_eq_nat_uint)
    with assms show ?thesis by arith
  qed
  have "uint (ucast x :: 8 word) = uint x"
    using uint_ucast_u64_to_u8[of x] uint_x by simp
  then show ?thesis
    by (metis unat_eq_nat_uint)
qed

lemma Len64_decomp:
  "\<exists>k x3. (x :: u64) >> k = x3 \<and> unat x3 < 256 \<and> Len64 x = k + len8tab (ucast x3)"
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

  show ?thesis using shift bound len_eq by blast
qed

lemma u64_shift_len8tab_eq_zero:
  fixes x :: u64
  assumes "unat x < 256"
  shows "x >> len8tab (ucast x) = 0"
proof -
  have "unat (x >> len8tab (ucast x)) = unat x div 2 ^ len8tab (ucast x)"
  proof -
    have "unat (x >> len8tab (ucast x)) = unat (drop_bit (len8tab (ucast x)) x)"
      by (simp add: shiftr_def)
    also have "\<dots> = drop_bit (len8tab (ucast x)) (unat x)"
      by (rule unat_drop_bit_eq)
    also have "\<dots> = unat x div 2 ^ len8tab (ucast x)"
      by (simp add: drop_bit_eq_div)
    finally show ?thesis .
  qed
  also have "\<dots> = 0"
  proof -
    have u8: "unat ((ucast x :: 8 word) >> len8tab (ucast x)) = 0"
      using len8tab_shift_8[of "ucast x"] by simp
    have u8_div: "unat ((ucast x :: 8 word) >> len8tab (ucast x)) = 
                  unat (ucast x :: 8 word) div 2 ^ len8tab (ucast x)"
    proof -
      have "unat ((ucast x :: 8 word) >> len8tab (ucast x)) = 
            unat (drop_bit (len8tab (ucast x)) (ucast x :: 8 word))"
        by (simp add: shiftr_def)
      also have "\<dots> = drop_bit (len8tab (ucast x)) (unat (ucast x :: 8 word))"
        by (rule unat_drop_bit_eq)
      also have "\<dots> = unat (ucast x :: 8 word) div 2 ^ len8tab (ucast x)"
        by (simp add: drop_bit_eq_div)
      finally show ?thesis .
    qed
    from u8 u8_div have "unat (ucast x :: 8 word) div 2 ^ len8tab (ucast x) = 0"
      by simp
    then show ?thesis
      using unat_ucast_u64_to_u8[OF assms] by simp
  qed
  finally show ?thesis
    by (metis unat_eq_zero)
qed
      
lemma Len64_shift_zero: "(x :: u64) >> Len64 x = 0"
proof -
  obtain k x3 where sh: "x >> k = x3" and bound: "unat x3 < 256"
                and len_eq: "Len64 x = k + len8tab (ucast x3)"
    using Len64_decomp by blast
  have "x >> Len64 x = x >> (k + len8tab (ucast x3))"
    unfolding len_eq ..
  also have "... = x >> k >> len8tab (ucast x3)"
    by (simp add: shiftr_def  add.commute)
  also have "... = x3 >> len8tab (ucast x3)"
    unfolding sh ..
  also have "... = 0"
    by (rule u64_shift_len8tab_eq_zero) (rule bound)
  finally show ?thesis .
qed

lemma bitlen_z0_shift: "BitLen y < 64 \<Longrightarrow> z0 y >> BitLen y = 0"
  unfolding BitLen_def
  using Len64_shift_zero[of "z0 y"]
  by (auto split: if_splits)

lemma zero_shiftr_eq [simp]: "(0 :: u64) >> n = 0"
  by (simp add: shiftr_def)

lemma bitlen_z1_shift: "\<lbrakk>64 \<le> BitLen y; BitLen y < 128\<rbrakk> \<Longrightarrow> z1 y >> (BitLen y - 64) = 0"
proof -
  assume A: "64 \<le> BitLen y" "BitLen y < 128"
  have z3: "z3 y = 0" using A unfolding BitLen_def by (auto split: if_splits)
  have z2: "z2 y = 0" using A z3 unfolding BitLen_def by (auto split: if_splits)
  show ?thesis
  proof (cases "z1 y = 0")
    case True
    thus ?thesis by simp
  next
    case False
    with z3 z2 have "BitLen y = 64 + Len64 (z1 y)"
      unfolding BitLen_def by simp
    hence "BitLen y - 64 = Len64 (z1 y)" by simp
    thus ?thesis using Len64_shift_zero[of "z1 y"] by simp
  qed
qed

lemma bitlen_z2_shift: "\<lbrakk>128 \<le> BitLen y; BitLen y < 192\<rbrakk> \<Longrightarrow> z2 y >> (BitLen y - 128) = 0"
proof -
  assume A: "128 \<le> BitLen y" "BitLen y < 192"
  have z3: "z3 y = 0" using A unfolding BitLen_def by (auto split: if_splits)
  show ?thesis
  proof (cases "z2 y = 0")
    case True
    thus ?thesis by simp
  next
    case False
    with z3 have "BitLen y = 128 + Len64 (z2 y)"
      unfolding BitLen_def by simp
    hence "BitLen y - 128 = Len64 (z2 y)" by simp
    thus ?thesis using Len64_shift_zero[of "z2 y"] by simp
  qed
qed

lemma bitlen_z3_shift: "\<lbrakk>192 \<le> BitLen y; BitLen y < 256\<rbrakk> \<Longrightarrow> z3 y >> (BitLen y - 192) = 0"
proof -
  assume A: "192 \<le> BitLen y" "BitLen y < 256"
  show ?thesis
  proof (cases "z3 y = 0")
    case True
    thus ?thesis by simp
  next
    case False
    with A have "BitLen y = 192 + Len64 (z3 y)"
      unfolding BitLen_def by simp
    hence "BitLen y - 192 = Len64 (z3 y)" by simp
    thus ?thesis using Len64_shift_zero[of "z3 y"] by simp
  qed
qed


lemma uint_decomp_256:
  fixes k :: int
  assumes "0 <= k" and "k < 2^256"
  shows "(k mod 2^64) + ((k >> 64) mod 2^64) * 2^64 +
         ((k >> 128) mod 2^64) * 2^128 +
         ((k >> 192) mod 2^64) * 2^192 = k"
proof -
  define r0 where "r0 = k mod 2^64"
  define q0 where "q0 = k div 2^64"
  define r1 where "r1 = q0 mod 2^64"
  define q1 where "q1 = q0 div 2^64"
  define r2 where "r2 = q1 mod 2^64"
  define q2 where "q2 = q1 div 2^64"
  define r3 where "r3 = q2 mod 2^64"
  define q3 where "q3 = q2 div 2^64"

  have shift64: "k >> 64 = k div 2^64"
    unfolding shiftr_def
    by (simp add: drop_bit_eq_div)

  have shift128: "k >> 128 = q1"
  proof -
    have "k >> 128 = k div 2^128"
      unfolding shiftr_def
      by (simp add: drop_bit_eq_div)
    also have "... = k div (2^64 * 2^64)"
      by (simp add: power_add)
    also have "... = (k div 2^64) div 2^64"
      by (rule zdiv_zmult2_eq) simp
    also have "... = q1"
      unfolding q0_def q1_def by simp
    finally show ?thesis .
  qed

  have shift128_div: "k div 2^128 = q1"
  proof -
    have "k >> 128 = k div 2^128"
      unfolding shiftr_def
      by (simp add: drop_bit_eq_div)
    then show ?thesis
      using shift128 by simp
  qed

  have shift192_div: "k div 2^192 = q2"
  proof -
    have "k div 2^192 = k div (2^128 * 2^64)"
      by (simp add: power_add)
    also have "... = (k div 2^128) div 2^64"
      by (rule zdiv_zmult2_eq) simp
    also have "... = q1 div 2^64"
      using shift128_div by simp
    also have "... = q2"
      unfolding q2_def by simp
    finally show ?thesis .
  qed

  have shift192: "k >> 192 = q2"
  proof -
    have "k >> 192 = k div 2^192"
      unfolding shiftr_def
      by (simp add: drop_bit_eq_div)
    then show ?thesis
      using shift192_div by simp
  qed

  have q3_eq: "q3 = k div 2^256"
  proof -
    have "q3 = q2 div 2^64"
      unfolding q3_def by simp
    also have "... = (k div 2^192) div 2^64"
      using shift192_div by simp
    also have "... = k div (2^192 * 2^64)"
      by (rule zdiv_zmult2_eq[symmetric]) simp
    also have "... = k div 2^256"
      by (simp add: power_add)
    finally show ?thesis .
  qed

  have q3_zero: "q3 = 0"
    using q3_eq assms by (simp add: zdiv_eq_0_iff)

  have decomp0: "k = r0 + q0 * 2^64"
    using div_mult_mod_eq[of k "2^64"]
    unfolding r0_def q0_def
    by (simp add: algebra_simps)

  have decomp1: "q0 = r1 + q1 * 2^64"
    using div_mult_mod_eq[of q0 "2^64"]
    unfolding r1_def q1_def
    by (simp add: algebra_simps)

  have decomp2: "q1 = r2 + q2 * 2^64"
    using div_mult_mod_eq[of q1 "2^64"]
    unfolding r2_def q2_def
    by (simp add: algebra_simps)

  have decomp3: "q2 = r3 + q3 * 2^64"
    using div_mult_mod_eq[of q2 "2^64"]
    unfolding r3_def q3_def
    by (simp add: algebra_simps)

  have "r0 + r1 * 2^64 + r2 * 2^128 + r3 * 2^192 = k"
  proof -
    have "r0 + r1 * 2^64 + r2 * 2^128 + r3 * 2^192 =
          r0 + q0 * 2^64"
      using decomp1 decomp2 decomp3 q3_zero
      by (simp add: algebra_simps power_add)
    also have "... = k"
      using decomp0 by simp
    finally show ?thesis .
  qed

  have limb_eq:
    "k mod 2^64 + ((k >> 64) mod 2^64) * 2^64 +
     ((k >> 128) mod 2^64) * 2^128 +
     ((k >> 192) mod 2^64) * 2^192 =
     r0 + r1 * 2^64 + r2 * 2^128 + r3 * 2^192"
  proof -
    have e0: "k mod 2^64 = r0"
      unfolding r0_def by simp
    have e1: "(k >> 64) mod 2^64 = r1"
      using shift64 unfolding r1_def q0_def by simp
    have e2: "(k >> 128) mod 2^64 = r2"
      using shift128 unfolding r2_def q1_def by simp
    have e3: "(k >> 192) mod 2^64 = r3"
      using shift192 unfolding r3_def q2_def by simp
    show ?thesis
      using e0 e1 e2 e3 by presburger
  qed

  then show ?thesis
    using `r0 + r1 * 2^64 + r2 * 2^128 + r3 * 2^192 = k`
    by presburger
qed
                                                             

lemma uint_word_of_int_mod1: "uint (word_of_int (x mod 2^64) :: u64) = x mod 2^64"
  by (simp add: uint_word_of_int)

lemma uint_word_of_int_mod2: "uint (word_of_int ((x >> 64) mod 2^64) :: u64) = (x >> 64) mod 2^64"
  by (simp add: uint_word_of_int)

lemma uint_word_of_int_mod3: "uint (word_of_int ((x >> 128) mod 2^64) :: u64) = (x >> 128) mod 2^64"
  by (simp add: uint_word_of_int)

lemma uint_word_of_int_mod4: "uint (word_of_int ((x >> 192) mod 2^64) :: u64) = (x >> 192) mod 2^64"
  by (simp add: uint_word_of_int)

lemma uint256_to_int_int_to_uint256:
  fixes k :: int
  assumes "0 \<le> k" and "k < 2^256"
  shows "uint256_to_int (int_to_uint256 k) = k"
proof -
  define y where "y = int_to_uint256 k"
  obtain a b c d where y_eq: "y = \<lparr>z0=a, z1=b, z2=c, z3=d\<rparr>"
    by (cases y) auto
  have a_eq: "a = word_of_int (k mod 2^64)"
    using y_eq y_def unfolding int_to_uint256_def by simp
  have b_eq: "b = word_of_int ((k >> 64) mod 2^64)"
    using y_eq y_def unfolding int_to_uint256_def by simp
  have c_eq: "c = word_of_int ((k >> 128) mod 2^64)"
    using y_eq y_def unfolding int_to_uint256_def by simp
  have d_eq: "d = word_of_int ((k >> 192) mod 2^64)"
    using y_eq y_def unfolding int_to_uint256_def by simp
  have "uint256_to_int y = uint a + (uint b << 64) + (uint c << 128) + (uint d << 192)"
    unfolding y_eq uint256_to_int_def by (simp add: Let_def)
  also have "... = uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192"
    by (simp only: int_shiftl_eq_mult)
  also have "... = (k mod 2^64) + ((k >> 64) mod 2^64) * 2^64 + 
                   ((k >> 128) mod 2^64) * 2^128 + ((k >> 192) mod 2^64) * 2^192"
    unfolding a_eq b_eq c_eq d_eq
    by (simp only: uint_word_of_int_mod1 uint_word_of_int_mod2 
                    uint_word_of_int_mod3 uint_word_of_int_mod4)
  also have "... = k"
    using assms by (rule uint_decomp_256)
  finally show ?thesis unfolding y_def .
qed


lemma uint256_word256_roundtrip:
  "uint256_to_word256 (word256_to_uint256 x) = x"
proof -
  have u_lt: "uint x < 2^256"
    using uint_lt2p[where 'a=256, of x] by simp
  have u_ge: "0 \<le> uint x" by simp
  have "uint256_to_word256 (word256_to_uint256 x) = 
        word_of_int (uint256_to_int (int_to_uint256 (uint x)))"
    by (simp add: uint256_to_word256_def word256_to_uint256_def)
  also have "... = word_of_int (uint x)"
    using uint256_to_int_int_to_uint256[OF u_ge u_lt] by simp
  also have "... = x"
    by simp
  finally show ?thesis .
qed

lemma Len64_nonneg: "0 \<le> Len64 x"
  by simp

lemma bitlen_lt_64_imp_z1_zero: "BitLen y < 64 \<Longrightarrow> z1 y = 0"
  unfolding BitLen_def
  using Len64_nonneg by (auto split: if_splits)

lemma bitlen_lt_128_imp_z2_zero: "BitLen y < 128 \<Longrightarrow> z2 y = 0"
  unfolding BitLen_def
  using Len64_nonneg by (auto split: if_splits)

lemma bitlen_lt_192_imp_z3_zero: "BitLen y < 192 \<Longrightarrow> z3 y = 0"
  unfolding BitLen_def
  using Len64_nonneg by (auto split: if_splits)

lemma len8tab_le_8: "len8tab w \<le> 8"
  unfolding len8tab_def
  by (simp split: if_splits)

lemma len8tab_upper: "len8tab w \<le> 8"
  unfolding len8tab_def by (simp split: if_splits)

lemma Len64_le_64: "Len64 x \<le> 64"
proof -
  show ?thesis
    unfolding Len64_def Let_def
    apply (auto split: if_splits prod.splits)
    unfolding len8tab_def
    by auto
qed

lemma bitlen_le_256: "BitLen y \<le> 256"
proof -
  show ?thesis
  proof (cases "z3 y \<noteq> 0")
    case True
    have "BitLen y = 192 + Len64 (z3 y)"
      unfolding BitLen_def using True by simp
    also have "192 + Len64 (z3 y) \<le> 192 + 64"
      using Len64_le_64[of "z3 y"] by simp
    also have "... = 256" by simp
    finally show ?thesis .
  next
    case z30: False
    show ?thesis
    proof (cases "z2 y \<noteq> 0")
      case True
      have "BitLen y = 128 + Len64 (z2 y)"
        unfolding BitLen_def using z30 True by simp
      also have "128 + Len64 (z2 y) \<le> 128 + 64"
        using Len64_le_64[of "z2 y"] by simp
      also have "... = 192" by simp
      also have "... \<le> 256" by simp
      finally show ?thesis .
    next
      case z20: False
      show ?thesis
      proof (cases "z1 y \<noteq> 0")
        case True
        have "BitLen y = 64 + Len64 (z1 y)"
          unfolding BitLen_def using z30 z20 True by simp
        also have "64 + Len64 (z1 y) \<le> 64 + 64"
          using Len64_le_64[of "z1 y"] by simp
        also have "... = 128" by simp
        also have "... \<le> 256" by simp
        finally show ?thesis .
      next
        case False
        have "BitLen y = Len64 (z0 y)"
          unfolding BitLen_def using z30 z20 False by simp
        also have "Len64 (z0 y) \<le> 64"
          using Len64_le_64[of "z0 y"] by simp
        also have "... \<le> 256" by simp
        finally show ?thesis .
      qed
    qed
  qed
qed

lemma and_1_eq_0_imp_even:
  "(base :: u256) AND 1 = 0 \<Longrightarrow> even base"
  by (smt (z3) and_one_eq even_iff_mod_2_eq_zero mod_word_one)

lemma and_one_eq_zero_iff_mod2_u64: "((w :: u64) AND 1 = 0) = (unat w mod 2 = 0)"
proof
  assume "w AND 1 = 0"
  have "unat w mod 2 = unat w mod unat (2 :: u64)"
    by simp
  also have "... = unat (w mod 2)"
    using unat_mod_distrib[of w "2 :: u64"] by simp
  also have "w mod 2 = 0"
  proof -
    from `w AND 1 = 0` have "even_word w"
      by (simp add: even_word_iff[symmetric])
    hence "even w" unfolding even_word_def .
    thus "w mod 2 = 0" by (simp add: even_iff_mod_2_eq_zero)
  qed
  also have "unat 0 = 0" by simp
  finally show "unat w mod 2 = 0" .
next
  assume "unat w mod 2 = 0"
  have "unat (w mod 2) = unat w mod unat (2 :: u64)"
    by (rule unat_mod_distrib)
  also have "... = 0" using `unat w mod 2 = 0` by simp
  finally have "unat (w mod 2) = 0" .
  hence "w mod 2 = 0" by (simp add: unat_eq_0)
  hence "even w" by (simp add: even_iff_mod_2_eq_zero)
  hence "even_word w" unfolding even_word_def .
  thus "w AND 1 = 0" by (simp add: even_word_iff)
qed

lemma and_one_eq_zero_iff_mod2_u256: "((w :: u256) AND 1 = 0) = (unat w mod 2 = 0)"
proof
  assume "w AND 1 = 0"
  have "unat w mod 2 = unat w mod unat (2 :: u256)"
    by simp
  also have "... = unat (w mod 2)"
    using unat_mod_distrib[of w "2 :: u256"] by simp
  also have "w mod 2 = 0"
  proof -
    from `w AND 1 = 0` have "even_word w"
      by (simp add: even_word_iff[symmetric])
    hence "even w" unfolding even_word_def .
    thus "w mod 2 = 0" by (simp add: even_iff_mod_2_eq_zero)
  qed
  also have "unat 0 = 0" by simp
  finally show "unat w mod 2 = 0" .
next
  assume "unat w mod 2 = 0"
  have "unat (w mod 2) = unat w mod unat (2 :: u256)"
    by (rule unat_mod_distrib)
  also have "... = 0" using `unat w mod 2 = 0` by simp
  finally have "unat (w mod 2) = 0" .
  hence "w mod 2 = 0" by (simp add: unat_eq_0)
  hence "even w" by (simp add: even_iff_mod_2_eq_zero)
  hence "even_word w" unfolding even_word_def .
  thus "w AND 1 = 0" by (simp add: even_word_iff)
qed

lemma factor_256: "((2::int)^64 - 1) * (1 + 2^64 + 2^128 + 2^192) = 2^256 - 1"
  by code_simp

lemma uint256_to_int_bound: "uint256_to_int y < 2^256"
proof (cases y)
  case (fields a b c d)
  have bounds: "uint a < 2^64" "uint b < 2^64" "uint c < 2^64" "uint d < 2^64"
    using uint_lt2p[where 'a=64] by (simp_all add: word_size)
  have "uint256_to_int (\<lparr>z0=a,z1=b,z2=c,z3=d\<rparr>) = 
        uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192"
    unfolding uint256_to_int_def by (simp add: Let_def int_shiftl_eq_mult)
  also have "... \<le> (2^64 - 1) + (2^64 - 1) * 2^64 + (2^64 - 1) * 2^128 + (2^64 - 1) * 2^192"
    using bounds by (intro add_mono mult_right_mono; simp)
  also have "... = (2^64 - 1) * (1 + 2^64 + 2^128 + 2^192)"
    by (simp add: algebra_simps)
  also have "... = 2^256 - 1"
    by (simp add: factor_256)
  also have "... < 2^256" by simp
  finally show ?thesis unfolding fields .
qed


lemma uint256_to_int_nonneg: "0 \<le> uint256_to_int y"
proof (cases y)
  case (fields a b c d)
  have "uint256_to_int (\<lparr>z0=a,z1=b,z2=c,z3=d\<rparr>) = 
        uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192"
    unfolding uint256_to_int_def by (simp add: Let_def int_shiftl_eq_mult)
  then show ?thesis unfolding fields by simp
qed

lemma uint_word_of_int_cancel: "uint (word_of_int (uint256_to_int y) :: u256) = uint256_to_int y"
proof -
  have "uint (word_of_int (uint256_to_int y) :: u256) = uint256_to_int y mod 2^256"
    by (simp add: uint_word_of_int)
  also have "... = uint256_to_int y"
    using uint256_to_int_nonneg uint256_to_int_bound by simp
  finally show ?thesis .
qed

lemma limb0_aux: "(x + y * (2^64 :: int)) mod (2^64 :: int) = x mod (2^64 :: int)"
  by presburger



lemma limb0: "((uint (a::u64) + uint (b::u64) * 2^64 + uint (c::u64) * 2^128 + uint (d::u64) * 2^192) mod 2^64) = uint a"
proof -
  have "(uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192) mod 2^64 =
        (uint a + 2^64 * (uint b + uint c * 2^64 + uint d * 2^128)) mod 2^64"
    by (simp add: algebra_simps)
  also have "... = uint a mod 2^64"
    by (metis limb0_aux mult.commute)  also have "... = uint a"
    using uint_lt_2p64[of a] by simp
  finally show ?thesis .
qed

lemma div_add_mult: "0 < (n::int) \<Longrightarrow> (x + n * y) div n = y + x div n"
  by simp

lemma pos_2p64: "0 < (2::int)^64"
  by simp

lemma pow128: "(2::int)^128 = (2::int)^64 * (2::int)^64"
  by simp

lemma pow192: "(2::int)^192 = (2::int)^64 * (2::int)^128"
  by simp

lemma limb1: "(((uint (a::u64) + uint (b::u64) * 2^64 + uint (c::u64) * 2^128 + uint (d::u64) * 2^192) >> 64) mod 2^64) = uint b"
proof -
  have step3: "uint a div (2^64 :: int) = (0::int)"
    using uint_lt_2p64[of a] uint_nonnegative[of a] pos_2p64
    by (metis (no_types) zdiv_eq_0_iff)
  have aux: "(2::int)^64 * (uint b + uint c * 2^64 + uint d * 2^128) =
             uint b * 2^64 + uint c * 2^128 + uint d * 2^192"
  proof -
    have "(2::int)^64 * (uint b + uint c * 2^64 + uint d * 2^128) =
          uint b * 2^64 + uint c * (2^64 * 2^64) + uint d * (2^64 * 2^128)"
      by (simp only: ring_distribs mult_ac)
    also have "... = uint b * 2^64 + uint c * 2^128 + uint d * 2^192"
      unfolding pow128 pow192 by (rule refl)
    finally show ?thesis .
  qed
  have step1: "uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192 =
               uint a + (2::int)^64 * (uint b + uint c * 2^64 + uint d * 2^128)"
    using aux by presburger
  have step2: "(uint a + (2::int)^64 * (uint b + uint c * 2^64 + uint d * 2^128)) div (2::int)^64 =
               (uint b + uint c * 2^64 + uint d * 2^128) + uint a div (2::int)^64"
    using pos_2p64 div_add_mult by presburger
  have div_eq: "(uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192) div (2::int)^64 =
                 uint b + uint c * 2^64 + uint d * 2^128"
  proof -
    from step1 have "(uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192) div (2::int)^64 =
                     (uint a + (2::int)^64 * (uint b + uint c * 2^64 + uint d * 2^128)) div (2::int)^64"
      by presburger
    also from step2 have "... = (uint b + uint c * 2^64 + uint d * 2^128) + uint a div (2::int)^64"
      by presburger
    also from step3 have "... = uint b + uint c * 2^64 + uint d * 2^128"
      by presburger
    finally show ?thesis .
  qed
  have mod_eq: "(uint b + uint c * 2^64 + uint d * 2^128) mod (2::int)^64 = uint b"
  proof -
    have inner: "(uint c + uint d * 2^64) * (2::int)^64 = uint c * 2^64 + uint d * 2^128"
    proof -
      have "(uint c + uint d * 2^64) * (2::int)^64 = uint c * (2::int)^64 + uint d * 2^64 * (2::int)^64"
        by (simp only: ring_distribs mult_ac)
      also have "... = uint c * (2::int)^64 + uint d * ((2::int)^64 * (2::int)^64)"
        by (simp only: mult_ac)
      also have "... = uint c * 2^64 + uint d * 2^128"
        unfolding pow128 by (rule refl)
      finally show ?thesis .
    qed
    have eq: "uint b + uint c * 2^64 + uint d * 2^128 = uint b + (uint c + uint d * 2^64) * (2::int)^64"
      using inner by presburger
    have "(uint b + uint c * 2^64 + uint d * 2^128) mod (2::int)^64 =
          (uint b + (uint c + uint d * 2^64) * (2::int)^64) mod (2::int)^64"
      using eq by presburger
    also have "... = uint b mod (2::int)^64"
      using limb0_aux by presburger
    also have "... = uint b"
      using uint_lt_2p64[of b] uint_nonnegative[of b] pos_2p64
      by (metis (no_types) mod_pos_pos_trivial)
    finally show ?thesis .
  qed
  show ?thesis
    using div_eq mod_eq
    unfolding shiftr_def drop_bit_eq_div
    by argo
qed

lemma pos_2p128: "0 < (2::int)^128"
  by code_simp

lemma pos_2p192: "0 < (2::int)^192"
  by code_simp

lemma bound_128: "((2::int)^64 - 1) * (1 + (2::int)^64) = (2::int)^128 - 1"
  by code_simp

lemma bound_192: "((2::int)^64 - 1) * (1 + (2::int)^64 + (2::int)^128) = (2::int)^192 - 1"
  by code_simp

lemma pow192': "(2::int)^128 * (2::int)^64 = (2::int)^192"
  by simp

lemma bound_128_raw: "((2::int)^64 - 1) + ((2::int)^64 - 1) * 2^64 = (2::int)^128 - 1"
  by code_simp

lemma sum2_lt_2p128: "uint (a::u64) + uint (b::u64) * 2^64 < (2::int)^128"
proof -
  have a_bound: "uint a \<le> (2::int)^64 - 1"
    using uint_lt_2p64[of a] by presburger
  have b_bound: "uint b \<le> (2::int)^64 - 1"
    using uint_lt_2p64[of b] by presburger
  have mult_bound: "uint b * 2^64 \<le> ((2::int)^64 - 1) * 2^64"
  proof (rule mult_right_mono)
    show "uint b \<le> (2::int)^64 - 1" by (rule b_bound)
    show "0 \<le> (2::int)^64" using pos_2p64 by (rule less_imp_le)
  qed
  have "uint a + uint b * 2^64 \<le> ((2::int)^64 - 1) + ((2::int)^64 - 1) * 2^64"
    using a_bound mult_bound by (rule add_mono)
  also have "... = (2::int)^128 - 1"
    using bound_128_raw by presburger
  also have "... < (2::int)^128"
    by presburger
  finally show ?thesis .
qed

lemma bound_192_raw: "((2::int)^64 - 1) + ((2::int)^64 - 1) * 2^64 + ((2::int)^64 - 1) * 2^128 = (2::int)^192 - 1"
  by code_simp

lemma sum3_lt_2p192: "uint (a::u64) + uint (b::u64) * 2^64 + uint (c::u64) * 2^128 < (2::int)^192"
proof -
  have a_bound: "uint a \<le> (2::int)^64 - 1"
    using uint_lt_2p64[of a] by presburger
  have b_bound: "uint b \<le> (2::int)^64 - 1"
    using uint_lt_2p64[of b] by presburger
  have c_bound: "uint c \<le> (2::int)^64 - 1"
    using uint_lt_2p64[of c] by presburger
  have mult_bound_b: "uint b * 2^64 \<le> ((2::int)^64 - 1) * 2^64"
  proof (rule mult_right_mono)
    show "uint b \<le> (2::int)^64 - 1" by (rule b_bound)
    show "0 \<le> (2::int)^64" using pos_2p64 by (rule less_imp_le)
  qed
  have mult_bound_c: "uint c * 2^128 \<le> ((2::int)^64 - 1) * 2^128"
  proof (rule mult_right_mono)
    show "uint c \<le> (2::int)^64 - 1" by (rule c_bound)
    show "0 \<le> (2::int)^128" using pos_2p128 by (rule less_imp_le)
  qed
  have "uint a + uint b * 2^64 \<le> ((2::int)^64 - 1) + ((2::int)^64 - 1) * 2^64"
    using a_bound mult_bound_b by (rule add_mono)
  then have "uint a + uint b * 2^64 + uint c * 2^128
             \<le> ((2::int)^64 - 1) + ((2::int)^64 - 1) * 2^64 + ((2::int)^64 - 1) * 2^128"
    using mult_bound_c by (rule add_mono)
  also have "... = (2::int)^192 - 1"
    using bound_192_raw by presburger
  also have "... < (2::int)^192"
    by presburger
  finally show ?thesis .
qed

lemma limb2: "(((uint (a::u64) + uint (b::u64) * 2^64 + uint (c::u64) * 2^128 + uint (d::u64) * 2^192) >> 128) mod 2^64) = uint c"
proof -
  have pos_2p64_le: "0 \<le> (2::int)^64"
    using pos_2p64 by (rule less_imp_le)
  have aux: "(2::int)^128 * (uint c + uint d * 2^64) = uint c * 2^128 + uint d * 2^192"
  proof -
    have "(2::int)^128 * (uint c + uint d * 2^64) =
          uint c * (2::int)^128 + uint d * (2::int)^128 * 2^64"
      by (simp only: ring_distribs mult_ac)
    also have "... = uint c * 2^128 + uint d * ((2::int)^128 * (2::int)^64)"
      by (simp only: mult_ac)
    also have "... = uint c * 2^128 + uint d * 2^192"
      unfolding pow192' by (rule refl)
    finally show ?thesis .
  qed
  have step1: "uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192 =
               (uint a + uint b * 2^64) + (2::int)^128 * (uint c + uint d * 2^64)"
    using aux by presburger
  have step2: "((uint a + uint b * 2^64) + (2::int)^128 * (uint c + uint d * 2^64)) div (2::int)^128 =
               (uint c + uint d * 2^64) + (uint a + uint b * 2^64) div (2::int)^128"
    using pos_2p128 div_add_mult by presburger
  have nonneg: "0 \<le> uint a + uint b * 2^64"
  proof -
    have a: "0 \<le> uint a" by (rule uint_nonnegative)
    have b: "0 \<le> uint b * 2^64"
      by (rule mult_nonneg_nonneg[OF uint_nonnegative[of b] pos_2p64_le])
    from a b show ?thesis by (rule add_nonneg_nonneg)
  qed
  have step3: "(uint a + uint b * 2^64) div (2::int)^128 = (0::int)"
    using nonneg sum2_lt_2p128 pos_2p128
    by (metis (no_types) div_pos_pos_trivial)
  have div_eq: "(uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192) div (2::int)^128 =
                 uint c + uint d * 2^64"
  proof -
    from step1 have "(uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192) div (2::int)^128 =
                     ((uint a + uint b * 2^64) + (2::int)^128 * (uint c + uint d * 2^64)) div (2::int)^128"
      by presburger
    also from step2 have "... = (uint c + uint d * 2^64) + (uint a + uint b * 2^64) div (2::int)^128"
      by presburger
    also from step3 have "... = uint c + uint d * 2^64"
      by presburger
    finally show ?thesis .
  qed
  have mod_eq: "(uint c + uint d * 2^64) mod (2::int)^64 = uint c"
  proof -
    have "(uint c + uint d * 2^64) mod (2::int)^64 = uint c mod (2::int)^64"
      using limb0_aux[of "uint c" "uint d"] by presburger
    also have "... = uint c"
      using uint_lt_2p64[of c] uint_nonnegative[of c] pos_2p64
      by (metis (no_types) mod_pos_pos_trivial)
    finally show ?thesis .
  qed
  show ?thesis
    using div_eq mod_eq
    unfolding shiftr_def drop_bit_eq_div
    by argo
qed

lemma limb3: "(((uint (a::u64) + uint (b::u64) * 2^64 + uint (c::u64) * 2^128 + uint (d::u64) * 2^192) >> 192) mod 2^64) = uint d"
proof -
  have pos_2p64_le: "0 \<le> (2::int)^64"
    using pos_2p64 by (rule less_imp_le)
  have pos_2p128_le: "0 \<le> (2::int)^128"
    using pos_2p128 by (rule less_imp_le)
  have nonneg_a: "0 \<le> uint a" by (rule uint_nonnegative)
  have nonneg_b: "0 \<le> uint b * 2^64"
    using uint_nonnegative[of b] pos_2p64_le by (rule mult_nonneg_nonneg)
  have nonneg_c: "0 \<le> uint c * 2^128"
    using uint_nonnegative[of c] pos_2p128_le by (rule mult_nonneg_nonneg)
  have nonneg_ab: "0 \<le> uint a + uint b * 2^64"
    using nonneg_a nonneg_b by (rule add_nonneg_nonneg)
  have nonneg: "0 \<le> uint a + uint b * 2^64 + uint c * 2^128"
    using nonneg_ab nonneg_c by (rule add_nonneg_nonneg)
  have step1: "uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192 =
               (uint a + uint b * 2^64 + uint c * 2^128) + (2::int)^192 * uint d"
    by presburger
  have step2: "((uint a + uint b * 2^64 + uint c * 2^128) + (2::int)^192 * uint d) div (2::int)^192 =
               uint d + (uint a + uint b * 2^64 + uint c * 2^128) div (2::int)^192"
    using pos_2p192 div_add_mult by presburger
  have step3: "(uint a + uint b * 2^64 + uint c * 2^128) div (2::int)^192 = (0::int)"
    using nonneg sum3_lt_2p192 pos_2p192
    by (metis (no_types) div_pos_pos_trivial)
  have div_eq: "(uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192) div (2::int)^192 = uint d"
  proof -
    from step1 have "(uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192) div (2::int)^192 =
                     ((uint a + uint b * 2^64 + uint c * 2^128) + (2::int)^192 * uint d) div (2::int)^192"
      by presburger
    also from step2 have "... = uint d + (uint a + uint b * 2^64 + uint c * 2^128) div (2::int)^192"
      by presburger
    also from step3 have "... = uint d"
      by presburger
    finally show ?thesis .
  qed
  have mod_eq: "uint d mod (2::int)^64 = uint d"
    using uint_lt_2p64[of d] uint_nonnegative[of d] pos_2p64
    by (metis (no_types) mod_pos_pos_trivial)
  show ?thesis
    using div_eq mod_eq
    unfolding shiftr_def drop_bit_eq_div
    by argo
qed

lemma int_to_uint256_uint256_to_int: "int_to_uint256 (uint256_to_int y) = y"
proof (cases y)
  case (fields a b c d)
  have V: "uint256_to_int (\<lparr>z0=a,z1=b,z2=c,z3=d\<rparr>) = 
           uint a + uint b * 2^64 + uint c * 2^128 + uint d * 2^192"
    unfolding uint256_to_int_def Let_def uint256.simps int_shiftl_eq_mult by (rule refl)
  have z0_eq: "word_of_int (uint256_to_int (\<lparr>z0=a,z1=b,z2=c,z3=d\<rparr>) mod 2^64) = a"
    unfolding V limb0 by (simp only: word_of_int_uint)
  have z1_eq: "word_of_int ((uint256_to_int (\<lparr>z0=a,z1=b,z2=c,z3=d\<rparr>) >> 64) mod 2^64) = b"
    unfolding V limb1 by (simp only: word_of_int_uint)
  have z2_eq: "word_of_int ((uint256_to_int (\<lparr>z0=a,z1=b,z2=c,z3=d\<rparr>) >> 128) mod 2^64) = c"
    unfolding V limb2 by (simp only: word_of_int_uint)
  have z3_eq: "word_of_int ((uint256_to_int (\<lparr>z0=a,z1=b,z2=c,z3=d\<rparr>) >> 192) mod 2^64) = d"
    unfolding V limb3 by (simp only: word_of_int_uint)
  show ?thesis
    unfolding fields int_to_uint256_def using z0_eq z1_eq z2_eq z3_eq by simp
qed

lemma word256_to_uint256_inv: "word256_to_uint256 (uint256_to_word256 y) = y"
  unfolding word256_to_uint256_def uint256_to_word256_def
  using uint_word_of_int_cancel int_to_uint256_uint256_to_int
  by metis


lemma uint_shiftr32: "uint ((w :: u64) >> 32) = uint w div 2^32"
proof -
  have "uint ((w :: u64) >> 32) = uint (w div (2^32 :: u64))"
    by (metis drop_bit_eq_div shiftr_def)
  also have "... = uint w div uint (2^32 :: u64)"
    by (rule uint_div)
  also have "... = uint w div 2^32"
  proof -
    have "0 < (2^32 :: u64)" by code_simp
    then have "uint (2^32 :: u64) = 2^32" by (rule uint_2p)
    then show ?thesis by presburger
  qed
  finally show ?thesis .
qed

lemma uint_and_mask32: "uint ((w :: u64) AND ((1 << 32) - 1)) = uint w mod 2^32"
proof -
  have mask: "((1 << 32) - 1 :: u64) = mask 32" by code_simp
  have eq1: "w AND mask 32 = word_of_int (uint w mod 2^32)"
    by (rule and_mask_mod_2p)
  have eq2: "uint (word_of_int (uint w mod 2^32) :: u64) = (uint w mod 2^32) mod 2^64"
    by (simp add: uint_word_of_int)
  have eq3: "(uint w mod 2^32) mod 2^64 = uint w mod 2^32"
  proof -
    have "uint w mod 2^32 < 2^32" by simp
    also have "... < 2^64" by code_simp
    finally have "uint w mod 2^32 < 2^64" .
    then show ?thesis by simp
  qed
  show ?thesis
    using mask eq1 eq2 eq3 by presburger
qed


lemma word_decomp_32:
  "uint (w :: u64) = uint (w >> 32) * 2^32 + uint (w AND ((1 << 32) - 1 :: u64))"
proof -
  have "uint (w >> 32) * 2^32 + uint (w AND ((1 << 32) - 1 :: u64)) =
        (uint w div 2^32) * 2^32 + uint w mod 2^32"
    by (simp add: uint_shiftr32 uint_and_mask32)
  also have "... = uint w"
    by (rule div_mult_mod_eq)
  finally show ?thesis
    by simp
qed

lemma uint_mul32:
  fixes x y :: u64
  assumes "uint x < 2^32" and "uint y < 2^32"
  shows "uint (x * y) = uint x * uint y"
proof -
  have prod_lt: "uint x * uint y < 2^64"
  proof -
    have "uint x * uint y < 2^32 * 2^32"
      by (rule mult_strict_mono') (use assms uint_nonnegative in auto)
    also have "... = 2^64"
      by code_simp
    finally show ?thesis .
  qed

  have "uint (x * y) = uint x * uint y mod 2 ^ LENGTH(64)"
    by (rule uint_word_ariths(3))
  also have "... = uint x * uint y mod 2^64"
    by simp
  also have "... = uint x * uint y"
    using prod_lt by simp
  finally show ?thesis .
qed

lemma uint_div32_lt:
  "uint (w :: u64) div 2^32 < 2^32"
proof -
  have unat_lt: "unat (w >> 32) < 2^32"
    using shift32_unat_lt[of w] .
  have uint_pow: "uint (2^32 :: u64) = 2^32"
    by (rule uint_2p) simp
  have unat_pow: "unat (2^32 :: u64) = 2^32"
    using uint_pow by (simp add: unat_eq_nat_uint)
  have word_lt: "(w >> 32) < (2^32 :: u64)"
    unfolding word_less_nat_alt
    using unat_lt unat_pow by simp
  have uint_lt: "uint (w >> 32) < uint (2^32 :: u64)"
    using word_lt by (simp add: word_less_alt)
  show ?thesis
    using uint_lt uint_pow by (metis uint_shiftr32)
qed

lemma mul64_hi_eq:
  "uint (fst (mul64 a b)) = (uint a * uint b) div 2^64"
proof -
  define mask32 where "mask32 = ((1 << 32) - 1 :: u64)"
  define x0 where "x0 = a AND mask32"
  define x1 where "x1 = a >> 32"
  define y0 where "y0 = b AND mask32"
  define y1 where "y1 = b >> 32"
  define w0 where "w0 = x0 * y0"
  define t where "t = x1 * y0 + (w0 >> 32)"
  define w1 where "w1 = t AND mask32"
  define w2 where "w2 = t >> 32"
  define w1' where "w1' = w1 + x0 * y1"
  define hi where "hi = x1 * y1 + w2 + (w1' >> 32)"
  define A where "A = uint a"
  define B where "B = uint b"
  define X0 where "X0 = uint x0"
  define X1 where "X1 = uint x1"
  define Y0 where "Y0 = uint y0"
  define Y1 where "Y1 = uint y1"

  have fst_eq: "fst (mul64 a b) = hi"
    unfolding mul64_def Let_def mask32_def x0_def x1_def y0_def y1_def
              w0_def t_def w1_def w2_def w1'_def hi_def
    by simp

  have X0_eq: "X0 = A mod 2^32"
    using uint_and_mask32[of a]
    unfolding X0_def A_def x0_def mask32_def by simp

  have X1_eq: "X1 = A div 2^32"
    using uint_shiftr32[of a]
    unfolding X1_def A_def x1_def by simp

  have Y0_eq: "Y0 = B mod 2^32"
    using uint_and_mask32[of b]
    unfolding Y0_def B_def y0_def mask32_def by simp

  have Y1_eq: "Y1 = B div 2^32"
    using uint_shiftr32[of b]
    unfolding Y1_def B_def y1_def by simp

  have X0_lt: "X0 < 2^32"
    using X0_eq by simp
  have X1_lt: "X1 < 2^32"
    using X1_eq uint_div32_lt[of a]
    unfolding A_def by simp
  have Y0_lt: "Y0 < 2^32"
    using Y0_eq by simp
  have Y1_lt: "Y1 < 2^32"
    using Y1_eq uint_div32_lt[of b]
    unfolding B_def by simp

  have A_decomp: "A = X1 * 2^32 + X0"
    using word_decomp_32[of a]
    unfolding A_def X1_def X0_def x1_def x0_def mask32_def by simp

  have B_decomp: "B = Y1 * 2^32 + Y0"
    using word_decomp_32[of b]
    unfolding B_def Y1_def Y0_def y1_def y0_def mask32_def by simp

  have x0y0_uint: "uint (x0 * y0) = X0 * Y0"
    using uint_mul32[of x0 y0] X0_lt Y0_lt
    unfolding X0_def Y0_def by simp

  have x1y0_uint: "uint (x1 * y0) = X1 * Y0"
    using uint_mul32[of x1 y0] X1_lt Y0_lt
    unfolding X1_def Y0_def by simp

  have x0y1_uint: "uint (x0 * y1) = X0 * Y1"
    using uint_mul32[of x0 y1] X0_lt Y1_lt
    unfolding X0_def Y1_def by simp

  have x1y1_uint: "uint (x1 * y1) = X1 * Y1"
    using uint_mul32[of x1 y1] X1_lt Y1_lt
    unfolding X1_def Y1_def by simp

  have w0_uint: "uint w0 = X0 * Y0"
    unfolding w0_def using x0y0_uint by simp

  have w0_shift: "uint (w0 >> 32) = (X0 * Y0) div 2^32"
    using uint_shiftr32[of w0] w0_uint by presburger

  have t_uint:
    "uint t = (X1 * Y0 + (X0 * Y0) div 2^32) mod 2^64"
  proof -
    have "uint t = (uint (x1 * y0) + uint (w0 >> 32)) mod 2 ^ LENGTH(64)"
      unfolding t_def
      by (rule uint_word_ariths(1))
    also have "... = (uint (x1 * y0) + uint (w0 >> 32)) mod 2^64"
      by simp
    also have "... = (X1 * Y0 + (X0 * Y0) div 2^32) mod 2^64"
      using x1y0_uint w0_shift by presburger
    finally show ?thesis .
  qed

  have w1_uint: "uint w1 = uint t mod 2^32"
    unfolding w1_def mask32_def
    by (rule uint_and_mask32[of t])

  have w2_uint: "uint w2 = uint t div 2^32"
    unfolding w2_def
    by (rule uint_shiftr32[of t])

  have w1'_uint:
    "uint w1' = (uint w1 + X0 * Y1) mod 2^64"
  proof -
    have "uint w1' = (uint w1 + uint (x0 * y1)) mod 2 ^ LENGTH(64)"
      unfolding w1'_def
      by (rule uint_word_ariths(1))
    also have "... = (uint w1 + uint (x0 * y1)) mod 2^64"
      by simp
    also have "... = (uint w1 + X0 * Y1) mod 2^64"
      using x0y1_uint by presburger
    finally show ?thesis .
  qed

  have w1'_shift: "uint (w1' >> 32) = uint w1' div 2^32"
    by (rule uint_shiftr32[of w1'])

  have hi_uint:
    "uint hi = (X1 * Y1 + uint t div 2^32 + uint w1' div 2^32) mod 2^64"
  proof -
    have add2:
      "uint (w2 + (w1' >> 32)) =
       (uint w2 + uint (w1' >> 32)) mod 2^64"
    proof -
      have "uint (w2 + (w1' >> 32)) =
            (uint w2 + uint (w1' >> 32)) mod 2 ^ LENGTH(64)"
        by (rule uint_word_ariths(1))
      then show ?thesis
        by simp
    qed

    have hi_step:
      "uint hi =
       (uint (x1 * y1) + uint (w2 + (w1' >> 32))) mod 2^64"
    proof -
      have "uint hi = uint ((x1 * y1 + w2) + (w1' >> 32))"
        unfolding hi_def by simp
      also have "... =
          (uint (x1 * y1 + w2) + uint (w1' >> 32)) mod 2 ^ LENGTH(64)"
        by (rule uint_word_ariths(1))
      also have "... =
          ((uint (x1 * y1) + uint w2) mod 2 ^ LENGTH(64) +
           uint (w1' >> 32)) mod 2 ^ LENGTH(64)"
        by (simp add: uint_word_ariths(1))
      also have "... =
          (uint (x1 * y1) + uint w2 + uint (w1' >> 32)) mod 2 ^ LENGTH(64)"
        by (simp add: mod_add_left_eq)
      also have "... =
          (uint (x1 * y1) +
           (uint w2 + uint (w1' >> 32)) mod 2 ^ LENGTH(64)) mod 2 ^ LENGTH(64)"
        by presburger
      also have "... =
          (uint (x1 * y1) + uint (w2 + (w1' >> 32))) mod 2 ^ LENGTH(64)"
        by (simp add: uint_word_ariths(1))
      also have "... =
          (uint (x1 * y1) + uint (w2 + (w1' >> 32))) mod 2^64"
        by simp
      finally show ?thesis .
    qed

    have "uint hi =
          (uint (x1 * y1) + uint (w2 + (w1' >> 32))) mod 2^64"
      by (fact hi_step)
    also have "... =
          (X1 * Y1 + (uint w2 + uint (w1' >> 32)) mod 2^64) mod 2^64"
      using add2 x1y1_uint by presburger
    also have "... =
          (X1 * Y1 + uint w2 + uint (w1' >> 32)) mod 2^64"
      by (simp add: mod_add_right_eq add.assoc)
    also have "... =
          (X1 * Y1 + uint t div 2^32 + uint w1' div 2^32) mod 2^64"
      using w2_uint w1'_shift by presburger
    finally show ?thesis .
  qed

  define P where "P = X1 * Y1"
  define U where "U = X1 * Y0"
  define V where "V = X0 * Y1"
  define C where "C = X0 * Y0"

  have X0_nonneg: "0 <= X0"
    unfolding X0_def by (rule uint_nonnegative)
  have X1_nonneg: "0 <= X1"
    unfolding X1_def by (rule uint_nonnegative)
  have Y0_nonneg: "0 <= Y0"
    unfolding Y0_def by (rule uint_nonnegative)
  have Y1_nonneg: "0 <= Y1"
    unfolding Y1_def by (rule uint_nonnegative)

  have P_nonneg: "0 <= P"
    unfolding P_def using X1_nonneg Y1_nonneg by simp
  have U_nonneg: "0 <= U"
    unfolding U_def using X1_nonneg Y0_nonneg by simp
  have V_nonneg: "0 <= V"
    unfolding V_def using X0_nonneg Y1_nonneg by simp
  have C_nonneg: "0 <= C"
    unfolding C_def using X0_nonneg Y0_nonneg by simp

  have P_lt: "P < 2^64"
  proof -
    have "P < 2^32 * 2^32"
      unfolding P_def
      by (rule mult_strict_mono') (use X1_nonneg X1_lt Y1_nonneg Y1_lt in auto)
    also have "... = 2^64" by code_simp
    finally show ?thesis .
  qed

  have U_lt: "U < 2^64"
  proof -
    have "U < 2^32 * 2^32"
      unfolding U_def
      by (rule mult_strict_mono') (use X1_nonneg X1_lt Y0_nonneg Y0_lt in auto)
    also have "... = 2^64" by code_simp
    finally show ?thesis .
  qed

  have V_lt: "V < 2^64"
  proof -
    have "V < 2^32 * 2^32"
      unfolding V_def
      by (rule mult_strict_mono') (use X0_nonneg X0_lt Y1_nonneg Y1_lt in auto)
    also have "... = 2^64" by code_simp
    finally show ?thesis .
  qed

  have C_lt: "C < 2^64"
  proof -
    have "C < 2^32 * 2^32"
      unfolding C_def
      by (rule mult_strict_mono') (use X0_nonneg X0_lt Y0_nonneg Y0_lt in auto)
    also have "... = 2^64" by code_simp
    finally show ?thesis .
  qed

  have AB_eq:
    "A * B = P * 2^64 + (U + V) * 2^32 + C"
    using A_decomp B_decomp
    unfolding P_def U_def V_def C_def
    by (simp add: algebra_simps power_add)

  have t_alt:
    "uint t = (U + C div 2^32) mod 2^64"
    using t_uint unfolding U_def C_def by presburger

  have w1'_alt:
    "uint w1' = (uint t mod 2^32 + V) mod 2^64"
    using w1_uint w1'_uint unfolding V_def by presburger

  have hi_alt:
    "uint hi =
     (P + uint t div 2^32 + uint w1' div 2^32) mod 2^64"
    using hi_uint unfolding P_def by presburger

  have hi_value: "uint hi = (A * B) div 2^64"
  proof -
    have X0_le: "X0 <= 2^32 - 1" using X0_lt by linarith
    have X1_le: "X1 <= 2^32 - 1" using X1_lt by linarith
    have Y0_le: "Y0 <= 2^32 - 1" using Y0_lt by linarith
    have Y1_le: "Y1 <= 2^32 - 1" using Y1_lt by linarith

    have U_le_max: "U <= ((2^32 - 1)::int)^2"
      unfolding U_def power2_eq_square
      by (rule mult_mono') (use X1_nonneg Y0_nonneg X1_le Y0_le in auto)

    have V_le_max: "V <= ((2^32 - 1)::int)^2"
      unfolding V_def power2_eq_square
      by (rule mult_mono') (use X0_nonneg Y1_nonneg X0_le Y1_le in auto)

    have max_plus_lt: "((2^32 - 1)::int)^2 + ((2^32 - 1)::int) < (2^64::int)"
      by code_simp

    have Cdiv_ge: "0 <= C div 2^32"
      by (simp add: pos_imp_zdiv_nonneg_iff C_nonneg)

    have Cdiv_lt: "C div 2^32 < 2^32"
    proof -
      have "C <= 2^64 - 1" using C_lt by linarith
      then have C_le_bound: "C div 2^32 <= (2^64 - 1) div 2^32"
        by (rule zdiv_mono1) simp
      have bound_eq: "((2::int)^64 - 1) div ((2::int)^32) = (2::int)^32 - 1"
        by code_simp
      show ?thesis
        using C_le_bound bound_eq by linarith
    qed

    define Q where "Q = U + C div 2^32"
    define W where "W = Q mod 2^32 + V"

    have Q_ge: "0 <= Q" unfolding Q_def using U_nonneg Cdiv_ge by linarith
    have Q_lt: "Q < 2^64"
    proof -
      have "Q <= ((2^32 - 1)::int)^2 + ((2^32 - 1)::int)"
        unfolding Q_def using U_le_max Cdiv_lt by linarith
      then show ?thesis using max_plus_lt by linarith
    qed

    have W_ge: "0 <= W" unfolding W_def using V_nonneg by simp
    have W_lt: "W < 2^64"
    proof -
      have "Q mod 2^32 < 2^32" by simp
      have "W <= ((2^32 - 1)::int)^2 + ((2^32 - 1)::int)"
        unfolding W_def using V_le_max `Q mod 2^32 < 2^32` by linarith
      then show ?thesis using max_plus_lt by linarith
    qed

    have t_eq_Q: "uint t = Q"
    proof -
      have "uint t = (U + C div 2^32) mod 2^64"
        using t_alt by simp
      also have "... = Q"
        using Q_ge Q_lt unfolding Q_def by simp
      finally show ?thesis .
    qed

    have w1'_eq_W: "uint w1' = W"
    proof -
      have "uint w1' = (uint t mod 2^32 + V) mod 2^64"
        using w1'_alt by simp
      also have "... = (Q mod 2^32 + V) mod 2^64"
        using t_eq_Q by simp
      also have "... = W"
        using W_ge W_lt unfolding W_def by simp
      finally show ?thesis .
    qed

    define S where "S = P + Q div 2^32 + W div 2^32"

    have hi_S: "uint hi = S mod 2^64"
    proof -
      have "uint hi = (P + uint t div 2^32 + uint w1' div 2^32) mod 2^64"
        using hi_alt by simp
      also have "... = (P + Q div 2^32 + W div 2^32) mod 2^64"
        using t_eq_Q w1'_eq_W by simp
      also have "... = S mod 2^64"
        unfolding S_def by simp
      finally show ?thesis .
    qed

    have C_decomp: "C = (C div 2^32) * 2^32 + C mod 2^32"
      by (simp add: div_mult_mod_eq)
    have Q_decomp: "Q = (Q div 2^32) * 2^32 + Q mod 2^32"
      by (simp add: div_mult_mod_eq)
    have W_decomp: "W = (W div 2^32) * 2^32 + W mod 2^32"
      by (simp add: div_mult_mod_eq)

    have AB_decomp:
      "A * B = S * 2^64 + (W mod 2^32) * 2^32 + C mod 2^32"
    proof -
      have step1: "A * B = P * 2^64 + (U + V) * 2^32 + C"
        by (fact AB_eq)

      have step2:
        "P * 2^64 + (U + V) * 2^32 + C =
         P * 2^64 + (Q + V) * 2^32 + C mod 2^32"
        using C_decomp unfolding Q_def by (simp add: algebra_simps)

      have Q_mul:
        "Q * 2^32 =
         (Q div 2^32) * 2^64 + (Q mod 2^32) * 2^32"
      proof -
        have two64: "(2::int)^64 = (2::int)^32 * (2::int)^32"
          by (simp add: power_add [symmetric])
        show ?thesis
          using Q_decomp two64 by algebra
      qed

      have W_mul:
        "W * 2^32 =
         (W div 2^32) * 2^64 + (W mod 2^32) * 2^32"
      proof -
        have two64: "(2::int)^64 = (2::int)^32 * (2::int)^32"
          by (simp add: power_add [symmetric])
        show ?thesis
          using W_decomp two64 by algebra
      qed

      have step3:
        "P * 2^64 + (Q + V) * 2^32 + C mod 2^32 =
         P * 2^64 + (Q div 2^32) * 2^64 + W * 2^32 + C mod 2^32"
        using Q_mul unfolding W_def by (simp add: algebra_simps)

      have step4:
        "P * 2^64 + (Q div 2^32) * 2^64 + W * 2^32 + C mod 2^32 =
         S * 2^64 + (W mod 2^32) * 2^32 + C mod 2^32"
        using W_mul unfolding S_def by (simp add: algebra_simps)

      show ?thesis
        using step1 step2 step3 step4 by presburger
    qed

    define L where "L = (W mod 2^32) * 2^32 + C mod 2^32"

    have L_ge: "0 <= L" unfolding L_def by simp
    have L_lt: "L < 2^64"
    proof -
      have Wmod_lt: "W mod 2^32 < 2^32" by simp
      have Cmod_lt: "C mod 2^32 < 2^32" by simp
  
      have Wmod_le: "W mod 2^32 <= 2^32 - 1"
        using Wmod_lt by linarith
      have Cmod_le: "C mod 2^32 <= 2^32 - 1"
        using Cmod_lt by linarith
  
      have "W mod 2^32 * 2^32 <= (2^32 - 1) * 2^32"
        using Wmod_le by (rule mult_right_mono) simp
  
      then have "L <= (2^32 - 1) * 2^32 + (2^32 - 1)"
        unfolding L_def using Cmod_le by linarith
  
      also have "((2^32 - 1)::int) * (2^32::int) + ((2^32 - 1)::int) < (2^64::int)"
        by code_simp
  
      finally show ?thesis .
    qed

    have S_div: "(A * B) div 2^64 = S"
    proof -
      have "A * B = S * 2^64 + L"
        using AB_decomp unfolding L_def by simp
      then have "(A * B) div 2^64 = (S * 2^64 + L) div 2^64"
        by simp
      also have "... = S + L div 2^64"
        by simp
      also have "... = S"
        using L_ge L_lt by (simp add: zdiv_eq_0_iff)
      finally show ?thesis .
    qed

    have A_ge: "0 <= A" unfolding A_def by simp
    have B_ge: "0 <= B" unfolding B_def by simp
    have A_lt: "A < 2^64" using uint_lt_2p64[of a] unfolding A_def by simp
    have B_lt: "B < 2^64" using uint_lt_2p64[of b] unfolding B_def by simp

    have prod_lt: "A * B < 2^128"
    proof -
      have "A * B < 2^64 * 2^64"
        by (rule mult_strict_mono') (use A_lt B_lt A_ge B_ge in auto)
      then show ?thesis by (simp add: power_add)
    qed

    have D_ge: "0 <= (A * B) div 2^64"
    proof -
      have "0 <= A * B" using A_ge B_ge by simp
      then show ?thesis by (simp add: pos_imp_zdiv_nonneg_iff)
    qed

    have D_lt: "(A * B) div 2^64 < 2^64"
    proof -
      have "A * B <= 2^128 - 1" using prod_lt by linarith
      then have D_le_bound: "(A * B) div 2^64 <= (2^128 - 1) div 2^64"
        by (rule zdiv_mono1) simp
      have bound_eq: "((2::int)^128 - 1) div ((2::int)^64) = (2::int)^64 - 1"
        by code_simp
      show ?thesis
        using D_le_bound bound_eq by linarith
    qed

    have S_ge: "0 <= S" using S_div D_ge by presburger
    have S_lt: "S < 2^64" using S_div D_lt by presburger

    have "uint hi = S mod 2^64" by (fact hi_S)
    also have "... = S"
      using S_ge S_lt by simp
    also have "... = (A * B) div 2^64"
      using S_div by simp
    finally show ?thesis .
  qed

    show ?thesis
    proof -
      have "uint hi = A * B div 2^64"
        by (fact hi_value)
      also have "... = uint a * uint b div 2^64"
        unfolding A_def B_def by simp
      finally show ?thesis
        unfolding fst_eq by simp
    qed
qed


lemma uint_mul_mod64:
  "uint ((a :: u64) * (b :: u64)) = (uint a * uint b) mod 2^64"
proof -
  have "uint (a * b) = uint a * uint b mod 2 ^ LENGTH(64)"
    by (rule uint_word_ariths(3))
  also have "... = uint a * uint b mod 2^64"
    by simp
  finally show ?thesis .
qed

lemma mul64_spec: "uint (fst (mul64 a b)) * 2^64 + uint (snd (mul64 a b)) = uint a * uint b"
proof -
  have snd_eq: "snd (mul64 a b) = a * b"
    unfolding mul64_def Let_def snd_conv by (rule refl)
  have "uint (fst (mul64 a b)) * 2^64 + uint (snd (mul64 a b)) =          
        (uint a * uint b) div 2^64 * 2^64 + uint (a * b)"
    using mul64_hi_eq snd_eq by presburger
  also have "... = (uint a * uint b) div 2^64 * 2^64 + (uint a * uint b) mod 2^64"
    using uint_mul_mod64 by presburger
  also have "... = uint a * uint b"
    by presburger
  finally show ?thesis .
qed

lemma uint_shiftr63_lt2:
  "uint ((w :: u64) >> 63) < 2"
proof -
  have unat_lt: "unat (w >> 63) < 2"
  proof -
    have eq: "unat (w >> 63) = unat w div 2^63"
      by (metis drop_bit_eq_div shiftr_def unat_drop_bit_eq)
    have "unat w < 2 * 2^63"
      using unat_lt_2p64[of w] by (simp add: power_add)
    then have "unat w div 2^63 < 2"
      by (simp add: div_less_iff_less_mult)
    then show ?thesis using eq by simp
  qed
  have "unat (2 :: u64) = 2" by code_simp
  have word_lt: "(w >> 63) < (2 :: u64)"
    unfolding word_less_nat_alt
    using unat_lt `unat (2 :: u64) = 2` by simp
  have "uint (w >> 63) < uint (2 :: u64)"
    using word_lt by (simp add: word_less_alt)
  also have "uint (2 :: u64) = 2" by code_simp
  finally show ?thesis .
qed

lemma uint_not_u64:
  "uint (NOT (w :: u64)) = 2^64 - 1 - uint w"
proof -
  have "uint (NOT w) = take_bit 64 (NOT (uint w))"
    by (simp add: word_not_def uint_word_of_int_eq)

  also have "... = mask 64 - take_bit 64 (uint w)"
    by (rule take_bit_not_eq_mask_diff)

  also have "... = 2^64 - 1 - uint w"
  proof -
    have "take_bit 64 (uint w) = uint w"
      using uint_nonnegative[of w] uint_lt_2p64[of w]
      by (simp add: take_bit_int_eq_self)
    then show ?thesis
      by (simp add: mask_eq_exp_minus_1)
  qed

  finally show ?thesis .
qed

lemma div_2p63_eq_bit:
  fixes x :: int
  assumes "0 \<le> x" "x < 2^64"
  shows "x div 2^63 = (if bit x 63 then 1 else 0)"
proof -
  have div_nonneg: "0 \<le> x div 2^63"
    using assms by (simp add: pos_imp_zdiv_nonneg_iff)

  have div_lt: "x div 2^63 < 2"
  proof -
    have "x < 2 * 2^63"
      using assms by (simp add: power_add)
    then have "x \<le> 2 * 2^63 - 1" by linarith

    have "x div 2^63 \<le> (2 * 2^63 - 1) div 2^63"
      by (rule zdiv_mono1) (use `x \<le> 2 * 2^63 - 1` in auto)

    also have "... = 1"
    proof -
      have pos: "0 < (2::int)^63" by simp
      have eq: "2 * (2::int)^63 - 1 =
                (2::int)^63 + ((2::int)^63 - 1)"
        by arith
      have low_div: "((2::int)^63 - 1) div (2::int)^63 = 0"
        using pos by (simp add: zdiv_eq_0_iff)
      show "(2 * (2::int)^63 - 1) div (2::int)^63 = 1"
        using pos eq low_div by (simp add: div_add_self1)
    qed

    finally show ?thesis
      by linarith
  qed

  have y01: "x div 2^63 = 0 \<or> x div 2^63 = 1"
    using div_nonneg div_lt by linarith

  have div_eq_iff: "x div 2^63 = 1 \<longleftrightarrow> bit x 63"
  proof -
    have "bit x 63 = odd (x div 2^63)"
      by (simp add: bit_iff_odd)
    also have "odd (x div 2^63) = (x div 2^63 = 1)"
      using y01 by auto
    finally show ?thesis by simp
  qed

  show ?thesis
    using y01 div_eq_iff by auto
qed


lemma carry_bool_eq:
  fixes A B l :: int
  assumes "A = 0 \<or> A = 1"
          "B = 0 \<or> B = 1"
          "l = 0 \<or> l = 1"
  shows "((A = 1 \<and> B = 1) \<or>
          ((A = 1 \<or> B = 1) \<and> (A + B + l) mod 2 = 0)) =
         ((A + B + l) div 2 = 1)"
  using assms
  by (cases "A = 0"; cases "B = 0"; cases "l = 0") auto

lemma carry_expr_div_int_c0:
  fixes a b :: int
  assumes "0 \<le> a" "a < 2^64"
          "0 \<le> b" "b < 2^64"
  shows "(((a AND b) OR
           ((a OR b) AND
            (2^64 - 1 - (a+b) mod 2^64))) div 2^63) =
         (a + b) div 2^64"
proof -
  define M where "M = (2::int)^64"
  define T where "T = (2::int)^63"
  define r where "r = (a+b) mod M"
  define q where "q = (a+b) div M"
  define E where "E = (a AND b) OR ((a OR b) AND (M - 1 - r))"
  define A where "A = a div T"
  define B where "B = b div T"
  define al where "al = a mod T"
  define bl where "bl = b mod T"
  define l where "l = (al + bl) div T"
  define d where "d = (a + b) div T"

  have M_eq: "M = T * 2"
    unfolding M_def T_def by (simp add: power_add)

  have r_bounds: "0 \<le> r" "r < M"
    unfolding r_def M_def
    using assms by simp_all

  have and_bounds: "0 \<le> a AND b" "a AND b < M"
  proof -
    show "0 \<le> a AND b"
      using assms by simp
    show "a AND b < M"
      using assms unfolding M_def
      by (simp add: AND_upper1''[of a "2^64" b])
  qed

  have or_bounds: "0 \<le> a OR b" "a OR b < M"
  proof -
    show "0 \<le> a OR b"
      using assms by simp
    show "a OR b < M"
      unfolding M_def
      by (rule OR_upper[where x=a and y=b and n=64])
         (use assms in auto)
  qed

  have comp_bounds: "0 \<le> M - 1 - r" "M - 1 - r < M"
    using r_bounds by auto

  have other_bounds:
    "0 \<le> (a OR b) AND (M - 1 - r)"
    "(a OR b) AND (M - 1 - r) < M"
  proof -
    show "0 \<le> (a OR b) AND (M - 1 - r)"
      using or_bounds(1) by simp
    show "(a OR b) AND (M - 1 - r) < M"
      using or_bounds
      by (simp add: AND_upper1''[of "a OR b" M "M - 1 - r"])
  qed

  have E_bounds: "0 \<le> E" "E < M"
  proof -
    show "0 \<le> E"
      unfolding E_def
      using and_bounds(1) other_bounds(1)
      by simp

    have E_lt_2p64: "E < 2^64"
    proof -
      have and_nonneg: "0 \<le> a AND b"
        by (fact and_bounds(1))
      have and_lt: "a AND b < 2^64"
        using and_bounds(2) unfolding M_def by simp
      have other_lt:
        "(a OR b) AND (2^64 - 1 - r) < 2^64"
        using other_bounds(2) unfolding M_def by simp

      show ?thesis
        unfolding E_def M_def
        by (rule OR_upper[where x="a AND b"
                           and y="(a OR b) AND (2^64 - 1 - r)"
                           and n=64])
           (use and_nonneg and_lt other_lt in auto)
    qed

    show "E < M"
      using E_lt_2p64 unfolding M_def by simp
  qed

  have al_bounds: "0 \<le> al" "al < T"
  proof -
    show "0 \<le> al"
      unfolding al_def T_def by simp
    show "al < T"
      unfolding al_def T_def by simp
  qed

  have bl_bounds: "0 \<le> bl" "bl < T"
  proof -
    show "0 \<le> bl"
      unfolding bl_def T_def by simp
    show "bl < T"
      unfolding bl_def T_def by simp
  qed

  have A01: "A = 0 \<or> A = 1"
  proof -
    have "A = a div T"
      by (simp add: A_def)
    also have "... = (if bit a 63 then 1 else 0)"
      using div_2p63_eq_bit[of a] assms unfolding T_def by simp
    finally show ?thesis by auto
  qed

  have B01: "B = 0 \<or> B = 1"
  proof -
    have "B = b div T"
      by (simp add: B_def)
    also have "... = (if bit b 63 then 1 else 0)"
      using div_2p63_eq_bit[of b] assms unfolding T_def by simp
    finally show ?thesis by auto
  qed

  have sumlow_lt_M: "al + bl < M"
    using al_bounds bl_bounds unfolding M_def T_def
    by (simp add: power_add)

  have l01: "l = 0 \<or> l = 1"
  proof -
    have "l = (al + bl) div T"
      by (simp add: l_def)
    also have "... = (if bit (al + bl) 63 then 1 else 0)"
      using div_2p63_eq_bit[of "al + bl"]
            al_bounds bl_bounds sumlow_lt_M
      unfolding T_def M_def by simp
    finally show ?thesis by auto
  qed

  have a_decomp: "a = A * T + al"
    unfolding A_def al_def
    using div_mult_mod_eq[of a T] by (simp add: algebra_simps)

  have b_decomp: "b = B * T + bl"
    unfolding B_def bl_def
    using div_mult_mod_eq[of b T] by (simp add: algebra_simps)

  have d_eq: "d = A + B + l"
  proof -
    have "d = (a + b) div T"
      by (simp add: d_def)
    also have "... = (A * T + al + (B * T + bl)) div T"
      using a_decomp b_decomp by argo
    also have "... = A + B + (al + bl) div T"
    proof -
      have "(A * T + al + (B * T + bl)) div T =
            (A * T + al) div T + (B * T + bl) div T +
            ((A * T + al) mod T + (B * T + bl) mod T) div T"
        by (rule div_add1_eq[where a="A * T + al"
                              and b="B * T + bl"
                              and c=T])
      also have "... = A + B + (al + bl) div T"
        using al_bounds bl_bounds by auto
      finally show ?thesis .
    qed
    also have "... = A + B + l"
      by (simp add: l_def)
    finally show ?thesis .
  qed

  have q_eq: "q = d div 2"
  proof -
    have "q = (a + b) div M"
      by (simp add: q_def)
    also have "... = (a + b) div (T * 2)"
      using M_eq by simp
    also have "... = ((a + b) div T) div 2"
      by (rule zdiv_zmult2_eq[where a="a+b" and b="T" and c="2"]) simp
    also have "... = d div 2"
      by (simp add: d_def)
    finally show ?thesis .
  qed

  have bit_a: "bit a 63 = (A = 1)"
  proof -
    have "A = a div T"
      by (simp add: A_def)
    also have "... = (if bit a 63 then 1 else 0)"
      using div_2p63_eq_bit[of a] assms unfolding T_def by simp
    finally show ?thesis by auto
  qed

  have bit_b: "bit b 63 = (B = 1)"
  proof -
    have "B = b div T"
      by (simp add: B_def)
    also have "... = (if bit b 63 then 1 else 0)"
      using div_2p63_eq_bit[of b] assms unfolding T_def by simp
    finally show ?thesis by auto
  qed

  have bit_sum: "bit (a+b) 63 = (d mod 2 = 1)"
  proof -
    have "bit (a+b) 63 = odd ((a+b) div 2^63)"
      by (simp add: bit_iff_odd)
    also have "... = odd d"
      unfolding d_def T_def by simp
    also have "odd d = (d mod 2 = 1)"
      by presburger
    finally show ?thesis .
  qed

  have bit_r: "bit r 63 = bit (a+b) 63"
  proof -
    have "r = (a+b) mod M"
      by (simp add: r_def)
    also have "... = take_bit 64 (a+b)"
      unfolding M_def by (simp add: take_bit_eq_mod)
    finally have r_take: "r = take_bit 64 (a+b)" .
    have "bit r 63 = bit (take_bit 64 (a+b)) 63"
      using r_take by argo
    also have "... = bit (a+b) 63"
      by (simp add: bit_take_bit_iff)
    finally show ?thesis .
  qed

  have comp_eq: "M - 1 - r = take_bit 64 (NOT (a+b))"
  proof -
    have "r = take_bit 64 (a+b)"
      unfolding r_def M_def by (simp add: take_bit_eq_mod)
    then have "M - 1 - r = mask 64 - take_bit 64 (a+b)"
      unfolding M_def by (simp add: mask_eq_exp_minus_1)
    also have "... = take_bit 64 (NOT (a+b))"
      by (rule take_bit_not_eq_mask_diff[symmetric])
    finally show ?thesis .
  qed

  have bit_comp: "bit (M - 1 - r) 63 = (d mod 2 = 0)"
  proof -
    have "bit (M - 1 - r) 63 =
          bit (take_bit 64 (NOT (a+b))) 63"
      using comp_eq by argo
    also have "... = bit (NOT (a+b)) 63"
      by (simp add: bit_take_bit_iff)
    also have "... = (\<not> bit (a+b) 63)"
      by (simp add: bit_not_iff)
    also have "... = (d mod 2 = 0)"
      using bit_sum by auto
    finally show ?thesis .
  qed

  have bit_E:
    "bit E 63 =
     ((A = 1 \<and> B = 1) \<or>
      ((A = 1 \<or> B = 1) \<and> d mod 2 = 0))"
  proof -
    have "bit E 63 =
          (bit (a AND b) 63 \<or>
           (bit (a OR b) 63 \<and> bit (M - 1 - r) 63))"
      unfolding E_def by (simp add: bit_simps)
    also have "... =
          ((bit a 63 \<and> bit b 63) \<or>
           ((bit a 63 \<or> bit b 63) \<and> bit (M - 1 - r) 63))"
      by (simp add: bit_simps)
    also have "... =
          ((A = 1 \<and> B = 1) \<or>
           ((A = 1 \<or> B = 1) \<and> d mod 2 = 0))"
      using bit_a bit_b bit_comp by simp
    finally show ?thesis .
  qed

  have bool_eq:
    "((A = 1 \<and> B = 1) \<or>
      ((A = 1 \<or> B = 1) \<and> d mod 2 = 0)) =
     (q = 1)"
  proof -
    have d_split: "d = A + B + l"
      by (fact d_eq)
    have "((A = 1 \<and> B = 1) \<or>
           ((A = 1 \<or> B = 1) \<and> d mod 2 = 0)) =
          ((A = 1 \<and> B = 1) \<or>
           ((A = 1 \<or> B = 1) \<and> (A + B + l) mod 2 = 0))"
      using d_split by simp
    also have "... = ((A + B + l) div 2 = 1)"
      using A01 B01 l01 by (rule carry_bool_eq)
    also have "... = (d div 2 = 1)"
      using d_split by simp
    also have "... = (q = 1)"
      using q_eq by simp
    finally show ?thesis .
  qed

  have bit_E_q: "bit E 63 = (q = 1)"
    using bit_E bool_eq by simp

  have d01: "d div 2 = 0 \<or> d div 2 = 1"
  proof -
    have "d = A + B + l"
      by (fact d_eq)
    then show ?thesis
      using A01 B01 l01
      by (cases "A = 0"; cases "B = 0"; cases "l = 0") auto
  qed

  have E_div_eq: "E div T = q"
  proof -
    have "E div T = (if bit E 63 then 1 else 0)"
    proof -
      have "0 \<le> E" by (fact E_bounds(1))
      have "E < 2^64"
        using E_bounds(2) unfolding M_def by simp
      show ?thesis
        using div_2p63_eq_bit[of E] `0 \<le> E` `E < 2^64`
        unfolding T_def by simp
    qed
    also have "... = (if q = 1 then 1 else 0)"
      using bit_E_q by simp
    also have "... = q"
    proof -
      have "q = 0 \<or> q = 1"
        using d01 q_eq by auto
      then show ?thesis by auto
    qed
    finally show ?thesis .
  qed

  show ?thesis
    using E_div_eq[unfolded E_def r_def q_def M_def T_def]
    by simp
qed

lemma carry_expr_div_int:
  fixes a b c :: int
  assumes "0 \<le> a" "a < 2^64"
          "0 \<le> b" "b < 2^64"
          "0 \<le> c" "c < 2"
  shows "(((a AND b) OR
           ((a OR b) AND
            (2^64 - 1 - (a + b + c) mod 2^64))) div 2^63) =
         (a + b + c) div 2^64"
proof -
  have c01: "c = 0 \<or> c = 1"
    using assms by linarith

  define M where "M = (2::int)^64"
  define T where "T = (2::int)^63"
  define r where "r = (a + b + c) mod M"
  define q where "q = (a + b + c) div M"
  define E where "E = (a AND b) OR ((a OR b) AND (M - 1 - r))"
  define A where "A = a div T"
  define B where "B = b div T"
  define al where "al = a mod T"
  define bl where "bl = b mod T"
  define l where "l = (al + bl + c) div T"
  define d where "d = (a + b + c) div T"

  have pos_M: "0 < M"
    unfolding M_def by simp
  have pos_T: "0 < T"
    unfolding T_def by simp

  have M_eq: "M = T * 2"
    unfolding M_def T_def by (simp add: power_add)

  have r_bounds: "0 \<le> r" "r < M"
    unfolding r_def
    using pos_M by simp_all

  have and_bounds: "0 \<le> a AND b" "a AND b < M"
  proof -
    show "0 \<le> a AND b"
      using assms by simp
    show "a AND b < M"
      using assms unfolding M_def
      by (simp add: AND_upper1''[of a "2^64" b])
  qed

  have or_bounds: "0 \<le> a OR b" "a OR b < M"
  proof -
    show "0 \<le> a OR b"
      using assms by simp
    show "a OR b < M"
      unfolding M_def
      by (rule OR_upper[where x=a and y=b and n=64])
         (use assms in auto)
  qed

  have comp_bounds: "0 \<le> M - 1 - r" "M - 1 - r < M"
    using r_bounds by auto

  have other_bounds:
    "0 \<le> (a OR b) AND (M - 1 - r)"
    "(a OR b) AND (M - 1 - r) < M"
  proof -
    show "0 \<le> (a OR b) AND (M - 1 - r)"
      using or_bounds(1) by simp
    show "(a OR b) AND (M - 1 - r) < M"
      using or_bounds
      by (simp add: AND_upper1''[where y="a OR b"
                                 and x="M - 1 - r"
                                 and z=M])
  qed

  have E_bounds: "0 \<le> E" "E < M"
  proof -
    show "0 \<le> E"
      unfolding E_def
      using and_bounds(1) other_bounds(1)
      by simp

    have E_lt_2p64: "E < 2^64"
    proof -
      have and_nonneg: "0 \<le> a AND b"
        by (fact and_bounds(1))
      have and_lt: "a AND b < 2^64"
        using and_bounds(2) unfolding M_def by simp
      have other_lt:
        "(a OR b) AND (2^64 - 1 - r) < 2^64"
        using other_bounds(2) unfolding M_def by simp

      show ?thesis
        unfolding E_def M_def
        by (rule OR_upper[where x="a AND b"
                           and y="(a OR b) AND (2^64 - 1 - r)"
                           and n=64])
           (use and_nonneg and_lt other_lt in auto)
    qed

    show "E < M"
      using E_lt_2p64 unfolding M_def by simp
  qed

  have al_bounds: "0 \<le> al" "al < T"
    unfolding al_def
    using pos_T by simp_all

  have bl_bounds: "0 \<le> bl" "bl < T"
    unfolding bl_def
    using pos_T by simp_all

  have A01: "A = 0 \<or> A = 1"
  proof -
    have "A = a div T"
      by (simp add: A_def)
    also have "... = (if bit a 63 then 1 else 0)"
      using div_2p63_eq_bit[of a] assms unfolding T_def by simp
    finally show ?thesis by auto
  qed

  have B01: "B = 0 \<or> B = 1"
  proof -
    have "B = b div T"
      by (simp add: B_def)
    also have "... = (if bit b 63 then 1 else 0)"
      using div_2p63_eq_bit[of b] assms unfolding T_def by simp
    finally show ?thesis by auto
  qed

  have low_nonneg: "0 \<le> al + bl + c"
    using al_bounds bl_bounds assms by linarith

  have sumlow_lt_M: "al + bl + c < M"
  proof -
    have "al + bl + c \<le> (T - 1) + (T - 1) + 1"
      using al_bounds bl_bounds assms by linarith
    also have "... = 2 * T - 1"
      by linarith
    also have "... < M"
      unfolding M_def T_def by (simp add: power_add)
    finally show ?thesis .
  qed

  have l01: "l = 0 \<or> l = 1"
  proof -
    have "l = (al + bl + c) div T"
      by (simp add: l_def)
    also have "... = (if bit (al + bl + c) 63 then 1 else 0)"
      using div_2p63_eq_bit[of "al + bl + c"]
            low_nonneg sumlow_lt_M
      unfolding T_def M_def by simp
    finally show ?thesis by auto
  qed

  have a_decomp: "a = A * T + al"
    unfolding A_def al_def
    using div_mult_mod_eq[of a T] by (simp add: algebra_simps)

  have b_decomp: "b = B * T + bl"
    unfolding B_def bl_def
    using div_mult_mod_eq[of b T] by (simp add: algebra_simps)

  have d_eq: "d = A + B + l"
  proof -
    have "d = (a + b + c) div T"
      by (simp add: d_def)
    also have "... = (A * T + al + (B * T + bl) + c) div T"
      using a_decomp b_decomp by argo
    also have "... = ((al + bl + c) + (A + B) * T) div T"
      by (simp add: algebra_simps)
    also have "... = (A + B) + (al + bl + c) div T"
      using pos_T by simp
    also have "... = A + B + l"
      by (simp add: l_def)
    finally show ?thesis .
  qed

  have q_eq: "q = d div 2"
  proof -
    have "q = (a + b + c) div M"
      by (simp add: q_def)
    also have "... = (a + b + c) div (T * 2)"
      using M_eq by simp
    also have "... = ((a + b + c) div T) div 2"
      by (rule zdiv_zmult2_eq[where a="a + b + c" and b="T" and c="2"]) simp
    also have "... = d div 2"
      by (simp add: d_def)
    finally show ?thesis .
  qed

  have bit_a: "bit a 63 = (A = 1)"
  proof -
    have "A = a div T"
      by (simp add: A_def)
    also have "... = (if bit a 63 then 1 else 0)"
      using div_2p63_eq_bit[of a] assms unfolding T_def by simp
    finally show ?thesis by auto
  qed

  have bit_b: "bit b 63 = (B = 1)"
  proof -
    have "B = b div T"
      by (simp add: B_def)
    also have "... = (if bit b 63 then 1 else 0)"
      using div_2p63_eq_bit[of b] assms unfolding T_def by simp
    finally show ?thesis by auto
  qed

  have bit_sum: "bit (a + b + c) 63 = (d mod 2 = 1)"
  proof -
    have "bit (a + b + c) 63 = odd ((a + b + c) div 2^63)"
      by (simp add: bit_iff_odd)
    also have "... = odd d"
      unfolding d_def T_def by simp
    also have "odd d = (d mod 2 = 1)"
      by presburger
    finally show ?thesis .
  qed

  have bit_r: "bit r 63 = bit (a + b + c) 63"
  proof -
    have "r = (a + b + c) mod M"
      by (simp add: r_def)
    also have "... = take_bit 64 (a + b + c)"
      unfolding M_def by (simp add: take_bit_eq_mod)
    finally have r_take: "r = take_bit 64 (a + b + c)" .
    have "bit r 63 = bit (take_bit 64 (a + b + c)) 63"
      using r_take by argo
    also have "... = bit (a + b + c) 63"
      by (simp add: bit_take_bit_iff)
    finally show ?thesis .
  qed

  have comp_eq: "M - 1 - r = take_bit 64 (NOT (a + b + c))"
  proof -
    have "r = take_bit 64 (a + b + c)"
      unfolding r_def M_def by (simp add: take_bit_eq_mod)
    then have "M - 1 - r = mask 64 - take_bit 64 (a + b + c)"
      unfolding M_def by (simp add: mask_eq_exp_minus_1)
    also have "... = take_bit 64 (NOT (a + b + c))"
      by (rule take_bit_not_eq_mask_diff[symmetric])
    finally show ?thesis .
  qed

  have bit_comp: "bit (M - 1 - r) 63 = (d mod 2 = 0)"
  proof -
    have "bit (M - 1 - r) 63 =
          bit (take_bit 64 (NOT (a + b + c))) 63"
      using comp_eq by argo
    also have "... = bit (NOT (a + b + c)) 63"
      by (simp add: bit_take_bit_iff)
    also have "... = (\<not> bit (a + b + c) 63)"
      by (simp add: bit_not_iff)
    also have "... = (d mod 2 = 0)"
      using bit_sum by auto
    finally show ?thesis .
  qed

  have bit_E:
    "bit E 63 =
     ((A = 1 \<and> B = 1) \<or>
      ((A = 1 \<or> B = 1) \<and> d mod 2 = 0))"
  proof -
    have "bit E 63 =
          (bit (a AND b) 63 \<or>
           (bit (a OR b) 63 \<and> bit (M - 1 - r) 63))"
      unfolding E_def by (simp add: bit_simps)
    also have "... =
          ((bit a 63 \<and> bit b 63) \<or>
           ((bit a 63 \<or> bit b 63) \<and> bit (M - 1 - r) 63))"
      by (simp add: bit_simps)
    also have "... =
          ((A = 1 \<and> B = 1) \<or>
           ((A = 1 \<or> B = 1) \<and> d mod 2 = 0))"
      using bit_a bit_b bit_comp by simp
    finally show ?thesis .
  qed

  have bool_eq:
    "((A = 1 \<and> B = 1) \<or>
      ((A = 1 \<or> B = 1) \<and> d mod 2 = 0)) =
     (q = 1)"
  proof -
    have d_split: "d = A + B + l"
      by (fact d_eq)
    have "((A = 1 \<and> B = 1) \<or>
           ((A = 1 \<or> B = 1) \<and> d mod 2 = 0)) =
          ((A = 1 \<and> B = 1) \<or>
           ((A = 1 \<or> B = 1) \<and> (A + B + l) mod 2 = 0))"
      using d_split by simp
    also have "... = ((A + B + l) div 2 = 1)"
      using A01 B01 l01 by (rule carry_bool_eq)
    also have "... = (d div 2 = 1)"
      using d_split by simp
    also have "... = (q = 1)"
      using q_eq by simp
    finally show ?thesis .
  qed

  have bit_E_q: "bit E 63 = (q = 1)"
    using bit_E bool_eq by simp

  have d01: "d div 2 = 0 \<or> d div 2 = 1"
  proof -
    have "d = A + B + l"
      by (fact d_eq)
    then show ?thesis
      using A01 B01 l01
      by (cases "A = 0"; cases "B = 0"; cases "l = 0") auto
  qed

  have E_div_eq: "E div T = q"
  proof -
    have "E div T = (if bit E 63 then 1 else 0)"
    proof -
      have "0 \<le> E" by (fact E_bounds(1))
      have "E < 2^64"
        using E_bounds(2) unfolding M_def by simp
      show ?thesis
        using div_2p63_eq_bit[of E] `0 \<le> E` `E < 2^64`
        unfolding T_def by simp
    qed
    also have "... = (if q = 1 then 1 else 0)"
      using bit_E_q by simp
    also have "... = q"
    proof -
      have "q = 0 \<or> q = 1"
        using d01 q_eq by auto
      then show ?thesis by auto
    qed
    finally show ?thesis .
  qed

  show ?thesis
    using E_div_eq[unfolded E_def r_def q_def M_def T_def]
    by simp
qed



lemma add64_carry_spec:
  assumes "uint c < 2"
  shows "uint (fst (Add64_carry x y c)) +
         uint (snd (Add64_carry x y c)) * 2^64 =
         uint x + uint y + uint c"
proof -
  have sum_eq:
    "uint (x + y + c) = (uint x + uint y + uint c) mod 2^64"
    by (simp add: uint_word_ariths mod_add_left_eq)

  have mask_uint:
    "uint (((x AND y) OR ((x OR y) AND (NOT (x + y + c))))) =
     ((uint x AND uint y) OR
      ((uint x OR uint y) AND
       (2^64 - 1 - (uint x + uint y + uint c) mod 2^64)))"
    using uint_and uint_or uint_not_u64[of "x + y + c"] sum_eq
    by (simp add: uint_and uint_or uint_not_u64 sum_eq)

  have shift_eq:
    "uint (((x AND y) OR ((x OR y) AND (NOT (x + y + c)))) >> 63) =
     uint (((x AND y) OR ((x OR y) AND (NOT (x + y + c))))) div 2^63"
  proof -
    have "uint (((x AND y) OR ((x OR y) AND (NOT (x + y + c)))) >> 63) =
          uint (((x AND y) OR ((x OR y) AND (NOT (x + y + c)))) div (2^63 :: u64))"
      by (metis drop_bit_eq_div shiftr_def)
    also have "... =
          uint (((x AND y) OR ((x OR y) AND (NOT (x + y + c))))) div uint (2^63 :: u64)"
      by (rule uint_div)
    also have "... =
          uint (((x AND y) OR ((x OR y) AND (NOT (x + y + c))))) div 2^63"
      by (simp add: uint_2p)
    finally show ?thesis .
  qed

  have carry_eq:
    "uint (((x AND y) OR ((x OR y) AND (NOT (x + y + c)))) >> 63) =
     (uint x + uint y + uint c) div 2^64"
  proof -
    have "uint (((x AND y) OR ((x OR y) AND (NOT (x + y + c)))) >> 63) =
          uint (((x AND y) OR ((x OR y) AND (NOT (x + y + c))))) div 2^63"
      by (fact shift_eq)
    also have "... =
          (((uint x AND uint y) OR
            ((uint x OR uint y) AND
             (2^64 - 1 - (uint x + uint y + uint c) mod 2^64))) div 2^63)"
      using mask_uint by presburger
    also have "... = (uint x + uint y + uint c) div 2^64"
      using uint_nonnegative[of x] uint_lt_2p64[of x]
            uint_nonnegative[of y] uint_lt_2p64[of y]
            uint_nonnegative[of c] assms
      by (rule carry_expr_div_int[of "uint x" "uint y" "uint c"])
    finally show ?thesis .
  qed  

  show ?thesis
    unfolding Add64_carry_def Let_def fst_conv snd_conv
    using sum_eq carry_eq by presburger
qed


lemma mul64_fst_lt:
  "uint (fst (mul64 a b)) < 2^64 - 1"
proof -
  have A_le: "uint a <= 2^64 - 1"
    using uint_lt_2p64[of a] by presburger
  have B_le: "uint b <= 2^64 - 1"
    using uint_lt_2p64[of b] by presburger
  have prod_le: "uint a * uint b <= (2^64 - 1) * (2^64 - 1)"
    by (rule mult_mono') (use A_le B_le uint_nonnegative in auto)
  have div_le: "(uint a * uint b) div 2^64 <=
                ((2^64 - 1) * (2^64 - 1)) div 2^64"
    using prod_le pos_2p64 by (rule zdiv_mono1)
  have bound_eq:
    "(((2::int)^64 - 1) * ((2::int)^64 - 1)) div (2::int)^64 =
     (2::int)^64 - 2"
    by code_simp
  have "uint (fst (mul64 a b)) <= 2^64 - 2"
    using mul64_hi_eq[of a b] div_le bound_eq by presburger
  then show ?thesis
    by presburger
qed

lemma add64_carry_c0:
  "uint (fst (Add64_carry x y 0)) +
   uint (snd (Add64_carry x y 0)) * 2^64 =
   uint x + uint y"
proof -
  have sum_eq:
    "uint (x + y + 0) = (uint x + uint y + uint 0) mod 2^64"
    by (simp add: uint_word_ariths mod_add_left_eq)

  have mask_uint:
    "uint (((x AND y) OR ((x OR y) AND (NOT (x + y + 0))))) =
     ((uint x AND uint y) OR
      ((uint x OR uint y) AND
       (2^64 - 1 - (uint x + uint y + uint 0) mod 2^64)))"
    using uint_and uint_or uint_not_u64[of "x + y + 0"] sum_eq
    by (simp add: uint_and uint_or uint_not_u64 sum_eq)

  have shift_eq:
    "uint (((x AND y) OR ((x OR y) AND (NOT (x + y + 0)))) >> 63) =
     uint (((x AND y) OR ((x OR y) AND (NOT (x + y + 0))))) div 2^63"
  proof -
    have "uint (((x AND y) OR ((x OR y) AND (NOT (x + y + 0)))) >> 63) =
          uint (((x AND y) OR ((x OR y) AND (NOT (x + y + 0)))) div (2^63 :: u64))"
      by (metis drop_bit_eq_div shiftr_def)
    also have "... =
          uint (((x AND y) OR ((x OR y) AND (NOT (x + y + 0))))) div uint (2^63 :: u64)"
      by (rule uint_div)
    also have "... =
          uint (((x AND y) OR ((x OR y) AND (NOT (x + y + 0))))) div 2^63"
      by (simp add: uint_2p)
    finally show ?thesis .
  qed

  have carry_eq:
    "uint (((x AND y) OR ((x OR y) AND (NOT (x + y + 0)))) >> 63) =
     (uint x + uint y) div 2^64"
  proof -
    have "uint (((x AND y) OR ((x OR y) AND (NOT (x + y + 0)))) >> 63) =
          uint (((x AND y) OR ((x OR y) AND (NOT (x + y + 0))))) div 2^63"
      by (fact shift_eq)
    also have "... =
          (((uint x AND uint y) OR
            ((uint x OR uint y) AND
             (2^64 - 1 - (uint x + uint y) mod 2^64))) div 2^63)"
      using mask_uint by simp
    also have "... = (uint x + uint y) div 2^64"
      using uint_nonnegative[of x] uint_lt_2p64[of x]
            uint_nonnegative[of y] uint_lt_2p64[of y]
      by (rule carry_expr_div_int_c0
            [where a = "uint x" and b = "uint y"])
    finally show ?thesis .
  qed

    show ?thesis
    unfolding Add64_carry_def Let_def fst_conv snd_conv
    using sum_eq carry_eq
    by (simp add: mod_div_mult_eq[of "uint x + uint y" "2^64"])
qed 

lemma add64_carry_y0:
  assumes "uint c < 2"
  shows "uint (fst (Add64_carry x 0 c)) +
         uint (snd (Add64_carry x 0 c)) * 2^64 =
         uint x + uint c"
  using assms add64_carry_spec[of c x "0::u64"]
  by simp


lemma add64_carry_snd_lt:
  "uint (snd (Add64_carry x y c)) < 2"
proof -
  have "snd (Add64_carry x y c) =
        (((x AND y) OR ((x OR y) AND (NOT (x + y + c)))) >> 63)"
    unfolding Add64_carry_def Let_def snd_conv by (rule refl)
  then show ?thesis
    using uint_shiftr63_lt2[of "((x AND y) OR ((x OR y) AND (NOT (x + y + c))))"]
    by presburger
qed


lemma mul64_decomp: "mul64 a b = (fst (mul64 a b), snd (mul64 a b))"
  by (rule surjective_pairing)

lemma add64_carry_decomp: "Add64_carry x y c = (fst (Add64_carry x y c), snd (Add64_carry x y c))"
  by (rule surjective_pairing)

lemma umulHop_decomp: "umulHop c a b = (fst (umulHop c a b), snd (umulHop c a b))"
  by (rule surjective_pairing)

lemma umulHop_expand:
  assumes "mul64 a b = (hi, lo)" "Add64_carry lo c 0 = (lo', carry)" "Add64_carry hi 0 carry = (hi', u)"
  shows "umulHop c a b = (hi', lo')"
proof -
  have "umulHop c a b = (case mul64 a b of (hi, lo) \<Rightarrow>
                          case Add64_carry lo c 0 of (lo, carry) \<Rightarrow>
                          case Add64_carry hi 0 carry of (hi, _) \<Rightarrow> (hi, lo))"
    unfolding umulHop_def Let_def by (rule refl)
  also have "... = (case Add64_carry lo c 0 of (lo, carry) \<Rightarrow>
                     case Add64_carry hi 0 carry of (hi, _) \<Rightarrow> (hi, lo))"
    using assms(1) by (simp only: prod.case)
  also have "... = (case Add64_carry hi 0 carry of (hi, _) \<Rightarrow> (hi, lo'))"
    using assms(2) by (simp only: prod.case)
  also have "... = (hi', lo')"
    using assms(3) by (simp only: prod.case)
  finally show ?thesis .
qed           

lemma umulHop_spec: "uint (fst (umulHop c a b)) * 2^64 + uint (snd (umulHop c a b)) = uint a * uint b + uint c"
proof -
  define hi where "hi = fst (mul64 a b)"
  define lo where "lo = snd (mul64 a b)"
  define lo' where "lo' = fst (Add64_carry lo c 0)"
  define carry where "carry = snd (Add64_carry lo c 0)"
  define hi' where "hi' = fst (Add64_carry hi 0 carry)"
  define u where "u = snd (Add64_carry hi 0 carry)"
  have pair1: "mul64 a b = (hi, lo)"
    unfolding hi_def lo_def using mul64_decomp by presburger
  have pair2: "Add64_carry lo c 0 = (lo', carry)"
    unfolding lo'_def carry_def using add64_carry_decomp by presburger
  have pair3: "Add64_carry hi 0 carry = (hi', u)"
    unfolding hi'_def u_def using add64_carry_decomp by presburger
  have umulHop_eq: "umulHop c a b = (hi', lo')"
    using pair1 pair2 pair3 by (rule umulHop_expand)
  have fst_eq: "fst (umulHop c a b) = hi'" using umulHop_eq by (metis fst_conv)
  have snd_eq: "snd (umulHop c a b) = lo'" using umulHop_eq by (metis snd_conv)
  have mul64_fact: "uint hi * 2^64 + uint lo = uint a * uint b"
    using mul64_spec[of a b] unfolding hi_def lo_def fst_conv snd_conv by presburger
  have add1_fact: "uint lo' + uint carry * 2^64 = uint lo + uint c"
    using add64_carry_c0[of lo c] unfolding lo'_def carry_def fst_conv snd_conv by presburger
     have carry_bound: "uint carry < 2"
       using add64_carry_snd_lt[of lo c 0] unfolding carry_def snd_conv by presburger
     have add2_full: "uint hi' + uint u * 2^64 = uint hi + uint carry"
       using carry_bound add64_carry_y0[of carry hi] unfolding hi'_def u_def fst_conv snd_conv by presburger
  have hi_lt: "uint hi < 2^64 - 1"
    using mul64_fst_lt[of a b] unfolding hi_def fst_conv by presburger
  have u_bound: "uint u < 2"
    using add64_carry_snd_lt[of hi 0 carry] unfolding u_def snd_conv by presburger
  have add2_u_zero: "uint u = 0"
  proof (rule ccontr)
    assume "uint u \<noteq> 0"
    with u_bound uint_nonnegative[of u] have "uint u = 1" by presburger
    then have "uint hi' + 2^64 = uint hi + uint carry" using add2_full by presburger
    also have "... < 2^64" using hi_lt carry_bound by presburger
    finally show False using uint_nonnegative[of hi'] by presburger
  qed
  have add2_fact: "uint hi' = uint hi + uint carry"
    using add2_full add2_u_zero by presburger
  have algebra: "uint hi' * 2^64 + uint lo' = uint a * uint b + uint c"
  proof -
    have "uint hi' * 2^64 + uint lo' = (uint hi + uint carry) * 2^64 + uint lo'"
      using add2_fact by presburger
    also have "... = uint hi * 2^64 + (uint carry * 2^64 + uint lo')"
      by (simp only: ring_distribs)
    also have "... = uint hi * 2^64 + (uint lo + uint c)"
      using add1_fact by (metis add.commute)
    also have "... = uint a * uint b + uint c"
      using mul64_fact by presburger
    finally show ?thesis .
  qed
  show ?thesis
    unfolding fst_eq snd_eq
    using algebra .
qed

lemma umulStep_expand:
  assumes
    "mul64 a b = (hi, lo)"
    "Add64_carry lo c 0 = (lo1, carry1)"
    "Add64_carry hi 0 carry1 = (hi1, carry2)"
    "Add64_carry lo1 d 0 = (lo2, carry3)"
    "Add64_carry hi1 0 carry3 = (hi2, u)"
  shows "umulStep d a b c = (hi2, lo2)"
proof -
  have "umulStep d a b c =
        (case mul64 a b of (hi, lo) \<Rightarrow>
          case Add64_carry lo c 0 of (lo, carry1) \<Rightarrow>
          case Add64_carry hi 0 carry1 of (hi, carry2) \<Rightarrow>
          case Add64_carry lo d 0 of (lo, carry3) \<Rightarrow>
          case Add64_carry hi 0 carry3 of (hi, _) \<Rightarrow> (hi, lo))"
    unfolding umulStep_def Let_def by (rule refl)
  also have "... = (case Add64_carry lo c 0 of (lo, carry1) \<Rightarrow>
                     case Add64_carry hi 0 carry1 of (hi, carry2) \<Rightarrow>
                     case Add64_carry lo d 0 of (lo, carry3) \<Rightarrow>
                     case Add64_carry hi 0 carry3 of (hi, _) \<Rightarrow> (hi, lo))"
    using assms(1) by (simp only: prod.case)
  also have "... = (case Add64_carry hi 0 carry1 of (hi, carry2) \<Rightarrow>
                     case Add64_carry lo1 d 0 of (lo, carry3) \<Rightarrow>
                     case Add64_carry hi 0 carry3 of (hi, _) \<Rightarrow> (hi, lo))"
    using assms(2) by (simp only: prod.case)
  also have "... = (case Add64_carry lo1 d 0 of (lo, carry3) \<Rightarrow>
                     case Add64_carry hi1 0 carry3 of (hi, _) \<Rightarrow> (hi, lo))"
    using assms(3) by (simp only: prod.case)
  also have "... = (case Add64_carry hi1 0 carry3 of (hi, _) \<Rightarrow> (hi, lo2))"
    using assms(4) by (simp only: prod.case)
  also have "... = (hi2, lo2)"
    using assms(5) by (simp only: prod.case)
  finally show ?thesis .
qed



lemma umulStep_spec_mod:
  shows "uint (fst (umulStep d a b c)) * 2^64 + uint (snd (umulStep d a b c)) =
         (uint a * uint b + uint d + uint c) mod 2^128"
proof -
  define hi where "hi = fst (mul64 a b)"
  define lo where "lo = snd (mul64 a b)"
  define lo1 where "lo1 = fst (Add64_carry lo c 0)"
  define carry1 where "carry1 = snd (Add64_carry lo c 0)"
  define hi1 where "hi1 = fst (Add64_carry hi 0 carry1)"
  define carry2 where "carry2 = snd (Add64_carry hi 0 carry1)"
  define lo2 where "lo2 = fst (Add64_carry lo1 d 0)"
  define carry3 where "carry3 = snd (Add64_carry lo1 d 0)"
  define hi2 where "hi2 = fst (Add64_carry hi1 0 carry3)"
  define u where "u = snd (Add64_carry hi1 0 carry3)"

  have pair1: "mul64 a b = (hi, lo)"
    unfolding hi_def lo_def using mul64_decomp by presburger
  have pair2: "Add64_carry lo c 0 = (lo1, carry1)"
    unfolding lo1_def carry1_def using add64_carry_decomp by presburger
  have pair3: "Add64_carry hi 0 carry1 = (hi1, carry2)"
    unfolding hi1_def carry2_def using add64_carry_decomp by presburger
  have pair4: "Add64_carry lo1 d 0 = (lo2, carry3)"
    unfolding lo2_def carry3_def using add64_carry_decomp by presburger
  have pair5: "Add64_carry hi1 0 carry3 = (hi2, u)"
    unfolding hi2_def u_def using add64_carry_decomp by presburger

  have umulStep_eq: "umulStep d a b c = (hi2, lo2)"
    using pair1 pair2 pair3 pair4 pair5 by (rule umulStep_expand)
  have fst_eq: "fst (umulStep d a b c) = hi2"
    using umulStep_eq by (metis fst_conv)
  have snd_eq: "snd (umulStep d a b c) = lo2"
    using umulStep_eq by (metis snd_conv)

  have mul64_fact: "uint hi * 2^64 + uint lo = uint a * uint b"
    using mul64_spec[of a b] unfolding hi_def lo_def fst_conv snd_conv by presburger
  have add1_fact: "uint lo1 + uint carry1 * 2^64 = uint lo + uint c"
    using add64_carry_c0[of lo c] unfolding lo1_def carry1_def fst_conv snd_conv by presburger

  have carry1_lt: "uint carry1 < 2"
    using add64_carry_snd_lt[of lo c 0] unfolding carry1_def snd_conv by presburger

  have add2_fact: "uint hi1 + uint carry2 * 2^64 = uint hi + uint carry1"
    using carry1_lt add64_carry_y0[of carry1 hi] unfolding hi1_def carry2_def fst_conv snd_conv by presburger

  have add3_fact: "uint lo2 + uint carry3 * 2^64 = uint lo1 + uint d"
    using add64_carry_c0[of lo1 d] unfolding lo2_def carry3_def fst_conv snd_conv by presburger

  have carry3_lt: "uint carry3 < 2"
    using add64_carry_snd_lt[of lo1 d 0] unfolding carry3_def snd_conv by presburger

  have add4_fact: "uint hi2 + uint u * 2^64 = uint hi1 + uint carry3"
    using carry3_lt add64_carry_y0[of carry3 hi1] unfolding hi2_def u_def fst_conv snd_conv by presburger
 
  have algebra:
    "uint hi2 * 2^64 + uint lo2 =
     uint a * uint b + uint d + uint c - (uint carry2 + uint u) * 2^128"
  proof -
    have hi2_eq: "uint hi2 = uint hi1 + uint carry3 - uint u * 2^64"
      using add4_fact by linarith
    have lo2_eq: "uint lo2 = uint lo1 + uint d - uint carry3 * 2^64"
      using add3_fact by linarith
    have hi1_eq: "uint hi1 = uint hi + uint carry1 - uint carry2 * 2^64"
      using add2_fact by linarith
    have lo1_eq: "uint lo1 = uint lo + uint c - uint carry1 * 2^64"
      using add1_fact by linarith

    have "uint hi2 * 2^64 + uint lo2 =
          (uint hi1 + uint carry3 - uint u * 2^64) * 2^64 +
          (uint lo1 + uint d - uint carry3 * 2^64)"
      by (simp add: hi2_eq lo2_eq)
    also have "... = uint hi1 * 2^64 + uint lo1 + uint d - uint u * 2^128"
      by (simp add: algebra_simps power_add)
    also have "... = (uint hi + uint carry1 - uint carry2 * 2^64) * 2^64 +
                      uint lo + uint c - uint carry1 * 2^64 + uint d - uint u * 2^128"
      by (simp add: hi1_eq lo1_eq)
    also have "... = uint hi * 2^64 + uint lo + uint d + uint c -
                      (uint carry2 + uint u) * 2^128"
      by (simp add: algebra_simps power_add)
    also have "... = uint a * uint b + uint d + uint c -
                      (uint carry2 + uint u) * 2^128"
      using mul64_fact by argo
    finally show ?thesis .
  qed

  have lhs_lt:
    "uint hi2 * 2^64 + uint lo2 < 2^128"
  proof -
    have hi2_le: "uint hi2 <= 2^64 - 1"
      using uint_lt_2p64[of hi2] by presburger
    have lo2_le: "uint lo2 <= 2^64 - 1"
      using uint_lt_2p64[of lo2] by presburger

    have two_nonneg: "0 <= (2::int)^64"
      using pos_2p64 by (rule less_imp_le)

    have hi2_scaled: "uint hi2 * 2^64 <= (2^64 - 1) * 2^64"
      using hi2_le two_nonneg by (meson mult_right_mono)

    have sum_le:
      "uint hi2 * 2^64 + uint lo2 <=
       (2^64 - 1) * 2^64 + (2^64 - 1)"
      using hi2_scaled lo2_le by (meson add_mono)

    have bound_eq:
      "((2::int)^64 - 1) * (2::int)^64 + ((2::int)^64 - 1) =
       (2::int)^128 - 1"
      by code_simp

    then show ?thesis
      using sum_le by linarith
  qed

  have lhs_nonneg: "0 <= uint hi2 * 2^64 + uint lo2"
    by simp

  have lhs_mod_self:
    "uint hi2 * 2^64 + uint lo2 =
     (uint hi2 * 2^64 + uint lo2) mod 2^128"
    using lhs_lt lhs_nonneg by simp

  have rhs_mod_eq:
    "(uint hi2 * 2^64 + uint lo2) mod 2^128 =
     (uint a * uint b + uint d + uint c) mod 2^128"
  proof -
    have K_mod:
      "((uint carry2 + uint u) * 2^128) mod 2^128 = 0"
      by simp

    have "uint hi2 * 2^64 + uint lo2 =
          (uint a * uint b + uint d + uint c) -
          (uint carry2 + uint u) * 2^128"
      by (fact algebra)

    then have "(uint hi2 * 2^64 + uint lo2) mod 2^128 =
               ((uint a * uint b + uint d + uint c) -
                (uint carry2 + uint u) * 2^128) mod 2^128"
      by presburger

    also have "... =
      ((uint a * uint b + uint d + uint c) mod 2^128 -
       ((uint carry2 + uint u) * 2^128) mod 2^128) mod 2^128"
      by (rule mod_diff_eq[symmetric])

    also have "... = (uint a * uint b + uint d + uint c) mod 2^128"
      using K_mod by simp

    finally show ?thesis .
  qed

  show ?thesis
    unfolding fst_eq snd_eq
    using lhs_mod_self rhs_mod_eq by presburger
qed

lemma uint256_mul_expand:
  assumes
    "z0 x = x0" "z1 x = x1" "z2 x = x2" "z3 x = x3"
    "z0 y = y0" "z1 y = y1" "z2 y = y2" "z3 y = y3"
    "mul64 x0 y0 = (carry0, z0')"
    "umulHop carry0 x1 y0 = (carry0_mid, res1)"
    "umulHop carry0_mid x2 y0 = (carry0_final, res2)"
    "umulHop res1 x0 y1 = (carry1, z1')"
    "umulStep res2 x1 y1 carry1 = (carry1_new, res2')"
    "umulHop res2' x0 y2 = (carry2, z2')"
    "z3' = x3*y0 + x2*y1 + x0*y3 + x1*y2 + carry0_final + carry1_new + carry2"
  shows "x *\<^sub>u y = \<lparr>z0=z0', z1=z1', z2=z2', z3=z3'\<rparr>"
  unfolding uint256_mul_def Let_def
  using assms
  by (simp only: prod.case)

lemma uint256_mul_mod:
  "uint256_to_int (x *\<^sub>u y) = (uint256_to_int x * uint256_to_int y) mod 2^256"
proof -
  obtain x0 x1 x2 x3 where x_eq: "x = \<lparr>z0=x0,z1=x1,z2=x2,z3=x3\<rparr>"
    by (cases x) auto
  obtain y0 y1 y2 y3 where y_eq: "y = \<lparr>z0=y0,z1=y1,z2=y2,z3=y3\<rparr>"
    by (cases y) auto

  define z00 where "z00 = snd (mul64 x0 y0)"
  define c00 where "c00 = fst (mul64 x0 y0)"
  define r10 where "r10 = snd (umulHop c00 x1 y0)"
  define c10 where "c10 = fst (umulHop c00 x1 y0)"
  define r20 where "r20 = snd (umulHop c10 x2 y0)"
  define c20 where "c20 = fst (umulHop c10 x2 y0)"
  define z1 where "z1 = snd (umulHop r10 x0 y1)"
  define c01 where "c01 = fst (umulHop r10 x0 y1)"
  define r21 where "r21 = snd (umulStep r20 x1 y1 c01)"
  define c11 where "c11 = fst (umulStep r20 x1 y1 c01)"
  define z2 where "z2 = snd (umulHop r21 x0 y2)"
  define c02 where "c02 = fst (umulHop r21 x0 y2)"
  define z3 where "z3 = x3*y0 + x2*y1 + x0*y3 + x1*y2 + c20 + c11 + c02"

  have p0: "mul64 x0 y0 = (c00, z00)"
    unfolding c00_def z00_def using mul64_decomp by presburger
  have p1: "umulHop c00 x1 y0 = (c10, r10)"
    unfolding c10_def r10_def using umulHop_decomp by presburger
  have p2: "umulHop c10 x2 y0 = (c20, r20)"
    unfolding c20_def r20_def using umulHop_decomp by presburger
  have p3: "umulHop r10 x0 y1 = (c01, z1)"
    unfolding c01_def z1_def using umulHop_decomp by presburger
  have p4: "umulStep r20 x1 y1 c01 = (c11, r21)"
    unfolding c11_def r21_def by (metis surjective_pairing)
  have p5: "umulHop r21 x0 y2 = (c02, z2)"
    unfolding c02_def z2_def using umulHop_decomp by presburger

  have result_eq:
    "x *\<^sub>u y = \<lparr>z0=z00,z1=z1,z2=z2,z3=z3\<rparr>"
    by (rule uint256_mul_expand)
       (auto simp: x_eq y_eq p0 p1 p2 p3 p4 p5 z3_def)

  define X0 where "X0 = uint x0"
  define X1 where "X1 = uint x1"
  define X2 where "X2 = uint x2"
  define X3 where "X3 = uint x3"
  define Y0 where "Y0 = uint y0"
  define Y1 where "Y1 = uint y1"
  define Y2 where "Y2 = uint y2"
  define Y3 where "Y3 = uint y3"

  have m00: "uint c00 * 2^64 + uint z00 = X0 * Y0"
    using mul64_spec[of x0 y0]
    unfolding c00_def z00_def fst_conv snd_conv X0_def Y0_def by simp
  have m10: "uint c10 * 2^64 + uint r10 = X1 * Y0 + uint c00"
    using umulHop_spec[of c00 x1 y0]
    unfolding c10_def r10_def fst_conv snd_conv X1_def Y0_def by simp
  have m20: "uint c20 * 2^64 + uint r20 = X2 * Y0 + uint c10"
    using umulHop_spec[of c10 x2 y0]
    unfolding c20_def r20_def fst_conv snd_conv X2_def Y0_def by simp
  have m01: "uint c01 * 2^64 + uint z1 = X0 * Y1 + uint r10"
    using umulHop_spec[of r10 x0 y1]
    unfolding c01_def z1_def fst_conv snd_conv X0_def Y1_def by simp
  have m11: "uint c11 * 2^64 + uint r21 =
             (X1 * Y1 + uint r20 + uint c01) mod 2^128"
    using umulStep_spec_mod[of r20 x1 y1 c01]
    unfolding c11_def r21_def fst_conv snd_conv X1_def Y1_def by simp
  have m02: "uint c02 * 2^64 + uint z2 = X0 * Y2 + uint r21"
    using umulHop_spec[of r21 x0 y2]
    unfolding c02_def z2_def fst_conv snd_conv X0_def Y2_def by simp

  have mod_sum_cong:
    "((a::int) + b mod m + c mod m + d mod m + f + g + h) mod m =
     (a mod m + b mod m + c mod m + d mod m + f + g + h) mod m"
    for a b c d f g h m :: int
  proof -
    have diff:
      "((a + b mod m + c mod m + d mod m + f + g + h) -
        (a mod m + b mod m + c mod m + d mod m + f + g + h)) =
       a - a mod m"
      by arith
    have "m dvd (a - a mod m)"
      by simp
    with diff show ?thesis
      by (simp add: mod_eq_dvd_iff)
  qed

  have z3_uint:
    "uint z3 = (X3 * Y0 + X2 * Y1 + X0 * Y3 + X1 * Y2 +
                uint c20 + uint c11 + uint c02) mod 2^64"
  proof -
    have uint_sum_list:
      "uint (sum_list xs) = (sum_list (map uint xs)) mod 2^64"
      for xs :: "u64 list"
    proof (induct xs)
      case Nil
      then show ?case by simp
    next
      case (Cons x xs)
      have "uint (sum_list (x # xs)) = uint (x + sum_list xs)"
        by simp
      also have "... = (uint x + uint (sum_list xs)) mod 2^64"
        by (simp add: uint_word_ariths)
      also have "... = (uint x + (sum_list (map uint xs)) mod 2^64) mod 2^64"
        using Cons by presburger
      also have "... = (uint x + sum_list (map uint xs)) mod 2^64"
        by (simp add: mod_add_right_eq)
      also have "... = sum_list (map uint (x # xs)) mod 2^64"
        by simp
      finally show ?case .
    qed

    have step1:
      "uint z3 =
       (uint (x3 * y0) + uint (x2 * y1) + uint (x0 * y3) +
        uint (x1 * y2) + uint c20 + uint c11 + uint c02) mod 2^64"
    proof -
      have z3_sum:
        "z3 = sum_list [x3*y0, x2*y1, x0*y3, x1*y2, c20, c11, c02]"
        unfolding z3_def by (simp add: ac_simps)

      have "uint z3 =
            uint (sum_list [x3*y0, x2*y1, x0*y3, x1*y2, c20, c11, c02])"
        using z3_sum by presburger
      also have "... =
            sum_list (map uint [x3*y0, x2*y1, x0*y3, x1*y2, c20, c11, c02]) mod 2^64"
        by (rule uint_sum_list)
      also have "... =
            (uint (x3*y0) + uint (x2*y1) + uint (x0*y3) +
             uint (x1*y2) + uint c20 + uint c11 + uint c02) mod 2^64"
        by (simp add: ac_simps)
      finally show ?thesis .
    qed

    have step2':
      "(uint (x3 * y0) + uint (x2 * y1) + uint (x0 * y3) +
        uint (x1 * y2) + uint c20 + uint c11 + uint c02) mod 2^64 =
       (uint x3 * uint y0 + uint x2 * uint y1 +
        uint x0 * uint y3 + uint x1 * uint y2 +
        uint c20 + uint c11 + uint c02) mod 2^64"
      by (intro mod_add_cong) (simp_all add: uint_mul_mod64)

    show ?thesis
      using step1 step2'
      unfolding X0_def X1_def X2_def X3_def Y0_def Y1_def Y2_def Y3_def
      by (simp add: ac_simps)

  qed

  have algebra:
    "uint z00 + uint z1 * 2^64 + uint z2 * 2^128 + uint z3 * 2^192 =
     (X0 + X1 * 2^64 + X2 * 2^128 + X3 * 2^192) *
     (Y0 + Y1 * 2^64 + Y2 * 2^128 + Y3 * 2^192) mod 2^256"
  proof -
    define q2 where
      "q2 = (X1 * Y1 + uint r20 + uint c01) div 2^128"
    define q3 where
      "q3 = (X3 * Y0 + X2 * Y1 + X0 * Y3 + X1 * Y2 +
             uint c20 + uint c11 + uint c02) div 2^64"
    define Q where
      "Q = X0*Y0 + (X0*Y1 + X1*Y0) * 2^64 +
           (X0*Y2 + X1*Y1 + X2*Y0) * 2^128 +
           (X0*Y3 + X1*Y2 + X2*Y1 + X3*Y0) * 2^192"

    have f5_exact:
      "uint c11 * 2^64 + uint r21 =
       X1 * Y1 + uint r20 + uint c01 - q2 * 2^128"
      using m11 unfolding q2_def
      by (simp add: div_mult_mod_eq algebra_simps)

    have z3_exact:
      "uint z3 =
       X3 * Y0 + X2 * Y1 + X0 * Y3 + X1 * Y2 +
       uint c20 + uint c11 + uint c02 - q3 * 2^64"
      using z3_uint unfolding q3_def
      by (simp add: div_mult_mod_eq algebra_simps)

    have S_eq:
      "uint z00 + uint z1 * 2^64 + uint z2 * 2^128 + uint z3 * 2^192 =
       Q - (q2 + q3) * 2^256"
    proof -
      have e00: "uint z00 = X0*Y0 - uint c00 * 2^64"
        using m00 by simp
      have e01: "uint z1 * 2^64 =
                 X0*Y1*2^64 + uint r10*2^64 - uint c01*2^128"
        using m01 by simp
      have e02: "uint z2 * 2^128 =
                 X0*Y2*2^128 + uint r21*2^128 - uint c02*2^192"
        using m02 by simp
      have e03: "uint z3 * 2^192 =
                 (X3*Y0 + X2*Y1 + X0*Y3 + X1*Y2 +
                  uint c20 + uint c11 + uint c02) * 2^192 -
                 q3 * 2^256"
        using z3_exact by simp

      have stepA:
        "uint z00 + uint z1 * 2^64 + uint z2 * 2^128 + uint z3 * 2^192 =
         X0*Y0 + X0*Y1*2^64 + X0*Y2*2^128 + X0*Y3*2^192 +
         uint r10*2^64 + uint r21*2^128 -
         uint c00*2^64 - uint c01*2^128 +
         (X3*Y0 + X2*Y1 + X1*Y2)*2^192 +
         (uint c20 + uint c11)*2^192 -
         q3*2^256"
      proof -
        show ?thesis
          using e00 e01 e02 e03
          by (simp add: algebra_simps power_add)
      qed

      have b10:
        "uint r10 * 2^64 - uint c00 * 2^64 =
         X1*Y0 * 2^64 - uint c10 * 2^128"
        using m10 by simp

      have b11:
        "uint r21 * 2^128 + uint c11 * 2^192 - uint c01 * 2^128 =
         X1*Y1 * 2^128 + uint r20 * 2^128 - q2 * 2^256"
        using f5_exact by simp

      have b20:
        "uint r20 * 2^128 - uint c10 * 2^128 + uint c20 * 2^192 =
         X2*Y0 * 2^128"
        using m20 by simp

      have stepB:
        "X0*Y0 + X0*Y1*2^64 + X0*Y2*2^128 + X0*Y3*2^192 +
         uint r10*2^64 + uint r21*2^128 -
         uint c00*2^64 - uint c01*2^128 +
         (X3*Y0 + X2*Y1 + X1*Y2)*2^192 +
         (uint c20 + uint c11)*2^192 -
         q3*2^256 =
         Q - (q2 + q3) * 2^256"
      proof -
        show ?thesis
          using b10 b11 b20
          unfolding Q_def
          by (simp add: algebra_simps power_add)
      qed

      show ?thesis
        using stepA stepB by presburger
    qed

    have P_decomp:
      "(X0 + X1 * 2^64 + X2 * 2^128 + X3 * 2^192) *
       (Y0 + Y1 * 2^64 + Y2 * 2^128 + Y3 * 2^192) =
       Q + 2^256 *
         ((X1*Y3 + X2*Y2 + X3*Y1) +
          (X2*Y3 + X3*Y2) * 2^64 +
          X3*Y3 * 2^128)"
      unfolding Q_def
      by (simp add: algebra_simps power_add)

    have S_mod_eq:
      "(uint z00 + uint z1 * 2^64 + uint z2 * 2^128 + uint z3 * 2^192) mod 2^256 =
       Q mod 2^256"
    proof -
      have "uint z00 + uint z1 * 2^64 + uint z2 * 2^128 + uint z3 * 2^192 =
            Q - (q2 + q3) * 2^256"
        by (fact S_eq)
      then have
        "(uint z00 + uint z1 * 2^64 + uint z2 * 2^128 + uint z3 * 2^192) mod 2^256 =
         (Q - (q2 + q3) * 2^256) mod 2^256"
        by presburger
      also have "... =
        (Q mod 2^256 - ((q2 + q3) * 2^256) mod 2^256) mod 2^256"
        by (rule mod_diff_eq[symmetric])
      also have "... = Q mod 2^256"
        by simp
      finally show ?thesis .
    qed

    have P_mod_eq:
      "(X0 + X1 * 2^64 + X2 * 2^128 + X3 * 2^192) *
       (Y0 + Y1 * 2^64 + Y2 * 2^128 + Y3 * 2^192) mod 2^256 =
       Q mod 2^256"
    proof -
      have "((X0 + X1 * 2^64 + X2 * 2^128 + X3 * 2^192) *
             (Y0 + Y1 * 2^64 + Y2 * 2^128 + Y3 * 2^192)) =
            Q + 2^256 *
              ((X1*Y3 + X2*Y2 + X3*Y1) +
               (X2*Y3 + X3*Y2) * 2^64 +
               X3*Y3 * 2^128)"
        by (fact P_decomp)
      then have
        "((X0 + X1 * 2^64 + X2 * 2^128 + X3 * 2^192) *
          (Y0 + Y1 * 2^64 + Y2 * 2^128 + Y3 * 2^192)) mod 2^256 =
         (Q + 2^256 *
           ((X1*Y3 + X2*Y2 + X3*Y1) +
            (X2*Y3 + X3*Y2) * 2^64 +
            X3*Y3 * 2^128)) mod 2^256"
        by presburger
      also have "... = Q mod 2^256"
        by (metis mod_mult_self1 mult.commute)                                       
        finally show ?thesis .
    qed

    have result_val:
      "uint z00 + uint z1 * 2^64 + uint z2 * 2^128 + uint z3 * 2^192 =
       uint256_to_int (x *\<^sub>u y)"
      unfolding result_eq uint256_to_int_def
      by (simp add: Let_def int_shiftl_eq_mult)

    have S_ge:
      "0 \<le> uint z00 + uint z1 * 2^64 + uint z2 * 2^128 + uint z3 * 2^192"
      using uint256_to_int_nonneg[of "x *\<^sub>u y"] result_val by presburger

    have S_lt:
      "uint z00 + uint z1 * 2^64 + uint z2 * 2^128 + uint z3 * 2^192 < 2^256"
      using uint256_to_int_bound[of "x *\<^sub>u y"] result_val by presburger

    have S_self:
      "uint z00 + uint z1 * 2^64 + uint z2 * 2^128 + uint z3 * 2^192 =
       (uint z00 + uint z1 * 2^64 + uint z2 * 2^128 + uint z3 * 2^192) mod 2^256"
      using S_ge S_lt by simp

    show ?thesis
      using S_self S_mod_eq P_mod_eq by presburger
  qed

  have A_eq: "uint256_to_int x =
              X0 + X1 * 2^64 + X2 * 2^128 + X3 * 2^192"
    unfolding x_eq uint256_to_int_def
    by (simp add: Let_def int_shiftl_eq_mult X0_def X1_def X2_def X3_def)

  have B_eq: "uint256_to_int y =
              Y0 + Y1 * 2^64 + Y2 * 2^128 + Y3 * 2^192"
    unfolding y_eq uint256_to_int_def
    by (simp add: Let_def int_shiftl_eq_mult Y0_def Y1_def Y2_def Y3_def)

  have int_result:
    "uint256_to_int (x *\<^sub>u y) =
     uint z00 + uint z1 * 2^64 + uint z2 * 2^128 + uint z3 * 2^192"
    unfolding result_eq uint256_to_int_def
    by (simp add: Let_def int_shiftl_eq_mult)

  show ?thesis
    using int_result algebra A_eq B_eq by presburger
qed


lemma len256: "LENGTH(256) = 256"
  by code_simp

lemma word_of_int_mod_256: "word_of_int (a mod 2^256) = (word_of_int a :: u256)"
proof -
  have eq: "uint (word_of_int (a mod 2^256) :: u256) = uint (word_of_int a :: u256)"
    using len256
    by (metis mod_mod_trivial uint_word_of_int)
  then show ?thesis
    by (metis word_uint_eq_iff)
qed

lemma mul_equiv: "uint256_to_word256 (x *\<^sub>u y) = uint256_to_word256 x * uint256_to_word256 y"
proof -
  have "uint256_to_word256 (x *\<^sub>u y) = word_of_int (uint256_to_int (x *\<^sub>u y))"
    unfolding uint256_to_word256_def by presburger
  also have "... = word_of_int ((uint256_to_int x * uint256_to_int y) mod 2^256)"
    using uint256_mul_mod by presburger
  also have "... = word_of_int (uint256_to_int x * uint256_to_int y)"
    using word_of_int_mod_256 by presburger
  also have "... = word_of_int (uint256_to_int x) * word_of_int (uint256_to_int y)"
    by (rule wi_hom_mult [symmetric])
  also have "... = uint256_to_word256 x * uint256_to_word256 y"
    unfolding uint256_to_word256_def by presburger
  finally show ?thesis .
qed


lemma mul64_comm: "mul64 a b = mul64 b a"
proof -
  have lo_eq: "snd (mul64 a b) = snd (mul64 b a)"
    unfolding mul64_def Let_def
    by (simp add: mult.commute)
  have hi_uint_eq: "uint (fst (mul64 a b)) = uint (fst (mul64 b a))"
    using mul64_hi_eq[of a b] mul64_hi_eq[of b a]
    by (simp add: mult.commute)
  have hi_eq: "fst (mul64 a b) = fst (mul64 b a)"
    using hi_uint_eq by (metis word_uint_eq_iff)
  show ?thesis
    using hi_eq lo_eq by (rule prod_eqI)
qed

lemma umulHop_comm: "umulHop c a b = umulHop c b a"
proof -
  have "umulHop c a b =
        (case mul64 a b of
          (hi, lo) \<Rightarrow>
            case Add64_carry lo c 0 of
              (lo, carry) \<Rightarrow>
                case Add64_carry hi 0 carry of
                  (hi, _) \<Rightarrow> (hi, lo))"
    unfolding umulHop_def Let_def by (rule refl)
  also have "... =
        (case mul64 b a of
          (hi, lo) \<Rightarrow>
            case Add64_carry lo c 0 of
              (lo, carry) \<Rightarrow>
                case Add64_carry hi 0 carry of
                  (hi, _) \<Rightarrow> (hi, lo))"
    using mul64_comm[of a b] by simp
  also have "... = umulHop c b a"
    unfolding umulHop_def Let_def by (rule refl)
  finally show ?thesis .
qed


lemma squared_eq_mul: "squared x = (x *\<^sub>u x)"
proof -
  obtain x0 x1 x2 x3 where
    x_eq: "x = \<lparr>z0 = x0, z1 = x1, z2 = x2, z3 = x3\<rparr>"
    by (cases x) auto
  show ?thesis
    unfolding squared_def uint256_mul_def Let_def
    using x_eq
    by (simp add: mul64_comm umulHop_comm 
                   algebra_simps)
qed

lemma squared_int_mod:
  "uint256_to_int (squared x) =
   (uint256_to_int x * uint256_to_int x) mod 2^256"
proof -
  have "uint256_to_int (squared x) = uint256_to_int (x *\<^sub>u x)"
    using squared_eq_mul by presburger
  also have "... = (uint256_to_int x * uint256_to_int x) mod 2^256"
    by (rule uint256_mul_mod[of x x])
  finally show ?thesis .
qed



lemma squared_equiv: "uint256_to_word256 (squared x) = u256_sq (uint256_to_word256 x)"
proof -
  have "uint256_to_word256 (squared x) = word_of_int (uint256_to_int (squared x))"
    unfolding uint256_to_word256_def by presburger
  also have "... = word_of_int ((uint256_to_int x * uint256_to_int x) mod 2^256)"
    using squared_int_mod by presburger
  also have "... = word_of_int (uint256_to_int x * uint256_to_int x)"
    using word_of_int_mod_256 by presburger
  also have "... = word_of_int (uint256_to_int x) * word_of_int (uint256_to_int x)"
    by (metis wi_hom_mult)
  also have "... = uint256_to_word256 x * uint256_to_word256 x"
    unfolding uint256_to_word256_def by presburger
  also have "... = u256_sq (uint256_to_word256 x)"
    unfolding u256_sq.simps by presburger
  finally show ?thesis .
qed


lemma unat_shiftr1: "unat ((w :: u64) >> 1) = unat w div 2"
proof -
  have "unat ((w :: u64) >> 1) = unat (drop_bit 1 w)"
    by (simp add: shiftr_def)
  also have "... = drop_bit 1 (unat w)"
    by (rule unat_drop_bit_eq)
  also have "... = unat w div 2"
    by (simp add: drop_bit_eq_div)
  finally show ?thesis .
qed

lemma unat_and1_simple: "unat ((w :: u64) AND 1) = (if w AND 1 = 1 then 1 else 0)"
  using word_and_1_cases[of w] by auto

lemma unat_and_1_eq_mod2: "unat ((w :: u64) AND 1) = unat w mod 2"
proof -
  have cases: "w AND 1 = 0 \<or> w AND 1 = 1" by (rule word_and_1_cases)
  then show ?thesis
  proof
    assume A: "w AND 1 = 0"
    then show ?thesis
      using and_one_eq_zero_iff_mod2_u64[of w] A by auto
  next
    assume A: "w AND 1 = 1"
    then have lhs: "unat (w AND 1) = 1" by simp
    have A_eq: "(w AND 1 = 0) = (unat w mod 2 = 0)"
      using and_one_eq_zero_iff_mod2_u64[of w] .
    with A have "False = (unat w mod 2 = 0)" by simp
    hence "unat w mod 2 \<noteq> 0" by simp
    hence "unat w mod 2 = 1" by presburger
    then show ?thesis using lhs by simp
  qed
qed                                                                                        

lemma unat_word_decomp: "unat (w :: u64) = unat (w AND 1) + 2 * unat (w >> 1)"
  using unat_and_1_eq_mod2 unat_shiftr1 by presburger

lemma u64_nat_lower_zero [simp]: "u64_nat_lower (0 :: u64) n = 0"
  by (induction n) simp_all

lemma u64_nat_lower_Suc_eq:
  "u64_nat_lower w (Suc n) = u64_nat_lower w n + 2^n * unat ((w >> n) AND 1)"
proof (induction n arbitrary: w)
  case 0
  then show ?case by (simp add: shiftr_def)
next
  case (Suc n)
  have "u64_nat_lower w (Suc (Suc n)) = unat (w AND 1) + 2 * u64_nat_lower (w >> 1) (Suc n)"
    by simp
  also have "... = unat (w AND 1) + 2 * (u64_nat_lower (w >> 1) n + 2^n * unat (((w >> 1) >> n) AND 1))"
    using Suc by simp
  also have "... = (unat (w AND 1) + 2 * u64_nat_lower (w >> 1) n) + 2^(Suc n) * unat ((w >> Suc n) AND 1)"
    by (simp add: algebra_simps shiftr_def )
  also have "... = u64_nat_lower w (Suc n) + 2^(Suc n) * unat ((w >> Suc n) AND 1)"
    by simp
  finally show ?case .
qed

lemma unat_shr1_less:
  assumes "w \<noteq> (0 :: u64)"
  shows "unat (w >> 1) < unat w"
  using assms unat_shiftr1 unat_gt_0
  by (metis div_less_dividend  one_less_numeral_iff semiring_norm(76))

lemma u64_nat_lower_full: "u64_nat_lower (w :: u64) 64 = unat w"
proof (induction w rule: measure_induct_rule[where f=unat])
  case (less w)
  show ?case
  proof (cases "w = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have shr_lt: "unat (w >> 1) < unat w"
      by (rule unat_shr1_less[OF False])
    have eq_63_64: "u64_nat_lower (w >> 1) 63 = u64_nat_lower (w >> 1) 64"
    proof -
      have "u64_nat_lower (w >> 1) 64 = 
            u64_nat_lower (w >> 1) 63 + 2^63 * unat (((w >> 1) >> 63) AND 1)"
        using u64_nat_lower_Suc_eq[of "w >> 1" 63] by simp
      also have "... = u64_nat_lower (w >> 1) 63"
        by (simp add: shiftr_def u64_shift_ge_64)
      finally show ?thesis by simp
    qed
    have step: "u64_nat_lower w 64 = unat (w AND 1) + 2 * u64_nat_lower (w >> 1) 63"
    proof -
      have "64 = Suc 63" by code_simp
      thus ?thesis by (simp only: u64_nat_lower.simps(2))
    qed
    have "u64_nat_lower w 64 = unat (w AND 1) + 2 * u64_nat_lower (w >> 1) 63"
      using step by simp
    also have "... = unat (w AND 1) + 2 * u64_nat_lower (w >> 1) 64"
      using eq_63_64 by simp
    also have "... = unat (w AND 1) + 2 * unat (w >> 1)"
      using less shr_lt by auto
    also have "... = unat w"
      using unat_and_1_eq_mod2 unat_shiftr1 by presburger
    finally show ?thesis .
  qed
qed

lemma u64_nat_lower_trunc: "(w :: u64) >> n = 0 \<Longrightarrow> u64_nat_lower w n = u64_nat_lower w 64"
proof (induction w arbitrary: n rule: measure_induct_rule[where f=unat])
  case (less w)
  show ?case
  proof (cases "w = 0")
    case True then show ?thesis by simp
  next
    case w_ne: False
    show ?thesis
    proof (cases "n = 0")
      case True
      with less.prems show ?thesis by (simp add: shiftr_def)
    next
      case n_ne: False
      then obtain m where n_eq: "n = Suc m" using not0_implies_Suc by blast
      have shr_pre: "(w >> 1) >> m = 0"
        using less.prems n_eq by (simp add: shiftr_def)
      have shr_lt: "unat (w >> 1) < unat w"
        by (rule unat_shr1_less[OF w_ne])
      have bridge: "u64_nat_lower (w >> 1) 64 = u64_nat_lower (w >> 1) 63"
        using u64_nat_lower_Suc_eq[of "w >> 1" 63]
        by (simp add: shiftr_def u64_shift_ge_64)
      have last_step: "unat (w AND 1) + 2 * u64_nat_lower (w >> 1) 63 = u64_nat_lower w 64"
      proof -
        have "64 = Suc 63" by code_simp
        thus ?thesis by (simp only: u64_nat_lower.simps(2))
      qed
      have "u64_nat_lower w n = u64_nat_lower w (Suc m)"
        by (simp add: n_eq)
      also have "... = unat (w AND 1) + 2 * u64_nat_lower (w >> 1) m"
        by simp
      also have "... = unat (w AND 1) + 2 * u64_nat_lower (w >> 1) 64"
        using less(1)[OF shr_lt shr_pre] by simp
      also have "... = unat (w AND 1) + 2 * u64_nat_lower (w >> 1) 63"
        using bridge by simp
      also have "... = u64_nat_lower w 64"
        using last_step by simp
      finally show ?thesis .
    qed
  qed
qed


lemma u256_lowbit_equiv:
  "((uint256_to_word256 x) AND (1 :: u256) = 0) = (z0 x AND 1 = 0)"
proof -
  have decomp: "unat (uint256_to_word256 x) = 
        unat (z0 x) + 2^64 * unat (z1 x) + 2^128 * unat (z2 x) + 2^192 * unat (z3 x)"
    by (rule unat_uint256_decomp)
  define T1 where "T1 \<equiv> 2^64 * unat (z1 x)"
  define T2 where "T2 \<equiv> 2^128 * unat (z2 x)"
  define T3 where "T3 \<equiv> 2^192 * unat (z3 x)"
  have T1_even: "even T1"      
    unfolding T1_def by simp
  have T2_even: "even T2"
    unfolding T2_def by simp
  have T3_even: "even T3"
    unfolding T3_def by simp
  have tail_even: "even (T1 + T2 + T3)"
    using T1_even T2_even T3_even by simp
  have parity: "unat (uint256_to_word256 x) mod 2 = unat (z0 x) mod 2"
  proof -
    have "unat (uint256_to_word256 x) = unat (z0 x) + (T1 + T2 + T3)"
      using decomp unfolding T1_def T2_def T3_def by simp
    hence "unat (uint256_to_word256 x) mod 2 = (unat (z0 x) + (T1 + T2 + T3)) mod 2"
      by presburger
    also have "... = unat (z0 x) mod 2"
    proof -
      from tail_even obtain k where "T1 + T2 + T3 = 2 * k"
        by (metis evenE)
      thus ?thesis by simp
    qed
    finally show ?thesis .
  qed
  show ?thesis
    using parity and_one_eq_zero_iff_mod2_u256 and_one_eq_zero_iff_mod2_u64
    by auto
qed


lemma Exp_aux_equiv:
  "(uint256_to_word256 (fst (Exp_aux res mult w n curBit)),
    uint256_to_word256 (fst (snd (Exp_aux res mult w n curBit))),
    snd (snd (Exp_aux res mult w n curBit))) =
   u256_pow_aux (uint256_to_word256 res) (uint256_to_word256 mult) w n curBit"
proof (induction n arbitrary: res mult w curBit)
  case 0
  then show ?case by simp
next
  case (Suc n)
  note outer_IH = Suc.IH
  show ?case
  proof (cases curBit)
    case 0
    then show ?thesis by simp
  next
    case (Suc curBit')
    show ?thesis
    proof (cases "w AND 1 = 1")
      case True
      then show ?thesis
        using outer_IH[of "res *\<^sub>u mult" "squared mult" "w >> 1" curBit']
              squared_equiv[of mult] mul_equiv
        by (simp add: \<open>curBit = Suc curBit'\<close>)
    next
      case False
      then show ?thesis
        using outer_IH[of res "squared mult" "w >> 1" curBit']
              squared_equiv[of mult]
        by (simp add: \<open>curBit = Suc curBit'\<close>)
    qed
  qed
qed

lemma uint256_to_word256_zero:
  "uint256_to_word256 uint256_zero = (0 :: u256)"
  by code_simp

lemma uint256_to_word256_one:
  "uint256_to_word256 uint256_one = (1 :: u256)"
  by code_simp

lemma two_pow_256_zero: "(2 :: u256) ^ 256 = 0"
  by code_simp

lemma even_base_large_exp_zero:
  fixes base :: u256
  assumes "even base" and "unat exp \<ge> 256"
  shows "base ^ unat exp = 0"
proof -
  from assms(1) obtain k where "base = 2 * k"
    by (metis dvdE)
  have base_256: "base ^ 256 = 0"
  proof -
    have "base ^ 256 = (2 * k) ^ 256" using \<open>base = 2 * k\<close> by simp
    also have "\<dots> = 2 ^ 256 * k ^ 256" by (rule power_mult_distrib)
    also have "2 ^ 256 = (0 :: u256)" by (rule two_pow_256_zero)
    also have "0 * k ^ 256 = 0" by simp
    finally show ?thesis .
  qed
  from assms(2) obtain m where "unat exp = 256 + m"
    by (metis nat_le_iff_add)
  then have "base ^ unat exp = base ^ 256 * base ^ m"
    by (simp add: power_add)
  also have "\<dots> = 0" by (simp add: base_256)
  finally show ?thesis .
qed

lemma Len64_gt_8_imp_unat_ge_256:
  fixes x :: u64
  assumes "8 < Len64 x"
  shows "256 \<le> unat x"
proof (rule ccontr)
  assume "\<not> 256 \<le> unat x"
  then have unat_lt: "unat x < 256" by linarith

  have unat_pow8: "unat ((1 << 8) :: u64) = 256"
    by (fact unat_256)
  have unat_pow16: "unat ((1 << 16) :: u64) = (2::nat)^16"
    by (simp add: pow16 unat_numeral)
  have unat_pow32: "unat ((1 << 32) :: u64) = (2::nat)^32"
    by (simp add: pow32 unat_numeral)

  have x_lt8: "x < (1 << 8 :: u64)"
  proof -
    have "unat x < unat ((1 << 8) :: u64)"
      using unat_lt unat_pow8 by simp
    then show ?thesis
      by (simp add: word_less_nat_alt)
  qed

  have x_lt16: "x < (1 << 16 :: u64)"
  proof -
    have "256 < (2::nat)^16" by simp
    have "unat x < (2::nat)^16"
      using unat_lt `256 < (2::nat)^16` by linarith
    then have "unat x < unat ((1 << 16) :: u64)"
      using unat_pow16 by linarith
    then show ?thesis
      by (simp add: word_less_nat_alt)
  qed

  have x_lt32: "x < (1 << 32 :: u64)"
  proof -
    have "256 < (2::nat)^32" by simp
    have "unat x < (2::nat)^32"
      using unat_lt `256 < (2::nat)^32` by linarith
    then have "unat x < unat ((1 << 32) :: u64)"
      using unat_pow32 by linarith
    then show ?thesis
      by (simp add: word_less_nat_alt)
  qed

  have not32: "\<not> (1 << 32 :: u64) \<le> x"
    using x_lt32 by (simp add: not_le)
  have not16: "\<not> (1 << 16 :: u64) \<le> x"
    using x_lt16 by (simp add: not_le)
  have not8: "\<not> (1 << 8 :: u64) \<le> x"
    using x_lt8 by (simp add: not_le)

  have b32: "(if (1 << 32 :: u64) \<le> x
              then (32::nat, x >> 32)
              else (0::nat, x)) = (0, x)"
    using not32 by simp

  have b16: "(if (1 << 16 :: u64) \<le> x
              then (16::nat, x >> 16)
              else (0::nat, x)) = (0, x)"
    using not16 by simp

  have b8: "(if (1 << 8 :: u64) \<le> x
             then (8::nat, x >> 8)
             else (0::nat, x)) = (0, x)"
    using not8 by simp

  have len_eq: "Len64 x = len8tab (ucast x)"
    unfolding Len64_def Let_def
    by (simp add: b32 b16 b8 split: prod.split)

  have tab_le: "len8tab (ucast x) \<le> 8"
    unfolding len8tab_def
    by (simp split: if_splits)

  with assms show False
    using len_eq by linarith
qed

lemma bitlen_gt_8_imp_unat_ge_256:
  assumes "BitLen (word256_to_uint256 exp) > 8"
  shows "unat exp \<ge> 256"
proof (rule ccontr)
  assume "\<not> 256 \<le> unat exp"
  then have unat_lt: "unat exp < 256" by linarith

  have exp_uint_lt: "uint exp < 256"
  proof -
    have "uint exp = int (unat exp)"
      using unat_eq_nat_uint[of exp] uint_nonnegative[of exp]
      by (metis int_nat_eq)
    then show ?thesis using unat_lt by linarith
  qed

  have exp_uint_ge: "0 \<le> uint exp"
    by (rule uint_nonnegative)

  have exp_uint_lt_2p64: "uint exp < 2^64"
    using exp_uint_lt by simp
  have exp_uint_lt_2p128: "uint exp < 2^128"
    using exp_uint_lt by simp
  have exp_uint_lt_2p192: "uint exp < 2^192"
    using exp_uint_lt by simp

  let ?w = "word256_to_uint256 exp"

  have take64: "take_bit 64 (uint exp) = uint exp"
    using exp_uint_ge exp_uint_lt_2p64
    by (simp add: take_bit_int_eq_self)

  have drop64: "drop_bit 64 (uint exp) = 0"
    using take64 by (simp add: take_bit_eq_self_iff_drop_bit_eq_0)

  have shift64: "(uint exp >> 64) = 0"
    using drop64 unfolding shiftr_def by simp


  have take128: "take_bit 128 (uint exp) = uint exp"
    using exp_uint_ge exp_uint_lt_2p128
    by (simp add: take_bit_int_eq_self)

  have drop128: "drop_bit 128 (uint exp) = 0"
    using take128 by (simp add: take_bit_eq_self_iff_drop_bit_eq_0)

  have shift128: "(uint exp >> 128) = 0"
    using drop128 unfolding shiftr_def by simp


  have take192: "take_bit 192 (uint exp) = uint exp"
    using exp_uint_ge exp_uint_lt_2p192
    by (simp add: take_bit_int_eq_self)

  have drop192: "drop_bit 192 (uint exp) = 0"
    using take192 by (simp add: take_bit_eq_self_iff_drop_bit_eq_0)

  have shift192: "(uint exp >> 192) = 0"
    using drop192 unfolding shiftr_def by simp

  have z1_eq: "z1 ?w = 0"
    unfolding word256_to_uint256_def int_to_uint256_def
    by (simp add: shift64)
  have z2_eq: "z2 ?w = 0"
    unfolding word256_to_uint256_def int_to_uint256_def
    by (simp add: shift128)
  have z3_eq: "z3 ?w = 0"
    unfolding word256_to_uint256_def int_to_uint256_def
    by (simp add: shift192)

  have z0_eq: "z0 ?w = word_of_int (uint exp mod 2^64)"
    unfolding word256_to_uint256_def int_to_uint256_def by simp

  have z0_uint_eq: "uint (z0 ?w) = uint exp"
  proof -
    have "uint (word_of_int (uint exp mod 2^64) :: u64) = uint exp mod 2^64"
      by (simp add: uint_word_of_int)
    also have "... = uint exp"
      using exp_uint_ge exp_uint_lt_2p64 by simp
    finally show ?thesis using z0_eq by simp
  qed

  have z0_unat_eq: "unat (z0 ?w) = unat exp"
    using z0_uint_eq by (metis unat_eq_nat_uint)

  have z0_len_le: "Len64 (z0 ?w) \<le> 8"
  proof (rule ccontr)
    assume "\<not> Len64 (z0 ?w) \<le> 8"
    then have "8 < Len64 (z0 ?w)" by linarith
    then have "256 \<le> unat (z0 ?w)"
      by (rule Len64_gt_8_imp_unat_ge_256)
    with z0_unat_eq unat_lt show False by linarith
  qed

  have "BitLen ?w = Len64 (z0 ?w)"
    unfolding BitLen_def
    using z1_eq z2_eq z3_eq by simp

  with assms z0_len_le show False
    by linarith
qed


section \<open>Main lemma: u256_pow = mathematical power\<close>

lemma u256_pow_eq_pow:
  fixes base exp :: u256
  shows "base pow\<^sub>2\<^sub>5\<^sub>6 exp = base ^ unat exp"
proof (cases "base AND 1 = 0 \<and> BitLen (word256_to_uint256 exp) > 8")
  case True
  then have even_base: "base AND 1 = 0" and bitlen_gt: "BitLen (word256_to_uint256 exp) > 8"
    by auto
  have even: "even base"
    using even_base and_1_eq_0_imp_even by blast
  have unat_ge: "unat exp \<ge> 256"
    using bitlen_gt bitlen_gt_8_imp_unat_ge_256 by blast
  have lhs: "base pow\<^sub>2\<^sub>5\<^sub>6 exp = 0"
    unfolding u256_pow_def Let_def using True by simp
  have rhs: "base ^ unat exp = 0"
    using even_base_large_exp_zero[OF even unat_ge] .
  from lhs rhs show ?thesis by simp
next
  case False
  let ?bl = "BitLen (word256_to_uint256 exp)"
  let ?w  = "word256_to_uint256 exp"
  let ?z0 = "z0 ?w" and ?z1 = "z1 ?w" and ?z2 = "z2 ?w" and ?z3 = "z3 ?w"

  define n0 where "n0 = min 64 ?bl"
  define n1 where "n1 = min 64 (?bl - n0)"
  define n2 where "n2 = min 64 (?bl - n0 - n1)"
  define n3 where "n3 = ?bl - n0 - n1 - n2"

  have n0_ge: "n0 \<le> ?bl" by (simp add: n0_def)
  have n1_ge: "n1 \<le> ?bl - n0" by (simp add: n1_def)
  have n2_ge: "n2 \<le> ?bl - n0 - n1" by (simp add: n2_def)
  have n3_ge: "n3 \<le> ?bl - n0 - n1 - n2" by (simp add: n3_def)

  have c1_eq: "snd (snd (u256_pow_aux (1::u256) base ?z0 64 ?bl)) = ?bl - n0"
    by (cases "64 \<le> ?bl") (auto simp: n0_def inv_enough_cur inv_short_cur)
  let ?c1 = "?bl - n0"
  let ?c2 = "?bl - n0 - n1"

  \<comment> \<open>Per-stage results from invariants\<close>
  have s1_r: "fst (u256_pow_aux (1::u256) base ?z0 64 ?bl) = base ^ u64_nat_lower ?z0 n0"
    by (cases "64 \<le> ?bl") (auto simp: n0_def inv_enough_fst inv_short_fst)
  have s1_m: "fst (snd (u256_pow_aux (1::u256) base ?z0 64 ?bl)) = base ^ (2 ^ n0)"
    by (cases "64 \<le> ?bl") (auto simp: n0_def inv_enough_snd inv_short_snd)

    have s2_fst: "\<And>r m. fst (u256_pow_aux r m ?z1 64 ?c1) = r * m ^ u64_nat_lower ?z1 n1"
    unfolding n1_def
    by (cases "64 \<le> ?c1") (auto simp: inv_enough_fst inv_short_fst)
  have s2_snd: "\<And>r m. fst (snd (u256_pow_aux r m ?z1 64 ?c1)) = m ^ (2 ^ n1)"
    unfolding n1_def
    by (cases "64 \<le> ?c1") (auto simp: inv_enough_snd inv_short_snd)

  have s3_fst: "\<And>r m. fst (u256_pow_aux r m ?z2 64 ?c2) = r * m ^ u64_nat_lower ?z2 n2"
    unfolding n2_def
    by (cases "64 \<le> ?c2") (auto simp: inv_enough_fst inv_short_fst)
  have s3_snd: "\<And>r m. fst (snd (u256_pow_aux r m ?z2 64 ?c2)) = m ^ (2 ^ n2)"
    unfolding n2_def
    by (cases "64 \<le> ?c2") (auto simp: inv_enough_snd inv_short_snd)

     have s4_fst: "\<And>r m. fst (u256_pow_aux r m ?z3 64 (?c1 - n1 - n2)) =
                         r * m ^ u64_nat_lower ?z3 n3"
  proof -
    fix r m
    have c3: "?c1 - n1 - n2 = n3"
      by (simp add: n3_def)
    show "fst (u256_pow_aux r m ?z3 64 (?c1 - n1 - n2)) = r * m ^ u64_nat_lower ?z3 n3"
    proof (cases "?c1 - n1 - n2 < 64")
      case True
      with c3 show ?thesis by (simp add: inv_short_fst)
    next
      case False
      then have ge64: "64 \<le> n3" using c3 by simp
      have shift0: "?z3 >> n3 = 0"
        by (rule u64_shift_ge_64[OF ge64])
      have "fst (u256_pow_aux r m ?z3 64 n3) = r * m ^ u64_nat_lower ?z3 64"
        using inv_enough_fst[OF ge64] by simp
      also have "u64_nat_lower ?z3 64 = u64_nat_lower ?z3 n3"
        using u64_nat_lower_trunc[OF shift0] by simp
      finally show ?thesis unfolding c3 .
    qed
  qed

  \<comment> \<open>Algebraic chaining of the four stages\<close>
  let ?r1  = "fst (u256_pow_aux (1::u256) base ?z0 64 ?bl)"
  let ?m1  = "fst (snd (u256_pow_aux (1::u256) base ?z0 64 ?bl))"
  let ?r2  = "fst (u256_pow_aux ?r1 ?m1 ?z1 64 ?c1)"
  let ?m2  = "fst (snd (u256_pow_aux ?r1 ?m1 ?z1 64 ?c1))"
  let ?r3  = "fst (u256_pow_aux ?r2 ?m2 ?z2 64 ?c2)"
  let ?m3  = "fst (snd (u256_pow_aux ?r2 ?m2 ?z2 64 ?c2))"
  let ?r4  = "fst (u256_pow_aux ?r3 ?m3 ?z3 64 (?c1 - n1 - n2))"

  have r1_eq: "?r1 = base ^ u64_nat_lower ?z0 n0" by (rule s1_r)
  have m1_eq: "?m1 = base ^ (2 ^ n0)" by (rule s1_m)

  have r2_eq: "?r2 = base ^ (u64_nat_lower ?z0 n0 + 2 ^ n0 * u64_nat_lower ?z1 n1)"
  proof -
    have "?r2 = ?r1 * ?m1 ^ u64_nat_lower ?z1 n1" by (rule s2_fst)
    also have "\<dots> = base ^ u64_nat_lower ?z0 n0 *
                    (base ^ (2 ^ n0)) ^ u64_nat_lower ?z1 n1"
      using r1_eq m1_eq by simp
    also have "\<dots> = base ^ (u64_nat_lower ?z0 n0 + 2 ^ n0 * u64_nat_lower ?z1 n1)"
      by (simp add: power_add power_mult[symmetric])
    finally show ?thesis .
  qed

  have m2_eq: "?m2 = base ^ (2 ^ (n0 + n1))"
  proof -
    have "?m2 = ?m1 ^ (2 ^ n1)" by (rule s2_snd)
    also have "\<dots> = (base ^ (2 ^ n0)) ^ (2 ^ n1)" using m1_eq by simp
    also have "\<dots> = base ^ (2 ^ (n0 + n1))" by (simp add: power_mult power_add)
    finally show ?thesis .
  qed

  have r3_eq: "?r3 = base ^ (u64_nat_lower ?z0 n0 + 2 ^ n0 * u64_nat_lower ?z1 n1 +
                            2 ^ (n0 + n1) * u64_nat_lower ?z2 n2)"
  proof -
    have "?r3 = ?r2 * ?m2 ^ u64_nat_lower ?z2 n2" by (rule s3_fst)
    also have "\<dots> = base ^ (u64_nat_lower ?z0 n0 + 2 ^ n0 * u64_nat_lower ?z1 n1) *
                    (base ^ (2 ^ (n0 + n1))) ^ u64_nat_lower ?z2 n2"
      using r2_eq m2_eq by simp
    also have "\<dots> = base ^ (u64_nat_lower ?z0 n0 + 2 ^ n0 * u64_nat_lower ?z1 n1 +
                           2 ^ (n0 + n1) * u64_nat_lower ?z2 n2)"
      by (simp add: power_add power_mult[symmetric])
    finally show ?thesis .
  qed

  have m3_eq: "?m3 = base ^ (2 ^ (n0 + n1 + n2))"
  proof -
    have "?m3 = ?m2 ^ (2 ^ n2)" by (rule s3_snd)
    also have "\<dots> = (base ^ (2 ^ (n0 + n1))) ^ (2 ^ n2)" using m2_eq by simp
    also have "\<dots> = base ^ (2 ^ (n0 + n1 + n2))" by (simp add: power_mult power_add)
    finally show ?thesis .
  qed

  have r4_eq: "?r4 = base ^ (u64_nat_lower ?z0 n0 + 2 ^ n0 * u64_nat_lower ?z1 n1 +
                            2 ^ (n0 + n1) * u64_nat_lower ?z2 n2 +
                            2 ^ (n0 + n1 + n2) * u64_nat_lower ?z3 n3)"
  proof -
    have "?r4 = ?r3 * ?m3 ^ u64_nat_lower ?z3 n3" by (rule s4_fst)
    also have "\<dots> = base ^ (u64_nat_lower ?z0 n0 + 2 ^ n0 * u64_nat_lower ?z1 n1 +
                           2 ^ (n0 + n1) * u64_nat_lower ?z2 n2) *
                    (base ^ (2 ^ (n0 + n1 + n2))) ^ u64_nat_lower ?z3 n3"
      using r3_eq m3_eq by simp
    also have "\<dots> = base ^ (u64_nat_lower ?z0 n0 + 2 ^ n0 * u64_nat_lower ?z1 n1 +
                           2 ^ (n0 + n1) * u64_nat_lower ?z2 n2 +
                           2 ^ (n0 + n1 + n2) * u64_nat_lower ?z3 n3)"
      by (simp add: power_add power_mult[symmetric])
    finally show ?thesis .
  qed

  \<comment> \<open>Bridge: partial extraction = full unat, via BitLen shift axioms\<close>
  have z0_full: "u64_nat_lower ?z0 n0 = unat ?z0"
  proof (cases "64 \<le> ?bl")
    case True
    then have "n0 = 64" by (simp add: n0_def)
    then show ?thesis by (simp add: u64_nat_lower_full)
  next
    case False
    then have bl_lt: "?bl < 64" by simp
    then have "n0 = ?bl" by (simp add: n0_def)
    moreover have "?z0 >> ?bl = 0" by (rule bitlen_z0_shift[OF bl_lt])
    ultimately show ?thesis
      using u64_nat_lower_trunc u64_nat_lower_full by auto
  qed

  have z1_full: "u64_nat_lower ?z1 n1 = unat ?z1"
  proof (cases "64 \<le> ?bl - n0")
    case True
    then have "n1 = 64" by (simp add: n1_def)
    then show ?thesis by (simp add: u64_nat_lower_full)
    next
    case False
    then have n1_eq: "n1 = ?bl - n0" by (simp add: n1_def)
    show ?thesis
    proof (cases "64 \<le> ?bl")
      case True
      then have n0_64: "n0 = 64" by (simp add: n0_def)
      have lt128: "?bl < 128"
      proof -
        from n0_64 False have "?bl - 64 < 64" using n1_eq by auto
        then show ?thesis by auto
      qed
      have shift: "?z1 >> (?bl - 64) = 0"
        using bitlen_z1_shift[OF True lt128] .
      from n1_eq n0_64 shift
      show ?thesis using u64_nat_lower_trunc u64_nat_lower_full by auto
    next
      case False
      then have bl_lt64: "?bl < 64" by simp
      then have n0_bl: "n0 = ?bl" by (simp add: n0_def)
      with n1_eq have "n1 = 0" by simp
      moreover have "unat ?z1 = 0"
        using bitlen_lt_64_imp_z1_zero[OF bl_lt64] by simp
      ultimately show ?thesis by simp
    qed
  qed

  have z2_full: "u64_nat_lower ?z2 n2 = unat ?z2"
  proof (cases "64 \<le> ?bl - n0 - n1")
    case True
    then have "n2 = 64" by (simp add: n2_def)
    then show ?thesis by (simp add: u64_nat_lower_full)
   next
    case False
    then have n2_eq: "n2 = ?bl - n0 - n1" by (simp add: n2_def)
    show ?thesis
    proof (cases "128 \<le> ?bl")
      case True
      then have n0_64: "n0 = 64" and n1_64: "n1 = 64"
        by (auto simp: n0_def n1_def)
      have lt192: "?bl < 192"
      proof -
        from n0_64 n1_64 False n2_eq have "?bl - 128 < 64" by auto
        then show ?thesis by auto
      qed
      have shift: "?z2 >> (?bl - 128) = 0"
        using bitlen_z2_shift[OF True lt192] .
      from n2_eq n0_64 n1_64 shift
      show ?thesis using u64_nat_lower_trunc u64_nat_lower_full by auto
    next
      case False
      then have bl_lt128: "?bl < 128" by simp
      with n0_def n1_def n2_eq have "n2 = 0"
        by auto
      moreover have "unat ?z2 = 0"
        using bitlen_lt_128_imp_z2_zero[OF bl_lt128] by simp
      ultimately show ?thesis by simp
    qed
  qed

   have z3_full: "u64_nat_lower ?z3 n3 = unat ?z3"
  proof (cases "64 \<le> n3")
    case True
    then have ge64: "64 \<le> n3" by simp
    have shift: "?z3 >> n3 = 0"
      by (rule u64_shift_ge_64[OF ge64])
    have "u64_nat_lower ?z3 n3 = u64_nat_lower ?z3 64"
      using u64_nat_lower_trunc[OF shift] by simp
    also have "u64_nat_lower ?z3 64 = unat ?z3"
      by (rule u64_nat_lower_full)
    finally show ?thesis .
  next
    case False
    then have n3_lt64: "n3 < 64" by simp
    show ?thesis
    proof (cases "192 \<le> ?bl")
      case True
      then have n0_64: "n0 = 64" and n1_64: "n1 = 64" and n2_64: "n2 = 64"
        by (auto simp: n0_def n1_def n2_def)
      have lt256: "?bl < 256"
      proof (rule ccontr)
        assume "\<not> ?bl < 256"
        then have ge256: "256 \<le> ?bl" by simp
        with bitlen_le_256[of ?w] have "?bl = 256" by (rule antisym)
        with n0_64 n1_64 n2_64 have "n3 = 64" by (simp add: n3_def)
        with n3_lt64 show False by simp
      qed
      have shift: "?z3 >> (?bl - 192) = 0"
        using bitlen_z3_shift[OF True lt256] .
      from n3_lt64 n0_64 n1_64 n2_64 have "n3 = ?bl - 192"
        by (auto simp: n3_def)
      with shift show ?thesis
        using u64_nat_lower_trunc u64_nat_lower_full by auto
    next
      case False
      then have bl_lt192: "?bl < 192" by simp
            have "n3 = 0"
      proof (cases "?bl < 64")
        case True
        then show ?thesis by (auto simp: n0_def n1_def n2_def n3_def)
      next
        case False then have ge64: "64 \<le> ?bl" by simp
        show ?thesis
        proof (cases "?bl < 128")
          case True
          with ge64 show ?thesis by (auto simp: n0_def n1_def n2_def n3_def)
        next
          case False then have ge128: "128 \<le> ?bl" by simp
          with bl_lt192 show ?thesis by (auto simp: n0_def n1_def n2_def n3_def)
        qed
      qed
      moreover have "unat ?z3 = 0"
        using bitlen_lt_192_imp_z3_zero[OF bl_lt192] by simp
      ultimately show ?thesis by simp
    qed
  qed

    have exponent_sum:
    "u64_nat_lower ?z0 n0 + 2 ^ n0 * u64_nat_lower ?z1 n1 +
     2 ^ (n0 + n1) * u64_nat_lower ?z2 n2 +
     2 ^ (n0 + n1 + n2) * u64_nat_lower ?z3 n3 =
     unat (uint256_to_word256 ?w)"
  proof -
    have E0: "u64_nat_lower ?z0 n0 = unat ?z0"
      by (rule z0_full)
    have E1: "2 ^ n0 * u64_nat_lower ?z1 n1 = 2^64 * unat ?z1"
    proof (cases "64 \<le> ?bl")
      case True
      then have "n0 = 64" by (simp add: n0_def)
      then show ?thesis by (simp add: z1_full)
    next
      case False
      then have bl_lt64: "?bl < 64" by simp
      then have n0_bl: "n0 = ?bl" and n1_0: "n1 = 0"
        by (auto simp: n0_def n1_def)
      have z1_zero: "unat ?z1 = 0"
        using bitlen_lt_64_imp_z1_zero[OF bl_lt64] by simp
      from n0_bl n1_0 z1_zero show ?thesis by simp
    qed
    have E2: "2 ^ (n0 + n1) * u64_nat_lower ?z2 n2 = 2^128 * unat ?z2"
    proof (cases "128 \<le> ?bl")
      case True
      then have "n0 = 64" "n1 = 64" by (auto simp: n0_def n1_def)
      then show ?thesis by (simp add: z2_full)
    next
      case False
      then have bl_lt128: "?bl < 128" by simp
      with n0_def n1_def n2_def have "n2 = 0" by auto
      moreover have "unat ?z2 = 0"
        using bitlen_lt_128_imp_z2_zero[OF bl_lt128] by simp
      ultimately show ?thesis by simp
    qed
    have E3: "2 ^ (n0 + n1 + n2) * u64_nat_lower ?z3 n3 = 2^192 * unat ?z3"
    proof (cases "192 \<le> ?bl")
      case True
      then have "n0 = 64" "n1 = 64" "n2 = 64" by (auto simp: n0_def n1_def n2_def)
      then show ?thesis by (simp add: z3_full)
     next
      case False
      then have bl_lt192: "?bl < 192" by simp
      have "n3 = 0"
      proof (cases "?bl < 64")
        case True
        then show ?thesis by (auto simp: n0_def n1_def n2_def n3_def)
      next
        case False then have ge64: "64 \<le> ?bl" by simp
        show ?thesis
        proof (cases "?bl < 128")
          case True
          with ge64 show ?thesis by (auto simp: n0_def n1_def n2_def n3_def)
        next
          case False then have ge128: "128 \<le> ?bl" by simp
          with bl_lt192 show ?thesis by (auto simp: n0_def n1_def n2_def n3_def)
        qed                     
      qed
      moreover have "unat ?z3 = 0"
        using bitlen_lt_192_imp_z3_zero[OF bl_lt192] by simp
      ultimately show ?thesis by simp
    qed
    from E0 E1 E2 E3
    show ?thesis by (simp add: unat_uint256_decomp[of ?w])
  qed

  have result: "?r4 = base ^ unat (uint256_to_word256 ?w)"
    using r4_eq exponent_sum by simp

  show ?thesis
  proof -
    obtain r1 m1 c1 where
      P1: "u256_pow_aux (1::u256) base ?z0 64 ?bl = (r1, m1, c1)"
      by (cases "u256_pow_aux (1::u256) base ?z0 64 ?bl") auto
    have r1_eq': "r1 = ?r1" using P1 by simp
    have m1_eq': "m1 = ?m1" using P1 by simp
    have c1_eq': "c1 = ?c1" using P1 c1_eq by simp

    obtain r2 m2 c2 where
      P2: "u256_pow_aux r1 m1 ?z1 64 c1 = (r2, m2, c2)"
      by (cases "u256_pow_aux r1 m1 ?z1 64 c1") auto
    have r2_eq': "r2 = ?r2" using P2 r1_eq' m1_eq' c1_eq' by simp
    have m2_eq': "m2 = ?m2" using P2 r1_eq' m1_eq' c1_eq' by simp
    have c2_eq': "c2 = ?c2"
      using P2 r1_eq' m1_eq' c1_eq'
    proof (cases "64 \<le> ?c1")
      case True
      then have "n1 = 64" by (simp add: n1_def)
      have "c2 = snd (snd (u256_pow_aux ?r1 ?m1 ?z1 64 ?c1))"
        using P2 r1_eq' m1_eq' c1_eq' by simp
      also have "... = ?c1 - 64"
        using True by (simp add: inv_enough_cur)
      also have "... = ?c2"
        using \<open>n1 = 64\<close> by simp
      finally show ?thesis .
    next
      case False
      then have "?c1 < 64" by simp
      then have "n1 = ?c1" by (simp add: n1_def)
      hence "?c2 = 0" by simp
      have "c2 = snd (snd (u256_pow_aux ?r1 ?m1 ?z1 64 ?c1))"
        using P2 r1_eq' m1_eq' c1_eq' by simp
      also have "... = 0"
        using False by (simp add: inv_short_cur)
      also have "... = ?c2"
        using \<open>?c2 = 0\<close> by simp
      finally show ?thesis .
    qed

    obtain r3 m3 c3 where
      P3: "u256_pow_aux r2 m2 ?z2 64 c2 = (r3, m3, c3)"
      by (cases "u256_pow_aux r2 m2 ?z2 64 c2") auto
    have r3_eq': "r3 = ?r3" using P3 r2_eq' m2_eq' c2_eq' by simp
    have m3_eq': "m3 = ?m3" using P3 r2_eq' m2_eq' c2_eq' by simp
    have c3_eq': "c3 = ?c1 - n1 - n2"
      using P3 r2_eq' m2_eq' c2_eq'
    proof (cases "64 \<le> ?c2")
      case True
      then have "n2 = 64" by (simp add: n2_def)
      have "c3 = snd (snd (u256_pow_aux ?r2 ?m2 ?z2 64 ?c2))"
        using P3 r2_eq' m2_eq' c2_eq' by simp
      also have "... = ?c2 - 64"
        using True by (simp add: inv_enough_cur)
      also have "... = ?c1 - n1 - n2"
        using \<open>n2 = 64\<close> by simp
      finally show ?thesis .
    next
      case False
      then have "?c2 < 64" by simp
      then have "n2 = ?c2" by (simp add: n2_def)
      hence "?c1 - n1 - n2 = 0" by simp
      have "c3 = snd (snd (u256_pow_aux ?r2 ?m2 ?z2 64 ?c2))"
        using P3 r2_eq' m2_eq' c2_eq' by simp
      also have "... = 0"
        using False by (simp add: inv_short_cur)
      also have "... = ?c1 - n1 - n2"
        using \<open>?c1 - n1 - n2 = 0\<close> by simp
      finally show ?thesis .
    qed

    obtain r4 m4 c4 where
      P4: "u256_pow_aux r3 m3 ?z3 64 c3 = (r4, m4, c4)"
      by (cases "u256_pow_aux r3 m3 ?z3 64 c3") auto
    have r4_eq': "r4 = ?r4" using P4 r3_eq' m3_eq' c3_eq' by simp

    have "base pow\<^sub>2\<^sub>5\<^sub>6 exp = r4"
      unfolding u256_pow_def Let_def using False P1 P2 P3 P4 by (auto split: prod.split)
    also have "r4 = ?r4" by (rule r4_eq')
    also have "?r4 = base ^ unat exp"
      using result uint256_word256_roundtrip[of exp] by simp
    finally show ?thesis .
  qed
qed


section \<open>Final theorem: Exp equivalence\<close>

theorem exp_equivalence:
  "uint256_to_word256 (Exp x y) = (uint256_to_word256 x) ^ (unat(uint256_to_word256 y))"
proof (cases "z0 x AND 1 = 0 \<and> 8 < BitLen y")
  case True
  then have lhs: "uint256_to_word256 (Exp x y) = uint256_to_word256 uint256_zero"
    unfolding Exp_def Let_def by simp
  have even: "(uint256_to_word256 x) AND (1 :: u256) = 0"
    using True u256_lowbit_equiv by auto
  have rhs: "(uint256_to_word256 x) ^ unat (uint256_to_word256 y) =
             uint256_to_word256 uint256_zero"
  proof -
    have "(uint256_to_word256 x) ^ unat (uint256_to_word256 y) =
          u256_pow (uint256_to_word256 x) (uint256_to_word256 y)"
      using u256_pow_eq_pow by simp
    also have "... = 0"
      unfolding u256_pow_def Let_def uint256_word256_roundtrip word256_to_uint256_inv
      using even True by simp
    also have "... = uint256_to_word256 uint256_zero"
      using uint256_to_word256_zero by simp
    finally show ?thesis .
  qed
  from lhs rhs show ?thesis by simp
next
  case False
  let ?BL = "BitLen y"
  let ?Mu = "uint256_to_word256 x"

  obtain r1 m1 c1 where
    P1: "Exp_aux uint256_one x (z0 y) 64 ?BL = (r1, m1, c1)"
    by (cases "Exp_aux uint256_one x (z0 y) 64 ?BL") auto
  obtain r2 m2 c2 where
    P2: "Exp_aux r1 m1 (z1 y) 64 c1 = (r2, m2, c2)"
    by (cases "Exp_aux r1 m1 (z1 y) 64 c1") auto
  obtain r3 m3 c3 where
    P3: "Exp_aux r2 m2 (z2 y) 64 c2 = (r3, m3, c3)"
    by (cases "Exp_aux r2 m2 (z2 y) 64 c2") auto
  obtain r4 m4 c4 where
    P4: "Exp_aux r3 m3 (z3 y) 64 c3 = (r4, m4, c4)"
    by (cases "Exp_aux r3 m3 (z3 y) 64 c3") auto

  have lhs: "uint256_to_word256 (Exp x y) = uint256_to_word256 r4"
    unfolding Exp_def Let_def using False P1 P2 P3 P4
    by (auto split: prod.split)

  have eq1: "u256_pow_aux (1::u256) ?Mu (z0 y) 64 ?BL =
             (uint256_to_word256 r1, uint256_to_word256 m1, c1)"
    using P1 Exp_aux_equiv[of uint256_one x "z0 y" 64 ?BL] uint256_to_word256_one by auto
  have eq2: "u256_pow_aux (uint256_to_word256 r1) (uint256_to_word256 m1) (z1 y) 64 c1 =
             (uint256_to_word256 r2, uint256_to_word256 m2, c2)"
    using P2 Exp_aux_equiv[of r1 m1 "z1 y" 64 c1] by auto
  have eq3: "u256_pow_aux (uint256_to_word256 r2) (uint256_to_word256 m2) (z2 y) 64 c2 =
             (uint256_to_word256 r3, uint256_to_word256 m3, c3)"
    using P3 Exp_aux_equiv[of r2 m2 "z2 y" 64 c2] by auto
  have eq4: "u256_pow_aux (uint256_to_word256 r3) (uint256_to_word256 m3) (z3 y) 64 c3 =
             (uint256_to_word256 r4, uint256_to_word256 m4, c4)"
    using P4 Exp_aux_equiv[of r3 m3 "z3 y" 64 c3] by auto

  have r4_u256: "uint256_to_word256 r4 = u256_pow ?Mu (uint256_to_word256 y)"
    unfolding u256_pow_def Let_def uint256_word256_roundtrip word256_to_uint256_inv
    using False u256_lowbit_equiv eq1 eq2 eq3 eq4
    by (auto split: prod.split)

  have r4_final: "uint256_to_word256 r4 = ?Mu ^ unat (uint256_to_word256 y)"
    using r4_u256 u256_pow_eq_pow by simp

  show ?thesis unfolding lhs using r4_final by simp
qed

end
