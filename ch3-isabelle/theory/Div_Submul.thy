theory Div_Submul
  imports Div_Comparison Div_Normalization
begin

lemma submul_digit_balance:
  fixes x y q borrow :: u64
    and p s t :: "u64 \<times> u64"
  defines "p \<equiv> mul64 y q"
    and "s \<equiv> Sub64_borrow x borrow 0"
    and "t \<equiv> Sub64_borrow (fst s) (snd p) 0"
  shows "uint x - uint y * uint q - uint borrow =
    uint (fst t) - uint (fst p + snd s + snd t) * 2^64"
proof -
  have prod: "uint (fst p) * 2^64 + uint (snd p) = uint y * uint q"
    unfolding p_def by (rule mul64_spec)
  have sub1: "uint x - uint borrow = uint (fst s) - uint (snd s) * 2^64"
    using sub64_balance[of 0 x borrow] unfolding s_def by simp
  have sub2: "uint (fst s) - uint (snd p) = uint (fst t) - uint (snd t) * 2^64"
    using sub64_balance[of 0 "fst s" "snd p"] unfolding t_def by simp
  have total: "uint x - uint y * uint q - uint borrow =
    uint (fst t) - (uint (fst p) + uint (snd s) + uint (snd t)) * 2^64"
    using prod sub1 sub2 by (simp_all; linarith)
  have yb: "uint y \<le> 2^64 - 1" and qb: "uint q \<le> 2^64 - 1"
    and bb: "uint borrow \<le> 2^64 - 1"
    using uint_lt_2p64[of y] uint_lt_2p64[of q] uint_lt_2p64[of borrow] by linarith+
  have product_bound: "uint y * uint q \<le> ((2::int)^64 - 1) * (2^64 - 1)"
    by (rule mult_mono[OF yb qb]) simp_all
  have result_bound: "uint (fst t) < 2^64" by (rule uint_lt_2p64)
  have borrow_bound: "uint (fst p) + uint (snd s) + uint (snd t) < 2^64"
    using total product_bound bb result_bound uint_nonnegative[of x] by (simp_all; linarith)
  have borrow_ge: "0 \<le> uint (fst p) + uint (snd s) + uint (snd t)" by simp
  have normalized: "uint (fst p + snd s + snd t) =
      uint (fst p) + uint (snd s) + uint (snd t)"
    using mod_pos_pos_trivial[OF borrow_ge borrow_bound]
    by (simp add: uint_word_ariths mod_add_left_eq)
  show ?thesis using total normalized by simp
qed

definition limb_prefix :: "uint256 \<Rightarrow> nat \<Rightarrow> int" where
  "limb_prefix x n = (\<Sum>i<n. uint (getword x i) * (2^64)^i)"

lemma limb_prefix_zero [simp]: "limb_prefix x 0 = 0"
  by (simp add: limb_prefix_def)

lemma limb_prefix_Suc:
  "limb_prefix x (Suc n) = limb_prefix x n + uint (getword x n)*(2^64)^n"
  by (simp add: limb_prefix_def)

lemma limb_prefix_full:
  "limb_prefix x (dLen x) = uint256_to_int x"
  unfolding dLen_def
  by (auto simp: numeral_eq_Suc limb_prefix_Suc getword_def uint256_to_int_def Let_def int_shiftl_eq_mult)

lemma update_word_uint256_value:
  assumes "i < 4"
  shows "uint256_to_int (update_word_uint256 x i w) =
    uint256_to_int x + (uint w - uint (getword x i))*(2^64)^i"
proof -
  have "i=0 \<or> i=1 \<or> i=2 \<or> i=3" using assms by arith
  then show ?thesis
    by (auto simp: update_word_uint256_def getword_def uint256_to_int_def Let_def
      int_shiftl_eq_mult algebra_simps)
qed

lemma update_word_u4_value:
  assumes "i \<le> 4"
  shows "uint256_u4_to_int (update_word_u4 x u4 i w) =
    uint256_u4_to_int (x,u4) + (uint w - uint (getword_u x i u4))*(2^64)^i"
proof (cases "i=4")
  case True
  then show ?thesis
    by (simp add: update_word_u4_def uint256_u4_to_int_def getword_u_def algebra_simps)
next
  case False
  have lt: "i < 4" using assms False by simp
  show ?thesis
    using update_word_uint256_value[OF lt, of x w]
    by (simp add: update_word_u4_def False uint256_u4_to_int_def getword_u_def lt)
qed

lemma subMulTo_aux_balance:
  assumes n: "n \<le> dLen y" and bound: "dLen y+j \<le> 4"
    and out: "subMulTo_aux x u4 y q n j borrow = (b,x',u4')"
  shows "u4'=u4 \<and>
    uint256_to_int x' - uint b*(2^64)^(dLen y+j) =
    uint256_to_int x - uint borrow*(2^64)^(dLen y-n+j) -
      uint q*(2^64)^j*(limb_prefix y (dLen y)-limb_prefix y (dLen y-n))"
  using n out
proof (induction n arbitrary: x u4 borrow)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?i = "dLen y-Suc n"
  have nL: "n < dLen y" using Suc.prems(1) by simp
  have idx: "?i+j < 4" using bound Suc.prems(1) by arith
  have idx4: "?i+j \<noteq> 4" using idx by arith
  have next_idx: "dLen y-n = Suc ?i" using nL by arith
  obtain ph pl where mul: "mul64 (getword y ?i) q = (ph,pl)" by (cases "mul64 (getword y ?i) q") auto
  obtain s c1 where sub1: "Sub64_borrow (getword x (?i+j)) borrow 0 = (s,c1)"
    by (cases "Sub64_borrow (getword x (?i+j)) borrow 0") auto
  obtain t c2 where sub2: "Sub64_borrow s pl 0 = (t,c2)"
    by (cases "Sub64_borrow s pl 0") auto
  let ?x = "update_word_uint256 x (?i+j) t"
  let ?b = "ph+c1+c2"
  have step: "subMulTo_aux ?x u4 y q n j ?b = (b,x',u4')"
    using Suc.prems(2)
    by (simp only: subMulTo_aux.simps Let_def getword_u_def if_P[OF idx] mul sub1 sub2
      prod.case update_word_u4_def if_not_P[OF idx4])
  have IH: "u4'=u4 \<and>
    uint256_to_int x' - uint b*(2^64)^(dLen y+j) =
    uint256_to_int ?x - uint ?b*(2^64)^(dLen y-n+j) -
      uint q*(2^64)^j*(limb_prefix y (dLen y)-limb_prefix y (dLen y-n))"
    using Suc.IH[OF less_imp_le[OF nL] step] .
  have digit: "uint (getword x (?i+j)) - uint (getword y ?i)*uint q - uint borrow =
      uint t - uint ?b*2^64"
    using submul_digit_balance[of "getword x (?i+j)" "getword y ?i" q borrow]
    by (simp add: mul sub1 sub2)
  note scaled = arg_cong[where f="\<lambda>v::int. v*(2^64)^(?i+j)", OF digit]
  note update = update_word_uint256_value[OF idx, of x t]
  have pref: "limb_prefix y (dLen y-n) = limb_prefix y ?i + uint (getword y ?i)*(2^64)^?i"
    by (simp add: next_idx limb_prefix_Suc)
  have balance:
    "uint256_to_int ?x - uint ?b*(2^64)^(dLen y-n+j) -
      uint q*(2^64)^j*(limb_prefix y (dLen y)-limb_prefix y (dLen y-n)) =
     uint256_to_int x - uint borrow*(2^64)^(?i+j) -
      uint q*(2^64)^j*(limb_prefix y (dLen y)-limb_prefix y ?i)"
    using scaled
    unfolding update next_idx limb_prefix_Suc power_Suc power_add
    by (simp only: algebra_simps; algebra)
  show ?case using IH balance by simp

qed

lemma subMulTo_correct:
  assumes "dLen y+j \<le> 4" and "subMulTo x u4 y j q = (b,x',u4')"
  shows "u4'=u4 \<and>
    uint256_to_int x' - uint b*(2^64)^(dLen y+j) =
      uint256_to_int x - uint q*uint256_to_int y*(2^64)^j"
  using subMulTo_aux_balance[OF order_refl assms(1), of x u4 q 0 b x' u4'] assms(2)
  by (simp add: subMulTo_def limb_prefix_full algebra_simps)
lemma addTo_aux_balance:
  assumes n: "n \<le> dLen y" and bound: "dLen y+j \<le> 4" and carry: "uint carry < 2"
    and out: "addTo_aux x u4 y n j carry = (c,x',u4')"
  shows "u4'=u4 \<and> uint c < 2 \<and>
    uint256_to_int x' + uint c*(2^64)^(dLen y+j) =
    uint256_to_int x + uint carry*(2^64)^(dLen y-n+j) +
      (2^64)^j*(limb_prefix y (dLen y)-limb_prefix y (dLen y-n))"
  using n carry out
proof (induction n arbitrary: x u4 carry)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?i = "dLen y-Suc n"
  have nL: "n < dLen y" using Suc.prems(1) by simp
  have idx: "?i+j < 4" using bound Suc.prems(1) by arith
  have idx4: "?i+j \<noteq> 4" using idx by arith
  have next_idx: "dLen y-n = Suc ?i" using nL by arith
  obtain s c1 where add: "Add64_carry (getword x (?i+j)) (getword y ?i) carry = (s,c1)"
    by (cases "Add64_carry (getword x (?i+j)) (getword y ?i) carry") auto
  let ?x = "update_word_uint256 x (?i+j) s"
  have c1: "uint c1 < 2"
    using add64_carry_snd_lt[of "getword x (?i+j)" "getword y ?i" carry] by (simp add: add)
  have step: "addTo_aux ?x u4 y n j c1 = (c,x',u4')"
    using Suc.prems(3)
    by (simp only: addTo_aux.simps Let_def getword_u_def if_P[OF idx] add
      prod.case update_word_u4_def if_not_P[OF idx4])
  have IH: "u4'=u4 \<and> uint c < 2 \<and>
    uint256_to_int x' + uint c*(2^64)^(dLen y+j) =
    uint256_to_int ?x + uint c1*(2^64)^(dLen y-n+j) +
      (2^64)^j*(limb_prefix y (dLen y)-limb_prefix y (dLen y-n))"
    using Suc.IH[OF less_imp_le[OF nL] c1 step] .
  have digit: "uint s + uint c1*2^64 =
      uint (getword x (?i+j)) + uint (getword y ?i) + uint carry"
    using add64_carry_spec[OF Suc.prems(2), of "getword x (?i+j)" "getword y ?i"]
    by (simp add: add)
  note scaled = arg_cong[where f="\<lambda>v::int. v*(2^64)^(?i+j)", OF digit]
  note update = update_word_uint256_value[OF idx, of x s]
  have balance:
    "uint256_to_int ?x + uint c1*(2^64)^(dLen y-n+j) +
      (2^64)^j*(limb_prefix y (dLen y)-limb_prefix y (dLen y-n)) =
     uint256_to_int x + uint carry*(2^64)^(?i+j) +
      (2^64)^j*(limb_prefix y (dLen y)-limb_prefix y ?i)"
    using scaled
    unfolding update next_idx limb_prefix_Suc power_Suc power_add
    by (simp only: algebra_simps; algebra)
  show ?case using IH balance by simp
qed

lemma addTo_correct:
  assumes "dLen y+j \<le> 4" and "addTo x u4 y j = (c,x',u4')"
  shows "u4'=u4 \<and> uint c < 2 \<and>
    uint256_to_int x' + uint c*(2^64)^(dLen y+j) =
      uint256_to_int x + uint256_to_int y*(2^64)^j"
  using addTo_aux_balance[OF order_refl assms(1), of 0 x u4 c x' u4'] assms(2)
  by (simp add: addTo_def limb_prefix_full algebra_simps)

end
