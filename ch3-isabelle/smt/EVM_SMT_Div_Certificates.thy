theory EVM_SMT_Div_Certificates
  imports EVM_SMT_Compare_Certificates EVM_SMT_Substitution
begin

text \<open>The division-family expressions retain their two production function
  symbols. The interpretation parameter below makes their meaning explicit.
  A certificate with the mathematical interpretation does not assert that an
  arbitrary Z3 interpretation, or the separate Knuth implementation, satisfies
  the corresponding arithmetic specification.\<close>

lemma packed_zero [simp]: "uint256_to_int uint256_zero = 0"
  by (simp add: pack_horner uint256_zero_def)

lemma pack_zero_iff [simp]:
  "(uint256_to_int x = 0) = (x = uint256_zero)"
proof -
  have z: "uint256_to_int uint256_zero = 0"
    by (simp add: pack_horner uint256_zero_def)
  show ?thesis
    using smt_int_to_uint256_pack[of x] smt_int_to_uint256_pack[of uint256_zero] z
    by metis
qed

lemma pack_eq_iff [simp]:
  "(uint256_to_int x = uint256_to_int y) = (x = y)"
  using smt_int_to_uint256_pack[of x] smt_int_to_uint256_pack[of y] by metis

lemma int_to_uint256_normalized:
  "int_to_uint256 (bv_norm 256 k) = int_to_uint256 k"
proof -
  have low: "a mod 18446744073709551616 = take_bit 64 a" for a :: int
    by (simp add: take_bit_eq_mod)
  show ?thesis
    by (rule uint256.equality)
       (simp_all add: int_to_uint256_def word_of_int_eq_iff bv_norm_eq_take_bit
          shiftr_def low drop_bit_take_bit take_bit_take_bit)
qed

lemma pack_int_to_uint256:
  "uint256_to_int (int_to_uint256 k) = bv_norm 256 k"
proof -
  have "uint256_to_int (int_to_uint256 (bv_norm 256 k)) = bv_norm 256 k"
    by (rule uint256_to_int_int_to_uint256) (rule bv_norm_nonnegative | rule bv_norm_less)+
  then show ?thesis by (simp add: int_to_uint256_normalized)
qed

lemma norm128_uint [simp]: "bv_norm 128 (uint (x :: u64)) = uint x"
  by (rule bv_norm_small) (use limb_uint_range[of x] in auto)

lemma pack_high192:
  "bv_norm 192 (uint256_to_int x div 2^64) =
    uint (z1 x) + 2^64 * (uint (z2 x) + 2^64 * uint (z3 x))"
proof -
  have lo: "0 \<le> uint (z1 x) + 2^64 * (uint (z2 x) + 2^64 * uint (z3 x))" by simp
  have hi: "uint (z1 x) + 2^64 * (uint (z2 x) + 2^64 * uint (z3 x)) < (2::int)^192"
    using limb_uint_range[of "z1 x"] limb_uint_range[of "z2 x"]
      limb_uint_range[of "z3 x"] by (simp_all; linarith)
  show ?thesis
    by (simp only: pack_horner limb_div bv_norm_small[OF lo hi])
qed

lemma pack_isuint64:
  "(0 = bv_norm 192 (uint256_to_int x div 2^64)) = Isuint64 x"
  unfolding pack_high192 Isuint64_def
  using uint_nonnegative[of "z1 x"] uint_nonnegative[of "z2 x"] uint_nonnegative[of "z3 x"]
  by (auto simp: word_uint_eq_iff; linarith)

lemmas pack_isuint64_simp = pack_isuint64[simplified]

lemma isuint64_pack:
  "Isuint64 x \<Longrightarrow> uint256_to_int x = uint (z0 x)"
  by (simp add: Isuint64_def pack_horner)

lemma pack_small_isuint64:
  "uint256_to_int x < 2^64 \<Longrightarrow> Isuint64 x"
proof -
  assume small: "uint256_to_int x < 2^64"
  have "uint256_to_int x div 2^64 = 0"
    by (rule div_pos_pos_trivial[OF pack_nonnegative small])
  then show ?thesis using pack_isuint64[of x] by simp
qed

lemma bv_udiv64_normalized:
  assumes "0 \<le> a" "a < 2^64" "0 < b"
  shows "bv_norm 64 (a div b) = a div b"
proof -
  have lo: "0 \<le> a div b" using assms by (simp add: pos_imp_zdiv_nonneg_iff)
  have le: "a div b \<le> a"
    using zdiv_mono2[OF assms(1), of 1 b] assms(3) by simp
  show ?thesis using assms(2) le by (intro bv_norm_small lo) linarith
qed

lemma bv_urem64_normalized:
  assumes "0 \<le> a" "a < 2^64" "0 < b"
  shows "bv_norm 64 (a mod b) = a mod b"
proof -
  have lo: "0 \<le> a mod b" using assms by simp
  have le: "a mod b \<le> a" by (rule zmod_le_nonneg_dividend[OF assms(1)])
  show ?thesis using assms(2) le by (intro bv_norm_small lo) linarith
qed

definition div_production_model :: "(smt_uf \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow>
    uint256 \<Rightarrow> uint256 \<Rightarrow> int" where
  "div_production_model uf x y =
    (if y = uint256_zero \<or> uint256_lt x y then 0
     else if x = y then 1
     else if Isuint64 x then
       bv_norm 64 (if uint (z0 y) = 0 then 2^128 - 1 else uint (z0 x) div uint (z0 y))
     else bv_norm 256 (uf HolimanUDiv (uint256_to_int x) (uint256_to_int y)))"

definition mod_production_model :: "(smt_uf \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow>
    uint256 \<Rightarrow> uint256 \<Rightarrow> int" where
  "mod_production_model uf x y =
    (if y = uint256_zero \<or> x = y then 0
     else if uint256_lt x y then uint256_to_int x
     else if Isuint64 x then
       bv_norm 64 (if uint (z0 y) = 0 then uint (z0 x) else uint (z0 x) mod uint (z0 y))
     else bv_norm 256 (uf HolimanURem (uint256_to_int x) (uint256_to_int y)))"


lemma div_zero_eval:
  "smt_eval_with uf (evm_inputs x y) generated_div_node_10 =
    Some (BoolV (y = uint256_zero))"
  by (cases y) (simp add: generated_div_defs evm_inputs_def uint256_zero_def uint_0_iff conj_assoc)

lemma div_lt_eval:
  "smt_eval_with uf (evm_inputs x y) generated_div_node_41 =
    Some (BoolV (uint256_lt x y))"
  unfolding smt_lt256_correct[symmetric] smt_lt256_def
  by (simp add: generated_div_defs evm_inputs_def Let_def
      bv_norm_nested bv_norm_sub_left smt_sub64_normalized)

lemma div_eq_eval:
  "smt_eval_with uf (evm_inputs x y) generated_div_node_48 = Some (BoolV (x = y))"
  by (simp add: generated_div_defs evm_inputs_def uint256_eq_limbs conj_assoc)

lemma div_is64_eval:
  "smt_eval_with uf (evm_inputs x y) generated_div_node_52 = Some (BoolV (Isuint64 x))"
  by (simp add: generated_div_defs evm_inputs_def pack_isuint64_simp)

lemma div_fast_eval:
  "smt_eval_with uf (evm_inputs x y) generated_div_node_57 = Some (BVV 256
    (bv_norm 64 (if uint (z0 y) = 0 then 2^128 - 1 else uint (z0 x) div uint (z0 y))))"
  by (simp add: generated_div_defs evm_inputs_def bv_norm_nested)

lemma div_uf_eval:
  "smt_eval_with uf (evm_inputs x y) generated_div_node_58 = Some (BVV 256
    (bv_norm 256 (uf HolimanUDiv (uint256_to_int x) (uint256_to_int y))))"
  by (simp add: generated_div_defs evm_inputs_def)

lemma exported_div_model:
  "smt_eval_with uf (evm_inputs x y) exported_div =
    Some (BVV 256 (div_production_model uf x y))"
  by (simp add: exported_div_def generated_div_node_61_def generated_div_node_60_def
      generated_div_node_59_def generated_div_node_42_def generated_div_node_43_def
      generated_div_node_49_def div_zero_eval div_lt_eval div_eq_eval div_is64_eval
      div_fast_eval div_uf_eval div_production_model_def)

lemma mod_zero_structure: "generated_mod_node_10 = generated_div_node_10"
  by (simp add: generated_mod_defs generated_div_defs)
lemma mod_lt_structure: "generated_mod_node_48 = generated_div_node_41"
  by (simp add: generated_mod_defs generated_div_defs)
lemma mod_eq_structure: "generated_mod_node_20 = generated_div_node_48"
  by (simp add: generated_mod_defs generated_div_defs)
lemma mod_is64_structure: "generated_mod_node_51 = generated_div_node_52"
  by (simp add: generated_mod_defs generated_div_defs)

lemma mod_fast_eval:
  "smt_eval_with uf (evm_inputs x y) generated_mod_node_56 = Some (BVV 256
    (bv_norm 64 (if uint (z0 y) = 0 then uint (z0 x) else uint (z0 x) mod uint (z0 y))))"
  by (simp add: generated_mod_defs evm_inputs_def bv_norm_nested)

lemma mod_uf_eval:
  "smt_eval_with uf (evm_inputs x y) generated_mod_node_57 = Some (BVV 256
    (bv_norm 256 (uf HolimanURem (uint256_to_int x) (uint256_to_int y))))"
  by (simp add: generated_mod_defs evm_inputs_def)

lemma exported_mod_model:
  "smt_eval_with uf (evm_inputs x y) exported_mod =
    Some (BVV 256 (mod_production_model uf x y))"
  by (simp add: exported_mod_def generated_mod_node_60_def generated_mod_node_59_def
      generated_mod_node_58_def generated_mod_node_21_def generated_mod_node_22_def
      generated_mod_node_11_def mod_zero_structure mod_lt_structure mod_eq_structure
      mod_is64_structure div_zero_eval div_lt_eval div_eq_eval div_is64_eval
      mod_fast_eval mod_uf_eval mod_production_model_def evm_inputs_def)

lemma bv_udiv_normalized:
  assumes "0 \<le> a" "a < 2^w" "0 < b"
  shows "bv_norm w (a div b) = a div b"
proof -
  have lo: "0 \<le> a div b" using assms by (simp add: pos_imp_zdiv_nonneg_iff)
  have le: "a div b \<le> a"
    using zdiv_mono2[OF assms(1), of 1 b] assms(3) by simp
  show ?thesis using assms(2) le by (intro bv_norm_small lo) linarith
qed

lemma div_production_mathematical:
  "div_production_model mathematical_uf x y =
    (if y = uint256_zero then 0 else uint256_to_int x div uint256_to_int y)"
proof (cases "y = uint256_zero")
  case True then show ?thesis by (simp add: div_production_model_def)
next
  case False
  have ypos: "0 < uint256_to_int y" using False pack_nonnegative[of y] pack_zero_iff[of y] by linarith
  show ?thesis
  proof (cases "uint256_lt x y")
    case True
    then have "uint256_to_int x div uint256_to_int y = 0"
      by (intro div_pos_pos_trivial pack_nonnegative) (simp add: uint256_lt_int)
    with True False show ?thesis by (simp add: div_production_model_def)
  next
    case not_lt: False
    have le: "uint256_to_int y \<le> uint256_to_int x" using not_lt by (simp add: uint256_lt_int)
    show ?thesis
    proof (cases "x = y")
      case True
      with False ypos not_lt show ?thesis by (simp add: div_production_model_def)
    next
      case not_eq: False
      show ?thesis
      proof (cases "Isuint64 x")
        case True
        have xp: "uint256_to_int x = uint (z0 x)" by (rule isuint64_pack[OF True])
        have ys: "Isuint64 y"
          by (rule pack_small_isuint64) (use le limb_uint_range[of "z0 x"] xp in linarith)
        have yp: "uint256_to_int y = uint (z0 y)" by (rule isuint64_pack[OF ys])
        have norm: "bv_norm 64 (uint (z0 x) div uint (z0 y)) = uint (z0 x) div uint (z0 y)"
          by (rule bv_udiv64_normalized) (use limb_uint_range[of "z0 x"] ypos yp in auto)
        show ?thesis using False not_lt not_eq True ypos norm
          by (simp add: div_production_model_def xp yp)
      next
        case False
        have norm: "bv_norm 256 (uint256_to_int x div uint256_to_int y) =
            uint256_to_int x div uint256_to_int y"
          by (rule bv_udiv_normalized) (rule pack_nonnegative | rule pack_less | rule ypos)+
        show ?thesis using False not_lt not_eq ypos norm
          by (simp add: div_production_model_def)
      qed
    qed
  qed
qed

lemma mod_production_mathematical:
  "mod_production_model mathematical_uf x y =
    (if y = uint256_zero then 0 else uint256_to_int x mod uint256_to_int y)"
proof (cases "y = uint256_zero")
  case True then show ?thesis by (simp add: mod_production_model_def)
next
  case False
  have ypos: "0 < uint256_to_int y" using False pack_nonnegative[of y] pack_zero_iff[of y] by linarith
  have normrem: "bv_norm 256 (uint256_to_int x mod uint256_to_int y) =
      uint256_to_int x mod uint256_to_int y"
  proof (rule bv_norm_small)
    show "0 \<le> uint256_to_int x mod uint256_to_int y" using ypos by simp
    show "uint256_to_int x mod uint256_to_int y < 2^256"
      using pos_mod_bound[OF ypos, of "uint256_to_int x"] pack_less[of y] by linarith
  qed
  show ?thesis
  proof (cases "x = y")
    case True with False show ?thesis by (simp add: mod_production_model_def)
  next
    case not_eq: False
    show ?thesis
    proof (cases "uint256_lt x y")
      case True
      then have "uint256_to_int x mod uint256_to_int y = uint256_to_int x"
        by (intro mod_pos_pos_trivial pack_nonnegative) (simp add: uint256_lt_int)
      with False not_eq True show ?thesis by (simp add: mod_production_model_def)
    next
      case not_lt: False
      have le: "uint256_to_int y \<le> uint256_to_int x" using not_lt by (simp add: uint256_lt_int)
      show ?thesis
      proof (cases "Isuint64 x")
        case True
        have xp: "uint256_to_int x = uint (z0 x)" by (rule isuint64_pack[OF True])
        have ys: "Isuint64 y"
          by (rule pack_small_isuint64) (use le limb_uint_range[of "z0 x"] xp in linarith)
        have yp: "uint256_to_int y = uint (z0 y)" by (rule isuint64_pack[OF ys])
        have norm: "bv_norm 64 (uint (z0 x) mod uint (z0 y)) = uint (z0 x) mod uint (z0 y)"
          by (rule bv_urem64_normalized) (use limb_uint_range[of "z0 x"] ypos yp in auto)
        show ?thesis using False not_lt not_eq True ypos norm
          by (simp add: mod_production_model_def xp yp)
      next
        case False
        show ?thesis using False not_lt not_eq ypos normrem
          by (simp add: mod_production_model_def)
      qed
    qed
  qed
qed

theorem exported_div_mathematical:
  "smt_eval (evm_inputs x y) exported_div = Some (BVV 256
    (if y = uint256_zero then 0 else uint256_to_int x div uint256_to_int y))"
  by (simp add: exported_div_model div_production_mathematical)

theorem exported_mod_mathematical:
  "smt_eval (evm_inputs x y) exported_mod = Some (BVV 256
    (if y = uint256_zero then 0 else uint256_to_int x mod uint256_to_int y))"
  by (simp add: exported_mod_model mod_production_mathematical)

definition signed_abs_word :: "uint256 \<Rightarrow> uint256" where
  "signed_abs_word x =
    (if bv_norm 1 (uint256_to_int x div 2^255) = 1 then Neg x else x)"

lemma packed_sign_extract:
  "(bv_norm 1 (uint256_to_int x div 2^255) = 1) = (2^255 \<le> uint256_to_int x)"
proof -
  have lo: "0 \<le> uint256_to_int x div (2::int)^255"
    by (simp add: pack_nonnegative pos_imp_zdiv_nonneg_iff)
  have hi: "uint256_to_int x div (2::int)^255 < 2"
    using pack_less[of x] by (simp add: div_less_iff_less_mult)
  have pos: "(0 < uint256_to_int x div (2::int)^255) = (2^255 \<le> uint256_to_int x)"
    using pack_nonnegative[of x] by (simp add: pos_imp_zdiv_pos_iff)
  have quo: "(uint256_to_int x div (2::int)^255 = 1) = (2^255 \<le> uint256_to_int x)"
    using lo hi pos by linarith
  show ?thesis using lo hi quo by (simp add: bv_norm_def)
qed

lemma signed_abs_word_alt:
  "signed_abs_word x = (if 2^255 \<le> uint256_to_int x then Neg x else x)"
  unfolding signed_abs_word_def by (simp only: packed_sign_extract)

lemma packed_signed:
  "sint (uint256_to_word256 x) = bv_signed 256 (uint256_to_int x)"
  by (simp add: packed_word_sint sign_is_negative_packed bv_signed_def)

lemma signed_abs_pack:
  "uint256_to_int (signed_abs_word x) = abs (sint (uint256_to_word256 x))"
proof (cases "uint256_to_int x < 2^255")
  case True
  then show ?thesis
    by (simp add: signed_abs_word_alt packed_signed bv_signed_def pack_nonnegative)
next
  case False
  have nz: "uint256_to_int x \<noteq> 0" using False by auto
  have neg: "uint256_to_int x - 2^256 < 0" using pack_less[of x] by linarith
  show ?thesis using False nz neg pack_range[of x]
    by (simp add: signed_abs_word_alt packed_signed bv_signed_def
        pack_neg bv_norm_def zmod_zminus1_eq_if)
qed

lemma signed_abs_zero [simp]:
  "(signed_abs_word x = uint256_zero) = (x = uint256_zero)"
  using signed_abs_pack[of x] pack_range[of x]
  by (auto simp: packed_signed bv_signed_def split: if_splits)

lemma sdiv_quotient_structure:
  "generated_sdiv_node_133 =
    smt_substitute (\<lambda>w n. if n = 0 then generated_sdiv_node_85 else generated_sdiv_node_44)
      exported_div"
  by (simp add: generated_sdiv_defs generated_div_defs)

lemma smod_remainder_structure:
  "generated_smod_node_131 =
    smt_substitute (\<lambda>w n. if n = 0 then generated_smod_node_84 else generated_smod_node_43)
      exported_mod"
  by (simp add: generated_smod_defs generated_mod_defs)

lemma addmod_remainder_structure:
  "generated_addmod_node_68 =
    smt_substitute (\<lambda>w n. if n = 0 then generated_addmod_node_21 else generated_addmod_node_1)
      exported_mod"
  by (simp add: generated_addmod_defs generated_mod_defs)

lemma sdiv_abs_first:
  "smt_eval_with uf (evm_inputs x y) generated_sdiv_node_85 =
    Some (BVV 256 (uint256_to_int (signed_abs_word x)))"
  unfolding signed_abs_word_def Neg_def smt_sub256_correct[symmetric] smt_sub256_def
  by (simp add: generated_sdiv_defs evm_inputs_def uint256_zero_def Let_def
      bv_norm_nested bv_norm_sub_left four_normalized_concat
      four_normalized_concat_simp smt_sub64_normalized)

lemma sdiv_abs_second:
  "smt_eval_with uf (evm_inputs x y) generated_sdiv_node_44 =
    Some (BVV 256 (uint256_to_int (signed_abs_word y)))"
  unfolding signed_abs_word_def Neg_def smt_sub256_correct[symmetric] smt_sub256_def
  by (simp add: generated_sdiv_defs evm_inputs_def uint256_zero_def Let_def
      bv_norm_nested bv_norm_sub_left four_normalized_concat
      four_normalized_concat_simp smt_sub64_normalized)

lemma smod_abs_first_structure:
  "generated_smod_node_84 = generated_sdiv_node_85"
  by (simp add: generated_smod_defs generated_sdiv_defs)

lemma smod_abs_second_structure:
  "generated_smod_node_43 = generated_sdiv_node_44"
  by (simp add: generated_smod_defs generated_sdiv_defs)

lemma sdiv_quotient_eval:
  "smt_eval_with uf (evm_inputs x y) generated_sdiv_node_133 =
    Some (BVV 256 (div_production_model uf (signed_abs_word x) (signed_abs_word y)))"
  unfolding sdiv_quotient_structure
  apply (subst smt_eval_substitute_binary256[OF exported_div_inputs,
    where x="uint256_to_int (signed_abs_word x)" and y="uint256_to_int (signed_abs_word y)"])
    apply (simp add: sdiv_abs_first)
   apply (simp add: sdiv_abs_second)
  apply (fold evm_inputs_def)
  apply (rule exported_div_model)
  done

lemma smod_remainder_eval:
  "smt_eval_with uf (evm_inputs x y) generated_smod_node_131 =
    Some (BVV 256 (mod_production_model uf (signed_abs_word x) (signed_abs_word y)))"
  unfolding smod_remainder_structure
  apply (subst smt_eval_substitute_binary256[OF exported_mod_inputs,
    where x="uint256_to_int (signed_abs_word x)" and y="uint256_to_int (signed_abs_word y)"])
    apply (simp add: smod_abs_first_structure sdiv_abs_first)
   apply (simp add: smod_abs_second_structure sdiv_abs_second)
  apply (fold evm_inputs_def)
  apply (rule exported_mod_model)
  done

lemma packed_sign_extract_negative:
  "(bv_norm 1 (uint256_to_int x div 2^255) = 1) = (sint (uint256_to_word256 x) < 0)"
  unfolding packed_sign_extract packed_signed bv_signed_def
  using pack_range[of x] by auto

lemmas packed_sign_extract_negative_simp = packed_sign_extract_negative[simplified]

lemma sdiv_sign_first:
  "smt_eval_with uf (evm_inputs x y) generated_sdiv_node_6 =
    Some (BoolV (sint (uint256_to_word256 x) < 0))"
proof -
  have eval: "smt_eval_with uf (evm_inputs x y) generated_sdiv_node_6 =
      Some (BoolV (1 = bv_norm 1 (uint256_to_int x div 2^255)))"
    by (simp add: generated_sdiv_node_6_def generated_sdiv_node_3_def
        generated_sdiv_node_5_def generated_sdiv_node_4_def evm_inputs_def)
  have sign: "(1 = bv_norm 1 (uint256_to_int x div 2^255)) =
      (sint (uint256_to_word256 x) < 0)"
    by (subst eq_commute[of "1::int" "bv_norm 1 (uint256_to_int x div 2^255)"])
       (rule packed_sign_extract_negative)
  show ?thesis using eval by (simp only: sign)
qed

lemma sdiv_sign_second:
  "smt_eval_with uf (evm_inputs x y) generated_sdiv_node_8 =
    Some (BoolV (sint (uint256_to_word256 y) < 0))"
proof -
  have eval: "smt_eval_with uf (evm_inputs x y) generated_sdiv_node_8 =
      Some (BoolV (1 = bv_norm 1 (uint256_to_int y div 2^255)))"
    by (simp add: generated_sdiv_node_8_def generated_sdiv_node_3_def
        generated_sdiv_node_7_def generated_sdiv_node_1_def evm_inputs_def)
  have sign: "(1 = bv_norm 1 (uint256_to_int y div 2^255)) =
      (sint (uint256_to_word256 y) < 0)"
    by (subst eq_commute[of "1::int" "bv_norm 1 (uint256_to_int y div 2^255)"])
       (rule packed_sign_extract_negative)
  show ?thesis using eval by (simp only: sign)
qed

lemma sdiv_zero_guard:
  "smt_eval_with uf (evm_inputs x y) generated_sdiv_node_2 =
    Some (BoolV (y = uint256_zero))"
proof -
  have eval: "smt_eval_with uf (evm_inputs x y) generated_sdiv_node_2 =
      Some (BoolV (0 = uint256_to_int y))"
    by (simp add: generated_sdiv_node_2_def generated_sdiv_node_0_def
        generated_sdiv_node_1_def evm_inputs_def)
  have zero: "(0 = uint256_to_int y) = (y = uint256_zero)"
    by (subst eq_commute[of "0::int" "uint256_to_int y"]) (rule pack_zero_iff)
  show ?thesis using eval by (simp only: zero)
qed

lemma division_model_normalized:
  "bv_norm 256 (div_production_model uf x y) = div_production_model uf x y"
  using smt_eval_with_wellformed[OF exported_div_model[where uf=uf and x=x and y=y]]
  by (auto intro: bv_norm_small)

lemma remainder_model_normalized:
  "bv_norm 256 (mod_production_model uf x y) = mod_production_model uf x y"
  using smt_eval_with_wellformed[OF exported_mod_model[where uf=uf and x=x and y=y]]
  by (auto intro: bv_norm_small)

lemma exported_sdiv_signed:
  "smt_eval (evm_inputs x y) exported_sdiv = Some (BVV 256
    (if y = uint256_zero then 0 else bv_norm 256
      (if (sint (uint256_to_word256 x) < 0) = (sint (uint256_to_word256 y) < 0)
       then abs (sint (uint256_to_word256 x)) div abs (sint (uint256_to_word256 y))
       else - (abs (sint (uint256_to_word256 x)) div abs (sint (uint256_to_word256 y))))))"
proof -
  have norm: "bv_norm 256
      (if y = uint256_zero then 0 else
        abs (sint (uint256_to_word256 x)) div abs (sint (uint256_to_word256 y))) =
      (if y = uint256_zero then 0 else
        abs (sint (uint256_to_word256 x)) div abs (sint (uint256_to_word256 y)))"
    using division_model_normalized[of mathematical_uf "signed_abs_word x" "signed_abs_word y"]
    by (simp only: div_production_mathematical signed_abs_pack signed_abs_zero)
  show ?thesis using norm
    by (cases "y = uint256_zero"; cases "(sint (uint256_to_word256 x) < 0) = (sint (uint256_to_word256 y) < 0)")
       (simp_all add: exported_sdiv_def generated_sdiv_node_136_def
         generated_sdiv_node_135_def generated_sdiv_node_134_def generated_sdiv_node_9_def
         generated_sdiv_node_0_def sdiv_quotient_eval sdiv_sign_first sdiv_sign_second
         sdiv_zero_guard div_production_mathematical signed_abs_pack)
qed

lemma smod_sign_structure: "generated_smod_node_6 = generated_sdiv_node_6"
  by (simp add: generated_smod_defs generated_sdiv_defs)

lemma smod_zero_guard_structure: "generated_smod_node_2 = generated_sdiv_node_2"
  by (simp add: generated_smod_defs generated_sdiv_defs)

lemma exported_smod_signed:
  "smt_eval (evm_inputs x y) exported_smod = Some (BVV 256
    (if y = uint256_zero then 0 else bv_norm 256
      (if sint (uint256_to_word256 x) < 0
       then - (abs (sint (uint256_to_word256 x)) mod abs (sint (uint256_to_word256 y)))
       else abs (sint (uint256_to_word256 x)) mod abs (sint (uint256_to_word256 y)))))"
proof -
  have norm: "bv_norm 256
      (if y = uint256_zero then 0 else
        abs (sint (uint256_to_word256 x)) mod abs (sint (uint256_to_word256 y))) =
      (if y = uint256_zero then 0 else
        abs (sint (uint256_to_word256 x)) mod abs (sint (uint256_to_word256 y)))"
    using remainder_model_normalized[of mathematical_uf "signed_abs_word x" "signed_abs_word y"]
    by (simp only: mod_production_mathematical signed_abs_pack signed_abs_zero)
  show ?thesis using norm
    by (cases "y = uint256_zero"; cases "sint (uint256_to_word256 x) < 0")
       (simp_all add: exported_smod_def generated_smod_node_134_def
         generated_smod_node_133_def generated_smod_node_132_def generated_smod_node_0_def
         smod_remainder_eval smod_sign_structure smod_zero_guard_structure
         sdiv_sign_first sdiv_zero_guard mod_production_mathematical signed_abs_pack)
qed

definition hol_sdiv_result :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
  "hol_sdiv_result x y = (if y = uint256_zero then uint256_zero else
    let d = sint (uint256_to_word256 y); n = sint (uint256_to_word256 x);
        min_int = - (2^255)
    in if n = min_int \<and> d = -1 then int_to_uint256 min_int
       else if d < 0 then
         if n < 0 then int_to_uint256 ((-1*n) div (-1*d))
         else int_to_uint256 (-1*(n div (-1*d)))
       else if n < 0 then int_to_uint256 (-1*((-1*n) div d))
       else int_to_uint256 (n div d))"

definition hol_smod_result :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
  "hol_smod_result x y = (if y = uint256_zero then uint256_zero else
    let d = sint (uint256_to_word256 y); n = sint (uint256_to_word256 x)
    in if d < 0 then
         if n < 0 then int_to_uint256 (-1*((-1*n) mod (-1*d)))
         else int_to_uint256 (n mod (-1*d))
       else if n < 0 then int_to_uint256 (-1*((-1*n) mod d))
       else int_to_uint256 (n mod d))"

text \<open>The preceding result functions spell out the arithmetic lambdas used
  by the existing SDIV and SMOD dispatcher branches, with sintFromW256 unfolded
  to sint. They do not replace those branches or the separate limb helpers.\<close>

theorem exported_sdiv_correct:
  "smt_eval (evm_inputs x y) exported_sdiv =
    Some (BVV 256 (uint256_to_int (hol_sdiv_result x y)))"
  unfolding exported_sdiv_signed hol_sdiv_result_def Let_def
  by (auto simp: pack_int_to_uint256 packed_zero abs_if
      bv_norm_def split: if_splits)

theorem exported_smod_correct:
  "smt_eval (evm_inputs x y) exported_smod =
    Some (BVV 256 (uint256_to_int (hol_smod_result x y)))"
  unfolding exported_smod_signed hol_smod_result_def Let_def
  by (auto simp: pack_int_to_uint256 packed_zero abs_if
      split: if_splits)

lemma norm257_pack [simp]: "bv_norm 257 (uint256_to_int x) = uint256_to_int x"
  by (rule bv_norm_small) (use pack_range[of x] in auto)

lemma packed_sum_range:
  "0 \<le> uint256_to_int x + uint256_to_int y"
  "uint256_to_int x + uint256_to_int y < (2::int)^257"
proof -
  show "0 \<le> uint256_to_int x + uint256_to_int y"
    using pack_nonnegative[of x] pack_nonnegative[of y] by linarith
  show "uint256_to_int x + uint256_to_int y < (2::int)^257"
    using pack_less[of x] pack_less[of y] by (simp_all; linarith)
qed

lemma norm257_sum [simp]:
  "bv_norm 257 (uint256_to_int x + uint256_to_int y) = uint256_to_int x + uint256_to_int y"
  by (rule bv_norm_small) (rule packed_sum_range)+

lemma packed_sum_no_carry:
  "(0 = bv_norm 1 ((uint256_to_int x + uint256_to_int y) div 2^256)) =
    (uint256_to_int x + uint256_to_int y < 2^256)"
proof -
  let ?s = "uint256_to_int x + uint256_to_int y"
  have lo: "0 \<le> ?s div (2::int)^256"
    using packed_sum_range(1)[of x y] by (simp add: pos_imp_zdiv_nonneg_iff)
  have hi: "?s div (2::int)^256 < 2"
    using packed_sum_range(2)[of x y] by (simp add: div_less_iff_less_mult)
  have pos: "(0 < ?s div (2::int)^256) = (2^256 \<le> ?s)"
    using packed_sum_range(1)[of x y] by (simp add: pos_imp_zdiv_pos_iff)
  have quo: "(?s div (2::int)^256 = 0) = (?s < 2^256)"
    using lo hi pos by linarith
  show ?thesis using lo hi quo by (auto simp: bv_norm_def)
qed

lemmas packed_sum_no_carry_simp = packed_sum_no_carry[simplified]

lemma addmod_sum_low_eval:
  "smt_eval_with uf (evm_inputs3 x y m) generated_addmod_node_21 =
    Some (BVV 256 (uint256_to_int (int_to_uint256 (uint256_to_int x + uint256_to_int y))))"
  by (simp add: generated_addmod_defs evm_inputs3_def pack_int_to_uint256 bv_norm_nested)

lemma addmod_modulus_eval:
  "smt_eval_with uf (evm_inputs3 x y m) generated_addmod_node_1 =
    Some (BVV 256 (uint256_to_int m))"
  by (simp add: generated_addmod_node_1_def evm_inputs3_def)

lemma addmod_remainder_eval:
  "smt_eval_with uf (evm_inputs3 x y m) generated_addmod_node_68 =
    Some (BVV 256 (mod_production_model uf
      (int_to_uint256 (uint256_to_int x + uint256_to_int y)) m))"
  unfolding addmod_remainder_structure
  apply (subst smt_eval_substitute_binary256[OF exported_mod_inputs,
    where x="uint256_to_int (int_to_uint256 (uint256_to_int x + uint256_to_int y))"
      and y="uint256_to_int m"])
    apply (simp add: addmod_sum_low_eval)
   apply (simp add: addmod_modulus_eval)
  apply (fold evm_inputs_def)
  apply (rule exported_mod_model)
  done

theorem exported_addmod_correct:
  "smt_eval (evm_inputs3 x y m) exported_addmod =
    Some (BVV 256 (uint256_to_int
      (if m = uint256_zero then uint256_zero else
       int_to_uint256 ((uint256_to_int x + uint256_to_int y) mod uint256_to_int m))))"
proof (cases "m = uint256_zero")
  case True
  show ?thesis
    using True
    by (simp add: exported_addmod_def generated_addmod_node_73_def
        generated_addmod_node_72_def generated_addmod_node_71_def
        generated_addmod_node_70_def generated_addmod_node_69_def
        generated_addmod_node_10_def generated_addmod_node_9_def
        generated_addmod_node_8_def generated_addmod_node_7_def
        generated_addmod_node_6_def generated_addmod_node_5_def
        generated_addmod_node_4_def generated_addmod_node_3_def
        generated_addmod_node_2_def generated_addmod_node_1_def
        generated_addmod_node_0_def addmod_remainder_eval mod_production_mathematical
        evm_inputs3_def packed_zero)
next
  case False
  have mpos: "0 < uint256_to_int m" using False pack_nonnegative[of m] pack_zero_iff[of m] by linarith
  have remlo: "0 \<le> (uint256_to_int x + uint256_to_int y) mod uint256_to_int m"
    using mpos by simp
  have remhi: "(uint256_to_int x + uint256_to_int y) mod uint256_to_int m < 2^256"
    using pos_mod_bound[OF mpos, of "uint256_to_int x + uint256_to_int y"] pack_less[of m] by linarith
  have normrem256: "bv_norm 256 ((uint256_to_int x + uint256_to_int y) mod uint256_to_int m) =
      (uint256_to_int x + uint256_to_int y) mod uint256_to_int m"
    by (rule bv_norm_small[OF remlo remhi])
  have normrem257: "bv_norm 257 ((uint256_to_int x + uint256_to_int y) mod uint256_to_int m) =
      (uint256_to_int x + uint256_to_int y) mod uint256_to_int m"
    by (rule bv_norm_small[OF remlo]) (use remhi in \<open>simp_all; linarith\<close>)
  show ?thesis
    using False mpos
    by (cases "uint256_to_int x + uint256_to_int y < 2^256")
       (simp_all add: exported_addmod_def generated_addmod_node_73_def
        generated_addmod_node_72_def generated_addmod_node_71_def
        generated_addmod_node_70_def generated_addmod_node_69_def
        generated_addmod_node_10_def generated_addmod_node_9_def
        generated_addmod_node_8_def generated_addmod_node_7_def
        generated_addmod_node_6_def generated_addmod_node_5_def
        generated_addmod_node_4_def generated_addmod_node_3_def
        generated_addmod_node_2_def generated_addmod_node_1_def
        generated_addmod_node_0_def addmod_remainder_eval mod_production_mathematical
        evm_inputs3_def pack_int_to_uint256 packed_sum_no_carry_simp
        bv_norm_small[OF packed_sum_range(1)] normrem256 normrem257)
qed

lemma packed_one [simp]: "uint256_to_int uint256_one = 1"
  by (simp add: pack_horner uint256_one_def)

lemma packed_set64:
  "uint256_to_int \<lparr>z0=w,z1=0,z2=0,z3=0\<rparr> = uint w"
  by (simp add: pack_horner)

lemma iszero_iff_record_zero: "IsZero x = (x = uint256_zero)"
  by (cases x) (simp add: IsZero_def uint256_zero_def or_eq_0_iff)

lemma limb_eq_iff_record_eq: "uint256_eq x y = (x = y)"
  by (cases x; cases y) (simp add: uint256_eq_def)

fun concrete_division_uf :: "smt_uf \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "concrete_division_uf HolimanUDiv a b =
    uint256_to_int (fst (udivrem uint256_zero (int_to_uint256 a) (int_to_uint256 b)))"
| "concrete_division_uf HolimanURem a b =
    uint256_to_int (snd (udivrem uint256_zero (int_to_uint256 a) (int_to_uint256 b)))"

lemma norm64_word_rem:
  "bv_norm 64 (if uint (b::u64) = 0 then uint (a::u64) else uint a mod uint b) = uint (a mod b)"
  by (cases "b = 0") (simp_all add: uint_0_iff uint_mod_distrib[symmetric])

theorem exported_mod_concrete_helper:
  "smt_eval_with concrete_division_uf (evm_inputs x y) exported_mod =
    Some (BVV 256 (uint256_to_int (Mod x y)))"
  unfolding exported_mod_model mod_production_model_def Mod_def
  by (simp add: iszero_iff_record_zero limb_eq_iff_record_eq Let_def
      case_prod_unfold smt_int_to_uint256_pack packed_set64 norm64_word_rem
      split: if_splits)

theorem exported_mod_correct:
  "smt_eval (evm_inputs x y) exported_mod = Some (BVV 256
    (uint256_to_int (if y = uint256_zero then uint256_zero else
      int_to_uint256 (uint256_to_int x mod uint256_to_int y))))"
proof (cases "y = uint256_zero")
  case True then show ?thesis by (simp add: exported_mod_mathematical)
next
  case False
  have ypos: "0 < uint256_to_int y"
    using False pack_nonnegative[of y] pack_zero_iff[of y] by linarith
  have lo: "0 \<le> uint256_to_int x mod uint256_to_int y" using ypos by simp
  have hi: "uint256_to_int x mod uint256_to_int y < 2^256"
    using pos_mod_bound[OF ypos, of "uint256_to_int x"] pack_less[of y] by linarith
  show ?thesis using False
    by (simp add: exported_mod_mathematical pack_int_to_uint256 bv_norm_small[OF lo hi])
qed

theorem exported_div_reference_correct:
  "smt_eval (evm_inputs x y) exported_div = Some (BVV 256
    (uint256_to_int (if y = uint256_zero then uint256_zero else
      int_to_uint256 (uint256_to_int x div uint256_to_int y))))"
proof (cases "y = uint256_zero")
  case True then show ?thesis by (simp add: exported_div_mathematical)
next
  case False
  have ypos: "0 < uint256_to_int y"
    using False pack_nonnegative[of y] pack_zero_iff[of y] by linarith
  have norm: "bv_norm 256 (uint256_to_int x div uint256_to_int y) =
      uint256_to_int x div uint256_to_int y"
    by (rule bv_udiv_normalized) (rule pack_nonnegative | rule pack_less | rule ypos)+
  show ?thesis using False
    by (simp add: exported_div_mathematical pack_int_to_uint256 norm)
qed

lemma division_fastpath_denominator:
  assumes "y \<noteq> uint256_zero" "\<not> uint256_lt x y" "Isuint64 x"
  shows "uint (z0 y) \<noteq> 0"
proof -
  have xp: "uint256_to_int x = uint (z0 x)" by (rule isuint64_pack[OF assms(3)])
  have le: "uint256_to_int y \<le> uint256_to_int x"
    using assms(2) by (simp add: uint256_lt_int)
  have ys: "Isuint64 y"
    by (rule pack_small_isuint64) (use le limb_uint_range[of "z0 x"] xp in linarith)
  have yp: "uint256_to_int y = uint (z0 y)" by (rule isuint64_pack[OF ys])
  show ?thesis using assms(1) pack_zero_iff[of y] yp by auto
qed

text \<open>The concrete interpretation names the quotient and remainder of the
  existing udivrem helper. The wrapper exposes the equality shortcut present in
  production Python. It requires no arithmetic-correctness assumption about the
  Knuth implementation.\<close>

theorem exported_div_concrete_bridge:
  "smt_eval_with concrete_division_uf (evm_inputs x y) exported_div =
    Some (BVV 256 (uint256_to_int
      (if x = y \<and> y \<noteq> uint256_zero then uint256_one else uint256_div x y)))"
proof -
  have norm: "bv_norm 64 (uint (z0 x) div uint (z0 y)) = uint (z0 x div z0 y)"
    by (simp add: uint_div_distrib[symmetric])
  show ?thesis
    by (cases "y = uint256_zero"; cases "uint256_lt x y";
        cases "x = y"; cases "Isuint64 x")
       (simp_all add: exported_div_model div_production_model_def uint256_div_def
        concrete_division_uf.simps smt_int_to_uint256_pack Let_def case_prod_unfold
        packed_set64 norm division_fastpath_denominator uint256_lt_int)
qed

theorem exported_div_concrete_correct:
  "smt_eval_with concrete_division_uf (evm_inputs x y) exported_div =
    Some (BVV 256 (uint256_to_int (uint256_div x y)))"
  using exported_div_concrete_bridge[of x y]
  by (cases "x = y"; cases "y = uint256_zero")
     (simp_all add: uint256_div_def uint256_lt_int)

ML \<open>
  val certificates = @{thms exported_div_reference_correct exported_mod_correct
    exported_sdiv_correct exported_smod_correct exported_addmod_correct
    exported_div_concrete_bridge exported_div_concrete_correct
    exported_mod_concrete_helper smt_eval_substitute}
  val _ = if null (Thm_Deps.all_oracles certificates) then ()
    else error "Division-family certificates have oracle dependencies"
\<close>

end
