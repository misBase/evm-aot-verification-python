theory EVM_SMT_Signextend_Certificates
  imports EVM_SMT_Signextend_Bridge Generated_EVM_Arithmetic
begin

lemma signextend_value_if [simp]:
  "(if p then BVV w a else BVV w b) = BVV w (if p then a else b)"
  by (cases p) simp_all

lemma signextend_norm_numeral [simp]:
  "bv_norm w (numeral n) = numeral n mod 2^w"
  by (simp add: bv_norm_def)

lemma signextend_sign_bit:
  "(1 = bv_norm 1 (a div 2^n)) = bit a n"
  by (auto simp: bv_norm_def bit_iff_odd odd_iff_mod_2_eq_one)

lemma integer_signextend_choice:
  "(if bit a n then or a (not (mask (Suc n))) else and a (mask (Suc n))) =
    signed_take_bit n (a::int)"
  by (rule bit_eqI)
     (auto simp: bit_simps min_def less_Suc_eq_le split: if_splits; metis order_antisym)

lemma signextend_norm_or:
  "bv_norm w (or a (bv_norm w b)) = bv_norm w (or a b)"
  by (rule bit_eqI) (auto simp: bv_norm_eq_take_bit bit_simps)

lemma signextend_choice:
  "(if bit a n then bv_norm 256 (or a (bv_norm 256 (not (mask (Suc n)))))
    else bv_norm 256 (and a (mask (Suc n)))) =
    bv_norm 256 (signed_take_bit n a)"
  using arg_cong[OF integer_signextend_choice[of a n], of "bv_norm 256"]
  by (simp add: signextend_norm_or split: if_splits)

lemma signextend_full_width [simp]:
  "bv_norm 256 (signed_take_bit 255 (uint256_to_int x)) = uint256_to_int x"
proof -
  have "bv_norm 256 (signed_take_bit 255 a) = bv_norm 256 a" for a
    by (simp add: bv_norm_eq_take_bit take_bit_signed_take_bit)
  then show ?thesis by simp
qed

lemmas signextend_sign_simps =
  signextend_sign_bit[where n = "7", simplified]
  signextend_sign_bit[where n = "15", simplified]
  signextend_sign_bit[where n = "23", simplified]
  signextend_sign_bit[where n = "31", simplified]
  signextend_sign_bit[where n = "39", simplified]
  signextend_sign_bit[where n = "47", simplified]
  signextend_sign_bit[where n = "55", simplified]
  signextend_sign_bit[where n = "63", simplified]
  signextend_sign_bit[where n = "71", simplified]
  signextend_sign_bit[where n = "79", simplified]
  signextend_sign_bit[where n = "87", simplified]
  signextend_sign_bit[where n = "95", simplified]
  signextend_sign_bit[where n = "103", simplified]
  signextend_sign_bit[where n = "111", simplified]
  signextend_sign_bit[where n = "119", simplified]
  signextend_sign_bit[where n = "127", simplified]
  signextend_sign_bit[where n = "135", simplified]
  signextend_sign_bit[where n = "143", simplified]
  signextend_sign_bit[where n = "151", simplified]
  signextend_sign_bit[where n = "159", simplified]
  signextend_sign_bit[where n = "167", simplified]
  signextend_sign_bit[where n = "175", simplified]
  signextend_sign_bit[where n = "183", simplified]
  signextend_sign_bit[where n = "191", simplified]
  signextend_sign_bit[where n = "199", simplified]
  signextend_sign_bit[where n = "207", simplified]
  signextend_sign_bit[where n = "215", simplified]
  signextend_sign_bit[where n = "223", simplified]
  signextend_sign_bit[where n = "231", simplified]
  signextend_sign_bit[where n = "239", simplified]
  signextend_sign_bit[where n = "247", simplified]
  signextend_sign_bit[where n = "255", simplified]

lemmas signextend_choice_simps =
  signextend_choice[where n = "7", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "15", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "23", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "31", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "39", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "47", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "55", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "63", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "71", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "79", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "87", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "95", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "103", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "111", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "119", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "127", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "135", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "143", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "151", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "159", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "167", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "175", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "183", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "191", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "199", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "207", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "215", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "223", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "231", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "239", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "247", simplified mask_eq_exp_minus_1]
  signextend_choice[where n = "255", simplified mask_eq_exp_minus_1]

lemma signextend_byte_0:
  "smt_eval (evm_inputs x y) generated_signextend_node_13 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 7 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="7"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_1:
  "smt_eval (evm_inputs x y) generated_signextend_node_22 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 15 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="15"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_2:
  "smt_eval (evm_inputs x y) generated_signextend_node_31 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 23 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="23"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_3:
  "smt_eval (evm_inputs x y) generated_signextend_node_40 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 31 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="31"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_4:
  "smt_eval (evm_inputs x y) generated_signextend_node_49 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 39 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="39"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_5:
  "smt_eval (evm_inputs x y) generated_signextend_node_58 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 47 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="47"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_6:
  "smt_eval (evm_inputs x y) generated_signextend_node_67 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 55 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="55"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_7:
  "smt_eval (evm_inputs x y) generated_signextend_node_76 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 63 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="63"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_8:
  "smt_eval (evm_inputs x y) generated_signextend_node_85 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 71 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="71"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_9:
  "smt_eval (evm_inputs x y) generated_signextend_node_94 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 79 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="79"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_10:
  "smt_eval (evm_inputs x y) generated_signextend_node_103 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 87 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="87"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_11:
  "smt_eval (evm_inputs x y) generated_signextend_node_112 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 95 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="95"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_12:
  "smt_eval (evm_inputs x y) generated_signextend_node_121 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 103 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="103"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_13:
  "smt_eval (evm_inputs x y) generated_signextend_node_130 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 111 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="111"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_14:
  "smt_eval (evm_inputs x y) generated_signextend_node_139 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 119 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="119"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_15:
  "smt_eval (evm_inputs x y) generated_signextend_node_148 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 127 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="127"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_16:
  "smt_eval (evm_inputs x y) generated_signextend_node_157 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 135 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="135"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_17:
  "smt_eval (evm_inputs x y) generated_signextend_node_166 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 143 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="143"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_18:
  "smt_eval (evm_inputs x y) generated_signextend_node_175 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 151 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="151"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_19:
  "smt_eval (evm_inputs x y) generated_signextend_node_184 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 159 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="159"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_20:
  "smt_eval (evm_inputs x y) generated_signextend_node_193 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 167 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="167"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_21:
  "smt_eval (evm_inputs x y) generated_signextend_node_202 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 175 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="175"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_22:
  "smt_eval (evm_inputs x y) generated_signextend_node_211 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 183 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="183"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_23:
  "smt_eval (evm_inputs x y) generated_signextend_node_220 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 191 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="191"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_24:
  "smt_eval (evm_inputs x y) generated_signextend_node_229 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 199 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="199"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_25:
  "smt_eval (evm_inputs x y) generated_signextend_node_238 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 207 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="207"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_26:
  "smt_eval (evm_inputs x y) generated_signextend_node_247 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 215 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="215"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_27:
  "smt_eval (evm_inputs x y) generated_signextend_node_256 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 223 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="223"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_28:
  "smt_eval (evm_inputs x y) generated_signextend_node_265 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 231 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="231"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_29:
  "smt_eval (evm_inputs x y) generated_signextend_node_274 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 239 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="239"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_30:
  "smt_eval (evm_inputs x y) generated_signextend_node_283 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 247 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="247"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemma signextend_byte_31:
  "smt_eval (evm_inputs x y) generated_signextend_node_292 =
    Some (BVV 256 (bv_norm 256 (signed_take_bit 255 (uint256_to_int y))))"
  using signextend_choice[where a="uint256_to_int y" and n="255"]
  by (auto simp: generated_signextend_defs evm_inputs_def mask_eq_exp_minus_1
      signextend_sign_simps split: if_splits)

lemmas signextend_byte_nodes =
  signextend_byte_0
  signextend_byte_1
  signextend_byte_2
  signextend_byte_3
  signextend_byte_4
  signextend_byte_5
  signextend_byte_6
  signextend_byte_7
  signextend_byte_8
  signextend_byte_9
  signextend_byte_10
  signextend_byte_11
  signextend_byte_12
  signextend_byte_13
  signextend_byte_14
  signextend_byte_15
  signextend_byte_16
  signextend_byte_17
  signextend_byte_18
  signextend_byte_19
  signextend_byte_20
  signextend_byte_21
  signextend_byte_22
  signextend_byte_23
  signextend_byte_24
  signextend_byte_25
  signextend_byte_26
  signextend_byte_27
  signextend_byte_28
  signextend_byte_29
  signextend_byte_30
  signextend_byte_31

lemmas signextend_selection_defs =
  exported_signextend_def
  generated_signextend_node_0_def
  generated_signextend_node_1_def
  generated_signextend_node_2_def
  generated_signextend_node_3_def
  generated_signextend_node_4_def
  generated_signextend_node_5_def
  generated_signextend_node_14_def
  generated_signextend_node_15_def
  generated_signextend_node_23_def
  generated_signextend_node_24_def
  generated_signextend_node_32_def
  generated_signextend_node_33_def
  generated_signextend_node_41_def
  generated_signextend_node_42_def
  generated_signextend_node_50_def
  generated_signextend_node_51_def
  generated_signextend_node_59_def
  generated_signextend_node_60_def
  generated_signextend_node_68_def
  generated_signextend_node_69_def
  generated_signextend_node_77_def
  generated_signextend_node_78_def
  generated_signextend_node_86_def
  generated_signextend_node_87_def
  generated_signextend_node_95_def
  generated_signextend_node_96_def
  generated_signextend_node_104_def
  generated_signextend_node_105_def
  generated_signextend_node_113_def
  generated_signextend_node_114_def
  generated_signextend_node_122_def
  generated_signextend_node_123_def
  generated_signextend_node_131_def
  generated_signextend_node_132_def
  generated_signextend_node_140_def
  generated_signextend_node_141_def
  generated_signextend_node_149_def
  generated_signextend_node_150_def
  generated_signextend_node_158_def
  generated_signextend_node_159_def
  generated_signextend_node_167_def
  generated_signextend_node_168_def
  generated_signextend_node_176_def
  generated_signextend_node_177_def
  generated_signextend_node_185_def
  generated_signextend_node_186_def
  generated_signextend_node_194_def
  generated_signextend_node_195_def
  generated_signextend_node_203_def
  generated_signextend_node_204_def
  generated_signextend_node_212_def
  generated_signextend_node_213_def
  generated_signextend_node_221_def
  generated_signextend_node_222_def
  generated_signextend_node_230_def
  generated_signextend_node_231_def
  generated_signextend_node_239_def
  generated_signextend_node_240_def
  generated_signextend_node_248_def
  generated_signextend_node_249_def
  generated_signextend_node_257_def
  generated_signextend_node_258_def
  generated_signextend_node_266_def
  generated_signextend_node_267_def
  generated_signextend_node_275_def
  generated_signextend_node_276_def
  generated_signextend_node_284_def
  generated_signextend_node_285_def
  generated_signextend_node_293_def
  generated_signextend_node_294_def
  generated_signextend_node_295_def
  generated_signextend_node_296_def
  generated_signextend_node_297_def
  generated_signextend_node_298_def
  generated_signextend_node_299_def
  generated_signextend_node_300_def
  generated_signextend_node_301_def
  generated_signextend_node_302_def
  generated_signextend_node_303_def
  generated_signextend_node_304_def
  generated_signextend_node_305_def
  generated_signextend_node_306_def
  generated_signextend_node_307_def
  generated_signextend_node_308_def
  generated_signextend_node_309_def
  generated_signextend_node_310_def
  generated_signextend_node_311_def
  generated_signextend_node_312_def
  generated_signextend_node_313_def
  generated_signextend_node_314_def
  generated_signextend_node_315_def
  generated_signextend_node_316_def
  generated_signextend_node_317_def
  generated_signextend_node_318_def
  generated_signextend_node_319_def
  generated_signextend_node_320_def
  generated_signextend_node_321_def
  generated_signextend_node_322_def
  generated_signextend_node_323_def
  generated_signextend_node_324_def
  generated_signextend_node_325_def

definition smt_signextend_result :: "uint256 \<Rightarrow> uint256 \<Rightarrow> int" where
  "smt_signextend_result idx value = (if uint256_to_int idx < 31 then
    bv_norm 256 (signed_take_bit (8 * nat (uint256_to_int idx) + 7) (uint256_to_int value))
    else uint256_to_int value)"

lemma signextend_integer_correct:
  "uint256_to_int (extend_sign value idx) = smt_signextend_result idx value"
proof (cases "uint256_to_int idx < 31")
  case True
  show ?thesis
    by (simp add: extend_sign_as_integer[OF True] smt_signextend_result_def
        True smt_pack_int_to_uint256)
next
  case False
  then show ?thesis
    by (simp add: smt_signextend_result_def extend_sign_def signextend_guard)
qed

lemma exported_signextend_model:
  "smt_eval (evm_inputs x y) exported_signextend =
    Some (BVV 256 (smt_signextend_result x y))"
proof (cases "uint256_to_int x < 32")
  case False
  then have large: "\<not> uint256_to_int x < 31" by linarith
  show ?thesis using False large
    by (auto simp: signextend_selection_defs signextend_byte_nodes evm_inputs_def smt_signextend_result_def; linarith)
next
  case True
  have cases: "uint256_to_int x = 0 \<or> uint256_to_int x = 1 \<or> uint256_to_int x = 2 \<or> uint256_to_int x = 3 \<or> uint256_to_int x = 4 \<or> uint256_to_int x = 5 \<or> uint256_to_int x = 6 \<or> uint256_to_int x = 7 \<or> uint256_to_int x = 8 \<or> uint256_to_int x = 9 \<or> uint256_to_int x = 10 \<or> uint256_to_int x = 11 \<or> uint256_to_int x = 12 \<or> uint256_to_int x = 13 \<or> uint256_to_int x = 14 \<or> uint256_to_int x = 15 \<or> uint256_to_int x = 16 \<or> uint256_to_int x = 17 \<or> uint256_to_int x = 18 \<or> uint256_to_int x = 19 \<or> uint256_to_int x = 20 \<or> uint256_to_int x = 21 \<or> uint256_to_int x = 22 \<or> uint256_to_int x = 23 \<or> uint256_to_int x = 24 \<or> uint256_to_int x = 25 \<or> uint256_to_int x = 26 \<or> uint256_to_int x = 27 \<or> uint256_to_int x = 28 \<or> uint256_to_int x = 29 \<or> uint256_to_int x = 30 \<or> uint256_to_int x = 31"
    using True pack_nonnegative[of x] by presburger
  show ?thesis using cases
    by (elim disjE)
       (simp_all add: signextend_selection_defs signextend_byte_nodes evm_inputs_def smt_signextend_result_def
           signextend_sign_simps signextend_choice_simps)
qed

theorem exported_signextend_correct:
  "smt_eval (evm_inputs x y) exported_signextend =
    Some (BVV 256 (uint256_to_int (extend_sign y x)))"
  by (simp add: exported_signextend_model signextend_integer_correct)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms exported_signextend_correct}) then ()
    else error "SIGNEXTEND certificate has oracle dependencies"
\<close>

end
