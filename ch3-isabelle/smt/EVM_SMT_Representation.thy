theory EVM_SMT_Representation
  imports SMT_BV "EVM_SMT_Base.uint256"
begin

text \<open>The input boundary uses the actual BV256 API of the Python semantics.
  These lemmas connect its four extracts to the existing uint256 record.\<close>

definition evm_inputs :: "uint256 \<Rightarrow> uint256 \<Rightarrow> nat \<Rightarrow> int" where
  "evm_inputs x y n = (if n = 0 then uint256_to_int x else uint256_to_int y)"

definition evm_inputs3 :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> nat \<Rightarrow> int" where
  "evm_inputs3 x y m n = (if n = 0 then uint256_to_int x
    else if n = 1 then uint256_to_int y else uint256_to_int m)"

lemma limb_uint_range:
  "0 \<le> uint (w :: u64)" "uint w < 2 ^ 64"
  using uint_nonnegative[of w] uint_lt2p[of w] by simp_all

lemma pack_horner:
  "uint256_to_int x = uint (z0 x) + 2^64 *
     (uint (z1 x) + 2^64 * (uint (z2 x) + 2^64 * uint (z3 x)))"
  by (simp add: uint256_to_int_def Let_def shiftl_def push_bit_eq_mult algebra_simps)

lemma pack_nonnegative: "0 \<le> uint256_to_int x"
  unfolding pack_horner by simp

lemma pack_less: "uint256_to_int x < 2^256"
  using limb_uint_range[of "z0 x"] limb_uint_range[of "z1 x"]
    limb_uint_range[of "z2 x"] limb_uint_range[of "z3 x"]
  unfolding pack_horner by (simp_all; linarith)

lemmas pack_range = pack_nonnegative pack_less

lemma pack_normalized [simp]: "bv_norm 256 (uint256_to_int x) = uint256_to_int x"
  by (rule bv_norm_small) (rule pack_range)+

lemma limb_normalized [simp]: "bv_norm 64 (uint (w :: u64)) = uint w"
  by (rule bv_norm_small) (rule limb_uint_range)+

lemma bv_norm_zero [simp]: "bv_norm w 0 = 0"
  by (simp add: bv_norm_def)

lemma bv_norm_one [simp]: "0 < w \<Longrightarrow> bv_norm w 1 = 1"
  by (simp add: bv_norm_def)

lemma limb_mod:
  "(uint (w :: u64) + 2^64 * k) mod 2^64 = uint w"
  by (subst mod_mult_self2) (rule mod_pos_pos_trivial[OF limb_uint_range])

lemma limb_div:
  "(uint (w :: u64) + 2^64 * k) div 2^64 = k"
proof -
  have nz: "(2::int)^64 \<noteq> 0" by simp
  have small: "uint w div 2^64 = 0"
    by (rule div_pos_pos_trivial[OF limb_uint_range])
  show ?thesis by (simp only: div_mult_self2[OF nz] small add_0_right)
qed

lemma packed_limb0:
  "bv_norm 64 (uint256_to_int x) = uint (z0 x)"
  by (simp only: bv_norm_def pack_horner limb_mod)

lemma packed_limb1:
  "bv_norm 64 (uint256_to_int x div 2^64) = uint (z1 x)"
  by (simp only: bv_norm_def pack_horner limb_div limb_mod zero_le_power zero_le_numeral)

lemma packed_limb2:
  "bv_norm 64 (uint256_to_int x div 2^128) = uint (z2 x)"
proof -
  have power: "(2::int)^128 = 2^64 * 2^64" by simp
  show ?thesis
    by (simp only: power zdiv_zmult2_eq bv_norm_def pack_horner limb_div limb_mod zero_le_power zero_le_numeral)
qed

lemma packed_limb3:
  "bv_norm 64 (uint256_to_int x div 2^192) = uint (z3 x)"
proof -
  have power: "(2::int)^192 = 2^64 * (2^64 * 2^64)" by simp
  show ?thesis
    by (simp only: power zdiv_zmult2_eq bv_norm_def pack_horner limb_div
        mod_pos_pos_trivial[OF limb_uint_range] zero_le_power zero_le_numeral mult_nonneg_nonneg)
qed

lemmas packed_limb_simps [simp] = packed_limb0 packed_limb1[simplified]
  packed_limb2[simplified] packed_limb3[simplified]

lemmas packed_mod_simps = packed_limb0[unfolded bv_norm_def, simplified]
  packed_limb1[unfolded bv_norm_def, simplified]
  packed_limb2[unfolded bv_norm_def, simplified]
  packed_limb3[unfolded bv_norm_def, simplified]

lemma smt_int_to_uint256_pack:
  "int_to_uint256 (uint256_to_int x) = x"
  by (rule uint256.equality)
     (simp_all add: int_to_uint256_def Let_def shiftr_def drop_bit_eq_div
        packed_mod_simps word_of_int_uint)

lemma four_limb_concat:
  fixes a b c d :: u64
  shows "bv_norm 256 (bv_norm 192 (bv_norm 128
      (uint d * 2^64 + uint c) * 2^64 + uint b) * 2^64 + uint a) =
    uint256_to_int \<lparr>z0 = a, z1 = b, z2 = c, z3 = d\<rparr>"
proof -
  have r128lo: "0 \<le> uint d * 2^64 + uint c" by simp
  have r128hi: "uint d * 2^64 + uint c < 2^128"
    using limb_uint_range[of c] limb_uint_range[of d] by (simp_all; linarith)
  have r192lo: "0 \<le> (uint d * 2^64 + uint c) * 2^64 + uint b" by simp
  have r192hi: "(uint d * 2^64 + uint c) * 2^64 + uint b < 2^192"
    using limb_uint_range[of b] r128hi by (simp_all; linarith)
  have r256lo: "0 \<le> ((uint d * 2^64 + uint c) * 2^64 + uint b) * 2^64 + uint a" by simp
  have r256hi: "((uint d * 2^64 + uint c) * 2^64 + uint b) * 2^64 + uint a < 2^256"
    using limb_uint_range[of a] r192hi by (simp_all; linarith)
  note r128 = r128lo r128hi
  note r192 = r192lo r192hi
  note r256 = r256lo r256hi
  show ?thesis
    by (simp only: bv_norm_small[OF r128] bv_norm_small[OF r192]
        bv_norm_small[OF r256]; simp add: pack_horner algebra_simps)
qed

lemmas four_limb_concat_simp = four_limb_concat[simplified]

lemma bv_and_uint [simp]:
  "bv_norm 64 (and (uint (x :: u64)) (uint y)) = uint (and x y)"
  by (simp only: unsigned_and_eq[symmetric] limb_normalized)

lemma bv_or_uint [simp]:
  "bv_norm 64 (or (uint (x :: u64)) (uint y)) = uint (or x y)"
  by (simp only: unsigned_or_eq[symmetric] limb_normalized)

lemma bv_xor_uint [simp]:
  "bv_norm 64 (xor (uint (x :: u64)) (uint y)) = uint (xor x y)"
  by (simp only: unsigned_xor_eq[symmetric] limb_normalized)

lemma bv_not_uint [simp]:
  "bv_norm 64 (not (uint (x :: u64))) = uint (not x)"
  by (simp add: unsigned_not_eq bv_norm_def take_bit_eq_mod)

lemma bv_mask64 [simp]:
  "bv_norm 64 18446744073709551615 = 18446744073709551615"
  by (simp add: bv_norm_def)

lemma bv_xor_mask64 [simp]:
  "bv_norm 64 (xor (uint (x :: u64)) 18446744073709551615) = uint (not x)"
proof -
  have mask: "uint (-1 :: u64) = 18446744073709551615"
    by (simp add: unsigned_minus_1_eq_mask mask_eq_exp_minus_1)
  have comp: "xor x (-1) = not x"
    by (rule bit_word_eqI) (simp add: bit_simps)
  show ?thesis using bv_xor_uint[of x "-1"] by (simp only: mask comp)
qed

end
