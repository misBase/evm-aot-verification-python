theory EVM_SMT_Bit_Representation
  imports EVM_SMT_Representation
begin

text \<open>The shift and byte guards inspect the full packed operand.  The
  limb implementations remain the computational definitions below those guards.\<close>

lemma packed_bit0:
  assumes "n < 64"
  shows "bit (uint256_to_int x) n = bit (z0 x) n"
  using arg_cong[OF packed_limb0[of x], of "\<lambda>i. bit i n"] assms
  by (simp only: bv_norm_def take_bit_eq_mod[symmetric] bit_take_bit_iff bit_uint_iff; simp)

lemma packed_bit1:
  assumes "n < 64"
  shows "bit (uint256_to_int x) (n + 64) = bit (z1 x) n"
  using arg_cong[OF packed_limb1[of x], of "\<lambda>i. bit i n"] assms
  by (simp only: bv_norm_def take_bit_eq_mod[symmetric] drop_bit_eq_div[symmetric]
      bit_take_bit_iff bit_drop_bit_eq bit_uint_iff; simp add: add.commute)

lemma packed_bit2:
  assumes "n < 64"
  shows "bit (uint256_to_int x) (n + 128) = bit (z2 x) n"
  using arg_cong[OF packed_limb2[of x], of "\<lambda>i. bit i n"] assms
  by (simp only: bv_norm_def take_bit_eq_mod[symmetric] drop_bit_eq_div[symmetric]
      bit_take_bit_iff bit_drop_bit_eq bit_uint_iff; simp add: add.commute)

lemma packed_bit3:
  assumes "n < 64"
  shows "bit (uint256_to_int x) (n + 192) = bit (z3 x) n"
  using arg_cong[OF packed_limb3[of x], of "\<lambda>i. bit i n"] assms
  by (simp only: bv_norm_def take_bit_eq_mod[symmetric] drop_bit_eq_div[symmetric]
      bit_take_bit_iff bit_drop_bit_eq bit_uint_iff; simp add: add.commute)

lemma packed_bit:
  assumes "n < 256"
  shows "bit (uint256_to_int x) n =
    (if n < 64 then bit (z0 x) n
     else if n < 128 then bit (z1 x) (n - 64)
     else if n < 192 then bit (z2 x) (n - 128)
     else bit (z3 x) (n - 192))"
  using assms packed_bit0[of n x] packed_bit1[of "n-64" x]
    packed_bit2[of "n-128" x] packed_bit3[of "n-192" x]
  by (auto split: if_splits)

lemma low_shift_amount:
  assumes "uint256_to_int s < 256"
  shows "nat (uint256_to_int s) = unat (z0 s)"
proof -
  have small: "uint256_to_int s < 2^64" using assms by (simp_all; linarith)
  have "uint (z0 s) = uint256_to_int s"
    using packed_limb0[of s] pack_nonnegative[of s] small
    by (simp add: bv_norm_def)
  then show ?thesis by (simp add: unat_eq_nat_uint)
qed

lemma packed_bit_outside:
  assumes "256 \<le> n"
  shows "\<not> bit (uint256_to_int x) n"
proof -
  have "uint (uint256_to_word256 x) = uint256_to_int x"
    using mod_pos_pos_trivial[OF pack_range[of x]]
    by (simp add: uint256_to_word256_def uint_word_of_int)
  moreover have "\<not> bit (uint (uint256_to_word256 x)) n"
    using assms by (simp add: bit_uint_iff)
  ultimately show ?thesis by simp
qed


lemma packed_bit_all:
  "bit (uint256_to_int x) n =
    (if n < 64 then bit (z0 x) n
     else if n < 128 then bit (z1 x) (n - 64)
     else if n < 192 then bit (z2 x) (n - 128)
     else if n < 256 then bit (z3 x) (n - 192) else False)"
  using packed_bit[of n x] packed_bit_outside[of n x]
  by (auto split: if_splits)

lemma decode_bits:
  "bit (z0 (int_to_uint256 i)) n = (n < 64 \<and> bit i n)"
  "bit (z1 (int_to_uint256 i)) n = (n < 64 \<and> bit i (n + 64))"
  "bit (z2 (int_to_uint256 i)) n = (n < 64 \<and> bit i (n + 128))"
  "bit (z3 (int_to_uint256 i)) n = (n < 64 \<and> bit i (n + 192))"
proof -
  have len64: "LENGTH(64) = 64" by simp
  show "bit (z0 (int_to_uint256 i)) n = (n < 64 \<and> bit i n)"
    by (simp only: int_to_uint256_def uint256.select_convs bit_word_of_int_iff len64
        take_bit_eq_mod[symmetric] bit_take_bit_iff) simp
  show "bit (z1 (int_to_uint256 i)) n = (n < 64 \<and> bit i (n + 64))"
    by (simp only: int_to_uint256_def uint256.select_convs bit_word_of_int_iff len64
        shiftr_def take_bit_eq_mod[symmetric] bit_take_bit_iff bit_drop_bit_eq)
       (simp add: add.commute)
  show "bit (z2 (int_to_uint256 i)) n = (n < 64 \<and> bit i (n + 128))"
    by (simp only: int_to_uint256_def uint256.select_convs bit_word_of_int_iff len64
        shiftr_def take_bit_eq_mod[symmetric] bit_take_bit_iff bit_drop_bit_eq)
       (simp add: add.commute)
  show "bit (z3 (int_to_uint256 i)) n = (n < 64 \<and> bit i (n + 192))"
    by (simp only: int_to_uint256_def uint256.select_convs bit_word_of_int_iff len64
        shiftr_def take_bit_eq_mod[symmetric] bit_take_bit_iff bit_drop_bit_eq)
       (simp add: add.commute)
qed

lemma smt_pack_int_to_uint256:
  "uint256_to_int (int_to_uint256 i) = bv_norm 256 i"
  unfolding bv_norm_def
  apply (subst take_bit_eq_mod[symmetric])
  apply (rule bit_eqI)
  by (auto simp: packed_bit_all decode_bits bit_take_bit_iff split: if_splits)

lemma limb_bit_outside:
  "64 \<le> n \<Longrightarrow> \<not> bit (x :: u64) n"
  using bit_imp_le_length[of x n] by auto

lemma limb_shr_bit:
  "bit ((x :: u64) >> m) n = (m + n < 64 \<and> bit x (m + n))"
  by (auto simp: shiftr_def bit_simps dest: bit_imp_le_length)

end
