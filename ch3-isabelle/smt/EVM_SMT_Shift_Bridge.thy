theory EVM_SMT_Shift_Bridge
  imports EVM_SMT_Bit_Representation
begin

lemma lsh_as_integer:
  assumes small: "uint256_to_int s < 256"
  shows "Lsh s x = int_to_uint256 (push_bit (nat (uint256_to_int s)) (uint256_to_int x))"
proof -
  let ?n = "unat (z0 s)"
  have n: "?n < 256" using small
    by (subst low_shift_amount[OF small, symmetric]) simp
  show ?thesis
    apply (rule uint256.equality; (rule bit_word_eqI)?)
    using small n
    apply (simp_all add: Lsh_def Let_def low_shift_amount[OF small]
      decode_bits bit_or_iff bit_and_iff limb_shr_bit)
    apply (simp_all add: shiftl_def bit_simps packed_bit_all add.commute)
    apply safe
    by (presburger)+
qed

lemma rsh_as_integer:
  assumes small: "uint256_to_int s < 256"
  shows "Rsh s x = int_to_uint256 (drop_bit (nat (uint256_to_int s)) (uint256_to_int x))"
proof -
  let ?n = "unat (z0 s)"
  have n: "?n < 256" using small
    by (subst low_shift_amount[OF small, symmetric]) simp
  show ?thesis
    apply (rule uint256.equality; (rule bit_word_eqI)?)
    using small n
    apply (simp_all add: Rsh_def Let_def low_shift_amount[OF small]
      decode_bits bit_or_iff bit_and_iff limb_shr_bit)
    apply (simp_all add: shiftl_def bit_simps packed_bit_all add.commute)
    apply safe
    by (presburger)+
qed


lemma isBitSet_255:
  "isBitSet x 255 = bit (uint256_to_int x) 255"
proof -
  have "((z3 x AND (1 << 63)) \<noteq> 0) = bit (z3 x) 63"
    by (simp only: shiftl_def bit_iff_and_push_bit_not_eq_0[symmetric])
  then show ?thesis
    by (simp add: isBitSet_def Let_def packed_bit_all)
qed

lemma signed_pack_positive:
  assumes "\<not> bit (uint256_to_int x) 255"
  shows "signed_take_bit 255 (uint256_to_int x) = uint256_to_int x"
  using assms pack_range[of x]
  by (simp add: signed_take_bit_eq_take_bit_minus take_bit_eq_mod)

lemma mask64_int_bits:
  "bit (18446744073709551615 :: int) n = (n < 64)"
proof -
  have mask: "(18446744073709551615 :: int) = mask 64"
    by (simp add: mask_eq_exp_minus_1)
  show ?thesis by (simp only: mask bit_mask_iff) simp
qed

lemma mask64_word_bits:
  "bit (18446744073709551615 :: u64) n = (n < 64)"
proof -
  have cast: "(18446744073709551615 :: u64) = word_of_int (18446744073709551615 :: int)"
    by simp
  show ?thesis by (simp only: cast bit_word_of_int_iff mask64_int_bits) simp
qed

lemma srsh_as_integer:
  assumes small: "uint256_to_int s < 256"
  shows "SRsh s x = int_to_uint256
    (drop_bit (nat (uint256_to_int s)) (signed_take_bit 255 (uint256_to_int x)))"
proof (cases "isBitSet x 255")
  case False
  have signed: "signed_take_bit 255 (uint256_to_int x) = uint256_to_int x"
    by (rule signed_pack_positive) (use False in \<open>simp add: isBitSet_255\<close>)
  show ?thesis by (simp add: SRsh_def False signed rsh_as_integer[OF small])
next
  case True
  let ?n = "unat (z0 s)"
  have n: "?n < 256" using small
    by (subst low_shift_amount[OF small, symmetric]) simp
  have mod_case: "?n mod 64 = ?n - k * 64"
    if "k * 64 \<le> ?n" "?n < (k + 1) * 64" for k
  proof -
    have q: "?n div 64 = k"
      by (rule div_nat_eqI) (use that in \<open>simp_all add: algebra_simps\<close>)
    show ?thesis by (simp only: minus_div_mult_eq_mod[symmetric] q)
  qed
  have mod: "?n mod 64 = (if 192 \<le> ?n then ?n - 192
    else if 128 \<le> ?n then ?n - 128 else if 64 \<le> ?n then ?n - 64 else ?n)"
    using n mod_case[of 0] mod_case[of 1] mod_case[of 2] mod_case[of 3]
    by (auto split: if_splits)
  have sign: "bit (z3 x) 63" using True by (simp add: isBitSet_255 packed_bit_all)
  have sign_eq: "k = 63 \<Longrightarrow> bit (z3 x) k" for k using sign by simp
  have sign_ne: "\<not> bit (z3 x) k \<Longrightarrow> k \<noteq> 63" for k using sign by auto
  have mask: "(2^64 - 1 :: u64) = -1" by simp
  show ?thesis
    apply (rule uint256.equality; (rule bit_word_eqI)?)
    using small n True sign
    apply (simp_all add: SRsh_def Let_def low_shift_amount[OF small]
      decode_bits bit_or_iff bit_and_iff limb_shr_bit MaxUint64_def mask mod)
    apply (simp_all add: shiftl_def bit_simps packed_bit_all add.commute min_def
      mask64_int_bits mask64_word_bits)
    apply safe
    by ((frule sign_ne; presburger) | (rule sign_eq; presburger) | presburger)+
qed

lemma lsh_packed:
  "uint256_to_int (Lsh s x) = bv_norm 256
    (if uint256_to_int s \<ge> 256 then 0
     else uint256_to_int x * 2^(nat (uint256_to_int s)))"
proof (cases "uint256_to_int s \<ge> 256")
  case True
  then show ?thesis by (simp add: Lsh_def uint256_zero_def pack_horner)
next
  case False
  then have small: "uint256_to_int s < 256" by simp
  show ?thesis using lsh_as_integer[OF small, of x] False
    by (simp add: smt_pack_int_to_uint256 push_bit_eq_mult)
qed

lemma rsh_packed:
  "uint256_to_int (Rsh s x) = bv_norm 256
    (if uint256_to_int s \<ge> 256 then 0
     else uint256_to_int x div 2^(nat (uint256_to_int s)))"
proof (cases "uint256_to_int s \<ge> 256")
  case True
  then show ?thesis by (simp add: Rsh_def uint256_zero_def pack_horner)
next
  case False
  then have small: "uint256_to_int s < 256" by simp
  show ?thesis using rsh_as_integer[OF small, of x] False
    by (simp add: smt_pack_int_to_uint256 drop_bit_eq_div)
qed


lemma srsh_packed:
  "uint256_to_int (SRsh s x) = bv_norm 256
    (if uint256_to_int s \<ge> 256
     then (if bit (uint256_to_int x) 255 then -1 else 0)
     else drop_bit (nat (uint256_to_int s))
       (signed_take_bit 255 (uint256_to_int x)))"
proof (cases "uint256_to_int s \<ge> 256")
  case True
  then show ?thesis
    by (simp add: SRsh_def Rsh_def isBitSet_255 SetAllOne_def
        uint256_zero_def pack_horner bv_norm_def)
next
  case False
  then have small: "uint256_to_int s < 256" by simp
  show ?thesis using srsh_as_integer[OF small, of x] False
    by (simp add: smt_pack_int_to_uint256)
qed


lemma shifts_high_limb_regression:
  "Lsh uint256_2_64 x = uint256_zero"
  "Rsh uint256_2_64 x = uint256_zero"
  "SRsh uint256_2_64 x = (if isBitSet x 255 then SetAllOne else uint256_zero)"
  by (simp_all add: Lsh_def Rsh_def SRsh_def uint256_2_64_def
      uint256_to_int_def Let_def shiftl_def push_bit_eq_mult)

end
