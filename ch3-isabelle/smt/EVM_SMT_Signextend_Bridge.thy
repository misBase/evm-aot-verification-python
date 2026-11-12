theory EVM_SMT_Signextend_Bridge
  imports EVM_SMT_Bit_Representation
begin

text \<open>The bridge first proves the limb mask-and-shift identity. It then
  checks each in-range byte index and connects the existing HOL helper to signed
  bit truncation. The separate full-width guard handles every larger index.\<close>

lemma signextend_guard:
  "GtUint64 idx 30 = (30 < uint256_to_int idx)"
proof -
  have nonzero: "(w \<noteq> (0::u64)) = (0 < uint w)" for w
    using uint_nonnegative[of w] uint_0_iff[of w] by linarith
  show ?thesis
    unfolding GtUint64_def or_eq_0_iff
    using limb_uint_range[of "z0 idx"] limb_uint_range[of "z1 idx"]
      limb_uint_range[of "z2 idx"] limb_uint_range[of "z3 idx"]
    by (auto simp: nonzero word_less_alt pack_horner; linarith)
qed

lemma limb_sign_test:
  "((w :: u64) AND 128 \<noteq> 0) = bit w 7"
proof -
  have "(128::u64) = push_bit 7 1" by code_simp
  then show ?thesis
    by (simp only: bit_iff_and_push_bit_not_eq_0[symmetric])
qed

lemma signextend_masks:
  "(0xFFFFFFFFFFFFFFFF::u64) = -1"
  "(0xFFFFFFFFFFFFFF00::u64) = NOT (mask 8)"
  "(0xFF::u64) = mask 8"
  by code_simp+

lemma signed_take_bit_bits_cut:
  "bit (signed_take_bit k (a :: int)) n =
    (if n < Suc k then bit a n else bit a k)"
  by (cases "n \<le> k") (simp_all add: bit_signed_take_bit_iff min_def)

lemma signextend_limb_bits:
  fixes w :: u64
  assumes off: "m \<le> 56" and nb: "n < 64"
  shows "bit (((if ((w >> m) AND 128) \<noteq> 0 then
      (NOT (mask 8)) OR ((w >> m) AND mask 8)
      else (w >> m) AND mask 8) << m) OR
      (w AND (NOT ((-1) << m)))) n =
    (if n < m + 8 then bit w n else bit w (m + 7))"
  using off nb
  by (cases "n < m"; cases "n < m+8"; cases "bit w (m+7)")
     (auto simp: limb_sign_test limb_shr_bit shiftl_def bit_or_iff
       bit_and_iff bit_not_iff bit_mask_iff bit_push_bit_iff)

lemma signed_take_word_bits_cut:
  "bit (signed_take_bit k (a :: u64)) n =
    (n < 64 \<and> (if n < Suc k then bit a n else bit a k))"
  by (cases "n \<le> k") (simp_all add: bit_signed_take_bit_iff min_def)

lemma signextend_limb_word:
  fixes w :: u64
  assumes off: "m \<le> 56"
  shows "((if ((w >> m) AND 128) \<noteq> 0 then
      (NOT (mask 8)) OR ((w >> m) AND mask 8)
      else (w >> m) AND mask 8) << m) OR
      (w AND (NOT ((-1) << m))) = signed_take_bit (m + 7) w"
  by (rule bit_word_eqI)
     (simp add: signextend_limb_bits[OF off] signed_take_word_bits_cut)

lemma signextend_index_simps:
  "unat ((0 :: u64) >> 3) = 0"
  "unat ((0 :: u64) AND 7) = 0"
  "unat ((1 :: u64) >> 3) = 0"
  "unat ((1 :: u64) AND 7) = 1"
  "unat ((2 :: u64) >> 3) = 0"
  "unat ((2 :: u64) AND 7) = 2"
  "unat ((3 :: u64) >> 3) = 0"
  "unat ((3 :: u64) AND 7) = 3"
  "unat ((4 :: u64) >> 3) = 0"
  "unat ((4 :: u64) AND 7) = 4"
  "unat ((5 :: u64) >> 3) = 0"
  "unat ((5 :: u64) AND 7) = 5"
  "unat ((6 :: u64) >> 3) = 0"
  "unat ((6 :: u64) AND 7) = 6"
  "unat ((7 :: u64) >> 3) = 0"
  "unat ((7 :: u64) AND 7) = 7"
  "unat ((8 :: u64) >> 3) = 1"
  "unat ((8 :: u64) AND 7) = 0"
  "unat ((9 :: u64) >> 3) = 1"
  "unat ((9 :: u64) AND 7) = 1"
  "unat ((10 :: u64) >> 3) = 1"
  "unat ((10 :: u64) AND 7) = 2"
  "unat ((11 :: u64) >> 3) = 1"
  "unat ((11 :: u64) AND 7) = 3"
  "unat ((12 :: u64) >> 3) = 1"
  "unat ((12 :: u64) AND 7) = 4"
  "unat ((13 :: u64) >> 3) = 1"
  "unat ((13 :: u64) AND 7) = 5"
  "unat ((14 :: u64) >> 3) = 1"
  "unat ((14 :: u64) AND 7) = 6"
  "unat ((15 :: u64) >> 3) = 1"
  "unat ((15 :: u64) AND 7) = 7"
  "unat ((16 :: u64) >> 3) = 2"
  "unat ((16 :: u64) AND 7) = 0"
  "unat ((17 :: u64) >> 3) = 2"
  "unat ((17 :: u64) AND 7) = 1"
  "unat ((18 :: u64) >> 3) = 2"
  "unat ((18 :: u64) AND 7) = 2"
  "unat ((19 :: u64) >> 3) = 2"
  "unat ((19 :: u64) AND 7) = 3"
  "unat ((20 :: u64) >> 3) = 2"
  "unat ((20 :: u64) AND 7) = 4"
  "unat ((21 :: u64) >> 3) = 2"
  "unat ((21 :: u64) AND 7) = 5"
  "unat ((22 :: u64) >> 3) = 2"
  "unat ((22 :: u64) AND 7) = 6"
  "unat ((23 :: u64) >> 3) = 2"
  "unat ((23 :: u64) AND 7) = 7"
  "unat ((24 :: u64) >> 3) = 3"
  "unat ((24 :: u64) AND 7) = 0"
  "unat ((25 :: u64) >> 3) = 3"
  "unat ((25 :: u64) AND 7) = 1"
  "unat ((26 :: u64) >> 3) = 3"
  "unat ((26 :: u64) AND 7) = 2"
  "unat ((27 :: u64) >> 3) = 3"
  "unat ((27 :: u64) AND 7) = 3"
  "unat ((28 :: u64) >> 3) = 3"
  "unat ((28 :: u64) AND 7) = 4"
  "unat ((29 :: u64) >> 3) = 3"
  "unat ((29 :: u64) AND 7) = 5"
  "unat ((30 :: u64) >> 3) = 3"
  "unat ((30 :: u64) AND 7) = 6"
  by code_simp+

lemma extend_sign_as_integer:
  assumes small: "uint256_to_int idx < 31"
  shows "extend_sign value idx = int_to_uint256
    (signed_take_bit (8 * nat (uint256_to_int idx) + 7) (uint256_to_int value))"
proof -
  let ?i = "unat (z0 idx)"
  have small256: "uint256_to_int idx < 256" using small by linarith
  have idx: "nat (uint256_to_int idx) = ?i"
    by (rule low_shift_amount[OF small256])
  have ibound: "?i < 31" using small pack_nonnegative[of idx] idx by linarith
  have icases: "?i = 0 \<or> ?i = 1 \<or> ?i = 2 \<or> ?i = 3 \<or> ?i = 4 \<or> ?i = 5 \<or> ?i = 6 \<or> ?i = 7 \<or> ?i = 8 \<or> ?i = 9 \<or> ?i = 10 \<or> ?i = 11 \<or> ?i = 12 \<or> ?i = 13 \<or> ?i = 14 \<or> ?i = 15 \<or> ?i = 16 \<or> ?i = 17 \<or> ?i = 18 \<or> ?i = 19 \<or> ?i = 20 \<or> ?i = 21 \<or> ?i = 22 \<or> ?i = 23 \<or> ?i = 24 \<or> ?i = 25 \<or> ?i = 26 \<or> ?i = 27 \<or> ?i = 28 \<or> ?i = 29 \<or> ?i = 30" using ibound by presburger
  have guard: "\<not> GtUint64 idx 30" using small by (simp add: signextend_guard)
  have wcases: "z0 idx = 0 \<or> z0 idx = 1 \<or> z0 idx = 2 \<or> z0 idx = 3 \<or> z0 idx = 4 \<or> z0 idx = 5 \<or> z0 idx = 6 \<or> z0 idx = 7 \<or> z0 idx = 8 \<or> z0 idx = 9 \<or> z0 idx = 10 \<or> z0 idx = 11 \<or> z0 idx = 12 \<or> z0 idx = 13 \<or> z0 idx = 14 \<or> z0 idx = 15 \<or> z0 idx = 16 \<or> z0 idx = 17 \<or> z0 idx = 18 \<or> z0 idx = 19 \<or> z0 idx = 20 \<or> z0 idx = 21 \<or> z0 idx = 22 \<or> z0 idx = 23 \<or> z0 idx = 24 \<or> z0 idx = 25 \<or> z0 idx = 26 \<or> z0 idx = 27 \<or> z0 idx = 28 \<or> z0 idx = 29 \<or> z0 idx = 30"
    using icases by (simp add: word_unat_eq_iff)
  show ?thesis using wcases
    by (elim disjE)
       (simp add: extend_sign_def guard Let_def idx getword_def signextend_masks
          signextend_index_simps signextend_limb_word cong: if_cong split del: if_split;
        rule uint256.equality; (rule bit_word_eqI)?;
        auto simp: limb_sign_test decode_bits signed_take_word_bits_cut
          signed_take_bit_bits_cut limb_shr_bit packed_bit_all add.commute;
        presburger)+
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms extend_sign_as_integer signextend_guard}) then ()
    else error "Sign-extension bridge has oracle dependencies"
\<close>

end
