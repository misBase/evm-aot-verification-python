theory EVM_SMT_Modular_Certificates
  imports EVM_SMT_Arithmetic_Certificates
begin

text \<open>The result on the right is the integer multiplication and remainder
  used by the existing MULMOD instruction rule. The exported expression keeps
  the full double-width product before taking the remainder.\<close>

lemma packed_zero_iff:
  "(uint256_to_int x = 0) = (x = uint256_zero)"
proof
  assume "uint256_to_int x = 0"
  then have "x = int_to_uint256 0"
    using smt_int_to_uint256_pack[of x] by simp
  then show "x = uint256_zero"
    by (simp add: int_to_uint256_def uint256_zero_def shiftr_def drop_bit_eq_div)
next
  assume "x = uint256_zero"
  then show "uint256_to_int x = 0"
    by (simp add: uint256_to_int_def uint256_zero_def shiftl_def push_bit_eq_mult)
qed

lemma packed_zero_value [simp]:
  "uint256_to_int uint256_zero = 0"
  by (simp add: uint256_to_int_def uint256_zero_def shiftl_def push_bit_eq_mult)

lemma packed_product_range:
  "0 \<le> uint256_to_int x * uint256_to_int y"
  "uint256_to_int x * uint256_to_int y < (2::int)^512"
proof -
  show "0 \<le> uint256_to_int x * uint256_to_int y"
    by (intro mult_nonneg_nonneg pack_nonnegative)
  have bounds: "uint256_to_int x \<le> (2::int)^256 - 1"
    "uint256_to_int y \<le> (2::int)^256 - 1"
    using pack_less[of x] pack_less[of y] by linarith+
  have "uint256_to_int x * uint256_to_int y \<le>
    ((2::int)^256 - 1) * (2^256 - 1)"
    by (rule mult_mono) (use bounds pack_nonnegative[of y] in auto)
  then show "uint256_to_int x * uint256_to_int y < (2::int)^512"
    by (simp_all; linarith)
qed

lemma packed_remainder_range:
  assumes "m \<noteq> uint256_zero"
  shows "0 \<le> a mod uint256_to_int m"
    "a mod uint256_to_int m < (2::int)^256"
proof -
  have positive: "0 < uint256_to_int m"
    using assms packed_zero_iff[of m] pack_nonnegative[of m] by linarith
  show "0 \<le> a mod uint256_to_int m" using positive by simp
  have "a mod uint256_to_int m < uint256_to_int m" using positive by simp
  then show "a mod uint256_to_int m < (2::int)^256"
    using pack_less[of m] by linarith
qed

theorem exported_mulmod_correct:
  "smt_eval (evm_inputs3 x y m) exported_mulmod =
    Some (BVV 256 (uint256_to_int
      (if m = uint256_zero then uint256_zero
       else int_to_uint256
         ((uint256_to_int x * uint256_to_int y) mod uint256_to_int m))))"
proof (cases "m = uint256_zero")
  case True
  then show ?thesis
    by (simp add: generated_mulmod_defs evm_inputs3_def Let_def)
next
  case False
  have norm_inputs: "bv_norm 512 (uint256_to_int x) = uint256_to_int x"
    "bv_norm 512 (uint256_to_int y) = uint256_to_int y"
    "bv_norm 512 (uint256_to_int m) = uint256_to_int m"
    using pack_range[of x] pack_range[of y] pack_range[of m]
    by (intro bv_norm_small; simp_all; linarith)+
  have norm_product: "bv_norm 512 (uint256_to_int x * uint256_to_int y) =
      uint256_to_int x * uint256_to_int y"
    by (rule bv_norm_small) (rule packed_product_range)+
  have norm_rem: "bv_norm 512 ((uint256_to_int x * uint256_to_int y) mod uint256_to_int m) =
      (uint256_to_int x * uint256_to_int y) mod uint256_to_int m"
    using packed_remainder_range[OF False, of "uint256_to_int x * uint256_to_int y"]
    by (intro bv_norm_small; simp_all; linarith)
  have norm_rem256: "bv_norm 256 ((uint256_to_int x * uint256_to_int y) mod uint256_to_int m) =
      (uint256_to_int x * uint256_to_int y) mod uint256_to_int m"
    by (rule bv_norm_small) (rule packed_remainder_range[OF False])+
  have cast: "uint256_to_int (int_to_uint256
      ((uint256_to_int x * uint256_to_int y) mod uint256_to_int m)) =
      (uint256_to_int x * uint256_to_int y) mod uint256_to_int m"
    by (rule uint256_to_int_int_to_uint256) (rule packed_remainder_range[OF False])+
  have nonzero: "uint256_to_int m \<noteq> 0"
    using False by (simp add: packed_zero_iff)
  show ?thesis
    by (simp add: generated_mulmod_defs evm_inputs3_def False nonzero
        norm_inputs norm_product norm_rem norm_rem256 cast)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms exported_mulmod_correct}) then ()
    else error "MULMOD certificate has oracle dependencies"
\<close>

end
