theory EVM_SMT_Mul_Certificates
  imports EVM_SMT_Arithmetic_Certificates
begin

text \<open>The production expression follows the four-limb multiplication
  schedule. The proofs first connect each widened product and carry operation
  with its existing HOL helper, then compose the limb results.\<close>

definition smt_mul64 :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "smt_mul64 x y = (bv_norm 64 (bv_norm 128 (x * y) div 2^64), bv_norm 64 (x*y))"

lemma smt_mul64_correct:
  "smt_mul64 (uint x) (uint y) = (uint (fst (mul64 x y)), uint (snd (mul64 x y)))"
proof -
  let ?h = "fst (mul64 x y)"
  let ?l = "snd (mul64 x y)"
  have spec: "uint x * uint y = uint ?h * 2^64 + uint ?l"
    using mul64_spec[of x y] by simp
  have lo: "0 \<le> uint x * uint y" by simp
  have hi: "uint x * uint y < (2::int)^128"
    using uint_lt_2p64[of ?h] uint_lt_2p64[of ?l]
    unfolding spec by (simp_all; linarith)
  have quot: "(uint ?h * (2::int)^64 + uint ?l) div 2^64 = uint ?h"
    using limb_div[of ?l "uint ?h"] by (simp add: ac_simps)
  have rem: "(uint ?h * (2::int)^64 + uint ?l) mod 2^64 = uint ?l"
    using limb_mod[of ?l "uint ?h"] by (simp add: ac_simps)
  have normalized: "bv_norm 128 (uint x * uint y) = uint x * uint y"
    by (rule bv_norm_small[OF lo hi])
  show ?thesis unfolding smt_mul64_def
    apply (subst normalized)
    by (simp only: spec quot limb_normalized bv_norm_def rem mod_pos_pos_trivial[OF limb_uint_range])
qed

definition smt_umul_hop :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "smt_umul_hop z x y = (let
     (hi, lo) = smt_mul64 x y;
     (lo, carry) = smt_add64 lo z 0;
     (hi, unused) = smt_add64 hi 0 carry
   in (hi, lo))"

definition smt_umul_step :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "smt_umul_step z x y carry = (let
     (hi, lo) = smt_mul64 x y;
     (lo, carry1) = smt_add64 lo carry 0;
     (hi, carry2) = smt_add64 hi 0 carry1;
     (lo, carry3) = smt_add64 lo z 0;
     (hi, unused) = smt_add64 hi 0 carry3
   in (hi, lo))"

lemma smt_add64_uint_zero_right:
  "uint c < 2 \<Longrightarrow> smt_add64 (uint x) 0 (uint c) =
    (uint (fst (Add64_carry x 0 c)), uint (snd (Add64_carry x 0 c)))"
  using smt_add64_correct[of c x 0] by simp

lemma smt_umul_hop_correct:
  "smt_umul_hop (uint z) (uint x) (uint y) =
    (uint (fst (umulHop z x y)), uint (snd (umulHop z x y)))"
  unfolding smt_umul_hop_def umulHop_def
  by (simp add: case_prod_unfold Let_def smt_mul64_correct smt_add64_zero
      smt_add64_uint_zero_right smt_add64_carry_lt2)

lemma smt_umul_step_correct:
  "smt_umul_step (uint z) (uint x) (uint y) (uint c) =
    (uint (fst (umulStep z x y c)), uint (snd (umulStep z x y c)))"
  unfolding smt_umul_step_def umulStep_def
  by (simp add: case_prod_unfold Let_def smt_mul64_correct smt_add64_zero
      smt_add64_uint_zero_right smt_add64_carry_lt2)

definition smt_mul256 :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
  "smt_mul256 x y = (let
     x0 = uint (z0 x); x1 = uint (z1 x); x2 = uint (z2 x); x3 = uint (z3 x);
     y0 = uint (z0 y); y1 = uint (z1 y); y2 = uint (z2 y); y3 = uint (z3 y);
     (carry0, r0) = smt_mul64 x0 y0;
     (carry0, res1) = smt_umul_hop carry0 x1 y0;
     (carry0, res2) = smt_umul_hop carry0 x2 y0;
     (carry1, r1) = smt_umul_hop res1 x0 y1;
     (carry1, res2) = smt_umul_step res2 x1 y1 carry1;
     (carry2, r2) = smt_umul_hop res2 x0 y2;
     r3 = x3*y0 + x2*y1 + x0*y3 + x1*y2 + carry0 + carry1 + carry2
   in \<lparr>z0 = word_of_int r0, z1 = word_of_int r1,
       z2 = word_of_int r2, z3 = word_of_int r3\<rparr>)"

lemma smt_mul256_correct:
  "smt_mul256 x y = uint256_mul x y"
  unfolding smt_mul256_def uint256_mul_def
  by (simp add: case_prod_unfold Let_def smt_mul64_correct
      smt_umul_hop_correct smt_umul_step_correct
      wi_hom_syms)


lemma bv_norm128_uint [simp]: "bv_norm 128 (uint (x :: u64)) = uint x"
proof (rule bv_norm_small)
  show "0 \<le> uint x" by simp
  show "uint x < (2::int)^128"
    using limb_uint_range(2)[of x] by (simp_all; linarith)
qed

lemma bv_norm_add_right:
  "bv_norm w (a + bv_norm w b) = bv_norm w (a + b)"
  by (simp add: bv_norm_def mod_add_right_eq)


lemma bv_norm_add_four:
  "bv_norm w (bv_norm w a + bv_norm w b + (c + bv_norm w d)) =
    bv_norm w (a + b + (c + d))"
  unfolding bv_norm_def
  by (rule mod_add_cong) (simp_all add: mod_add_eq mod_add_right_eq mod_add_left_eq)

lemma exported_mul_model:
  "smt_eval (evm_inputs x y) exported_mul =
    Some (BVV 256 (uint256_to_int (smt_mul256 x y)))"
  unfolding smt_mul256_def smt_umul_hop_def smt_umul_step_def smt_mul64_def
  by (simp add: generated_mul_defs evm_inputs_def Let_def
      bv_norm_nested bv_norm_add_left bv_norm_add_right bv_norm_add_four
      four_normalized_concat_simp smt_add64_normalized)

lemma exported_mul_correct:
  "smt_eval (evm_inputs x y) exported_mul =
    Some (BVV 256 (uint256_to_int (uint256_mul x y)))"
  by (simp add: exported_mul_model smt_mul256_correct)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms exported_mul_correct}) then ()
    else error "Multiplication certificate has oracle dependencies"
\<close>

end
