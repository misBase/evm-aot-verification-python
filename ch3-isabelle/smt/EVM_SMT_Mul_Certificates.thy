theory EVM_SMT_Mul_Certificates
  imports EVM_SMT_Arithmetic_Certificates
begin

text \<open>The production expression follows the compiler's four-limb multiplication
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


lemma bv_norm_add_right2:
  "bv_norm w (a + (b + bv_norm w c)) = bv_norm w (a + (b + c))"
  by (simp add: bv_norm_def add.assoc[symmetric] mod_add_right_eq)

lemma bv_norm_add_inner_left:
  "bv_norm w (bv_norm w a + b + c) = bv_norm w (a + b + c)"
  by (simp add: bv_norm_def add.assoc mod_add_left_eq)

lemma bv_norm_add_inner_right:
  "bv_norm w (a + bv_norm w b + c) = bv_norm w (a + b + c)"
  by (metis bv_norm_add_left bv_norm_add_right)

lemma bv_norm_add_right3:
  "bv_norm w (a + (b + (c + bv_norm w d))) = bv_norm w (a + (b + (c + d)))"
  by (simp add: bv_norm_def add.assoc[symmetric] mod_add_right_eq)

lemma bv_norm_add_inner_right2:
  "bv_norm w (a + (b + bv_norm w c) + d) = bv_norm w (a + (b + c) + d)"
  by (metis bv_norm_add_left bv_norm_add_right2)

lemma bv_norm_add_inner_right3:
  "bv_norm w (a + (b + (c + bv_norm w e)) + d) = bv_norm w (a + (b + (c + e)) + d)"
  by (metis bv_norm_add_left bv_norm_add_right3)

lemma bv_norm_add_four:
  "bv_norm w (bv_norm w a + bv_norm w b + (c + bv_norm w d)) =
    bv_norm w (a + b + (c + d))"
  unfolding bv_norm_def
  by (rule mod_add_cong) (simp_all add: mod_add_eq mod_add_right_eq mod_add_left_eq)

subsection \<open>The compiler's multiplication schedule\<close>

text \<open>The validator encodes MUL as the compiler emits it: the first factor is the
  second stack operand and the second factor the top, each multiply-accumulate step
  adds its \<open>z\<close> term before the running carry, and the top limb is accumulated by the
  same hop and step operations. The value is the same 256-bit product; the lemmas
  below show that this schedule computes \<open>smt_mul256\<close>.\<close>

definition smt_umul_step_x86 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "smt_umul_step_x86 z x y carry = (let
     (hi, lo) = smt_mul64 x y;
     (lo, carry1) = smt_add64 lo z 0;
     (hi, carry2) = smt_add64 hi 0 carry1;
     (lo, carry3) = smt_add64 lo carry 0;
     (hi, unused) = smt_add64 hi 0 carry3
   in (hi, lo))"

definition smt_mul256_cg :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
  "smt_mul256_cg p q = (let
     p0 = uint (z0 p); p1 = uint (z1 p); p2 = uint (z2 p); p3 = uint (z3 p);
     q0 = uint (z0 q); q1 = uint (z1 q); q2 = uint (z2 q); q3 = uint (z3 q);
     (carry0, r0) = smt_mul64 p0 q0;
     (carry0, res1) = smt_umul_hop carry0 p1 q0;
     (carry0, res2) = smt_umul_hop carry0 p2 q0;
     (unused0, res3) = smt_umul_hop carry0 p3 q0;
     (carry1, r1) = smt_umul_hop res1 p0 q1;
     (carry1, res2) = smt_umul_step_x86 res2 p1 q1 carry1;
     (unused1, res3) = smt_umul_step_x86 res3 p2 q1 carry1;
     (carry2, r2) = smt_umul_hop res2 p0 q2;
     (unused2, res3) = smt_umul_step_x86 res3 p1 q2 carry2;
     (unused3, r3) = smt_umul_hop res3 p0 q3
   in \<lparr>z0 = word_of_int r0, z1 = word_of_int r1,
       z2 = word_of_int r2, z3 = word_of_int r3\<rparr>)"

text \<open>Two-stage accumulation of \<open>u\<close> and then \<open>v\<close> into a 128-bit value \<open>(h, l)\<close>.\<close>

definition smt_add2 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "smt_add2 h l u v = (let
     (lo, b1) = smt_add64 l u 0;
     (hi, w1) = smt_add64 h 0 b1;
     (lo, b2) = smt_add64 lo v 0;
     (hi, w2) = smt_add64 hi 0 b2
   in (hi, lo))"

lemma smt_umul_step_x86_add2:
  "smt_umul_step_x86 z x y c = (let (hi, lo) = smt_mul64 x y in smt_add2 hi lo z c)"
  unfolding smt_umul_step_x86_def smt_add2_def by (simp add: case_prod_unfold Let_def)

lemma smt_umul_step_add2:
  "smt_umul_step z x y c = (let (hi, lo) = smt_mul64 x y in smt_add2 hi lo c z)"
  unfolding smt_umul_step_def smt_add2_def by (simp add: case_prod_unfold Let_def)

lemma smt_add64_small:
  fixes a b :: int
  assumes "0 \<le> a" "a < 2^64" "0 \<le> b" "b < 2^64"
  shows "smt_add64 a b 0 = ((a + b) mod 2^64, (a + b) div 2^64)"
proof -
  have s0: "0 \<le> a + b" using assms by simp
  have s1: "a + b \<le> 2^65 - 2" using assms by simp
  have d0: "0 \<le> (a + b) div 2^64" using s0 by simp
  have "(a + b) div 2^64 \<le> (2^65 - 2) div (2^64 :: int)"
    using s1 by (intro zdiv_mono1) simp_all
  then have d1: "(a + b) div 2^64 < 2" by simp
  have m65: "(a + b) mod 2^65 = a + b" using s0 s1 by simp
  have m2: "(a + b) div 2^64 mod 2 = (a + b) div 2^64" using d0 d1 by simp
  show ?thesis unfolding smt_add64_def using m65 m2 by simp
qed

lemma smt_add64_fst_hi: "fst (smt_add64 a 0 b) = (a + b) mod 2^64"
  by (simp add: smt_add64_def)

lemma smt_add2_exact:
  fixes h l u v :: int
  assumes l0: "0 \<le> l" and l1: "l < 2^64" and h0: "0 \<le> h"
      and u0: "0 \<le> u" and u1: "u < 2^64" and v0: "0 \<le> v" and v1: "v < 2^64"
      and bound: "h * 2^64 + l + u + v < 2^128"
  shows "smt_add2 h l u v = ((h * 2^64 + l + u + v) div 2^64, (h * 2^64 + l + u + v) mod 2^64)"
proof -
  define q1 where "q1 = (l + u) div 2^64"
  define r1 where "r1 = (l + u) mod 2^64"
  define q2 where "q2 = (r1 + v) div 2^64"
  have r1r: "0 \<le> r1" "r1 < 2^64" unfolding r1_def by simp_all
  have q1n: "0 \<le> q1" unfolding q1_def using l0 u0 by simp
  have q2n: "0 \<le> q2" unfolding q2_def using r1r v0 by simp
  have dv: "(l + u + v) div 2^64 = q1 + q2"
    using div_add1_eq[of "l + u" v "2^64"] v0 v1 unfolding q1_def q2_def r1_def by simp
  have sdiv: "(h * 2^64 + l + u + v) div 2^64 = h + q1 + q2"
  proof -
    have "(h * 2^64 + l + u + v) div 2^64 = (l + u + v + h * 2^64) div (2^64 :: int)"
      by (simp add: ac_simps)
    also have "\<dots> = h + (l + u + v) div 2^64" by simp
    finally show ?thesis using dv by simp
  qed
  have smod: "(h * 2^64 + l + u + v) mod 2^64 = (r1 + v) mod 2^64"
  proof -
    have "(h * 2^64 + l + u + v) mod 2^64 = (l + u + v + h * 2^64) mod (2^64 :: int)"
      by (simp add: ac_simps)
    also have "\<dots> = (l + u + v) mod 2^64" by simp
    also have "\<dots> = (r1 + v) mod 2^64" unfolding r1_def by (simp add: mod_add_left_eq)
    finally show ?thesis .
  qed
  have "(h * 2^64 + l + u + v) div 2^64 \<le> (2^128 - 1) div (2^64 :: int)"
    using bound by (intro zdiv_mono1) simp_all
  then have top: "h + q1 + q2 < 2^64" using sdiv by simp
  have m1: "(h + q1) mod 2^64 = h + q1" using h0 q1n q2n top by simp
  have m2: "(h + q1 + q2) mod 2^64 = h + q1 + q2" using h0 q1n q2n top by simp
  have a1: "smt_add64 l u 0 = (r1, q1)"
    unfolding q1_def r1_def using l0 l1 u0 u1 by (rule smt_add64_small)
  have a2: "smt_add64 r1 v 0 = ((r1 + v) mod 2^64, q2)"
    unfolding q2_def using r1r v0 v1 by (rule smt_add64_small)
  show ?thesis
    unfolding smt_add2_def Let_def case_prod_unfold
    using a1 a2 m1 m2 sdiv smod by (simp add: smt_add64_fst_hi)
qed

lemma smt_mul64_bound:
  fixes x y :: int
  assumes "0 \<le> x" "x < 2^64" "0 \<le> y" "y < 2^64"
  shows "x * y \<le> 2^128 - 2^65 + 1"
proof -
  have "x * y \<le> (2^64 - 1) * (2^64 - 1 :: int)"
    using assms by (intro mult_mono) simp_all
  then show ?thesis by simp
qed

lemma smt_mul64_exact:
  fixes x y :: int
  assumes x0: "0 \<le> x" and x1: "x < 2^64" and y0: "0 \<le> y" and y1: "y < 2^64"
  shows "smt_mul64 x y = (x * y div 2^64, x * y mod 2^64)"
proof -
  have p0: "0 \<le> x * y" using x0 y0 by simp
  have p1: "x * y < 2^128" using smt_mul64_bound[OF x0 x1 y0 y1] by simp
  have "x * y div 2^64 \<le> (2^128 - 1) div (2^64 :: int)"
    using p1 by (intro zdiv_mono1) simp_all
  then have h1: "x * y div 2^64 < 2^64" by simp
  have h0: "0 \<le> x * y div 2^64" using p0 by simp
  show ?thesis
    unfolding smt_mul64_def bv_norm_def using p0 p1 h0 h1 by simp
qed

lemma smt_umul_steps_exact:
  fixes x y z c :: int
  assumes x0: "0 \<le> x" and x1: "x < 2^64" and y0: "0 \<le> y" and y1: "y < 2^64"
      and z0: "0 \<le> z" and z1: "z < 2^64" and c0: "0 \<le> c" and c1: "c < 2^64"
  shows "smt_umul_step_x86 z x y c = ((x * y + z + c) div 2^64, (x * y + z + c) mod 2^64)"
    and "smt_umul_step z x y c = ((x * y + z + c) div 2^64, (x * y + z + c) mod 2^64)"
proof -
  have m: "smt_mul64 x y = (x * y div 2^64, x * y mod 2^64)"
    using x0 x1 y0 y1 by (rule smt_mul64_exact)
  have p0: "0 \<le> x * y" using x0 y0 by simp
  have pb: "x * y \<le> 2^128 - 2^65 + 1" using x0 x1 y0 y1 by (rule smt_mul64_bound)
  have hl: "x * y div 2^64 * 2^64 + x * y mod 2^64 = x * y" by simp
  have h0: "0 \<le> x * y div 2^64" using p0 by simp
  have lr: "0 \<le> x * y mod 2^64" "x * y mod 2^64 < 2^64" by simp_all
  have b1: "x * y div 2^64 * 2^64 + x * y mod 2^64 + z + c < 2^128"
    unfolding hl using pb z1 c1 by simp
  have b2: "x * y div 2^64 * 2^64 + x * y mod 2^64 + c + z < 2^128"
    unfolding hl using pb z1 c1 by simp
  have e1: "smt_add2 (x * y div 2^64) (x * y mod 2^64) z c =
      ((x * y + z + c) div 2^64, (x * y + z + c) mod 2^64)"
    using smt_add2_exact[OF lr h0 z0 z1 c0 c1 b1] hl by simp
  have e2: "smt_add2 (x * y div 2^64) (x * y mod 2^64) c z =
      ((x * y + z + c) div 2^64, (x * y + z + c) mod 2^64)"
    using smt_add2_exact[OF lr h0 c0 c1 z0 z1 b2] hl by (simp add: ac_simps)
  show "smt_umul_step_x86 z x y c = ((x * y + z + c) div 2^64, (x * y + z + c) mod 2^64)"
    unfolding smt_umul_step_x86_add2 m by (simp only: Let_def prod.case e1)
  show "smt_umul_step z x y c = ((x * y + z + c) div 2^64, (x * y + z + c) mod 2^64)"
    unfolding smt_umul_step_add2 m by (simp only: Let_def prod.case e2)
qed

lemma smt_umul_step_x86_eq:
  fixes x y z c :: int
  assumes "0 \<le> z" "z < 2^64" "0 \<le> x" "x < 2^64" "0 \<le> y" "y < 2^64" "0 \<le> c" "c < 2^64"
  shows "smt_umul_step_x86 z x y c = smt_umul_step z x y c"
  using smt_umul_steps_exact[of x y z c] assms by simp

text \<open>Range facts, stated with \<open>2^64\<close> and declared to the simplifier in the numeral
  form that it normalizes goals to.\<close>

lemma smt_add64_fst_range:
  "0 \<le> fst (smt_add64 a b c)" "fst (smt_add64 a b c) < 2^64"
  by (simp_all add: smt_add64_def)

lemmas smt_add64_fst_range_simps [simp] = smt_add64_fst_range[simplified]

lemma smt_mul64_range:
  "0 \<le> fst (smt_mul64 x y)" "fst (smt_mul64 x y) < 2^64"
  "0 \<le> snd (smt_mul64 x y)" "snd (smt_mul64 x y) < 2^64"
  by (simp_all add: smt_mul64_def bv_norm_def)

lemmas smt_mul64_range_simps [simp] = smt_mul64_range[simplified]

lemma smt_umul_hop_range:
  "0 \<le> fst (smt_umul_hop z x y)" "fst (smt_umul_hop z x y) < 2^64"
  "0 \<le> snd (smt_umul_hop z x y)" "snd (smt_umul_hop z x y) < 2^64"
  by (simp_all add: smt_umul_hop_def case_prod_unfold Let_def)

lemmas smt_umul_hop_range_simps [simp] = smt_umul_hop_range[simplified]

lemma smt_umul_step_range:
  "0 \<le> fst (smt_umul_step z x y c)" "fst (smt_umul_step z x y c) < 2^64"
  "0 \<le> snd (smt_umul_step z x y c)" "snd (smt_umul_step z x y c) < 2^64"
  by (simp_all add: smt_umul_step_def case_prod_unfold Let_def)

lemmas smt_umul_step_range_simps [simp] = smt_umul_step_range[simplified]

lemma smt_umul_hop_lo: "snd (smt_umul_hop z x y) = bv_norm 64 (x * y + z)"
  unfolding smt_umul_hop_def smt_mul64_def smt_add64_def bv_norm_def
  by (simp add: case_prod_unfold Let_def mod_add_left_eq)

lemma smt_umul_step_lo: "snd (smt_umul_step z x y c) = bv_norm 64 (x * y + c + z)"
  unfolding smt_umul_step_def smt_mul64_def smt_add64_def bv_norm_def
  by (simp add: case_prod_unfold Let_def mod_add_left_eq add.assoc)

lemma smt_mul256_cg_eq:
  "smt_mul256_cg p q = smt_mul256 p q"
  unfolding smt_mul256_cg_def smt_mul256_def
  apply (simp add: case_prod_unfold Let_def limb_uint_range[simplified] smt_umul_step_x86_eq)
  apply (simp add: smt_umul_hop_lo smt_umul_step_lo bv_norm_add_right ac_simps)
  done

subsection \<open>Certificate\<close>

text \<open>The exported expression has variable 0 as the top stack operand and
  variable 1 as the second; the compiler's schedule multiplies the second by the top.\<close>

lemma exported_mul_model:
  "smt_eval (evm_inputs x y) exported_mul =
    Some (BVV 256 (uint256_to_int (smt_mul256_cg y x)))"
  unfolding smt_mul256_cg_def smt_umul_hop_def smt_umul_step_x86_def smt_mul64_def
  apply (simp add: generated_mul_defs evm_inputs_def Let_def
      bv_norm_nested bv_norm_add_left bv_norm_add_right bv_norm_add_right2 bv_norm_add_right3
      bv_norm_add_inner_left bv_norm_add_inner_right bv_norm_add_inner_right2 bv_norm_add_inner_right3
      bv_norm_add bv_norm_add_four four_normalized_concat_simp smt_add64_normalized)
  done

lemma uint256_mul_commute:
  "uint256_mul y x = uint256_mul x y"
  by (metis int_to_uint256_uint256_to_int uint256_mul_mod mult.commute)

lemma exported_mul_correct:
  "smt_eval (evm_inputs x y) exported_mul =
    Some (BVV 256 (uint256_to_int (uint256_mul x y)))"
proof -
  have "smt_mul256_cg y x = uint256_mul x y"
    unfolding smt_mul256_cg_eq smt_mul256_correct by (rule uint256_mul_commute)
  then show ?thesis
    by (simp add: exported_mul_model)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms exported_mul_correct}) then ()
    else error "Multiplication certificate has oracle dependencies"
\<close>

end
