theory EVM_SMT_Mul_Certificates
  imports EVM_SMT_Arithmetic_Certificates
begin

text \<open>The production expression follows the compiler's four-limb
  multiplication schedule, with the second operand first and with partial
  products added before the running carry. The proofs connect this schedule
  to the existing HOL multiplication without changing its definition.\<close>

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

lemma umulStep_addends_commute:
  "umulStep z x y c = umulStep c x y z"
proof -
  let ?p = "umulStep z x y c"
  let ?q = "umulStep c x y z"
  have total: "uint (snd ?p) + 2^64 * uint (fst ?p) =
      uint (snd ?q) + 2^64 * uint (fst ?q)"
    using umulStep_spec_mod[of z x y c] umulStep_spec_mod[of c x y z]
    by (simp add: ac_simps)
  have hi: "uint (fst ?p) = uint (fst ?q)"
    using arg_cong[OF total, of "\<lambda>n::int. n div 2^64"]
    by (simp only: limb_div)
  have lo: "uint (snd ?p) = uint (snd ?q)"
    using arg_cong[OF total, of "\<lambda>n::int. n mod 2^64"]
    by (simp only: limb_mod)
  show ?thesis using hi lo by (simp add: prod_eq_iff word_uint_eq_iff)
qed

definition smt_umul_step_codegen ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "smt_umul_step_codegen z x y c = smt_umul_step c x y z"

lemma smt_umul_step_codegen_correct:
  "smt_umul_step_codegen (uint z) (uint x) (uint y) (uint c) =
    (uint (fst (umulStep z x y c)), uint (snd (umulStep z x y c)))"
  unfolding smt_umul_step_codegen_def
  by (simp only: smt_umul_step_correct umulStep_addends_commute[of c x y z])

lemma umulHop_low:
  "snd (umulHop z x y) = x * y + z"
  by (simp add: umulHop_def mul64_def Add64_carry_def case_prod_unfold Let_def)

lemma umulStep_low:
  "snd (umulStep z x y c) = x * y + c + z"
  by (simp add: umulStep_def mul64_def Add64_carry_def case_prod_unfold Let_def)

definition smt_mul_codegen :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
  "smt_mul_codegen p q = (let
     p0 = uint (z0 p); p1 = uint (z1 p); p2 = uint (z2 p); p3 = uint (z3 p);
     q0 = uint (z0 q); q1 = uint (z1 q); q2 = uint (z2 q); q3 = uint (z3 q);
     (carry0, r0) = smt_mul64 p0 q0;
     (carry0, res1) = smt_umul_hop carry0 p1 q0;
     (carry0, res2) = smt_umul_hop carry0 p2 q0;
     (unused, res3) = smt_umul_hop carry0 p3 q0;
     (carry1, r1) = smt_umul_hop res1 p0 q1;
     (carry1, res2) = smt_umul_step_codegen res2 p1 q1 carry1;
     (unused, res3) = smt_umul_step_codegen res3 p2 q1 carry1;
     (carry2, r2) = smt_umul_hop res2 p0 q2;
     (unused, res3) = smt_umul_step_codegen res3 p1 q2 carry2;
     (unused, r3) = smt_umul_hop res3 p0 q3
   in \<lparr>z0 = word_of_int r0, z1 = word_of_int r1,
       z2 = word_of_int r2, z3 = word_of_int r3\<rparr>)"

lemma smt_mul_codegen_correct:
  "smt_mul_codegen p q = uint256_mul p q"
  unfolding smt_mul_codegen_def uint256_mul_def
  by (simp add: case_prod_unfold Let_def smt_mul64_correct
      smt_umul_hop_correct smt_umul_step_codegen_correct
      umulHop_low umulStep_low ac_simps)

text \<open>Evaluate the generated nodes in topological order. Each rewrite
  produces a kernel-checked equality that subsequent nodes reuse, avoiding
  repeated expansion of shared subexpressions. For each node, the simplifier
  works with fresh variables for the child payloads. We discharge these
  temporary hypotheses, instantiate the variables with the actual payloads,
  and apply the already proved child equalities. No temporary hypotheses
  remain. Local weak congruence rules defer arithmetic normalization until
  the final result. SUBGOAL defers this work until the method receives an
  actual goal, rather than its closure check.\<close>

lemma smt_BVV_width_cong:
  "w = v \<Longrightarrow> BVV w x = BVV v x"
  by simp

lemma exported_mul_model:
  "smt_eval (evm_inputs x y) exported_mul =
    Some (BVV 256 (uint256_to_int (smt_mul_codegen y x)))"
  by (tactic \<open>SUBGOAL (fn (_, i) =>
    let
      val ss = (@{context} delsimprocs [@{simproc fast_arith}])
        addsimps @{thms evm_inputs_def Let_def bv_norm_nested
          bv_norm_add_left bv_norm_add_right bv_norm_add_four
          four_normalized_concat_simp smt_add64_normalized};
      val node_context = ss
        |> Simplifier.add_cong @{thm smt_BVV_width_cong}
        |> Simplifier.add_cong @{thm prod.case_cong_weak};
      val eval = Thm.rhs_of (Simplifier.rewrite ss
        @{cterm "smt_eval (evm_inputs x y)"});
      fun abstract_child (name, eq) =
        (case Thm.term_of (Thm.rhs_of eq) of
          (some as Const (@{const_name Some}, _)) $
              ((bvv as Const (@{const_name BVV}, _)) $ width $ payload) =>
            let
              val v = Free (name, @{typ int});
              val hyp = Thm.cterm_of ss (Logic.mk_equals
                (Thm.term_of (Thm.lhs_of eq), some $ (bvv $ width $ v)));
            in (Thm.cterm_of ss v, Thm.cterm_of ss payload, Thm.assume hyp) end
        | _ => error "Expected a bit-vector node value in the MUL certificate");
      fun eval_node def (cache, equations) =
        let
          val definition = def RS @{thm eq_reflection};
          val node = Thm.lhs_of definition;
          fun child_eq c =
            (case Termtab.lookup cache (Const c) of
              SOME eq => eq
            | NONE => error ("Missing preceding MUL node: " ^ #1 c));
          val children = Term.add_consts (Thm.term_of (Thm.rhs_of definition)) []
            |> filter (fn (_, T) => T = @{typ smt_expr})
            |> map child_eq;
          val (names, _) = Variable.variant_fixes
            (map (K "mul_payload") children) ss;
          val args = map abstract_child (names ~~ children);
          val hypotheses = map #3 args;
          val generic = Simplifier.rewrite
            (node_context addsimps (def :: hypotheses)) (Thm.apply eval node);
          val discharged = fold_rev (Thm.implies_intr o Thm.cprop_of) hypotheses generic;
          val generalized = fold_rev (fn (v, _, _) => Thm.forall_intr v) args discharged;
          val instantiated = fold (fn (_, p, _) => Thm.forall_elim p) args generalized;
          val eq = fold (fn premise => fn rule => Thm.implies_elim rule premise)
            children instantiated;
          val _ = if null (Thm.hyps_of eq) then ()
            else error "Undischarged MUL node hypotheses";
        in (Termtab.update (Thm.term_of node, eq) cache, eq :: equations) end;
      (* The exported root definition precedes the topologically ordered nodes. *)
      val (_, equations) = fold eval_node (tl @{thms generated_mul_defs}) (Termtab.empty, []);
      (* Restore the original congruences for complete arithmetic normalization. *)
      val result_ss = ss addsimps equations addsimps @{thms exported_mul_def
        smt_mul_codegen_def smt_umul_step_codegen_def smt_umul_hop_def
        smt_umul_step_def smt_mul64_def case_prod_unfold};
      val word_ss = @{context} addsimps @{thms bv_norm64_as_word add.assoc};
    in (asm_full_simp_tac result_ss THEN_ALL_NEW asm_full_simp_tac word_ss) i end) 1
  \<close>)

lemma exported_mul_correct:
  "smt_eval (evm_inputs x y) exported_mul =
    Some (BVV 256 (uint256_to_int (uint256_mul x y)))"
  by (simp add: exported_mul_model smt_mul_codegen_correct uint256_mul_mod mult.commute)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms exported_mul_correct}) then ()
    else error "Multiplication certificate has oracle dependencies"
\<close>

end
