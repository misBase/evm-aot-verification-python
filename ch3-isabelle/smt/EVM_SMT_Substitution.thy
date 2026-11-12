theory EVM_SMT_Substitution
  imports SMT_BV
begin

text \<open>Composition reuses a certificate for a production expression after
  replacing its input variables by other certified expressions. The substitution
  theorem reasons about arbitrary expressions and explicit function valuations.\<close>

fun smt_substitute :: "(nat \<Rightarrow> nat \<Rightarrow> smt_expr) \<Rightarrow> smt_expr \<Rightarrow> smt_expr" where
  "smt_substitute sigma (BVConst w x) = BVConst w x"
| "smt_substitute sigma (BVVar w n) = sigma w n"
| "smt_substitute sigma (BoolConst b) = BoolConst b"
| "smt_substitute sigma (BVBin op a b) = BVBin op (smt_substitute sigma a) (smt_substitute sigma b)"
| "smt_substitute sigma (BVWide op a b) = BVWide op (smt_substitute sigma a) (smt_substitute sigma b)"
| "smt_substitute sigma (BVUF op a b) = BVUF op (smt_substitute sigma a) (smt_substitute sigma b)"
| "smt_substitute sigma (BVNot a) = BVNot (smt_substitute sigma a)"
| "smt_substitute sigma (BVConcat a b) = BVConcat (smt_substitute sigma a) (smt_substitute sigma b)"
| "smt_substitute sigma (BVExtract hi lo a) = BVExtract hi lo (smt_substitute sigma a)"
| "smt_substitute sigma (BVZeroExt n a) = BVZeroExt n (smt_substitute sigma a)"
| "smt_substitute sigma (SMTEq a b) = SMTEq (smt_substitute sigma a) (smt_substitute sigma b)"
| "smt_substitute sigma (SMTNot a) = SMTNot (smt_substitute sigma a)"
| "smt_substitute sigma (SMTAnd a b) = SMTAnd (smt_substitute sigma a) (smt_substitute sigma b)"
| "smt_substitute sigma (SMTOr a b) = SMTOr (smt_substitute sigma a) (smt_substitute sigma b)"
| "smt_substitute sigma (SMTIte c a b) = SMTIte (smt_substitute sigma c) (smt_substitute sigma a) (smt_substitute sigma b)"
| "smt_substitute sigma (BVCmp cmp a b) = BVCmp cmp (smt_substitute sigma a) (smt_substitute sigma b)"

lemma smt_eval_substitute:
  assumes "\<And>n w. (n,w) \<in> smt_inputs e \<Longrightarrow>
    smt_eval_with uf env (sigma w n) =
      (if w > 0 then Some (BVV w (bv_norm w (rho n))) else None)"
  shows "smt_eval_with uf env (smt_substitute sigma e) = smt_eval_with uf rho e"
  using assms by (induction e) auto

lemma smt_eval_environment_cong:
  assumes "\<And>n w. (n,w) \<in> smt_inputs e \<Longrightarrow> bv_norm w (env n) = bv_norm w (rho n)"
  shows "smt_eval_with uf env e = smt_eval_with uf rho e"
  using assms by (induction e) auto

lemma smt_eval_substitute_binary256:
  assumes inputs: "smt_inputs e \<subseteq> {(0,256),(1,256)}"
      and left: "smt_eval_with uf env a = Some (BVV 256 (bv_norm 256 x))"
      and right: "smt_eval_with uf env b = Some (BVV 256 (bv_norm 256 y))"
  shows "smt_eval_with uf env
      (smt_substitute (\<lambda>w n. if n = 0 then a else b) e) =
    smt_eval_with uf (\<lambda>n. if n = 0 then x else y) e"
  apply (rule smt_eval_substitute)
  using inputs left right by auto

end
