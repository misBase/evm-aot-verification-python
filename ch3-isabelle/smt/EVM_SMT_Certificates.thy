theory EVM_SMT_Certificates
  imports EVM_SMT_Arithmetic_Certificates EVM_SMT_Logic_Certificates
    EVM_SMT_Mul_Certificates EVM_SMT_Compare_Certificates
    EVM_SMT_Shift_Certificates EVM_SMT_Modular_Certificates
    EVM_SMT_Byte_Certificates EVM_SMT_Signextend_Certificates
    EVM_SMT_Div_Certificates
begin

text \<open>The supported operations are scalar HOL library helpers and
  reference result functions. This layer deliberately does not assert a theorem
  about stack updates, gas, exceptions, or the Python CFG executor.\<close>

datatype certified_evm_op =
  CAdd | CSub | CEq | CIszero | CAnd | COr | CXor | CNot

fun certified_expression :: "certified_evm_op \<Rightarrow> smt_expr" where
  "certified_expression CAdd = exported_add"
| "certified_expression CSub = exported_sub"
| "certified_expression CEq = exported_eq"
| "certified_expression CIszero = exported_iszero"
| "certified_expression CAnd = exported_and"
| "certified_expression COr = exported_or"
| "certified_expression CXor = exported_xor"
| "certified_expression CNot = exported_not"

fun certified_hol_result :: "certified_evm_op \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
  "certified_hol_result CAdd x y = uint256_add x y"
| "certified_hol_result CSub x y = uint256_sub x y"
| "certified_hol_result CEq x y = (if x = y then uint256_one else uint256_zero)"
| "certified_hol_result CIszero x y = (if x = uint256_zero then uint256_one else uint256_zero)"
| "certified_hol_result CAnd x y = uint256_and x y"
| "certified_hol_result COr x y = uint256_or x y"
| "certified_hol_result CXor x y = uint256_xor x y"
| "certified_hol_result CNot x y = uint256_not x"

definition decode_smt_word :: "smt_value option \<Rightarrow> uint256 option" where
  "decode_smt_word v = (case v of
      Some (BVV w n) \<Rightarrow> if w = 256 then Some (int_to_uint256 n) else None
    | _ \<Rightarrow> None)"

theorem certified_arithmetic_eval:
  "smt_eval (evm_inputs x y) (certified_expression op) =
    Some (BVV 256 (uint256_to_int (certified_hol_result op x y)))"
  by (cases op) (simp_all add: exported_add_correct exported_sub_correct
      exported_eq_correct exported_iszero_correct exported_and_correct
      exported_or_correct exported_xor_correct exported_not_correct)

theorem certified_arithmetic_correct:
  "decode_smt_word (smt_eval (evm_inputs x y) (certified_expression op)) =
    Some (certified_hol_result op x y)"
  by (simp add: certified_arithmetic_eval decode_smt_word_def
      smt_int_to_uint256_pack)

theorem certified_arithmetic_type:
  "smt_type (certified_expression op) = Some (SBV 256)"
  by (cases op) (simp_all add: exported_add_type exported_sub_type
      exported_eq_type exported_iszero_type exported_and_type
      exported_or_type exported_xor_type exported_not_type)

theorem certified_arithmetic_inputs:
  "smt_inputs (certified_expression op) \<subseteq> {(0, 256), (1, 256)}"
  by (cases op) (simp_all only: certified_expression.simps
      exported_add_inputs exported_sub_inputs
      exported_eq_inputs exported_iszero_inputs exported_and_inputs
      exported_or_inputs exported_xor_inputs exported_not_inputs)

theorem certified_arithmetic_inputs_consistent:
  "smt_inputs_consistent (certified_expression op)"
  using certified_arithmetic_inputs[of op]
  by (auto simp: smt_inputs_consistent_def)

text \<open>Fail the build if an admitted proof, evaluation oracle, or SMT oracle
  enters the transitive dependencies of the central certificates. This checks
  proof dependencies, not merely the surface syntax of the new theories.\<close>

ML \<open>
  val certificates = @{thms certified_arithmetic_correct certified_arithmetic_eval
    certified_arithmetic_type certified_arithmetic_inputs_consistent
    smt_eval_type smt_eval_wellformed}
  val _ =
    if null (Thm_Deps.all_oracles certificates) then ()
    else error "EVM SMT certificates have oracle dependencies"
\<close>


text \<open>The table-wide certificates retain the original binary interface
  above and additionally support a third operand for modular operations.
  Operand order follows the Python arithmetic-method interface. In particular,
  shifts use (value, amount), whereas BYTE and SIGNEXTEND use (index, value).

  The default interpretation supplies mathematical quotient and remainder.
  The DIV result below is therefore the mathematical reference value, not an
  assertion that the existing Knuth implementation satisfies this reference.
  Concrete-helper correspondence and mathematical refinement are distinct
  obligations. The byte certificates concern Byte and extend_sign, and do not
  by themselves prove correspondence with the separate dispatcher wrappers.\<close>

datatype table_evm_op =
  TAdd | TSub | TMul | TDiv | TMod | TSdiv | TSmod | TAddmod | TMulmod | TLt | TGt | TEq | TSlt | TSgt | TAnd | TOr | TXor | TNot | TShl | TShr | TSar | TByte | TSignextend | TIszero

fun table_expression :: "table_evm_op \<Rightarrow> smt_expr" where
  "table_expression TAdd = exported_add"
| "table_expression TSub = exported_sub"
| "table_expression TMul = exported_mul"
| "table_expression TDiv = exported_div"
| "table_expression TMod = exported_mod"
| "table_expression TSdiv = exported_sdiv"
| "table_expression TSmod = exported_smod"
| "table_expression TAddmod = exported_addmod"
| "table_expression TMulmod = exported_mulmod"
| "table_expression TLt = exported_lt"
| "table_expression TGt = exported_gt"
| "table_expression TEq = exported_eq"
| "table_expression TSlt = exported_slt"
| "table_expression TSgt = exported_sgt"
| "table_expression TAnd = exported_and"
| "table_expression TOr = exported_or"
| "table_expression TXor = exported_xor"
| "table_expression TNot = exported_not"
| "table_expression TShl = exported_shl"
| "table_expression TShr = exported_shr"
| "table_expression TSar = exported_sar"
| "table_expression TByte = exported_byte"
| "table_expression TSignextend = exported_signextend"
| "table_expression TIszero = exported_iszero"

fun table_hol_result ::
  "table_evm_op \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
  "table_hol_result TAdd x y m = (uint256_add x y)"
| "table_hol_result TSub x y m = (uint256_sub x y)"
| "table_hol_result TMul x y m = (uint256_mul x y)"
| "table_hol_result TDiv x y m = (if y = uint256_zero then uint256_zero else int_to_uint256 (uint256_to_int x div uint256_to_int y))"
| "table_hol_result TMod x y m = (if y = uint256_zero then uint256_zero else int_to_uint256 (uint256_to_int x mod uint256_to_int y))"
| "table_hol_result TSdiv x y m = (hol_sdiv_result x y)"
| "table_hol_result TSmod x y m = (hol_smod_result x y)"
| "table_hol_result TAddmod x y m = (if m = uint256_zero then uint256_zero else int_to_uint256 ((uint256_to_int x + uint256_to_int y) mod uint256_to_int m))"
| "table_hol_result TMulmod x y m = (if m = uint256_zero then uint256_zero else int_to_uint256 ((uint256_to_int x * uint256_to_int y) mod uint256_to_int m))"
| "table_hol_result TLt x y m = (if uint256_lt x y then uint256_one else uint256_zero)"
| "table_hol_result TGt x y m = (if uint256_gt x y then uint256_one else uint256_zero)"
| "table_hol_result TEq x y m = (if x = y then uint256_one else uint256_zero)"
| "table_hol_result TSlt x y m = (if word_sless (uint256_to_word256 x) (uint256_to_word256 y) then uint256_one else uint256_zero)"
| "table_hol_result TSgt x y m = (if word_sless (uint256_to_word256 y) (uint256_to_word256 x) then uint256_one else uint256_zero)"
| "table_hol_result TAnd x y m = (uint256_and x y)"
| "table_hol_result TOr x y m = (uint256_or x y)"
| "table_hol_result TXor x y m = (uint256_xor x y)"
| "table_hol_result TNot x y m = (uint256_not x)"
| "table_hol_result TShl x y m = (Lsh y x)"
| "table_hol_result TShr x y m = (Rsh y x)"
| "table_hol_result TSar x y m = (SRsh y x)"
| "table_hol_result TByte x y m = (Byte y x)"
| "table_hol_result TSignextend x y m = (extend_sign y x)"
| "table_hol_result TIszero x y m = (if x = uint256_zero then uint256_one else uint256_zero)"

lemma binary_eval_ternary:
  assumes "smt_inputs e \<subseteq> {(0,256),(1,256)}"
  shows "smt_eval_with uf (evm_inputs3 x y m) e = smt_eval_with uf (evm_inputs x y) e"
  apply (rule smt_eval_environment_cong)
  using assms by (auto simp: evm_inputs3_def evm_inputs_def)

lemmas binary_exported_eval =
  binary_eval_ternary[OF exported_add_inputs]
  binary_eval_ternary[OF exported_sub_inputs]
  binary_eval_ternary[OF exported_mul_inputs]
  binary_eval_ternary[OF exported_div_inputs]
  binary_eval_ternary[OF exported_mod_inputs]
  binary_eval_ternary[OF exported_sdiv_inputs]
  binary_eval_ternary[OF exported_smod_inputs]
  binary_eval_ternary[OF exported_lt_inputs]
  binary_eval_ternary[OF exported_gt_inputs]
  binary_eval_ternary[OF exported_eq_inputs]
  binary_eval_ternary[OF exported_slt_inputs]
  binary_eval_ternary[OF exported_sgt_inputs]
  binary_eval_ternary[OF exported_and_inputs]
  binary_eval_ternary[OF exported_or_inputs]
  binary_eval_ternary[OF exported_xor_inputs]
  binary_eval_ternary[OF exported_not_inputs]
  binary_eval_ternary[OF exported_shl_inputs]
  binary_eval_ternary[OF exported_shr_inputs]
  binary_eval_ternary[OF exported_sar_inputs]
  binary_eval_ternary[OF exported_byte_inputs]
  binary_eval_ternary[OF exported_signextend_inputs]
  binary_eval_ternary[OF exported_iszero_inputs]

theorem table_arithmetic_eval:
  "smt_eval (evm_inputs3 x y m) (table_expression op) =
    Some (BVV 256 (uint256_to_int (table_hol_result op x y m)))"
  by (cases op) (simp_all add: binary_exported_eval
    exported_add_correct exported_sub_correct exported_mul_correct
    exported_div_reference_correct exported_mod_correct exported_sdiv_correct
    exported_smod_correct exported_addmod_correct exported_mulmod_correct
    exported_lt_correct exported_gt_correct exported_eq_correct
    exported_slt_correct exported_sgt_correct exported_and_correct
    exported_or_correct exported_xor_correct exported_not_correct
    exported_shl_correct exported_shr_correct exported_sar_correct
    exported_byte_correct exported_signextend_correct exported_iszero_correct
    uint256_slt_word_sless uint256_sgt_word_sless)

theorem table_arithmetic_correct:
  "decode_smt_word (smt_eval (evm_inputs3 x y m) (table_expression op)) =
    Some (table_hol_result op x y m)"
  by (simp add: table_arithmetic_eval decode_smt_word_def smt_int_to_uint256_pack)

theorem table_arithmetic_type:
  "smt_type (table_expression op) = Some (SBV 256)"
  by (cases op) (simp_all add:
    exported_add_type exported_sub_type exported_mul_type exported_div_type
    exported_mod_type exported_sdiv_type exported_smod_type exported_addmod_type
    exported_mulmod_type exported_lt_type exported_gt_type exported_eq_type
    exported_slt_type exported_sgt_type exported_and_type exported_or_type
    exported_xor_type exported_not_type exported_shl_type exported_shr_type
    exported_sar_type exported_byte_type exported_signextend_type exported_iszero_type)

theorem table_arithmetic_inputs:
  "smt_inputs (table_expression op) \<subseteq> {(0,256),(1,256),(2,256)}"
  using
    exported_add_inputs exported_sub_inputs exported_mul_inputs exported_div_inputs
    exported_mod_inputs exported_sdiv_inputs exported_smod_inputs exported_addmod_inputs
    exported_mulmod_inputs exported_lt_inputs exported_gt_inputs exported_eq_inputs
    exported_slt_inputs exported_sgt_inputs exported_and_inputs exported_or_inputs
    exported_xor_inputs exported_not_inputs exported_shl_inputs exported_shr_inputs
    exported_sar_inputs exported_byte_inputs exported_signextend_inputs exported_iszero_inputs
  by (cases op) auto

theorem table_arithmetic_inputs_consistent:
  "smt_inputs_consistent (table_expression op)"
  using table_arithmetic_inputs[of op]
  by (auto simp: smt_inputs_consistent_def)

definition requires_summary :: "table_evm_op \<Rightarrow> bool" where
  "requires_summary op \<longleftrightarrow> op \<in> {TDiv, TMod, TSdiv, TSmod, TAddmod}"

lemma table_summary_free:
  "\<not> requires_summary op \<Longrightarrow> smt_ufs (table_expression op) = {}"
  by (cases op) (simp_all add: requires_summary_def
    exported_add_ufs exported_sub_ufs exported_mul_ufs exported_div_ufs
    exported_mod_ufs exported_sdiv_ufs exported_smod_ufs exported_addmod_ufs
    exported_mulmod_ufs exported_lt_ufs exported_gt_ufs exported_eq_ufs
    exported_slt_ufs exported_sgt_ufs exported_and_ufs exported_or_ufs
    exported_xor_ufs exported_not_ufs exported_shl_ufs exported_shr_ufs
    exported_sar_ufs exported_byte_ufs exported_signextend_ufs exported_iszero_ufs)

theorem table_arithmetic_eval_summary_free:
  assumes "\<not> requires_summary op"
  shows "smt_eval_with uf (evm_inputs3 x y m) (table_expression op) =
    Some (BVV 256 (uint256_to_int (table_hol_result op x y m)))"
proof -
  have "smt_eval_with uf (evm_inputs3 x y m) (table_expression op) =
      smt_eval (evm_inputs3 x y m) (table_expression op)"
    by (rule smt_eval_uf_free[OF table_summary_free[OF assms]])
  also have "... = Some (BVV 256 (uint256_to_int (table_hol_result op x y m)))"
    by (rule table_arithmetic_eval)
  finally show ?thesis .
qed

theorem table_arithmetic_eval_with_contract:
  assumes "\<And>f a b. f \<in> smt_ufs (table_expression op) \<Longrightarrow>
    uf f a b = mathematical_uf f a b"
  shows "smt_eval_with uf (evm_inputs3 x y m) (table_expression op) =
    Some (BVV 256 (uint256_to_int (table_hol_result op x y m)))"
proof -
  have "smt_eval_with uf (evm_inputs3 x y m) (table_expression op) =
      smt_eval (evm_inputs3 x y m) (table_expression op)"
    by (rule smt_eval_uf_cong) (use assms in blast)
  then show ?thesis by (simp add: table_arithmetic_eval)
qed

ML \<open>
  val certificates = @{thms table_arithmetic_eval table_arithmetic_correct
    table_arithmetic_type table_arithmetic_inputs_consistent
    table_arithmetic_eval_summary_free table_arithmetic_eval_with_contract
    smt_eval_with_type smt_eval_with_wellformed}
  val _ = if null (Thm_Deps.all_oracles certificates) then ()
    else error "Table-wide SMT certificates have oracle dependencies"
\<close>

end
