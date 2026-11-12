theory SMT_BV
  imports Main
begin

text \<open>A deliberately small deep embedding of the quantifier-free SMT
  expressions used by the arithmetic exporter. Widths are explicit, and malformed
  terms have no sort and no interpretation. The valuation assigns integers to
  numbered bit-vector inputs. Variables and constants reduce modulo their width.
  The two declared arithmetic function symbols have an explicit interpretation.
  No solver oracle supplies a proof in this theory.\<close>

datatype smt_sort = SBool | SBV nat
datatype smt_value = BoolV bool | BVV nat int
datatype smt_bv_binop = BVAdd | BVSub | BVMul | BVAnd | BVOr | BVXor
datatype smt_bv_wideop = BVUDiv | BVURem | BVShl | BVLshr | BVAshr
datatype smt_cmp = BVUlt | BVUle | BVUgt | BVUge | BVSlt | BVSle | BVSgt | BVSge

datatype smt_uf = HolimanUDiv | HolimanURem

datatype smt_expr =
    BVConst nat int
  | BVVar nat nat
  | BoolConst bool
  | BVBin smt_bv_binop smt_expr smt_expr
  | BVWide smt_bv_wideop smt_expr smt_expr
  | BVUF smt_uf smt_expr smt_expr
  | BVNot smt_expr
  | BVConcat smt_expr smt_expr
  | BVExtract nat nat smt_expr
  | BVZeroExt nat smt_expr
  | SMTEq smt_expr smt_expr
  | SMTNot smt_expr
  | SMTAnd smt_expr smt_expr
  | SMTOr smt_expr smt_expr
  | SMTIte smt_expr smt_expr smt_expr
  | BVCmp smt_cmp smt_expr smt_expr

fun smt_inputs :: "smt_expr \<Rightarrow> (nat \<times> nat) set" where
  "smt_inputs (BVConst w x) = {}"
| "smt_inputs (BVVar w n) = {(n, w)}"
| "smt_inputs (BoolConst b) = {}"
| "smt_inputs (BVBin op a b) = smt_inputs a \<union> smt_inputs b"
| "smt_inputs (BVWide op a b) = smt_inputs a \<union> smt_inputs b"
| "smt_inputs (BVUF f a b) = smt_inputs a \<union> smt_inputs b"
| "smt_inputs (BVNot a) = smt_inputs a"
| "smt_inputs (BVConcat a b) = smt_inputs a \<union> smt_inputs b"
| "smt_inputs (BVExtract hi lo a) = smt_inputs a"
| "smt_inputs (BVZeroExt n a) = smt_inputs a"
| "smt_inputs (SMTEq a b) = smt_inputs a \<union> smt_inputs b"
| "smt_inputs (SMTNot a) = smt_inputs a"
| "smt_inputs (SMTAnd a b) = smt_inputs a \<union> smt_inputs b"
| "smt_inputs (SMTOr a b) = smt_inputs a \<union> smt_inputs b"
| "smt_inputs (SMTIte c a b) = smt_inputs c \<union> smt_inputs a \<union> smt_inputs b"
| "smt_inputs (BVCmp cmp a b) = smt_inputs a \<union> smt_inputs b"

fun smt_ufs :: "smt_expr \<Rightarrow> smt_uf set" where
  "smt_ufs (BVConst w x) = {}"
| "smt_ufs (BVVar w n) = {}"
| "smt_ufs (BoolConst b) = {}"
| "smt_ufs (BVBin op a b) = smt_ufs a \<union> smt_ufs b"
| "smt_ufs (BVWide op a b) = smt_ufs a \<union> smt_ufs b"
| "smt_ufs (BVUF f a b) = {f} \<union> smt_ufs a \<union> smt_ufs b"
| "smt_ufs (BVNot a) = smt_ufs a"
| "smt_ufs (BVConcat a b) = smt_ufs a \<union> smt_ufs b"
| "smt_ufs (BVExtract hi lo a) = smt_ufs a"
| "smt_ufs (BVZeroExt n a) = smt_ufs a"
| "smt_ufs (SMTEq a b) = smt_ufs a \<union> smt_ufs b"
| "smt_ufs (SMTNot a) = smt_ufs a"
| "smt_ufs (SMTAnd a b) = smt_ufs a \<union> smt_ufs b"
| "smt_ufs (SMTOr a b) = smt_ufs a \<union> smt_ufs b"
| "smt_ufs (SMTIte c a b) = smt_ufs c \<union> smt_ufs a \<union> smt_ufs b"
| "smt_ufs (BVCmp cmp a b) = smt_ufs a \<union> smt_ufs b"

definition smt_inputs_consistent :: "smt_expr \<Rightarrow> bool" where
  "smt_inputs_consistent e \<longleftrightarrow>
   (\<forall>n w v. (n, w) \<in> smt_inputs e \<longrightarrow>
     (n, v) \<in> smt_inputs e \<longrightarrow> w = v)"

text \<open>Input identifiers have one global declared width. Exported artifacts
  additionally certify their input declaration set. This rules out treating the
  same SMT variable as two different bit-vector sorts.\<close>

lemma fixed_width_inputs_consistent:
  "smt_inputs e \<subseteq> {(n, w) |n. n \<in> ns} \<Longrightarrow> smt_inputs_consistent e"
  by (auto simp: smt_inputs_consistent_def)

definition bv_norm :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "bv_norm w x = x mod 2 ^ w"

definition bv_signed :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "bv_signed w x = (if x < 2 ^ (w - 1) then x else x - 2 ^ w)"

fun bv_bin :: "smt_bv_binop \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "bv_bin BVAdd x y = x + y"
| "bv_bin BVSub x y = x - y"
| "bv_bin BVMul x y = x * y"
| "bv_bin BVAnd x y = and x y"
| "bv_bin BVOr x y = or x y"
| "bv_bin BVXor x y = xor x y"

fun bv_wide :: "smt_bv_wideop \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "bv_wide BVUDiv w x y = (if y = 0 then 2^w - 1 else x div y)"
| "bv_wide BVURem w x y = (if y = 0 then x else x mod y)"
| "bv_wide BVShl w x y = (if y \<ge> int w then 0 else x * 2^(nat y))"
| "bv_wide BVLshr w x y = (if y \<ge> int w then 0 else x div 2^(nat y))"
| "bv_wide BVAshr w x y =
    (if y \<ge> int w then (if bv_signed w x < 0 then -1 else 0)
     else bv_signed w x div 2^(nat y))"

fun bv_compare :: "smt_cmp \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "bv_compare BVUlt w x y = (x < y)"
| "bv_compare BVUle w x y = (x \<le> y)"
| "bv_compare BVUgt w x y = (x > y)"
| "bv_compare BVUge w x y = (x \<ge> y)"
| "bv_compare BVSlt w x y = (bv_signed w x < bv_signed w y)"
| "bv_compare BVSle w x y = (bv_signed w x \<le> bv_signed w y)"
| "bv_compare BVSgt w x y = (bv_signed w x > bv_signed w y)"
| "bv_compare BVSge w x y = (bv_signed w x \<ge> bv_signed w y)"

fun smt_type :: "smt_expr \<Rightarrow> smt_sort option" where
  "smt_type (BVConst w x) = (if w > 0 then Some (SBV w) else None)"
| "smt_type (BVVar w n) = (if w > 0 then Some (SBV w) else None)"
| "smt_type (BoolConst b) = Some SBool"
| "smt_type (BVBin op a b) = (case (smt_type a, smt_type b) of
     (Some (SBV w), Some (SBV v)) \<Rightarrow> if w = v then Some (SBV w) else None
   | _ \<Rightarrow> None)"
| "smt_type (BVWide op a b) = (case (smt_type a, smt_type b) of
     (Some (SBV w), Some (SBV v)) \<Rightarrow> if w = v then Some (SBV w) else None
   | _ \<Rightarrow> None)"
| "smt_type (BVUF f a b) =
    (if smt_type a = Some (SBV 256) \<and> smt_type b = Some (SBV 256)
     then Some (SBV 256) else None)"
| "smt_type (BVNot a) = (case smt_type a of
     Some (SBV w) \<Rightarrow> Some (SBV w) | _ \<Rightarrow> None)"
| "smt_type (BVConcat a b) = (case (smt_type a, smt_type b) of
     (Some (SBV w), Some (SBV v)) \<Rightarrow> Some (SBV (w + v))
   | _ \<Rightarrow> None)"
| "smt_type (BVExtract hi lo a) = (case smt_type a of
     Some (SBV w) \<Rightarrow>
       if lo \<le> hi \<and> hi < w then Some (SBV (hi - lo + 1)) else None
   | _ \<Rightarrow> None)"
| "smt_type (BVZeroExt n a) = (case smt_type a of
     Some (SBV w) \<Rightarrow> Some (SBV (n + w)) | _ \<Rightarrow> None)"
| "smt_type (SMTEq a b) = (case (smt_type a, smt_type b) of
     (Some s, Some t) \<Rightarrow> if s = t then Some SBool else None
   | _ \<Rightarrow> None)"
| "smt_type (SMTNot a) = (if smt_type a = Some SBool then Some SBool else None)"
| "smt_type (SMTAnd a b) =
     (if smt_type a = Some SBool \<and> smt_type b = Some SBool then Some SBool else None)"
| "smt_type (SMTOr a b) =
     (if smt_type a = Some SBool \<and> smt_type b = Some SBool then Some SBool else None)"
| "smt_type (SMTIte c a b) = (case (smt_type c, smt_type a, smt_type b) of
     (Some SBool, Some s, Some t) \<Rightarrow> if s = t then Some s else None
   | _ \<Rightarrow> None)"
| "smt_type (BVCmp cmp a b) = (case (smt_type a, smt_type b) of
     (Some (SBV w), Some (SBV v)) \<Rightarrow> if w = v then Some SBool else None
   | _ \<Rightarrow> None)"

fun value_sort :: "smt_value \<Rightarrow> smt_sort" where
  "value_sort (BoolV b) = SBool"
| "value_sort (BVV w x) = SBV w"

fun smt_eval_with :: "(smt_uf \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> smt_expr \<Rightarrow> smt_value option" where
  "smt_eval_with uf env (BVConst w x) =
     (if w > 0 then Some (BVV w (bv_norm w x)) else None)"
| "smt_eval_with uf env (BVVar w n) =
     (if w > 0 then Some (BVV w (bv_norm w (env n))) else None)"
| "smt_eval_with uf env (BoolConst b) = Some (BoolV b)"
| "smt_eval_with uf env (BVBin op a b) = (case (smt_eval_with uf env a, smt_eval_with uf env b) of
     (Some (BVV w x), Some (BVV v y)) \<Rightarrow>
       if w = v then Some (BVV w (bv_norm w (bv_bin op x y))) else None
   | _ \<Rightarrow> None)"
| "smt_eval_with uf env (BVWide op a b) = (case (smt_eval_with uf env a, smt_eval_with uf env b) of
     (Some (BVV w x), Some (BVV v y)) \<Rightarrow>
       if w = v then Some (BVV w (bv_norm w (bv_wide op w x y))) else None
   | _ \<Rightarrow> None)"
| "smt_eval_with uf env (BVUF f a b) = (case (smt_eval_with uf env a, smt_eval_with uf env b) of
     (Some (BVV w x), Some (BVV v y)) \<Rightarrow>
       if w = 256 \<and> v = 256 then Some (BVV 256 (bv_norm 256 (uf f x y))) else None
   | _ \<Rightarrow> None)"
| "smt_eval_with uf env (BVNot a) = (case smt_eval_with uf env a of
     Some (BVV w x) \<Rightarrow> Some (BVV w (bv_norm w (not x)))
   | _ \<Rightarrow> None)"
| "smt_eval_with uf env (BVConcat a b) = (case (smt_eval_with uf env a, smt_eval_with uf env b) of
     (Some (BVV w x), Some (BVV v y)) \<Rightarrow>
       Some (BVV (w + v) (bv_norm (w + v) (x * 2 ^ v + y)))
   | _ \<Rightarrow> None)"
| "smt_eval_with uf env (BVExtract hi lo a) = (case smt_eval_with uf env a of
     Some (BVV w x) \<Rightarrow>
       if lo \<le> hi \<and> hi < w
       then Some (BVV (hi - lo + 1) (bv_norm (hi - lo + 1) (x div 2 ^ lo)))
       else None
   | _ \<Rightarrow> None)"
| "smt_eval_with uf env (BVZeroExt n a) = (case smt_eval_with uf env a of
     Some (BVV w x) \<Rightarrow> Some (BVV (n + w) (bv_norm (n + w) x))
   | _ \<Rightarrow> None)"
| "smt_eval_with uf env (SMTEq a b) = (case (smt_eval_with uf env a, smt_eval_with uf env b) of
     (Some x, Some y) \<Rightarrow>
       if value_sort x = value_sort y then Some (BoolV (x = y)) else None
   | _ \<Rightarrow> None)"
| "smt_eval_with uf env (SMTNot a) = (case smt_eval_with uf env a of
     Some (BoolV b) \<Rightarrow> Some (BoolV (\<not> b)) | _ \<Rightarrow> None)"
| "smt_eval_with uf env (SMTAnd a b) = (case (smt_eval_with uf env a, smt_eval_with uf env b) of
     (Some (BoolV x), Some (BoolV y)) \<Rightarrow> Some (BoolV (x \<and> y))
   | _ \<Rightarrow> None)"
| "smt_eval_with uf env (SMTOr a b) = (case (smt_eval_with uf env a, smt_eval_with uf env b) of
     (Some (BoolV x), Some (BoolV y)) \<Rightarrow> Some (BoolV (x \<or> y))
   | _ \<Rightarrow> None)"
| "smt_eval_with uf env (SMTIte c a b) = (case (smt_eval_with uf env c, smt_eval_with uf env a, smt_eval_with uf env b) of
     (Some (BoolV p), Some x, Some y) \<Rightarrow>
       if value_sort x = value_sort y then Some (if p then x else y) else None
   | _ \<Rightarrow> None)"
| "smt_eval_with uf env (BVCmp cmp a b) = (case (smt_eval_with uf env a, smt_eval_with uf env b) of
     (Some (BVV w x), Some (BVV v y)) \<Rightarrow>
       if w = v then Some (BoolV (bv_compare cmp w x y)) else None
   | _ \<Rightarrow> None)"


text \<open>The default interpretation is an explicit arithmetic contract for
  the two production summaries. It is not a claim about all interpretations
  permitted by the unconstrained Z3 function declarations.\<close>

fun mathematical_uf :: "smt_uf \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "mathematical_uf HolimanUDiv x y = (if y = 0 then 0 else x div y)"
| "mathematical_uf HolimanURem x y = (if y = 0 then 0 else x mod y)"

abbreviation smt_eval :: "(nat \<Rightarrow> int) \<Rightarrow> smt_expr \<Rightarrow> smt_value option" where
  "smt_eval env e \<equiv> smt_eval_with mathematical_uf env e"

lemma smt_eval_uf_cong:
  assumes "\<forall>f \<in> smt_ufs e. \<forall>x y. uf f x y = vf f x y"
  shows "smt_eval_with uf env e = smt_eval_with vf env e"
  using assms
  by (induction e) (auto split: option.splits smt_value.splits)

lemma smt_eval_uf_free:
  "smt_ufs e = {} \<Longrightarrow> smt_eval_with uf env e = smt_eval env e"
  by (rule smt_eval_uf_cong) simp


fun value_wellformed :: "smt_value \<Rightarrow> bool" where
  "value_wellformed (BoolV b) = True"
| "value_wellformed (BVV w x) = (w > 0 \<and> 0 \<le> x \<and> x < 2 ^ w)"

lemma bv_norm_nonnegative [simp]: "0 \<le> bv_norm w x"
  by (simp add: bv_norm_def)

lemma bv_norm_less [simp]: "bv_norm w x < 2 ^ w"
  by (simp add: bv_norm_def)

lemma bv_norm_idem [simp]: "bv_norm w (bv_norm w x) = bv_norm w x"
  by (simp add: bv_norm_def)

lemma bv_norm_small:
  "0 \<le> x \<Longrightarrow> x < 2 ^ w \<Longrightarrow> bv_norm w x = x"
  by (simp add: bv_norm_def)

lemma bv_norm_eq_take_bit: "bv_norm w x = take_bit w x"
  by (simp add: bv_norm_def take_bit_eq_mod)

lemma bv_norm_nested:
  "bv_norm w (bv_norm v x) = bv_norm (min w v) x"
  by (simp add: bv_norm_eq_take_bit take_bit_take_bit)

lemma bv_norm_add:
  "bv_norm w (bv_norm w x + bv_norm w y) = bv_norm w (x + y)"
  by (simp add: bv_norm_def mod_add_eq)

lemma bv_norm_sub:
  "bv_norm w (bv_norm w x - bv_norm w y) = bv_norm w (x - y)"
  by (simp add: bv_norm_def mod_diff_eq)

lemma bv_norm_mul:
  "bv_norm w (bv_norm w x * bv_norm w y) = bv_norm w (x * y)"
  by (simp add: bv_norm_def mod_mult_eq)

text \<open>The following results certify the interpreter itself. In particular,
  a successful interpretation never silently coerces Boolean and bit-vector
  values, and every returned bit-vector has exactly its declared width.\<close>

lemma smt_eval_with_type:
  "smt_eval_with uf env e = Some v \<Longrightarrow> smt_type e = Some (value_sort v)"
  by (induction e arbitrary: v)
     (auto split: option.splits smt_value.splits smt_sort.splits if_splits)

lemma smt_eval_with_sort:
  "map_option value_sort (smt_eval_with uf env e) = smt_type e"
  apply (induction e)
  apply (auto split: option.splits smt_value.splits smt_sort.splits if_splits)
  apply (rule exI, erule sym)+
  done

lemma smt_eval_with_complete:
  "smt_type e = Some s \<Longrightarrow>
   \<exists>v. smt_eval_with uf env e = Some v \<and> value_sort v = s"
  using smt_eval_with_sort[of uf env e] by (cases "smt_eval_with uf env e") auto

lemma smt_eval_with_wellformed:
  "smt_eval_with uf env e = Some v \<Longrightarrow> value_wellformed v"
  by (induction e arbitrary: v)
     (auto simp: bv_norm_def split: option.splits smt_value.splits if_splits)

lemma illtyped_has_no_value_with:
  "smt_type e = None \<Longrightarrow> smt_eval_with uf env e = None"
  using smt_eval_with_type by (metis option.distinct(1) option.exhaust)

lemmas smt_eval_type = smt_eval_with_type[where uf = mathematical_uf]
lemmas smt_eval_sort = smt_eval_with_sort[where uf = mathematical_uf]
lemmas smt_eval_complete = smt_eval_with_complete[where uf = mathematical_uf]
lemmas smt_eval_wellformed = smt_eval_with_wellformed[where uf = mathematical_uf]
lemmas illtyped_has_no_value = illtyped_has_no_value_with[where uf = mathematical_uf]

end
