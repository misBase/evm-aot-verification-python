theory Div_Knuth_Loop
  imports Div_Knuth_Step
begin

lemma getword_update_other:
  assumes "i<4" "k<4" "i\<noteq>k"
  shows "getword (update_word_uint256 x i w) k = getword x k"
  using assms by (auto simp: update_word_uint256_def getword_def)

lemma knuth_loop_zero_as_step:
 "udivrem_knuth_loop 0 u u4 d (getword d (dLen d-1)) (getword d (dLen d-2))
    (reciprocal2by1 (getword d (dLen d-1))) quot =
    (let (q,r,r4)=knuth_step 0 u u4 d in (update_word_uint256 quot 0 q,r,r4))"
  by (simp only: udivrem_knuth_loop.simps knuth_step_def knuth_trial_def
       knuth_post_subtract_def Let_def split_def add_0 add_0_left prod.collapse fst_conv snd_conv)

lemma knuth_loop_Suc_as_step:
 "udivrem_knuth_loop (Suc n) u u4 d (getword d (dLen d-1)) (getword d (dLen d-2))
    (reciprocal2by1 (getword d (dLen d-1))) quot =
    (let (q,r,r4)=knuth_step (Suc n) u u4 d in
     udivrem_knuth_loop n r r4 d (getword d (dLen d-1)) (getword d (dLen d-2))
       (reciprocal2by1 (getword d (dLen d-1))) (update_word_uint256 quot (Suc n) q))"
  by (simp only: udivrem_knuth_loop.simps knuth_step_def knuth_trial_def
       knuth_post_subtract_def Let_def split_def add_0 add_0_left prod.collapse fst_conv snd_conv)

lemma knuth_quotient_composition:
  fixes N D P :: int
  assumes "D>0" "P>0"
  shows "(N div (D*P))*P+(N mod (D*P)) div D = N div D"
proof -
  have decomp: "N = N mod (D*P) + (N div (D*P))*P*D"
    using div_mult_mod_eq[of N "D*P"] by (simp add: algebra_simps)
  have nz: "D \<noteq> 0" using assms by simp
  have "(N div (D*P))*P+(N mod (D*P)) div D =
      (N mod (D*P) + (N div (D*P))*P*D) div D"
    by (rule div_mult_self1[symmetric, OF nz])
  also have "... = N div D" by (simp only: decomp[symmetric])
  finally show ?thesis .
qed

abbreviation knuth_run where
 "knuth_run j u u4 d quot \<equiv>
  udivrem_knuth_loop j u u4 d (getword d (dLen d-1)) (getword d (dLen d-2))
   (reciprocal2by1 (getword d (dLen d-1))) quot"

lemma knuth_loop_correct_from_step:
  fixes d u quot :: uint256 and u4 :: u64 and n :: nat
  assumes dpos: "0 < uint256_to_int d"
    and dlen: "2 \<le> dLen d"
    and index: "n + dLen d \<le> 4"
    and zero: "\<And>i. i\<le>n \<Longrightarrow> getword quot i=0"
    and bound: "uint256_u4_to_int (u,u4) < uint256_to_int d * ((2::int)^64)^Suc n"
    and step: "\<And>i x x4. i\<le>n \<Longrightarrow>
      uint256_u4_to_int (x,x4) < uint256_to_int d * ((2::int)^64)^Suc i \<Longrightarrow>
      uint (fst (knuth_step i x x4 d)) = uint256_u4_to_int (x,x4) div (uint256_to_int d * ((2::int)^64)^i) \<and>
      uint256_u4_to_int (snd (knuth_step i x x4 d)) = uint256_u4_to_int (x,x4) mod (uint256_to_int d * ((2::int)^64)^i)"
  shows "uint256_to_int (fst (knuth_run n u u4 d quot)) =
      uint256_to_int quot + uint256_u4_to_int (u,u4) div uint256_to_int d \<and>
    uint256_u4_to_int (snd (knuth_run n u u4 d quot)) =
      uint256_u4_to_int (u,u4) mod uint256_to_int d"
  using index zero bound step
proof (induction n arbitrary: u u4 quot)
  case 0
  obtain q r r4 where digit: "knuth_step 0 u u4 d=(q,r,r4)"
    by (cases "knuth_step 0 u u4 d") auto
  have spec: "uint q = uint256_u4_to_int (u,u4) div uint256_to_int d"
    "uint256_u4_to_int (r,r4) = uint256_u4_to_int (u,u4) mod uint256_to_int d"
    using "0.prems"(4)[OF order_refl "0.prems"(3)] by (simp_all add: digit)
  have qvalue: "uint256_to_int (update_word_uint256 quot 0 q) = uint256_to_int quot + uint q"
    using update_word_uint256_value[of 0 quot q] "0.prems"(2)[of 0] by simp
  show ?case
    unfolding knuth_loop_zero_as_step digit
    by (simp add: Let_def qvalue spec)
next
  case (Suc n)
  let ?D = "uint256_to_int d"
  let ?B = "(2::int)^64"
  let ?N = "uint256_u4_to_int (u,u4)"
  let ?P = "?B^Suc n"
  obtain q r r4 where digit: "knuth_step (Suc n) u u4 d=(q,r,r4)"
    by (cases "knuth_step (Suc n) u u4 d") auto
  have qspec: "uint q = ?N div (?D*?P)"
    and rspec: "uint256_u4_to_int (r,r4) = ?N mod (?D*?P)"
    using Suc.prems(4)[OF order_refl Suc.prems(3)] by (simp_all add: digit)
  let ?qnew = "update_word_uint256 quot (Suc n) q"
  have index: "n+dLen d\<le>4" using Suc.prems(1) by arith
  have nsmall: "Suc n<4" using Suc.prems(1) dlen by arith
  have zero: "\<And>i. i\<le>n \<Longrightarrow> getword ?qnew i=0"
  proof -
    fix i assume i: "i\<le>n"
    have "getword ?qnew i=getword quot i"
      by (rule getword_update_other[OF nsmall]) (use i nsmall in auto)
    also have "...=0" by (rule Suc.prems(2)) (use i in arith)
    finally show "getword ?qnew i=0" .
  qed
  have bound: "uint256_u4_to_int (r,r4) < ?D*?B^Suc n"
    unfolding rspec using dpos by simp
  have step: "\<And>i x x4. i\<le>n \<Longrightarrow>
      uint256_u4_to_int (x,x4) < ?D * ?B^Suc i \<Longrightarrow>
      uint (fst (knuth_step i x x4 d)) = uint256_u4_to_int (x,x4) div (?D * ?B^i) \<and>
      uint256_u4_to_int (snd (knuth_step i x x4 d)) = uint256_u4_to_int (x,x4) mod (?D * ?B^i)"
    by (rule Suc.prems(4)) arith
  note ih = Suc.IH[OF index zero bound step]
  have qvalue: "uint256_to_int ?qnew = uint256_to_int quot + uint q*?P"
    using update_word_uint256_value[OF nsmall, of quot q] Suc.prems(2)[OF order_refl] by simp
  have compose: "(?N div (?D*?P))*?P+(?N mod (?D*?P)) div ?D = ?N div ?D"
    by (rule knuth_quotient_composition[OF dpos]) simp
  have remainder: "(?N mod (?D*?P)) mod ?D = ?N mod ?D"
    by (rule mod_mod_cancel) simp
  show ?case
    unfolding knuth_loop_Suc_as_step digit
    using ih qvalue qspec rspec compose remainder by (simp add: Let_def; linarith)
qed

end
