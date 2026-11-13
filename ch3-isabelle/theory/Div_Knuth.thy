theory Div_Knuth
  imports Div_Knuth_Loop Div_Knuth_Step_Proof
begin

lemma udivremKnuth_correct:
  fixes d u :: uint256 and u4 :: u64 and ulen :: nat
  assumes length: "2\<le>dLen d" "dLen d\<le>ulen" "ulen\<le>4"
    and normalized: "2^63\<le>uint (getword d (dLen d-1))"
    and divisor: "0<uint256_to_int d" "uint256_to_int d<(2^64)^(dLen d)"
    and bound: "uint256_u4_to_int (u,u4)<uint256_to_int d*(2^64)^Suc (ulen-dLen d)"
  shows "uint256_to_int (fst (udivremKnuth uint256_zero u u4 d ulen)) =
      uint256_u4_to_int (u,u4) div uint256_to_int d \<and>
    uint256_u4_to_int (snd (udivremKnuth uint256_zero u u4 d ulen)) =
      uint256_u4_to_int (u,u4) mod uint256_to_int d"
proof -
  let ?n = "ulen-dLen d"
  let ?D = "uint256_to_int d"
  let ?B = "(2::int)^64"
  have index: "?n+dLen d\<le>4" using length by arith
  have zero: "\<And>i. i\<le>?n \<Longrightarrow> getword uint256_zero i=0"
    by (simp add: getword_def uint256_zero_def)
  have step: "\<And>i x x4. i\<le>?n \<Longrightarrow>
      uint256_u4_to_int (x,x4) < ?D * ?B^Suc i \<Longrightarrow>
      uint (fst (knuth_step i x x4 d)) = uint256_u4_to_int (x,x4) div (?D * ?B^i) \<and>
      uint256_u4_to_int (snd (knuth_step i x x4 d)) = uint256_u4_to_int (x,x4) mod (?D * ?B^i)"
  proof -
    fix i x x4
    assume i: "i\<le>?n" and b: "uint256_u4_to_int (x,x4) < ?D*?B^Suc i"
    have index_i: "i+dLen d\<le>4" using i index by arith
    show "uint (fst (knuth_step i x x4 d)) = uint256_u4_to_int (x,x4) div (?D * ?B^i) \<and>
      uint256_u4_to_int (snd (knuth_step i x x4 d)) = uint256_u4_to_int (x,x4) mod (?D * ?B^i)"
      by (rule knuth_step_correct[OF length(1) index_i normalized divisor b])
  qed
  have qzero: "uint256_to_int uint256_zero = 0"
    by (simp add: uint256_to_int_def uint256_zero_def int_shiftl_eq_mult)
  show ?thesis
    using knuth_loop_correct_from_step[OF divisor(1) length(1) index zero bound step]
    by (simp add: udivremKnuth_def Let_def qzero)
qed

ML \<open>
val _ = if null (Thm_Deps.all_oracles @{thms udivremKnuth_correct knuth_step_correct})
  then () else error "Knuth correctness has oracle dependencies"
\<close>

end
