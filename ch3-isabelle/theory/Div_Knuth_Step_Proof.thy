theory Div_Knuth_Step_Proof
  imports Div_Knuth_Step Div_Knuth_Decomposition
begin

lemma knuth_step_correct_from_trial:
  fixes d u :: uint256 and u4 :: u64 and j :: nat
  assumes index: "j+dLen d\<le>4"
    and divisor: "0<uint256_to_int d" "uint256_to_int d<(2^64)^(dLen d)"
    and bound: "uint256_u4_to_int (u,u4)<uint256_to_int d*(2^64)^Suc j"
    and lower: "(uint (knuth_trial j u u4 d)-1)*(uint256_to_int d*(2^64)^j)<uint256_u4_to_int (u,u4)"
    and upper: "uint256_u4_to_int (u,u4)<(uint (knuth_trial j u u4 d)+1)*(uint256_to_int d*(2^64)^j)"
  shows "uint (fst (knuth_step j u u4 d)) = uint256_u4_to_int (u,u4) div (uint256_to_int d*(2^64)^j) \<and>
    uint256_u4_to_int (snd (knuth_step j u u4 d)) = uint256_u4_to_int (u,u4) mod (uint256_to_int d*(2^64)^j)"
proof -
  let ?B = "(2::int)^64"
  let ?D = "uint256_to_int d * ?B^j"
  let ?P = "?B^(j+dLen d)"
  let ?N = "uint256_u4_to_int (u,u4)"
  have dp: "0<?D" using divisor(1) by simp
  have du: "?D<?P"
    unfolding power_add using divisor(2)
    by (simp add: mult.commute)
  have cu: "uint256_to_int d*?B^Suc j < ?B^Suc (j+dLen d)"
    using du by (simp only: power_Suc; simp add: algebra_simps)
  have cap: "?N < ?B^Suc (j+dLen d)" using bound cu by linarith
  show ?thesis unfolding knuth_step_def
    by (rule knuth_post_subtract_correct[OF index dp du cap lower upper])
qed

lemma knuth_step_correct:
  fixes d u :: uint256 and u4 :: u64 and j :: nat
  assumes dlen: "2\<le>dLen d"
    and index: "j+dLen d\<le>4"
    and normalized: "2^63\<le>uint (getword d (dLen d-1))"
    and divisor: "0<uint256_to_int d" "uint256_to_int d<(2^64)^(dLen d)"
    and bound: "uint256_u4_to_int (u,u4)<uint256_to_int d*(2^64)^Suc j"
  shows "uint (fst (knuth_step j u u4 d)) = uint256_u4_to_int (u,u4) div (uint256_to_int d*(2^64)^j) \<and>
    uint256_u4_to_int (snd (knuth_step j u u4 d)) = uint256_u4_to_int (u,u4) mod (uint256_to_int d*(2^64)^j)"
proof -
  let ?B = "(2::int)^64"
  let ?m = "dLen d"
  let ?k = "j+?m"
  let ?W = "?B^(?k-2)"
  let ?N = "uint256_u4_to_int (u,u4)"
  let ?D = "uint256_to_int d * ?B^j"
  let ?dt = "(uint256_to_int d mod ?B^(?m-2))*?B^j"
  have mhi: "?m\<le>4" and klo: "2\<le>?k" using index dlen by arith+
  have du: "?D < ?B^?k"
    unfolding power_add using divisor(2) by (simp add: mult.commute)
  have cu: "uint256_to_int d*?B^Suc j < ?B^Suc ?k"
    using du by (simp only: power_Suc; simp add: algebra_simps)
  have cap: "?N < ?B^Suc ?k" using bound cu by linarith
  have nval: "?N = (uint (getword_u u ?k u4)*?B+uint (getword u (?k-1)))*(?B*?W) +
      uint (getword u (?k-2))*?W + ?N mod ?W"
    by (rule uint256_u4_three_digits[OF klo index cap])
  have dval: "?D = uint (getword d (?m-1))*(?B*?W)+uint (getword d (?m-2))*?W+?dt"
    and dt: "0\<le>?dt" "?dt<?W"
    using knuth_divisor_digits[OF dlen mhi divisor(2), of j]
    by (simp_all only: power_mult)
  have wp: "0<?W" by simp
  have ut: "0\<le>?N mod ?W" "?N mod ?W<?W" by simp_all
  have trialcap: "?N<?B*?D" using bound by (simp add: power_Suc algebra_simps)
  have lower: "(uint (knuth_trial j u u4 d)-1)*?D<?N"
    and upper: "?N<(uint (knuth_trial j u u4 d)+1)*?D"
    unfolding knuth_trial_as_words
    by (rule knuth_trial_words_bounds[OF normalized wp dt ut dval nval trialcap])+
  show ?thesis
    by (rule knuth_step_correct_from_trial[OF index divisor bound lower upper])
qed

end
