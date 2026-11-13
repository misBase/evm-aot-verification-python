theory Div_Reciprocal
  imports "EVM_SMT_Base.Exp"
begin

text \<open>The reciprocal-based division step uses a normalized divisor.
  Its numeric reciprocal bounds imply the two corrections produce the
  Euclidean quotient and remainder. The final theorem follows the actual
  word operations, including both carries and all modular truncations.\<close>

lemma reciprocal_remainder_bounds:
  fixes B d h l e L R :: int
  assumes B: "0 < B"
    and d: "0 < d" "d < B"
    and h: "0 \<le> h" "h < d"
    and l: "0 \<le> l" "l < B"
    and e: "0 < e" "e \<le> d"
    and L: "0 \<le> L" "L < B"
    and eq: "B * R = h * e + l * (B-d) + d * L - B*d"
  shows "-d \<le> R" "R < B"
    "R < 0 \<Longrightarrow> L < R+B"
    "0 \<le> R \<Longrightarrow> L < R \<Longrightarrow> R+d < B"
proof -
  have gap: "0 < B-d" using d by linarith
  have he0: "0 \<le> h*e" using h e by (intro mult_nonneg_nonneg) auto
  have lg0: "0 \<le> l*(B-d)" using l gap by (intro mult_nonneg_nonneg) auto
  have dL0: "0 \<le> d*L" using d L by (intro mult_nonneg_nonneg) auto
  have "B * (-d) \<le> B * R" using eq he0 lg0 dL0 by simp
  then show "-d \<le> R" by (simp only: mult_le_cancel_left_pos[OF B])
  have he_le: "h*e \<le> h*d" using e(2) h(1) by (rule mult_left_mono)
  have hd_lt: "h*d < d*d" using h(2) d(1) by (rule mult_strict_right_mono)
  have he: "h*e < d*d" using he_le hd_lt by linarith
  have lg: "l*(B-d) < B*(B-d)"
    using l(2) gap by (rule mult_strict_right_mono)
  have dL: "d*L < d*B" using L(2) d(1) by (rule mult_strict_left_mono)
  have dd: "d*d < B*d" using d by (intro mult_strict_right_mono) auto
  have "B*R < B*B" using eq he lg dL dd by (simp_all add: algebra_simps; linarith)
  then show "R < B" using B by simp
  show "R < 0 \<Longrightarrow> L < R+B"
  proof -
    assume neg: "R < 0"
    have pos: "0 < (B-d)*(l-L+B)"
      using gap l L by (intro mult_pos_pos) linarith+
    have "0 < B*(R+B-L)"
      using eq pos he0 by (simp_all add: algebra_simps; linarith)
    then have "0 < R+B-L" using B by (meson zero_less_mult_pos)
    then show "L < R+B" by linarith
  qed
  show "0 \<le> R \<Longrightarrow> L < R \<Longrightarrow> R+d < B"
  proof -
    assume r0: "0 \<le> R" and lr: "L < R"
    have dLR: "d*L < d*R" using lr d(1) by (rule mult_strict_left_mono)
    have "(B-d)*R < (B-d)*(B-d)"
      using eq he lg dLR by (simp_all add: algebra_simps; linarith)
    then have "R < B-d" using gap by simp
    then show "R+d < B" by linarith
  qed
qed

lemma reciprocal_correction:
  fixes B d R L Q :: int
  assumes B: "0 < B" and d: "0 < d" "d < B" "B \<le> 2*d"
    and bounds: "-d \<le> R" "R < B"
    and neg: "R < 0 \<Longrightarrow> L < R+B"
    and pos: "0 \<le> R \<Longrightarrow> L < R \<Longrightarrow> R+d < B"
  shows "(let r0 = R mod B;
              qr = (if r0 > L then (Q-1, (r0+d) mod B) else (Q, r0));
              q1 = fst qr; r1 = snd qr
          in if d \<le> r1 then (q1+1, r1-d) else (q1, r1)) =
    (if R < 0 then (Q-1, R+d)
     else if R < d then (Q, R) else (Q+1, R-d))"
proof (cases "R < 0")
  case True
  have rb: "0 \<le> R+B" "R+B < B" using True bounds d by linarith+
  have rm: "R mod B = R+B"
    using mod_pos_pos_trivial[OF rb] by simp
  have rd: "0 \<le> R+d" "R+d < d" "R+d < B" using bounds True d by linarith+
  have rm_d: "(R+B+d) mod B = R+d"
  proof -
    have "(R+B+d) mod B = (R+d+B) mod B" by (simp add: algebra_simps)
    also have "... = R+d" using rd by simp
    finally show ?thesis .
  qed
  show ?thesis using True neg[OF True] rm rd rm_d
    by (simp add: Let_def)
next
  case False
  have r0: "0 \<le> R" using False by simp
  have rm: "R mod B = R" using r0 bounds by simp
  show ?thesis
  proof (cases "L < R")
    case True
    have rd: "0 \<le> R+d" "R+d < B" "d \<le> R+d"
      using r0 d pos[OF r0 True] by linarith+
    have r_lt_d: "R < d" using rd d by linarith
    have rdmod: "(R+d) mod B = R+d" using rd by simp
    show ?thesis using False True rm rdmod rd r_lt_d
      by (simp add: Let_def)
  next
    case False
    show ?thesis using \<open>\<not> R < 0\<close> False rm
      by (simp add: Let_def not_less)
  qed
qed


lemma reciprocal_estimate_identity:
  fixes B d h l m e Q L :: int
  assumes recip: "m*d+e = B*B"
    and estimate: "m*h+l = (Q-1)*B+L"
  shows "B*(h*B+l-Q*d) = h*e+l*(B-d)+d*L-B*d"
proof -
  have a: "h*(m*d+e) = h*(B*B)" using recip by simp
  have b: "d*(m*h+l) = d*((Q-1)*B+L)" using estimate by simp
  show ?thesis using a b by (simp_all add: algebra_simps; linarith)
qed

lemma reciprocal_estimate_bounded:
  fixes B d h l m e :: int
  assumes B: "0 < B" and m: "B \<le> m"
    and d: "0 < d" "d < B"
    and h: "0 \<le> h" "h < d"
    and l: "0 \<le> l" "l < B"
    and e: "0 < e"
    and recip: "m*d+e = B*B"
  shows "0 \<le> m*h+l" "m*h+l < B*B"
proof -
  have m0: "0 \<le> m" using B m by linarith
  have mh0: "0 \<le> m*h" using m0 h(1) by (rule mult_nonneg_nonneg)
  show "0 \<le> m*h+l" using mh0 l by linarith
  have hd: "h \<le> d-1" using h by linarith
  have mh: "m*h \<le> m*(d-1)" using hd m0 by (rule mult_left_mono)
  show "m*h+l < B*B" using mh recip e m l by (simp_all add: algebra_simps; linarith)
qed

lemma reciprocal_correct_unwrapped:
  fixes B d h l m e Q L :: int
  defines "R \<equiv> h*B+l-Q*d"
  assumes B: "0 < B" and d: "0 < d" "d < B" "B \<le> 2*d"
    and h: "0 \<le> h" "h < d"
    and l: "0 \<le> l" "l < B"
    and e: "0 < e" "e \<le> d"
    and L: "0 \<le> L" "L < B"
    and recip: "m*d+e = B*B"
    and estimate: "m*h+l = (Q-1)*B+L"
  shows "(let r0 = R mod B;
              qr = (if r0 > L then (Q-1, (r0+d) mod B) else (Q, r0));
              q1 = fst qr; r1 = snd qr;
              result = (if d \<le> r1 then (q1+1, r1-d) else (q1, r1))
          in h*B+l = fst result*d+snd result \<and> 0 \<le> snd result \<and> snd result < d)"
proof -
  have identity: "B*R = h*e+l*(B-d)+d*L-B*d"
    unfolding R_def by (rule reciprocal_estimate_identity[OF recip estimate])
  have bounds: "-d \<le> R" "R < B"
    "R < 0 \<Longrightarrow> L < R+B"
    "0 \<le> R \<Longrightarrow> L < R \<Longrightarrow> R+d < B"
    using reciprocal_remainder_bounds[OF B d(1,2) h l e L identity] by blast+
  note corr = reciprocal_correction[OF B d bounds]
  show ?thesis
    using corr bounds d
    unfolding Let_def
    by (simp only: split_beta; split if_splits; simp_all add: R_def algebra_simps; linarith)
qed


definition reciprocal_estimate_words :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<times> u64" where
  "reciprocal_estimate_words h l v =
    (let (mh, ml) = mul64 v h;
         (ql, c) = Add64_carry ml l 0;
         (qh, _) = Add64_carry mh h c
     in (qh, ql))"

lemma reciprocal_estimate_words_correct:
  assumes bound: "(2^64 + uint v)*uint h + uint l < (2^64)*(2^64)"
  shows "uint (fst (reciprocal_estimate_words h l v))*2^64 +
         uint (snd (reciprocal_estimate_words h l v)) = (2^64 + uint v)*uint h + uint l"
proof -
  obtain mh ml where mul: "mul64 v h = (mh, ml)" by (cases "mul64 v h") auto
  obtain ql c where low: "Add64_carry ml l 0 = (ql, c)" by (cases "Add64_carry ml l 0") auto
  obtain qh c2 where high: "Add64_carry mh h c = (qh, c2)" by (cases "Add64_carry mh h c") auto
  have mulspec: "uint mh*2^64+uint ml = uint v*uint h" using mul64_spec[of v h] by (simp add: mul)
  have lowspec: "uint ql+uint c*2^64 = uint ml+uint l"
    using add64_carry_spec[of "0::u64" ml l] by (simp add: low)
  have cbound: "uint c < 2" using add64_carry_snd_lt[of ml l 0] by (simp add: low)
  have highspec: "uint qh+uint c2*2^64 = uint mh+uint h+uint c"
    using add64_carry_spec[OF cbound, of mh h] by (simp add: high)
  have total: "uint qh*2^64+uint ql+uint c2*((2^64)*(2^64)) = (2^64+uint v)*uint h+uint l"
    using mulspec lowspec highspec by (simp_all add: algebra_simps; linarith)
  have c2zero: "uint c2 = 0"
    using total bound uint_nonnegative[of qh] uint_nonnegative[of ql] uint_nonnegative[of c2]
    by (simp_all add: algebra_simps; linarith)
  show ?thesis
    unfolding reciprocal_estimate_words_def
    using total c2zero by (simp add: mul low high)
qed

definition reciprocal_correction_int :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "reciprocal_correction_int B d Q R L =
    (let r0 = R mod B;
         qr = (if r0 > L then (Q-1, (r0+d) mod B) else (Q, r0));
         q1 = fst qr; r1 = snd qr
     in if d \<le> r1 then (q1+1, r1-d) else (q1, r1))"

definition reciprocal_correction_words :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<times> u64" where
  "reciprocal_correction_words qh ql d l =
    (let q0 = qh+1; r0 = l-q0*d;
         qr = (if r0 > ql then (q0-1, r0+d) else (q0, r0));
         q1 = fst qr; r1 = snd qr
     in if d \<le> r1 then (q1+1, r1-d) else (q1, r1))"

lemma udivrem2by1_as_correction:
  "udivrem2by1 h l d v =
    reciprocal_correction_words (fst (reciprocal_estimate_words h l v))
      (snd (reciprocal_estimate_words h l v)) d l"
  by (simp add: udivrem2by1_def reciprocal_estimate_words_def
      reciprocal_correction_words_def Let_def split_def)

lemma reciprocal_last_correction_model:
  fixes qw rw d :: u64 and Q R :: int
  assumes q: "qw = word_of_int Q" and r: "uint rw = R"
  shows "(if d \<le> rw then (qw+1, rw-d) else (qw,rw)) =
    (word_of_int (fst (if uint d \<le> R then (Q+1,R-uint d) else (Q,R))),
     word_of_int (snd (if uint d \<le> R then (Q+1,R-uint d) else (Q,R))))"
proof -
  have guard: "(d \<le> rw) = (uint d \<le> R)" using r by (simp add: word_le_def)
  have rw: "rw = word_of_int R" using r by (metis word_of_int_uint)
  show ?thesis using guard q rw by simp
qed

lemma reciprocal_correction_words_model:
  fixes qh ql d l :: u64 and Q R :: int and qr :: "int \<times> int"
  defines "Q \<equiv> uint qh+1"
    and "R \<equiv> (uint l-Q*uint d) mod 2^64"
    and "qr \<equiv> reciprocal_correction_int (2^64) (uint d) Q R (uint ql)"
  shows "reciprocal_correction_words qh ql d l =
    (word_of_int (fst qr), word_of_int (snd qr))"
proof -
  have qr0: "qh+1 = (word_of_int Q :: u64)"
    unfolding Q_def by (simp add: word_of_int_uint)
  have ru: "uint (l-(qh+1)*d) = R"
    unfolding R_def Q_def
    by (simp add: uint_word_ariths mod_diff_right_eq mod_mult_left_eq)
  have rr: "l-(qh+1)*d = (word_of_int R :: u64)"
    using ru by (metis word_of_int_uint)
  have rb: "0 \<le> R" "R < 2^64" unfolding R_def by simp_all
  have first_guard: "(l-(qh+1)*d > ql) = (R > uint ql)"
    by (simp only: word_less_def ru)
  show ?thesis
  proof (cases "R > uint ql")
    case True
    have qone: "qh+1-1 = (word_of_int (Q-1) :: u64)" using qr0 by simp
    have rone: "uint (l-(qh+1)*d+d) = (R+uint d) mod 2^64"
      using uint_word_ariths(1)[of "l-(qh+1)*d" d] by (simp add: ru)
    note last = reciprocal_last_correction_model[OF qone rone]
    show ?thesis
      unfolding reciprocal_correction_words_def qr_def reciprocal_correction_int_def
      using last True first_guard rb
      by (simp only: Let_def first_guard if_True True mod_pos_pos_trivial[OF rb]
        fst_conv snd_conv)
  next
    case False
    note last = reciprocal_last_correction_model[OF qr0 ru]
    show ?thesis
      unfolding reciprocal_correction_words_def qr_def reciprocal_correction_int_def
      using last False first_guard rb
      by (simp only: Let_def first_guard if_False False mod_pos_pos_trivial[OF rb]
        fst_conv snd_conv)
  qed
qed


lemma udivrem2by1_correct_reciprocal:
  fixes h l d v :: u64
  assumes normalized: "2^63 \<le> uint d"
    and high: "uint h < uint d"
    and recip_lower: "(2^64+uint v)*uint d < (2^64)*(2^64)"
    and recip_upper: "(2^64)*(2^64) \<le> (2^64+uint v+1)*uint d"
  shows "uint (fst (udivrem2by1 h l d v)) = (uint h*2^64+uint l) div uint d \<and>
    uint (snd (udivrem2by1 h l d v)) = (uint h*2^64+uint l) mod uint d"
proof -
  have p63 [simp]: "(2::int)^63 = 9223372036854775808"
    by (simp add: power_numeral_even power_numeral_odd Let_def)
  have p64 [simp]: "(2::int)^64 = 18446744073709551616"
    by (simp add: power_numeral_even power_numeral_odd Let_def)
  let ?B = "(2::int)^64"
  let ?D = "uint d"
  let ?H = "uint h"
  let ?L = "uint l"
  let ?M = "?B+uint v"
  let ?E = "?B*?B-?M*?D"
  let ?N = "?H*?B+?L"
  let ?qh = "fst (reciprocal_estimate_words h l v)"
  let ?ql = "snd (reciprocal_estimate_words h l v)"
  let ?Q = "uint ?qh+1"
  let ?R = "?N-?Q*?D"
  let ?QR = "reciprocal_correction_int ?B ?D ?Q ?R (uint ?ql)"
  have B: "0 < ?B" by simp
  have ds: "0 < ?D" "?D < ?B" "?B \<le> 2*?D"
  proof -
    show "0 < ?D" using normalized by (simp_all; linarith)
    show "?D < ?B" by (rule uint_lt_2p64)
    have "2 * (2::int)^63 \<le> 2*?D" using normalized by simp
    then show "?B \<le> 2*?D" by simp
  qed
  have hs: "0 \<le> ?H" "?H < ?D" using high by simp_all
  have ls: "0 \<le> ?L" "?L < ?B" using uint_lt_2p64[of l] by simp_all
  have es: "0 < ?E" "?E \<le> ?D"
  proof -
    show "0 < ?E" using recip_lower by linarith
    show "?E \<le> ?D" using recip_upper by (simp_all add: algebra_simps; linarith)
  qed
  have rec: "?M*?D+?E = ?B*?B" by simp
  have mb: "?B \<le> ?M" by simp
  have bound: "?M*?H+?L < ?B*?B"
    by (rule reciprocal_estimate_bounded(2)[OF B mb ds(1,2) hs ls es(1) rec])
  have est: "?M*?H+?L = (?Q-1)*?B+uint ?ql"
    using reciprocal_estimate_words_correct[OF bound] by simp
  have qls: "0 \<le> uint ?ql" "uint ?ql < ?B"
    using uint_lt_2p64[of ?ql] by simp_all
  have correct: "?N = fst ?QR*?D+snd ?QR \<and> 0 \<le> snd ?QR \<and> snd ?QR < ?D"
    using reciprocal_correct_unwrapped[OF B ds hs ls es qls rec est]
    by (simp only: reciprocal_correction_int_def Let_def)
  have ns: "0 \<le> ?N" "?N < ?B*?D"
  proof -
    show "0 \<le> ?N" using hs ls by (simp_all add: algebra_simps; linarith)
    show "?N < ?B*?D" using hs ls by (simp_all add: algebra_simps; linarith)
  qed
  have qdiv: "?N div ?D = fst ?QR"
  proof -
    have "?N div ?D = (fst ?QR*?D+snd ?QR) div ?D" using correct by simp
    also have "... = fst ?QR" using correct[THEN conjunct2] ds(1) by simp
    finally show ?thesis .
  qed
  have rmod: "?N mod ?D = snd ?QR"
  proof -
    have "?N mod ?D = (fst ?QR*?D+snd ?QR) mod ?D" using correct by simp
    also have "... = snd ?QR" using correct[THEN conjunct2] ds(1) by simp
    finally show ?thesis .
  qed
  have q0: "0 \<le> fst ?QR"
  proof -
    have "0 \<le> ?N div ?D" using ns(1) ds(1) by (simp add: pos_imp_zdiv_nonneg_iff)
    then show ?thesis using qdiv by simp
  qed
  have qB: "fst ?QR < ?B"
  proof -
    have "fst ?QR*?D < ?B*?D" using correct ns by linarith
    then show ?thesis by (simp only: mult_less_cancel_right_pos[OF ds(1)])
  qed
  have rB: "snd ?QR < ?B" using correct ds by linarith
  have rcong: "(?L-?Q*?D) mod ?B = ?R mod ?B"
  proof -
    have "?R mod ?B = (?H*?B+(?L-?Q*?D)) mod ?B"
      by (simp only: add_diff_eq)
    also have "... = (?L-?Q*?D) mod ?B" by (rule mod_mult_self3)
    finally show ?thesis by (rule sym)
  qed
  have modcorr: "reciprocal_correction_int ?B ?D ?Q ((?L-?Q*?D) mod ?B) (uint ?ql) = ?QR"
    by (simp only: reciprocal_correction_int_def mod_mod_trivial rcong)
  have model: "udivrem2by1 h l d v = (word_of_int (fst ?QR), word_of_int (snd ?QR))"
    using reciprocal_correction_words_model[where qh="?qh" and ql="?ql" and d=d and l=l]
    by (simp only: udivrem2by1_as_correction modcorr)
  show ?thesis using qdiv rmod correct[THEN conjunct2] q0 qB rB
    by (simp add: model uint_word_of_int)
qed
ML \<open>
val _ = if null (Thm_Deps.all_oracles @{thms udivrem2by1_correct_reciprocal})
  then () else error "Reciprocal division proof has oracle dependencies"
\<close>
end
