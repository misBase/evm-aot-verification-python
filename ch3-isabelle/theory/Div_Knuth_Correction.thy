theory Div_Knuth_Correction
  imports Div_Knuth_State
begin

definition knuth_post_subtract :: "nat \<Rightarrow> uint256 \<Rightarrow> u64 \<Rightarrow> uint256 \<Rightarrow> u64 \<Rightarrow> u64 \<times> uint256 \<times> u64" where
  "knuth_post_subtract j x x4 d q =
    (let k = j+dLen d; h = getword_u x k x4;
         (b,xs,x4s) = subMulTo x x4 d j q;
         (xn,x4n) = update_word_u4 xs x4s k (h-b);
         final = (if h < b then
           (let (c,xa,x4a) = addTo xn x4n d j
            in update_word_u4 xa x4a k (h-b+c))
          else (xn,x4n));
         qfinal = (if h < b then q-1 else q)
     in (qfinal,final))"

lemma correction_state_nonnegative:
  "0 \<le> uint256_u4_to_int (x,x4)"
  by (simp add: uint256_u4_to_int_def uint256_to_int_nonneg)

lemma knuth_post_subtract_correct:
  fixes x d :: uint256 and x4 q :: u64 and j k :: nat and P D N :: int
  defines "k \<equiv> j+dLen d"
    and "P \<equiv> ((2::int)^64)^k"
    and "D \<equiv> uint256_to_int d*((2::int)^64)^j"
    and "N \<equiv> uint256_u4_to_int (x,x4)"
  assumes index: "k \<le> 4"
    and divisor: "0 < D" "D < P"
    and capacity: "N < ((2::int)^64)^Suc k"
    and lower: "(uint q-1)*D < N"
    and upper: "N < (uint q+1)*D"
  shows "uint (fst (knuth_post_subtract j x x4 d q)) = N div D \<and>
    uint256_u4_to_int (snd (knuth_post_subtract j x x4 d q)) = N mod D"
proof -
  let ?B = "(2::int)^64"
  let ?h = "getword_u x k x4"
  let ?Q = "uint q"
  let ?R = "N-?Q*D"
  have Ppos: "0 < P" unfolding P_def by simp
  have Nnonneg: "0 \<le> N" unfolding N_def by (rule correction_state_nonnegative)
  have subindex: "dLen d+j \<le> 4" using index unfolding k_def by simp
  obtain b xs x4s where sub: "subMulTo x x4 d j q = (b,xs,x4s)"
    by (cases "subMulTo x x4 d j q") auto
  obtain xn x4n where update: "update_word_u4 xs x4s k (?h-b) = (xn,x4n)"
    by (cases "update_word_u4 xs x4s k (?h-b)") auto
  let ?Ns = "uint256_u4_to_int (xs,x4s)"
  let ?Nn = "uint256_u4_to_int (xn,x4n)"
  let ?L = "?Ns mod P"
  have subbal: "?Ns-uint b*P = ?R"
    using subMulTo_correct[OF subindex sub]
    unfolding uint256_u4_to_int_def N_def D_def P_def k_def
    by (simp add: algebra_simps)
  have top: "uint ?h = N div P"
    using uint256_u4_top_digit[OF index] capacity
    unfolding N_def P_def by simp
  have subtop: "?Ns div P = uint ?h"
    using subMulTo_preserves_high_value[OF index[unfolded k_def] sub] top
    unfolding P_def k_def N_def by simp
  have subdigit: "getword_u xs k x4s = ?h"
    by (rule subMulTo_preserves_high[OF _ index sub]) (simp add: k_def)
  have splitNs: "?Ns = uint ?h*P+?L"
    using div_mult_mod_eq[of ?Ns P] subtop by simp
  have Lbounds: "0 \<le> ?L" "?L < P" using Ppos by simp_all
  have residual: "?R = ?L+(uint ?h-uint b)*P"
    using subbal splitNs by (simp_all add: algebra_simps; linarith)
  have updated: "?Nn = ?Ns+(uint (?h-b)-uint ?h)*P"
    using update_word_u4_value[OF index, of xs x4s "?h-b"]
    unfolding update subdigit P_def by simp
  have Rlower: "-P < ?R" using lower divisor by (simp_all add: algebra_simps; linarith)
  have Rupper: "?R < D" using upper by (simp_all add: algebra_simps; linarith)
  have corrected: "let out = knuth_post_subtract j x x4 d q in
      N = uint (fst out)*D+uint256_u4_to_int (snd out) \<and>
      0 \<le> uint256_u4_to_int (snd out) \<and>
      uint256_u4_to_int (snd out) < D"
  proof (cases "?h < b")
    case False
    have no_borrow: "uint b \<le> uint ?h" using False by (simp add: word_less_def)
    have subuint: "uint (?h-b) = uint ?h-uint b" using no_borrow by (simp add: uint_sub_lem)
    have final: "knuth_post_subtract j x x4 d q = (q,xn,x4n)"
      unfolding knuth_post_subtract_def
      using False by (simp add: k_def[symmetric] sub update)
    have nvalue: "?Nn = ?R" using updated subuint subbal by (simp add: algebra_simps)
    have rnonneg: "0 \<le> ?R" using nvalue correction_state_nonnegative[of xn x4n] by simp
    show ?thesis using nvalue rnonneg Rupper
      by (simp add: final Let_def)
  next
    case True
    have borrow: "uint ?h < uint b" using True by (simp add: word_less_def)
    have hd: "uint ?h-uint b \<le> -1" using borrow by linarith
    have scaled: "(uint ?h-uint b)*P \<le> (-1)*P"
      by (rule mult_right_mono[OF hd]) (use Ppos in linarith)
    have Rneg: "?R < 0" using residual Lbounds scaled by linarith
    have Rdiv: "?R div P = uint ?h-uint b"
    proof -
      have "?R div P = (?L+(uint ?h-uint b)*P) div P" using residual by simp
      also have "... = uint ?h-uint b" using Ppos Lbounds by simp
      finally show ?thesis .
    qed
    have rplus: "0 \<le> ?R+P" "?R+P < P" using Rlower Rneg by linarith+
    have "(?R+P) div P = 0" using rplus by simp
    then have "?R div P+1 = 0" using Ppos by (simp add: div_add_self2)
    then have diff: "uint ?h-uint b = -1" using Rdiv by linarith
    have subuint: "uint (?h-b) = ?B-1"
      using borrow diff by (simp add: uint_sub_if')
    have first: "?Nn = (?B-1)*P+?L"
      using updated splitNs subuint by (simp add: algebra_simps)
    have firsttop: "getword_u xn k x4n = ?h-b"
      using getword_u_update_same[OF index, of xs x4s "?h-b"] unfolding update by simp
    obtain c xa x4a where add: "addTo xn x4n d j = (c,xa,x4a)"
      by (cases "addTo xn x4n d j") auto
    let ?Na = "uint256_u4_to_int (xa,x4a)"
    have addbal: "?Na+uint c*P = ?Nn+D"
      using addTo_correct[OF subindex add]
      unfolding uint256_u4_to_int_def D_def P_def k_def
      by (simp add: algebra_simps)
    have atop: "getword_u xa k x4a = ?h-b"
      using addTo_preserves_high[OF _ index add] firsttop
      by (simp add: k_def)
    have atopdiv: "?Na div P = ?B-1"
    proof -
      have "?Na div P = ?Nn div P"
        using addTo_preserves_high_value[OF index[unfolded k_def] add]
        by (simp only: P_def k_def)
      also have "... = ?B-1" using first Ppos Lbounds by simp
      finally show ?thesis .
    qed
    have rembounds: "0 \<le> ?R+D" "?R+D < D" "?R+D < P"
      using lower Rneg divisor by (simp_all add: algebra_simps; linarith)+
    have sumvalue: "?Nn+D = ?B*P+(?R+D)"
      using first residual diff by (simp add: algebra_simps)
    have carry: "uint c = 1"
    proof -
      have "(?Na+uint c*P) div P = (?Nn+D) div P" using addbal by simp
      then have "(?B-1)+uint c = ?B"
        using atopdiv Ppos rembounds by (simp add: sumvalue)
      then show ?thesis by simp
    qed
    have lastword: "uint (?h-b+c) = 0"
      using uint_word_ariths(1)[of "?h-b" c] subuint carry by simp
    obtain xf x4f where finalupdate: "update_word_u4 xa x4a k (?h-b+c) = (xf,x4f)"
      by (cases "update_word_u4 xa x4a k (?h-b+c)") auto
    have finalvalue: "uint256_u4_to_int (xf,x4f) = ?R+D"
    proof -
      have val: "uint256_u4_to_int (xf,x4f) = ?Na-(?B-1)*P"
        using update_word_u4_value[OF index, of xa x4a "?h-b+c"]
        unfolding finalupdate atop
        using subuint lastword by (simp add: P_def)
      show ?thesis using val addbal sumvalue carry by (simp_all add: algebra_simps; linarith)
    qed
    have qpositive: "0 < ?Q"
    proof -
      have "0 < ?Q*D" using Rneg Nnonneg by linarith
      then show ?thesis using divisor(1) by (meson zero_less_mult_pos2)
    qed
    have qsub: "uint (q-1) = ?Q-1" using qpositive by (simp add: uint_sub_if')
    have final: "knuth_post_subtract j x x4 d q = (q-1,xf,x4f)"
      unfolding knuth_post_subtract_def
      using True by (simp add: k_def[symmetric] sub update add finalupdate)
    show ?thesis
      by (simp only: final Let_def fst_conv snd_conv qsub finalvalue)
         (use rembounds in \<open>simp add: algebra_simps\<close>)
  qed
  let ?out = "knuth_post_subtract j x x4 d q"
  have balance: "N = uint (fst ?out)*D+uint256_u4_to_int (snd ?out)"
    and rb: "0 \<le> uint256_u4_to_int (snd ?out)" "uint256_u4_to_int (snd ?out) < D"
    using corrected by (simp_all add: Let_def)
  have qdiv: "N div D = uint (fst ?out)"
    by (subst balance) (use divisor rb in simp)
  have rmod: "N mod D = uint256_u4_to_int (snd ?out)"
    by (subst balance) (use divisor rb in simp)
  show ?thesis using qdiv rmod by simp
qed
ML \<open>
val _ = if null (Thm_Deps.all_oracles @{thms knuth_post_subtract_correct})
  then () else error "Knuth correction proof has oracle dependencies"
\<close>
end
