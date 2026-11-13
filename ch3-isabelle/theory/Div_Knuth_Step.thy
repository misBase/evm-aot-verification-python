theory Div_Knuth_Step
  imports Div_Knuth_Correction Div_By1
begin

definition knuth_trial :: "nat \<Rightarrow> uint256 \<Rightarrow> u64 \<Rightarrow> uint256 \<Rightarrow> u64" where
  "knuth_trial j u u4 d =
    (let dh = getword d (dLen d-1);
         dl = getword d (dLen d-2);
         reciprocal = reciprocal2by1 dh;
         u2 = getword_u u (j+dLen d) u4;
         u1 = getword u (j+dLen d-1);
         u0 = getword u (j+dLen d-2);
         (qhat,rhat) = (if u2 \<ge> dh then (2^64-1,0)
                       else udivrem2by1 u2 u1 dh reciprocal)
     in if u2 \<ge> dh then qhat
        else let (ph,pl) = mul64 qhat dl
             in if ph > rhat \<or> (ph = rhat \<and> pl > u0)
                then qhat-1 else qhat)"

definition knuth_step :: "nat \<Rightarrow> uint256 \<Rightarrow> u64 \<Rightarrow> uint256 \<Rightarrow> u64 \<times> uint256 \<times> u64" where
  "knuth_step j u u4 d = knuth_post_subtract j u u4 d (knuth_trial j u u4 d)"
lemma knuth_double_word_compare:
  fixes h l r u :: u64
  shows "(h > r \<or> (h = r \<and> l > u)) =
         (uint h*2^64+uint l > uint r*2^64+uint u)"
proof -
  have lb: "0 \<le> uint l" "uint l < 2^64" using uint_nonnegative uint_lt_2p64 by auto
  have ub: "0 \<le> uint u" "uint u < 2^64" using uint_nonnegative uint_lt_2p64 by auto
  show ?thesis
    unfolding word_less_alt word_uint_eq_iff
    using lb ub by (simp_all; linarith)
qed

lemma knuth_mul64_compare:
  fixes q dl r u0 :: u64
  shows "(let (ph,pl) = mul64 q dl in ph > r \<or> (ph = r \<and> pl > u0)) =
         (uint q*uint dl > uint r*2^64+uint u0)"
  by (simp only: case_prod_unfold Let_def knuth_double_word_compare mul64_spec)

lemma knuth_adjust_uint:
  fixes q dl r u0 :: u64
  shows "uint (let (ph,pl) = mul64 q dl in
            if ph > r \<or> (ph = r \<and> pl > u0) then q-1 else q) =
         (if uint q*uint dl > uint r*2^64+uint u0 then uint q-1 else uint q)"
proof -
  have adjust: "uint q*uint dl > uint r*2^64+uint u0 \<Longrightarrow> 0 < uint q"
  proof -
    assume gt: "uint q*uint dl > uint r*2^64+uint u0"
    have rhs: "0 \<le> uint r*2^64+uint u0" by simp
    have nz: "uint q \<noteq> 0"
    proof
      assume zero: "uint q=0"
      have "uint r*2^64+uint u0 < 0" using gt by (simp add: zero)
      then show False using rhs by linarith
    qed
    show "0 < uint q" using nz uint_nonnegative[of q] by linarith
  qed
  note test = knuth_mul64_compare[of q dl r u0, unfolded case_prod_unfold Let_def]
  show ?thesis
    unfolding case_prod_unfold Let_def test
    using adjust by (auto simp: uint_sub_if')
qed
definition knuth_trial_words :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64" where
  "knuth_trial_words h u1 u0 dh dl =
    (if h \<ge> dh then 2^64-1
     else let (q,r) = udivrem2by1 h u1 dh (reciprocal2by1 dh);
              (ph,pl) = mul64 q dl
          in if ph > r \<or> (ph = r \<and> pl > u0) then q-1 else q)"

lemma knuth_trial_as_words:
  "knuth_trial j u u4 d = knuth_trial_words
    (getword_u u (j+dLen d) u4) (getword u (j+dLen d-1)) (getword u (j+dLen d-2))
    (getword d (dLen d-1)) (getword d (dLen d-2))"
  by (simp add: knuth_trial_def knuth_trial_words_def Let_def case_prod_unfold)

lemma knuth_trial_words_bounds:
  fixes h u1 u0 dh dl :: u64 and V dt ut D N :: int
  assumes normalized: "2^63 \<le> uint dh"
    and vp: "0 < V"
    and dt: "0 \<le> dt" "dt < V"
    and ut: "0 \<le> ut" "ut < V"
    and dval: "D = uint dh*(2^64*V)+uint dl*V+dt"
    and nval: "N = (uint h*2^64+uint u1)*(2^64*V)+uint u0*V+ut"
    and cap: "N < 2^64*D"
  shows "(uint (knuth_trial_words h u1 u0 dh dl)-1)*D < N"
    and "N < (uint (knuth_trial_words h u1 u0 dh dl)+1)*D"
proof -
  let ?B = "(2::int)^64"
  let ?W = "?B*V"
  have bp: "0 < ?B" by simp
  have wp: "0 < ?W" using vp by simp
  have dhnorm: "?B \<le> 2*uint dh" using normalized by (simp_all; linarith)
  have dhpos: "0 < uint dh" using normalized by (simp_all; linarith)
  have result: "(uint (knuth_trial_words h u1 u0 dh dl)-1)*D < N \<and>
    N < (uint (knuth_trial_words h u1 u0 dh dl)+1)*D"
  proof (cases "h \<ge> dh")
    case True
    have capword: "uint ((2^64-1)::u64) = ?B-1" by code_simp
    have trial: "uint (knuth_trial_words h u1 u0 dh dl) = ?B-1"
      using True by (simp add: knuth_trial_words_def capword)
    have dlV: "(uint dl+1)*V \<le> ?B*V"
      by (rule mult_right_mono) (use uint_lt_2p64[of dl] vp in linarith)+
    have dlV': "uint dl*V+V \<le> ?B*V" using dlV by (simp only: algebra_simps)
    have prod: "0 \<le> uint dl*V" using vp by simp
    have tail: "0 \<le> uint dl*V+dt" "uint dl*V+dt < ?W"
      using prod dt dlV' by linarith+
    have high: "uint dh*(?B*?W) \<le> uint h*(?B*?W)"
      by (rule mult_right_mono) (use True wp in \<open>simp_all add: word_le_def\<close>)
    have wnn: "0 \<le> ?W" using wp by linarith
    have vnn: "0 \<le> V" using vp by linarith
    have middle: "0 \<le> uint u1*?W" by (rule mult_nonneg_nonneg[OF uint_nonnegative wnn])
    have low: "0 \<le> uint u0*V" by (rule mult_nonneg_nonneg[OF uint_nonnegative vnn])
    have nsplit: "N = uint h*(?B*?W)+uint u1*?W+uint u0*V+ut"
      unfolding nval by (simp only: algebra_simps)
    have lower: "uint dh*(?B*?W) \<le> N"
      using high middle low ut nsplit by linarith
    note bounds = knuth_capped_trial_bounds[of ?B ?W "uint dh" "uint dl*V+dt" D N]
    show ?thesis
      using bounds wp dhnorm tail dval lower cap unfolding trial by auto
  next
    case False
    have high: "uint h < uint dh" using False by (simp add: word_le_def)
    obtain q r where qr: "udivrem2by1 h u1 dh (reciprocal2by1 dh) = (q,r)"
      by (cases "udivrem2by1 h u1 dh (reciprocal2by1 dh)") auto
    have correct: "uint q = (uint h*?B+uint u1) div uint dh"
      "uint r = (uint h*?B+uint u1) mod uint dh"
      using udivrem2by1_correct_reciprocal[OF normalized high reciprocal2by1_bounds[OF normalized], of u1]
      by (simp_all add: qr)
    have rb: "0 \<le> uint r" "uint r < uint dh"
      using correct dhpos by simp_all
    have split: "uint h*?B+uint u1 = uint q*uint dh+uint r"
      using correct by simp
    have trial: "uint (knuth_trial_words h u1 u0 dh dl) =
      (if uint q*uint dl > uint r*?B+uint u0 then uint q-1 else uint q)"
      unfolding knuth_trial_words_def using False
      by (simp only: if_False qr Let_def case_prod_conv knuth_adjust_uint[unfolded Let_def])
    note bounds = knuth_trial_bounds[of "?B" V "uint dh" "uint dl" dt "uint u0" ut
      "uint q" "uint r" "uint h" "uint u1"]
    have all: "0 \<le> uint (knuth_trial_words h u1 u0 dh dl) \<and>
        (uint (knuth_trial_words h u1 u0 dh dl)-1)*D < N \<and>
        N < (uint (knuth_trial_words h u1 u0 dh dl)+1)*D"
      using bounds vp dhnorm dt ut rb split uint_lt_2p64[of dh] uint_lt_2p64[of dl]
        uint_lt_2p64[of u0] uint_lt_2p64[of q]
      unfolding trial dval nval by simp
    show ?thesis
      using all by auto
  qed
  show "(uint (knuth_trial_words h u1 u0 dh dl)-1)*D < N"
    and "N < (uint (knuth_trial_words h u1 u0 dh dl)+1)*D" using result by auto
qed

ML \<open>
val _ = if null (Thm_Deps.all_oracles @{thms knuth_trial_words_bounds})
  then () else error "Knuth trial proof has oracle dependencies"
\<close>
end
