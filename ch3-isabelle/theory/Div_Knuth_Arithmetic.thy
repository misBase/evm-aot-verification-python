theory Div_Knuth_Arithmetic
  imports Main
begin

lemma knuth_trial_bounds:
  fixes B V dh dl dt h u1 u0 ut q r :: int
  assumes B: "2 \<le> B" and V: "0 < V"
    and dh: "B \<le> 2*dh" "dh < B"
    and dl: "0 \<le> dl" "dl < B" and dt: "0 \<le> dt" "dt < V"
    and u0: "0 \<le> u0" "u0 < B" and ut: "0 \<le> ut" "ut < V"
    and q: "0 \<le> q" "q < B" and r: "0 \<le> r" "r < dh"
    and split: "h*B+u1 = q*dh+r"
  defines "D \<equiv> dh*(B*V)+dl*V+dt"
    and "U \<equiv> (h*B+u1)*(B*V)+u0*V+ut"
    and "Q \<equiv> if q*dl > r*B+u0 then q-1 else q"
  shows "0 \<le> Q \<and> (Q-1)*D < U \<and> U < (Q+1)*D"
proof -
  let ?W = "B*V"
  let ?tail = "dl*V+dt"
  let ?low = "u0*V+ut"
  have bp: "0 < B" using B by linarith
  have wp: "0 < ?W" using bp V by simp
  have dh1: "1 \<le> dh" using B dh by linarith
  have dlV: "(dl+1)*V \<le> B*V"
    by (rule mult_right_mono) (use dl V in linarith)+
  have u0V: "(u0+1)*V \<le> B*V"
    by (rule mult_right_mono) (use u0 V in linarith)+
  have dlV': "dl*V+V \<le> B*V" using dlV by (simp add: algebra_simps)
  have u0V': "u0*V+V \<le> B*V" using u0V by (simp add: algebra_simps)
  have dlp: "0 \<le> dl*V" using dl V by simp
  have u0p: "0 \<le> u0*V" using u0 V by simp
  have tail: "0 \<le> ?tail" "?tail < ?W"
    using dlp dt dlV' by linarith+
  have low: "0 \<le> ?low" "?low < ?W"
    using u0p ut u0V' by linarith+
  have dhW: "?W \<le> dh*?W"
    using mult_right_mono[OF dh1, of ?W] wp by simp
  have dw: "?W \<le> D" unfolding D_def using dhW tail by linarith
  have twice: "B*?W \<le> (2*dh)*?W"
    by (rule mult_right_mono[OF dh(1)]) (use wp in linarith)
  have twoD: "B*?W \<le> 2*D"
    unfolding D_def using twice tail by (simp_all add: algebra_simps; linarith)
  have qt: "q*?tail < B*?W"
  proof -
    have "q*?tail \<le> B*?tail"
      by (rule mult_right_mono) (use q tail in auto)
    also have "... < B*?W" using bp tail by simp
    finally show ?thesis .
  qed
  have rw: "0 \<le> r*?W" using r wp by simp
  have diff: "U-q*D = r*?W+?low-q*?tail"
    unfolding U_def D_def by (subst split) (simp add: algebra_simps)
  have lower: "(q-2)*D < U"
    using diff twoD qt rw low by (simp_all add: algebra_simps; linarith)
  have gap: "?W \<le> (dh-r)*?W"
    using mult_right_mono[of 1 "dh-r" ?W] r wp by simp
  have pos_tail: "0 \<le> (q+1)*?tail" using q tail by simp
  have diff_upper: "(q+1)*D-U = (dh-r)*?W+(q+1)*?tail-?low"
    unfolding D_def U_def by (subst split) (simp add: algebra_simps)
  have upper: "U < (q+1)*D"
    using diff_upper gap low pos_tail by linarith
  have diff_adjust: "q*D-U = (q*dl-r*B-u0)*V+q*dt-ut"
    unfolding D_def U_def by (subst split) (simp add: algebra_simps)
  show ?thesis
  proof (cases "q*dl > r*B+u0")
    case True
    have rz: "0 \<le> r*B+u0" using r u0 bp by simp
    have qpos: "0 < q" using True q rz by (cases "q=0"; simp_all; linarith)
    have digit_gap: "1 \<le> q*dl-r*B-u0" using True by linarith
    have qdt: "0 \<le> q*dt" using q dt by simp
    have gapV: "V \<le> (q*dl-r*B-u0)*V"
      using mult_right_mono[OF digit_gap, of V] V by simp
    have adjust: "U < q*D"
      using diff_adjust gapV qdt ut by linarith
    show ?thesis unfolding Q_def using True qpos lower adjust by simp
  next
    case False
    have qdt: "q*dt < ?W"
    proof -
      have "q*dt \<le> B*dt" by (rule mult_right_mono) (use q dt in auto)
      also have "... < B*V" using bp dt by simp
      finally show ?thesis .
    qed
    have gapV: "(q*dl-r*B-u0)*V \<le> 0"
      by (rule mult_nonpos_nonneg) (use False V in linarith)+
    have close: "(q-1)*D < U"
      using diff_adjust gapV qdt dw ut by (simp_all add: algebra_simps; linarith)
    show ?thesis unfolding Q_def using False q upper close by simp
  qed
qed


lemma knuth_capped_trial_bounds:
  fixes B W dh tail U D :: int
  assumes B: "2 \<le> B" and W: "0 < W"
    and dh: "B \<le> 2*dh"
    and tail: "0 \<le> tail" "tail < W"
    and dval: "D = dh*W+tail"
    and lower: "dh*(B*W) \<le> U"
    and upper: "U < B*D"
  shows "0 \<le> B-1 \<and> (B-2)*D < U \<and> U < B*D"
proof -
  have bt: "(B-2)*tail \<le> (B-2)*W"
    by (rule mult_left_mono) (use B tail in linarith)+
  have bW: "B*W \<le> 2*dh*W"
    by (rule mult_right_mono[OF dh]) (use W in linarith)
  have bw': "(B-2)*W < B*W" using W by (simp add: algebra_simps)
  have near: "(B-2)*tail < 2*dh*W" using bt bW bw' by linarith
  have identity: "dh*(B*W)-(B-2)*D = 2*dh*W-(B-2)*tail"
    by (simp add: dval algebra_simps)
  show ?thesis using B identity near lower upper by linarith
qed

lemma knuth_final_correction:
  fixes D U Q q r :: int
  assumes D: "0 < D" and U: "0 \<le> U" and Q: "0 \<le> Q"
    and lower: "(Q-1)*D < U" and upper: "U < (Q+1)*D"
  defines "q \<equiv> if U < Q*D then Q-1 else Q"
    and "r \<equiv> U-q*D"
  shows "0 \<le> q \<and> 0 \<le> r \<and> r < D \<and> q = U div D \<and> r = U mod D"
proof -
  have lower': "Q*D-D < U" using lower by (simp add: algebra_simps)
  have upper': "U < Q*D+D" using upper by (simp add: algebra_simps)
  have bounds: "0 \<le> q \<and> 0 \<le> r \<and> r < D"
  proof (cases "U < Q*D")
    case True
    have "0 < Q" using True Q U by (cases "Q=0"; simp_all; linarith)
    then have qp: "0 \<le> Q-1" by linarith
    have qeq: "q = Q-1" unfolding q_def using True by simp
    have req: "r = U-Q*D+D" unfolding r_def qeq by (simp add: algebra_simps)
    show ?thesis
      using qeq req qp True lower' by linarith
  next
    case False
    have qeq: "q = Q" unfolding q_def using False by simp
    show ?thesis
      unfolding r_def qeq using False Q upper' by linarith
  qed
  have split: "U = q*D+r" unfolding r_def by simp
  have quotient: "U div D = q"
    by (subst split) (use D bounds in \<open>simp add: div_pos_pos_trivial\<close>)
  have remainder: "U mod D = r"
    by (subst split) (use D bounds in \<open>simp add: mod_pos_pos_trivial\<close>)
  show ?thesis using bounds quotient remainder by simp
qed

end
