theory Green_AC_Approximation
  imports Green_AC_Paths "HOL-Complex_Analysis.Winding_Numbers"
begin

text \<open>Approximating the velocity in L1 and integrating it gives a valid
  path uniformly close to an absolutely continuous path.\<close>
lemma green_ac_path_continuous_velocity_approx:
  fixes g :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (g has_vector_derivative g' t) (at t)"
    and eps: "0 < \<epsilon>"
  shows "\<exists>h p. continuous_on UNIV h \<and>
    p = (\<lambda>t. g 0 + integral {0..t} h) \<and>
    valid_path p \<and>
    (\<forall>t\<in>{0..1}. norm (p t - g t) < \<epsilon>) \<and>
    integral {0..1} (\<lambda>t. norm (g' t - h t)) < \<epsilon>"
proof -
  let ?I = "{0..1::real}"
  have gabs: "g' absolutely_integrable_on ?I"
    by (rule green_ac_velocity_absolutely_integrable[OF ac null deriv])
  obtain h where habs: "h absolutely_integrable_on ?I"
    and hc: "continuous_on UNIV h"
    and herr: "norm (integral ?I (\<lambda>t. norm (g' t - h t))) < \<epsilon>"
    by (rule absolutely_integrable_approximate_continuous_vector
      [OF _ gabs eps])
      auto
  have err: "integral ?I (\<lambda>t. norm (g' t - h t)) < \<epsilon>"
    using herr by simp
  let ?p = "\<lambda>t. g 0 + integral {0..t} h"
  have valid: "valid_path ?p"
    by (rule green_continuous_velocity_valid_path[OF hc])
  have diff_abs: "(\<lambda>t. g' t - h t) absolutely_integrable_on ?I"
    using gabs habs by (simp add: set_integral_diff(1))
  have norm_int: "(\<lambda>t. norm (g' t - h t)) integrable_on ?I"
    using diff_abs by (simp add: absolutely_integrable_on_def)
  have close: "norm (?p t - g t) < \<epsilon>" if t: "t \<in> ?I" for t
  proof -
    have sub: "{0..t} \<subseteq> ?I"
      using t by auto
    have gsub: "g' integrable_on {0..t}"
      by (rule integrable_on_subinterval[OF _ sub])
        (use gabs in \<open>simp add: absolutely_integrable_on_def\<close>)
    have hsub: "h integrable_on {0..t}"
      by (rule integrable_on_subinterval[OF _ sub])
        (use habs in \<open>simp add: absolutely_integrable_on_def\<close>)
    have dsub: "(\<lambda>x. g' x - h x) integrable_on {0..t}"
      by (rule integrable_diff[OF gsub hsub])
    have nsub: "(\<lambda>x. norm (g' x - h x)) integrable_on {0..t}"
      by (rule integrable_on_subinterval[OF norm_int sub])
    have eq: "?p t - g t = - integral {0..t} (\<lambda>x. g' x - h x)"
      using green_ac_subinterval_integral[OF ac null deriv t]
      by (simp add: integral_diff[OF gsub hsub] algebra_simps)
    have first: "norm (?p t - g t) \<le>
        integral {0..t} (\<lambda>x. norm (g' x - h x))"
      unfolding eq norm_minus_cancel
      by (rule integral_norm_bound_integral[OF dsub nsub]) simp
    have second: "integral {0..t} (\<lambda>x. norm (g' x - h x)) \<le>
        integral ?I (\<lambda>x. norm (g' x - h x))"
      by (rule integral_subset_le[OF sub nsub norm_int]) simp
    show ?thesis
      using first second err by linarith
  qed
  show ?thesis
    by (intro exI[where x=h] exI[where x="?p"])
      (use hc valid close err in auto)
qed

theorem green_ac_path_smooth_approx:
  fixes g :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (g has_vector_derivative g' t) (at t)"
    and eps: "0 < \<epsilon>"
  shows "\<exists>k p. continuous_on UNIV k \<and>
    p = (\<lambda>t. g 0 + integral {0..t} k) \<and>
    valid_path p \<and>
    pathstart p = pathstart g \<and> pathfinish p = pathfinish g \<and>
    (\<forall>t\<in>{0..1}. norm (p t - g t) < \<epsilon>) \<and>
    integral {0..1} (\<lambda>t. norm (g' t - k t)) < \<epsilon>"
proof -
  let ?I = "{0..1::real}"
  have de: "0 < \<epsilon> / 3"
    using eps by simp
  obtain h p0 where hc: "continuous_on UNIV h"
    and p0def: "p0 = (\<lambda>t. g 0 + integral {0..t} h)"
    and p0close: "\<And>t. t \<in> ?I \<Longrightarrow> norm (p0 t - g t) < \<epsilon> / 3"
    and herr: "integral ?I (\<lambda>t. norm (g' t - h t)) < \<epsilon> / 3"
    using green_ac_path_continuous_velocity_approx[OF ac null deriv de]
    by blast
  define d where "d = g 1 - p0 1"
  define k where "k = (\<lambda>t. h t + d)"
  define p where "p = (\<lambda>t. g 0 + integral {0..t} k)"
  have dc: "norm d < \<epsilon> / 3"
    using p0close[of 1] unfolding d_def
    by (simp add: norm_minus_commute)
  have kc: "continuous_on UNIV k"
    unfolding k_def using hc by (intro continuous_intros)
  have hI: "continuous_on ?I h"
    by (rule continuous_on_subset[OF hc]) simp
  have hi: "h integrable_on ?I"
    by (rule integrable_continuous_real[OF hI])
  have ki: "k integrable_on ?I"
    by (rule integrable_continuous_real)
      (rule continuous_on_subset[OF kc], simp)
  have peq: "p t = p0 t + t *\<^sub>R d" if t: "t \<in> ?I" for t
  proof -
    have sub: "{0..t} \<subseteq> ?I"
      using t by auto
    have ht: "h integrable_on {0..t}"
      by (rule integrable_on_subinterval[OF hi sub])
    have dt: "(\<lambda>_::real. d) integrable_on {0..t}"
      by (rule integrable_continuous_real) (intro continuous_intros)
    have t0: "0 \<le> t"
      using t by simp
    show ?thesis
      unfolding p_def p0def k_def
      by (simp add: integral_add[OF ht dt] t0)
  qed
  have valid: "valid_path p"
    unfolding p_def
    by (rule green_continuous_velocity_valid_path[OF kc])
  have start: "pathstart p = pathstart g"
    unfolding p_def pathstart_def by simp
  have finish: "pathfinish p = pathfinish g"
    using peq[of 1] unfolding pathfinish_def d_def by simp
  have close: "norm (p t - g t) < \<epsilon>" if t: "t \<in> ?I" for t
  proof -
    have eq: "p t - g t = (p0 t - g t) + t *\<^sub>R d"
      using peq[OF t] by (simp add: algebra_simps)
    have bound: "norm (p t - g t) \<le>
      norm (p0 t - g t) + norm (t *\<^sub>R d)"
      unfolding eq by (rule norm_triangle_ineq)
    have t0: "0 \<le> t" and t1: "t \<le> 1"
      using t by auto
    have "t * norm d \<le> 1 * norm d"
      by (rule mult_right_mono[OF t1]) simp
    then have "norm (t *\<^sub>R d) \<le> norm d"
      using t0 by simp
    then show ?thesis
      using bound p0close[OF t] dc eps by linarith
  qed
  have gabs: "g' absolutely_integrable_on ?I"
    by (rule green_ac_velocity_absolutely_integrable[OF ac null deriv])
  have habs: "h absolutely_integrable_on ?I"
    using hI by (metis absolutely_integrable_continuous interval_cbox)
  have kabs: "k absolutely_integrable_on ?I"
    using kc by (metis absolutely_integrable_continuous
      continuous_on_subset interval_cbox subset_UNIV)
  have diffk_abs: "(\<lambda>t. g' t - k t) absolutely_integrable_on ?I"
    by (rule set_integral_diff(1)[OF gabs kabs])
  have diffh_abs: "(\<lambda>t. g' t - h t) absolutely_integrable_on ?I"
    by (rule set_integral_diff(1)[OF gabs habs])
  have n1int: "(\<lambda>t. norm (g' t - k t)) integrable_on ?I"
    using diffk_abs by (simp add: absolutely_integrable_on_def)
  have nhint: "(\<lambda>t. norm (g' t - h t)) integrable_on ?I"
    using diffh_abs by (simp add: absolutely_integrable_on_def)
  have dint: "(\<lambda>_::real. norm d) integrable_on ?I"
    by (rule integrable_continuous_real) (intro continuous_intros)
  have n2int: "(\<lambda>t. norm (g' t - h t) + norm d) integrable_on ?I"
    by (rule integrable_add[OF nhint dint])
  have estimate: "integral ?I (\<lambda>t. norm (g' t - k t)) \<le>
    integral ?I (\<lambda>t. norm (g' t - h t) + norm d)"
  proof (rule integral_le[OF n1int n2int])
    fix t assume "t \<in> ?I"
    have eq: "g' t - k t = (g' t - h t) + (-d)"
      by (simp add: k_def algebra_simps)
    show "norm (g' t - k t) \<le> norm (g' t - h t) + norm d"
      unfolding eq
      using norm_triangle_ineq[of "g' t - h t" "-d"] by simp
  qed
  have sum_eq: "integral ?I (\<lambda>t. norm (g' t - h t) + norm d) =
      integral ?I (\<lambda>t. norm (g' t - h t)) + norm d"
    using integral_add[OF nhint dint] by simp
  have velclose: "integral ?I (\<lambda>t. norm (g' t - k t)) < \<epsilon>"
    using estimate sum_eq herr dc eps by linarith
  show ?thesis
    by (intro exI[where x=k] exI[where x=p])
      (use kc p_def valid start finish close velclose in auto)
qed

corollary green_ac_winding_approximants:
  fixes g :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (g has_vector_derivative g' t) (at t)"
    and away: "z \<notin> path_image g"
    and eps: "0 < \<epsilon>"
  shows "\<exists>k p. continuous_on UNIV k \<and>
    p = (\<lambda>t. g 0 + integral {0..t} k) \<and>
    valid_path p \<and>
    pathstart p = pathstart g \<and> pathfinish p = pathfinish g \<and>
    winding_number p z = winding_number g z \<and>
    (\<forall>t\<in>{0..1}. norm (p t - g t) < \<epsilon>) \<and>
    integral {0..1} (\<lambda>t. norm (g' t - k t)) < \<epsilon>"
proof -
  have path: "path g"
    by (rule green_ac_path_is_path[OF ac])
  have closed: "closed (path_image g)"
    by (rule compact_imp_closed) (rule compact_path_image[OF path])
  have nonempty: "path_image g \<noteq> {}"
    by (auto simp: path_image_def)
  define r where "r = infdist z (path_image g)"
  have rpos: "0 < r"
    unfolding r_def by (rule infdist_pos_not_in_closed[OF closed nonempty away])
  define e where "e = min \<epsilon> (r / 2)"
  have epos: "0 < e"
    using eps rpos by (simp add: e_def)
  obtain k p where kc: "continuous_on UNIV k"
    and pdef: "p = (\<lambda>t. g 0 + integral {0..t} k)"
    and valid: "valid_path p"
    and start: "pathstart p = pathstart g"
    and finish: "pathfinish p = pathfinish g"
    and close: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (p t - g t) < e"
    and vel: "integral {0..1} (\<lambda>t. norm (g' t - k t)) < e"
    using green_ac_path_smooth_approx[OF ac null deriv epos]
    by blast
  have near: "norm (p t - g t) < norm (g t - z)"
    if t: "t \<in> {0..1}" for t
  proof -
    have "r \<le> dist z (g t)"
      unfolding r_def by (rule infdist_le)
        (use t in \<open>auto simp: path_image_def\<close>)
    then show ?thesis
      using close[OF t] rpos by (simp add: e_def dist_norm norm_minus_commute)
  qed
  have winding: "winding_number p z = winding_number g z"
    by (rule winding_number_nearby_paths_eq
      [OF path valid_path_imp_path[OF valid] start finish near])
  show ?thesis
    by (intro exI[where x=k] exI[where x=p])
      (use kc pdef valid start finish winding close vel in
        \<open>auto simp: e_def\<close>)
qed

context green_ac_velocity
begin

lemmas continuous_velocity_approx =
  green_ac_path_continuous_velocity_approx[OF ac null deriv]
  and smooth_approx = green_ac_path_smooth_approx[OF ac null deriv]
  and winding_approximants =
    green_ac_winding_approximants[OF ac null deriv]

end

end
