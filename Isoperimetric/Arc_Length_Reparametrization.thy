theory Arc_Length_Reparametrization
  imports "HOL-Analysis.Rectifiable_Path"
begin

text \<open>
  Arc length reparametrization for rectifiable paths, following HOL Light's
  @{text "Multivariate/integration.ml"}.

  Given a rectifiable path @{term g}, there exists a reparametrization @{term h}
  that is Lipschitz with constant @{term "path_length g"}, preserves the path image,
  and has the property that arc length grows linearly with the parameter.
\<close>

section \<open>Reparametrization\<close>

lemma rectifiable_path_reparametrization:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "rectifiable_path g" "continuous_on {0..1} \<phi>" "\<phi> ` {0..1} \<subseteq> {0..1}"
    and \<phi>01: "\<phi> 0 = 0" "\<phi> 1 = 1"
    and mono: "mono_on {0..1} \<phi>"
  shows "rectifiable_path (g \<circ> \<phi>)"
  unfolding rectifiable_path_def
proof
  have g_path: "path g" and g_bv: "has_bounded_variation_on g {0..1}"
    using assms(1) unfolding rectifiable_path_def by auto
  show "path (g \<circ> \<phi>)"
    by (meson assms continuous_on_compose continuous_on_path g_path path_def)
  show "has_bounded_variation_on (g \<circ> \<phi>) {0..1}"
    using has_bounded_variation_compose_monotone(1)[OF _ mono] \<phi>01 using g_bv by force
qed

lemma path_length_reparametrization:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "rectifiable_path g" "continuous_on {0..1} \<phi>" "\<phi> ` {0..1} \<subseteq> {0..1}" "\<phi> 0 = 0" "\<phi> 1 = 1"
    and mono: "mono_on {0..1} \<phi>"
  shows "path_length (g \<circ> \<phi>) = path_length g"
proof -
  have g_bv: "has_bounded_variation_on g {0..1}"
    using assms(1) unfolding rectifiable_path_def by auto
  \<comment> \<open>Upper bound: monotone composition decreases variation\<close>
  have upper: "vector_variation {0..1} (g \<circ> \<phi>) \<le> vector_variation {0..1} g"
    using has_bounded_variation_compose_monotone(2)[OF _ mono] g_bv assms(4,5) by simp
  \<comment> \<open>Lower bound: construct monotone right inverse \<psi> of \<phi>\<close>
  have \<phi>_surj: "\<phi> ` {0..1} = {0..1}"
    using IVT'[of \<phi> 0 _ 1] assms  by(force intro: continuous_on_subset[OF assms(2)])
  define \<psi> where "\<psi> s = (SOME t. t \<in> {0..1} \<and> \<phi> t = s)" for s
  have \<psi>_prop: "\<psi> s \<in> {0..1} \<and> \<phi> (\<psi> s) = s" if "s \<in> {0..1}" for s
    by (smt (verit, del_insts) \<phi>_surj \<psi>_def imageE someI_ex that)
  have \<psi>_mono: "mono_on {0..1} \<psi>"
    using mono unfolding monotone_on_def
    by (metis \<psi>_prop antisym linorder_le_cases)
  have \<psi>0: "\<psi> 0 \<in> {0..1}" using \<psi>_prop by auto
  have \<psi>1: "\<psi> 1 \<in> {0..1}" using \<psi>_prop by auto
  have bv_comp: "has_bounded_variation_on (g \<circ> \<phi>) {0..1}"
    using has_bounded_variation_compose_monotone(1)[OF _ mono] g_bv assms(4,5) by simp
  have lower: "vector_variation {0..1} g \<le> vector_variation {0..1} (g \<circ> \<phi>)"
  proof -
    have eq: "vector_variation {0..1} g = vector_variation {0..1} ((g \<circ> \<phi>) \<circ> \<psi>)"
      by (metis (mono_tags, lifting) \<psi>_prop comp_apply vector_variation_cong)
    have bv_sub: "has_bounded_variation_on (g \<circ> \<phi>) {\<psi> 0..\<psi> 1}"
      using has_bounded_variation_on_subset[OF bv_comp] \<psi>0 \<psi>1 by auto
    show ?thesis
      using has_bounded_variation_compose_monotone(2)[OF bv_sub \<psi>_mono]
      using \<psi>0 \<psi>1 bv_comp eq vector_variation_monotone by fastforce 
  qed
  show ?thesis
    unfolding path_length_def using upper lower by linarith
qed

section \<open>Uniqueness and minimality\<close>

lemma continuous_injective_on_interval_mono:
  fixes \<phi> :: "real \<Rightarrow> real"
  assumes cont: "continuous_on {a..b} \<phi>" and inj: "inj_on \<phi> {a..b}"
  shows "(\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. x \<le> y \<longrightarrow> \<phi> x \<le> \<phi> y) \<or>
         (\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. x \<le> y \<longrightarrow> \<phi> y \<le> \<phi> x)"
proof (cases "\<phi> a \<le> \<phi> b")
  case True
  \<comment> \<open>Show \<phi> is increasing\<close>
  have "\<phi> s \<le> \<phi> t" if st: "s \<in> {a..b}" "t \<in> {a..b}" "s \<le> t" for s t
  proof (rule ccontr)
    assume non: "\<not> \<phi> s \<le> \<phi> t"
    then have st_lt: "s < t"
      using less_eq_real_def that(3) by blast
    show False
    proof (cases "\<phi> t < \<phi> a")
      case True
      \<comment> \<open>\<phi>(t) < \<phi>(a) \<le> \<phi>(b), by IVT' on [t,b] get c with \<phi>(c) = \<phi>(a)\<close>
      obtain c where c: "c \<ge> t" "c \<le> b" "\<phi> c = \<phi> a"
        using IVT'[of \<phi> t "\<phi> a" b] True \<open>\<phi> a \<le> \<phi> b\<close> continuous_on_subset[OF cont] st by auto
      then have "c = a" using inj_onD[OF inj \<open>\<phi> c = \<phi> a\<close>] st by auto
      then show False using c(1) st_lt st(1) by auto
    next
      case False
      \<comment> \<open>\<phi>(a) \<le> \<phi>(t) < \<phi>(s), by IVT' on [a,s] get c with \<phi>(c) = \<phi>(t)\<close>
      obtain c where c: "c \<ge> a" "c \<le> s" "\<phi> c = \<phi> t"
        using IVT'[of \<phi> a "\<phi> t" s] False non continuous_on_subset[OF cont] st
        by auto
      then have "c = t" using inj_onD[OF inj \<open>\<phi> c = \<phi> t\<close>] st by auto
      then show False using c(2) st_lt by auto
    qed
  qed
  then show ?thesis by auto
next
  case False
  then have fab: "\<phi> b < \<phi> a"
    by auto
  \<comment> \<open>Show \<phi> is decreasing: symmetric argument\<close>
  have "\<phi> t \<le> \<phi> s" if st: "s \<in> {a..b}" "t \<in> {a..b}" "s \<le> t" for s t
  proof (rule ccontr)
    assume non: "\<not> \<phi> t \<le> \<phi> s"
    then have st_lt: "s < t" using st(3)
      using less_eq_real_def by fastforce
    show False
    proof (cases "\<phi> s < \<phi> b")
      case True
      \<comment> \<open>\<phi>(s) < \<phi>(b) < \<phi>(a), by IVT2' on [a,s] get c with \<phi>(c) = \<phi>(b)\<close>
      obtain c where c: "c \<ge> a" "c \<le> s" "\<phi> c = \<phi> b"
        using IVT2'[of \<phi> s "\<phi> b" a] True fab continuous_on_subset[OF cont] st by auto
      then have "c = b" using inj_onD[OF inj \<open>\<phi> c = \<phi> b\<close>] st by auto
      then show False using c(2) st_lt st(2) by auto
    next
      case False
      \<comment> \<open>\<phi>(b) \<le> \<phi>(s) < \<phi>(t), by IVT2' on [t,b] get c with \<phi>(c) = \<phi>(s)\<close>
      then obtain c where c: "c \<ge> t" "c \<le> b" "\<phi> c = \<phi> s"
        using IVT2'[of \<phi> b "\<phi> s" t] non continuous_on_subset[OF cont] st by auto
      then have "c = s" using inj_onD[OF inj \<open>\<phi> c = \<phi> s\<close>] st by auto
      then show False using c(1) st_lt by auto
    qed
  qed
  then show ?thesis by auto
qed

lemma continuous_on_path_length_subpath_right:
  assumes "rectifiable_path g" "s \<in> {0..1}"
  shows "continuous_on {0..1} (\<lambda>t. path_length (subpath s t g))"
proof -
  have g_bv: "has_bounded_variation_on g {0..1}"
    using assms(1) unfolding rectifiable_path_def by auto
  have g_cont: "continuous_on {0..1} g"
    using assms(1) unfolding rectifiable_path_def path_def by auto
  define V where "V t = vector_variation {0..t} g" for t :: real
  have V_cont: "continuous_on {0..1} V"
    unfolding V_def continuous_on_eq_continuous_within
    by (metis continuous_on_eq_continuous_within g_bv g_cont vector_variation_continuous)
  have V_mono: "V x \<le> V y" if "x \<in> {0..1}" "y \<in> {0..1}" "x \<le> y" for x y
  proof -
    have bv_0y: "has_bounded_variation_on g {0..y}"
      using has_bounded_variation_on_subset[OF g_bv] that by auto
    have "V y = V x + vector_variation {x..y} g"
      using vector_variation_combine[OF bv_0y] that unfolding V_def by auto
    moreover have "vector_variation {x..y} g \<ge> 0"
      using vector_variation_pos_le[OF has_bounded_variation_on_subset[OF g_bv]] that by auto
    ultimately show ?thesis by linarith
  qed
  have eq: "path_length (subpath s t g) = \<bar>V t - V s\<bar>"
    if t01: "t \<in> {0..1}" for t
  proof -
    have "path_length (subpath s t g) = vector_variation (closed_segment s t) g"
      using path_length_subpath_eq[OF assms(2) t01 assms(1)] .
    also have "\<dots> = \<bar>V t - V s\<bar>"
    proof (cases "s \<le> t")
      case True
      have bv_0t: "has_bounded_variation_on g {0..t}"
        using has_bounded_variation_on_subset[OF g_bv] t01 by auto
      have split: "V t = V s + vector_variation {s..t} g"
        using vector_variation_combine[OF bv_0t] assms(2) True unfolding V_def by simp
      then have "vector_variation {s..t} g = V t - V s" by linarith
      then show ?thesis using True
        using V_mono assms(2) closed_segment_eq_real_ivl1 that by force
    next
      case False
      have bv_0s: "has_bounded_variation_on g {0..s}"
        using has_bounded_variation_on_subset[OF g_bv] assms(2) by auto
      have split: "V s = V t + vector_variation {t..s} g"
        using vector_variation_combine[OF bv_0s] t01 False unfolding V_def by simp
      then have "vector_variation {t..s} g = V s - V t" by linarith
      then show ?thesis
        using False V_mono assms(2) that by (force simp: closed_segment_eq_real_ivl)
    qed
    finally show ?thesis .
  qed
  then have "continuous_on {0..1} (\<lambda>t. \<bar>V t - V s\<bar>) = continuous_on {0..1} (\<lambda>t. path_length (subpath s t g))"
    by (metis (no_types, lifting) path_def path_eq)
  moreover have "continuous_on {0..1} (\<lambda>t. \<bar>V t - V s\<bar>)"
    by (intro continuous_intros V_cont)
  ultimately show ?thesis
    by blast
qed

lemma continuous_on_path_length_subpath_left:
  assumes "rectifiable_path g" "t \<in> {0..1}"
  shows "continuous_on {0..1} (\<lambda>s. path_length (subpath s t g))"
proof -
  have eq: "path_length (subpath s t g) = path_length (subpath t s g)" if "s \<in> {0..1}" for s
    by (metis assms closed_segment_commute path_length_subpath_eq that)
  have "continuous_on {0..1} (\<lambda>s. path_length (subpath t s g))"
    using continuous_on_path_length_subpath_right[OF assms] .
  with eq show ?thesis
    using continuous_on_eq by force
qed

end
