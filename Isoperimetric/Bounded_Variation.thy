theory Bounded_Variation
  imports "HOL-Analysis.Analysis"
begin

lemma continuous_within_comparison:
  fixes f :: \<open>'a::metric_space \<Rightarrow> 'b::metric_space\<close>
    and g :: \<open>'a::metric_space \<Rightarrow> 'c::metric_space\<close>
  assumes \<open>continuous (at a within s) g\<close>
    and \<open>\<And>x. x \<in> s \<Longrightarrow> dist (f a) (f x) \<le> dist (g a) (g x)\<close>
  shows \<open>continuous (at a within s) f\<close>
  unfolding continuous_within_eps_delta
proof (intro allI impI)
  fix \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>
  with assms(1)[unfolded continuous_within_eps_delta]
  obtain \<delta> where \<open>\<delta> > 0\<close> and \<delta>: \<open>\<And>x'. x' \<in> s \<Longrightarrow> dist x' a < \<delta> \<Longrightarrow> dist (g x') (g a) < \<epsilon>\<close>
    by auto
  show \<open>\<exists>\<delta>>0. \<forall>x'\<in>s. dist x' a < \<delta> \<longrightarrow> dist (f x') (f a) < \<epsilon>\<close>
  proof (intro exI conjI ballI impI)
    show \<open>\<delta> > 0\<close> by fact
  next
    fix x' assume \<open>x' \<in> s\<close> \<open>dist x' a < \<delta>\<close>
    have \<open>dist (f a) (f x') \<le> dist (g a) (g x')\<close> using assms(2) \<open>x' \<in> s\<close> by simp
    also have \<open>dist (g a) (g x') = dist (g x') (g a)\<close> by (simp add: dist_commute)
    also have \<open>\<dots> < \<epsilon>\<close> using \<delta> \<open>x' \<in> s\<close> \<open>dist x' a < \<delta>\<close> by simp
    finally show \<open>dist (f x') (f a) < \<epsilon>\<close> by (simp add: dist_commute)
  qed
qed

lemma continuous_within_ivl_split:
  fixes c :: \<open>'a::linorder_topology\<close>
  assumes \<open>c \<in> {a..b}\<close>
  shows \<open>continuous (at c within {a..b}) f \<longleftrightarrow>
         continuous (at c within {a..c}) f \<and> continuous (at c within {c..b}) f\<close>
proof -
  from assms have \<open>a \<le> c\<close> \<open>c \<le> b\<close> by auto
  then have \<open>{a..b} = {a..c} \<union> {c..b}\<close> by (rule ivl_disj_un_two_touch(4) [symmetric])
  then show ?thesis
    by (simp add: continuous_within Lim_within_Un)
qed

hide_const (open) Polynomial.content

text \<open>
  Bounded variation and vector variation for functions @{typ "real \<Rightarrow> 'a::euclidean_space"},
  following HOL Light's @{text "Multivariate/integration.ml"} (lines 8660--19100).

  HOL Light works with @{text "real^1 \<Rightarrow> real^N"} and defines bounded variation via
  set variation of the increment function. We adapt this to Isabelle's @{typ real}
  domain directly.
\<close>

section \<open>Set variation\<close>

definition set_variation :: "real set \<Rightarrow> (real set \<Rightarrow> 'a::euclidean_space) \<Rightarrow> real" where
  "set_variation s f = Sup {(\<Sum>k\<in>d. norm (f k)) | d. \<exists>t. d division_of t \<and> t \<subseteq> s}"

definition has_bounded_setvariation_on ::
  "(real set \<Rightarrow> 'a::euclidean_space) \<Rightarrow> real set \<Rightarrow> bool" where
  "has_bounded_setvariation_on f s \<longleftrightarrow>
    (\<exists>B. \<forall>d t. d division_of t \<and> t \<subseteq> s \<longrightarrow> (\<Sum>k\<in>d. norm (f k)) \<le> B)"

section \<open>Bounded variation for functions\<close>

definition has_bounded_variation_on ::
  "(real \<Rightarrow> 'a::euclidean_space) \<Rightarrow> real set \<Rightarrow> bool" where
  "has_bounded_variation_on f s \<longleftrightarrow>
    has_bounded_setvariation_on (\<lambda>k. f (Sup k) - f (Inf k)) s"

definition vector_variation :: "real set \<Rightarrow> (real \<Rightarrow> 'a::euclidean_space) \<Rightarrow> real" where
  "vector_variation s f = set_variation s (\<lambda>k. f (Sup k) - f (Inf k))"

subsection \<open>Closure and subset properties\<close>

lemma has_bounded_variation_on_subset:
  "has_bounded_variation_on f s \<Longrightarrow> t \<subseteq> s \<Longrightarrow> has_bounded_variation_on f t"
  unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def
  by (meson order_trans)

lemma has_bounded_variation_on_const:
  "has_bounded_variation_on (\<lambda>x. c) s"
  unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def
  by (rule exI[of _ 0]) simp

lemma has_bounded_variation_on_cmul:
  "has_bounded_variation_on f s \<Longrightarrow> has_bounded_variation_on (\<lambda>x. a *\<^sub>R f x) s"
  unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def
proof -
  assume "\<exists>B. \<forall>d t. d division_of t \<and> t \<subseteq> s \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B"
  then obtain B where B: "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B"
    by meson
  show "\<exists>B. \<forall>d t. d division_of t \<and> t \<subseteq> s \<longrightarrow>
    (\<Sum>k\<in>d. norm (a *\<^sub>R f (Sup k) - a *\<^sub>R f (Inf k))) \<le> B"
  proof (intro exI allI impI)
    fix d t assume \<section>: "d division_of t \<and> t \<subseteq> s"
    have "(\<Sum>k\<in>d. norm (a *\<^sub>R f (Sup k) - a *\<^sub>R f (Inf k))) =
      (\<Sum>k\<in>d. \<bar>a\<bar> * norm (f (Sup k) - f (Inf k)))"
      by (simp add: scaleR_diff_right[symmetric])
    also have "\<dots> = \<bar>a\<bar> * (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))"
      by (simp add: sum_distrib_left)
    also have "\<dots> \<le> \<bar>a\<bar> * B"
      using B \<section> abs_ge_zero mult_left_mono by blast
    finally show "(\<Sum>k\<in>d. norm (a *\<^sub>R f (Sup k) - a *\<^sub>R f (Inf k))) \<le> \<bar>a\<bar> * B" .
  qed
qed

lemma has_bounded_variation_on_neg:
  "has_bounded_variation_on f s \<Longrightarrow> has_bounded_variation_on (\<lambda>x. - f x) s"
  using has_bounded_variation_on_cmul[of f s "-1"]
  by simp

lemma has_bounded_variation_on_add:
  "has_bounded_variation_on f s \<Longrightarrow> has_bounded_variation_on g s \<Longrightarrow>
    has_bounded_variation_on (\<lambda>x. f x + g x) s"
  unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def
proof -
  assume "\<exists>B. \<forall>d t. d division_of t \<and> t \<subseteq> s \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B"
  then obtain Bf where Bf: "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> Bf"
    by blast
  assume "\<exists>B. \<forall>d t. d division_of t \<and> t \<subseteq> s \<longrightarrow>
    (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> B"
  then obtain Bg where Bg: "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
    (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> Bg" 
    by blast
  show "\<exists>B. \<forall>d t. d division_of t \<and> t \<subseteq> s \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) + g (Sup k) - (f (Inf k) + g (Inf k)))) \<le> B"
  proof (intro exI allI impI)
    fix d t assume \<section>: "d division_of t \<and> t \<subseteq> s"
    have "(\<Sum>k\<in>d. norm (f (Sup k) + g (Sup k) - (f (Inf k) + g (Inf k)))) =
      (\<Sum>k\<in>d. norm ((f (Sup k) - f (Inf k)) + (g (Sup k) - g (Inf k))))"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) + norm (g (Sup k) - g (Inf k)))"
      by (intro sum_mono norm_triangle_ineq)
    also have "\<dots> = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) + (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))"
      by (simp add: sum.distrib)
    also have "\<dots> \<le> Bf + Bg"
      using Bf Bg \<section> add_mono by blast
    finally show "(\<Sum>k\<in>d. norm (f (Sup k) + g (Sup k) - (f (Inf k) + g (Inf k)))) \<le> Bf + Bg" .
  qed
qed

lemma has_bounded_variation_on_sub:
  "has_bounded_variation_on f s \<Longrightarrow> has_bounded_variation_on g s \<Longrightarrow>
    has_bounded_variation_on (\<lambda>x. f x - g x) s"
  using has_bounded_variation_on_add[of f s "\<lambda>x. - g x"]
    has_bounded_variation_on_neg[of g s]
  by simp


lemma has_bounded_variation_on_norm:
  "has_bounded_variation_on f s \<Longrightarrow>
    has_bounded_variation_on (\<lambda>x. norm (f x) *\<^sub>R e) s"
  unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def
proof -
  assume "\<exists>B. \<forall>d t. d division_of t \<and> t \<subseteq> s \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B"
  then obtain B where B: "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B"
    by blast
  show "\<exists>B. \<forall>d t. d division_of t \<and> t \<subseteq> s \<longrightarrow>
    (\<Sum>k\<in>d. norm (norm (f (Sup k)) *\<^sub>R e - norm (f (Inf k)) *\<^sub>R e)) \<le> B"
  proof (intro exI allI impI)
    fix d t assume dt: "d division_of t \<and> t \<subseteq> s"
    have "(\<Sum>k\<in>d. norm (norm (f (Sup k)) *\<^sub>R e - norm (f (Inf k)) *\<^sub>R e)) =
      (\<Sum>k\<in>d. \<bar>norm (f (Sup k)) - norm (f (Inf k))\<bar> * norm e)"
      by (simp add: scaleR_diff_left[symmetric])
    also have "\<dots> \<le> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) * norm e)"
      by (intro sum_mono mult_right_mono) (auto simp: norm_triangle_ineq3)
    also have "\<dots> = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) * norm e"
      by (simp add: sum_distrib_right)
    also have "\<dots> \<le> B * norm e"
      using B dt landau_o.R_mult_right_mono by force
    finally show "(\<Sum>k\<in>d. norm (norm (f (Sup k)) *\<^sub>R e - norm (f (Inf k)) *\<^sub>R e)) \<le> B * norm e" .
  qed
qed

lemma has_bounded_variation_on_inner_left:
  assumes \<open>has_bounded_variation_on f s\<close>
  shows \<open>has_bounded_variation_on (\<lambda>x. f x \<bullet> b) s\<close>
  unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def
proof -
  from assms obtain B where B: \<open>\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B\<close>
    unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def by meson
  show \<open>\<exists>B. \<forall>d t. d division_of t \<and> t \<subseteq> s \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) \<bullet> b - f (Inf k) \<bullet> b)) \<le> B\<close>
  proof (intro exI[of _ \<open>B * norm b\<close>] allI impI)
    fix d t assume dt: \<open>d division_of t \<and> t \<subseteq> s\<close>
    have \<open>(\<Sum>k\<in>d. norm (f (Sup k) \<bullet> b - f (Inf k) \<bullet> b)) =
      (\<Sum>k\<in>d. \<bar>(f (Sup k) - f (Inf k)) \<bullet> b\<bar>)\<close>
      by (simp add: inner_diff_left)
    also have \<open>\<dots> \<le> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) * norm b)\<close>
      by (intro sum_mono) (auto simp: Cauchy_Schwarz_ineq2)
    also have \<open>\<dots> = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) * norm b\<close>
      by (simp add: sum_distrib_right)
    also have \<open>\<dots> \<le> B * norm b\<close>
      using B dt by (intro mult_right_mono) auto
    finally show \<open>(\<Sum>k\<in>d. norm (f (Sup k) \<bullet> b - f (Inf k) \<bullet> b)) \<le> B * norm b\<close> .
  qed
qed


subsection \<open>Other fundamental properties\<close>

lemma has_bounded_variation_on_interval:
  "has_bounded_variation_on f {a..b} \<longleftrightarrow>
    (\<exists>B. \<forall>d. d division_of {a..b} \<longrightarrow>
      (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B)"
proof (unfold has_bounded_variation_on_def has_bounded_setvariation_on_def, rule iffI)
  assume "\<exists>B. \<forall>d t. d division_of t \<and> t \<subseteq> {a..b} \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B"
  then show "\<exists>B. \<forall>d. d division_of {a..b} \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B"
    by auto
next
  assume "\<exists>B. \<forall>d. d division_of {a..b} \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B"
  then obtain B where B: "\<And>d. d division_of {a..b} \<Longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B"
    by auto
  show "\<exists>B. \<forall>d t. d division_of t \<and> t \<subseteq> {a..b} \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B"
  proof (intro exI allI impI)
    fix d t
    assume dt: "d division_of t \<and> t \<subseteq> {a..b}"
    then have div_d: "d division_of t" and sub: "t \<subseteq> {a..b}" by auto
    have div_union: "d division_of \<Union>d"
      using division_of_union_self[OF div_d] .
    have union_eq: "\<Union>d = t"
      using division_ofD(6)[OF div_d] .
    have union_sub: "\<Union>d \<subseteq> cbox a b"
      using sub unfolding union_eq cbox_interval .
    obtain q where dq: "d \<subseteq> q" and q_div: "q division_of cbox a b"
      using partial_division_extend_interval[OF div_union union_sub] by auto
    have q_div': "q division_of {a..b}"
      using q_div unfolding cbox_interval .
    have fin_q: "finite q"
      using division_of_finite[OF q_div] .
    have "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> (\<Sum>k\<in>q. norm (f (Sup k) - f (Inf k)))"
      by (rule sum_mono2[OF fin_q dq]) auto
    also have "\<dots> \<le> B"
      using B[OF q_div'] .
    finally show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B" .
  qed
qed

lemma vector_variation_on_interval:
  assumes "has_bounded_variation_on f {a..b}"
  shows "vector_variation {a..b} f =
    Sup {(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) | d. d division_of {a..b}}"
proof -
  let ?g = "\<lambda>k. f (Sup k) - f (Inf k)"
  define A where "A = {(\<Sum>k\<in>d. norm (?g k)) | d. \<exists>t. d division_of t \<and> t \<subseteq> {a..b}}"
  define B where "B = {(\<Sum>k\<in>d. norm (?g k)) | d. d division_of {a..b}}"
  have vv: "vector_variation {a..b} f = Sup A"
    unfolding vector_variation_def set_variation_def A_def by simp
  have B_sub_A: "B \<subseteq> A" unfolding A_def B_def by blast
  have B_ne: "B \<noteq> {}"
  proof -
    obtain p where "p division_of cbox a b" using elementary_interval by blast
    then show ?thesis unfolding B_def by (auto simp: cbox_interval)
  qed
  have A_ne: "A \<noteq> {}" using B_sub_A B_ne by auto
  have bdd_A: "bdd_above A"
  proof -
    from assms obtain M where M: "\<forall>d t. d division_of t \<and> t \<subseteq> {a..b} \<longrightarrow>
      (\<Sum>k\<in>d. norm (?g k)) \<le> M"
      unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def by auto
    show ?thesis unfolding bdd_above_def A_def
    proof (intro exI[of _ M] ballI)
      fix x assume "x \<in> {(\<Sum>k\<in>d. norm (?g k)) | d. \<exists>t. d division_of t \<and> t \<subseteq> {a..b}}"
      then obtain d t where "d division_of t" "t \<subseteq> {a..b}"
        "x = (\<Sum>k\<in>d. norm (?g k))" by auto
      then show "x \<le> M" using M by auto
    qed
  qed
  have bdd_B: "bdd_above B"
    using bdd_above_mono[OF bdd_A B_sub_A] .
  have A_le_B: "\<forall>x \<in> A. \<exists>y \<in> B. x \<le> y"
  proof
    fix x assume "x \<in> A"
    then obtain d t where dt: "d division_of t" "t \<subseteq> {a..b}"
      and x_eq: "x = (\<Sum>k\<in>d. norm (?g k))" unfolding A_def by auto
    have "d division_of \<Union>d" using division_of_union_self[OF dt(1)] .
    moreover have "\<Union>d = t" using division_ofD(6)[OF dt(1)] .
    ultimately have "\<Union>d \<subseteq> cbox a b" using dt(2) by (simp add: cbox_interval)
    then obtain q where dq: "d \<subseteq> q" and q_div: "q division_of cbox a b"
      using partial_division_extend_interval \<open>d division_of \<Union>d\<close> by blast
    have q_div': "q division_of {a..b}" using q_div by (simp add: cbox_interval)
    have fin_q: "finite q" using division_of_finite[OF q_div] .
    have "x \<le> (\<Sum>k\<in>q. norm (?g k))"
      unfolding x_eq by (rule sum_mono2[OF fin_q dq]) auto
    moreover have "(\<Sum>k\<in>q. norm (?g k)) \<in> B" unfolding B_def using q_div' by auto
    ultimately show "\<exists>y \<in> B. x \<le> y" by auto
  qed
  have "Sup A = Sup B"
  proof (rule antisym)
    show "Sup A \<le> Sup B"
    proof (rule cSup_least[OF A_ne])
      fix x assume "x \<in> A"
      then obtain y where yB: "y \<in> B" and xy: "x \<le> y" using A_le_B by auto
      have "y \<le> Sup B" using cSup_upper[OF yB bdd_B] .
      with xy show "x \<le> Sup B" by linarith
    qed
    show "Sup B \<le> Sup A"
      using cSup_subset_mono[OF B_ne bdd_A B_sub_A] .
  qed
  with vv show ?thesis unfolding B_def by simp
qed

lemma vector_variation_pos_le:
  assumes "has_bounded_variation_on f {a..b}"
  shows "0 \<le> vector_variation {a..b} f"
proof -
  have "vector_variation {a..b} f =
    Sup {(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) | d. d division_of {a..b}}"
    using vector_variation_on_interval[OF assms] .
  moreover have "0 \<le> Sup {(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) | d. d division_of {a..b}}"
  proof -
    let ?S = "{(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) | d. d division_of {a..b}}"
    obtain p where p: "p division_of cbox a b" using elementary_interval by blast
    then have "(\<Sum>k\<in>p. norm (f (Sup k) - f (Inf k))) \<in> ?S"
      by (auto simp: cbox_interval)
    moreover have "0 \<le> (\<Sum>k\<in>p. norm (f (Sup k) - f (Inf k)))"
      by (intro sum_nonneg) auto
    moreover have "bdd_above ?S"
    proof -
      from assms obtain M where "\<forall>d. d division_of {a..b} \<longrightarrow>
        (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> M"
        unfolding has_bounded_variation_on_interval by auto
      then show ?thesis unfolding bdd_above_def by auto
    qed
    ultimately show "0 \<le> Sup ?S"
      by (metis (no_types, lifting) cSup_upper2)
  qed
  ultimately show ?thesis by linarith
qed

lemma vector_variation_ge_norm_function:
  assumes "has_bounded_variation_on f {a..b}" "x \<in> {a..b}" "y \<in> {a..b}"
  shows "norm (f x - f y) \<le> vector_variation {a..b} f"
proof -
  let ?g = "\<lambda>k. f (Sup k) - f (Inf k)"
  define S where "S = {(\<Sum>k\<in>d. norm (?g k)) | d. \<exists>t. d division_of t \<and> t \<subseteq> {a..b}}"
  have vv: "vector_variation {a..b} f = Sup S"
    unfolding vector_variation_def set_variation_def S_def by simp
  have bdd: "bdd_above S"
  proof -
    from assms(1) obtain M where M: "\<forall>d t. d division_of t \<and> t \<subseteq> {a..b} \<longrightarrow>
      (\<Sum>k\<in>d. norm (?g k)) \<le> M"
      unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def by auto
    show ?thesis unfolding bdd_above_def S_def
    proof (intro exI[of _ M] ballI)
      fix x assume "x \<in> {(\<Sum>k\<in>d. norm (?g k)) | d. \<exists>t. d division_of t \<and> t \<subseteq> {a..b}}"
      then obtain d t where "d division_of t" "t \<subseteq> {a..b}"
        "x = (\<Sum>k\<in>d. norm (?g k))" by auto
      then show "x \<le> M" using M by auto
    qed
  qed
  \<comment> \<open>WLOG x \<le> y\<close>
  have "norm (f x - f y) = norm (f (min x y) - f (max x y))"
    by (simp add: min_def max_def norm_minus_commute)
  also have "\<dots> = norm (f (max x y) - f (min x y))"
    by (simp add: norm_minus_commute)
  also have "\<dots> \<le> Sup S"
  proof -
    let ?lo = "min x y" and ?hi = "max x y"
    have lo_le_hi: "?lo \<le> ?hi" by simp
    have sub: "{?lo..?hi} \<subseteq> {a..b}" using assms(2,3) by auto
    have ne: "cbox ?lo ?hi \<noteq> {}" using lo_le_hi by (simp add: cbox_interval)
    have div: "{cbox ?lo ?hi} division_of cbox ?lo ?hi"
      using division_of_self[OF ne] .
    then have div': "{{?lo..?hi}} division_of {?lo..?hi}"
      by (simp add: cbox_interval)
    have "norm (f ?hi - f ?lo) = (\<Sum>k\<in>{{?lo..?hi}}. norm (?g k))"
      using lo_le_hi by (simp add: interval_bounds_real)
    also have "\<dots> \<in> S" unfolding S_def using div' sub by blast
    finally have "norm (f ?hi - f ?lo) \<in> S" .
    then show "norm (f ?hi - f ?lo) \<le> Sup S"
      using cSup_upper[OF _ bdd] by auto
  qed
  also have "Sup S = vector_variation {a..b} f" using vv by simp
  finally show ?thesis by simp
qed

lemma vector_variation_const_eq:
  assumes "has_bounded_variation_on f {a..b}" "is_interval {a..b}"
  shows "vector_variation {a..b} f = 0 \<longleftrightarrow> (\<exists>c. \<forall>t \<in> {a..b}. f t = c)"
proof
  assume vv0: "vector_variation {a..b} f = 0"
  show "\<exists>c. \<forall>t \<in> {a..b}. f t = c"
  proof (cases "{a..b} = {}")
    case True then show ?thesis by auto
  next
    case False
    then obtain z where z: "z \<in> {a..b}" by auto
    have "\<forall>t \<in> {a..b}. f t = f z"
    proof
      fix t assume t: "t \<in> {a..b}"
      have "norm (f t - f z) \<le> vector_variation {a..b} f"
        using vector_variation_ge_norm_function[OF assms(1) t z] .
      then have "norm (f t - f z) \<le> 0" using vv0 by simp
      then show "f t = f z" by simp
    qed
    then show ?thesis by auto
  qed
next
  assume "\<exists>c. \<forall>t \<in> {a..b}. f t = c"
  then obtain c where c: "\<And>t. t \<in> {a..b} \<Longrightarrow> f t = c" by auto
  have eq: "vector_variation {a..b} f =
    Sup {(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) | d. d division_of {a..b}}"
    using vector_variation_on_interval[OF assms(1)] .
  have all_zero: "\<And>d. d division_of {a..b} \<Longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) = 0"
  proof -
    fix d assume div: "d division_of {a..b}"
    show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) = 0"
    proof (rule sum.neutral, rule ballI)
      fix k assume kd: "k \<in> d"
      have ksub: "k \<subseteq> {a..b}" using division_ofD(2)[OF div kd] .
      have kne: "k \<noteq> {}" using division_ofD(3)[OF div kd] .
      obtain u v where kuv: "k = cbox u v" using division_ofD(4)[OF div kd] by auto
      then have "k = {u..v}" by (simp add: cbox_interval)
      with kne have uv: "u \<le> v" by auto
      have "Sup k = v" unfolding \<open>k = {u..v}\<close> using interval_bounds_real(1)[OF uv] .
      have "Inf k = u" unfolding \<open>k = {u..v}\<close> using interval_bounds_real(2)[OF uv] .
      have "v \<in> {a..b}" using ksub uv unfolding \<open>k = {u..v}\<close> by auto
      have "u \<in> {a..b}" using ksub uv unfolding \<open>k = {u..v}\<close> by auto
      then show "norm (f (Sup k) - f (Inf k)) = 0"
        using c[OF \<open>v \<in> {a..b}\<close>] c[OF \<open>u \<in> {a..b}\<close>]
        unfolding \<open>Sup k = v\<close> \<open>Inf k = u\<close> by simp
    qed
  qed
  have "{(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) | d. d division_of {a..b}} = {0}"
  proof
    show "{(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) | d. d division_of {a..b}} \<subseteq> {0}"
      using all_zero by auto
    show "{0} \<subseteq> {(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) | d. d division_of {a..b}}"
    proof -
      obtain p where "p division_of cbox a b" using elementary_interval by blast
      then have "p division_of {a..b}" by (simp add: cbox_interval)
      moreover have "(\<Sum>k\<in>p. norm (f (Sup k) - f (Inf k))) = 0"
        using all_zero[OF \<open>p division_of {a..b}\<close>] .
      ultimately show ?thesis by auto
    qed
  qed
  then have "Sup {(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) | d. d division_of {a..b}} = 0"
    using cSup_singleton by simp
  with eq show "vector_variation {a..b} f = 0" by simp
qed

lemma vector_variation_on_null:
  assumes "content {a..b} = 0"
  shows "vector_variation {a..b} f = 0"
proof -
  let ?g = "\<lambda>k. f (Sup k) - f (Inf k)"
  from assms have ba: "b \<le> a" using content_real_eq_0 by auto
  have all_zero: "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> {a..b} \<Longrightarrow>
    (\<Sum>k\<in>d. norm (?g k)) = 0"
  proof -
    fix d t assume div: "d division_of t" and sub: "t \<subseteq> {a..b}"
    have t_sub: "t \<subseteq> {a..b}" using sub .
    have fin: "finite d" using division_of_finite[OF div] .
    show "(\<Sum>k\<in>d. norm (?g k)) = 0"
    proof (rule sum.neutral, rule ballI)
      fix k assume kd: "k \<in> d"
      obtain u v where kuv: "k = cbox u v" using division_ofD(4)[OF div kd] by auto
      have kne: "k \<noteq> {}" using division_ofD(3)[OF div kd] .
      have ksub: "k \<subseteq> {a..b}" using division_ofD(2)[OF div kd] sub by auto
      from kuv have "k = {u..v}" by (simp add: cbox_interval)
      with kne have uv: "u \<le> v" by auto
      from ksub have "u \<in> {a..b}" "v \<in> {a..b}" using uv unfolding \<open>k = {u..v}\<close> by auto
      then have "u = a" "v = a" using ba by auto
      then show "norm (?g k) = 0" unfolding \<open>k = {u..v}\<close>
        using interval_bounds_real[OF uv] by simp
    qed
  qed
  have "{(\<Sum>k\<in>d. norm (?g k)) | d. \<exists>t. d division_of t \<and> t \<subseteq> {a..b}} = {0}"
  proof
    show "{(\<Sum>k\<in>d. norm (?g k)) | d. \<exists>t. d division_of t \<and> t \<subseteq> {a..b}} \<subseteq> {0}"
      using all_zero by auto
    have "{} division_of {}" using division_of_trivial by simp
    moreover have "({} :: real set) \<subseteq> {a..b}" by auto
    ultimately show "{0} \<subseteq> {(\<Sum>k\<in>d. norm (?g k)) | d. \<exists>t. d division_of t \<and> t \<subseteq> {a..b}}"
      by (auto intro!: exI[of _ "{}"] exI[of _ "{}"])
  qed
  then have eq0: "vector_variation {a..b} f = Sup {0 :: real}"
    unfolding vector_variation_def set_variation_def by simp
  then show ?thesis using cSup_singleton by simp
qed

lemma vector_variation_monotone:
  assumes "has_bounded_variation_on f {a..b}" "{c..d} \<subseteq> {a..b}"
  shows "vector_variation {c..d} f \<le> vector_variation {a..b} f"
proof -
  let ?g = "\<lambda>k. f (Sup k) - f (Inf k)"
  define A where "A = {(\<Sum>k\<in>p. norm (?g k)) | p. \<exists>t. p division_of t \<and> t \<subseteq> {a..b}}"
  define C where "C = {(\<Sum>k\<in>p. norm (?g k)) | p. \<exists>t. p division_of t \<and> t \<subseteq> {c..d}}"
  have vvab: "vector_variation {a..b} f = Sup A"
    unfolding vector_variation_def set_variation_def A_def by simp
  have vvcd: "vector_variation {c..d} f = Sup C"
    unfolding vector_variation_def set_variation_def C_def by simp
  have C_sub_A: "C \<subseteq> A" unfolding C_def A_def using assms(2) by blast
  have C_ne: "C \<noteq> {}"
    by (metis (mono_tags, lifting) C_def Collect_empty_eq_bot Orderings.order_eq_iff
        bot_empty_eq box_real(2) elementary_interval ex_in_conv)
  have bdd_A: "bdd_above A"
  proof -
    from assms(1) obtain M where "\<forall>p t. p division_of t \<and> t \<subseteq> {a..b} \<longrightarrow>
      (\<Sum>k\<in>p. norm (?g k)) \<le> M"
      unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def by auto
    then show ?thesis unfolding bdd_above_def A_def
      by (intro exI[of _ M] ballI) auto
  qed
  have "Sup C \<le> Sup A"
    using cSup_subset_mono[OF C_ne bdd_A C_sub_A] .
  with vvab vvcd show ?thesis by simp
qed

lemma has_bounded_setvariation_works:
  assumes "has_bounded_setvariation_on f s"
  shows "(\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow> (\<Sum>k\<in>d. norm (f k)) \<le> set_variation s f)"
    and "(\<And>B. (\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow> (\<Sum>k\<in>d. norm (f k)) \<le> B) \<Longrightarrow>
            set_variation s f \<le> B)"
proof -
  define S where "S = {\<Sum>k\<in>d. norm (f k) | d. \<exists>t. d division_of t \<and> t \<subseteq> s}"
  have sv_eq: "set_variation s f = Sup S"
    unfolding set_variation_def S_def ..
  have S_ne: "S \<noteq> {}"
  proof -
    have "({} :: real set set) division_of ({} :: real set)"
      using division_of_trivial by simp
    moreover have "({} :: real set) \<subseteq> s" by simp
    ultimately have "(\<Sum>k\<in>({}::real set set). norm (f k)) \<in> S"
      unfolding S_def by blast
    then show ?thesis by auto
  qed
  have bdd: "bdd_above S"
  proof -
    from assms obtain B where B: "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
      (\<Sum>k\<in>d. norm (f k)) \<le> B"
      unfolding has_bounded_setvariation_on_def by meson
    show ?thesis unfolding bdd_above_def S_def
      by (intro exI[of _ B] ballI) (auto intro: B)
  qed
  {
    fix d t assume "d division_of t" "t \<subseteq> s"
    then have "(\<Sum>k\<in>d. norm (f k)) \<in> S"
      unfolding S_def by blast
    then show "(\<Sum>k\<in>d. norm (f k)) \<le> set_variation s f"
      unfolding sv_eq using cSup_upper[OF _ bdd] by auto
  }
  {
    fix B :: real
    assume "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow> (\<Sum>k\<in>d. norm (f k)) \<le> B"
    then have "\<forall>x \<in> S. x \<le> B" unfolding S_def by auto
    then show "set_variation s f \<le> B"
      unfolding sv_eq using cSup_le_iff[OF S_ne bdd] by auto
  }
qed

lemma has_bounded_variation_works:
  assumes "has_bounded_variation_on f s"
  shows "(\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
            (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> vector_variation s f)"
    and "(\<And>B. (\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
                  (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B) \<Longrightarrow>
            vector_variation s f \<le> B)"
  using has_bounded_setvariation_works[of "\<lambda>k. f (Sup k) - f (Inf k)" s]
    assms[unfolded has_bounded_variation_on_def]
  unfolding vector_variation_def by auto

lemma vector_variation_le_component_sum:
  assumes \<open>has_bounded_variation_on f s\<close>
  shows \<open>vector_variation s f \<le> (\<Sum>b\<in>Basis. vector_variation s (\<lambda>u. f u \<bullet> b))\<close>
proof (rule has_bounded_variation_works(2)[OF assms])
  fix d t assume dt: \<open>d division_of t\<close> \<open>t \<subseteq> s\<close>
  have \<open>(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le>
    (\<Sum>k\<in>d. \<Sum>b\<in>Basis. \<bar>(f (Sup k) - f (Inf k)) \<bullet> b\<bar>)\<close>
    by (intro sum_mono norm_le_l1)
  also have \<open>\<dots> = (\<Sum>b\<in>Basis. \<Sum>k\<in>d. \<bar>(f (Sup k) - f (Inf k)) \<bullet> b\<bar>)\<close>
    by (rule sum.swap)
  also have \<open>\<dots> = (\<Sum>b\<in>Basis. \<Sum>k\<in>d. norm (f (Sup k) \<bullet> b - f (Inf k) \<bullet> b))\<close>
    by (simp add: inner_diff_left)
  also have \<open>\<dots> \<le> (\<Sum>b\<in>Basis. vector_variation s (\<lambda>u. f u \<bullet> b))\<close>
    by (intro sum_mono has_bounded_variation_works(1)[OF has_bounded_variation_on_inner_left[OF assms] dt(1,2)])
  finally show \<open>(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le>
    (\<Sum>b\<in>Basis. vector_variation s (\<lambda>u. f u \<bullet> b))\<close> .
qed


lemma vector_variation_triangle:
  assumes "has_bounded_variation_on f s" "has_bounded_variation_on g s"
  shows "vector_variation s (\<lambda>x. f x + g x) \<le> vector_variation s f + vector_variation s g"
proof (rule has_bounded_variation_works(2)[OF has_bounded_variation_on_add[OF assms]])
  fix d t assume dt: "d division_of t" "t \<subseteq> s"
  have "(\<Sum>k\<in>d. norm (f (Sup k) + g (Sup k) - (f (Inf k) + g (Inf k)))) =
    (\<Sum>k\<in>d. norm ((f (Sup k) - f (Inf k)) + (g (Sup k) - g (Inf k))))"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) + norm (g (Sup k) - g (Inf k)))"
    by (intro sum_mono norm_triangle_ineq)
  also have "\<dots> = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) + (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))"
    by (simp add: sum.distrib)
  also have "\<dots> \<le> vector_variation s f + vector_variation s g"
    by (intro add_mono has_bounded_variation_works(1)[OF assms(1) dt(1,2)]
                        has_bounded_variation_works(1)[OF assms(2) dt(1,2)])
  finally show "(\<Sum>k\<in>d. norm (f (Sup k) + g (Sup k) - (f (Inf k) + g (Inf k))))
    \<le> vector_variation s f + vector_variation s g" .
qed

lemma vector_variation_neg:
  shows "vector_variation s (\<lambda>x. - f x) = vector_variation s f"
  unfolding vector_variation_def set_variation_def
  by (simp add: norm_minus_commute)

lemma vector_variation_triangle_sub:
  assumes "has_bounded_variation_on f s" "has_bounded_variation_on g s"
  shows "vector_variation s (\<lambda>x. f x - g x) \<le> vector_variation s f + vector_variation s g"
proof -
  have "vector_variation s (\<lambda>x. f x - g x) = vector_variation s (\<lambda>x. f x + (- g x))"
    by simp
  also have "\<dots> \<le> vector_variation s f + vector_variation s (\<lambda>x. - g x)"
    by (rule vector_variation_triangle[OF assms(1) has_bounded_variation_on_neg[OF assms(2)]])
  also have "vector_variation s (\<lambda>x. - g x) = vector_variation s g"
    by (rule vector_variation_neg)
  finally show ?thesis .
qed



lemma vector_variation_le_Un:
  assumes fst: "has_bounded_variation_on f (s \<union> t)" and "interior s \<inter> interior t = {}"
  shows "vector_variation s f + vector_variation t f
         \<le> vector_variation (s \<union> t) f"
proof -
  have bvs: "has_bounded_variation_on f s"
    by (rule has_bounded_variation_on_subset[OF assms(1)]) auto
  have bvt: "has_bounded_variation_on f t"
    by (rule has_bounded_variation_on_subset[OF assms(1)]) auto
  have "vector_variation s f \<le> vector_variation (s \<union> t) f - vector_variation t f"
  proof (rule has_bounded_variation_works(2)[OF bvs])
    fix ds s' assume ds: "ds division_of s'" "s' \<subseteq> s"
    show "(\<Sum>k\<in>ds. norm (f (Sup k) - f (Inf k)))
          \<le> vector_variation (s \<union> t) f - vector_variation t f"
    proof -
      have "vector_variation t f
            \<le> vector_variation (s \<union> t) f - (\<Sum>k\<in>ds. norm (f (Sup k) - f (Inf k)))"
      proof (rule has_bounded_variation_works(2)[OF bvt])
        fix dt t' assume dt: "dt division_of t'" "t' \<subseteq> t"
        show "(\<Sum>k\<in>dt. norm (f (Sup k) - f (Inf k)))
              \<le> vector_variation (s \<union> t) f - (\<Sum>k\<in>ds. norm (f (Sup k) - f (Inf k)))"
        proof -
          have disj: "interior s' \<inter> interior t' = {}"
          proof -
            have "interior s' \<subseteq> interior s" by (rule interior_mono[OF ds(2)])
            moreover have "interior t' \<subseteq> interior t" by (rule interior_mono[OF dt(2)])
            ultimately show ?thesis using assms(2) by blast
          qed
          have "ds \<union> dt division_of s' \<union> t'"
            by (rule division_disjoint_union[OF ds(1) dt(1) disj])
          moreover have "s' \<union> t' \<subseteq> s \<union> t"
            using ds(2) dt(2) by auto
          moreover have "(\<Sum>k\<in>ds. norm (f (Sup k) - f (Inf k)))
                       + (\<Sum>k\<in>dt. norm (f (Sup k) - f (Inf k)))
                       = (\<Sum>k\<in>ds \<union> dt. norm (f (Sup k) - f (Inf k)))"
          proof (rule sum.union_inter_neutral[symmetric])
            show "finite ds" by (rule division_ofD(1)[OF ds(1)])
            show "finite dt" by (rule division_ofD(1)[OF dt(1)])
            show "\<forall>x\<in>ds \<inter> dt. norm (f (Sup x) - f (Inf x)) = 0"
            proof
              fix k assume k: "k \<in> ds \<inter> dt"
              then have ks: "k \<in> ds" and kt: "k \<in> dt" by auto
              obtain a b where kab: "k = cbox a b"
                using division_ofD(4)[OF ds(1) ks] by auto
              have "k \<noteq> {}" using division_ofD(3)[OF ds(1) ks] .
              then have ab: "a \<le> b" using kab by (simp add: box_real)
              have "interior k \<subseteq> interior s'" using division_ofD(2)[OF ds(1) ks] by (rule interior_mono)
              moreover have "interior k \<subseteq> interior t'" using division_ofD(2)[OF dt(1) kt] by (rule interior_mono)
              ultimately have "interior k = {}" using disj by blast
              then have "box a b = {}" using kab by (simp add: interior_cbox)
              then have "b \<le> a" by (simp add: box_eq_empty inner_Basis)
              with ab have "a = b" by simp
              then show "norm (f (Sup k) - f (Inf k)) = 0"
                using kab by (simp add: box_real)
            qed
          qed
          ultimately have "(\<Sum>k\<in>ds. norm (f (Sup k) - f (Inf k)))
                        + (\<Sum>k\<in>dt. norm (f (Sup k) - f (Inf k)))
                        \<le> vector_variation (s \<union> t) f"
            using has_bounded_variation_works(1)[OF fst]
            by auto
          then show ?thesis by linarith
        qed
      qed
      then show ?thesis by linarith
    qed
  qed
  then show ?thesis by linarith
qed

lemma finite_frontier_interval_real:
  fixes s :: "real set"
  assumes "is_interval s"
  shows "finite (frontier s) \<and> card (frontier s) \<le> 2"
proof (cases "interior s = {}")
  case True
  \<comment> \<open>A convex real set with empty interior is either empty or a singleton.\<close>
  have "s = {} \<or> (\<exists>a. s = {a})"
  proof (cases "s = {}")
    case True then show ?thesis by simp
  next
    case False
    then obtain x where xs: "x \<in> s" by auto
    have "s = {x}"
    proof (rule ccontr)
      assume "s \<noteq> {x}"
      then obtain y where ys: "y \<in> s" and yx: "y \<noteq> x" using xs by blast
      have convS: "convex s" using assms is_interval_convex by blast
      consider "x < y" | "y < x" using yx by linarith
      then obtain a b where ab: "a < b" "{a..b} \<subseteq> s"
      proof cases
        case 1
        with atMostAtLeast_subset_convex[OF convS xs ys] show ?thesis
          using that[of x y] by auto
      next
        case 2
        with atMostAtLeast_subset_convex[OF convS ys xs] show ?thesis
          using that[of y x] by auto
      qed
      then have "{a <..< b} \<subseteq> interior s"
        using interior_atLeastAtMost_real interior_mono by blast
      moreover have "{a <..< b} \<noteq> {}" using ab(1) by auto
      ultimately show False using True by auto
    qed
    then show ?thesis by auto
  qed
  then show "finite (frontier s) \<and> card (frontier s) \<le> 2" by (auto simp: frontier_def)
next
  \<comment> \<open>Interior is nonempty.  Any point of the frontier that lies strictly between
    two points of the closure must be in the interior (by convexity), so cannot
    be a frontier point.  This limits the frontier to at most 2 elements.\<close>
  case False
  then  obtain c where c_int: "c \<in> interior s" by blast
  have convS: "convex s" using assms is_interval_convex_1 by blast
  show ?thesis
  proof (rule ccontr)
    assume inf: "\<not> ?thesis"
    \<comment> \<open>An infinite set of reals contains at least 3 distinct points, and among any
      3 reals we can pick a middle one.\<close>
    then consider "infinite (frontier s)" | "card (frontier s) \<ge> 3"
      by linarith
    then obtain F where "finite F" "F \<subseteq> frontier s" "card F = 3"
      by (meson infinite_arbitrarily_large obtain_subset_with_card_n)
    define x where "x \<equiv> Min F"
    have \<open>x \<in> F\<close>
      using Min_in \<open>card F = 3\<close> \<open>finite F\<close> x_def by fastforce
    define y where "y \<equiv> Min (F - {x})"
    obtain "finite (F - {x})" "card (F - {x}) = 2"
      by (simp add: \<open>card F = 3\<close> \<open>finite F\<close> \<open>x \<in> F\<close>)
    then have y: \<open>y \<in> F - {x}\<close>
      by (metis card.empty eq_Min_iff y_def zero_neq_numeral)
    define z where "z \<equiv> Min (F - {x} - {y})"
    obtain "finite (F - {x} - {y})" "card (F - {x} - {y}) = 1"
      using \<open>card (F - {x}) = 2\<close> \<open>finite F\<close> \<open>y \<in> F - {x}\<close> by auto
    then have z: \<open>z \<in> F - {x} - {y}\<close>
      by (metis Min_in card.empty one_neq_zero z_def)
    have \<open>x<y\<close>
      by (metis Diff_iff Min_gr_iff Min_less_iff \<open>finite F\<close> \<open>y \<in> F - {x}\<close> insertCI
          linorder_neqE_linordered_idom x_def)
    have \<open>y<z\<close>
      by (metis Diff_iff Diff_insert2 \<open>finite (F - {x})\<close> \<open>z \<in> F - {x} - {y}\<close> atLeastAtMost_iff
          atLeastAtMost_singleton eq_Min_iff linorder_not_less y_def)
    \<comment> \<open>@{term y} lies in the open segment from some interior point to a closure point,
      hence in the interior — contradiction.\<close>
    have y_cls: "y \<in> closure s"
      using \<open>F \<subseteq> frontier s\<close> frontier_def y by auto
    have y_nint: "y \<notin> interior s"
      using \<open>F \<subseteq> frontier s\<close> frontier_def y by auto
    have x_cls: "x \<in> closure s"
      using \<open>F \<subseteq> frontier s\<close> \<open>x \<in> F\<close> frontier_def by auto
    have z_cls: "z \<in> closure s"
      using \<open>F \<subseteq> frontier s\<close> frontier_def z by auto
    \<comment> \<open>Use the interior point @{term c} and one of @{term x}, @{term z} to trap @{term y}.\<close>
    have "y \<in> interior s"
    proof (cases "c \<le> y")
      case True
      \<comment> \<open>@{term c} \<le> @{term y} < @{term z}, so @{term y} \<in> open_segment c z \<subseteq> interior s.\<close>
      have "c \<noteq> y" using c_int y_nint by auto
      then have "c < y" using True by auto
      have "open_segment c z \<subseteq> interior s"
        by (rule in_interior_closure_convex_segment[OF convS c_int z_cls])
      moreover have "y \<in> open_segment c z"
        using \<open>c < y\<close> \<open>y < z\<close> open_segment_eq_real_ivl by auto
      ultimately show "y \<in> interior s" by auto
    next
      case False
      \<comment> \<open>@{term x} < @{term y} < @{term c}, so @{term y} \<in> open_segment x c.
        But open_segment c x = open_segment x c \<subseteq> interior s.\<close>
      then have "y < c" by auto
      have "open_segment c x \<subseteq> interior s"
        by (rule in_interior_closure_convex_segment[OF convS c_int x_cls])
      moreover have "y \<in> open_segment c x"
        using \<open>x < y\<close> \<open>y < c\<close> open_segment_eq_real_ivl by auto
      ultimately show "y \<in> interior s" by auto
    qed
    with y_nint show False by contradiction
  qed
qed


lemma has_bounded_variation_on_closure:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "is_interval s" "has_bounded_variation_on f s"
  shows "has_bounded_variation_on f (closure s)"
proof -
  have fin_fr: "finite (frontier s)" and card2: "card (frontier s) \<le> 2"
    using finite_frontier_interval_real [OF \<open>is_interval s\<close>] by auto
  have "bounded (f ` closure s)"
  proof (rule bounded_subset)
    show "bounded (f ` (s \<union> frontier s))"
    proof -
      have "bounded (f ` s)"
      proof (cases "s = {}")
        case True then show ?thesis by simp
      next
        case False
        then obtain a where aS: "a \<in> s" by auto
        obtain K where K: "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
          (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> K"
          using assms(2) unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def
          by blast
        show ?thesis unfolding bounded_iff
        proof (intro exI[of _ "norm (f a) + K"] ballI)
          fix y assume "y \<in> f ` s"
          then obtain x where xS: "x \<in> s" and y_eq: "y = f x" by auto
          have sub: "{min a x..max a x} \<subseteq> s"
            using mem_is_interval_1_I[OF assms(1) aS xS]
            by (smt (verit, del_insts) aS assms(1) interval_cbox interval_subset_is_interval xS)
          have d: "{{min a x..max a x}} division_of {min a x..max a x}"
            by (intro division_ofI) auto
          have "norm (f x - f a) \<le> (\<Sum>k\<in>{{min a x..max a x}}. norm (f (Sup k) - f (Inf k)))"
            by simp (smt (verit) norm_minus_commute)
          also have "\<dots> \<le> K" using K[OF d sub] .
          finally show "norm y \<le> norm (f a) + K"
            by (metis add.commute diff_le_eq norm_triangle_ineq2 order_trans y_eq)
        qed
      qed
      moreover have "bounded (f ` frontier s)"
        using fin_fr by (intro finite_imp_bounded finite_imageI)
      ultimately show ?thesis
        by (simp add: image_Un bounded_Un)
    qed
  next
    show "f ` closure s \<subseteq> f ` (s \<union> frontier s)"
      by (simp add: closure_Un_frontier)
  qed
  then obtain B' where B'bd: "\<And>x. x \<in> closure s \<Longrightarrow> norm (f x) \<le> B'"
    unfolding bounded_iff by (auto simp: image_iff)
  define B where "B = max B' 0"
  have Bbd: "norm (f x) \<le> B" if "x \<in> closure s" for x 
    using B'bd[OF that] unfolding B_def by simp
  have Bge0: "B \<ge> 0" unfolding B_def by simp
  obtain K where K: "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> K"
    using assms(2) unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def
    by blast
  let ?B = "K + 8*B"
  show ?thesis
    unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def
  proof (intro exI strip)
    fix d t
    assume dt: "d division_of t \<and> t \<subseteq> closure s"
    then have \<open>finite d\<close>
      by blast
    define dd where "dd \<equiv> {k \<in> d. k \<subseteq> s} \<union> {k \<in> d. \<not> k \<subseteq> s}"
    have \<open>d = dd\<close>
      unfolding dd_def by blast
    have \<open>(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) 
        = (\<Sum>k\<in>{k \<in> d. k \<subseteq> s}. norm (f (Sup k) - f (Inf k))) + (\<Sum>k\<in>{k \<in> d. \<not> k \<subseteq> s}. norm (f (Sup k) - f (Inf k))) \<close>
      using \<open>finite d\<close> \<open>d = dd\<close> dd_def sum.union_disjoint
      by (metis (mono_tags, lifting) IntE equals0I finite_Un mem_Collect_eq) 
    also have \<open>... \<le> ?B\<close>
    proof (rule add_mono)
      show "(\<Sum>k | k \<in> d \<and> k \<subseteq> s. norm (f (Sup k) - f (Inf k))) \<le> K"
      proof (rule K)
        show "{k \<in> d. k \<subseteq> s} division_of \<Union> {k \<in> d. k \<subseteq> s}"
          by (metis (lifting) \<open>d = dd\<close> dd_def division_ofD(6) division_of_subset dt sup_ge1)
        show "\<Union>{k \<in> d. k \<subseteq> s} \<subseteq> s"
          by blast
      qed
      have "(\<Sum>k | k \<in> d \<and> \<not> k \<subseteq> s. norm (f (Sup k) - f (Inf k))) 
          = (\<Sum>k | k \<in> d \<and> \<not> k \<subseteq> s \<and> f (Sup k) \<noteq> f (Inf k). norm (f (Sup k) - f (Inf k)))"
        using \<open>finite d\<close> by (intro sum.mono_neutral_right) auto
      also have \<open>... \<le> real (card {k \<in> d. \<not> k \<subseteq> s \<and> f (Sup k) \<noteq> f (Inf k)}) * (2 * B)\<close>
      proof (rule sum_bounded_above)
        fix i :: "real set"
        assume "i \<in> {k \<in> d. \<not> k \<subseteq> s \<and> f (Sup k) \<noteq> f (Inf k)}"
        then have "i \<in> d" " \<not> i \<subseteq> s" "f (Sup i) \<noteq> f (Inf i)"
          by auto
        show "norm (f (Sup i) - f (Inf i)) \<le> 2 * B"
        proof -
          have "i \<subseteq> t" using division_ofD(2)[OF conjunct1[OF dt] \<open>i \<in> d\<close>] .
          then have isub: "i \<subseteq> closure s" using dt by blast
          have "i \<noteq> {}" using division_ofD(3)[OF conjunct1[OF dt] \<open>i \<in> d\<close>] .
          moreover obtain a b where iab: "i = cbox a b"
            using division_ofD(4)[OF conjunct1[OF dt] \<open>i \<in> d\<close>] by auto
          ultimately have ab: "a \<le> b" by (simp add: cbox_interval)
          then have "Sup i = b" "Inf i = a" 
            using iab by (simp_all add: cbox_interval cSup_atLeastAtMost cInf_atLeastAtMost)
          moreover have "a \<in> i" "b \<in> i" using iab ab by (auto simp: cbox_interval)
          ultimately have "Sup i \<in> closure s" "Inf i \<in> closure s"
            using isub by auto
          then have "norm (f (Sup i)) \<le> B" "norm (f (Inf i)) \<le> B"
            using Bbd by auto
          then show ?thesis
            using norm_triangle_ineq4[of "f (Sup i)" "f (Inf i)"] by linarith
        qed
      qed
      also have \<open>... \<le> 8 * B\<close>
      proof -
        have "card {k \<in> d. \<not> k \<subseteq> s \<and> f (Sup k) \<noteq> f (Inf k)} \<le> 4"
        proof -
          let ?S = "{k \<in> d. \<not> k \<subseteq> s \<and> f (Sup k) \<noteq> f (Inf k)}"
          define g where "g k = (if Inf k \<in> frontier s then (Inf k, True) else (Sup k, False))" for k
          have endpt_frontier: "Inf k \<in> frontier s \<or> Sup k \<in> frontier s" if "k \<in> ?S" for k
          proof -
            from that have kd: "k \<in> d" and nks: "\<not> k \<subseteq> s" and neq: "f (Sup k) \<noteq> f (Inf k)" by auto
            obtain a b where kab: "k = cbox a b" 
              using division_ofD(4)[OF conjunct1[OF dt] kd] by auto
            have kne: "k \<noteq> {}" using division_ofD(3)[OF conjunct1[OF dt] kd] .
            have kt: "k \<subseteq> closure s" using division_ofD(2)[OF conjunct1[OF dt] kd] dt by blast
            have ab: "a \<le> b" using kab kne by (simp add: cbox_interval)
            have inf_k: "Inf k = a" "Sup k = b" 
              using kab ab by (simp_all add: cbox_interval cSup_atLeastAtMost cInf_atLeastAtMost)
            have "a \<in> k" "b \<in> k" using kab ab by (auto simp: cbox_interval)
            then have "Inf k \<in> closure s" "Sup k \<in> closure s"
              using kt inf_k by auto
            moreover have "Inf k \<notin> s \<or> Sup k \<notin> s"
            proof (rule ccontr)
              assume "\<not> (Inf k \<notin> s \<or> Sup k \<notin> s)"
              then have "a \<in> s" "b \<in> s" using inf_k by auto
              then have "k \<subseteq> s"
                using assms(1) interval_subset_is_interval kab by blast
              with nks show False by contradiction
            qed
            ultimately show ?thesis
              using closure_Un_frontier by auto
          qed
          have g_img: "g ` ?S \<subseteq> frontier s \<times> UNIV"
            using endpt_frontier unfolding g_def by auto
          have g_inj: "inj_on g ?S"
          proof (rule inj_onI)
            fix k1 k2
            assume k1S: "k1 \<in> ?S" and k2S: "k2 \<in> ?S" and geq: "g k1 = g k2"
            from k1S have k1d: "k1 \<in> d" and ne1: "f (Sup k1) \<noteq> f (Inf k1)" by auto
            from k2S have k2d: "k2 \<in> d" and ne2: "f (Sup k2) \<noteq> f (Inf k2)" by auto
            obtain a1 b1 where k1ab: "k1 = cbox a1 b1" 
              using division_ofD(4)[OF conjunct1[OF dt] k1d] by auto
            obtain a2 b2 where k2ab: "k2 = cbox a2 b2" 
              using division_ofD(4)[OF conjunct1[OF dt] k2d] by auto
            have k1ne: "k1 \<noteq> {}" using division_ofD(3)[OF conjunct1[OF dt] k1d] .
            have k2ne: "k2 \<noteq> {}" using division_ofD(3)[OF conjunct1[OF dt] k2d] .
            have a1b1: "a1 \<le> b1" using k1ab k1ne by force
            have a2b2: "a2 \<le> b2" using k2ab k2ne by force
            have nondeg1: "a1 < b1" 
            proof (rule ccontr)
              assume "\<not> a1 < b1"
              then have "a1 = b1" using a1b1 by linarith
              then have "Sup k1 = Inf k1"
                using k1ab by (simp add: cbox_interval cSup_atLeastAtMost cInf_atLeastAtMost)
              with ne1 show False by simp
            qed
            have nondeg2: "a2 < b2" 
            proof (rule ccontr)
              assume "\<not> a2 < b2"
              then have "a2 = b2" using a2b2 by linarith
              then have "Sup k2 = Inf k2"
                using k2ab by (simp add: cbox_interval cSup_atLeastAtMost cInf_atLeastAtMost)
              with ne2 show False by simp
            qed
            show "k1 = k2"
            proof (cases "Inf k1 \<in> frontier s")
              case True
              then have "Inf k2 \<in> frontier s" and "Inf k1 = Inf k2"
                using geq unfolding g_def by (auto split: if_splits)
              then have "a1 = a2" using k1ab k2ab a1b1 a2b2 by force
              then have "interior k1 \<inter> interior k2 \<noteq> {}" if "k1 \<noteq> k2"
              proof -
                have "interior k1 = {a1<..<b1}" "interior k2 = {a2<..<b2}"
                  using k1ab k2ab by (simp_all add: cbox_interval interior_atLeastAtMost_real)
                moreover have "(a1 + min b1 b2) / 2 \<in> {a1<..<b1} \<inter> {a2<..<b2}"
                  using \<open>a1 = a2\<close> nondeg1 nondeg2 by (auto simp: field_simps min_def)
                ultimately show ?thesis by force
              qed
              then show "k1 = k2"
                using division_ofD(5)[OF conjunct1[OF dt] k1d k2d] by auto
            next
              case False
              then have "Inf k2 \<notin> frontier s" and "Sup k1 = Sup k2"
                using geq unfolding g_def by (auto split: if_splits)
              then have "b1 = b2" using k1ab k2ab a1b1 a2b2 
                by force
              then have "interior k1 \<inter> interior k2 \<noteq> {}" if "k1 \<noteq> k2"
              proof -
                have "interior k1 = {a1<..<b1}" "interior k2 = {a2<..<b2}"
                  using k1ab k2ab by (simp_all add: cbox_interval interior_atLeastAtMost_real)
                moreover have "(max a1 a2 + b1) / 2 \<in> {a1<..<b1} \<inter> {a2<..<b2}"
                  using \<open>b1 = b2\<close> nondeg1 nondeg2 by (auto simp: field_simps max_def)
                ultimately show ?thesis by force
              qed
              then show "k1 = k2"
                using division_ofD(5)[OF conjunct1[OF dt] k1d k2d] by auto
            qed
          qed
          have "card ?S \<le> card (frontier s \<times> (UNIV :: bool set))"
            using card_inj_on_le[OF g_inj g_img]
            using fin_fr finite by blast
          also have "... = card (frontier s) * 2"
            using card_cartesian_product card_UNIV_bool by metis
          also have "... \<le> 2 * 2" using card2 by auto
          finally show ?thesis by simp
        qed
        then have card_le: "real (card {k \<in> d. \<not> k \<subseteq> s \<and> f (Sup k) \<noteq> f (Inf k)}) \<le> 4"
          by auto
        show ?thesis
        proof -
          have "real (card {k \<in> d. \<not> k \<subseteq> s \<and> f (Sup k) \<noteq> f (Inf k)}) * (2 * B) \<le> 4 * (2 * B)"
            using card_le Bge0 by (intro mult_right_mono) auto
          then show ?thesis by simp
        qed
      qed
      finally show "(\<Sum>k | k \<in> d \<and> \<not> k \<subseteq> s. norm (f (Sup k) - f (Inf k))) \<le> 8 * B" .
    qed
    finally show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> ?B" .
  qed
qed

lemma has_bounded_variation_on_closure_eq:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "is_interval s"
  shows "has_bounded_variation_on f (closure s) \<longleftrightarrow> has_bounded_variation_on f s"
  by (meson assms closure_subset has_bounded_variation_on_closure has_bounded_variation_on_subset)

lemma has_bounded_set_variation:
  "has_bounded_setvariation_on f s \<and> set_variation s f \<le> c \<longleftrightarrow>
    (\<forall>d t. d division_of t \<and> t \<subseteq> s \<longrightarrow> (\<Sum>k\<in>d. norm (f k)) \<le> c)"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume L: ?L
  then have bdd: "has_bounded_setvariation_on f s" and le: "set_variation s f \<le> c"
    by auto
  show ?R
  proof (intro allI impI)
    fix d t assume "d division_of t \<and> t \<subseteq> s"
    then have "(\<Sum>k\<in>d. norm (f k)) \<le> set_variation s f"
      using has_bounded_setvariation_works(1)[OF bdd] by auto
    also have "\<dots> \<le> c" using le .
    finally show "(\<Sum>k\<in>d. norm (f k)) \<le> c" .
  qed
next
  assume R: ?R
  show ?L
  proof (intro conjI)
    show "has_bounded_setvariation_on f s"
      unfolding has_bounded_setvariation_on_def using R by blast
    show "set_variation s f \<le> c"
      using R by (intro has_bounded_setvariation_works(2))
        (auto simp: has_bounded_setvariation_on_def)
  qed
qed

lemma has_bounded_vector_variation_on_interval:
  "has_bounded_variation_on f {a..b} \<and> vector_variation {a..b} f \<le> c \<longleftrightarrow>
    (\<forall>d. d division_of {a..b} \<longrightarrow>
      (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> c)"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume L: ?L
  then have bdd: "has_bounded_variation_on f {a..b}"
    and le: "vector_variation {a..b} f \<le> c" by auto
  show ?R
  proof (intro allI impI)
    fix d assume "d division_of {a..b}"
    then have "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> vector_variation {a..b} f"
      using has_bounded_variation_works(1)[OF bdd] by auto
    also have "\<dots> \<le> c" using le .
    finally show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> c" .
  qed
next
  assume R: ?R
  show ?L
  proof (intro conjI)
    show bv: "has_bounded_variation_on f {a..b}"
      unfolding has_bounded_variation_on_interval using R by blast
    show "vector_variation {a..b} f \<le> c"
    proof (rule has_bounded_variation_works(2)[OF bv])
      fix d t assume "d division_of t" "t \<subseteq> {a..b}"
      then have div_d: "d division_of t" and sub: "t \<subseteq> {a..b}" by auto
      have "d division_of \<Union>d"
        using division_of_union_self[OF div_d] .
      moreover have "\<Union>d = t"
        using division_ofD(6)[OF div_d] .
      ultimately have "\<Union>d \<subseteq> cbox a b"
        using sub by (simp add: cbox_interval)
      then obtain q where dq: "d \<subseteq> q" and q_div: "q division_of cbox a b"
        using partial_division_extend_interval \<open>d division_of \<Union>d\<close> by blast
      have q_div': "q division_of {a..b}"
        using q_div by (simp add: cbox_interval)
      have fin_q: "finite q"
        using division_of_finite[OF q_div] .
      have "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> (\<Sum>k\<in>q. norm (f (Sup k) - f (Inf k)))"
        by (rule sum_mono2[OF fin_q dq]) auto
      also have "\<dots> \<le> c"
        using R q_div' by auto
      finally show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> c" .
    qed
  qed
qed

lemma has_bounded_vector_variation:
  "has_bounded_variation_on f s \<and> vector_variation s f \<le> c \<longleftrightarrow>
    (\<forall>d t. d division_of t \<and> t \<subseteq> s \<longrightarrow>
      (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> c)"
  unfolding has_bounded_variation_on_def vector_variation_def
  using has_bounded_set_variation .


lemma 
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and s t :: "real set"
  assumes "is_interval s" "is_interval t"
    "has_bounded_variation_on f s" "has_bounded_variation_on f t"
  shows has_bounded_variation_on_Un: "has_bounded_variation_on f (s \<union> t)" (is ?th1)
    and vector_variation_Un_le:
    "(s \<inter> t = {} \<Longrightarrow> s \<inter> closure t = {} \<and> t \<inter> closure s = {}) 
    \<Longrightarrow> vector_variation (s \<union> t) f \<le> vector_variation s f + vector_variation t f" (is "PROP ?th2")
proof -
  have combined: "has_bounded_variation_on f (s \<union> t) \<and> vector_variation (s \<union> t) f 
         \<le> vector_variation s f + vector_variation t f"
    if "is_interval s" and "is_interval t"
      and clo: "s \<inter> t = {} \<Longrightarrow> s \<inter> closure t = {} \<and> t \<inter> closure s = {}"
      and bv_fs: "has_bounded_variation_on f s"
      and bv_ft: "has_bounded_variation_on f t"
    for f :: "real \<Rightarrow> 'a" and s t
  proof (cases "s={} \<or> t={}")
    case True
    then show ?thesis
      using that vector_variation_pos_le [of f]
      by (metis Un_empty_left add.commute atLeastatMost_empty_iff2 le_add_same_cancel2
          sup_bot_right)
  next
    case False
    then obtain p q where "p \<in> s" and "q \<in> t"
       by blast
    show ?thesis
      unfolding has_bounded_vector_variation
    proof (intro strip)
      fix d u
      assume du: "d division_of u \<and> u \<subseteq> s \<union> t"
      have "\<exists>j k. j \<noteq> {} \<and> k \<noteq> {} \<and> (\<exists>a b. j = {a..b}) \<and> (\<exists>a b. k = {a..b})
                \<and> j \<subseteq> s \<and> k \<subseteq> t \<and> (j \<subseteq> i \<or> interior j = {}) \<and> (k \<subseteq> i \<or> interior k = {}) 
                \<and> norm (f (Sup i) - f (Inf i)) \<le> norm (f (Sup j) - f (Inf j)) + norm (f (Sup k) - f (Inf k))"
        if "i \<in> d" for i 
      proof -
        obtain a b where iab: "i = {a..b}" and ne: "{a..b} \<noteq> {}"
          by (metis \<open>i \<in> d\<close> box_real(2) division_ofD(3,4) du)
        then have ab: "a \<le> b"
          using atLeastatMost_empty_iff by blast
        then have "a \<in> {a..b}" "b \<in> {a..b}" using ab by auto
        have iSup: "Sup i = b" and iInf: "Inf i = a"
          using ab iab by auto
        have isub: "i \<subseteq> u" and usub: "u \<subseteq> s \<union> t"
          using du that division_ofD(2) by (blast, meson)
        then have ab_st: "{a,b} \<subseteq> s \<union> t"
          by (metis Un_insert_left Un_insert_right atLeastatMost_empty_iff2 ne
              empty_subsetI iab insert_subset ivl_disj_un_singleton(5,6) subset_iff)
        have one_in_each: ?thesis
          if aS: "a \<in> S" and bT: "b \<in> T" and ivS: "is_interval S" and ivT: "is_interval T"
            and st: "(S = s \<and> T = t) \<or> (S = t \<and> T = s)"
          for S T
        proof (cases "s \<inter> t = {}")
          case True
          \<comment> \<open>Separated case: connectedness contradiction\<close>
          have sep: "s \<inter> closure t = {} \<and> t \<inter> closure s = {}" using clo True by blast
          have sub: "{a..b} \<subseteq> s \<union> t" using isub usub iab by blast
          have o1: "open (- closure t)" and o2: "open (- closure s)"
            using open_Compl closed_closure by blast+
          have s_sub: "s \<subseteq> - closure t" and t_sub: "t \<subseteq> - closure s"
            using sep by blast+
          have "{a..b} \<subseteq> (- closure t) \<union> (- closure s)"
            using sub s_sub t_sub by blast
          moreover have "(- closure t) \<inter> (- closure s) \<inter> {a..b} = {}"
            using sub closure_subset by blast
          moreover have "(- closure t) \<inter> {a..b} \<noteq> {} \<and> (- closure s) \<inter> {a..b} \<noteq> {}"
            using aS bT st s_sub t_sub ab by auto
          ultimately show ?thesis
            by (meson connectedD connected_Icc o1 o2)
        next
          case False
          \<comment> \<open>Overlapping case: pick c \<in> s \<inter> t, split at c' = max a (min c b)\<close>
          obtain c where "c \<in> s" "c \<in> t" using False by blast
          with aS bT ivS ivT st
          have c': "max a (min c b) \<in> s \<and> max a (min c b) \<in> t \<and> max a (min c b) \<in> {a..b}"
            by (smt (verit) ab atLeastAtMost_iff max.absorb1 max.absorb2 mem_is_interval_1_I
                min_le_iff_disj)
          define c' where "c' = max a (min c b)"
          then have c'_s: "c' \<in> s" and c'_t: "c' \<in> t" and c'_ab: "a \<le> c'" "c' \<le> b"
            using c' by auto
          have lo_sub_S: "{a..c'} \<subseteq> S"
            using aS c'_s c'_t ivS st interval_subset_is_interval[of S a c']
            by (auto simp: box_real)
          have hi_sub_T: "{c'..b} \<subseteq> T"
            using bT c'_s c'_t ivT st interval_subset_is_interval[of T c' b]
            by (auto simp: box_real)
          have lo_sub_i: "{a..c'} \<subseteq> {a..b}" and hi_sub_i: "{c'..b} \<subseteq> {a..b}"
            using c'_ab ab by auto
          have tri: "norm (f b - f a) \<le> norm (f c' - f a) + norm (f b - f c')"
            by (simp add: order_trans [OF _ norm_triangle_ineq])
          show ?thesis using st
          proof
            assume st': "S = s \<and> T = t"
            show ?thesis
              apply (rule_tac x="{a..c'}" in exI, rule_tac x="{c'..b}" in exI)
              using c'_ab ab lo_sub_S hi_sub_T lo_sub_i hi_sub_i iab ne tri st'
              by (auto simp: iSup iInf)
          next
            assume st': "S = t \<and> T = s"
            show ?thesis
              apply (rule_tac x="{c'..b}" in exI, rule_tac x="{a..c'}" in exI)
              using c'_ab ab lo_sub_S hi_sub_T lo_sub_i hi_sub_i iab ne tri st'
              by (auto simp: iSup iInf)
          qed
        qed
        from ab_st consider "a \<in> s \<and> b \<in> s" | "a \<in> s \<and> b \<in> t" | "a \<in> t \<and> b \<in> s" | "a \<in> t \<and> b \<in> t"
          by blast
        then show ?thesis
        proof cases
          case 1 \<comment> \<open>Both endpoints in s\<close>
          show ?thesis
            apply (rule exI[where x="{a..b}"])
            apply (rule exI[where x="{q..q}"])
            using 1 ne \<open>q \<in> t\<close> iab ab \<open>is_interval s\<close> interval_subset_is_interval[of _ a b] 
            by (force simp: iSup iInf interior_atLeastAtMost_real)
        next
          case 2 \<comment> \<open>a \<in> s, b \<in> t\<close>
          then show ?thesis using one_in_each[where S=s and T=t] \<open>is_interval s\<close> \<open>is_interval t\<close> by blast
        next
          case 3 \<comment> \<open>a \<in> t, b \<in> s\<close>
          then show ?thesis using one_in_each[where S=t and T=s] \<open>is_interval s\<close> \<open>is_interval t\<close> by blast
        next
          case 4 \<comment> \<open>Both endpoints in t\<close>
          show ?thesis
            apply (rule exI[where x="{p..p}"])
            apply (rule exI[where x="{a..b}"])
            using 4 ne \<open>p \<in> s\<close> iab ab \<open>is_interval t\<close> interval_subset_is_interval[of _ a b] 
            by (force simp: iSup iInf interior_atLeastAtMost_real)
        qed
      qed
      then obtain L R where LR: "\<forall>i\<in>d. L i \<noteq> {} \<and> R i \<noteq> {} \<and> (\<exists>a b. L i = {a..b}) 
             \<and> (\<exists>a b. R i = {a..b}) \<and> L i \<subseteq> s \<and> R i \<subseteq> t \<and> (L i \<subseteq> i \<or> interior (L i) = {}) 
             \<and> (R i \<subseteq> i \<or> interior (R i) = {}) 
             \<and> norm (f (Sup i) - f (Inf i)) \<le> norm (f (Sup (L i)) - f (Inf (L i))) + norm (f (Sup (R i)) - f (Inf (R i)))"
        by metis
      have \<open>finite d\<close>
        using du by blast
      have div_sum_bound: "(\<Sum>k\<in>d. norm (f (Sup (g k)) - f (Inf (g k)))) \<le> vector_variation S f"
        if gne: "\<forall>i\<in>d. g i \<noteq> {}"
          and gcbox: "\<forall>i\<in>d. \<exists>a b. g i = {a..b}"
          and gsub: "\<forall>i\<in>d. g i \<subseteq> S"
          and gcontain: "\<forall>i\<in>d. g i \<subseteq> i \<or> interior (g i) = {}"
          and bvS: "has_bounded_variation_on f S"
        for g :: "real set \<Rightarrow> real set" and S
      proof -
        define d' where "d' = {k \<in> d. interior (g k) \<noteq> {}}"
        have fd': "finite d'" unfolding d'_def using \<open>finite d\<close> by auto
        have d'_sub: "d' \<subseteq> d" unfolding d'_def by auto
        have zero: "norm (f (Sup (g k)) - f (Inf (g k))) = 0" if "k \<in> d - d'" for k
        proof -
          from that have kd: "k \<in> d" and int: "interior (g k) = {}" by (auto simp: d'_def)
          from gcbox kd obtain a b where ab: "g k = {a..b}" by blast
          have ne: "g k \<noteq> {}" using gne kd by blast
          have "a = b"
            using ab int ne by auto
          then show "norm (f (Sup (g k)) - f (Inf (g k))) = 0"
            by (simp add: ab)
        qed
        have split_sum: "(\<Sum>k\<in>d. norm (f (Sup (g k)) - f (Inf (g k)))) 
                       = (\<Sum>k\<in>d'. norm (f (Sup (g k)) - f (Inf (g k))))"
        proof -
          have "(\<Sum>k\<in>d. norm (f (Sup (g k)) - f (Inf (g k)))) 
              = (\<Sum>k\<in>d'. norm (f (Sup (g k)) - f (Inf (g k)))) + (\<Sum>k\<in>d-d'. norm (f (Sup (g k)) - f (Inf (g k))))"
            using sum.subset_diff[OF d'_sub \<open>finite d\<close>]
            by (metis (mono_tags, lifting) add.commute)
          with zero show ?thesis by simp
        qed
        have inj_g: "inj_on g d'"
        proof (rule inj_onI)
          fix x y assume "x \<in> d'" "y \<in> d'" "g x = g y"
          then have \<section>: "x \<in> d" "y \<in> d" "interior (g x) \<noteq> {}" "interior (g y) \<noteq> {}"
            unfolding d'_def by auto
          then have "interior (g x) \<subseteq> interior x" "interior (g y) \<subseteq> interior y"
            using interior_mono gcontain by metis+
          then show "x = y"
            using du \<open>x \<in> d\<close> \<open>y \<in> d\<close> \<section>
            by (metis \<open>g x = g y\<close> division_ofD(5) inf.boundedI subset_empty)
        qed
        have gd'_div: "g ` d' division_of \<Union> (g ` d')"
          unfolding division_of_def
        proof (intro conjI ballI allI impI)
          fix K1 K2 assume "K1 \<in> g ` d'" "K2 \<in> g ` d'" "K1 \<noteq> K2"
          then obtain x1 x2 where k12: "x1 \<in> d'" "K1 = g x1" "x2 \<in> d'" "K2 = g x2" by auto
          then have "x1 \<noteq> x2" using \<open>K1 \<noteq> K2\<close> by auto
          have "x1 \<in> d" "x2 \<in> d" using k12 d'_sub by auto
          have "interior (g x1) \<noteq> {}" "interior (g x2) \<noteq> {}" using k12 d'_def by auto
          then have "g x1 \<subseteq> x1" "g x2 \<subseteq> x2" using gcontain \<open>x1 \<in> d\<close> \<open>x2 \<in> d\<close> by meson+
          then have "interior (g x1) \<subseteq> interior x1" "interior (g x2) \<subseteq> interior x2"
            using interior_mono by blast+
          moreover have "interior x1 \<inter> interior x2 = {}"
            using du \<open>x1 \<in> d\<close> \<open>x2 \<in> d\<close> \<open>x1 \<noteq> x2\<close> by (meson division_ofD(5))
          ultimately show "interior K1 \<inter> interior K2 = {}"
            using k12 by auto
        qed (use fd' gcbox gne in \<open>auto simp: d'_def\<close>)
        have gd'_sub_S: "\<Union> (g ` d') \<subseteq> S"
          using gsub bot.extremum by (fastforce simp: d'_def)
        have "(\<Sum>k\<in>d'. norm (f (Sup (g k)) - f (Inf (g k))))
            = (\<Sum>k \<in> g ` d'. norm (f (Sup k) - f (Inf k)))"
          by (metis (no_types, lifting) inj_g sum.reindex_cong)
        also have "\<dots> \<le> vector_variation S f"
          using has_bounded_variation_works(1)[OF bvS gd'_div gd'_sub_S] .
        finally show ?thesis using split_sum by simp
      qed
      have "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) 
          \<le> (\<Sum>k\<in>d. norm (f (Sup (L k)) - f (Inf (L k))) + norm (f (Sup (R k)) - f (Inf (R k))))"
        by (meson LR sum_mono)
      also have "\<dots> \<le> vector_variation s f + vector_variation t f"
        unfolding sum.distrib
      proof (intro add_mono)
        show "(\<Sum>k\<in>d. norm (f (Sup (L k)) - f (Inf (L k)))) \<le> vector_variation s f"
          using div_sum_bound[of L s] LR bv_fs by blast
      next
        show "(\<Sum>k\<in>d. norm (f (Sup (R k)) - f (Inf (R k)))) \<le> vector_variation t f"
          using div_sum_bound[of R t] LR bv_ft by blast
      qed

      finally show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> vector_variation s f + vector_variation t f" .
    qed
  qed
  show "has_bounded_variation_on f (s \<union> t)"
  proof -
    have "has_bounded_variation_on f (closure s \<union> closure t)"
      by (metis (lifting) ext assms closure_closure combined convex_closure
          has_bounded_variation_on_closure_eq inf_commute is_interval_convex_1)
    then have "has_bounded_variation_on f (closure s \<union> closure t)"
      using combined by blast
    then show ?thesis
      by (metis has_bounded_variation_on_subset closure_Un closure_subset)
  qed
  show "(s \<inter> t = {} \<Longrightarrow> s \<inter> closure t = {} \<and> t \<inter> closure s = {}) 
    \<Longrightarrow> vector_variation (s \<union> t) f \<le> vector_variation s f + vector_variation t f" 
      using combined assms  by blast
qed


text \<open>
  The key splitting lemma for vector variation on general interval sets,
  following HOL Light's @{text VECTOR_VARIATION_SPLIT}.
  Given an interval set @{term s} and a split point @{term a}, the variation
  over @{term s} equals the sum of variations over the left part
  @{term "s \<inter> {..a}"} and the right part @{term "s \<inter> {a..}"}.
\<close>

lemma vector_variation_split:
  assumes "is_interval s" "has_bounded_variation_on f s"
  shows "vector_variation (s \<inter> {..a}) f + vector_variation (s \<inter> {a..}) f =
         vector_variation s f"
proof -
  let ?L = "s \<inter> {..a}" and ?R = "s \<inter> {a..}"
  have split: "?L \<union> ?R = s"
    by auto
  have "vector_variation ?L f + vector_variation ?R f \<le> vector_variation s f"
  proof (rule vector_variation_le_Un[of f ?L ?R, unfolded split])
    show "has_bounded_variation_on f s"
      by (rule assms(2))
    show "interior ?L \<inter> interior ?R = {}"
      by force
  qed
  moreover have "vector_variation (?L \<union> ?R) f \<le> vector_variation ?L f + vector_variation ?R f"
  proof (rule vector_variation_Un_le)
    show "is_interval ?L" "is_interval ?R"
      by (auto intro: is_interval_Int assms(1) is_interval_ic is_interval_ci)
    show "has_bounded_variation_on f ?L" "has_bounded_variation_on f ?R"
      by (auto intro: has_bounded_variation_on_subset[OF assms(2)])
    show "?L \<inter> ?R = {} \<Longrightarrow> ?L \<inter> closure ?R = {} \<and> ?R \<inter> closure ?L = {}"
    proof -
      assume disj: "?L \<inter> ?R = {}"
      have "closure ?R \<subseteq> {a..}"
        by (rule closure_minimal) (auto intro: closed_real_atLeast)
      moreover have "closure ?L \<subseteq> {..a}"
        by (rule closure_minimal) (auto intro: closed_real_atMost)
      moreover have "?L \<inter> ?R = s \<inter> {a}" by auto
      moreover note disj
      ultimately show "?L \<inter> closure ?R = {} \<and> ?R \<inter> closure ?L = {}"
        by auto
    qed
  qed
  ultimately show ?thesis  
    by (simp add: split)
qed

lemma has_bounded_variation_on_split:
  assumes "is_interval s"
  shows "has_bounded_variation_on f s \<longleftrightarrow>
    has_bounded_variation_on f (s \<inter> {..a}) \<and>
    has_bounded_variation_on f (s \<inter> {a..})"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume bv: ?lhs
  then show ?rhs
    by (auto intro: has_bounded_variation_on_subset)
next
  assume ?rhs
  then have "has_bounded_variation_on f (s \<inter> {..a} \<union> s \<inter> {a..})"
    by (intro has_bounded_variation_on_Un is_interval_Int assms is_interval_ic is_interval_ci) auto
  moreover have "s \<inter> {..a} \<union> s \<inter> {a..} = s"
    by auto
  ultimately show ?lhs
    by simp
qed

lemma has_bounded_variation_on_combine:
  assumes "a \<le> c" "c \<le> b"
  shows "has_bounded_variation_on f {a..b} \<longleftrightarrow>
    has_bounded_variation_on f {a..c} \<and> has_bounded_variation_on f {c..b}"
proof -
  have *: "has_bounded_variation_on f {a..b} \<longleftrightarrow>
    has_bounded_variation_on f ({a..b} \<inter> {..c}) \<and>
    has_bounded_variation_on f ({a..b} \<inter> {c..})"
    by (rule has_bounded_variation_on_split) (simp add: is_interval_cc)
  show ?thesis
    using * assms by (simp add: Int_atLeastAtMostL1 Int_atLeastAtMostL2 min_absorb2 max_absorb2)
qed


lemma vector_variation_combine:
  assumes bv: "has_bounded_variation_on f {a..b}" and cab: "c \<in> {a..b}"
  shows "vector_variation {a..b} f = vector_variation {a..c} f + vector_variation {c..b} f"
proof -
  from cab have ac: "a \<le> c" and cb: "c \<le> b" by auto
  have *: "vector_variation ({a..b} \<inter> {..c}) f + vector_variation ({a..b} \<inter> {c..}) f =
           vector_variation {a..b} f"
    by (rule vector_variation_split[OF is_interval_cc bv])
  show ?thesis
    using * ac cb by (simp add: Int_atLeastAtMostL1 Int_atLeastAtMostL2 min_absorb2 max_absorb2)
qed

subsection \<open>Composition and monotonicity\<close>

lemma has_bounded_variation_compose_monotone:
  assumes bv: "has_bounded_variation_on g {f a..f b}"
    and mono: "mono_on {a..b} f"
  shows "has_bounded_variation_on (g \<circ> f) {a..b}" (is ?th1)
    and "vector_variation {a..b} (g \<circ> f) \<le> vector_variation {f a..f b} g" (is ?th2)
proof -
  have \<open>(\<Sum>k\<in>d. norm ((g \<circ> f) (Sup k) - (g \<circ> f) (Inf k))) \<le> vector_variation {f a..f b} g\<close>
    if "d division_of {a..b}" for d
  proof -
    define D where \<open>D \<equiv> (\<lambda>k. {f (Inf k)..f(Sup k)}) ` d\<close>
    have "finite d" using division_of_finite[OF that] .
    have kprops: "\<And>k. k \<in> d \<Longrightarrow> k \<subseteq> {a..b} \<and> k \<noteq> {} \<and> (\<exists>l u. k = cbox l u)"
      using division_ofD(2,3,4)[OF that] by auto
    have int_disj: "\<And>k1 k2. k1 \<in> d \<Longrightarrow> k2 \<in> d \<Longrightarrow> k1 \<noteq> k2 \<Longrightarrow> interior k1 \<inter> interior k2 = {}"
      using division_ofD(5)[OF that] by auto
    have k_interval: "\<And>k. k \<in> d \<Longrightarrow> \<exists>l u. l \<le> u \<and> k = {l..u} \<and> Inf k = l \<and> Sup k = u"
    proof -
      fix k assume "k \<in> d"
      then obtain l u where "k = cbox l u" "k \<noteq> {}" using kprops by blast
      then have "l \<le> u" by force
      then have "k = {l..u}" "Inf k = l" "Sup k = u"
        using \<open>k = cbox l u\<close> by (auto simp: cbox_interval)
      with \<open>l \<le> u\<close> show "\<exists>l u. l \<le> u \<and> k = {l..u} \<and> Inf k = l \<and> Sup k = u" by auto
    qed
    have mono_le: "\<And>x y. x \<in> {a..b} \<Longrightarrow> y \<in> {a..b} \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
      using mono by (simp add: monotone_on_def)
    have fInf_le_fSup: "\<And>k. k \<in> d \<Longrightarrow> f (Inf k) \<le> f (Sup k)"
    proof -
      fix k assume "k \<in> d"
      then obtain l u where lu: "l \<le> u" "k = {l..u}" "Inf k = l" "Sup k = u"
        using k_interval by blast
      have "k \<subseteq> {a..b}" using kprops \<open>k \<in> d\<close> by auto
      then have "l \<in> {a..b}" "u \<in> {a..b}" using lu by auto
      then show "f (Inf k) \<le> f (Sup k)" using lu mono_le by auto
    qed
    have \<open>D division_of \<Union>D\<close>
      unfolding division_of_def
    proof (intro conjI ballI allI impI)
      show "finite D" unfolding D_def using \<open>finite d\<close> by auto
    next
      fix K assume "K \<in> D"
      then obtain k where kd: "k \<in> d" and K_eq: "K = {f (Inf k)..f (Sup k)}"
        unfolding D_def by auto
      show "K \<subseteq> \<Union>D" using \<open>K \<in> D\<close> by auto
      show "K \<noteq> {}" using K_eq fInf_le_fSup[OF kd] by auto
      show "\<exists>a b. K = cbox a b" using K_eq by (auto simp: cbox_interval)
    next
      fix K1 K2 assume K1D: "K1 \<in> D" and K2D: "K2 \<in> D" and ne: "K1 \<noteq> K2"
      from K1D obtain k1 where k1d: "k1 \<in> d" and K1_eq: "K1 = {f (Inf k1)..f (Sup k1)}"
        unfolding D_def by auto
      from K2D obtain k2 where k2d: "k2 \<in> d" and K2_eq: "K2 = {f (Inf k2)..f (Sup k2)}"
        unfolding D_def by auto
      obtain l1 u1 where lu1: "l1 \<le> u1" "k1 = {l1..u1}" "Inf k1 = l1" "Sup k1 = u1"
        using k_interval[OF k1d] by blast
      obtain l2 u2 where lu2: "l2 \<le> u2" "k2 = {l2..u2}" "Inf k2 = l2" "Sup k2 = u2"
        using k_interval[OF k2d] by blast
      have k1_sub: "k1 \<subseteq> {a..b}" using kprops k1d by auto
      have k2_sub: "k2 \<subseteq> {a..b}" using kprops k2d by auto
      have l1a: "l1 \<in> {a..b}" "u1 \<in> {a..b}" using k1_sub lu1 by auto
      have l2a: "l2 \<in> {a..b}" "u2 \<in> {a..b}" using k2_sub lu2 by auto
      have fl1u1: "f l1 \<le> f u1" using mono_le l1a lu1(1) by auto
      have fl2u2: "f l2 \<le> f u2" using mono_le l2a lu2(1) by auto
      have k1_ne_k2: "k1 \<noteq> k2"
        using K1_eq K2_eq ne by blast
      have int_k1k2: "interior k1 \<inter> interior k2 = {}"
        using int_disj[OF k1d k2d k1_ne_k2] .
      show "interior K1 \<inter> interior K2 = {}"
      proof (rule ccontr)
        assume "interior K1 \<inter> interior K2 \<noteq> {}"
        then obtain y where y1: "y \<in> interior K1" and y2: "y \<in> interior K2" by auto
        have int_K1: "interior K1 = {f l1<..<f u1}"
          using K1_eq lu1 fl1u1 by (auto simp: interior_atLeastAtMost_real)
        then have y_in1: "f l1 < y" "y < f u1" using y1 by auto
        have int_K2: "interior K2 = {f l2<..<f u2}"
          using K2_eq lu2 fl2u2 by (auto simp: interior_atLeastAtMost_real)
        then have y_in2: "f l2 < y" "y < f u2" using y2 by auto
        have fl1_lt_fu1: "f l1 < f u1"
          using int_K1 y1 by auto
        have fl2_lt_fu2: "f l2 < f u2"
          using int_K2 y2 by auto
        have l1_lt_u1: "l1 < u1"
          using fl1_lt_fu1 lu1(1) by (cases "l1 = u1") auto
        have l2_lt_u2: "l2 < u2"
          using fl2_lt_fu2 lu2(1) by (cases "l2 = u2") auto
        have "l1 < u2"
        proof (rule ccontr)
          assume "\<not> l1 < u2"
          then have "u2 \<le> l1" by linarith
          then have "f u2 \<le> f l1" using mono_le l1a(1) l2a(2) by auto
          with y_in1(1) y_in2(2) show False by linarith
        qed
        moreover have "l2 < u1"
        proof (rule ccontr)
          assume "\<not> l2 < u1"
          then have "u1 \<le> l2" by linarith
          then have "f u1 \<le> f l2" using mono_le l2a(1) l1a(2) by auto
          with y_in2(1) y_in1(2) show False by linarith
        qed
        ultimately have "max l1 l2 < min u1 u2"
          using l1_lt_u1 l2_lt_u2 by auto
        then have "(max l1 l2 + min u1 u2) / 2 \<in> {l1<..<u1} \<inter> {l2<..<u2}"
          using l1_lt_u1 l2_lt_u2 by auto
        then have "(max l1 l2 + min u1 u2) / 2 \<in> interior k1 \<inter> interior k2"
          using lu1(2) lu2(2) by (simp add: interior_atLeastAtMost_real)
        with int_k1k2 show False by auto
      qed
    next
      show "\<Union>D = \<Union>D" ..
    qed
    moreover have \<open>\<Union>D \<subseteq> {f a..f b}\<close>
    proof
      fix x assume "x \<in> \<Union>D"
      then obtain K where KD: "K \<in> D" and xK: "x \<in> K" by auto
      from KD obtain k where kd: "k \<in> d" and K_eq: "K = {f (Inf k)..f (Sup k)}"
        unfolding D_def by auto
      obtain l u where lu: "l \<le> u" "k = {l..u}" "Inf k = l" "Sup k = u"
        using k_interval[OF kd] by blast
      have k_sub: "k \<subseteq> {a..b}" using kprops kd by auto
      then have la: "l \<in> {a..b}" "u \<in> {a..b}" using lu by auto
      have "f a \<le> f l" using mono_le la(1) by auto
      moreover have "f u \<le> f b" using mono_le la(2) by auto
      moreover have "x \<in> {f l..f u}" using xK K_eq lu by auto
      ultimately show "x \<in> {f a..f b}" by auto
    qed
    ultimately have *: \<open>(\<Sum>k\<in>D. norm (g (Sup k) - g (Inf k))) \<le> vector_variation {f a..f b} g\<close>
      using has_bounded_variation_works [OF bv] by auto
    have **: "norm (g (f (Sup x)) - g (f (Inf x))) = 0"
      if "x \<in> d" "y \<in> d" "x \<noteq> y" 
        and eq: "{f (Inf x)..f (Sup x)} = {f (Inf y)..f (Sup y)}"
      for x y
    proof -
      obtain l1 u1 where lu1: "l1 \<le> u1" "x = {l1..u1}" "Inf x = l1" "Sup x = u1"
        using k_interval[OF \<open>x \<in> d\<close>] by blast
      obtain l2 u2 where lu2: "l2 \<le> u2" "y = {l2..u2}" "Inf y = l2" "Sup y = u2"
        using k_interval[OF \<open>y \<in> d\<close>] by blast
      have x_sub: "x \<subseteq> {a..b}" using kprops \<open>x \<in> d\<close> by auto
      have y_sub: "y \<subseteq> {a..b}" using kprops \<open>y \<in> d\<close> by auto
      have la1: "l1 \<in> {a..b}" "u1 \<in> {a..b}" using x_sub lu1 by auto
      have la2: "l2 \<in> {a..b}" "u2 \<in> {a..b}" using y_sub lu2 by auto
      have fl1u1: "f l1 \<le> f u1" using fInf_le_fSup[OF \<open>x \<in> d\<close>] lu1 by simp
      have fl2u2: "f l2 \<le> f u2" using fInf_le_fSup[OF \<open>y \<in> d\<close>] lu2 by simp
      have eq': "{f l1..f u1} = {f l2..f u2}" using eq lu1 lu2 by simp
      have fl_eq: "f l1 = f l2" and fu_eq: "f u1 = f u2"
        using eq' fl1u1 fl2u2 by (auto simp: Icc_eq_Icc)
      have int_xy: "interior x \<inter> interior y = {}"
        using int_disj[OF \<open>x \<in> d\<close> \<open>y \<in> d\<close> \<open>x \<noteq> y\<close>] .
      have disj: "{l1<..<u1} \<inter> {l2<..<u2} = {}"
        using int_xy lu1(2) lu2(2) by (simp add: interior_atLeastAtMost_real)
      have "f l1 = f u1"
      proof (cases "u1 \<le> l2")
        case True
        then have "f u1 \<le> f l2" using mono_le la1(2) la2(1) by auto
        then show ?thesis using fl_eq fl1u1 by linarith
      next
        case False
        then have "l2 < u1" by linarith
        show ?thesis
        proof (cases "u2 \<le> l1")
          case True
          then have "f u2 \<le> f l1" using mono_le la2(2) la1(1) by auto
          then show ?thesis using fu_eq fl2u2 fl_eq by linarith
        next
          case False
          then have "l1 < u2" by linarith
          \<comment> \<open>Both l2 < u1 and l1 < u2, so the open intervals overlap — unless one is degenerate\<close>
          have "l1 = u1 \<or> l2 = u2"
          proof (rule ccontr)
            assume "\<not> (l1 = u1 \<or> l2 = u2)"
            then have "l1 < u1" "l2 < u2" using lu1(1) lu2(1) by linarith+
            then have "max l1 l2 < min u1 u2"
              using \<open>l2 < u1\<close> \<open>l1 < u2\<close> by auto
            then have "(max l1 l2 + min u1 u2) / 2 \<in> {l1<..<u1} \<inter> {l2<..<u2}"
              using \<open>l1 < u1\<close> \<open>l2 < u2\<close> by auto
            with disj show False by auto
          qed
          then show ?thesis
            using fl_eq fu_eq by fastforce
        qed
      qed
      then show ?thesis using lu1 lu2 by simp
    qed
    show ?thesis
    proof -
      let ?h = \<open>\<lambda>k. {f (Inf k)..f (Sup k)}\<close>
      let ?G = \<open>\<lambda>K. norm (g (Sup K) - g (Inf K))\<close>
      have D_eq: \<open>D = ?h ` d\<close> unfolding D_def ..
      have sup_h: \<open>Sup {f (Inf k)..f (Sup k)} = f (Sup k)\<close> if \<open>k \<in> d\<close> for k
        using fInf_le_fSup[OF that] by (simp add: cSup_atLeastAtMost)
      have inf_h: \<open>Inf {f (Inf k)..f (Sup k)} = f (Inf k)\<close> if \<open>k \<in> d\<close> for k
        using fInf_le_fSup[OF that] by (simp add: cInf_atLeastAtMost)
      have \<open>?G (?h x) = 0\<close> if \<open>x \<in> d\<close> \<open>y \<in> d\<close> \<open>x \<noteq> y\<close> \<open>?h x = ?h y\<close> for x y
        using ** fInf_le_fSup that by auto
      then have eq1: \<open>sum ?G D = sum (?G \<circ> ?h) d\<close>
        unfolding D_eq using \<open>finite d\<close> by (intro sum.reindex_nontrivial)
      have \<open>(?G \<circ> ?h) k = norm (g (f (Sup k)) - g (f (Inf k)))\<close> if \<open>k \<in> d\<close> for k
        by (simp add: o_def sup_h[OF that] inf_h[OF that])
      then have \<open>(\<Sum>k\<in>d. norm ((g \<circ> f) (Sup k) - (g \<circ> f) (Inf k))) = sum (?G \<circ> ?h) d\<close>
        by auto
      then show ?thesis using eq1 * by linarith
    qed
  qed
  then show ?th1 ?th2
    using has_bounded_vector_variation_on_interval by blast+
qed

lemma Lipschitz_imp_has_bounded_variation:
  assumes "bounded s"
    and "\<And>x y. x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> norm (f x - f y) \<le> B * norm (x - y)"
  shows "has_bounded_variation_on f s"
  unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def
proof -
  from assms(1) obtain R where R: "\<And>x. x \<in> s \<Longrightarrow> \<bar>x\<bar> \<le> R"
    unfolding bounded_real by auto
  have R_nonneg: "0 \<le> R" if "s \<noteq> {}" using that R by (auto intro: order_trans[OF abs_ge_zero])
  then have s_sub: "s \<subseteq> cbox (-R) R" using R
    by fastforce
  show "\<exists>M. \<forall>d t. d division_of t \<and> t \<subseteq> s \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> M"
  proof (intro exI[of _ "\<bar>B\<bar> * content (cbox (-R) R)"] allI impI)
    fix d t assume dt: "d division_of t \<and> t \<subseteq> s"
    then have div_d: "d division_of t" and sub: "t \<subseteq> s" by auto
    have fin_d: "finite d" using division_of_finite[OF div_d] .
    have union_d: "\<Union>d = t" using division_ofD(6)[OF div_d] .
    have div_union: "d division_of \<Union>d" using division_of_union_self[OF div_d] .
    have union_sub: "\<Union>d \<subseteq> cbox (-R) R" using sub s_sub union_d by auto
    obtain q where dq: "d \<subseteq> q" and q_div: "q division_of cbox (-R) R"
      using partial_division_extend_interval[OF div_union union_sub] by auto
    have fin_q: "finite q" using division_of_finite[OF q_div] .
    have "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> (\<Sum>k\<in>d. \<bar>B\<bar> * content k)"
    proof (rule sum_mono)
      fix k assume kd: "k \<in> d"
      from division_ofD(2,4)[OF div_d kd] obtain l u where
        k_eq: "k = cbox l u" and kne: "k \<noteq> {}"
        using dt kd by blast
      then have lu: "l \<le> u"
        by fastforce
      have "k \<subseteq> t" using kd union_d by auto
      then have ls: "l \<in> s" and us: "u \<in> s"
        using lu sub k_eq by (auto simp: cbox_interval)
      have "norm (f u - f l) \<le> B * norm (u - l)"
        using assms(2)[OF us ls] .
      also have "\<dots> = B * (u - l)" using lu by (simp add: real_norm_def)
      also have "\<dots> \<le> \<bar>B\<bar> * (u - l)" by (intro mult_right_mono) (use lu in auto)
      also have "\<dots> = \<bar>B\<bar> * content k"
        using lu k_eq by (simp add: cbox_interval)
      finally show "norm (f (Sup k) - f (Inf k)) \<le> \<bar>B\<bar> * content k"
        using lu k_eq by (simp add: cbox_interval)
    qed
    also have "\<dots> = \<bar>B\<bar> * (\<Sum>k\<in>d. content k)"
      by (simp add: sum_distrib_left)
    also have "\<dots> \<le> \<bar>B\<bar> * (\<Sum>k\<in>q. content k)"
      by (intro mult_left_mono sum_mono2[OF fin_q dq]) auto
    also have "(\<Sum>k\<in>q. content k) = content (cbox (-R) R)"
      using additive_content_division[OF q_div] .
    finally show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> \<bar>B\<bar> * content (cbox (-R) R)" .
  qed
qed

lemma Lipschitz_vector_variation_le:
  assumes bv: \<open>has_bounded_variation_on f {a..b}\<close>
    and R: \<open>\<forall>x y. x \<in> {a..b} \<longrightarrow> y \<in> {a..b} \<longrightarrow> norm (f x - f y) \<le> B * \<bar>x - y\<bar>\<close>
    and xab: \<open>x \<in> {a..b}\<close> and yab: \<open>y \<in> {a..b}\<close> and le: \<open>x \<le> y\<close>
  shows \<open>\<bar>vector_variation {a..x} f - vector_variation {a..y} f\<bar> \<le> B * \<bar>x - y\<bar>\<close>
proof -
  have bv_ay: \<open>has_bounded_variation_on f {a..y}\<close>
    using has_bounded_variation_on_subset[OF bv] yab by auto
  have x_in: \<open>x \<in> {a..y}\<close>
    using xab le by auto
  have combine: \<open>vector_variation {a..y} f =
      vector_variation {a..x} f + vector_variation {x..y} f\<close>
    using vector_variation_combine[OF bv_ay x_in] .
  have bv_xy: \<open>has_bounded_variation_on f {x..y}\<close>
    using has_bounded_variation_on_subset[OF bv] xab yab le by auto
  have vv_xy_le: \<open>vector_variation {x..y} f \<le> B * (y - x)\<close>
  proof (rule has_bounded_variation_works(2)[OF bv_xy])
    fix d t assume dt: \<open>d division_of t\<close> \<open>t \<subseteq> {x..y}\<close>
    show \<open>(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B * (y - x)\<close>
    proof -
      have fin_d: \<open>finite d\<close>
        using division_of_finite[OF dt(1)] .
      have \<open>(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> (\<Sum>k\<in>d. B * content k)\<close>
      proof (rule sum_mono)
        fix k assume kd: \<open>k \<in> d\<close>
        from division_ofD(2,4)[OF dt(1) kd] obtain l u where
          k_eq: \<open>k = cbox l u\<close> and kne: \<open>k \<noteq> {}\<close>
          by (metis cbox_division_memE dt(1) kd)
        then have lu: \<open>l \<le> u\<close> by fastforce
        have \<open>k \<subseteq> {x..y}\<close>
          using kd dt by blast
        then have ls: \<open>l \<in> {a..b}\<close> and us: \<open>u \<in> {a..b}\<close>
          using lu k_eq xab yab le by (auto simp: cbox_interval)
        have \<open>norm (f (Sup k) - f (Inf k)) = norm (f u - f l)\<close>
          using lu k_eq by (simp add: cbox_interval)
        also have \<open>\<dots> \<le> B * norm (u - l)\<close>
          using R us ls by auto
        also have \<open>\<dots> = B * (u - l)\<close>
          using lu by (simp add: real_norm_def)
        also have \<open>\<dots> = B * content k\<close>
          using lu k_eq by (simp add: cbox_interval)
        finally show \<open>norm (f (Sup k) - f (Inf k)) \<le> B * content k\<close> .
      qed
      also have \<section>: \<open>\<dots> = B * (\<Sum>k\<in>d. content k)\<close>
        by (simp add: sum_distrib_left)
      also have \<open>\<dots> \<le> B * (y - x)\<close>
      proof -
        have sum_le: \<open>(\<Sum>k\<in>d. content k) \<le> y - x\<close>
          by (metis le cbox_interval dt measure_lborel_Icc subadditive_content_division)
        show ?thesis
        proof (cases \<open>B \<ge> 0\<close>)
          case True
          then show ?thesis using sum_le by (intro mult_left_mono) auto
        next
          case False
          then have Bneg: \<open>B < 0\<close> by linarith
          have \<open>\<forall>k\<in>d. content k \<ge> 0\<close> by (simp add: content_nonneg)
          then have \<open>\<forall>k\<in>d. B * content k \<le> 0\<close>
            using Bneg by (simp add: mult_nonpos_nonneg)
          then have \<open>(\<Sum>k\<in>d. B * content k) \<le> 0\<close>
            using sum_nonpos by metis
          moreover have \<open>(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> (\<Sum>k\<in>d. B * content k)\<close>
            using \<open>(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> (\<Sum>k\<in>d. B * content k)\<close> .
          ultimately show ?thesis
            using Bneg le
            by (smt (verit) R \<section> diff_ge_0_iff_ge norm_ge_zero order.trans xab yab)
        qed
      qed
      finally show ?thesis .
    qed
  qed
  have vv_nonneg: \<open>vector_variation {x..y} f \<ge> 0\<close>
    using vector_variation_pos_le using bv_xy by blast
  have \<open>\<bar>vector_variation {a..x} f - vector_variation {a..y} f\<bar> =
        vector_variation {x..y} f\<close>
    using combine vv_nonneg by linarith
  also have \<open>\<dots> \<le> B * (y - x)\<close>
    using vv_xy_le .
  also have \<open>\<dots> = B * \<bar>x - y\<bar>\<close>
    using le by (simp add: abs_if)
  finally show ?thesis .
qed

lemma Lipschitz_vector_variation:
  assumes \<open>has_bounded_variation_on f {a..b}\<close>
  shows \<open>(\<forall>x y. x \<in> {a..b} \<longrightarrow> y \<in> {a..b} \<longrightarrow>
              \<bar>vector_variation {a..x} f - vector_variation {a..y} f\<bar> \<le> B * \<bar>x - y\<bar>)
     \<longleftrightarrow> (\<forall>x y. x \<in> {a..b} \<longrightarrow> y \<in> {a..b} \<longrightarrow>
              norm (f x - f y) \<le> B * \<bar>x - y\<bar>)\<close>
     (is "?L = ?R")
proof
  assume L: ?L
  have \<open>(\<forall>x y. x \<le> y \<longrightarrow> x \<in> {a..b} \<longrightarrow> y \<in> {a..b} \<longrightarrow>
              norm (f x - f y) \<le> B * \<bar>x - y\<bar>)\<close>
  proof (intro allI impI)
    fix x y :: real assume xy: \<open>x \<le> y\<close> \<open>x \<in> {a..b}\<close> \<open>y \<in> {a..b}\<close>
    have bv_ay: \<open>has_bounded_variation_on f {a..y}\<close>
      using has_bounded_variation_on_subset[OF assms] xy(3) by auto
    have x_in: \<open>x \<in> {a..y}\<close>
      using xy by auto
    have combine: \<open>vector_variation {a..y} f =
        vector_variation {a..x} f + vector_variation {x..y} f\<close>
      using vector_variation_combine[OF bv_ay x_in] .
    have bv_xy: \<open>has_bounded_variation_on f {x..y}\<close>
      using has_bounded_variation_on_subset[OF assms] xy by auto
    have \<open>norm (f x - f y) \<le> vector_variation {x..y} f\<close>
      using vector_variation_ge_norm_function[OF bv_xy] xy(1) by auto
    then show \<open>norm (f x - f y) \<le> B * \<bar>x - y\<bar>\<close>
      using combine L xy(2,3) by fastforce
  qed
  then show ?R
    by (metis abs_minus_commute linorder_linear norm_minus_commute)
next
  assume R: ?R
  show ?L
  proof (intro allI impI)
    fix x y :: real assume \<open>x \<in> {a..b}\<close> \<open>y \<in> {a..b}\<close>
    then show \<open>\<bar>vector_variation {a..x} f - vector_variation {a..y} f\<bar> \<le> B * \<bar>x - y\<bar>\<close>
      by (smt (verit, ccfv_SIG) Lipschitz_vector_variation_le R assms norm_minus_commute
          real_norm_def)
  qed
qed

lemma vector_variation_minus_function_monotone:
  assumes "has_bounded_variation_on f {a..b}" "x \<in> {a..b}" "y \<in> {a..b}" "x \<le> y"
  shows "norm (f y - f x) \<le> vector_variation {x..y} f"
    and "vector_variation {a..x} f - norm (f x - f a) \<le>
      vector_variation {a..y} f - norm (f y - f a)"
proof -
  have bv_xy: "has_bounded_variation_on f {x..y}"
    using has_bounded_variation_on_subset[OF assms(1)] assms(2,3) by auto
  show goal1: "norm (f y - f x) \<le> vector_variation {x..y} f"
    using vector_variation_ge_norm_function[OF bv_xy] assms(4) by auto
  have bv_ay: "has_bounded_variation_on f {a..y}"
    using has_bounded_variation_on_subset[OF assms(1)] assms(3) by auto
  have x_in_ay: "x \<in> {a..y}"
    using assms(2,4) by auto
  have combine: "vector_variation {a..y} f =
      vector_variation {a..x} f + vector_variation {x..y} f"
    using vector_variation_combine[OF bv_ay x_in_ay] .
  have "norm (f y - f a) \<le> norm (f y - f x) + norm (f x - f a)"
    using norm_triangle_ineq[of "f y - f x" "f x - f a"] by simp
  then have "norm (f y - f a) \<le> vector_variation {x..y} f + norm (f x - f a)"
    using goal1 by linarith
  then show "vector_variation {a..x} f - norm (f x - f a) \<le>
      vector_variation {a..y} f - norm (f y - f a)"
    using combine by linarith
qed


subsection \<open>Bounded variation implies bounded\<close>

lemma has_bounded_variation_on_imp_bounded:
  "has_bounded_variation_on f {a..b} \<Longrightarrow> bounded (f ` {a..b})"
proof -
  assume bv: "has_bounded_variation_on f {a..b}"
  then obtain M where M: "\<And>d. d division_of {a..b} \<Longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> M"
    unfolding has_bounded_variation_on_interval by auto
  show "bounded (f ` {a..b})"
  proof (cases "a \<le> b")
    case False then show ?thesis by auto
  next
    case True
    show ?thesis unfolding bounded_iff
    proof (intro exI ballI)
      fix y assume "y \<in> f ` {a..b}"
      then obtain x where xab: "x \<in> {a..b}" and y_eq: "y = f x" by auto
      then have ax: "a \<le> x" and xb: "x \<le> b" by auto
      \<comment> \<open>Use the division {{a..x}, {x..b}} to bound norm(f x - f a)\<close>
      have d: "{{a..x}, {x..b}} division_of {a..b}"
        using ax xb True by (intro division_ofI) auto
      have "(\<Sum>k\<in>{{a..x}, {x..b}}. norm (f (Sup k) - f (Inf k))) \<le> M"
        using M[OF d] .
      moreover have "norm (f x - f a) \<le> (\<Sum>k\<in>{{a..x}, {x..b}}. norm (f (Sup k) - f (Inf k)))"
        using ax xb member_le_sum division_of_finite[OF d]
        by (metis (no_types, lifting) cInf_atLeastAtMost cSup_atLeastAtMost insert_iff
            norm_ge_zero)
      ultimately have "norm (f x - f a) \<le> M" by linarith
      then have "norm y \<le> norm (f a) + M"
        by (metis add.commute diff_le_eq norm_triangle_ineq2 order_trans y_eq)
      then show "norm y \<le> norm (f a) + M" .
    qed
  qed
qed

subsection \<open>Increasing/decreasing functions\<close>

lemma division_telescope_eq:
  fixes g :: "real \<Rightarrow> real"
  assumes "d division_of {a..b}" and "a \<le> b"
  shows "(\<Sum>k\<in>d. (g (Sup k) - g (Inf k))) = g b - g a"
proof -
  define h where "h S = (if S = {} then 0 else g (Sup S) - g (Inf S))" for S :: "real set"
  have h_singleton: "h {x} = 0" for x unfolding h_def by simp
  have h_interval: "h {l..u} = g u - g l" if "l \<le> u" for l u
    unfolding h_def using that by auto
  have "operative (+) 0 h"
  proof (rule operative.intro)
    show "comm_monoid_set (+) (0::real)"
      using sum.comm_monoid_set_axioms .
  next
    show "operative_axioms (+) 0 h"
    proof (rule operative_axioms.intro)
      fix a' b' :: real
      assume "box a' b' = {}"
      then have "a' \<ge> b'" by (simp add: box_eq_empty)
      then show "h (cbox a' b') = 0"
      proof (cases "a' = b'")
        case True then show ?thesis unfolding h_def by (simp add: cbox_interval)
      next
        case False
        with \<open>a' \<ge> b'\<close> have "b' < a'" by linarith
        then have "cbox a' b' = {}" by (simp add: cbox_interval)
        then show ?thesis unfolding h_def by simp
      qed
    next
      fix a' b' c :: real and k :: real
      assume kB: "k \<in> Basis"
      then have k1: "k = 1" by (simp add: Basis_real_def)
      show "h (cbox a' b') = h (cbox a' b' \<inter> {x. x \<bullet> k \<le> c}) + h (cbox a' b' \<inter> {x. c \<le> x \<bullet> k})"
      proof (cases "a' \<le> b'")
        case ab: True
        have eq1: "cbox a' b' \<inter> {x. x \<bullet> k \<le> c} = {a'..min b' c}"
          using k1 ab by (auto simp: cbox_interval min_def)
        have eq2: "cbox a' b' \<inter> {x. c \<le> x \<bullet> k} = {max a' c..b'}"
          using k1 ab by (auto simp: cbox_interval max_def)
        have whole: "h (cbox a' b') = g b' - g a'"
          using h_interval[OF ab] by (simp add: cbox_interval)
        show ?thesis
        proof (cases "c < a'")
          case True
          then have "{a'..min b' c} = {}" by auto
          moreover have "max a' c = a'" using True by auto
          ultimately show ?thesis using eq1 eq2 whole h_def by auto
        next
          case False
          then have ca': "a' \<le> c" by linarith
          show ?thesis
          proof (cases "b' < c")
            case True
            then have "{max a' c..b'} = {}" by auto
            moreover have "min b' c = b'" using True by auto
            ultimately show ?thesis using eq1 eq2 whole h_def by auto
          next
            case False
            then have cb': "c \<le> b'" by linarith
            have minv: "min b' c = c" using cb' by auto
            have maxv: "max a' c = c" using ca' by auto
            have left: "h {a'..min b' c} = g c - g a'"
              using h_interval[of a' c] ca' minv by simp
            have right: "h {max a' c..b'} = g b' - g c"
              using h_interval[of c b'] cb' maxv by simp
            show ?thesis using eq1 eq2 whole left right by auto
          qed
        qed
      next
        case False
        then have "cbox a' b' = {}" by (auto simp: cbox_interval)
        moreover have "cbox a' b' \<inter> {x. x \<bullet> k \<le> c} = {}" using calculation by auto
        moreover have "cbox a' b' \<inter> {x. c \<le> x \<bullet> k} = {}" using calculation by auto
        ultimately show ?thesis unfolding h_def by simp
      qed
    qed
  qed
  then have eq: "sum h d = h (cbox a b)"
    using assms(1) operative.division[of "(+)" 0 h d a b]
    by (simp add: sum_def cbox_interval)
  have "h (cbox a b) = g b - g a"
    using h_interval[OF assms(2)] by (simp add: cbox_interval)
  moreover have "sum h d = (\<Sum>k\<in>d. (g (Sup k) - g (Inf k)))"
  proof (rule sum.cong)
    show "d = d" ..
  next
    fix k assume kd: "k \<in> d"
    then have "k \<noteq> {}" using division_ofD(3)[OF assms(1) kd] by auto
    then show "h k = g (Sup k) - g (Inf k)" unfolding h_def by auto
  qed
  ultimately show ?thesis using eq by simp
qed

lemma increasing_bounded_variation:
  fixes f :: "real \<Rightarrow> 'a::ordered_euclidean_space"
  assumes "mono_on {a..b} f"
  shows "has_bounded_variation_on f {a..b}"
  unfolding has_bounded_variation_on_interval
proof (intro exI allI impI)
  fix d assume div_d: "d division_of {a..b}"
  have fin_d: "finite d" using division_of_finite[OF div_d] .
  have "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> (\<Sum>k\<in>d. (\<Sum>i\<in>Basis. \<bar>(f (Sup k) - f (Inf k)) \<bullet> i\<bar>))"
    by (intro sum_mono norm_le_l1)
  also have "\<dots> = (\<Sum>i\<in>Basis. (\<Sum>k\<in>d. \<bar>(f (Sup k) - f (Inf k)) \<bullet> i\<bar>))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>i\<in>Basis. (\<Sum>k\<in>d. (f (Sup k) \<bullet> i - f (Inf k) \<bullet> i)))"
  proof (intro sum.cong refl)
    fix i::'a and k assume iBasis: "i \<in> Basis" and  kd: "k \<in> d" 
    from division_ofD(2,4)[OF div_d kd] obtain l u where
      k_eq: "k = cbox l u" and "k \<noteq> {}"
      by (metis div_d division_ofD(3) kd)
    then have lu: "l \<le> u"
      by force
    have "k \<subseteq> {a..b}" using division_ofD(2)[OF div_d kd] by auto
    then have "l \<in> {a..b}" "u \<in> {a..b}" using lu k_eq by (auto simp: cbox_interval)
    have "f l \<le> f u" 
      using assms \<open>l \<in> {a..b}\<close> \<open>u \<in> {a..b}\<close> lu by (simp add: monotone_on_def)
    then have "f l \<bullet> i \<le> f u \<bullet> i" using iBasis eucl_le by metis
    have "Inf k = l" "Sup k = u" using lu k_eq by (auto simp: cbox_interval)
    then show "\<bar>(f (Sup k) - f (Inf k)) \<bullet> i\<bar> = f (Sup k) \<bullet> i - f (Inf k) \<bullet> i"
      using \<open>f l \<bullet> i \<le> f u \<bullet> i\<close> by (simp add: inner_diff_left abs_of_nonneg)
  qed
  also have "\<dots> \<le> (\<Sum>i\<in>Basis. \<bar>(f b - f a) \<bullet> i\<bar>)"
  proof (intro sum_mono)
    fix i::'a assume iBasis: "i \<in> Basis"
    show "(\<Sum>k\<in>d. (f (Sup k) \<bullet> i - f (Inf k) \<bullet> i)) \<le> \<bar>(f b - f a) \<bullet> i\<bar>"
    proof (cases "d = {}")
      case True
      then show ?thesis by simp
    next
      case False
      then obtain k where "k \<in> d" by blast
      then have "k \<subseteq> {a..b}" "k \<noteq> {}" using division_ofD(2,3)[OF div_d] by auto
      then have ab: "a \<le> b" by auto
      have tele: "(\<Sum>k\<in>d. (f (Sup k) \<bullet> i - f (Inf k) \<bullet> i)) = f b \<bullet> i - f a \<bullet> i"
        using division_telescope_eq[OF div_d ab, of "\<lambda>x. f x \<bullet> i"] by simp
      also have "\<dots> \<le> \<bar>(f b - f a) \<bullet> i\<bar>" by (simp add: inner_diff_left)
      finally show ?thesis .
    qed
  qed
  also have "\<dots> \<le> (\<Sum>i::'a\<in>Basis. norm (f b - f a))"
    by (intro sum_mono) (auto simp: Basis_le_norm)
  also have "\<dots> = DIM('a) * norm (f b - f a)"
    by simp
  finally show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> DIM('a) * norm (f b - f a)" .
qed

lemma increasing_vector_variation:
  fixes f :: "real \<Rightarrow> real"
  assumes mono: "mono_on {a..b} f"
    and ab: "a \<le> b"
  shows "vector_variation {a..b} f = norm (f b - f a)"
proof (rule antisym)
  have bv: "has_bounded_variation_on f {a..b}"
    using increasing_bounded_variation[OF mono] .
  show "norm (f b - f a) \<le> vector_variation {a..b} f"
    using vector_variation_ge_norm_function[OF bv] ab by auto
  have vv_eq: "vector_variation {a..b} f =
    Sup {(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) | d. d division_of {a..b}}"
    using vector_variation_on_interval[OF bv] .
  have fa_le_fb: "f a \<le> f b" using mono ab
    by (simp add: monotone_on_def)
  show "vector_variation {a..b} f \<le> norm (f b - f a)"
    unfolding vv_eq
  proof (rule cSup_least)
    obtain p where "p division_of cbox a b" using elementary_interval by blast
    then show "{(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) | d. d division_of {a..b}} \<noteq> {}"
      by (auto simp: cbox_interval)
  next
    fix s assume "s \<in> {(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) | d. d division_of {a..b}}"
    then obtain d where div_d: "d division_of {a..b}"
      and s_eq: "s = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))" by auto
    have "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) = (\<Sum>k\<in>d. (f (Sup k) - f (Inf k)))"
    proof (rule sum.cong[OF refl])
      fix k assume kd: "k \<in> d"
      from division_ofD(2,4)[OF div_d kd] obtain l u where
        k_eq: "k = cbox l u" and "k \<noteq> {}"
        by (metis div_d division_ofD(3) kd)
      then have lu: "l \<le> u" by force
      have "k \<subseteq> {a..b}" using division_ofD(2)[OF div_d kd] by auto
      then have "l \<in> {a..b}" "u \<in> {a..b}" using lu k_eq by (auto simp: cbox_interval)
      then have "f l \<le> f u" 
        using mono lu by (simp add: monotone_on_def)
      have "Inf k = l" "Sup k = u" using lu k_eq by (auto simp: cbox_interval)
      then show "norm (f (Sup k) - f (Inf k)) = f (Sup k) - f (Inf k)"
        using \<open>f l \<le> f u\<close> by auto
    qed
    also have "\<dots> = f b - f a"
      using division_telescope_eq[OF div_d ab] .
    also have "\<dots> = norm (f b - f a)"
      using fa_le_fb by auto
    finally show "s \<le> norm (f b - f a)" using s_eq by simp
  qed
qed

subsection \<open>Darboux decomposition\<close>

text \<open>A function of bounded variation on an interval can be written as the difference
  of two monotone functions. This is the Darboux (or Jordan) decomposition theorem.\<close>

lemma has_bounded_variation_Darboux_gen:
  fixes f :: "real \<Rightarrow> real"
  assumes ivs: "is_interval s" and bv: "has_bounded_variation_on f s"
  shows "\<exists>g h. mono_on s g \<and> mono_on s h \<and> (\<forall>x. f x = g x - h x)"
proof -
  define g where "g x = vector_variation (s \<inter> {..x}) f" for x
  define h where "h x = vector_variation (s \<inter> {..x}) f - f x" for x
  have sub_xy: "{x..y} \<subseteq> s" if "x \<in> s" "y \<in> s" "x \<le> y" for x y
    using ivs that unfolding is_interval_def
    by (metis cbox_interval interval_subset_is_interval ivs)
  have g_mono: "mono_on s g"
    unfolding mono_on_def g_def
  proof (intro allI impI)
    fix x y assume "x \<in> s \<and> y \<in> s \<and> x \<le> y"
    then have xy: "x \<in> s" "y \<in> s" "x \<le> y" by auto
    have bv_sy: "has_bounded_variation_on f (s \<inter> {..y})"
      using has_bounded_variation_on_subset[OF bv] by auto
    have sub: "s \<inter> {..x} \<subseteq> s \<inter> {..y}" using xy(3) by auto
    show "vector_variation (s \<inter> {..x}) f \<le> vector_variation (s \<inter> {..y}) f"
      using bv_sy sub
      by (metis (mono_tags, lifting) dual_order.trans has_bounded_variation_on_subset
          has_bounded_variation_works)
  qed
  have h_mono: "mono_on s h"
    unfolding mono_on_def h_def
  proof (intro allI impI)
    fix x y assume "x \<in> s \<and> y \<in> s \<and> x \<le> y"
    then have xy: "x \<in> s" "y \<in> s" "x \<le> y" by auto
    have xy_sub: "{x..y} \<subseteq> s" by (rule sub_xy[OF xy])
    have bv_sy: "has_bounded_variation_on f (s \<inter> {..y})"
      using has_bounded_variation_on_subset[OF bv] by auto
    have iv_sy: "is_interval (s \<inter> {..y})"
      by (rule is_interval_Int[OF ivs is_interval_ic])
    have x_in: "x \<in> s \<inter> {..y}" using xy by auto
    have split: "vector_variation (s \<inter> {..y}) f =
      vector_variation (s \<inter> {..y} \<inter> {..x}) f + vector_variation (s \<inter> {..y} \<inter> {x..}) f"
      using vector_variation_split[OF iv_sy bv_sy, of x] by linarith
    have eq1: "s \<inter> {..y} \<inter> {..x} = s \<inter> {..x}" using xy(3) by auto
    have eq2: "s \<inter> {..y} \<inter> {x..} = s \<inter> {x..y}" using xy(3) by auto
    have "s \<inter> {x..y} = {x..y}" using xy_sub by auto
    then have eq3: "s \<inter> {..y} \<inter> {x..} = {x..y}" using eq2 by auto
    have bv_xy: "has_bounded_variation_on f {x..y}"
      using has_bounded_variation_on_subset[OF bv xy_sub] .
    have "f y - f x \<le> \<bar>f y - f x\<bar>" by (rule abs_ge_self)
    also have "\<dots> = norm (f y - f x)" by (simp add: real_norm_def)
    also have "\<dots> \<le> vector_variation {x..y} f"
      using vector_variation_ge_norm_function[OF bv_xy] xy(3) by auto
    also have "\<dots> = vector_variation (s \<inter> {..y}) f - vector_variation (s \<inter> {..x}) f"
      using split eq1 eq3 by simp
    finally show "vector_variation (s \<inter> {..x}) f - f x \<le> vector_variation (s \<inter> {..y}) f - f y"
      by linarith
  qed
  have eq: "\<forall>x. f x = g x - h x"
    unfolding g_def h_def by simp
  show ?thesis
    using g_mono h_mono eq by blast
qed

lemma has_bounded_variation_Darboux:
  fixes f :: "real \<Rightarrow> real"
  shows "has_bounded_variation_on f {a..b} \<longleftrightarrow>
    (\<exists>g h. mono_on {a..b} g \<and> mono_on {a..b} h \<and> (\<forall>x. f x = g x - h x))"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume bv: ?L
  define g where "g x = vector_variation {a..x} f" for x
  define h where "h x = vector_variation {a..x} f - f x" for x
  have g_mono: "mono_on {a..b} g"
    unfolding mono_on_def g_def
  proof (intro allI impI)
    fix x y assume "x \<in> {a..b} \<and> y \<in> {a..b} \<and> x \<le> y"
    then have xy: "x \<in> {a..b}" "y \<in> {a..b}" "x \<le> y" by auto
    have bv_ay: "has_bounded_variation_on f {a..y}"
      using has_bounded_variation_on_subset[OF bv] xy(2) by auto
    have sub: "{a..x} \<subseteq> {a..y}" using xy(3) by auto
    show "vector_variation {a..x} f \<le> vector_variation {a..y} f"
      by (rule vector_variation_monotone[OF bv_ay sub])
  qed
  have h_mono: "mono_on {a..b} h"
    unfolding mono_on_def h_def
  proof (intro allI impI)
    fix x y assume "x \<in> {a..b} \<and> y \<in> {a..b} \<and> x \<le> y"
    then have xy: "x \<in> {a..b}" "y \<in> {a..b}" "x \<le> y" by auto
    have "f y - f x \<le> \<bar>f y - f x\<bar>"
      by (rule abs_ge_self)
    also have "\<dots> = norm (f y - f x)"
      by (simp add: real_norm_def)
    also have "\<dots> \<le> vector_variation {x..y} f"
      using vector_variation_minus_function_monotone(1)[OF bv xy] .
    also have "\<dots> = vector_variation {a..y} f - vector_variation {a..x} f"
    proof -
      have bv_ay: "has_bounded_variation_on f {a..y}"
        using has_bounded_variation_on_subset[OF bv] xy(2) by auto
      have "x \<in> {a..y}" using xy by auto
      from vector_variation_combine[OF bv_ay this]
      show ?thesis by linarith
    qed
    finally show "vector_variation {a..x} f - f x \<le> vector_variation {a..y} f - f y"
      by linarith
  qed
  have eq: "\<forall>x. f x = g x - h x"
    unfolding g_def h_def by simp
  show ?R
    using g_mono h_mono eq by blast
next
  assume ?R
  then obtain g h where mono_g: "mono_on {a..b} g" and mono_h: "mono_on {a..b} h"
    and eq: "\<forall>x. f x = g x - h x" by blast
  have bv_g: "has_bounded_variation_on g {a..b}"
    by (rule increasing_bounded_variation[OF mono_g])
  have bv_h: "has_bounded_variation_on h {a..b}"
    by (rule increasing_bounded_variation[OF mono_h])
  have "f = (\<lambda>x. g x - h x)" using eq by auto
  then show ?L
    using has_bounded_variation_on_sub[OF bv_g bv_h] by simp
qed

lemma has_bounded_variation_Darboux_strict:
  fixes f :: "real \<Rightarrow> real"
  shows "has_bounded_variation_on f {a..b} \<longleftrightarrow>
    (\<exists>g h. strict_mono_on {a..b} g \<and> strict_mono_on {a..b} h \<and> (\<forall>x. f x = g x - h x))"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then obtain g h where mono_g: "mono_on {a..b} g" and mono_h: "mono_on {a..b} h"
    and eq: "\<forall>x. f x = g x - h x"
    using has_bounded_variation_Darboux by blast
  define g' where "g' x = g x + x" for x
  define h' where "h' x = h x + x" for x
  have sg: "strict_mono_on {a..b} g'"
    unfolding strict_mono_on_def g'_def
    by (metis add_le_less_mono linorder_not_less mono_g nle_le ord.mono_on_def)
  have sh: "strict_mono_on {a..b} h'"
    unfolding strict_mono_on_def h'_def
  proof clarify
    fix x y assume "x \<in> {a..b}" "y \<in> {a..b}" "x < y"
    then have "h x \<le> h y"
      using mono_h unfolding mono_on_def by (simp add: less_imp_le)
    then show "h x + x < h y + y"
      using \<open>x < y\<close> by linarith
  qed
  have "\<forall>x. f x = g' x - h' x"
    unfolding g'_def h'_def using eq by simp
  then show ?R using sg sh by blast
next
  assume ?R
  then obtain g h where sg: "strict_mono_on {a..b} g" and sh: "strict_mono_on {a..b} h"
    and eq: "\<forall>x. f x = g x - h x" by blast
  have mono_g: "mono_on {a..b} g"
    using sg unfolding strict_mono_on_def mono_on_def
    by (metis order_le_less)
  have mono_h: "mono_on {a..b} h"
    using sh unfolding strict_mono_on_def mono_on_def
    by (metis le_less)
  show ?L
    using has_bounded_variation_Darboux mono_g mono_h eq by blast
qed

subsection \<open>One-sided limits of monotone and BV functions\<close>

text \<open>A monotone increasing function on a closed interval has a left limit at every
point of that interval. The limit is the supremum of the function values to the left.\<close>

lemma increasing_left_limit:
  fixes f :: \<open>real \<Rightarrow> real\<close>
  assumes mono: \<open>mono_on {a..b} f\<close> and c_in: \<open>c \<in> {a..b}\<close>
  shows \<open>\<exists>l. (f \<longlongrightarrow> l) (at c within {a..c})\<close>
proof (cases \<open>c islimpt {a..c}\<close>)
  case False
  then have \<open>at c within {a..c} = bot\<close>
    by (simp add: trivial_limit_within)
  then show ?thesis
    using tendsto_bot by (intro exI) auto
next
  case True
  \<comment> \<open>In this case a < c, so there are points to the left\<close>
  have ac: \<open>a < c\<close>
  proof (rule ccontr)
    assume \<open>\<not> a < c\<close>
    then have \<open>{a..c} \<subseteq> {c}\<close> using c_in by auto
    then have \<open>finite {a..c}\<close> using finite_subset by blast
    then show False using True islimpt_finite by blast
  qed
  define S where \<open>S = f ` ({a..b} \<inter> {..<c})\<close>
  have S_ne: \<open>S \<noteq> {}\<close>
    unfolding S_def using ac c_in by force
  have S_bdd: \<open>bdd_above S\<close>
    unfolding S_def bdd_above_def using mono mono_onD
    by(intro exI[of _ \<open>f b\<close>] ballI, fastforce)

  define l where \<open>l = Sup S\<close>
  show ?thesis
  proof (intro exI tendstoI)
    fix e :: real assume \<open>e > 0\<close>
    \<comment> \<open>Find d with l - e < f d\<close>
    have \<open>l - e < l\<close> using \<open>e > 0\<close> by simp
    then obtain y where \<open>y \<in> S\<close> \<open>l - e < y\<close>
      using less_cSup_iff[OF S_ne S_bdd] l_def by blast
    then obtain d where d_in: \<open>d \<in> {a..b}\<close> and dc: \<open>d < c\<close> and fd: \<open>l - e < f d\<close>
      unfolding S_def by auto
    \<comment> \<open>For x \<in> (d, c) \<inter> {a..c}, we have |f x - l| < e\<close>
    show \<open>\<forall>\<^sub>F x in at c within {a..c}. dist (f x) l < e\<close>
      unfolding eventually_at_filter eventually_nhds
    proof (intro exI conjI ballI impI)
      show \<open>open {d<..}\<close> by auto
      show \<open>c \<in> {d<..}\<close> using dc by auto
      fix x assume \<open>x \<in> {d<..}\<close> \<open>x \<noteq> c\<close> \<open>x \<in> {a..c}\<close>
      then have xc: \<open>x < c\<close> and xab: \<open>x \<in> {a..b}\<close> and dx: \<open>d < x\<close>
        using c_in by auto
      have fx_le_l: \<open>f x \<le> l\<close>
        unfolding l_def
        by (intro cSup_upper[OF _ S_bdd]) (auto simp: S_def intro: xab xc)
      have \<open>f d \<le> f x\<close>
        using mono d_in xab dx unfolding mono_on_def by auto
      then have \<open>l - e < f x\<close> using fd by linarith
      then show \<open>dist (f x) l < e\<close>
        using fx_le_l unfolding dist_real_def by linarith
    qed
  qed
qed

lemma decreasing_left_limit:
  fixes f :: \<open>real \<Rightarrow> real\<close>
  assumes mono: \<open>antimono_on {a..b} f\<close> and c_in: \<open>c \<in> {a..b}\<close>
  shows \<open>\<exists>l. (f \<longlongrightarrow> l) (at c within {a..c})\<close>
proof -
  have \<open>mono_on {a..b} (\<lambda>x. - f x)\<close>
    using mono unfolding mono_on_def monotone_on_def by auto
  from increasing_left_limit[OF this c_in]
  obtain l where \<open>((\<lambda>x. - f x) \<longlongrightarrow> l) (at c within {a..c})\<close> by blast
  then have \<open>(f \<longlongrightarrow> - l) (at c within {a..c})\<close>
    by (rule tendsto_minus_cancel[where a=\<open>- l\<close>, simplified])
  then show ?thesis by blast
qed

lemma increasing_right_limit:
  fixes f :: \<open>real \<Rightarrow> real\<close>
  assumes mono: \<open>mono_on {a..b} f\<close> and c_in: \<open>c \<in> {a..b}\<close>
  shows \<open>\<exists>l. (f \<longlongrightarrow> l) (at c within {c..b})\<close>
proof (cases \<open>c islimpt {c..b}\<close>)
  case False
  then have \<open>at c within {c..b} = bot\<close>
    by (simp add: trivial_limit_within)
  then show ?thesis
    using tendsto_bot by (intro exI) auto
next
  case True
  have cb: \<open>c < b\<close>
  proof (rule ccontr)
    assume \<open>\<not> c < b\<close>
    then have \<open>{c..b} \<subseteq> {c}\<close> using c_in by auto
    then have \<open>finite {c..b}\<close> using finite_subset by blast
    then show False using True islimpt_finite by blast
  qed
  define S where \<open>S = f ` ({a..b} \<inter> {c<..})\<close>
  have S_ne: \<open>S \<noteq> {}\<close>
  proof -
    have \<open>b \<in> {a..b} \<inter> {c<..}\<close> using cb c_in by auto
    then show ?thesis unfolding S_def by blast
  qed
  have S_bdd: \<open>bdd_below S\<close>
  proof -
    have \<open>f a \<le> f x\<close> if \<open>x \<in> {a..b}\<close> for x
      using mono_onD[OF mono] that c_in by auto
    then show ?thesis unfolding S_def bdd_below_def by (intro exI[of _ \<open>f a\<close>]) auto
  qed
  define l where \<open>l = Inf S\<close>
  show ?thesis
  proof (intro exI tendstoI)
    fix e :: real assume \<open>e > 0\<close>
    have \<open>l < l + e\<close> using \<open>e > 0\<close> by simp
    then obtain y where \<open>y \<in> S\<close> \<open>y < l + e\<close>
      using cInf_less_iff[OF S_ne S_bdd] l_def by blast
    then obtain d where d_in: \<open>d \<in> {a..b}\<close> and dc: \<open>c < d\<close> and fd: \<open>f d < l + e\<close>
      unfolding S_def by auto
    show \<open>\<forall>\<^sub>F x in at c within {c..b}. dist (f x) l < e\<close>
      unfolding eventually_at_filter eventually_nhds
    proof (intro exI conjI ballI impI)
      show \<open>open {..<d}\<close> by auto
      show \<open>c \<in> {..<d}\<close> using dc by auto
      fix x assume \<open>x \<in> {..<d}\<close> \<open>x \<noteq> c\<close> \<open>x \<in> {c..b}\<close>
      then have xc: \<open>c < x\<close> and xab: \<open>x \<in> {a..b}\<close> and xd: \<open>x < d\<close>
        using c_in by auto
      have l_le_fx: \<open>l \<le> f x\<close>
        unfolding l_def
        by (intro cInf_lower[OF _ S_bdd]) (auto simp: S_def intro: xab xc)
      have \<open>f x \<le> f d\<close>
        using mono d_in xab xd unfolding mono_on_def by auto
      then have \<open>f x < l + e\<close> using fd by linarith
      then show \<open>dist (f x) l < e\<close>
        using l_le_fx unfolding dist_real_def by linarith
    qed
  qed
qed


lemma decreasing_right_limit:
  fixes f :: \<open>real \<Rightarrow> real\<close>
  assumes mono: \<open>antimono_on {a..b} f\<close> and c_in: \<open>c \<in> {a..b}\<close>
  shows \<open>\<exists>l. (f \<longlongrightarrow> l) (at c within {c..b})\<close>
proof -
  have \<open>mono_on {a..b} (\<lambda>x. - f x)\<close>
    using mono unfolding mono_on_def monotone_on_def by auto
  from increasing_right_limit[OF this c_in]
  obtain l where \<open>((\<lambda>x. - f x) \<longlongrightarrow> l) (at c within {c..b})\<close> by blast
  then have \<open>(f \<longlongrightarrow> - l) (at c within {c..b})\<close>
    by (rule tendsto_minus_cancel[where a=\<open>- l\<close>, simplified])
  then show ?thesis by blast
qed


lemma has_bounded_variation_left_limit:
  fixes f :: \<open>real \<Rightarrow> real\<close>
  assumes bv: \<open>has_bounded_variation_on f {a..b}\<close> and c_in: \<open>c \<in> {a..b}\<close>
  shows \<open>\<exists>l. (f \<longlongrightarrow> l) (at c within {a..c})\<close>
proof -
  from bv obtain g h where mono_g: \<open>mono_on {a..b} g\<close> and mono_h: \<open>mono_on {a..b} h\<close>
    and eq: \<open>\<forall>x. f x = g x - h x\<close>
    using has_bounded_variation_Darboux by blast
  from increasing_left_limit[OF mono_g c_in]
  obtain l1 where l1: \<open>(g \<longlongrightarrow> l1) (at c within {a..c})\<close> by blast
  from increasing_left_limit[OF mono_h c_in]
  obtain l2 where l2: \<open>(h \<longlongrightarrow> l2) (at c within {a..c})\<close> by blast
  have \<open>(f \<longlongrightarrow> l1 - l2) (at c within {a..c})\<close>
  proof (rule Lim_transform_eventually[OF tendsto_diff[OF l1 l2]])
    show \<open>\<forall>\<^sub>F x in at c within {a..c}. g x - h x = f x\<close>
      using eq by (intro always_eventually) auto
  qed
  then show ?thesis by blast
qed

lemma has_bounded_variation_right_limit:
  fixes f :: \<open>real \<Rightarrow> real\<close>
  assumes bv: \<open>has_bounded_variation_on f {a..b}\<close> and c_in: \<open>c \<in> {a..b}\<close>
  shows \<open>\<exists>l. (f \<longlongrightarrow> l) (at c within {c..b})\<close>
proof -
  from bv obtain g h where mono_g: \<open>mono_on {a..b} g\<close> and mono_h: \<open>mono_on {a..b} h\<close>
    and eq: \<open>\<forall>x. f x = g x - h x\<close>
    using has_bounded_variation_Darboux by blast
  from increasing_right_limit[OF mono_g c_in]
  obtain l1 where l1: \<open>(g \<longlongrightarrow> l1) (at c within {c..b})\<close> by blast
  from increasing_right_limit[OF mono_h c_in]
  obtain l2 where l2: \<open>(h \<longlongrightarrow> l2) (at c within {c..b})\<close> by blast
  have \<open>(f \<longlongrightarrow> l1 - l2) (at c within {c..b})\<close>
  proof (rule Lim_transform_eventually[OF tendsto_diff[OF l1 l2]])
    show \<open>\<forall>\<^sub>F x in at c within {c..b}. g x - h x = f x\<close>
      using eq by (intro always_eventually) auto
  qed
  then show ?thesis by blast
qed



subsection \<open>Continuity of vector variation\<close>

lemma continuous_vector_variation_left_1:
  fixes f :: \<open>real \<Rightarrow> real\<close>
  assumes \<open>has_bounded_variation_on f {a..b}\<close> \<open>c \<in> {a..b}\<close>
  shows \<open>continuous (at c within {a..c}) (\<lambda>x. vector_variation {a..x} f) \<longleftrightarrow>
         continuous (at c within {a..c}) f\<close>   (is \<open>?L = ?R  \<close>)
proof
  assume L: ?L
  show ?R
  proof -
    from assms have ac: \<open>a \<le> c\<close> and cb: \<open>c \<le> b\<close> by auto
    have bv_ac: \<open>has_bounded_variation_on f {a..c}\<close>
      using has_bounded_variation_on_subset[OF assms(1)] assms(2) by auto
    \<comment> \<open>L gives tendsto of vv\<close>
    from L have vv_tend: \<open>((\<lambda>x. vector_variation {a..x} f) \<longlongrightarrow> vector_variation {a..c} f) (at c within {a..c})\<close>
      by (simp add: continuous_within)
    \<comment> \<open>Hence the difference tends to 0\<close>
    have diff_tend: \<open>((\<lambda>x. vector_variation {a..c} f - vector_variation {a..x} f) \<longlongrightarrow> 0) (at c within {a..c})\<close>
      using tendsto_diff[OF tendsto_const vv_tend] by (metis diff_self)
    \<comment> \<open>The norm bound holds eventually\<close>
    have bound: \<open>\<forall>\<^sub>F x in at c within {a..c}. norm (f x - f c) \<le> vector_variation {a..c} f - vector_variation {a..x} f\<close>
    proof (unfold at_within_def eventually_inf_principal, rule always_eventually, rule allI, rule impI)
      fix x assume xS: \<open>x \<in> {a..c} - {c}\<close>
      then have xac: \<open>x \<in> {a..c}\<close> and xc: \<open>x \<noteq> c\<close> by auto
      then have xle: \<open>x \<le> c\<close> by auto
      have bv_xc: \<open>has_bounded_variation_on f {x..c}\<close>
        using has_bounded_variation_on_subset[OF bv_ac] xac by auto
      have \<open>norm (f x - f c) \<le> vector_variation {x..c} f\<close>
        using vector_variation_ge_norm_function[OF bv_xc] xac by auto
      also have \<open>\<dots> = vector_variation {a..c} f - vector_variation {a..x} f\<close>
        using vector_variation_combine[OF bv_ac xac] by linarith
      finally show \<open>norm (f x - f c) \<le> vector_variation {a..c} f - vector_variation {a..x} f\<close> .
    qed
    \<comment> \<open>By null comparison\<close>
    have \<open>((\<lambda>x. f x - f c) \<longlongrightarrow> 0) (at c within {a..c})\<close>
      by (rule Lim_null_comparison[OF bound diff_tend])
    then show ?R
      by (simp add: continuous_within LIM_zero_iff)
  qed
next
  assume R: ?R
  show ?L
  proof (cases \<open>c islimpt {a..c}\<close>)
    case False
    then show ?thesis
      using trivial_limit_within continuous_bot by metis
  next
    case True
    \<comment> \<open>Darboux decomposition: $f = g - h$ with $g$, $h$ monotone\<close>
    from assms(1) obtain g h where
      mono_g: \<open>mono_on {a..b} g\<close> and mono_h: \<open>mono_on {a..b} h\<close>
      and eq: \<open>\<And>x. f x = g x - h x\<close>
      using has_bounded_variation_Darboux[of f a b] by auto
    \<comment> \<open>Left limits of g and h at c exist by increasing_left_limit\<close>
    obtain gc where gc: \<open>(g \<longlongrightarrow> gc) (at c within {a..c})\<close>
      using increasing_left_limit[OF mono_g assms(2)] by auto
    obtain hc where hc: \<open>(h \<longlongrightarrow> hc) (at c within {a..c})\<close>
      using increasing_left_limit[OF mono_h assms(2)] by auto
    define k where "k \<equiv> gc - g c"
    have \<open>k = hc - h c\<close>
    proof -
      have \<open>(f \<longlongrightarrow> gc - hc) (at c within {a..c})\<close>
        by (metis (lifting) ext eq gc hc tendsto_diff)
      moreover have \<open>(f \<longlongrightarrow> f c) (at c within {a..c})\<close>
        using R by (simp add: continuous_within)
      moreover have \<open>at c within {a..c} \<noteq> bot\<close>
        using True trivial_limit_within by blast
      ultimately have \<open>f c = gc - hc\<close>
        using tendsto_unique by blast
      then show ?thesis unfolding k_def eq by algebra
    qed
    define g' where \<open>g' \<equiv> \<lambda>x. if c \<le> x then g(x) + k else g(x)\<close>
    define h' where \<open>h' \<equiv> \<lambda>x. if c \<le> x then h(x) + k else h(x)\<close>
    have not_bot: \<open>at c within {a..c} \<noteq> bot\<close>
      using True trivial_limit_within by blast
    \<comment> \<open>A monotone function shifted by k at c stays monotone on {a..c}\<close>
    have mono_shift: \<open>mono_on {a..c} (\<lambda>x. if c \<le> x then \<phi> x + k else \<phi> x)\<close>
      if mono_\<phi>: \<open>mono_on {a..b} \<phi>\<close> and lim_\<phi>: \<open>(\<phi> \<longlongrightarrow> \<phi>c) (at c within {a..c})\<close>
        and k_eq: \<open>k = \<phi>c - \<phi> c\<close> for \<phi> \<phi>c
    proof (unfold mono_on_def, intro allI impI, elim conjE)
      fix r s assume rs: \<open>r \<in> {a..c}\<close> \<open>s \<in> {a..c}\<close> \<open>r \<le> s\<close>
      have \<phi>_le_\<phi>c: \<open>\<phi> x \<le> \<phi>c\<close> if \<open>x \<in> {a..c}\<close> \<open>x < c\<close> for x
      proof (rule tendsto_lowerbound[OF lim_\<phi> _ not_bot])
        show \<open>\<forall>\<^sub>F y in at c within {a..c}. \<phi> x \<le> \<phi> y\<close>
          unfolding eventually_at_filter
        proof (rule eventually_nhds_metric[THEN iffD2], rule exI[of _ \<open>c - x\<close>], intro conjI allI impI)
          show \<open>0 < c - x\<close> using that by simp
        next
          fix y assume dy: \<open>dist y c < c - x\<close> and yc: \<open>y \<noteq> c\<close> and yac: \<open>y \<in> {a..c}\<close>
          then have \<open>y \<in> {a..b}\<close> using assms(2) by auto
          have \<open>x \<in> {a..b}\<close> using that assms(2) by auto
          have \<open>x \<le> y\<close> using dy by (auto simp: dist_real_def)
          show \<open>\<phi> x \<le> \<phi> y\<close>
            using mono_onD[OF mono_\<phi> \<open>x \<in> {a..b}\<close> \<open>y \<in> {a..b}\<close> \<open>x \<le> y\<close>] .
        qed
      qed
      show \<open>(if c \<le> r then \<phi> r + k else \<phi> r) \<le> (if c \<le> s then \<phi> s + k else \<phi> s)\<close>
      proof (cases \<open>s < c\<close>)
        case True
        then show ?thesis
          using mono_onD[OF mono_\<phi>] rs assms(2) by auto
      next
        case False
        then show ?thesis
          using \<phi>_le_\<phi>c rs k_eq by auto
      qed
    qed
    have mono_g': \<open>mono_on {a..c} g'\<close>
      unfolding g'_def using mono_shift[OF mono_g gc] k_def by simp
    have mono_h': \<open>mono_on {a..c} h'\<close>
      unfolding h'_def using mono_shift[OF mono_h hc \<open>k = hc - h c\<close>] .
    have \<open>f = (\<lambda>x. g' x - h' x)\<close>
      by (force simp: eq g'_def h'_def)
    show ?thesis
    proof -
      have ac: \<open>a \<le> c\<close> using assms(2) by auto
      have bv_ac: \<open>has_bounded_variation_on f {a..c}\<close>
        using has_bounded_variation_on_subset[OF assms(1)] assms(2) by auto
      \<comment> \<open>A shifted function is continuous at c when the original has the matching left limit\<close>
      have cont_shift: \<open>((\<lambda>x. if c \<le> x then \<phi> x + k else \<phi> x) \<longlongrightarrow>
                        (if c \<le> c then \<phi> c + k else \<phi> c)) (at c within {a..c})\<close>
        if \<open>(\<phi> \<longlongrightarrow> \<phi>c) (at c within {a..c})\<close> \<open>k = \<phi>c - \<phi> c\<close> for \<phi> \<phi>c
      proof -
        have \<open>\<forall>\<^sub>F x in at c within {a..c}. (if c \<le> x then \<phi> x + k else \<phi> x) = \<phi> x\<close>
          unfolding eventually_at_filter by auto
        then have \<open>((\<lambda>x. if c \<le> x then \<phi> x + k else \<phi> x) \<longlongrightarrow> \<phi>c) (at c within {a..c})\<close>
          using that(1) tendsto_cong by force
        then show ?thesis using that(2) by simp
      qed
      have cont_g': \<open>(g' \<longlongrightarrow> g' c) (at c within {a..c})\<close>
        unfolding g'_def using cont_shift[OF gc] k_def by simp
      have cont_h': \<open>(h' \<longlongrightarrow> h' c) (at c within {a..c})\<close>
        unfolding h'_def using cont_shift[OF hc \<open>k = hc - h c\<close>] .
      \<comment> \<open>Variation of a monotone function on a subinterval = endpoint difference\<close>
      have vv_mono: \<open>vector_variation {x..c} \<phi>' = norm (\<phi>' c - \<phi>' x)\<close>
        if \<open>mono_on {a..c} \<phi>'\<close> \<open>x \<in> {a..c}\<close> for \<phi>' :: \<open>real \<Rightarrow> real\<close> and x
        using increasing_vector_variation[OF mono_on_subset[OF that(1)]] that(2) by auto
      \<comment> \<open>The \<epsilon>/2 argument\<close>
      show \<open>continuous (at c within {a..c}) (\<lambda>x. vector_variation {a..x} f)\<close>
        unfolding continuous_within tendsto_iff
      proof (intro allI impI)
        fix \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>
        then have e2: \<open>\<epsilon> / 2 > 0\<close> by simp
        \<comment> \<open>Get eventually-close from continuity of g' and h' for \<epsilon>/2\<close>
        have ev_gh': \<open>\<forall>\<^sub>F x in at c within {a..c}.
          dist (g' x) (g' c) < \<epsilon> / 2 \<and> dist (h' x) (h' c) < \<epsilon> / 2 \<and> x \<in> {a..c}\<close>
        proof (intro eventually_conj)
          show \<open>\<forall>\<^sub>F x in at c within {a..c}. dist (g' x) (g' c) < \<epsilon> / 2\<close>
            using tendstoD[OF cont_g' e2] .
          show \<open>\<forall>\<^sub>F x in at c within {a..c}. dist (h' x) (h' c) < \<epsilon> / 2\<close>
            using tendstoD[OF cont_h' e2] .
          show \<open>\<forall>\<^sub>F x in at c within {a..c}. x \<in> {a..c}\<close>
            unfolding eventually_at_filter by (auto intro: always_eventually)
        qed
        \<comment> \<open>Combine using triangle inequality\<close>
        show \<open>\<forall>\<^sub>F x in at c within {a..c}. dist (vector_variation {a..x} f) (vector_variation {a..c} f) < \<epsilon>\<close>
        proof (rule eventually_mono[OF ev_gh'])
          fix x
          assume H: \<open>dist (g' x) (g' c) < \<epsilon> / 2 \<and> dist (h' x) (h' c) < \<epsilon> / 2 \<and> x \<in> {a..c}\<close>
          then have dg: \<open>dist (g' x) (g' c) < \<epsilon> / 2\<close>
            and dh: \<open>dist (h' x) (h' c) < \<epsilon> / 2\<close>
            and xac: \<open>x \<in> {a..c}\<close> by auto
          show \<open>dist (vector_variation {a..x} f) (vector_variation {a..c} f) < \<epsilon>\<close>
          proof (cases \<open>x = c\<close>)
            case True
            then show ?thesis using \<open>\<epsilon> > 0\<close> by simp
          next
            case False
            then have xc: \<open>x < c\<close> and xle: \<open>x \<le> c\<close> using xac by auto
            have bv_xc: \<open>has_bounded_variation_on f {x..c}\<close>
              using has_bounded_variation_on_subset[OF bv_ac] xac by auto
            \<comment> \<open>Variation of f on {x..c} bounded by sum of variations of g' and h'\<close>
            have vv_f_xc: \<open>vector_variation {x..c} f \<le> vector_variation {x..c} g' + vector_variation {x..c} h'\<close>
            proof -
              have \<open>{x..c} \<subseteq> {a..c}\<close> using xac by auto
              have \<open>vector_variation {x..c} f = vector_variation {x..c} (\<lambda>t. g' t - h' t)\<close>
                using \<open>f = (\<lambda>x. g' x - h' x)\<close> by simp
              also have \<open>\<dots> \<le> vector_variation {x..c} g' + vector_variation {x..c} h'\<close>
                using vector_variation_triangle_sub
                  [OF increasing_bounded_variation[OF mono_on_subset[OF mono_g' \<open>{x..c} \<subseteq> {a..c}\<close>]]
                      increasing_bounded_variation[OF mono_on_subset[OF mono_h' \<open>{x..c} \<subseteq> {a..c}\<close>]]] .
              finally show ?thesis .
            qed
            \<comment> \<open>Chain the bounds\<close>
            have \<open>dist (vector_variation {a..x} f) (vector_variation {a..c} f)
                  = \<bar>vector_variation {a..x} f - vector_variation {a..c} f\<bar>\<close>
              by (simp add: dist_real_def)
            also have \<open>\<dots> = vector_variation {x..c} f\<close>
              using vector_variation_combine[OF bv_ac xac] vector_variation_pos_le[OF bv_xc]
              by linarith
            also have \<open>\<dots> \<le> vector_variation {x..c} g' + vector_variation {x..c} h'\<close>
              using vv_f_xc .
            also have \<open>\<dots> = norm (g' c - g' x) + norm (h' c - h' x)\<close>
              using vv_mono[OF mono_g' xac] vv_mono[OF mono_h' xac] by simp
            also have \<open>\<dots> = dist (g' x) (g' c) + dist (h' x) (h' c)\<close>
              by (simp add: dist_real_def dist_commute)
            also have \<open>\<dots> < \<epsilon> / 2 + \<epsilon> / 2\<close>
              using dg dh by linarith
            also have \<open>\<dots> = \<epsilon>\<close> by simp
            finally show ?thesis .
          qed
        qed
      qed
    qed
  qed
qed

lemma continuous_vector_variation_left:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  assumes \<open>has_bounded_variation_on f {a..b}\<close> \<open>c \<in> {a..b}\<close>
  shows \<open>continuous (at c within {a..c}) (\<lambda>x. vector_variation {a..x} f) \<longleftrightarrow>
         continuous (at c within {a..c}) f\<close>   (is \<open>?L = ?R\<close>)
proof
  assume L: ?L
  show ?R
  proof -
    have bv_ac: \<open>has_bounded_variation_on f {a..c}\<close>
      using has_bounded_variation_on_subset[OF assms(1)] assms(2) by auto
    show ?thesis unfolding continuous_within Lim_within
    proof (intro allI impI)
      fix \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>
      from L[unfolded continuous_within Lim_within, rule_format, OF \<open>\<epsilon> > 0\<close>]
      obtain \<delta> where \<open>\<delta> > 0\<close> and \<delta>: \<open>\<And>x. x \<in> {a..c} \<Longrightarrow> 0 < dist x c \<Longrightarrow> dist x c < \<delta> \<Longrightarrow>
        dist (vector_variation {a..x} f) (vector_variation {a..c} f) < \<epsilon>\<close>
        by auto
      show \<open>\<exists>\<delta>>0. \<forall>x\<in>{a..c}. 0 < dist x c \<and> dist x c < \<delta> \<longrightarrow> dist (f x) (f c) < \<epsilon>\<close>
      proof (intro exI[of _ \<delta>] conjI ballI impI)
        show \<open>\<delta> > 0\<close> by fact
      next
        fix x assume \<open>x \<in> {a..c}\<close> \<open>0 < dist x c \<and> dist x c < \<delta>\<close>
        then have xac: \<open>x \<in> {a..c}\<close> and xnc: \<open>x \<noteq> c\<close> and xd: \<open>dist x c < \<delta>\<close> by auto
        have bv_xc: \<open>has_bounded_variation_on f {x..c}\<close>
          using has_bounded_variation_on_subset[OF bv_ac] xac by auto
        have vv_split: \<open>vector_variation {a..c} f = vector_variation {a..x} f + vector_variation {x..c} f\<close>
          using vector_variation_combine[OF bv_ac xac] .
        have vv_pos: \<open>vector_variation {x..c} f \<ge> 0\<close>
          using vector_variation_pos_le[OF bv_xc] .
        have dist_vv: \<open>dist (vector_variation {a..x} f) (vector_variation {a..c} f) < \<epsilon>\<close>
          using \<delta>[OF xac] xnc xd by auto
        have \<open>vector_variation {x..c} f = dist (vector_variation {a..x} f) (vector_variation {a..c} f)\<close>
          by (simp add: dist_norm vv_pos vv_split)
        also have \<open>\<dots> < \<epsilon>\<close> by fact
        finally have vv_bound: \<open>vector_variation {x..c} f < \<epsilon>\<close> .
        have \<open>dist (f x) (f c) = norm (f x - f c)\<close> by (simp add: dist_norm)
        also have \<open>\<dots> \<le> vector_variation {x..c} f\<close>
          using vector_variation_ge_norm_function[OF bv_xc] xac by auto
        also have \<open>\<dots> < \<epsilon>\<close> by fact
        finally show \<open>dist (f x) (f c) < \<epsilon>\<close> .
      qed
    qed
  qed
next
  assume R: ?R
  show ?L
  proof (cases \<open>c islimpt {a..c}\<close>)
    case False
    then show ?thesis using continuous_bot
      by (metis trivial_limit_within)
  next
    case True
    show ?thesis
    proof (rule continuous_within_comparison
        [where g = \<open>\<lambda>x. \<Sum>b\<in>Basis. vector_variation {a..x} (\<lambda>u. f u \<bullet> b)\<close>])
      have bv_ac: \<open>has_bounded_variation_on f {a..c}\<close>
        using has_bounded_variation_on_subset[OF assms(1)] assms(2) by auto
      \<comment> \<open>Subgoal 1: Continuity of the sum of component vector variations\<close>
      show \<open>continuous (at c within {a..c})
        (\<lambda>x. \<Sum>i\<in>Basis. vector_variation {a..x} (\<lambda>u. f u \<bullet> i))\<close>
      proof (rule continuous_sum)
        fix i :: 'a assume iB: \<open>i \<in> Basis\<close>
        have bv_comp: \<open>has_bounded_variation_on (\<lambda>u. f u \<bullet> i) {a..b}\<close>
          using has_bounded_variation_on_inner_left[OF assms(1)] .
        have cont_comp: \<open>continuous (at c within {a..c}) (\<lambda>u. f u \<bullet> i)\<close>
        proof (unfold continuous_within)
          from R have \<open>(f \<longlongrightarrow> f c) (at c within {a..c})\<close> by (simp add: continuous_within)
          then show \<open>((\<lambda>u. f u \<bullet> i) \<longlongrightarrow> f c \<bullet> i) (at c within {a..c})\<close>
            by (intro tendsto_inner tendsto_const)
        qed
        show \<open>continuous (at c within {a..c}) (\<lambda>x. vector_variation {a..x} (\<lambda>u. f u \<bullet> i))\<close>
          using continuous_vector_variation_left_1[OF bv_comp assms(2)] cont_comp by simp
      qed
    next
      \<comment> \<open>Subgoal 2: Distance bound\<close>
      have bv_ac: \<open>has_bounded_variation_on f {a..c}\<close>
        using has_bounded_variation_on_subset[OF assms(1)] assms(2) by auto
      fix x assume xac: \<open>x \<in> {a..c}\<close>
      have bv_xc: \<open>has_bounded_variation_on f {x..c}\<close>
        using has_bounded_variation_on_subset[OF bv_ac] xac by auto
      have bv_comp_ac: \<open>\<And>b. has_bounded_variation_on (\<lambda>u. f u \<bullet> b) {a..c}\<close>
        using has_bounded_variation_on_inner_left[OF bv_ac] .
      have bv_comp_xc: \<open>\<And>b. has_bounded_variation_on (\<lambda>u. f u \<bullet> b) {x..c}\<close>
        using has_bounded_variation_on_inner_left[OF bv_xc] .
      \<comment> \<open>Intermediate claim: vector_variation_combine for f and each component\<close>
      have vv_split: \<open>vector_variation {a..c} f =
        vector_variation {a..x} f + vector_variation {x..c} f\<close>
        using vector_variation_combine[OF bv_ac xac] .
      have vv_comp_split: \<open>vector_variation {a..c} (\<lambda>u. f u \<bullet> b) =
        vector_variation {a..x} (\<lambda>u. f u \<bullet> b) + vector_variation {x..c} (\<lambda>u. f u \<bullet> b)\<close>
        if \<open>b \<in> Basis\<close> for b
        using vector_variation_combine[OF bv_comp_ac xac] .
      \<comment> \<open>LHS: dist of vector variations of f\<close>
      have lhs: \<open>dist (vector_variation {a..c} f) (vector_variation {a..x} f) =
        vector_variation {x..c} f\<close>
      proof -
        have \<open>vector_variation {x..c} f \<ge> 0\<close>
          using vector_variation_pos_le[OF bv_xc] .
        then show ?thesis
          by (simp add: dist_real_def vv_split)
      qed
      \<comment> \<open>RHS: dist of sums of component vector variations\<close>
      have rhs: \<open>dist (\<Sum>b\<in>Basis. vector_variation {a..c} (\<lambda>u. f u \<bullet> b))
                       (\<Sum>b\<in>Basis. vector_variation {a..x} (\<lambda>u. f u \<bullet> b)) =
        (\<Sum>b\<in>Basis. vector_variation {x..c} (\<lambda>u. f u \<bullet> b))\<close>
      proof -
        have eq: \<open>(\<Sum>b\<in>Basis. vector_variation {a..c} (\<lambda>u. f u \<bullet> b)) -
          (\<Sum>b\<in>Basis. vector_variation {a..x} (\<lambda>u. f u \<bullet> b)) =
          (\<Sum>b\<in>Basis. vector_variation {x..c} (\<lambda>u. f u \<bullet> b))\<close>
        proof -
          have \<open>(\<Sum>b\<in>Basis. vector_variation {a..c} (\<lambda>u. f u \<bullet> b)) -
            (\<Sum>b\<in>Basis. vector_variation {a..x} (\<lambda>u. f u \<bullet> b)) =
            (\<Sum>b\<in>Basis. (vector_variation {a..c} (\<lambda>u. f u \<bullet> b) -
              vector_variation {a..x} (\<lambda>u. f u \<bullet> b)))\<close>
            by (simp add: sum_subtractf)
          also have \<open>\<dots> = (\<Sum>b\<in>Basis. vector_variation {x..c} (\<lambda>u. f u \<bullet> b))\<close>
            by (intro sum.cong refl) (use vv_comp_split in auto)
          finally show ?thesis .
        qed
        moreover have \<open>(\<Sum>b\<in>Basis. vector_variation {x..c} (\<lambda>u. f u \<bullet> b)) \<ge> 0\<close>
          by (intro sum_nonneg vector_variation_pos_le bv_comp_xc)
        ultimately show ?thesis
          by (simp add: dist_real_def)
      qed
      show \<open>dist (vector_variation {a..c} f) (vector_variation {a..x} f) \<le>
        dist (\<Sum>b\<in>Basis. vector_variation {a..c} (\<lambda>u. f u \<bullet> b))
             (\<Sum>b\<in>Basis. vector_variation {a..x} (\<lambda>u. f u \<bullet> b))\<close>
        unfolding lhs rhs
        using vector_variation_le_component_sum[OF bv_xc] .
    qed
  qed
qed


lemma division_of_reflect:
  fixes s :: real
  assumes \<open>d division_of t\<close>
  shows \<open>(`) ((-) s) ` d division_of ((-) s) ` t\<close>
proof -
  define d' where \<open>d' = (`) ((-) s) ` d\<close>
  have fin: \<open>finite d'\<close>
    unfolding d'_def using division_of_finite[OF assms] by auto
  have props: \<open>K \<subseteq> (-) s ` t \<and> K \<noteq> {} \<and> (\<exists>a b. K = cbox a b)\<close>
    if \<open>K \<in> d'\<close> for K
  proof -
    from that obtain k where kd: \<open>k \<in> d\<close> and K_eq: \<open>K = (-) s ` k\<close>
      unfolding d'_def by auto
    have ksub: \<open>k \<subseteq> t\<close> and kne: \<open>k \<noteq> {}\<close> using division_ofD(2,3)[OF assms kd] by auto
    from division_ofD(4)[OF assms kd] obtain u v where kuv: \<open>k = cbox u v\<close> by auto
    with kne have uv: \<open>u \<le> v\<close> by (simp add: cbox_interval)
    have \<open>K \<subseteq> (-) s ` t\<close>
      using ksub K_eq by (auto intro: image_mono)
    moreover have \<open>K \<noteq> {}\<close> using kne K_eq by auto
    moreover have \<open>\<exists>a b. K = cbox a b\<close>
      using K_eq kuv uv by (auto simp: cbox_interval image_diff_atLeastAtMost intro!: exI)
    ultimately show ?thesis by blast
  qed
  have disj: \<open>interior K1 \<inter> interior K2 = {}\<close>
    if \<open>K1 \<in> d'\<close> \<open>K2 \<in> d'\<close> \<open>K1 \<noteq> K2\<close> for K1 K2
  proof -
    from that obtain k1 k2 where k1d: \<open>k1 \<in> d\<close> and K1_eq: \<open>K1 = (-) s ` k1\<close>
      and k2d: \<open>k2 \<in> d\<close> and K2_eq: \<open>K2 = (-) s ` k2\<close>
      unfolding d'_def by auto
    have \<open>k1 \<noteq> k2\<close> using that K1_eq K2_eq by auto
    from division_ofD(5)[OF assms k1d k2d this]
    have \<open>interior k1 \<inter> interior k2 = {}\<close> .
    have interior_diff: \<open>interior ((-) s ` S) = (-) s ` interior S\<close> for S :: \<open>real set\<close>
    proof -
      have \<open>(-) s = (+) s \<circ> uminus\<close> by (auto simp: fun_eq_iff)
      then have \<open>(-) s ` S = (+) s ` (uminus ` S)\<close>
        by (metis image_comp)
      then have \<open>interior ((-) s ` S) = interior ((+) s ` (uminus ` S))\<close> by simp
      also have \<open>\<dots> = (+) s ` interior (uminus ` S)\<close> by (simp add: interior_translation)
      also have \<open>\<dots> = (+) s ` (uminus ` interior S)\<close> by (simp add: interior_negations)
      also have \<open>\<dots> = (-) s ` interior S\<close> by (auto simp: image_comp fun_eq_iff)
      finally show ?thesis .
    qed
    show ?thesis
      unfolding K1_eq K2_eq interior_diff
      using \<open>interior k1 \<inter> interior k2 = {}\<close>
      by (metis image_Int inj_on_diff_left image_empty image_is_empty)
  qed
  have \<open>\<Union> d' = (-) s ` t\<close>
  proof -
    have \<open>\<Union> d = t\<close> using division_ofD(6)[OF assms] .
    then show ?thesis
      unfolding d'_def by (simp add: image_Union[symmetric])
  qed
  then show ?thesis
    unfolding d'_def[symmetric] division_of_def
    using fin props disj by auto
qed

lemma has_bounded_variation_on_reflect:
  assumes \<open>has_bounded_variation_on f {s - \<beta>..s - \<alpha>}\<close>
  shows \<open>has_bounded_variation_on (f \<circ> (\<lambda>t. s - t)) {\<alpha>..\<beta>}\<close>
proof -
  from assms obtain B where B: \<open>\<And>d. d division_of {s - \<beta>..s - \<alpha>} \<Longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B\<close>
    unfolding has_bounded_variation_on_interval by blast
  show ?thesis
    unfolding has_bounded_variation_on_interval
  proof (intro exI[of _ B] allI impI)
    fix d assume d: \<open>d division_of {\<alpha>..\<beta>}\<close>
    define d' where \<open>d' = (`) ((-) s) ` d\<close>
    have d': \<open>d' division_of {s - \<beta>..s - \<alpha>}\<close>
      unfolding d'_def using division_of_reflect[OF d] by (simp add: image_diff_atLeastAtMost)
    have k_interval: \<open>\<exists>u v. u \<le> v \<and> k = {u..v}\<close> if \<open>k \<in> d\<close> for k
    proof -
      from division_ofD(3,4)[OF d that] obtain u v where \<open>k \<noteq> {}\<close> \<open>k = cbox u v\<close> by auto
      then have \<open>u \<le> v\<close> by force
      then show ?thesis using \<open>k = cbox u v\<close> by (auto simp: cbox_interval)
    qed
    have sum_eq: \<open>(\<Sum>k\<in>d. norm ((f \<circ> (\<lambda>t. s - t)) (Sup k) - (f \<circ> (\<lambda>t. s - t)) (Inf k))) =
                 (\<Sum>k\<in>d'. norm (f (Sup k) - f (Inf k)))\<close>
    proof -
      have inj: \<open>inj_on ((`) ((-) s)) d\<close>
        by (intro inj_onI) (auto simp: inj_image_eq_iff dest: inj_onD[OF inj_on_diff_left])
      have \<open>(\<Sum>k\<in>d'. norm (f (Sup k) - f (Inf k))) =
            (\<Sum>k\<in>d. norm (f (Sup ((-) s ` k)) - f (Inf ((-) s ` k))))\<close>
        unfolding d'_def using sum.reindex[OF inj] by simp
      also have \<open>\<dots> = (\<Sum>k\<in>d. norm (f (s - Inf k) - f (s - Sup k)))\<close>
      proof (rule sum.cong[OF refl])
        fix k assume \<open>k \<in> d\<close>
        then obtain u v where uv: \<open>u \<le> v\<close> \<open>k = {u..v}\<close> using k_interval by blast
        then have \<open>(-) s ` k = {s - v..s - u}\<close> by (simp add: image_diff_atLeastAtMost)
        moreover have \<open>s - v \<le> s - u\<close> using uv by simp
        ultimately show \<open>norm (f (Sup ((-) s ` k)) - f (Inf ((-) s ` k))) =
                         norm (f (s - Inf k) - f (s - Sup k))\<close>
          using uv by simp
      qed
      also have \<open>\<dots> = (\<Sum>k\<in>d. norm ((f \<circ> (\<lambda>t. s - t)) (Sup k) - (f \<circ> (\<lambda>t. s - t)) (Inf k)))\<close>
      proof (rule sum.cong[OF refl])
        fix k assume \<open>k \<in> d\<close>
        show \<open>norm (f (s - Inf k) - f (s - Sup k)) =
              norm ((f \<circ> (\<lambda>t. s - t)) (Sup k) - (f \<circ> (\<lambda>t. s - t)) (Inf k))\<close>
          by (simp add: norm_minus_commute)
      qed
      finally show ?thesis by simp
    qed
    show \<open>(\<Sum>k\<in>d. norm ((f \<circ> (\<lambda>t. s - t)) (Sup k) - (f \<circ> (\<lambda>t. s - t)) (Inf k))) \<le> B\<close>
      unfolding sum_eq using B[OF d'] .
  qed
qed

lemma vector_variation_reflect:
  assumes \<open>\<alpha> \<le> \<beta>\<close>
  shows \<open>vector_variation {\<alpha>..\<beta>} (f \<circ> (\<lambda>t. s - t)) = vector_variation {s - \<beta>..s - \<alpha>} f\<close>
proof -
  \<comment> \<open>Key helper: sums over a division and its reflection are equal\<close>
  have sum_eq: \<open>(\<Sum>k\<in>d. norm ((f \<circ> (\<lambda>t. s - t)) (Sup k) - (f \<circ> (\<lambda>t. s - t)) (Inf k))) =
               (\<Sum>k\<in>(`) ((-) s) ` d. norm (f (Sup k) - f (Inf k)))\<close>
    if d_div: \<open>d division_of t\<close> and t_sub: \<open>t \<subseteq> {\<alpha>..\<beta>}\<close> for d t
  proof -
    define d' where \<open>d' = (`) ((-) s) ` d\<close>
    have inj: \<open>inj_on ((`) ((-) s)) d\<close>
      by (intro inj_onI) (auto simp: inj_image_eq_iff dest: inj_onD[OF inj_on_diff_left])
    have k_interval: \<open>\<exists>u v. u \<le> v \<and> k = {u..v}\<close> if \<open>k \<in> d\<close> for k
    proof -
      from division_ofD(3,4)[OF d_div that] obtain u v where \<open>k \<noteq> {}\<close> \<open>k = cbox u v\<close> by auto
      then have \<open>u \<le> v\<close> by force
      then show ?thesis using \<open>k = cbox u v\<close> by (auto simp: cbox_interval)
    qed
    have \<open>(\<Sum>k\<in>d'. norm (f (Sup k) - f (Inf k))) =
          (\<Sum>k\<in>d. norm (f (Sup ((-) s ` k)) - f (Inf ((-) s ` k))))\<close>
      unfolding d'_def using sum.reindex[OF inj] by simp
    also have \<open>\<dots> = (\<Sum>k\<in>d. norm (f (s - Inf k) - f (s - Sup k)))\<close>
    proof (rule sum.cong[OF refl])
      fix k assume \<open>k \<in> d\<close>
      then obtain u v where uv: \<open>u \<le> v\<close> \<open>k = {u..v}\<close> using k_interval by blast
      then have \<open>(-) s ` k = {s - v..s - u}\<close> by (simp add: image_diff_atLeastAtMost)
      moreover have \<open>s - v \<le> s - u\<close> using uv by simp
      ultimately show \<open>norm (f (Sup ((-) s ` k)) - f (Inf ((-) s ` k))) =
                       norm (f (s - Inf k) - f (s - Sup k))\<close>
        using uv by simp
    qed
    also have \<open>\<dots> = (\<Sum>k\<in>d. norm ((f \<circ> (\<lambda>t. s - t)) (Sup k) - (f \<circ> (\<lambda>t. s - t)) (Inf k)))\<close>
    proof (rule sum.cong[OF refl])
      fix k assume \<open>k \<in> d\<close>
      show \<open>norm (f (s - Inf k) - f (s - Sup k)) =
            norm ((f \<circ> (\<lambda>t. s - t)) (Sup k) - (f \<circ> (\<lambda>t. s - t)) (Inf k))\<close>
        by (simp add: norm_minus_commute)
    qed
    finally show ?thesis unfolding d'_def by simp
  qed
  \<comment> \<open>Show the sets of sums are equal\<close>
  have set_eq: \<open>{\<Sum>k\<in>d. norm ((f \<circ> (\<lambda>t. s - t)) (Sup k) - (f \<circ> (\<lambda>t. s - t)) (Inf k)) |
                 d. \<exists>t. d division_of t \<and> t \<subseteq> {\<alpha>..\<beta>}} =
               {\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) |
                 d. \<exists>t. d division_of t \<and> t \<subseteq> {s - \<beta>..s - \<alpha>}}\<close>
    (is \<open>?A = ?B\<close>)
  proof (intro equalityI subsetI)
    fix x assume \<open>x \<in> ?A\<close>
    then obtain d t where dt: \<open>d division_of t\<close> \<open>t \<subseteq> {\<alpha>..\<beta>}\<close>
      and x_eq: \<open>x = (\<Sum>k\<in>d. norm ((f \<circ> (\<lambda>t. s - t)) (Sup k) - (f \<circ> (\<lambda>t. s - t)) (Inf k)))\<close>
      by auto
    have \<open>x = (\<Sum>k\<in>(`) ((-) s) ` d. norm (f (Sup k) - f (Inf k)))\<close>
      unfolding x_eq using sum_eq[OF dt] .
    moreover have \<open>(`) ((-) s) ` d division_of (-) s ` t\<close>
      using division_of_reflect[OF dt(1)] by auto
    moreover have \<open>(-) s ` t \<subseteq> {s - \<beta>..s - \<alpha>}\<close>
      using dt(2) by (auto simp: image_diff_atLeastAtMost)
    ultimately show \<open>x \<in> ?B\<close> by blast
  next
    fix x assume \<open>x \<in> ?B\<close>
    then obtain d t where dt: \<open>d division_of t\<close> \<open>t \<subseteq> {s - \<beta>..s - \<alpha>}\<close>
      and x_eq: \<open>x = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))\<close> by auto
    \<comment> \<open>Reflect back: d' = ((-) s) ` d is a division of ((-) s) ` t \<subseteq> {\<alpha>..\<beta>}\<close>
    define d' where \<open>d' = (`) ((-) s) ` d\<close>
    have d'_div: \<open>d' division_of (-) s ` t\<close>
      unfolding d'_def using division_of_reflect[OF dt(1)] by auto
    have t'_sub: \<open>(-) s ` t \<subseteq> {\<alpha>..\<beta>}\<close>
      using dt(2) by (auto simp: image_diff_atLeastAtMost)
    have \<open>(\<Sum>k\<in>d'. norm ((f \<circ> (\<lambda>t. s - t)) (Sup k) - (f \<circ> (\<lambda>t. s - t)) (Inf k))) =
          (\<Sum>k\<in>(`) ((-) s) ` d'. norm (f (Sup k) - f (Inf k)))\<close>
      using sum_eq[OF d'_div t'_sub] .
    also have \<open>(`) ((-) s) ` d' = d\<close>
      unfolding d'_def by (auto simp: image_image)
    also have \<open>(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) = x\<close> using x_eq by simp
    finally show \<open>x \<in> ?A\<close> using d'_div t'_sub by blast
  qed
  show ?thesis
    unfolding vector_variation_def set_variation_def set_eq ..
qed

lemma continuous_reflect:
  fixes f :: \<open>real \<Rightarrow> 'a::topological_space\<close>
  shows \<open>continuous (at c within S) (f \<circ> (\<lambda>t. s - t)) \<longleftrightarrow>
         continuous (at (s - c) within ((-) s) ` S) f\<close>
proof -
  have filt: \<open>filtermap ((-) s) (at c within S) = at (s - c) within (-) s ` S\<close>
  proof (rule filtermap_linear_at_within)
    show \<open>bij ((-) s)\<close> by (rule bij_diff)
    show \<open>isCont ((-) s) c\<close>
      using continuous_on_op_minus[of UNIV s]
      by (simp add: continuous_on_eq_continuous_at)
    show \<open>\<And>S. open S \<Longrightarrow> open ((-) s ` S)\<close>
      by (rule open_neg_translation)
  qed
  show ?thesis
    unfolding continuous_within
    by (simp add: tendsto_compose_filtermap filt)
qed

lemma continuous_vector_variation_at_right:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  assumes \<open>has_bounded_variation_on f {a..b}\<close> \<open>c \<in> {a..b}\<close>
  shows \<open>continuous (at c within {c..b}) (\<lambda>x. vector_variation {a..x} f) \<longleftrightarrow>
         continuous (at c within {c..b}) f\<close>
proof -
  define s where \<open>s = a + b\<close>
  define c' where \<open>c' = s - c\<close>
  have sc: \<open>s - c' = c\<close> unfolding c'_def by simp
  have sa: \<open>s - a = b\<close> and sb: \<open>s - b = a\<close> unfolding s_def by auto
  have ac: \<open>a \<le> c\<close> and cb: \<open>c \<le> b\<close> using assms(2) by auto
  have c'_mem: \<open>c' \<in> {a..b}\<close> unfolding c'_def s_def using ac cb by auto
  have img: \<open>(-) s ` {c..b} = {a..c'}\<close> and img': \<open>(-) s ` {a..c'} = {c..b}\<close>
    unfolding c'_def s_def by (auto simp: image_diff_atLeastAtMost)
  \<comment> \<open>The reflected function\<close>
  define g where \<open>g = f \<circ> (-) s\<close>
  have bv_g: \<open>has_bounded_variation_on g {a..b}\<close>
    unfolding g_def using has_bounded_variation_on_reflect[of f s b a] assms(1)
    by (simp add: s_def)
  \<comment> \<open>Step 1: continuous_vector_variation_left for g at c'\<close>
  have left: \<open>continuous (at c' within {a..c'}) (\<lambda>y. vector_variation {a..y} g) \<longleftrightarrow>
              continuous (at c' within {a..c'}) g\<close>
    using continuous_vector_variation_left[OF bv_g c'_mem] .
  \<comment> \<open>Step 2: Relate continuity of g at c' within {a..c'} to f at c within {c..b}\<close>
  have cont_f_g: \<open>continuous (at c within {c..b}) f \<longleftrightarrow> continuous (at c' within {a..c'}) g\<close>
    unfolding g_def using continuous_reflect[of c' \<open>{a..c'}\<close> f s]
    by (simp add: sc sa image_diff_atLeastAtMost)
  \<comment> \<open>Step 3: Show (\<lambda>y. vv{a..y} g) \<circ> r = (\<lambda>x. vv{x..b} f) pointwise\<close>
  have comp_eq: \<open>vector_variation {a..s - x} g = vector_variation {x..b} f\<close> for x
  proof (cases \<open>a \<le> s - x\<close>)
    case True
    then show ?thesis
      unfolding g_def using vector_variation_reflect[of a \<open>s - x\<close> f s] by (simp add: sa)
  next
    case False
    then have \<open>{a..s - x} = {}\<close> and \<open>{x..b} = {}\<close>
      unfolding s_def by auto
    then show ?thesis by (simp add: vector_variation_def set_variation_def)
  qed
  \<comment> \<open>Step 4: Relate continuity of (\<lambda>y. vv{a..y} g) at c' to (\<lambda>x. vv{x..b} f) at c\<close>
  have cont_vv_reflect: \<open>continuous (at c' within {a..c'}) (\<lambda>y. vector_variation {a..y} g) \<longleftrightarrow>
                          continuous (at c within {c..b}) (\<lambda>x. vector_variation {x..b} f)\<close>
  proof -
    have eq: \<open>(\<lambda>y. vector_variation {a..y} g) \<circ> (-) s = (\<lambda>x. vector_variation {x..b} f)\<close>
      by (rule ext) (simp add: comp_eq)
    show ?thesis
      using continuous_reflect[of c \<open>{c..b}\<close> \<open>\<lambda>y. vector_variation {a..y} g\<close> s]
      using eq img by force
  qed
  \<comment> \<open>Step 5: Relate continuity of (\<lambda>x. vv{x..b} f) to (\<lambda>x. vv{a..x} f)\<close>
  have vv_split: \<open>vector_variation {a..b} f - vector_variation {a..x} f = vector_variation {x..b} f\<close>
    if \<open>x \<in> {a..b}\<close> for x
    using vector_variation_combine[OF assms(1) that] by linarith
  have cont_vv_shift: \<open>continuous (at c within {c..b}) (\<lambda>x. vector_variation {x..b} f) \<longleftrightarrow>
                       continuous (at c within {c..b}) (\<lambda>x. vector_variation {a..x} f)\<close>
    (is \<open>?P \<longleftrightarrow> ?Q\<close>)
  proof
    assume ?Q
    have \<open>continuous (at c within {c..b}) (\<lambda>x. vector_variation {a..b} f - vector_variation {a..x} f)\<close>
      using continuous_diff[OF continuous_const \<open>?Q\<close>] .
    moreover have \<open>\<forall>\<^sub>F x in at c within {c..b}. vector_variation {a..b} f - vector_variation {a..x} f =
                   vector_variation {x..b} f\<close>
      unfolding eventually_at_topological
      by (meson vv_split ac atLeastAtMost_iff first_countable_basis order_trans)
    ultimately show ?P
      unfolding continuous_within
      using assms(2) tendsto_cong vv_split by fastforce
  next
    assume ?P
    have \<open>continuous (at c within {c..b}) (\<lambda>x. vector_variation {a..b} f - vector_variation {x..b} f)\<close>
      using continuous_diff[OF continuous_const \<open>?P\<close>] .
    moreover have \<open>\<forall>\<^sub>F x in at c within {c..b}. vector_variation {a..b} f - vector_variation {x..b} f =
                   vector_variation {a..x} f\<close>
      unfolding eventually_at_topological
    proof (intro exI[of _ UNIV] conjI ballI impI open_UNIV UNIV_I)
      fix x assume \<open>x \<noteq> c\<close> \<open>x \<in> {c..b}\<close>
      then have \<open>x \<in> {a..b}\<close> using ac by auto
      from vv_split[OF this] show \<open>vector_variation {a..b} f - vector_variation {x..b} f = vector_variation {a..x} f\<close>
        by linarith
    qed
    ultimately show ?Q
      by (metis (no_types, lifting) ext add.commute add.left_cancel assms(2)
          continuous_at_within_cong diff_add_cancel vv_split)
  qed
  \<comment> \<open>Chain the equivalences\<close>
  show ?thesis
    using left cont_f_g cont_vv_reflect cont_vv_shift by simp
qed

lemma vector_variation_continuous:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  assumes \<open>has_bounded_variation_on f {a..b}\<close> \<open>c \<in> {a..b}\<close>
  shows \<open>continuous (at c within {a..b}) (\<lambda>x. vector_variation {a..x} f) \<longleftrightarrow>
         continuous (at c within {a..b}) f\<close>
  unfolding continuous_within_ivl_split[OF assms(2)]
  using continuous_vector_variation_left[OF assms] continuous_vector_variation_at_right[OF assms]
  by simp


section \<open>Rectifiable paths and arc-length reparametrization\<close>

definition rectifiable_path :: \<open>(real \<Rightarrow> 'a::euclidean_space) \<Rightarrow> bool\<close> where
  \<open>rectifiable_path g \<longleftrightarrow> path g \<and> has_bounded_variation_on g {0..1}\<close>

definition path_length :: \<open>(real \<Rightarrow> 'a::euclidean_space) \<Rightarrow> real\<close> where
  \<open>path_length g = vector_variation {0..1} g\<close>

text \<open>
  We can factor a BV function through its variation.  Moreover the factor is
  Lipschitz (hence continuous) on its domain, though without continuity of the
  original function that domain may not be an interval.
\<close>

lemma factor_through_variation:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  assumes \<open>has_bounded_variation_on f {a..b}\<close>
  shows \<open>\<exists>g. (\<forall>x \<in> {a..b}. f x = g (vector_variation {a..x} f)) \<and>
             continuous_on ((\<lambda>x. vector_variation {a..x} f) ` {a..b}) g \<and>
             (\<forall>u \<in> (\<lambda>x. vector_variation {a..x} f) ` {a..b}.
              \<forall>v \<in> (\<lambda>x. vector_variation {a..x} f) ` {a..b}.
                dist (g u) (g v) \<le> dist u v)\<close>
proof -
  define S where \<open>S \<equiv> (\<lambda>x. vector_variation {a..x} f) ` {a..b}\<close>
  have claim1: \<open>\<exists>g. (\<forall>x \<in> {a..b}. f x = g (vector_variation {a..x} f)) \<and>
                    (\<forall>u \<in> S. \<forall>v \<in> S. dist (g u) (g v) \<le> dist u v)\<close>
  proof (cases \<open>{a..b} = {}\<close>)
    case True
    then show ?thesis unfolding S_def by auto
  next
    case False
    then have ab: \<open>a \<le> b\<close> by auto
    define V where \<open>V x \<equiv> vector_variation {a..x} f\<close> for x
    \<comment> \<open>Key injectivity-up-to-f property: V x = V y implies f x = f y\<close>
    have f_eq: \<open>f x = f y\<close>
      if \<open>x \<in> {a..b}\<close> \<open>y \<in> {a..b}\<close> \<open>V x = V y\<close> for x y
    proof -
      \<comment> \<open>Core argument: if p \<le> q with matching variation, then f p = f q\<close>
      have core: \<open>f p = f q\<close>
        if \<open>p \<le> q\<close> \<open>p \<in> {a..b}\<close> \<open>q \<in> {a..b}\<close> \<open>V p = V q\<close> for p q
      proof -
        have bv_aq: \<open>has_bounded_variation_on f {a..q}\<close>
          using has_bounded_variation_on_subset[OF assms] that ab by auto
        have p_in: \<open>p \<in> {a..q}\<close> using that by auto
        have vv0: \<open>vector_variation {p..q} f = 0\<close>
          by (metis V_def add.right_neutral add_left_cancel bv_aq
              \<open>V p = V q\<close> vector_variation_combine p_in)
        have bv_pq: \<open>has_bounded_variation_on f {p..q}\<close>
          using has_bounded_variation_on_subset[OF assms] that by auto
        from vector_variation_const_eq[OF bv_pq is_interval_cc] vv0
        show \<open>f p = f q\<close> using that by force
      qed
      show \<open>f x = f y\<close>
        using core[of x y] core[of y x] that by argo
    qed
    \<comment> \<open>Construct the factor g via Hilbert choice\<close>
    define g where \<open>g v \<equiv> f (SOME x. x \<in> {a..b} \<and> V x = v)\<close> for v
    have g_factor: \<open>f x = g (V x)\<close> if \<open>x \<in> {a..b}\<close> for x
    proof -
      have \<open>\<exists>y. y \<in> {a..b} \<and> V y = V x\<close> using that by auto
      then have \<open>(SOME y. y \<in> {a..b} \<and> V y = V x) \<in> {a..b} \<and>
                 V (SOME y. y \<in> {a..b} \<and> V y = V x) = V x\<close>
        by (rule someI_ex)
      then show ?thesis unfolding g_def using f_eq that by metis
    qed
    \<comment> \<open>Lipschitz property\<close>
    have g_lip: \<open>dist (g u) (g v) \<le> dist u v\<close>
      if \<open>u \<in> S\<close> \<open>v \<in> S\<close> for u v
    proof -
      from that obtain x y where
        x: \<open>x \<in> {a..b}\<close> \<open>u = V x\<close> and y: \<open>y \<in> {a..b}\<close> \<open>v = V y\<close>
        unfolding S_def V_def by auto
      \<comment> \<open>WLOG x \<le> y\<close>
      have lip: \<open>dist (g (V x)) (g (V y)) \<le> dist (V x) (V y)\<close>
        if xy: \<open>x \<le> y\<close> \<open>x \<in> {a..b}\<close> \<open>y \<in> {a..b}\<close> for x y
      proof -
        have bv_ay: \<open>has_bounded_variation_on f {a..y}\<close>
          using has_bounded_variation_on_subset[OF assms] xy(2,3) ab by auto
        have x_in: \<open>x \<in> {a..y}\<close> using xy by auto
        from vector_variation_combine[OF bv_ay x_in]
        have V_split: \<open>V y = V x + vector_variation {x..y} f\<close>
          unfolding V_def .
        have bv_xy: \<open>has_bounded_variation_on f {x..y}\<close>
          using has_bounded_variation_on_subset[OF assms] xy(1,2,3) by auto
        have Vx_le_Vy: \<open>V x \<le> V y\<close>
          using V_split vector_variation_pos_le[OF bv_xy] by linarith
        have \<open>dist (g (V x)) (g (V y)) = dist (f x) (f y)\<close>
          using g_factor xy(2,3) by simp
        also have \<open>\<dots> = norm (f x - f y)\<close> by (simp add: dist_norm)
        also have \<open>\<dots> \<le> vector_variation {x..y} f\<close>
          using vector_variation_ge_norm_function[OF bv_xy] xy(1) by auto
        also have \<open>\<dots> = V y - V x\<close> using V_split by simp
        also have \<open>\<dots> = dist (V x) (V y)\<close> using Vx_le_Vy by (simp add: dist_real_def)
        finally show ?thesis .
      qed
      show ?thesis
      proof (cases \<open>x \<le> y\<close>)
        case True then show ?thesis using lip x y by auto
      next
        case nle: False
        then have \<open>y \<le> x\<close> by auto
        then have \<open>dist (g (V y)) (g (V x)) \<le> dist (V y) (V x)\<close>
          using lip y(1) x(1) by auto
        then show ?thesis using x y by (simp add: dist_commute)
      qed
    qed
    show ?thesis
      using g_factor g_lip unfolding V_def by auto
  qed
  moreover
  have \<open>continuous_on S g\<close> if \<open>\<forall>u \<in> S. \<forall>v \<in> S. dist (g u) (g v) \<le> dist u v\<close> for g
    using continuous_on_iff order_le_less_trans that by blast
  ultimately show ?thesis
    using S_def by blast
qed

lemma factor_continuous_through_variation:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  assumes \<open>a \<le> b\<close>
    and \<open>continuous_on {a..b} f\<close>
    and \<open>has_bounded_variation_on f {a..b}\<close>
  defines \<open>l \<equiv> vector_variation {a..b} f\<close>
  shows \<open>\<exists>g. (\<forall>x \<in> {a..b}. f x = g (vector_variation {a..x} f)) \<and>
             continuous_on {0..l} g \<and>
             (\<forall>u \<in> {0..l}. \<forall>v \<in> {0..l}. dist (g u) (g v) \<le> dist u v) \<and>
             has_bounded_variation_on g {0..l} \<and>
             (\<lambda>x. vector_variation {a..x} f) ` {a..b} = {0..l} \<and>
             g ` {0..l} = f ` {a..b} \<and>
             (\<forall>x \<in> {0..l}. vector_variation {0..x} g = x)\<close>
proof -
  define S where \<open>S \<equiv> (\<lambda>x. vector_variation {a..x} f) ` {a..b}\<close>
  obtain g where
    g_factor: \<open>\<forall>x \<in> {a..b}. f x = g (vector_variation {a..x} f)\<close>
    and g_cont: \<open>continuous_on S g\<close>
    and g_lip: \<open>\<forall>u \<in> S. \<forall>v \<in> S. dist (g u) (g v) \<le> dist u v\<close>
    using factor_through_variation[OF assms(3)] unfolding S_def by blast
  define V where \<open>V \<equiv> \<lambda>x. vector_variation {a..x} f\<close>
  have V_a: \<open>V a = 0\<close>
    unfolding V_def using vector_variation_on_null[of a a f] by simp
  have V_b: \<open>V b = l\<close>
    unfolding V_def l_def by simp
  have V_mono: \<open>V x \<le> V y\<close> if \<open>x \<in> {a..b}\<close> \<open>y \<in> {a..b}\<close> \<open>x \<le> y\<close> for x y
  proof -
    have bv_ay: \<open>has_bounded_variation_on f {a..y}\<close>
      using has_bounded_variation_on_subset[OF assms(3)] that by auto
    have \<open>V y = V x + vector_variation {x..y} f\<close>
      unfolding V_def using vector_variation_combine[OF bv_ay] that by auto
    moreover have \<open>vector_variation {x..y} f \<ge> 0\<close>
      by (rule vector_variation_pos_le[OF has_bounded_variation_on_subset[OF assms(3)]])
         (use that in auto)
    ultimately show ?thesis by linarith
  qed
  have V_cont: \<open>continuous_on {a..b} V\<close>
    unfolding V_def continuous_on_eq_continuous_within
    using vector_variation_continuous[OF assms(3)] assms(2)[unfolded continuous_on_eq_continuous_within]
    by simp
  have S_eq: \<open>S = {0..l}\<close>
  proof (rule antisym)
    show \<open>S \<subseteq> {0..l}\<close>
    proof
      fix v assume \<open>v \<in> S\<close>
      then obtain x where \<open>x \<in> {a..b}\<close> \<open>v = V x\<close> unfolding S_def V_def by auto
      then have \<open>V a \<le> v\<close> \<open>v \<le> V b\<close>
        using V_mono assms(1) by auto
      then show \<open>v \<in> {0..l}\<close> using V_a V_b by auto
    qed
    show \<open>{0..l} \<subseteq> S\<close>
    proof -
      have \<open>connected S\<close>
        unfolding S_def V_def[symmetric]
        using connected_continuous_image[OF V_cont] by auto
      moreover have \<open>0 \<in> S\<close> using V_a assms(1) unfolding S_def V_def by force
      moreover have \<open>l \<in> S\<close> using V_b assms(1) unfolding S_def V_def by force
      ultimately show ?thesis using connected_contains_Icc by blast
    qed
  qed
  have g_bv: \<open>has_bounded_variation_on g {0..l}\<close>
  proof (rule Lipschitz_imp_has_bounded_variation[where B=1])
    show \<open>bounded {(0::real)..l}\<close> by simp
  next
    fix x y :: real assume xy: \<open>x \<in> {0..l}\<close> \<open>y \<in> {0..l}\<close>
    then have \<open>dist (g x) (g y) \<le> dist x y\<close>
      using g_lip S_eq by auto
    then show \<open>norm (g x - g y) \<le> 1 * norm (x - y)\<close>
      by (simp add: dist_norm)
  qed
  have g_image: \<open>g ` {0..l} = f ` {a..b}\<close>
  proof (rule antisym)
    show \<open>g ` {0..l} \<subseteq> f ` {a..b}\<close>
    proof
      fix y assume \<open>y \<in> g ` {0..l}\<close>
      then obtain u where \<open>u \<in> {0..l}\<close> \<open>y = g u\<close> by auto
      then obtain x where \<open>x \<in> {a..b}\<close> \<open>u = V x\<close>
        using S_eq[symmetric] unfolding S_def V_def by auto
      then have \<open>y = f x\<close> using g_factor \<open>y = g u\<close> V_def by auto
      then show \<open>y \<in> f ` {a..b}\<close> using \<open>x \<in> {a..b}\<close> by auto
    qed
    show \<open>f ` {a..b} \<subseteq> g ` {0..l}\<close>
      using S_def S_eq g_factor by blast
  qed
  have g_var: \<open>vector_variation {0..x} g = x\<close> if \<open>x \<in> {0..l}\<close> for x
  proof (rule antisym)
    \<comment> \<open>Upper bound: 1-Lipschitz implies variation \<le> length of interval\<close>
    show \<open>vector_variation {0..x} g \<le> x\<close>
    proof (rule has_bounded_variation_works(2)[OF has_bounded_variation_on_subset[OF g_bv]])
      show \<open>{0..x} \<subseteq> {0..l}\<close> using that by auto
    next
      fix d t assume dt: \<open>d division_of t\<close> \<open>t \<subseteq> {0..x}\<close>
      have \<open>(\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> (\<Sum>k\<in>d. content k)\<close>
      proof (rule sum_mono)
        fix k assume kd: \<open>k \<in> d\<close>
        obtain lk uk where k_eq: \<open>k = {lk..uk}\<close> and lk_le: \<open>lk \<le> uk\<close>
          by (metis atLeastatMost_empty_iff2 box_real(2) division_ofD(3,4) dt(1) kd)
        have k_sub: \<open>k \<subseteq> {0..x}\<close> using division_ofD(2)[OF dt(1) kd] dt(2) by auto
        then have lk_in: \<open>lk \<in> {0..l}\<close> and uk_in: \<open>uk \<in> {0..l}\<close>
          using k_eq lk_le that by auto
        have \<open>norm (g (Sup k) - g (Inf k)) = norm (g uk - g lk)\<close>
          using lk_le k_eq by (simp add: cbox_interval)
        also have \<open>\<dots> \<le> dist (g uk) (g lk)\<close> by (simp add: dist_norm)
        also have \<open>\<dots> \<le> dist uk lk\<close>
          using g_lip lk_in uk_in S_eq by auto
        also have \<open>\<dots> = uk - lk\<close> using lk_le by (simp add: dist_real_def)
        also have \<open>\<dots> = content k\<close> using lk_le k_eq by (simp add: cbox_interval)
        finally show \<open>norm (g (Sup k) - g (Inf k)) \<le> content k\<close> .
      qed
      also have \<open>(\<Sum>k\<in>d. content k) \<le> content (cbox 0 x)\<close>
        using subadditive_content_division[OF dt(1)] dt(2)
        by (simp add: cbox_interval)
      also have \<open>\<dots> = x\<close> using that by (simp add: cbox_interval)
      finally show \<open>(\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> x\<close> .
    qed
  next
    \<comment> \<open>Lower bound: variation of g on {0..x} \<ge> x via factoring through f\<close>
    show \<open>x \<le> vector_variation {0..x} g\<close>
    proof -
      have x_in_S: \<open>x \<in> S\<close> using that S_eq by auto
      then obtain t where t_in: \<open>t \<in> {a..b}\<close> and Vt: \<open>V t = x\<close>
        unfolding S_def V_def by auto
      have bv_at: \<open>has_bounded_variation_on f {a..t}\<close>
        using has_bounded_variation_on_subset[OF assms(3)] t_in by auto
      have mono_V_at: \<open>mono_on {a..t} V\<close>
        unfolding mono_on_def using V_mono t_in by auto
      have g_bv_0x: \<open>has_bounded_variation_on g {V a..V t}\<close>
        using has_bounded_variation_on_subset[OF g_bv] V_a Vt that by auto
      \<comment> \<open>g \<circ> V agrees with f on {a..t}\<close>
      have gV_eq_f: \<open>g (V u) = f u\<close> if \<open>u \<in> {a..t}\<close> for u
        using g_factor t_in that V_def by auto
      \<comment> \<open>Therefore their variations on {a..t} are equal\<close>
      have var_eq: \<open>vector_variation {a..t} (g \<circ> V) = vector_variation {a..t} f\<close>
      proof -
        have eq: \<open>norm ((g \<circ> V) (Sup k) - (g \<circ> V) (Inf k)) = norm (f (Sup k) - f (Inf k))\<close>
          if div: \<open>d division_of s\<close> \<open>s \<subseteq> {a..t}\<close> and kd: \<open>k \<in> d\<close> for d s k
        proof -
          obtain lk uk where \<open>k = cbox lk uk\<close> \<open>k \<noteq> {}\<close>
            using division_ofD(3,4)[OF div(1) kd] by auto
          then have lu: \<open>lk \<le> uk\<close> by force
          then have k_eq: \<open>k = {lk..uk}\<close> and Inf_k: \<open>Inf k = lk\<close> and Sup_k: \<open>Sup k = uk\<close>
            using \<open>k = cbox lk uk\<close> by (auto simp: cbox_interval)
          have \<open>k \<subseteq> {a..t}\<close>
            using division_ofD(2)[OF div(1) kd] div(2) by auto
          then have \<open>Inf k \<in> {a..t}\<close> \<open>Sup k \<in> {a..t}\<close> using lu Inf_k Sup_k k_eq by auto
          then show ?thesis using gV_eq_f by (simp add: comp_def)
        qed

        have sum_eq: \<open>(\<Sum>k\<in>d. norm ((g \<circ> V) (Sup k) - (g \<circ> V) (Inf k))) =
              (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))\<close>
          if \<open>d division_of s\<close> \<open>s \<subseteq> {a..t}\<close> for d s
          by (intro sum.cong refl eq[OF that])
        have \<open>{\<Sum>k\<in>d. norm ((g \<circ> V) (Sup k) - (g \<circ> V) (Inf k)) |d.
                \<exists>s. d division_of s \<and> s \<subseteq> {a..t}} =
              {\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) |d.
                \<exists>s. d division_of s \<and> s \<subseteq> {a..t}}\<close>
          (is \<open>?L = ?R\<close>)
        proof (rule antisym; rule subsetI)
          fix v assume \<open>v \<in> ?L\<close>
          then obtain d s where ds: \<open>d division_of s\<close> \<open>s \<subseteq> {a..t}\<close>
            and \<open>v = (\<Sum>k\<in>d. norm ((g \<circ> V) (Sup k) - (g \<circ> V) (Inf k)))\<close> by auto
          then have \<open>v = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))\<close>
            using sum_eq[OF ds] by simp
          then show \<open>v \<in> ?R\<close> using ds by blast
        next
          fix v assume \<open>v \<in> ?R\<close>
          then obtain d s where ds: \<open>d division_of s\<close> \<open>s \<subseteq> {a..t}\<close>
            and \<open>v = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))\<close> by auto
          then have \<open>v = (\<Sum>k\<in>d. norm ((g \<circ> V) (Sup k) - (g \<circ> V) (Inf k)))\<close>
            using sum_eq[OF ds] by simp
          then show \<open>v \<in> ?L\<close> using ds by blast
        qed
        then show ?thesis
          unfolding vector_variation_def set_variation_def comp_def by auto
      qed
      \<comment> \<open>Composition lemma: variation of g \<circ> V on {a..t} \<le> variation of g on {V a..V t}\<close>
      have \<open>vector_variation {a..t} (g \<circ> V) \<le> vector_variation {V a..V t} g\<close>
        using has_bounded_variation_compose_monotone(2)[OF g_bv_0x mono_V_at] .
      then have \<open>vector_variation {a..t} f \<le> vector_variation {0..x} g\<close>
        using var_eq V_a Vt by simp
      moreover have \<open>x = vector_variation {a..t} f\<close>
        using Vt[symmetric] by (simp add: V_def)
      ultimately show ?thesis by linarith
    qed
  qed
  show ?thesis
    by (metis S_def S_eq g_bv g_cont g_factor g_image g_lip g_var)
qed

text \<open>Arc-length reparametrization and existence of shortest paths.\<close>

lemma arc_length_reparametrization:
  fixes g :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  assumes \<open>rectifiable_path g\<close>
  shows \<open>\<exists>h. rectifiable_path h \<and>
             path_image h = path_image g \<and>
             pathstart h = pathstart g \<and>
             pathfinish h = pathfinish g \<and>
             path_length h = path_length g \<and>
             (arc g \<longrightarrow> arc h) \<and>
             (simple_path g \<longrightarrow> simple_path h) \<and>
             (\<forall>t \<in> {0..1}. path_length (subpath 0 t h) = path_length g * t) \<and>
             (\<forall>x \<in> {0..1}. \<forall>y \<in> {0..1}.
                dist (h x) (h y) \<le> path_length g * dist x y)\<close>
  sorry

end


