theory Bounded_Variation
  imports "HOL-Analysis.Analysis"
begin

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

lemma has_bounded_variation_on_combine:
  assumes "a \<le> c" "c \<le> b"
  shows "has_bounded_variation_on f {a..b} \<longleftrightarrow>
    has_bounded_variation_on f {a..c} \<and> has_bounded_variation_on f {c..b}"
proof
  assume bv: "has_bounded_variation_on f {a..b}"
  have "{a..c} \<subseteq> {a..b}" "{c..b} \<subseteq> {a..b}" using assms by auto
  then show "has_bounded_variation_on f {a..c} \<and> has_bounded_variation_on f {c..b}"
    using has_bounded_variation_on_subset[OF bv] by auto
next
  assume bvs: "has_bounded_variation_on f {a..c} \<and> has_bounded_variation_on f {c..b}"
  then have bv_ac: "has_bounded_variation_on f {a..c}"
    and bv_cb: "has_bounded_variation_on f {c..b}" by auto
  show "has_bounded_variation_on f {a..b}"
    unfolding has_bounded_variation_on_interval
  proof -
    let ?g = "\<lambda>k. f (Sup k) - f (Inf k)"
    from bv_ac obtain B1 where B1: "\<And>d. d division_of {a..c} \<Longrightarrow>
      (\<Sum>k\<in>d. norm (?g k)) \<le> B1"
      unfolding has_bounded_variation_on_interval by blast
    from bv_cb obtain B2 where B2: "\<And>d. d division_of {c..b} \<Longrightarrow>
      (\<Sum>k\<in>d. norm (?g k)) \<le> B2"
      unfolding has_bounded_variation_on_interval by blast
    show "\<exists>B. \<forall>d. d division_of {a..b} \<longrightarrow> (\<Sum>k\<in>d. norm (?g k)) \<le> B"
    proof (intro exI[of _ "B1 + B2"] allI impI)
      fix d assume div_d: "d division_of {a..b}"
      have fin_d: "finite d" using division_of_finite[OF div_d] .
      \<comment> \<open>Use division_split to split d at c\<close>
      have div_d_cbox: "d division_of cbox a b"
        using div_d by (simp add: cbox_interval)
      have one_Basis: "(1::real) \<in> Basis" by simp
      define d1 where "d1 = {l \<inter> {x. x \<bullet> 1 \<le> c} | l. l \<in> d \<and> l \<inter> {x. x \<bullet> 1 \<le> c} \<noteq> {}}"
      define d2 where "d2 = {l \<inter> {x. c \<le> x \<bullet> 1} | l. l \<in> d \<and> l \<inter> {x. c \<le> x \<bullet> 1} \<noteq> {}}"
      have d1_div: "d1 division_of cbox a b \<inter> {x. x \<bullet> 1 \<le> c}"
        unfolding d1_def using division_split(1)[OF div_d_cbox one_Basis, of c] .
      have d2_div: "d2 division_of cbox a b \<inter> {x. c \<le> x \<bullet> 1}"
        unfolding d2_def using division_split(2)[OF div_d_cbox one_Basis, of c] .
      \<comment> \<open>Simplify the split intervals\<close>
      have inner_simp: "\<And>x::real. x \<bullet> 1 = x" by simp
      have cbox_left: "cbox a b \<inter> {x::real. x \<bullet> 1 \<le> c} = {a..c}"
        using assms by (auto simp: cbox_interval)
      have cbox_right: "cbox a b \<inter> {x::real. c \<le> x \<bullet> 1} = {c..b}"
        using assms by (auto simp: cbox_interval)
      have d1_div': "d1 division_of {a..c}"
        using d1_div cbox_left by simp
      have d2_div': "d2 division_of {c..b}"
        using d2_div cbox_right by simp
      \<comment> \<open>Show \<Sum>_d \<le> \<Sum>_{d1} + \<Sum>_{d2} directly\<close>
      have key_ineq: "(\<Sum>k\<in>d. norm (?g k)) \<le> (\<Sum>k\<in>d1. norm (?g k)) + (\<Sum>k\<in>d2. norm (?g k))"
      proof -
        have fin_d1: "finite d1" using division_of_finite[OF d1_div'] .
        have fin_d2: "finite d2" using division_of_finite[OF d2_div'] .
        \<comment> \<open>For each k \<in> d, get its interval endpoints\<close>
        have k_props: "\<And>k. k \<in> d \<Longrightarrow> \<exists>u v. k = {u..v} \<and> u \<le> v"
        proof -
          fix k assume kd: "k \<in> d"
          from division_ofD(4)[OF div_d kd] obtain u v where "k = cbox u v" by auto
          moreover have "k \<noteq> {}" using division_ofD(3)[OF div_d kd] .
          ultimately show "\<exists>u v. k = {u..v} \<and> u \<le> v" by (auto simp: cbox_interval)
        qed
        \<comment> \<open>For each k \<in> d, the triangle inequality at c\<close>
        have tri: "norm (?g k) \<le> norm (f (min (Sup k) c) - f (Inf k)) +
                                   norm (f (Sup k) - f (max (Inf k) c))"
          if kd: "k \<in> d" for k
        proof -
          obtain u v where kuv: "k = {u..v}" and uv: "u \<le> v" using k_props[OF kd] by auto
          have sup_k: "Sup k = v" and inf_k: "Inf k = u"
            using kuv uv by (simp_all add: interval_bounds_real)
          show ?thesis
          proof (cases "u \<le> c \<and> c \<le> v")
            case True
            then have "min v c = c" "max u c = c" by auto
            then show ?thesis unfolding sup_k inf_k
              using norm_triangle_ineq[of "f c - f u" "f v - f c"] by simp
          next
            case False
            then show ?thesis
            proof (cases "v \<le> c")
              case True then show ?thesis unfolding sup_k inf_k using uv by auto
            next
              case False
              then have "c \<le> u" using \<open>\<not> (u \<le> c \<and> c \<le> v)\<close> by (cases "u \<le> c") auto
              then show ?thesis unfolding sup_k inf_k using uv by auto
            qed
          qed
        qed
        \<comment> \<open>Key observation: for k \<in> d with k = {u..v},
            k \<inter> {x. x \<le> c} = {u..min v c} (non-empty iff u \<le> c)
            and Sup/Inf of this piece give the matching terms\<close>
        \<comment> \<open>Define the left-projection map\<close>
        define \<phi>1 where "\<phi>1 k = k \<inter> {x::real. x \<le> c}" for k
        define \<phi>2 where "\<phi>2 k = k \<inter> {x::real. c \<le> x}" for k
        have \<phi>1_d1: "\<phi>1 ` {k \<in> d. \<phi>1 k \<noteq> {}} = d1"
          unfolding \<phi>1_def d1_def by (auto simp: inner_simp)
        have \<phi>2_d2: "\<phi>2 ` {k \<in> d. \<phi>2 k \<noteq> {}} = d2"
          unfolding \<phi>2_def d2_def by (auto simp: inner_simp)
        \<comment> \<open>When \<phi>1 k is non-empty, ?g(\<phi>1 k) = f(min(Sup k, c)) - f(Inf k)\<close>
        have \<phi>1_g: "?g (\<phi>1 k) = f (min (Sup k) c) - f (Inf k)"
          if kd: "k \<in> d" and ne: "\<phi>1 k \<noteq> {}" for k
        proof -
          obtain u v where kuv: "k = {u..v}" and uv: "u \<le> v" using k_props[OF kd] by auto
          have "u \<le> c" using ne kuv by (auto simp: \<phi>1_def)
          then have "\<phi>1 k = {u..min v c}" using kuv uv by (auto simp: \<phi>1_def)
          moreover have "u \<le> min v c" using \<open>u \<le> c\<close> uv by auto
          ultimately have "Sup (\<phi>1 k) = min v c" "Inf (\<phi>1 k) = u"
            by (simp_all add: interval_bounds_real)
          moreover have "Sup k = v" "Inf k = u" using kuv uv by (simp_all add: interval_bounds_real)
          ultimately show ?thesis by simp
        qed
        \<comment> \<open>When \<phi>2 k is non-empty, ?g(\<phi>2 k) = f(Sup k) - f(max(Inf k, c))\<close>
        have \<phi>2_g: "?g (\<phi>2 k) = f (Sup k) - f (max (Inf k) c)"
          if kd: "k \<in> d" and ne: "\<phi>2 k \<noteq> {}" for k
        proof -
          obtain u v where kuv: "k = {u..v}" and uv: "u \<le> v" using k_props[OF kd] by auto
          have "c \<le> v" using ne kuv by (auto simp: \<phi>2_def)
          then have "\<phi>2 k = {max u c..v}" using kuv uv by (auto simp: \<phi>2_def)
          moreover have "max u c \<le> v" using \<open>c \<le> v\<close> uv by auto
          ultimately have "Sup (\<phi>2 k) = v" "Inf (\<phi>2 k) = max u c"
            by (simp_all add: interval_bounds_real)
          moreover have "Sup k = v" "Inf k = u" using kuv uv by (simp_all add: interval_bounds_real)
          ultimately show ?thesis by simp
        qed
        \<comment> \<open>For non-straddling elements, the "wrong side" term is zero\<close>
        have left_only: "f (Sup k) - f (max (Inf k) c) = 0"
          if kd: "k \<in> d" and left: "\<phi>2 k = {}" for k
        proof -
          obtain u v where kuv: "k = {u..v}" and uv: "u \<le> v" using k_props[OF kd] by auto
          have "v < c" using left kuv uv by (auto simp: \<phi>2_def)
          then have "Sup k = v" "max (Inf k) c = c" "max u c = c"
            using kuv uv by (simp_all add: interval_bounds_real)
          \<comment> \<open>But v < c, so Sup k = v and max(Inf k, c) = c. The term is f(v) - f(c), not zero!\<close>
          then show ?thesis
          sorry
        qed
      qed
    qed
  qed
qed


lemma vector_variation_combine:
  assumes bv: "has_bounded_variation_on f {a..b}" and cab: "c \<in> {a..b}"
  shows "vector_variation {a..b} f = vector_variation {a..c} f + vector_variation {c..b} f"
proof -
  let ?g = "\<lambda>k. f (Sup k) - f (Inf k)"
  from cab have ac: "a \<le> c" and cb: "c \<le> b" by auto
  have bv_ac: "has_bounded_variation_on f {a..c}"
    using has_bounded_variation_on_subset[OF bv] cab by auto
  have bv_cb: "has_bounded_variation_on f {c..b}"
    using has_bounded_variation_on_subset[OF bv] cab by auto
      \<comment> \<open>\<ge> direction: combine divisions of {a..c} and {c..b}\<close>
  have ge: "vector_variation {a..c} f + vector_variation {c..b} f \<le> vector_variation {a..b} f"
  proof -
    define Sab where "Sab = {(\<Sum>k\<in>d. norm (?g k)) | d. d division_of {a..b}}"
    define Sac where "Sac = {(\<Sum>k\<in>d. norm (?g k)) | d. d division_of {a..c}}"
    define Scb where "Scb = {(\<Sum>k\<in>d. norm (?g k)) | d. d division_of {c..b}}"
    have vvab: "vector_variation {a..b} f = Sup Sab"
      using vector_variation_on_interval[OF bv] unfolding Sab_def .
    have vvac: "vector_variation {a..c} f = Sup Sac"
      using vector_variation_on_interval[OF bv_ac] unfolding Sac_def .
    have vvcb: "vector_variation {c..b} f = Sup Scb"
      using vector_variation_on_interval[OF bv_cb] unfolding Scb_def .
    have bdd_Sab: "bdd_above Sab"
    proof -
      from bv obtain M where "\<forall>d. d division_of {a..b} \<longrightarrow> (\<Sum>k\<in>d. norm (?g k)) \<le> M"
        unfolding has_bounded_variation_on_interval by auto
      then show ?thesis unfolding Sab_def bdd_above_def by auto
    qed
      \<comment> \<open>Every sum over d1 \<union> d2 is \<le> Sup Sab\<close>
    have key: "s1 + s2 \<le> Sup Sab" if s1_in: "s1 \<in> Sac" and s2_in: "s2 \<in> Scb" for s1 s2
    proof -
      from s1_in obtain d1 where d1_div: "d1 division_of {a..c}"
        and s1_eq: "s1 = (\<Sum>k\<in>d1. norm (?g k))" unfolding Sac_def by auto
      from s2_in obtain d2 where d2_div: "d2 division_of {c..b}"
        and s2_eq: "s2 = (\<Sum>k\<in>d2. norm (?g k))" unfolding Scb_def by auto
      have disj_int: "interior {a..c} \<inter> interior {c..b} = {}"
        by (auto simp: interior_atLeastAtMost_real)
      have union_eq: "{a..c} \<union> {c..b} = {a..b}"
        using ivl_disj_un_two_touch(4)[OF ac cb] .
      have d_div: "d1 \<union> d2 division_of {a..b}"
        using division_disjoint_union[OF d1_div d2_div disj_int] union_eq by simp
          \<comment> \<open>Elements of d1 and d2 are disjoint as sets of intervals\<close>
      have d1d2_disj: "d1 \<inter> d2 = {}"
      proof (rule ccontr)
        assume "d1 \<inter> d2 \<noteq> {}"
        then obtain k where kd1: "k \<in> d1" and kd2: "k \<in> d2" by auto
        have "k \<subseteq> {a..c}" using division_ofD(2)[OF d1_div kd1] .
        have "k \<subseteq> {c..b}" using division_ofD(2)[OF d2_div kd2] .
        have "k \<noteq> {}" using division_ofD(3)[OF d1_div kd1] .
        then have "interior k \<noteq> {} \<or> (\<exists>x. k = {x})"
          using division_ofD(4)[OF d1_div kd1]
          by auto
        then show False
        proof
          assume "interior k \<noteq> {}"
          then have "interior k \<subseteq> interior {a..c}" "interior k \<subseteq> interior {c..b}"
            using \<open>k \<subseteq> {a..c}\<close> \<open>k \<subseteq> {c..b}\<close> interior_mono by blast+
          then have "interior k \<subseteq> interior {a..c} \<inter> interior {c..b}"
            by blast
          then have "interior k = {}" using disj_int by auto
          with \<open>interior k \<noteq> {}\<close> show False by simp
        next
          assume "\<exists>x. k = {x}"
          then obtain x where kx: "k = {x}" by auto
          then have "x \<in> {a..c}" "x \<in> {c..b}" using \<open>k \<subseteq> {a..c}\<close> \<open>k \<subseteq> {c..b}\<close> by auto
          then have "x = c" by auto
          then have "k = {c}" using kx by auto
              \<comment> \<open>Both d1 and d2 contain {c}; but their interiors in {a..c} and {c..b} are disjoint\<close>
              \<comment> \<open>Actually this is possible, so d1 \<inter> d2 can be nonempty (containing {c}).\<close>
              \<comment> \<open>We handle this below.\<close>
          show False sorry
        qed
      qed
      oops

subsection \<open>Composition and monotonicity\<close>

lemma has_bounded_variation_compose_increasing:
  assumes "has_bounded_variation_on f {a..b}"
    and mono: "\<And>x y. x \<in> {c..d} \<Longrightarrow> y \<in> {c..d} \<Longrightarrow> x \<le> y \<Longrightarrow> g x \<le> g y"
    and img: "g ` {c..d} \<subseteq> {a..b}"
  shows "has_bounded_variation_on (f \<circ> g) {c..d}"
  sorry

lemma lipschitz_imp_has_bounded_variation:
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

lemma lipschitz_vector_variation:
  assumes "\<And>x y. x \<in> {a..b} \<Longrightarrow> y \<in> {a..b} \<Longrightarrow> norm (f x - f y) \<le> B * \<bar>x - y\<bar>"
  shows "vector_variation {a..b} f \<le> B * (b - a)"
  sorry

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
  assumes "\<And>x y. x \<in> {a..b} \<Longrightarrow> y \<in> {a..b} \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
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
    have "f l \<le> f u" using assms \<open>l \<in> {a..b}\<close> \<open>u \<in> {a..b}\<close> lu by auto
    then have "f l \<bullet> i \<le> f u \<bullet> i" using iBasis eucl_le by metis
    have "Inf k = l" "Sup k = u" using lu k_eq by (auto simp: cbox_interval)
    then show "\<bar>(f (Sup k) - f (Inf k)) \<bullet> i\<bar> = f (Sup k) \<bullet> i - f (Inf k) \<bullet> i"
      using \<open>f l \<bullet> i \<le> f u \<bullet> i\<close> by (simp add: inner_diff_left abs_of_nonneg)
  qed
  also have "\<dots> \<le> (\<Sum>i\<in>Basis. \<bar>(f b - f a) \<bullet> i\<bar>)"
  proof (intro sum_mono)
    fix i::'a assume iBasis: "i \<in> Basis"
    have ab: "a \<le> b"
    proof -
      from div_d obtain k where "k \<in> d" "k \<subseteq> {a..b}" "k \<noteq> {}"
        using Union_empty division_ofD(2,3,6) ex_in_conv
apply (auto simp: )
        by (metis Union_empty division_ofD(2,3,6) ex_in_conv)
      then show ?thesis by auto
    qed
    have tele: "(\<Sum>k\<in>d. (f (Sup k) \<bullet> i - f (Inf k) \<bullet> i)) = f b \<bullet> i - f a \<bullet> i"
      using division_telescope_eq[OF div_d ab, of "\<lambda>x. f x \<bullet> i"] by simp
    also have "\<dots> \<le> \<bar>(f b - f a) \<bullet> i\<bar>" by (simp add: inner_diff_left)
    finally show "(\<Sum>k\<in>d. (f (Sup k) \<bullet> i - f (Inf k) \<bullet> i)) \<le> \<bar>(f b - f a) \<bullet> i\<bar>" .
  qed
  also have "\<dots> \<le> (\<Sum>i::'a\<in>Basis. norm (f b - f a))"
    by (intro sum_mono) (auto simp: Basis_le_norm)
  also have "\<dots> = DIM('a) * norm (f b - f a)"
    by simp
  finally show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> DIM('a) * norm (f b - f a)" .
qed

lemma increasing_vector_variation:
  fixes f :: "real \<Rightarrow> real"
  assumes mono: "\<And>x y. x \<in> {a..b} \<Longrightarrow> y \<in> {a..b} \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
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
  have fa_le_fb: "f a \<le> f b" using mono ab by auto
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
      then have "f l \<le> f u" using mono lu by auto
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

subsection \<open>Continuity of vector variation\<close>

lemma vector_variation_continuous:
  assumes "continuous_on {a..b} f" "has_bounded_variation_on f {a..b}"
  shows "continuous_on {a..b} (\<lambda>x. vector_variation {a..x} f)"
  sorry

lemma vector_variation_minus_function_monotone:
  assumes "has_bounded_variation_on f {a..b}" "x \<in> {a..b}" "y \<in> {a..b}" "x \<le> y"
  shows "norm (f y - f x) \<le> vector_variation {x..y} f"
    and "vector_variation {a..x} f - norm (f x - f a) \<le>
      vector_variation {a..y} f - norm (f y - f a)"
proof -
  show "norm (f y - f x) \<le> vector_variation {x..y} f" sorry
  show "vector_variation {a..x} f - norm (f x - f a) \<le>
    vector_variation {a..y} f - norm (f y - f a)" sorry
qed

subsection \<open>Factoring through variation\<close>

lemma factor_continuous_through_variation:
  assumes "a \<le> b" "continuous_on {a..b} f"
    "has_bounded_variation_on f {a..b}"
    "vector_variation {a..b} f = l"
  shows "\<exists>g. (\<forall>x \<in> {a..b}. f x = g (vector_variation {a..x} f)) \<and>
    continuous_on {0..l} g \<and>
    (\<forall>u \<in> {0..l}. \<forall>v \<in> {0..l}. dist (g u) (g v) \<le> dist u v) \<and>
    has_bounded_variation_on g {0..l} \<and>
    (\<lambda>x. vector_variation {a..x} f) ` {a..b} = {0..l} \<and>
    g ` {0..l} = f ` {a..b} \<and>
    (\<forall>x \<in> {0..l}. vector_variation {0..x} g = x)"
  sorry

end

