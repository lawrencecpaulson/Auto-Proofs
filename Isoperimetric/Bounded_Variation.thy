theory Bounded_Variation
  imports "HOL-Analysis.Analysis" Isar_Explore
"HOL-ex.Sketch_and_Explore" 
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

lemma has_bounded_setvariation_on_works:
  assumes "has_bounded_setvariation_on f s"
  shows "(\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
            (\<Sum>k\<in>d. norm (f k)) \<le> set_variation s f)"
    and "(\<And>B. (\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
                  (\<Sum>k\<in>d. norm (f k)) \<le> B) \<Longrightarrow>
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

lemma has_bounded_variation_on_works:
  assumes "has_bounded_variation_on f s"
  shows "(\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
            (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> vector_variation s f)"
    and "(\<And>B. (\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
                  (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B) \<Longrightarrow>
            vector_variation s f \<le> B)"
  using has_bounded_setvariation_on_works[of "\<lambda>k. f (Sup k) - f (Inf k)" s]
    assms[unfolded has_bounded_variation_on_def]
  unfolding vector_variation_def by auto

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
  proof (rule has_bounded_variation_on_works(2)[OF bvs])
    fix ds s' assume ds: "ds division_of s'" "s' \<subseteq> s"
    show "(\<Sum>k\<in>ds. norm (f (Sup k) - f (Inf k)))
          \<le> vector_variation (s \<union> t) f - vector_variation t f"
    proof -
      have "vector_variation t f
            \<le> vector_variation (s \<union> t) f - (\<Sum>k\<in>ds. norm (f (Sup k) - f (Inf k)))"
      proof (rule has_bounded_variation_on_works(2)[OF bvt])
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
            using has_bounded_variation_on_works(1)[OF fst]
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
      using has_bounded_setvariation_on_works(1)[OF bdd] by auto
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
      using R by (intro has_bounded_setvariation_on_works(2))
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
      using has_bounded_variation_on_works(1)[OF bdd] by auto
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
    proof (rule has_bounded_variation_on_works(2)[OF bv])
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
      have "\<exists>j k. j \<noteq> {} \<and> k \<noteq> {} \<and> (\<exists>a b. j = {a..b}) \<and> (\<exists>a b. k = {a..b}) \<and> j \<subseteq> s \<and> k \<subseteq> t \<and> (j \<subseteq> i \<or> interior j = {}) \<and> (k \<subseteq> i \<or> interior k = {}) \<and> norm (f (Sup i) - f (Inf i)) \<le> norm (f (Sup j) - f (Inf j)) + norm (f (Sup k) - f (Inf k))"
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
        then have "{a,b} \<subseteq> s \<union> t"
          by (metis Un_insert_left Un_insert_right atLeastatMost_empty_iff2 ne
              empty_subsetI iab insert_subset ivl_disj_un_singleton(5,6) subset_iff)
        then consider "a \<in> s \<and> b \<in> s" | "a \<in> s \<and> b \<in> t" | "a \<in> t \<and> b \<in> s" | "a \<in> t \<and> b \<in> t"
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
          case 2
          show ?thesis
          proof (cases "s \<inter> t = {}")
            case True
            \<comment> \<open>Separated case: {a..b} connected, a \<in> s, b \<in> t, but s \<union> t not connected — contradiction\<close>
            show ?thesis
            proof -
              have sep: "s \<inter> closure t = {} \<and> t \<inter> closure s = {}" using clo True by blast
              have sub: "{a..b} \<subseteq> s \<union> t" using isub usub iab by blast
              have "a \<in> s" "b \<in> t" using 2 by auto
              \<comment> \<open>s \<inter> closure t = {} means every point in s is away from t, and vice versa\<close>
              \<comment> \<open>Use that - (closure t) is open, contains s, similarly - (closure s) open, contains t\<close>
              have "s \<inter> {a..b} \<noteq> {}" using \<open>a \<in> s\<close> \<open>a \<in> {a..b}\<close> by blast
              have "t \<inter> {a..b} \<noteq> {}" using \<open>b \<in> t\<close> \<open>b \<in> {a..b}\<close> by blast
              have "False"
              proof -
                have o1: "open (- closure t)" and o2: "open (- closure s)"
                  using open_Compl closed_closure by blast+
                have s_sub: "s \<subseteq> - closure t" and t_sub: "t \<subseteq> - closure s"
                  using sep by blast+
                have "{a..b} \<subseteq> (- closure t) \<union> (- closure s)"
                  using sub s_sub t_sub by blast
                moreover have "(- closure t) \<inter> (- closure s) \<inter> {a..b} = {}"
                  using sub closure_subset by blast
                moreover have "(- closure t) \<inter> {a..b} \<noteq> {}"
                  using \<open>a \<in> s\<close> s_sub \<open>a \<in> {a..b}\<close> by blast
                moreover have "(- closure s) \<inter> {a..b} \<noteq> {}"
                  using \<open>b \<in> t\<close> t_sub \<open>b \<in> {a..b}\<close> by blast
                ultimately show False
                  by (meson connectedD connected_Icc o1 o2)
              qed
              then show ?thesis by blast
            qed
          next
            case False
            \<comment> \<open>Overlapping case: pick c \<in> s \<inter> t \<inter> {a..b} as splitting point\<close>
            show ?thesis
            proof -
              obtain c where "c \<in> s" "c \<in> t" using False by blast
              with "2" \<open>is_interval s\<close> \<open>is_interval t\<close> 
              have c': "max a (min c b) \<in> s \<and> max a (min c b) \<in> t \<and> max a (min c b) \<in> {a..b}"
                by (smt (verit) ab atLeastAtMost_iff max.absorb1 max.absorb2 mem_is_interval_1_I
                    min_le_iff_disj)
              define c' where "c' = max a (min c b)"
              then have c'_s: "c' \<in> s" and c'_t: "c' \<in> t" and c'_ab: "a \<le> c'" "c' \<le> b"
                using c' by auto
              have j_sub_s: "{a..c'} \<subseteq> s"
                using 2 c'_s \<open>is_interval s\<close> interval_subset_is_interval[of s a c']
                by (auto simp: box_real)
              have k_sub_t: "{c'..b} \<subseteq> t"
                using 2 c'_t \<open>is_interval t\<close> interval_subset_is_interval[of t c' b]
                by (auto simp: box_real)
              have j_sub_i: "{a..c'} \<subseteq> {a..b}" and k_sub_i: "{c'..b} \<subseteq> {a..b}" 
                using c'_ab ab by auto
              have "norm (f b - f a) \<le> norm (f c' - f a) + norm (f b - f c')"
                by (simp add: order_trans [OF _ norm_triangle_ineq])
              then show ?thesis
                apply (rule_tac x="{a..c'}" in exI)
                apply (rule_tac x="{c'..b}" in exI)
                using c'_ab ab j_sub_s k_sub_t j_sub_i k_sub_i iab ne
                by (auto simp: iSup iInf)
            qed
          qed
        next
          case 3 \<comment> \<open>a \<in> t, b \<in> s — symmetric to case 2\<close>
          show ?thesis
          proof (cases "s \<inter> t = {}")
            case True
            \<comment> \<open>Separated case: same connectedness contradiction\<close>
            show ?thesis
            proof -
              have sep: "s \<inter> closure t = {} \<and> t \<inter> closure s = {}" using clo True by blast
              have sub: "{a..b} \<subseteq> s \<union> t" using isub usub iab by blast
              have conn: "connected {a..b::real}" by (simp add: connected_iff_interval)
              have "a \<in> t" "b \<in> s" using 3 by auto
              have "a \<in> {a..b}" "b \<in> {a..b}" using ab by auto
              have "False"
              proof -
                have o1: "open (- closure t)" and o2: "open (- closure s)"
                  using open_Compl closed_closure by blast+
                have s_sub: "s \<subseteq> - closure t" and t_sub: "t \<subseteq> - closure s"
                  using sep by blast+
                have "{a..b} \<subseteq> (- closure t) \<union> (- closure s)"
                  using sub s_sub t_sub by blast
                moreover have "(- closure t) \<inter> (- closure s) \<inter> {a..b} = {}"
                  using sub closure_subset[of s] closure_subset[of t] by blast
                moreover have "(- closure s) \<inter> {a..b} \<noteq> {}"
                  using \<open>a \<in> t\<close> t_sub \<open>a \<in> {a..b}\<close> by blast
                moreover have "(- closure t) \<inter> {a..b} \<noteq> {}"
                  using \<open>b \<in> s\<close> s_sub \<open>b \<in> {a..b}\<close> by blast
                ultimately show False
                  using conn unfolding connected_def by (metis o1 o2)
              qed
              then show ?thesis by blast
            qed
          next
            case False
            \<comment> \<open>Overlapping case: pick c \<in> s \<inter> t, split at c' = max a (min c b)\<close>
            show ?thesis
            proof -
              obtain c where "c \<in> s" "c \<in> t" using False by blast
              with 3 \<open>is_interval s\<close> \<open>is_interval t\<close> 
              have c': "max a (min c b) \<in> s \<and> max a (min c b) \<in> t \<and> max a (min c b) \<in> {a..b}"
                 by (smt (verit) ab atLeastAtMost_iff max.absorb1 max.absorb2 mem_is_interval_1_I
                    min_le_iff_disj)
              define c' where "c' = max a (min c b)"
              then have c'_s: "c' \<in> s" and c'_t: "c' \<in> t" and c'_ab: "a \<le> c'" "c' \<le> b"
                using c' by auto
              have j_sub_s: "{c'..b} \<subseteq> s"
                using 3 c'_s \<open>is_interval s\<close> interval_subset_is_interval[of s c' b]
                by (auto simp: box_real)
              have k_sub_t: "{a..c'} \<subseteq> t"
                using 3 c'_t \<open>is_interval t\<close> interval_subset_is_interval[of t a c']
                by (auto simp: box_real)
              have j_sub_i: "{c'..b} \<subseteq> {a..b}" and k_sub_i: "{a..c'} \<subseteq> {a..b}" 
                using c'_ab ab by auto
              have "norm (f b - f a) \<le> norm (f b - f c') + norm (f c' - f a)"
                by (simp add: order_trans [OF _ norm_triangle_ineq])
              then show ?thesis
                apply (rule_tac x="{c'..b}" in exI)
                apply (rule_tac x="{a..c'}" in exI)
                using c'_ab ab j_sub_s k_sub_t j_sub_i k_sub_i iab ne
                by (auto simp: iSup iInf)
            qed
          qed
        next
          case 4 \<comment> \<open>Both endpoints in t\<close>
          show ?thesis
            apply (rule exI[where x="{p..p}"])
            apply (rule exI[where x="{a..b}"])
            using 4 ne \<open>p \<in> s\<close> iab ab \<open>is_interval t\<close> interval_subset_is_interval[of _ a b] 
            by (force simp: iSup iInf interior_atLeastAtMost_real)
        qed
      qed
      show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> vector_variation s f + vector_variation t f"
        sorry
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
        sorry
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

