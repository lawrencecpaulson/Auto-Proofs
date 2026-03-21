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

subsection \<open>Basic properties\<close>

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

lemma vector_variation_combine:
  assumes "has_bounded_variation_on f {a..b}" "c \<in> {a..b}"
  shows "vector_variation {a..b} f = vector_variation {a..c} f + vector_variation {c..b} f"
  sorry

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

lemma division_telescope_le:
  fixes g :: "real \<Rightarrow> real"
  assumes div_d: "d division_of {a..b}"
    and mono: "\<And>x y. x \<in> {a..b} \<Longrightarrow> y \<in> {a..b} \<Longrightarrow> x \<le> y \<Longrightarrow> g x \<le> g y"
  shows "(\<Sum>k\<in>d. (g (Sup k) - g (Inf k))) \<le> g b - g a"
proof (cases "a < b")
  case True
  show ?thesis 
    using div_d
  proof (induction "card d" arbitrary: d a b rule: less_induct)
    case less
    have fin_d: "finite d" using division_of_finite[OF less.prems] .
    show ?case
    proof (cases "card d \<le> 1")
      case True
      then consider "d = {}" | "\<exists>k. d = {k}" using card_le_Suc0_iff_eq[of d] fin_d by auto
      then show ?thesis
      proof cases
        case 1 then show ?thesis 
          apply (simp add: )
          by simp
      next
        case 2
        then obtain k where dk: "d = {k}" by auto
        then have "k = {a..b}" using less.prems
          by (simp add: division_of_def)
        then have "Inf k = a" "Sup k = b"
          using division_ofD(4)[OF less.prems] dk by (auto simp: cbox_interval)
        then show ?thesis using dk by simp
      qed
    next
      case False
      then have "card d \<ge> 2" by linarith
          \<comment> \<open>Find the leftmost interval\<close>
      define l_min where "l_min = Min (Inf ` d)"
      have d_ne: "d \<noteq> {}" using False by auto
      have "l_min \<in> Inf ` d" unfolding l_min_def using d_ne fin_d by auto
      then obtain k0 where k0d: "k0 \<in> d" and k0_inf: "Inf k0 = l_min" by auto
      from division_ofD(2,4)[OF less.prems k0d] obtain l0 u0 where
        k0_eq: "k0 = cbox l0 u0" and k0_ne: "k0 \<noteq> {}"
        by (metis cbox_division_memE k0d less.prems)
      then have l0u0: "l0 \<le> u0"
        by fastforce
      have k0_inf': "Inf k0 = l0" and k0_sup: "Sup k0 = u0"
        using l0u0 k0_eq by (auto simp: cbox_interval)
      have l0_eq_a: "l0 = a"
      proof -
        have "k0 \<subseteq> {a..b}" using division_ofD(2)[OF less.prems k0d] by auto
        then have "a \<le> l0" using l0u0 k0_eq by (auto simp: cbox_interval)
        moreover have "l0 \<le> a"
        proof -
          have "a \<in> {a..b}" using division_ofD(4)[OF less.prems] d_ne
            using less.prems by fastforce
          then obtain k' where k'd: "k' \<in> d" and "a \<in> k'"
            using less.prems by blast
          from division_ofD(2,4)[OF less.prems k'd] obtain l' u' where
            k'_eq: "k' = cbox l' u'" and "k' \<noteq> {}"
            using \<open>a \<in> k'\<close> by blast
          then have "l' \<le> u'"
            by fastforce
          have "a \<in> {l'..u'}" using \<open>a \<in> k'\<close> k'_eq by (simp add: cbox_interval)
          then have "l' \<le> a" by auto
          have "Inf k' = l'" using \<open>l' \<le> u'\<close> k'_eq by (auto simp: cbox_interval)
          then have "l' \<in> Inf ` d" using k'd by auto
          then have "l_min \<le> l'" unfolding l_min_def using fin_d by auto
          then have "l0 \<le> l'" using k0_inf k0_inf' by simp
          then show "l0 \<le> a" using \<open>l' \<le> a\<close> by linarith
        qed
        ultimately show "l0 = a" by simp
      qed
        \<comment> \<open>Remove k0 and work with d - {k0} which is a division of {u0..b}\<close>
      define d' where "d' = d - {k0}"
      have card_d': "card d' < card d" unfolding d'_def using fin_d k0d
        by (meson card_Diff1_less_iff)
      have u0_le_b: "u0 \<le> b" using division_ofD(2)[OF less.prems k0d] l0u0 k0_eq
        by (auto simp: cbox_interval)
          \<comment> \<open>d' is a division of {u0..b}\<close>
      have div_d': "d' division_of {u0..b}" sorry
      have "(\<Sum>k\<in>d. (g (Sup k) - g (Inf k))) =
      (g u0 - g a) + (\<Sum>k\<in>d'. (g (Sup k) - g (Inf k)))"
        using k0d fin_d l0_eq_a k0_inf' k0_sup
        unfolding d'_def by (simp add: sum.remove)
      also have "(\<Sum>k\<in>d'. (g (Sup k) - g (Inf k))) \<le> g b - g u0"
        using less.hyps[OF card_d' div_d'] mono u0_le_b by auto
      also have "(g u0 - g a) + (g b - g u0) = g b - g a" by simp
      finally show ?thesis by linarith
    qed
  qed
next
next
  case False
  then have ba: "b \<le> a" by linarith
  have fin_d: "finite d" using division_of_finite[OF div_d] .
  show ?thesis
  proof (cases "a = b")
    case True
    then have "{a..b} = {a}" by auto
    then have d_sub: "\<And>k. k \<in> d \<Longrightarrow> k = {a}"
      using division_ofD(2,3)[OF div_d] by auto
    have "(\<Sum>k\<in>d. (g (Sup k) - g (Inf k))) = 0"
    proof (rule sum.neutral, rule ballI)
      fix k assume "k \<in> d"
      then have "k = {a}" using d_sub by auto
      then show "g (Sup k) - g (Inf k) = 0" by simp
    qed
    then show ?thesis using True by simp
  next
    case False
    then have "b < a" using ba by linarith
    then have "{a..b} = {}" by auto
    then have "d = {}" using div_d division_ofD(6) by fastforce
    then show ?thesis by simp
  qed
qed

lemma increasing_bounded_variation:
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
    fix i assume iBasis: "i \<in> Basis"
    show "(\<Sum>k\<in>d. \<bar>(f (Sup k) - f (Inf k)) \<bullet> i\<bar>) = (\<Sum>k\<in>d. (f (Sup k) \<bullet> i - f (Inf k) \<bullet> i))"
    proof (intro sum.cong refl)
      fix k assume kd: "k \<in> d"
      from division_ofD(2,4)[OF div_d kd] obtain l u where
        k_eq: "k = cbox l u" and "k \<noteq> {}" by auto
      then have lu: "l \<le> u" by (simp add: cbox_interval interval_ne_empty(1)[symmetric])
      have "k \<subseteq> {a..b}" using division_ofD(2)[OF div_d kd] by auto
      then have "l \<in> {a..b}" "u \<in> {a..b}" using lu k_eq by (auto simp: cbox_interval)
      have "f l \<le> f u" using assms \<open>l \<in> {a..b}\<close> \<open>u \<in> {a..b}\<close> lu by auto
      then have "f l \<bullet> i \<le> f u \<bullet> i" using iBasis unfolding eucl_le by auto
      have "Inf k = l" "Sup k = u" using lu k_eq by (auto simp: cbox_interval)
      then show "\<bar>(f (Sup k) - f (Inf k)) \<bullet> i\<bar> = f (Sup k) \<bullet> i - f (Inf k) \<bullet> i"
        using \<open>f l \<bullet> i \<le> f u \<bullet> i\<close> by (simp add: inner_diff_left abs_of_nonneg)
    qed
  qed
  also have "\<dots> \<le> (\<Sum>i\<in>Basis. \<bar>(f b - f a) \<bullet> i\<bar>)"
  proof (intro sum_mono)
    fix i assume iBasis: "i \<in> Basis"
    \<comment> \<open>Each component sum telescopes to f(b)\<sqdot>i - f(a)\<sqdot>i\<close>
    have tele: "(\<Sum>k\<in>d. (f (Sup k) \<bullet> i - f (Inf k) \<bullet> i)) \<le> f b \<bullet> i - f a \<bullet> i"
      sorry
    also have "\<dots> \<le> \<bar>(f b - f a) \<bullet> i\<bar>" by (simp add: inner_diff_left)
    finally show "(\<Sum>k\<in>d. (f (Sup k) \<bullet> i - f (Inf k) \<bullet> i)) \<le> \<bar>(f b - f a) \<bullet> i\<bar>" .
  qed
  also have "\<dots> \<le> (\<Sum>i\<in>Basis. norm (f b - f a))"
    by (intro sum_mono) (auto simp: Basis_le_norm)
  also have "\<dots> = DIM('a) * norm (f b - f a)"
    by simp
  finally show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> DIM('a) * norm (f b - f a)" .
qed

lemma increasing_vector_variation:
  assumes "\<And>x y. x \<in> {a..b} \<Longrightarrow> y \<in> {a..b} \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
    and "a \<le> b"
  shows "vector_variation {a..b} f = norm (f b - f a)"
  sorry

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

