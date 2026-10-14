theory Periodization
  imports Complex_Fourier_Series "HOL-Analysis.Uniform_Limit"
begin

definition periodization :: "(real \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> complex" where
  "periodization f x = (\<Sum>\<^sub>\<infinity>n::int. f (x + of_int n))"

lemma periodization_summable_base:
  fixes f :: "real \<Rightarrow> complex"
    and M :: "int \<Rightarrow> real"
  assumes majorant: "M summable_on UNIV"
    and bound: "\<And>n. norm (f (t + of_int n)) \<le> M n"
  shows "(\<lambda>n::int. f (t + of_int n)) summable_on UNIV"
proof -
  have "(\<lambda>n::int. norm (f (t + of_int n))) summable_on UNIV"
    by (rule Infinite_Sum.abs_summable_on_comparison_test'[OF majorant]) (use bound in auto)
  then show ?thesis by (rule abs_summable_summable)
qed

lemma periodization_summable:
  fixes f :: "real \<Rightarrow> complex"
    and M :: "int \<Rightarrow> real"
  assumes majorant: "M summable_on UNIV"
    and bound: "\<And>t n. t \<in> {0..1} \<Longrightarrow> norm (f (t + of_int n)) \<le> M n"
  shows "(\<lambda>n::int. f (x + of_int n)) summable_on UNIV"
proof -
  let ?t = "frac x"
  have t: "?t \<in> {0..1}" using frac_ge_0[of x] frac_lt_1[of x] by auto
  have base: "(\<lambda>n::int. f (?t + of_int n)) summable_on UNIV"
    by (rule periodization_summable_base[OF majorant]) (rule bound[OF t])
  have bij: "bij_betw (\<lambda>n::int. n + floor x) UNIV UNIV"
    by (simp add: bij_betw_def)
  have shift: "f (x + of_int n) = f (?t + of_int (n + floor x))" for n
    by (simp add: frac_def algebra_simps)
  show ?thesis
    using summable_on_reindex_bij_betw[OF bij, of "\<lambda>n. f (?t + of_int n)"]
      base by (simp add: shift)
qed

lemma periodization_uniform_limit_base:
  fixes f :: "real \<Rightarrow> complex"
    and M :: "int \<Rightarrow> real"
  assumes majorant: "M summable_on UNIV"
    and bound: "\<And>t n. t \<in> {0..1} \<Longrightarrow> norm (f (t + of_int n)) \<le> M n"
  shows "uniform_limit {0..1}
    (\<lambda>F t. \<Sum>n\<in>F. f (t + of_int n))
    (periodization f) (finite_subsets_at_top UNIV)"
  unfolding periodization_def
  by (rule Weierstrass_m_test_general_strong[where X'=UNIV and M=M])
    (use majorant bound in auto)

lemma periodization_periodic:
  fixes f :: "real \<Rightarrow> complex"
  shows "periodization f (x + 1) = periodization f x"
proof -
  have bij: "bij_betw (\<lambda>n::int. n + 1) UNIV UNIV"
    by (simp add: bij_betw_def)
  note shift = infsum_reindex_bij_betw[OF bij, of "\<lambda>n::int. f (x + of_int n)"]
  show ?thesis using shift
    by (simp add: periodization_def algebra_simps)
qed

lemma periodization_frac:
  fixes f :: "real \<Rightarrow> complex"
  shows "periodization f (frac x) = periodization f x"
proof -
  have bij: "bij_betw (\<lambda>n::int. n + floor x) UNIV UNIV"
    by (simp add: bij_betw_def)
  note shift = infsum_reindex_bij_betw[OF bij,
    of "\<lambda>n::int. f (frac x + of_int n)"]
  show ?thesis using shift
    by (simp add: periodization_def frac_def algebra_simps)
qed

lemma periodization_continuous_base:
  fixes f :: "real \<Rightarrow> complex"
    and M :: "int \<Rightarrow> real"
  assumes continuous: "continuous_on UNIV f"
    and majorant: "M summable_on UNIV"
    and bound: "\<And>t n. t \<in> {0..1} \<Longrightarrow> norm (f (t + of_int n)) \<le> M n"
  shows "continuous_on {0..1} (periodization f)"
proof (rule uniform_limit_theorem)
  have shifted_continuous:
    "continuous_on {0..1} (\<lambda>t. f (t + of_int n))" for n
    by (rule continuous_on_compose2[OF continuous])
      (auto intro: continuous_intros)
  show "\<forall>\<^sub>F F in finite_subsets_at_top (UNIV :: int set).
      continuous_on {0..1} (\<lambda>t. \<Sum>n\<in>F. f (t + of_int n))"
  proof (rule eventually_finite_subsets_at_top_weakI)
    fix F :: "int set"
    assume "finite F" "F \<subseteq> UNIV"
    then show "continuous_on {0..1} (\<lambda>t. \<Sum>n\<in>F. f (t + of_int n))"
      by (intro continuous_intros shifted_continuous)
  qed
  show "uniform_limit {0..1} (\<lambda>F t. \<Sum>n\<in>F. f (t + of_int n))
    (periodization f) (finite_subsets_at_top UNIV)"
    by (rule periodization_uniform_limit_base[OF majorant bound])
  show "\<not> trivial_limit (finite_subsets_at_top (UNIV :: int set))"
    by (rule finite_subsets_at_top_neq_bot)
qed

lemma periodization_continuous:
  fixes f :: "real \<Rightarrow> complex"
    and M :: "int \<Rightarrow> real"
  assumes continuous: "continuous_on UNIV f"
    and majorant: "M summable_on UNIV"
    and bound: "\<And>t n. t \<in> {0..1} \<Longrightarrow> norm (f (t + of_int n)) \<le> M n"
  shows "continuous_on UNIV (periodization f)"
proof -
  note base = periodization_continuous_base[OF continuous majorant bound]
  have rebase: "continuous_on {0..1} (\<lambda>x. Re (periodization f x))"
    using base by (intro continuous_intros)
  have imbase: "continuous_on {0..1} (\<lambda>x. Im (periodization f x))"
    using base by (intro continuous_intros)
  have endpoints: "periodization f 1 = periodization f 0"
    using periodization_periodic[where f=f and x=0] by simp
  have re: "continuous_on UNIV ((\<lambda>x. Re (periodization f x)) \<circ> frac)"
    by (rule continuous_on_compose_frac[OF rebase])
      (simp add: endpoints)
  have im: "continuous_on UNIV ((\<lambda>x. Im (periodization f x)) \<circ> frac)"
    by (rule continuous_on_compose_frac[OF imbase])
      (simp add: endpoints)
  have "continuous_on UNIV
    (\<lambda>x. Complex (Re (periodization f (frac x))) (Im (periodization f (frac x))))"
    by (rule continuous_on_Complex) (use re im in \<open>simp_all add: o_def\<close>)
  then have "continuous_on UNIV (\<lambda>x. periodization f (frac x))"
    by simp
  then show ?thesis by (simp add: periodization_frac)
qed

lemma integral_infsum_uniform:
  fixes u :: "int \<Rightarrow> real \<Rightarrow> complex"
    and g :: "real \<Rightarrow> complex"
    and a b :: real
  assumes uniform: "uniform_limit {a..b}
      (\<lambda>F t. \<Sum>n\<in>F. u n t) g (finite_subsets_at_top UNIV)"
    and continuous: "\<And>n. continuous_on {a..b} (u n)"
    and continuous_g: "continuous_on {a..b} g"
  shows "(\<integral>t. g t \<partial>(lebesgue_on {a..b})) =
    (\<Sum>\<^sub>\<infinity>n::int. \<integral>t. u n t \<partial>(lebesgue_on {a..b}))"
proof -
  let ?M = "lebesgue_on {a..b}"
  have cont_sum: "continuous_on {a..b} (\<lambda>t. \<Sum>n\<in>F. u n t)" for F
  proof (cases "finite F")
    case True
    then show ?thesis by (intro continuous_intros continuous)
  next
    case False
    then show ?thesis by simp
  qed
  obtain I J where I: "\<And>F. ((\<lambda>t. \<Sum>n\<in>F. u n t) has_integral I F) {a..b}"
    and J: "(g has_integral J) {a..b}"
    and lim: "(I \<longlongrightarrow> J) (finite_subsets_at_top (UNIV :: int set))"
    using uniform_limit_integral[OF uniform cont_sum finite_subsets_at_top_neq_bot]
    by blast
  have int_u: "integrable ?M (u n)" for n
    by (rule continuous_imp_integrable_real[OF continuous])
  have int_g: "integrable ?M g"
    by (rule continuous_imp_integrable_real[OF continuous_g])
  have If: "I F = (\<integral>t. (\<Sum>n\<in>F. u n t) \<partial>?M)" for F
  proof -
    have "I F = integral {a..b} (\<lambda>t. \<Sum>n\<in>F. u n t)"
      using I[of F] by (simp add: integral_unique)
    also have "\<dots> = (\<integral>t. (\<Sum>n\<in>F. u n t) \<partial>?M)"
      by (rule lebesgue_integral_eq_integral[symmetric])
        (auto intro: continuous_imp_integrable_real cont_sum)
    finally show ?thesis .
  qed
  have Jf: "J = (\<integral>t. g t \<partial>?M)"
  proof -
    have "J = integral {a..b} g" using J by (simp add: integral_unique)
    also have "\<dots> = (\<integral>t. g t \<partial>?M)"
      by (rule lebesgue_integral_eq_integral[OF int_g, symmetric]) auto
    finally show ?thesis .
  qed
  have eq: "I F = (\<Sum>n\<in>F. (\<integral>t. u n t \<partial>?M))" for F
    by (simp add: If Bochner_Integration.integral_sum int_u)
  have Ieq: "I = (\<lambda>F. \<Sum>n\<in>F. (\<integral>t. u n t \<partial>?M))"
    by (rule ext) (rule eq)
  have "((\<lambda>n::int. \<integral>t. u n t \<partial>?M) has_sum
    (\<integral>t. g t \<partial>?M)) UNIV"
    using lim by (simp add: has_sum_def Ieq Jf)
  then show ?thesis by (rule infsumI[symmetric])
qed

lemma periodization_integral_exchange:
  fixes f :: "real \<Rightarrow> complex"
    and M :: "int \<Rightarrow> real"
    and h :: "real \<Rightarrow> complex"
  assumes continuous: "continuous_on UNIV f"
    and majorant: "M summable_on UNIV"
    and bound: "\<And>t n. t \<in> {0..1} \<Longrightarrow> norm (f (t + of_int n)) \<le> M n"
    and continuous_h: "continuous_on {0..1} h"
    and norm_h: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (h t) \<le> 1"
  shows "(\<integral>t. periodization f t * h t \<partial>(lebesgue_on {0..1})) =
    (\<Sum>\<^sub>\<infinity>n::int. \<integral>t. f (t + of_int n) * h t \<partial>(lebesgue_on {0..1}))"
proof -
  let ?u = "\<lambda>n t. f (t + of_int n) * h t"
  have weighted_bound: "norm (?u n t) \<le> M n" if t: "t \<in> {0..1}" for n t
  proof -
    have "norm (?u n t) \<le> norm (f (t + of_int n))"
      using mult_left_mono[OF norm_h[OF t], of "norm (f (t + of_int n))"]
      by (simp add: norm_mult)
    also have "\<dots> \<le> M n" by (rule bound[OF t])
    finally show ?thesis .
  qed
  have u: "uniform_limit {0..1}
      (\<lambda>F t. \<Sum>n\<in>F. ?u n t)
      (\<lambda>t. periodization f t * h t) (finite_subsets_at_top UNIV)"
  proof -
    have "uniform_limit {0..1}
      (\<lambda>F t. \<Sum>n\<in>F. ?u n t)
      (\<lambda>t. \<Sum>\<^sub>\<infinity>n::int. ?u n t) (finite_subsets_at_top UNIV)"
      by (rule Weierstrass_m_test_general_strong[where X'=UNIV and M=M])
        (use majorant weighted_bound in auto)
    then show ?thesis
      by (simp add: periodization_def infsum_cmult_left')
  qed
  have shifted_continuous:
    "continuous_on {0..1} (\<lambda>t. f (t + of_int n))" for n
    by (rule continuous_on_compose2[OF continuous])
      (auto intro: continuous_intros)
  have cont_u: "continuous_on {0..1} (?u n)" for n
    by (intro continuous_intros shifted_continuous continuous_h)
  have cont_g: "continuous_on {0..1} (\<lambda>t. periodization f t * h t)"
    by (intro continuous_intros continuous_h
      periodization_continuous_base[OF continuous majorant bound])
  show ?thesis by (rule integral_infsum_uniform[OF u cont_u cont_g])
qed

lemma periodization_fourier_integral_exchange:
  fixes f :: "real \<Rightarrow> complex"
    and M :: "int \<Rightarrow> real"
  assumes continuous: "continuous_on UNIV f"
    and majorant: "M summable_on UNIV"
    and bound: "\<And>t n. t \<in> {0..1} \<Longrightarrow> norm (f (t + of_int n)) \<le> M n"
  shows "(\<integral>t. periodization f t * cis (-(2 * pi * of_int k * t))
      \<partial>(lebesgue_on {0..1})) =
    (\<Sum>\<^sub>\<infinity>n::int. \<integral>t. f (t + of_int n) * cis (-(2 * pi * of_int k * t))
      \<partial>(lebesgue_on {0..1}))"
  by (rule periodization_integral_exchange[OF continuous majorant bound])
    (auto intro!: continuous_intros)

lemma integral_unit_intervals:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes continuous: "continuous_on UNIV g"
  shows "(\<Sum>j<m. integral {0..1} (\<lambda>t. g (t + of_int (a + int j)))) =
    integral {of_int a..of_int a + real m} g"
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have shifted: "integral {0..1} (\<lambda>t. g (t + of_int (a + int m))) =
      integral {of_int a + real m..of_int a + real (Suc m)} g"
    using integral_shift_Icc_real[of 0 1 g "of_int (a + int m)"]
    by (simp add: o_def algebra_simps)
  have integrable: "g integrable_on {of_int a..of_int a + real (Suc m)}"
    by (rule integrable_continuous_real)
      (use continuous in \<open>auto intro: continuous_on_subset\<close>)
  have combined: "integral {of_int a..of_int a + real m} g +
      integral {of_int a + real m..of_int a + real (Suc m)} g =
      integral {of_int a..of_int a + real (Suc m)} g"
    by (rule Henstock_Kurzweil_Integration.integral_combine[OF _ _ integrable]) auto
  show ?case using Suc.IH shifted combined by simp
qed

lemma symmetric_integer_intervals_cofinal:
  "filterlim (\<lambda>m::nat. {-int m..<int m})
    (finite_subsets_at_top (UNIV :: int set)) sequentially"
proof (unfold filterlim_finite_subsets_at_top, safe)
  fix X :: "int set"
  assume finite: "finite X"
  have "\<exists>N::nat. \<forall>n\<in>X. -int N \<le> n \<and> n < int N"
    using finite
  proof (induction X rule: finite_induct)
    case empty
    then show ?case by (intro exI[of _ 1]) auto
  next
    case (insert n X)
    then obtain N :: nat where N: "\<forall>n\<in>X. -int N \<le> n \<and> n < int N"
      by blast
    let ?K = "max N (Suc (nat (abs n)))"
    have "-int ?K \<le> n \<and> n < int ?K"
      by linarith
    moreover have "\<forall>j\<in>X. -int ?K \<le> j \<and> j < int ?K"
      using N by auto
    ultimately show ?case by (intro exI[of _ ?K]) auto
  qed
  then obtain N :: nat where N: "\<forall>n\<in>X. -int N \<le> n \<and> n < int N"
    by blast
  show "\<forall>\<^sub>F m in sequentially.
      finite {-int m..<int m} \<and> X \<subseteq> {-int m..<int m} \<and>
      {-int m..<int m} \<subseteq> UNIV"
    using N by (auto simp: eventually_sequentially intro!: exI[of _ N])
qed

lemma infsum_symmetric_integer_intervals:
  fixes u :: "int \<Rightarrow> complex"
  assumes summable: "u summable_on UNIV"
  shows "((\<lambda>m::nat. \<Sum>n\<in>{-int m..<int m}. u n) \<longlonglongrightarrow>
    (\<Sum>\<^sub>\<infinity>n::int. u n))"
proof -
  have "((sum u) \<longlongrightarrow> infsum u UNIV)
    (finite_subsets_at_top (UNIV :: int set))"
    using summable by (simp add: summable_iff_has_sum_infsum has_sum_def)
  then show ?thesis
    using symmetric_integer_intervals_cofinal by (rule filterlim_compose)
qed

lemma symmetric_integer_interval_image:
  "{-int m..<int m} =
    (\<lambda>j::nat. -int m + int j) ` {..<2 * m}"
proof
  show "{-int m..<int m} \<subseteq>
    (\<lambda>j::nat. -int m + int j) ` {..<2 * m}"
  proof
    fix n :: int
    assume n: "n \<in> {-int m..<int m}"
    let ?j = "nat (n + int m)"
    have "?j < 2 * m" using n by (simp add: nat_less_iff; linarith)
    moreover have "n = -int m + int ?j" using n by simp
    ultimately show "n \<in> (\<lambda>j::nat. -int m + int j) ` {..<2 * m}"
      by blast
  qed
  show "(\<lambda>j::nat. -int m + int j) ` {..<2 * m} \<subseteq> {-int m..<int m}"
    by auto
qed

lemma integral_symmetric_unit_intervals:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes continuous: "continuous_on UNIV g"
  shows "(\<Sum>n\<in>{-int m..<int m}.
    integral {0..1} (\<lambda>t. g (t + of_int n))) =
    integral {-real m..real m} g"
proof -
  have reindex: "(\<Sum>n\<in>{-int m..<int m}.
      integral {0..1} (\<lambda>t. g (t + of_int n))) =
    (\<Sum>j<2*m. integral {0..1} (\<lambda>t. g (t + of_int (-int m + int j))))"
    by (subst symmetric_integer_interval_image)
      (subst sum.reindex, auto simp: inj_on_def)
  show ?thesis using reindex integral_unit_intervals[OF continuous,
      of "-int m" "2*m"]
    by simp
qed

lemma integral_symmetric_intervals_limit:
  fixes g :: "real \<Rightarrow> complex"
  assumes integrable: "integrable lebesgue g"
  shows "((\<lambda>m::nat. \<integral>x. g x \<partial>(lebesgue_on {-real m..real m}))
    \<longlonglongrightarrow> (\<integral>x. g x \<partial>lebesgue))"
proof -
  let ?A = "\<lambda>m::nat. {-real m..real m}"
  have cover: "(\<Union>m. ?A m) = UNIV"
  proof
    show "(\<Union>m. ?A m) \<subseteq> UNIV" by simp
    show "UNIV \<subseteq> (\<Union>m. ?A m)"
    proof
      fix x :: real
      obtain m :: nat where "abs x \<le> real m"
        using real_arch_simple[of "abs x"] by blast
      then have "x \<in> ?A m" by auto
      then show "x \<in> (\<Union>m. ?A m)" by blast
    qed
  qed
  have up: "incseq ?A" by (auto simp: incseq_def)
  have lim: "((\<lambda>m. set_lebesgue_integral lebesgue (?A m) g) \<longlonglongrightarrow>
    set_lebesgue_integral lebesgue (\<Union>m. ?A m) g)"
    by (rule set_integral_cont_up[OF _ up])
      (auto simp: cover set_integrable_def integrable)
  have restrict: "set_lebesgue_integral lebesgue (?A m) g =
      (\<integral>x. g x \<partial>(lebesgue_on (?A m)))" for m
    unfolding set_lebesgue_integral_def
    by (rule integral_restrict_space[symmetric]) auto
  have all: "set_lebesgue_integral lebesgue UNIV g =
      (\<integral>x. g x \<partial>lebesgue)"
    by (simp add: set_lebesgue_integral_def)
  show ?thesis using lim
    by (simp only: cover restrict all)
qed

lemma integral_integer_tiling:
  fixes g :: "real \<Rightarrow> complex"
  assumes continuous: "continuous_on UNIV g"
    and integrable: "integrable lebesgue g"
    and summable: "(\<lambda>n::int. \<integral>t. g (t + of_int n)
      \<partial>(lebesgue_on {0..1})) summable_on UNIV"
  shows "(\<Sum>\<^sub>\<infinity>n::int. \<integral>t. g (t + of_int n)
      \<partial>(lebesgue_on {0..1})) =
    (\<integral>x. g x \<partial>lebesgue)"
proof -
  let ?u = "\<lambda>n::int. \<integral>t. g (t + of_int n) \<partial>(lebesgue_on {0..1})"
  have shift_cont: "continuous_on {0..1} (\<lambda>t. g (t + of_int n))" for n
    by (rule continuous_on_compose2[OF continuous])
      (auto intro: continuous_intros)
  have cell: "?u n = integral {0..1} (\<lambda>t. g (t + of_int n))" for n
    by (rule lebesgue_integral_eq_integral)
      (auto intro: continuous_imp_integrable_real shift_cont)
  have large: "(\<integral>x. g x \<partial>(lebesgue_on {-real m..real m})) =
      integral {-real m..real m} g" for m
    by (rule lebesgue_integral_eq_integral)
      (use continuous in \<open>auto intro: continuous_imp_integrable_real
        continuous_on_subset\<close>)
  have finite_eq: "(\<Sum>n\<in>{-int m..<int m}. ?u n) =
      (\<integral>x. g x \<partial>(lebesgue_on {-real m..real m}))" for m
    using integral_symmetric_unit_intervals[OF continuous, of m]
    by (simp add: cell large)
  have left: "((\<lambda>m::nat. \<Sum>n\<in>{-int m..<int m}. ?u n)
      \<longlonglongrightarrow> infsum ?u UNIV)"
    by (rule infsum_symmetric_integer_intervals[OF summable])
  have right: "((\<lambda>m::nat. \<Sum>n\<in>{-int m..<int m}. ?u n)
      \<longlonglongrightarrow> (\<integral>x. g x \<partial>lebesgue))"
    using integral_symmetric_intervals_limit[OF integrable]
    by (simp add: finite_eq)
  show ?thesis using LIMSEQ_unique[OF left right] .
qed

lemma periodization_cell_integral_bound:
  fixes f :: "real \<Rightarrow> complex"
    and M :: "int \<Rightarrow> real"
  assumes continuous: "continuous_on UNIV f"
    and bound: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (f (t + of_int n)) \<le> M n"
  shows "integral {0..1} (\<lambda>t. norm (f (t + of_int n))) \<le> M n"
proof -
  have shifted: "continuous_on {0..1} (\<lambda>t. f (t + of_int n))"
    by (rule continuous_on_compose2[OF continuous])
      (auto intro: continuous_intros)
  have lebesgue_integrable: "integrable (lebesgue_on {0..1})
      (\<lambda>t. norm (f (t + of_int n)))"
    by (rule continuous_imp_integrable_real)
      (intro continuous_intros shifted)
  have const_integrable: "integrable (lebesgue_on {0..(1::real)}) (\<lambda>t. M n)"
    by (rule continuous_imp_integrable_real) (intro continuous_intros)
  have point_bound: "\<And>t. t \<in> space (lebesgue_on {0..1}) \<Longrightarrow>
      norm (f (t + of_int n)) \<le> M n"
    using bound by simp
  note comparison = Bochner_Integration.integral_mono[OF lebesgue_integrable
    const_integrable point_bound]
  have "integral {0..1} (\<lambda>t. norm (f (t + of_int n))) =
      (\<integral>t. norm (f (t + of_int n)) \<partial>(lebesgue_on {0..1}))"
    using lebesgue_integrable by (simp add: lebesgue_integral_eq_integral)
  also have "\<dots> \<le> integral\<^sup>L (lebesgue_on {0..(1::real)}) (\<lambda>t. M n)"
    by (rule comparison)
  also have "\<dots> = M n"
    by (simp add: measure_def emeasure_restrict_space emeasure_completion)
  finally show ?thesis .
qed

lemma periodization_symmetric_norm_bound:
  fixes f :: "real \<Rightarrow> complex"
    and M :: "int \<Rightarrow> real"
  assumes continuous: "continuous_on UNIV f"
    and majorant: "M summable_on UNIV"
    and bound: "\<And>t n. t \<in> {0..1} \<Longrightarrow> norm (f (t + of_int n)) \<le> M n"
  shows "integral {-real m..real m} (\<lambda>x. norm (f x)) \<le> infsum M UNIV"
proof -
  have nonnegative: "0 \<le> M n" for n
  proof -
    have "norm (f (of_int n)) \<le> M n" using bound[of 0 n] by simp
    then show ?thesis by (meson norm_ge_zero order_trans)
  qed
  have "integral {-real m..real m} (\<lambda>x. norm (f x)) =
    (\<Sum>n\<in>{-int m..<int m}.
      integral {0..1} (\<lambda>t. norm (f (t + of_int n))))"
    using integral_symmetric_unit_intervals[of "\<lambda>x. norm (f x)" m]
      continuous by (simp add: continuous_on_norm)
  also have "\<dots> \<le> (\<Sum>n\<in>{-int m..<int m}. M n)"
    by (intro sum_mono periodization_cell_integral_bound[OF continuous])
      (rule bound)
  also have "\<dots> \<le> infsum M UNIV"
    by (rule finite_sum_le_infsum[OF majorant]) (auto simp: nonnegative)
  finally show ?thesis .
qed

lemma periodization_integrable:
  fixes f :: "real \<Rightarrow> complex"
    and M :: "int \<Rightarrow> real"
  assumes continuous: "continuous_on UNIV f"
    and majorant: "M summable_on UNIV"
    and bound: "\<And>t n. t \<in> {0..1} \<Longrightarrow> norm (f (t + of_int n)) \<le> M n"
  shows "integrable lebesgue f"
proof -
  let ?H = "\<lambda>x. norm (f x)"
  let ?A = "\<lambda>m::nat. {-real m..real m}"
  let ?u = "\<lambda>m x. if x \<in> ?A m then ?H x else 0"
  let ?B = "\<lambda>m. \<integral>x. ?u m x \<partial>lebesgue"
  have int_interval: "integrable (lebesgue_on (?A m)) ?H" for m
    by (rule continuous_imp_integrable_real)
      (use continuous in \<open>auto intro!: continuous_intros
        intro: continuous_on_subset\<close>)
  have int_u: "integrable lebesgue (?u m)" for m
  proof -
    have S: "?A m \<in> sets lebesgue" by simp
    have "integrable lebesgue (?u m) \<longleftrightarrow>
      integrable (lebesgue_on (?A m)) ?H"
      by (rule Lebesgue_Measure.integrable_restrict_UNIV[OF S])
    then show ?thesis using int_interval[of m] by blast
  qed
  have B_eq: "?B m = (\<integral>x. ?H x \<partial>(lebesgue_on (?A m)))" for m
    by (rule Lebesgue_Measure.integral_restrict_UNIV) simp
  have B_nonneg: "0 \<le> ?B m" for m
    by (rule Bochner_Integration.integral_nonneg) simp
  have B_bound: "?B m \<le> infsum M UNIV" for m
  proof -
    have "?B m = (\<integral>x. ?H x \<partial>(lebesgue_on (?A m)))"
      by (rule B_eq)
    also have "\<dots> = integral (?A m) ?H"
      by (rule lebesgue_integral_eq_integral[OF int_interval]) simp
    also have "\<dots> \<le> infsum M UNIV"
      by (rule periodization_symmetric_norm_bound[OF continuous majorant bound])
    finally show ?thesis .
  qed
  have Bseq: "Bseq ?B"
  proof (unfold Bseq_def, intro exI[of _ "max 1 (infsum M UNIV)"] conjI allI)
    show "0 < max 1 (infsum M UNIV)" by simp
    show "norm (?B m) \<le> max 1 (infsum M UNIV)" for m
      using B_nonneg[of m] B_bound[of m] by simp
  qed
  have u_mono: "?u m x \<le> ?u (Suc m) x" for m x
    by auto
  have B_mono: "?B m \<le> ?B (Suc m)" for m
    by (rule Bochner_Integration.integral_mono[OF int_u int_u])
      (use u_mono in auto)
  have B_inc: "incseq ?B"
    using B_mono by (simp add: incseq_Suc_iff)
  obtain L where B_lim: "?B \<longlonglongrightarrow> L"
    using Bseq_monoseq_convergent[OF Bseq incseq_imp_monoseq[OF B_inc]]
    by (auto simp: convergent_def)
  have u_lim: "(\<lambda>m. ?u m x) \<longlonglongrightarrow> ?H x" for x
  proof -
    obtain N :: nat where "abs x \<le> real N"
      using real_arch_simple[of "abs x"] by blast
    then have eventually_eq: "\<forall>\<^sub>F m in sequentially. ?u m x = ?H x"
      unfolding eventually_sequentially by (intro exI[of _ N]) auto
    then show ?thesis by (rule tendsto_eventually)
  qed
  have continuous_H: "continuous_on UNIV ?H"
    using continuous by (intro continuous_intros)
  have measurable_H: "?H \<in> borel_measurable lebesgue"
  proof -
    have "?H \<in> borel_measurable (lebesgue_on UNIV)"
      by (rule continuous_imp_measurable_on_sets_lebesgue[OF continuous_H]) simp
    then show ?thesis by simp
  qed
  have measurable_f: "f \<in> borel_measurable lebesgue"
  proof -
    have "f \<in> borel_measurable (lebesgue_on UNIV)"
      by (rule continuous_imp_measurable_on_sets_lebesgue[OF continuous]) simp
    then show ?thesis by simp
  qed
  have u_inc: "incseq (\<lambda>m. ?u m x)" for x
    using u_mono by (simp add: incseq_Suc_iff)
  have u_inc_AE: "AE x in lebesgue. incseq (\<lambda>m. ?u m x)"
    by (rule AE_I2) (rule u_inc)
  have u_nonneg_AE: "AE x in lebesgue. 0 \<le> ?u m x" for m
    by simp
  have u_lim_AE: "AE x in lebesgue. (\<lambda>m. ?u m x) \<longlonglongrightarrow> ?H x"
    by (rule AE_I2) (rule u_lim)
  have integrable_H: "integrable lebesgue ?H"
    by (rule integral_monotone_convergence_nonneg(1)
      [OF int_u u_inc_AE u_nonneg_AE u_lim_AE B_lim measurable_H])
  show ?thesis
    by (rule integrable_norm_cancel[OF integrable_H measurable_f])
qed

end
