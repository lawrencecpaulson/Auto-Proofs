theory Reconstruction
  imports Fourier_Transform "HOL-Analysis.Summation_Tests"
begin

definition complex_fourier_series :: "(int \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> complex" where
  "complex_fourier_series c x =
    (\<Sum>\<^sub>\<infinity>n::int. c n * cis (of_int n * x))"

lemma complex_fourier_series_uniform:
  fixes c :: "int \<Rightarrow> complex"
  assumes summable: "(\<lambda>n. norm (c n)) summable_on UNIV"
  shows "uniform_limit UNIV
    (\<lambda>F x. \<Sum>n\<in>F. c n * cis (of_int n * x))
    (complex_fourier_series c) (finite_subsets_at_top UNIV)"
  unfolding complex_fourier_series_def
  by (rule Weierstrass_m_test_general_strong
    [where X'=UNIV and M="\<lambda>n. norm (c n)"])
    (use summable in \<open>auto simp: norm_mult\<close>)

lemma complex_fourier_series_continuous:
  fixes c :: "int \<Rightarrow> complex"
  assumes summable: "(\<lambda>n. norm (c n)) summable_on UNIV"
  shows "continuous_on UNIV (complex_fourier_series c)"
proof (rule uniform_limit_theorem)
  show "\<forall>\<^sub>F F in finite_subsets_at_top (UNIV :: int set).
    continuous_on UNIV (\<lambda>x. \<Sum>n\<in>F. c n * cis (of_int n * x))"
  proof (rule eventually_finite_subsets_at_top_weakI)
    fix F :: "int set"
    assume "finite F" "F \<subseteq> UNIV"
    then show "continuous_on UNIV
      (\<lambda>x. \<Sum>n\<in>F. c n * cis (of_int n * x))"
      by (intro continuous_intros)
  qed
  show "uniform_limit UNIV
    (\<lambda>F x. \<Sum>n\<in>F. c n * cis (of_int n * x))
    (complex_fourier_series c) (finite_subsets_at_top UNIV)"
    by (rule complex_fourier_series_uniform[OF summable])
  show "\<not> trivial_limit (finite_subsets_at_top (UNIV :: int set))"
    by (rule finite_subsets_at_top_neq_bot)
qed

lemma cis_integer_period:
  "cis (of_int n * (x + 2*pi)) = cis (of_int n * x)"
proof -
  have "cis (of_int n * (x + 2*pi)) =
    cis (of_int n * x) * cis (2 * pi * of_int n)"
    by (simp add: cis_mult algebra_simps)
  also have "\<dots> = cis (of_int n * x)"
  proof -
    have "of_int n \<in> (\<int>::real set)" by simp
    then have "cis (2 * pi * of_int n) = 1"
      by (rule cis_multiple_2pi)
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma complex_fourier_series_periodic:
  "complex_fourier_series c (x + 2*pi) = complex_fourier_series c x"
  by (simp add: complex_fourier_series_def cis_integer_period)

lemma integral_cis_integer:
  "(\<integral>x. cis (of_int m * x) \<partial>(lebesgue_on {-pi..pi})) =
    (if m = 0 then of_real (2*pi) else 0)"
proof -
  have int_cis: "integrable (lebesgue_on {-pi..pi})
      (\<lambda>x. cis (of_int m * x))"
    by (rule continuous_imp_integrable_real)
      (intro continuous_intros)
  have re_eq: "Re (\<integral>x. cis (of_int m * x) \<partial>(lebesgue_on {-pi..pi})) =
      (\<integral>x. cos (of_int m * x) \<partial>(lebesgue_on {-pi..pi}))"
    by (subst Bochner_Integration.integral_Re[symmetric])
      (simp_all add: int_cis)
  have im_eq: "Im (\<integral>x. cis (of_int m * x) \<partial>(lebesgue_on {-pi..pi})) =
      (\<integral>x. sin (of_int m * x) \<partial>(lebesgue_on {-pi..pi}))"
    by (subst Bochner_Integration.integral_Im[symmetric])
      (simp_all add: int_cis)
  have z: "of_int m \<in> (\<int>::real set)" by simp
  have real_part:
    "Re (\<integral>x. cis (of_int m * x) \<partial>(lebesgue_on {-pi..pi})) =
      (if m = 0 then 2*pi else 0)"
    using re_eq integral_cos_Z'[OF z] by simp
  have imag_part:
    "Im (\<integral>x. cis (of_int m * x) \<partial>(lebesgue_on {-pi..pi})) = 0"
    using im_eq integral_sin_Z'[OF z] by simp
  show ?thesis using real_part imag_part
    by (simp add: complex_eq_iff)
qed

lemma integral_fourier_exponential:
  fixes c :: complex
  shows "(\<integral>x. c * cis (of_int n * x) * cis (-(of_int k * x))
      \<partial>(lebesgue_on {-pi..pi})) =
    (if n = k then c * of_real (2*pi) else 0)"
proof -
  have point: "c * cis (of_int n * x) * cis (-(of_int k * x)) =
      c * cis (of_int (n-k) * x)" for x
    by (simp add: cis_mult algebra_simps)
  have "(\<integral>x. c * cis (of_int n * x) * cis (-(of_int k * x))
      \<partial>(lebesgue_on {-pi..pi})) =
    c * (\<integral>x. cis (of_int (n-k) * x)
      \<partial>(lebesgue_on {-pi..pi}))"
    by (simp add: point)
  also have "\<dots> = (if n = k then c * of_real (2*pi) else 0)"
    by (subst integral_cis_integer) simp
  finally show ?thesis .
qed

lemma complex_fourier_series_coefficient:
  fixes c :: "int \<Rightarrow> complex"
  assumes summable: "(\<lambda>n. norm (c n)) summable_on UNIV"
  shows "complex_fourier_coefficient (complex_fourier_series c) k = c k"
proof -
  let ?M = "lebesgue_on {-pi..pi}"
  let ?u = "\<lambda>n x. c n * cis (of_int n * x) * cis (-(of_int k * x))"
  let ?g = "\<lambda>x. complex_fourier_series c x * cis (-(of_int k * x))"
  have weighted_bound: "norm (?u n x) \<le> norm (c n)" for n x
    by (simp add: norm_mult)
  have uniform: "uniform_limit {-pi..pi}
    (\<lambda>F x. \<Sum>n\<in>F. ?u n x) ?g (finite_subsets_at_top UNIV)"
  proof -
    have "uniform_limit {-pi..pi}
      (\<lambda>F x. \<Sum>n\<in>F. ?u n x)
      (\<lambda>x. \<Sum>\<^sub>\<infinity>n::int. ?u n x)
      (finite_subsets_at_top UNIV)"
      by (rule Weierstrass_m_test_general_strong
        [where X'=UNIV and M="\<lambda>n. norm (c n)"])
        (use summable weighted_bound in auto)
    then show ?thesis
      by (simp add: complex_fourier_series_def infsum_cmult_left')
  qed
  have continuous_u: "continuous_on {-pi..pi} (?u n)" for n
    by (intro continuous_intros)
  have continuous_g: "continuous_on {-pi..pi} ?g"
    by (intro continuous_intros
      continuous_on_subset[OF complex_fourier_series_continuous[OF summable]])
      auto
  have exchange: "(\<integral>x. ?g x \<partial>?M) =
      (\<Sum>\<^sub>\<infinity>n::int. \<integral>x. ?u n x \<partial>?M)"
    by (rule integral_infsum_uniform[OF uniform continuous_u continuous_g])
  have "(complex_fourier_coefficient (complex_fourier_series c) k) =
      (\<Sum>\<^sub>\<infinity>n::int.
        (if n = k then c n * of_real (2*pi) else 0)) /
      of_real (2*pi)"
    by (simp add: complex_fourier_coefficient_def exchange
      integral_fourier_exponential)
  also have "\<dots> = c k"
  proof -
    have "(\<Sum>\<^sub>\<infinity>n::int.
        (if n = k then c n * of_real (2*pi) else 0)) =
      (\<Sum>\<^sub>\<infinity>n\<in>{k}.
        (if n = k then c n * of_real (2*pi) else 0))"
      by (rule infsum_cong_neutral) auto
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma complex_fourier_coefficient_diff:
  fixes g h :: "real \<Rightarrow> complex"
  assumes continuous_g: "continuous_on UNIV g"
    and continuous_h: "continuous_on UNIV h"
  shows "complex_fourier_coefficient (\<lambda>x. g x - h x) k =
    complex_fourier_coefficient g k - complex_fourier_coefficient h k"
proof -
  have int_g: "integrable (lebesgue_on {-pi..pi})
      (\<lambda>x. g x * cis (-(of_int k * x)))"
    by (rule continuous_imp_integrable_real)
      (use continuous_g in \<open>auto intro!: continuous_intros
        intro: continuous_on_subset\<close>)
  have int_h: "integrable (lebesgue_on {-pi..pi})
      (\<lambda>x. h x * cis (-(of_int k * x)))"
    by (rule continuous_imp_integrable_real)
      (use continuous_h in \<open>auto intro!: continuous_intros
        intro: continuous_on_subset\<close>)
  have point: "(g x - h x) * cis (-(of_int k * x)) =
      g x * cis (-(of_int k * x)) -
      h x * cis (-(of_int k * x))" for x
    by (simp add: algebra_simps)
  have integral_diff:
    "(\<integral>x. (g x - h x) * cis (-(of_int k * x))
      \<partial>(lebesgue_on {-pi..pi})) =
    (\<integral>x. g x * cis (-(of_int k * x))
      \<partial>(lebesgue_on {-pi..pi})) -
    (\<integral>x. h x * cis (-(of_int k * x))
      \<partial>(lebesgue_on {-pi..pi}))"
    by (simp only: point Bochner_Integration.integral_diff[OF int_g int_h])
  show ?thesis
    by (simp only: complex_fourier_coefficient_def
      integral_diff diff_divide_distrib)
qed

theorem poisson_summation:
  fixes f :: "real \<Rightarrow> complex"
    and M :: "int \<Rightarrow> real"
  assumes continuous: "continuous_on UNIV f"
    and majorant: "M summable_on UNIV"
    and bound: "\<And>t n. t \<in> {0..1} \<Longrightarrow> norm (f (t + of_int n)) \<le> M n"
    and samples: "(\<lambda>k::int. norm (real_fourier_transform f (of_int k)))
      summable_on UNIV"
  shows "periodization f x =
    (\<Sum>\<^sub>\<infinity>k::int. real_fourier_transform f (of_int k) *
      cis (2 * pi * of_int k * x))"
proof -
  let ?c = "\<lambda>k::int. real_fourier_transform f (of_int k)"
  let ?P = "\<lambda>t. periodization f (t / (2*pi))"
  let ?S = "complex_fourier_series ?c"
  let ?d = "\<lambda>t. ?P t - ?S t"
  have continuous_periodization: "continuous_on UNIV (periodization f)"
    by (rule periodization_continuous[OF continuous majorant bound])
  have continuous_P: "continuous_on UNIV ?P"
    by (rule continuous_on_compose2[OF continuous_periodization])
      (auto intro: continuous_intros)
  have periodic_P: "?P (t + 2*pi) = ?P t" for t
  proof -
    have "(t + 2*pi) / (2*pi) = t / (2*pi) + 1"
      by (simp add: add_divide_distrib)
    then show ?thesis by (simp add: periodization_periodic)
  qed
  have continuous_S: "continuous_on UNIV ?S"
    by (rule complex_fourier_series_continuous[OF samples])
  have periodic_S: "?S (t + 2*pi) = ?S t" for t
    by (rule complex_fourier_series_periodic)
  have continuous_d: "continuous_on UNIV ?d"
    by (intro continuous_intros continuous_P continuous_S)
  have periodic_d: "?d (t + 2*pi) = ?d t" for t
    by (simp add: periodic_P periodic_S)
  have coeff_d: "complex_fourier_coefficient ?d k = 0" for k
  proof -
    have "complex_fourier_coefficient ?d k =
      complex_fourier_coefficient ?P k -
      complex_fourier_coefficient ?S k"
      by (rule complex_fourier_coefficient_diff[OF continuous_P continuous_S])
    also have "\<dots> = 0"
      using periodization_complex_fourier_coefficient[OF continuous majorant bound, of k]
        complex_fourier_series_coefficient[OF samples, of k]
      by simp
    finally show ?thesis .
  qed
  have zero: "?d (2*pi*x) = 0"
    by (rule complex_fourier_coefficients_unique[OF continuous_d periodic_d coeff_d])
  have rescale: "?P (2*pi*x) = periodization f x"
    by simp
  have "?P (2*pi*x) = ?S (2*pi*x)"
    using zero by simp
  then show ?thesis
    by (simp add: rescale complex_fourier_series_def algebra_simps)
qed

corollary poisson_summation_zero:
  fixes f :: "real \<Rightarrow> complex"
    and M :: "int \<Rightarrow> real"
  assumes continuous: "continuous_on UNIV f"
    and majorant: "M summable_on UNIV"
    and bound: "\<And>t n. t \<in> {0..1} \<Longrightarrow> norm (f (t + of_int n)) \<le> M n"
    and samples: "(\<lambda>k::int. norm (real_fourier_transform f (of_int k)))
      summable_on UNIV"
  shows "(\<Sum>\<^sub>\<infinity>n::int. f (of_int n)) =
    (\<Sum>\<^sub>\<infinity>k::int. real_fourier_transform f (of_int k))"
  using poisson_summation[OF continuous majorant bound samples, of 0]
  by (simp add: periodization_def)

theorem poisson_summation_lattice:
  fixes f :: "real \<Rightarrow> complex"
    and M :: "int \<Rightarrow> real"
  assumes h: "0 < h"
    and continuous: "continuous_on UNIV f"
    and majorant: "M summable_on UNIV"
    and bound: "\<And>t n. t \<in> {0..1} \<Longrightarrow>
      norm (f (h * (t + of_int n))) \<le> M n"
    and samples: "(\<lambda>k::int.
      norm (real_fourier_transform f (of_int k / h))) summable_on UNIV"
  shows "(\<Sum>\<^sub>\<infinity>n::int. f (x + h * of_int n)) =
    (\<Sum>\<^sub>\<infinity>k::int.
      (real_fourier_transform f (of_int k / h) / of_real h) *
        cis (2 * pi * of_int k * x / h))"
proof -
  let ?g = "\<lambda>u. f (h * u)"
  have continuous_g: "continuous_on UNIV ?g"
    by (rule continuous_on_compose2[OF continuous])
      (auto intro: continuous_intros)
  have bound_g:
    "norm (?g (t + of_int n)) \<le> M n"
    if "t \<in> {0..1}" for t n
    by (rule bound[OF that])
  have inverse_norm:
    "norm (inverse (of_real h :: complex)) = inverse h"
    using h by (simp add: norm_inverse)
  have sample_eq:
    "norm (real_fourier_transform ?g (of_int k)) =
      (1 / h) *\<^sub>R
        norm (real_fourier_transform f (of_int k / h))"
    for k :: int
    using h inverse_norm
    by (simp add: real_fourier_transform_scale[OF continuous h]
        norm_divide divide_inverse norm_mult)
  have scaled_samples:
    "(\<lambda>k::int. (1 / h) *\<^sub>R
      norm (real_fourier_transform f (of_int k / h))) summable_on UNIV"
    by (rule summable_on_scaleR_right[OF samples])
  have samples_g:
    "(\<lambda>k::int. norm (real_fourier_transform ?g (of_int k)))
      summable_on UNIV"
    using scaled_samples by (simp add: sample_eq)
  have left:
    "(\<Sum>\<^sub>\<infinity>n::int. f (x + h * of_int n)) =
      periodization ?g (x / h)"
  proof -
    have eq: "f (x + h * of_int n) = ?g (x / h + of_int n)"
      for n :: int
      using h by (simp add: distrib_left)
    show ?thesis
      unfolding periodization_def
      by (rule infsum_cong) (simp add: eq)
  qed
  have right:
    "(\<Sum>\<^sub>\<infinity>k::int.
      real_fourier_transform ?g (of_int k) *
        cis (2 * pi * of_int k * (x / h))) =
    (\<Sum>\<^sub>\<infinity>k::int.
      (real_fourier_transform f (of_int k / h) / of_real h) *
        cis (2 * pi * of_int k * x / h))"
  proof (rule infsum_cong)
    fix k :: int
    assume "k \<in> UNIV"
    have transform:
      "real_fourier_transform ?g (of_int k) =
        real_fourier_transform f (of_int k / h) / of_real h"
      by (rule real_fourier_transform_scale[OF continuous h])
    have exponent:
      "2 * pi * of_int k * (x / h) =
        2 * pi * of_int k * x / h"
      by (simp add: divide_inverse mult_ac)
    show "real_fourier_transform ?g (of_int k) *
        cis (2 * pi * of_int k * (x / h)) =
      (real_fourier_transform f (of_int k / h) / of_real h) *
        cis (2 * pi * of_int k * x / h)"
      using transform exponent by simp
  qed
  show ?thesis
    using poisson_summation
      [OF continuous_g majorant bound_g samples_g, of "x / h"]
      left right by simp
qed

lemma summable_int_power_decay:
  assumes p: "1 < p"
  shows "(\<lambda>n::int. (1 + \<bar>real_of_int n\<bar>) powr (-p)) summable_on UNIV"
proof -
  let ?w = "\<lambda>n::int. (1 + \<bar>real_of_int n\<bar>) powr (-p)"
  have base: "summable (\<lambda>n::nat. real n powr (-p))"
    using summable_real_powr_iff[of "-p"] p by simp
  have nat: "summable (\<lambda>n::nat. real (Suc n) powr (-p))"
    using summable_Suc_iff[of "\<lambda>n::nat. real n powr (-p)"] base
    by simp
  have nat2: "summable (\<lambda>n::nat. real (Suc (Suc n)) powr (-p))"
    using summable_Suc_iff[of "\<lambda>n::nat. real (Suc n) powr (-p)"] nat
    by simp
  have nat_on: "(\<lambda>n::nat. real (Suc n) powr (-p)) summable_on UNIV"
    using nat by (simp add: summable_on_UNIV_nonneg_real_iff)
  have nat2_on: "(\<lambda>n::nat. real (Suc (Suc n)) powr (-p)) summable_on UNIV"
    using nat2 by (simp add: summable_on_UNIV_nonneg_real_iff)
  have pos_set: "(int ` (UNIV::nat set)) = {0..}"
  proof (intro equalityI subsetI)
    fix z :: int
    assume "z \<in> int ` (UNIV::nat set)"
    then show "z \<in> {0..}" by auto
  next
    fix z :: int
    assume "z \<in> {0..}"
    then have "z = int (nat z)" by simp
    then show "z \<in> int ` (UNIV::nat set)" by blast
  qed
  have neg_set: "((\<lambda>n::nat. -1 - int n) ` UNIV) = {..<0}"
  proof (intro equalityI subsetI)
    fix z :: int
    assume "z \<in> (\<lambda>n::nat. -1 - int n) ` UNIV"
    then show "z \<in> {..<0}" by auto
  next
    fix z :: int
    assume "z \<in> {..<0}"
    then have "z = -1 - int (nat (-z-1))"
      by (simp add: of_nat_nat)
    then show "z \<in> (\<lambda>n::nat. -1 - int n) ` UNIV"
      by blast
  qed
  have pos: "?w summable_on {0..}"
  proof -
    have "(\<lambda>n::nat. ?w (int n)) summable_on UNIV"
      using nat_on by simp
    then show ?thesis
      using summable_on_reindex[of int UNIV ?w]
      by (simp add: pos_set o_def)
  qed
  have neg: "?w summable_on {..<0}"
  proof -
    have "(\<lambda>n::nat. ?w (-1 - int n)) summable_on UNIV"
      using nat2_on by simp
    then show ?thesis
      using summable_on_reindex[of "\<lambda>n::nat. -1 - int n" UNIV ?w]
      by (simp add: neg_set inj_on_def o_def)
  qed
  have both: "?w summable_on ({0..} \<union> {..<0})"
    by (rule summable_on_Un_disjoint[OF pos neg]) auto
  have cover: "({0..} \<union> {..<0} :: int set) = UNIV" by auto
  show ?thesis using both by (simp only: cover)
qed

lemma power_decay_unit_shift:
  fixes p :: real
  assumes t: "t \<in> {0..1}"
    and p: "0 < p"
  shows "(1 + \<bar>t + of_int n\<bar>) powr (-p) \<le>
    (2 powr p) * (1 + \<bar>real_of_int n\<bar>) powr (-p)"
proof -
  let ?a = "1 + \<bar>t + of_int n\<bar>"
  let ?b = "1 + \<bar>real_of_int n\<bar>"
  have triangle: "\<bar>real_of_int n\<bar> \<le> \<bar>t + of_int n\<bar> + \<bar>t\<bar>"
    using abs_triangle_ineq[of "t + of_int n" "-t"]
    by (simp add: algebra_simps)
  have abs_t: "\<bar>t\<bar> \<le> 1" using t by auto
  have nonneg: "0 \<le> \<bar>t + of_int n\<bar>" by simp
  have aux: "\<bar>real_of_int n\<bar> \<le> 1 + \<bar>t + of_int n\<bar>"
    using triangle abs_t by linarith
  have b_le: "?b \<le> 2 * ?a"
  proof -
    have "?b \<le> 1 + (1 + \<bar>t + of_int n\<bar>)"
      using add_left_mono[OF aux, of 1] by simp
    also have "\<dots> \<le> 2 * ?a"
      using nonneg by simp
    finally show ?thesis .
  qed
  have half: "?b / 2 \<le> ?a"
    using b_le by (simp add: divide_le_eq)
  have half_pos: "0 < ?b / 2" by simp
  have upper: "?a powr (-p) \<le> (?b / 2) powr (-p)"
    by (rule powr_mono2'[OF _ half_pos half]) (use p in auto)
  have eq: "(?b / 2) powr (-p) =
    (2 powr p) * ?b powr (-p)"
    by (simp add: powr_divide powr_minus field_simps)
  show ?thesis using upper by (simp add: eq)
qed

theorem poisson_summation_power_decay:
  fixes f :: "real \<Rightarrow> complex"
    and A B p q :: real
  assumes continuous: "continuous_on UNIV f"
    and A_nonneg: "0 \<le> A"
    and B_nonneg: "0 \<le> B"
    and p: "1 < p"
    and q: "1 < q"
    and decay_f: "\<And>x. norm (f x) \<le> A * (1 + \<bar>x\<bar>) powr (-p)"
    and decay_transform: "\<And>\<xi>. norm (real_fourier_transform f \<xi>) \<le>
      B * (1 + \<bar>\<xi>\<bar>) powr (-q)"
  shows "(\<Sum>\<^sub>\<infinity>n::int. f (x + of_int n)) =
    (\<Sum>\<^sub>\<infinity>k::int. real_fourier_transform f (of_int k) *
      cis (2 * pi * of_int k * x))"
proof -
  let ?w = "\<lambda>n::int. (1 + \<bar>real_of_int n\<bar>) powr (-p)"
  let ?M = "\<lambda>n::int. ?w n *\<^sub>R (A * 2 powr p)"
  have majorant: "?M summable_on UNIV"
  proof (rule summable_on_scaleR_left)
    assume "A * 2 powr p \<noteq> 0"
    show "?w summable_on UNIV"
      by (rule summable_int_power_decay[OF p])
  qed
  have bound: "norm (f (t + of_int n)) \<le> ?M n"
    if t: "t \<in> {0..1}" for t n
  proof -
    have "norm (f (t + of_int n)) \<le>
      A * (1 + \<bar>t + of_int n\<bar>) powr (-p)"
      by (rule decay_f)
    also have "\<dots> \<le>
      A * ((2 powr p) * (1 + \<bar>real_of_int n\<bar>) powr (-p))"
    proof -
      have shift: "(1 + \<bar>t + of_int n\<bar>) powr (-p) \<le>
        (2 powr p) * (1 + \<bar>real_of_int n\<bar>) powr (-p)"
        by (rule power_decay_unit_shift[OF t]) (use p in auto)
      show ?thesis by (rule mult_left_mono[OF shift A_nonneg])
    qed
    also have "\<dots> = ?M n"
      by (simp add: mult_ac)
    finally show ?thesis .
  qed
  let ?v = "\<lambda>k::int. (1 + \<bar>real_of_int k\<bar>) powr (-q)"
  let ?N = "\<lambda>k::int. ?v k *\<^sub>R B"
  have sample_majorant: "?N summable_on UNIV"
  proof (rule summable_on_scaleR_left)
    assume "B \<noteq> 0"
    show "?v summable_on UNIV"
      by (rule summable_int_power_decay[OF q])
  qed
  have samples: "(\<lambda>k::int. norm (real_fourier_transform f (of_int k)))
      summable_on UNIV"
  proof (rule summable_on_comparison_test[OF sample_majorant])
    show "norm (real_fourier_transform f (of_int k)) \<le> ?N k"
      if "k \<in> UNIV" for k
      using decay_transform[of "of_int k"]
      by (simp add: mult.commute[of B])
    show "0 \<le> norm (real_fourier_transform f (of_int k))"
      if "k \<in> UNIV" for k by simp
  qed
  show ?thesis
    using poisson_summation[OF continuous majorant bound samples, of x]
    by (simp add: periodization_def)
qed

end
