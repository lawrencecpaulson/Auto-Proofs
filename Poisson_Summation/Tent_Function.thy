theory Tent_Function
  imports Reconstruction
begin

definition tent_function :: "real \<Rightarrow> complex" where
  "tent_function x = of_real (max 0 (1 - \<bar>x\<bar>))"

lemma tent_function_continuous:
  "continuous_on UNIV tent_function"
  unfolding tent_function_def by (intro continuous_intros)

lemma tent_function_bound:
  "norm (tent_function x) \<le> 1"
  by (simp add: tent_function_def)

lemma tent_function_support:
  fixes n :: int
  assumes t: "t \<in> {0..1}"
    and outside: "n \<notin> {-1, 0}"
  shows "tent_function (t + of_int n) = 0"
proof -
  have cases: "n \<le> -2 \<or> 1 \<le> n"
    using outside by auto
  then have "\<bar>t + of_int n\<bar> \<ge> 1"
    using t by auto
  then show ?thesis
    by (simp add: tent_function_def)
qed

lemma tent_function_base_values:
  assumes t: "t \<in> {0..1}"
  shows "tent_function t = of_real (1-t)"
    and "tent_function (t-1) = of_real t"
  using t by (auto simp: tent_function_def abs_if)

lemma tent_periodization_base:
  assumes t: "t \<in> {0..1}"
  shows "periodization tent_function t = 1"
proof -
  let ?u = "\<lambda>n::int. tent_function (t + of_int n)"
  have reduced: "(\<Sum>\<^sub>\<infinity>n::int. ?u n) =
    (\<Sum>\<^sub>\<infinity>n\<in>{-1,0}. ?u n)"
    by (rule infsum_cong_neutral)
      (use tent_function_support[OF t] in auto)
  have "periodization tent_function t =
      tent_function (t-1) + tent_function t"
    using reduced by (simp add: periodization_def)
  also have "\<dots> = 1"
    using tent_function_base_values[OF t] by simp
  finally show ?thesis .
qed

lemma tent_periodization:
  "periodization tent_function x = 1"
proof -
  have "frac x \<in> {0..1}"
    using frac_ge_0[of x] frac_lt_1[of x] by auto
  then have "periodization tent_function (frac x) = 1"
    by (rule tent_periodization_base)
  then show ?thesis by (simp add: periodization_frac)
qed

lemma tent_majorant:
  fixes t :: real and n :: int
  assumes t: "t \<in> {0..1}"
  shows "norm (tent_function (t + of_int n)) \<le>
    (if n \<in> {-1,0} then 1 else 0)"
  using tent_function_bound[of "t + of_int n"]
    tent_function_support[OF t, of n]
  by auto

lemma tent_majorant_summable:
  "(\<lambda>n::int. if n \<in> {-1,0} then (1::real) else 0) summable_on UNIV"
proof -
  have "(\<lambda>n::int. if n \<in> {-1,0} then (1::real) else 0)
    summable_on {-1,0}"
    by simp
  then show ?thesis
    using summable_on_cong_neutral
      [of UNIV "{-1,0}" "\<lambda>n::int. if n \<in> {-1,0} then (1::real) else 0"
        "\<lambda>n::int. if n \<in> {-1,0} then (1::real) else 0"]
    by auto
qed

lemma integral_cis_unit_integer:
  "(\<integral>t. cis (-(2 * pi * of_int k * t))
    \<partial>(lebesgue_on {0..1})) = (if k = 0 then 1 else 0)"
proof -
  let ?h = "\<lambda>t. cis (-(2 * pi * of_int k * t))"
  have continuous: "continuous_on UNIV ?h"
    by (intro continuous_intros)
  have periodic: "?h (t+1) = ?h t" for t
    using cis_integer_shift[of k t 1] by simp
  have centered: "(\<integral>t. ?h t \<partial>(lebesgue_on {-1/2..1/2})) =
    (\<integral>t. ?h t \<partial>(lebesgue_on {0..1}))"
    by (rule unit_period_integral_centered[OF continuous periodic])
  have scaled: "(\<integral>x. cis (-(of_int k * x))
      \<partial>(lebesgue_on {-pi..pi})) /\<^sub>R (2*pi) =
    (\<integral>t. ?h t \<partial>(lebesgue_on {-1/2..1/2}))"
    using integral_scaled_symmetric[OF continuous]
    by (simp add: field_simps)
  have left: "(\<integral>x. cis (-(of_int k * x))
      \<partial>(lebesgue_on {-pi..pi})) = (if k = 0 then of_real (2*pi) else 0)"
    using integral_cis_integer[of "-k"] by simp
  have unit_value: "(\<integral>t. ?h t \<partial>(lebesgue_on {0..1})) =
    (if k = 0 then of_real (2*pi) else 0) /\<^sub>R (2*pi)"
    using centered scaled left by simp
  show ?thesis using unit_value
    by (cases "k = 0") (simp_all add: scaleR_conv_of_real)
qed

lemma tent_fourier_samples:
  "real_fourier_transform tent_function (of_int k) =
    (if k = 0 then 1 else 0)"
proof -
  have "(\<integral>t. periodization tent_function t *
      cis (-(2 * pi * of_int k * t)) \<partial>(lebesgue_on {0..1})) =
    real_fourier_transform tent_function (of_int k)"
    by (rule periodization_fourier_transform
      [OF tent_function_continuous tent_majorant_summable tent_majorant])
  then show ?thesis
    by (simp add: tent_periodization integral_cis_unit_integer)
qed

lemma tent_fourier_samples_direct:
  "real_fourier_transform tent_function (of_int k) =
    (if k = 0 then 1 else 0)"
proof -
  let ?g = "\<lambda>x. tent_function x * cis (-(2 * pi * of_int k * x))"
  let ?h = "\<lambda>t. cis (-(2 * pi * of_int k * t))"
  let ?cell = "\<lambda>n::int. \<integral>t. ?g (t + of_int n) \<partial>(lebesgue_on {0..1})"
  have continuous_g: "continuous_on UNIV ?g"
    by (intro continuous_intros tent_function_continuous)
  have integrable_f: "integrable lebesgue tent_function"
    by (rule periodization_integrable
      [OF tent_function_continuous tent_majorant_summable tent_majorant])
  have integrable_g: "integrable lebesgue ?g"
    by (rule fourier_weight_integrable[OF tent_function_continuous integrable_f])
  have summable_cells: "?cell summable_on UNIV"
    by (rule fourier_weight_cells_summable
      [OF tent_function_continuous tent_majorant_summable tent_majorant])
  have tiling: "(\<Sum>\<^sub>\<infinity>n::int. ?cell n) =
      (\<integral>x. ?g x \<partial>lebesgue)"
    by (rule integral_integer_tiling[OF continuous_g integrable_g summable_cells])
  have cell_zero: "?cell n = 0" if outside: "n \<notin> {-1,0}" for n
  proof -
    have point_zero: "?g (t + of_int n) = 0" if "t \<in> {0..1}" for t
      using tent_function_support[OF that outside] by simp
    have "?cell n = (\<integral>t. (0::complex) \<partial>(lebesgue_on {0..(1::real)}))"
    proof (rule Bochner_Integration.integral_cong)
      show "lebesgue_on {0..1} = lebesgue_on {0..1}" by simp
      fix t :: real
      assume "t \<in> space (lebesgue_on {0..1})"
      then have "t \<in> {0..1}" by simp
      then show "?g (t + of_int n) = (0::complex)"
        by (rule point_zero)
    qed
    then show ?thesis by simp
  qed
  have reduced: "(\<Sum>\<^sub>\<infinity>n::int. ?cell n) = ?cell (-1) + ?cell 0"
  proof -
    have "(\<Sum>\<^sub>\<infinity>n::int. ?cell n) =
      (\<Sum>\<^sub>\<infinity>n\<in>{-1,0}. ?cell n)"
      by (rule infsum_cong_neutral) (use cell_zero in auto)
    then show ?thesis by simp
  qed
  have continuous_neg: "continuous_on {0..1} (\<lambda>t. ?g (t-1))"
    by (rule continuous_on_compose2[OF continuous_g])
      (auto intro: continuous_intros)
  have int_neg: "integrable (lebesgue_on {0..1}) (\<lambda>t. ?g (t-1))"
    by (rule continuous_imp_integrable_real[OF continuous_neg])
  have int_zero: "integrable (lebesgue_on {0..1}) ?g"
    by (rule continuous_imp_integrable_real)
      (use continuous_g in \<open>auto intro: continuous_on_subset\<close>)
  have point: "?g (t-1) + ?g t = ?h t" if t: "t \<in> {0..1}" for t
  proof -
    have phase: "cis (-(2 * pi * of_int k * (t-1))) = ?h t"
      using cis_integer_shift[of k t "-1"] by simp
    have tent_sum: "tent_function (t-1) + tent_function t = 1"
      using tent_function_base_values[OF t] by simp
    have "?g (t-1) + ?g t =
      (tent_function (t-1) + tent_function t) * ?h t"
      using phase by (simp add: algebra_simps)
    then show ?thesis using tent_sum by simp
  qed
  have cell_sum: "?cell (-1) + ?cell 0 =
      (\<integral>t. ?h t \<partial>(lebesgue_on {0..1}))"
  proof -
    have "?cell (-1) + ?cell 0 =
      (\<integral>t. ?g (t-1) + ?g t \<partial>(lebesgue_on {0..1}))"
      using int_neg int_zero
      by (simp add: Bochner_Integration.integral_add)
    also have "\<dots> = (\<integral>t. ?h t \<partial>(lebesgue_on {0..1}))"
      by (rule Bochner_Integration.integral_cong)
        (use point in auto)
    finally show ?thesis .
  qed
  have "real_fourier_transform tent_function (of_int k) =
      (\<integral>x. ?g x \<partial>lebesgue)"
    by (simp add: real_fourier_transform_def)
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>n::int. ?cell n)"
    using tiling by simp
  also have "\<dots> = (\<integral>t. ?h t \<partial>(lebesgue_on {0..1}))"
    using reduced cell_sum by simp
  also have "\<dots> = (if k = 0 then 1 else 0)"
    by (rule integral_cis_unit_integer)
  finally show ?thesis .
qed

lemma tent_samples_summable:
  "(\<lambda>k::int. norm (real_fourier_transform tent_function (of_int k)))
    summable_on UNIV"
proof -
  have "(\<lambda>k::int. norm (real_fourier_transform tent_function (of_int k)))
    summable_on {0}"
    by simp
  then show ?thesis
    using summable_on_cong_neutral
      [of UNIV "{0}"
        "\<lambda>k::int. norm (real_fourier_transform tent_function (of_int k))"
        "\<lambda>k::int. norm (real_fourier_transform tent_function (of_int k))"]
    by (auto simp: tent_fourier_samples_direct)
qed

lemma tent_poisson_formula:
  "(\<Sum>\<^sub>\<infinity>n::int. tent_function (x + of_int n)) =
    (\<Sum>\<^sub>\<infinity>k::int.
      real_fourier_transform tent_function (of_int k) *
        cis (2 * pi * of_int k * x))"
  using poisson_summation
    [OF tent_function_continuous tent_majorant_summable
      tent_majorant tent_samples_summable, of x]
  by (simp add: periodization_def)

theorem tent_poisson_normalization:
  "(\<Sum>\<^sub>\<infinity>n::int. tent_function (x + of_int n)) = 1"
  "(\<Sum>\<^sub>\<infinity>k::int.
    real_fourier_transform tent_function (of_int k) *
      cis (2 * pi * of_int k * x)) = 1"
proof -
  show "(\<Sum>\<^sub>\<infinity>n::int. tent_function (x + of_int n)) = 1"
    using tent_periodization[of x] by (simp add: periodization_def)
  have reduced: "(\<Sum>\<^sub>\<infinity>k::int.
      real_fourier_transform tent_function (of_int k) *
        cis (2 * pi * of_int k * x)) =
    (\<Sum>\<^sub>\<infinity>k\<in>{0}.
      real_fourier_transform tent_function (of_int k) *
        cis (2 * pi * of_int k * x))"
    by (rule infsum_cong_neutral) (auto simp: tent_fourier_samples_direct)
  show "(\<Sum>\<^sub>\<infinity>k::int.
      real_fourier_transform tent_function (of_int k) *
        cis (2 * pi * of_int k * x)) = 1"
    using reduced by (simp add: tent_fourier_samples_direct)
qed

end
