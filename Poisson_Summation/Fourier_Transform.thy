theory Fourier_Transform
  imports Periodization
begin

definition real_fourier_transform :: "(real \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> complex" where
  "real_fourier_transform f \<xi> =
    (\<integral>x. f x * cis (-(2 * pi * \<xi> * x)) \<partial>lebesgue)"

lemma real_fourier_transform_scale:
  fixes f :: "real \<Rightarrow> complex"
  assumes continuous: "continuous_on UNIV f"
    and a: "0 < a"
  shows "real_fourier_transform (\<lambda>x. f (a * x)) \<xi> =
    real_fourier_transform f (\<xi> / a) / of_real a"
proof -
  let ?h = "\<lambda>y. f y * cis (-(2 * pi * (\<xi> / a) * y))"
  have continuous_h: "continuous_on UNIV ?h"
    by (intro continuous_intros continuous)
  have continuous_scaled: "continuous_on UNIV (\<lambda>x. ?h (a * x))"
    by (rule continuous_on_compose2[OF continuous_h])
      (auto intro: continuous_intros)
  have measurable_h: "?h \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF continuous_h] by simp
  have measurable_scaled:
    "(\<lambda>x. ?h (a * x)) \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF continuous_scaled] by simp
  have affine:
    "(\<integral>x. ?h (a * x) \<partial>lborel) =
      (\<integral>y. ?h y \<partial>lborel) / of_real a"
  proof -
    have "(\<integral>y. ?h y \<partial>lborel) =
      a *\<^sub>R (\<integral>x. ?h (a * x) \<partial>lborel)"
      using lborel_integral_real_affine[where f="?h" and c=a and t=0] a
      by simp
    then show ?thesis
      using a by (simp add: scaleR_conv_of_real field_simps)
  qed
  have "real_fourier_transform (\<lambda>x. f (a * x)) \<xi> =
    (\<integral>x. ?h (a * x) \<partial>lebesgue)"
    using a by (simp add: real_fourier_transform_def field_simps)
  also have "\<dots> = (\<integral>x. ?h (a * x) \<partial>lborel)"
    using integral_completion[OF measurable_scaled] by simp
  also have "\<dots> = (\<integral>y. ?h y \<partial>lborel) / of_real a"
    by (rule affine)
  also have "\<dots> = real_fourier_transform f (\<xi> / a) / of_real a"
    using integral_completion[OF measurable_h]
    by (simp add: real_fourier_transform_def)
  finally show ?thesis .
qed

lemma cis_integer_shift:
  "cis (-(2 * pi * of_int k * (t + of_int n))) =
    cis (-(2 * pi * of_int k * t))"
proof -
  have "cis (-(2 * pi * of_int k * (t + of_int n))) =
    cis (-(2 * pi * of_int k * t)) * cis (2 * pi * of_int (-k*n))"
    by (simp add: cis_mult algebra_simps)
  also have "\<dots> = cis (-(2 * pi * of_int k * t))"
  proof -
    have "of_int (-k*n) \<in> (\<int>::real set)" by simp
    then have "cis (2 * pi * of_int (-k*n)) = 1"
      by (rule cis_multiple_2pi)
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma fourier_weight_integrable:
  fixes f :: "real \<Rightarrow> complex"
  assumes continuous: "continuous_on UNIV f"
    and integrable: "integrable lebesgue f"
  shows "integrable lebesgue
    (\<lambda>x. f x * cis (-(2 * pi * \<xi> * x)))"
proof (rule Bochner_Integration.integrable_bound[OF integrable])
  have "continuous_on UNIV
    (\<lambda>x. f x * cis (-(2 * pi * \<xi> * x)))"
    by (intro continuous_intros continuous)
  then show "(\<lambda>x. f x * cis (-(2 * pi * \<xi> * x)))
    \<in> borel_measurable lebesgue"
  proof -
    assume c: "continuous_on UNIV (\<lambda>x. f x * cis (-(2 * pi * \<xi> * x)))"
    have "(\<lambda>x. f x * cis (-(2 * pi * \<xi> * x)))
      \<in> borel_measurable (lebesgue_on UNIV)"
      by (rule continuous_imp_measurable_on_sets_lebesgue[OF c]) simp
    then show ?thesis by simp
  qed
  show "AE x in lebesgue.
    norm (f x * cis (-(2 * pi * \<xi> * x))) \<le> norm (f x)"
    by (rule AE_I2) (simp add: norm_mult)
qed

lemma real_fourier_transform_cmult:
  fixes f :: "real \<Rightarrow> complex"
  assumes continuous: "continuous_on UNIV f"
    and integrable: "integrable lebesgue f"
  shows "real_fourier_transform (\<lambda>x. c * f x) \<xi> =
    c * real_fourier_transform f \<xi>"
  using fourier_weight_integrable[OF continuous integrable, of \<xi>]
  by (simp add: real_fourier_transform_def mult_ac)

lemma fourier_weight_cells_summable:
  fixes f :: "real \<Rightarrow> complex"
    and M :: "int \<Rightarrow> real"
  assumes continuous: "continuous_on UNIV f"
    and majorant: "M summable_on UNIV"
    and bound: "\<And>t n. t \<in> {0..1} \<Longrightarrow> norm (f (t + of_int n)) \<le> M n"
  shows "(\<lambda>n::int. \<integral>t.
    f (t + of_int n) * cis (-(2 * pi * \<xi> * (t + of_int n)))
    \<partial>(lebesgue_on {0..1})) summable_on UNIV"
proof -
  let ?u = "\<lambda>n t. f (t + of_int n) * cis (-(2 * pi * \<xi> * (t + of_int n)))"
  have shift: "continuous_on {0..1} (\<lambda>t. f (t + of_int n))" for n
    by (rule continuous_on_compose2[OF continuous])
      (auto intro: continuous_intros)
  have int_u: "integrable (lebesgue_on {0..1}) (?u n)" for n
    by (rule continuous_imp_integrable_real)
      (intro continuous_intros shift)
  have int_norm: "integrable (lebesgue_on {0..1})
      (\<lambda>t. norm (f (t + of_int n)))" for n
    by (rule continuous_imp_integrable_real)
      (intro continuous_intros shift)
  have cell_bound: "norm (\<integral>t. ?u n t \<partial>(lebesgue_on {0..1})) \<le> M n" for n
  proof -
    have "norm (\<integral>t. ?u n t \<partial>(lebesgue_on {0..1})) \<le>
      (\<integral>t. norm (f (t + of_int n)) \<partial>(lebesgue_on {0..1}))"
      by (rule Bochner_Integration.integral_norm_bound_integral[OF int_u int_norm])
        (simp add: norm_mult)
    also have "\<dots> = integral {0..1} (\<lambda>t. norm (f (t + of_int n)))"
      by (simp add: lebesgue_integral_eq_integral[OF int_norm])
    also have "\<dots> \<le> M n"
      by (rule periodization_cell_integral_bound[OF continuous]) (rule bound)
    finally show ?thesis .
  qed
  have "(\<lambda>n::int. norm (\<integral>t. ?u n t \<partial>(lebesgue_on {0..1})))
    summable_on UNIV"
    by (rule Infinite_Sum.abs_summable_on_comparison_test'[OF majorant])
      (use cell_bound in auto)
  then show ?thesis by (rule abs_summable_summable)
qed

lemma periodization_fourier_transform:
  fixes f :: "real \<Rightarrow> complex"
    and M :: "int \<Rightarrow> real"
  assumes continuous: "continuous_on UNIV f"
    and majorant: "M summable_on UNIV"
    and bound: "\<And>t n. t \<in> {0..1} \<Longrightarrow> norm (f (t + of_int n)) \<le> M n"
  shows "(\<integral>t. periodization f t * cis (-(2 * pi * of_int k * t))
      \<partial>(lebesgue_on {0..1})) = real_fourier_transform f (of_int k)"
proof -
  let ?g = "\<lambda>x. f x * cis (-(2 * pi * of_int k * x))"
  have continuous_g: "continuous_on UNIV ?g"
    by (intro continuous_intros continuous)
  have integrable_g: "integrable lebesgue ?g"
    by (rule fourier_weight_integrable[OF continuous
      periodization_integrable[OF continuous majorant bound]])
  have summable_g: "(\<lambda>n::int. \<integral>t. ?g (t + of_int n)
      \<partial>(lebesgue_on {0..1})) summable_on UNIV"
    by (rule fourier_weight_cells_summable[OF continuous majorant bound])
  have "(\<integral>t. periodization f t * cis (-(2 * pi * of_int k * t))
      \<partial>(lebesgue_on {0..1})) =
    (\<Sum>\<^sub>\<infinity>n::int. \<integral>t.
      f (t + of_int n) * cis (-(2 * pi * of_int k * t))
      \<partial>(lebesgue_on {0..1}))"
    by (rule periodization_fourier_integral_exchange[OF continuous majorant bound])
  also have "\<dots> =
    (\<Sum>\<^sub>\<infinity>n::int. \<integral>t. ?g (t + of_int n)
      \<partial>(lebesgue_on {0..1}))"
    by (simp add: cis_integer_shift)
  also have "\<dots> = (\<integral>x. ?g x \<partial>lebesgue)"
    by (rule integral_integer_tiling[OF continuous_g integrable_g summable_g])
  finally show ?thesis by (simp add: real_fourier_transform_def)
qed

lemma unit_period_integral_centered:
  fixes h :: "real \<Rightarrow> complex"
  assumes continuous: "continuous_on UNIV h"
    and periodic: "\<And>x. h (x + 1) = h x"
  shows "(\<integral>x. h x \<partial>(lebesgue_on {-1/2..1/2})) =
    (\<integral>x. h x \<partial>(lebesgue_on {0..1}))"
proof -
  have integrable_center: "h integrable_on {-1/2..1/2}"
    by (rule integrable_continuous_real)
      (use continuous in \<open>auto intro: continuous_on_subset\<close>)
  have integrable_base: "h integrable_on {0..1}"
    by (rule integrable_continuous_real)
      (use continuous in \<open>auto intro: continuous_on_subset\<close>)
  have split_center: "integral {-1/2..1/2} h =
      integral {-1/2..0} h + integral {0..1/2} h"
    using Henstock_Kurzweil_Integration.integral_combine
      [OF _ _ integrable_center, of 0] by auto
  have split_base: "integral {0..1} h =
      integral {0..1/2} h + integral {1/2..1} h"
    using Henstock_Kurzweil_Integration.integral_combine
      [OF _ _ integrable_base, of "1/2"] by auto
  have shift: "integral {-1/2..0} h = integral {1/2..1} h"
  proof -
    have "integral {-1/2..0} h =
      integral {-1/2..0} (h \<circ> ((+) 1))"
      by (rule integral_cong) (simp_all add: o_def add.commute periodic)
    also have "\<dots> = integral {1/2..1} h"
      using integral_shift_Icc_real[of "-1/2" 0 h 1] by simp
    finally show ?thesis .
  qed
  have hk: "integral {-1/2..1/2} h = integral {0..1} h"
    using split_center split_base shift by simp
  have int_center: "integrable (lebesgue_on {-1/2..1/2}) h"
    by (rule continuous_imp_integrable_real)
      (use continuous in \<open>auto intro: continuous_on_subset\<close>)
  have int_base: "integrable (lebesgue_on {0..1}) h"
    by (rule continuous_imp_integrable_real)
      (use continuous in \<open>auto intro: continuous_on_subset\<close>)
  have center_bridge: "(\<integral>x. h x \<partial>(lebesgue_on {-1/2..1/2})) =
      integral {-1/2..1/2} h"
    by (rule lebesgue_integral_eq_integral[OF int_center]) simp
  have base_bridge: "(\<integral>x. h x \<partial>(lebesgue_on {0..1})) =
      integral {0..1} h"
    by (rule lebesgue_integral_eq_integral[OF int_base]) simp
  show ?thesis using hk center_bridge base_bridge by simp
qed

lemma integral_scaled_symmetric:
  fixes h :: "real \<Rightarrow> complex"
  assumes continuous: "continuous_on UNIV h"
  shows "(\<integral>x. h (x / (2*pi)) \<partial>(lebesgue_on {-pi..pi})) /\<^sub>R
    (2*pi) =
    (\<integral>t. h t \<partial>(lebesgue_on {-1/2..1/2}))"
proof -
  let ?c = "2*pi"
  let ?g = "\<lambda>x. h (x / ?c)"
  have positive: "0 < ?c" by simp
  have continuous_g: "continuous_on UNIV ?g"
    by (rule continuous_on_compose2[OF continuous])
      (auto intro: continuous_intros)
  have int_g: "integrable (lebesgue_on {-pi..pi}) ?g"
    by (rule continuous_imp_integrable_real)
      (use continuous_g in \<open>auto intro: continuous_on_subset\<close>)
  have hk_integrable: "?g integrable_on {-pi..pi}"
    by (rule integrable_continuous_real)
      (use continuous_g in \<open>auto intro: continuous_on_subset\<close>)
  have hk: "(?g has_integral integral {-pi..pi} ?g) {-pi..pi}"
    by (rule integrable_integral[OF hk_integrable])
  have hk_box: "(?g has_integral integral {-pi..pi} ?g) (cbox (-pi) pi)"
    using hk by simp
  note scaled = has_integral_affinity'[OF hk_box positive, of 0]
  have scaled_h: "(h has_integral
      (integral {-pi..pi} ?g /\<^sub>R ?c)) {-1/2..1/2}"
    using scaled by (simp add: field_simps)
  have bridge_g: "(\<integral>x. ?g x \<partial>(lebesgue_on {-pi..pi})) =
      integral {-pi..pi} ?g"
    by (rule lebesgue_integral_eq_integral[OF int_g]) simp
  have "(\<integral>x. ?g x \<partial>(lebesgue_on {-pi..pi})) /\<^sub>R ?c =
      integral {-pi..pi} ?g /\<^sub>R ?c"
    by (simp only: bridge_g)
  also have "\<dots> = integral {-1/2..1/2} h"
    using integral_unique[OF scaled_h] by simp
  also have "\<dots> =
      (\<integral>t. h t \<partial>(lebesgue_on {-1/2..1/2}))"
  proof -
    have "integrable (lebesgue_on {-1/2..1/2}) h"
      by (rule continuous_imp_integrable_real)
        (use continuous in \<open>auto intro: continuous_on_subset\<close>)
    then show ?thesis
      by (rule lebesgue_integral_eq_integral[symmetric]) simp
  qed
  finally show ?thesis .
qed

lemma complex_divide_real_scalar:
  fixes z :: complex
  shows "z / of_real c = z /\<^sub>R c"
  by (simp add: divide_inverse scaleR_conv_of_real mult.commute)

lemma periodization_complex_fourier_coefficient:
  fixes f :: "real \<Rightarrow> complex"
    and M :: "int \<Rightarrow> real"
  assumes continuous: "continuous_on UNIV f"
    and majorant: "M summable_on UNIV"
    and bound: "\<And>t n. t \<in> {0..1} \<Longrightarrow> norm (f (t + of_int n)) \<le> M n"
  shows "complex_fourier_coefficient
    (\<lambda>x. periodization f (x / (2*pi))) k =
    real_fourier_transform f (of_int k)"
proof -
  let ?h = "\<lambda>t. periodization f t * cis (-(2 * pi * of_int k * t))"
  have continuous_P: "continuous_on UNIV (periodization f)"
    by (rule periodization_continuous[OF continuous majorant bound])
  have continuous_h: "continuous_on UNIV ?h"
    by (intro continuous_intros continuous_P)
  have periodic_h: "?h (t + 1) = ?h t" for t
    using cis_integer_shift[of k t 1]
    by (simp add: periodization_periodic)
  have scaled_point: "?h (x / (2*pi)) =
      periodization f (x / (2*pi)) * cis (-(of_int k*x))" for x
    by (simp add: field_simps)
  have scalar: "z / (2 * of_real pi) = z /\<^sub>R (2*pi)" for z :: complex
    using complex_divide_real_scalar[of z "2*pi"] by simp
  have "complex_fourier_coefficient
      (\<lambda>x. periodization f (x / (2*pi))) k =
      (\<integral>x. ?h (x / (2*pi)) \<partial>(lebesgue_on {-pi..pi})) /\<^sub>R (2*pi)"
    by (simp add: complex_fourier_coefficient_def scalar scaled_point)
  also have "\<dots> =
      (\<integral>t. ?h t \<partial>(lebesgue_on {-1/2..1/2}))"
    by (rule integral_scaled_symmetric[OF continuous_h])
  also have "\<dots> =
      (\<integral>t. ?h t \<partial>(lebesgue_on {0..1}))"
    by (rule unit_period_integral_centered[OF continuous_h periodic_h])
  also have "\<dots> = real_fourier_transform f (of_int k)"
    by (rule periodization_fourier_transform[OF continuous majorant bound])
  finally show ?thesis .
qed

end
