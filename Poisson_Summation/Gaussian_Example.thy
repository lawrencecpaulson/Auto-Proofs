theory Gaussian_Example
  imports Reconstruction "HOL-Probability.Characteristic_Functions"
begin

definition standard_gaussian :: "real \<Rightarrow> complex" where
  "standard_gaussian x = of_real (normal_density 0 1 x)"

lemma standard_gaussian_continuous:
  "continuous_on UNIV standard_gaussian"
  unfolding standard_gaussian_def normal_density_def
  by (intro continuous_intros) simp

lemma standard_gaussian_fourier_transform:
  "real_fourier_transform standard_gaussian \<xi> =
    of_real (exp (- ((2*pi*\<xi>)\<^sup>2) / 2))"
proof -
  let ?t = "-(2*pi*\<xi>)"
  let ?h = "\<lambda>x. cis (-(2*pi*\<xi>*x))"
  let ?g = "\<lambda>x. normal_density 0 1 x"
  have continuous_h: "continuous_on UNIV ?h"
    by (intro continuous_intros)
  have measurable_h: "?h \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF continuous_h] by simp
  have continuous_g: "continuous_on UNIV ?g"
    unfolding normal_density_def
    by (intro continuous_intros) simp
  have measurable_g: "?g \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF continuous_g] by simp
  have nonneg_g: "AE x in lborel. 0 \<le> ?g x"
    by simp
  have measurable_product:
    "(\<lambda>x. standard_gaussian x * ?h x) \<in> borel_measurable lborel"
  proof -
    have "continuous_on UNIV (\<lambda>x. standard_gaussian x * ?h x)"
      by (intro continuous_intros standard_gaussian_continuous continuous_h)
    then show ?thesis
      using borel_measurable_continuous_onI by simp
  qed
  have char_integral:
    "char std_normal_distribution ?t =
      (\<integral>x. standard_gaussian x * ?h x \<partial>lborel)"
  proof -
    have "char std_normal_distribution ?t =
      (\<integral>x. ?h x \<partial>(density lborel ?g))"
      by (simp add: char_def cis_conv_exp algebra_simps)
    also have "\<dots> =
      (\<integral>x. ?g x *\<^sub>R ?h x \<partial>lborel)"
      by (rule integral_density[OF measurable_h measurable_g nonneg_g])
    also have "\<dots> =
      (\<integral>x. standard_gaussian x * ?h x \<partial>lborel)"
      by (simp add: standard_gaussian_def scaleR_conv_of_real)
    finally show ?thesis .
  qed
  have "real_fourier_transform standard_gaussian \<xi> =
    (\<integral>x. standard_gaussian x * ?h x \<partial>lebesgue)"
    by (simp add: real_fourier_transform_def)
  also have "\<dots> =
    (\<integral>x. standard_gaussian x * ?h x \<partial>lborel)"
    using integral_completion[OF measurable_product]
    by simp
  also have "\<dots> = char std_normal_distribution ?t"
    using char_integral by simp
  also have "\<dots> = of_real (exp (- ((2*pi*\<xi>)\<^sup>2) / 2))"
    by (simp add: char_std_normal_distribution)
  finally show ?thesis .
qed

lemma gaussian_quadratic_bound:
  fixes a x :: real
  assumes a: "1 / 2 \<le> a"
  shows "exp (-(a * x\<^sup>2)) \<le> 4 / (1 + \<bar>x\<bar>)\<^sup>2"
proof -
  let ?d = "(1 + \<bar>x\<bar>)\<^sup>2"
  let ?e = "exp (a * x\<^sup>2)"
  have ax: "x\<^sup>2 / 2 \<le> a * x\<^sup>2"
    using mult_right_mono[OF a, of "x\<^sup>2"] by simp
  have square: "\<bar>x\<bar>\<^sup>2 = x\<^sup>2" by simp
  have square_nonneg: "0 \<le> (\<bar>x\<bar> - 1)\<^sup>2" by simp
  have poly_eq: "4 * (1 + x\<^sup>2 / 2) =
    ?d + (\<bar>x\<bar> - 1)\<^sup>2 + 2"
    using square by (simp add: power2_eq_square; algebra)
  have poly: "?d \<le> 4 * (1 + x\<^sup>2 / 2)"
    using poly_eq square_nonneg by linarith
  have exp_bound: "1 + a * x\<^sup>2 \<le> ?e"
    by simp
  have bound: "?d \<le> 4 * ?e"
  proof -
    have "4 * (1 + x\<^sup>2 / 2) \<le> 4 * (1 + a * x\<^sup>2)"
      by (rule mult_left_mono) (use ax in auto)
    also have "\<dots> \<le> 4 * ?e"
      by (rule mult_left_mono) (use exp_bound in auto)
    finally have tail: "4 * (1 + x\<^sup>2 / 2) \<le> 4 * ?e" .
    show ?thesis by (rule order_trans[OF poly tail])
  qed
  have dpos: "0 < ?d" by simp
  have epos: "0 < ?e" by simp
  have "exp (-(a * x\<^sup>2)) = 1 / ?e"
    by (simp add: exp_minus inverse_eq_divide)
  also have "\<dots> \<le> 4 / ?d"
    using bound dpos epos
    by (simp add: divide_le_eq)
  finally show ?thesis .
qed

lemma standard_gaussian_decay:
  "norm (standard_gaussian x) \<le> 4 * (1 + \<bar>x\<bar>) powr (-2)"
proof -
  have sqrt_ge: "1 \<le> sqrt (2 * pi)"
    using pi_ge_two by simp
  have density_le: "norm (standard_gaussian x) \<le> exp (- x\<^sup>2 / 2)"
  proof -
    have mul_le:
      "exp (- x\<^sup>2 / 2) \<le> exp (- x\<^sup>2 / 2) * sqrt (2 * pi)"
      using mult_left_mono[OF sqrt_ge, of "exp (- x\<^sup>2 / 2)"]
      by simp
    show ?thesis
      using mul_le sqrt_ge
      by (simp add: standard_gaussian_def std_normal_density_def
          norm_divide divide_le_eq)
  qed
  have gaussian_le: "exp (- x\<^sup>2 / 2) \<le> 4 / (1 + \<bar>x\<bar>)\<^sup>2"
    using gaussian_quadratic_bound[of "1/2" x] by simp
  show ?thesis
    using density_le gaussian_le
    by (simp add: powr_minus_divide)
qed

lemma standard_gaussian_transform_decay:
  "norm (real_fourier_transform standard_gaussian \<xi>) \<le>
    4 * (1 + \<bar>\<xi>\<bar>) powr (-2)"
proof -
  have one_le: "(1::real) \<le> 2 * pi"
    using pi_ge_two by linarith
  have square_le: "(1::real) \<le> (2 * pi)\<^sup>2"
    using power_mono[OF one_le, of 2] by simp
  have a_ge: "(1::real) / 2 \<le> (2 * pi)\<^sup>2 / 2"
    using square_le by linarith
  have gaussian_le:
    "exp (- ((2 * pi * \<xi>)\<^sup>2) / 2) \<le> 4 / (1 + \<bar>\<xi>\<bar>)\<^sup>2"
  proof -
    have square_eq:
      "((2 * pi * \<xi>)\<^sup>2) / 2 = ((2 * pi)\<^sup>2 / 2) * \<xi>\<^sup>2"
      by (simp add: power2_eq_square; algebra)
    show ?thesis
      using gaussian_quadratic_bound[OF a_ge, of \<xi>]
      by (simp add: square_eq)
  qed
  show ?thesis
    using gaussian_le
    by (simp add: standard_gaussian_fourier_transform powr_minus_divide)
qed

theorem standard_gaussian_poisson:
  "(\<Sum>\<^sub>\<infinity>n::int. standard_gaussian (x + of_int n)) =
    (\<Sum>\<^sub>\<infinity>k::int.
      of_real (exp (- ((2 * pi * of_int k)\<^sup>2) / 2)) *
      cis (2 * pi * of_int k * x))"
proof -
  have summation:
    "(\<Sum>\<^sub>\<infinity>n::int. standard_gaussian (x + of_int n)) =
      (\<Sum>\<^sub>\<infinity>k::int.
        real_fourier_transform standard_gaussian (of_int k) *
        cis (2 * pi * of_int k * x))"
    by (rule poisson_summation_power_decay
        [where A=4 and B=4 and p=2 and q=2])
      (simp_all add: standard_gaussian_continuous
        standard_gaussian_decay standard_gaussian_transform_decay)
  show ?thesis
    using summation
    by (simp add: standard_gaussian_fourier_transform)
qed

corollary standard_gaussian_poisson_zero:
  "(\<Sum>\<^sub>\<infinity>n::int.
      (of_real (exp (- (of_int n)\<^sup>2 / 2) / sqrt (2 * pi)) :: complex)) =
    (\<Sum>\<^sub>\<infinity>k::int.
      of_real (exp (- ((2 * pi * of_int k)\<^sup>2) / 2)))"
proof -
  have lhs:
    "(\<Sum>\<^sub>\<infinity>n::int. standard_gaussian (0 + of_int n)) =
      (\<Sum>\<^sub>\<infinity>n::int.
        of_real (exp (- (of_int n)\<^sup>2 / 2) / sqrt (2 * pi)))"
    by (rule infsum_cong)
      (simp add: standard_gaussian_def std_normal_density_def)
  have rhs:
    "(\<Sum>\<^sub>\<infinity>k::int.
        of_real (exp (- ((2 * pi * of_int k)\<^sup>2) / 2)) *
        cis (2 * pi * of_int k * 0)) =
      (\<Sum>\<^sub>\<infinity>k::int.
        of_real (exp (- ((2 * pi * of_int k)\<^sup>2) / 2)))"
    by (rule infsum_cong) simp
  have "(\<Sum>\<^sub>\<infinity>n::int.
      of_real (exp (- (of_int n)\<^sup>2 / 2) / sqrt (2 * pi))) =
    (\<Sum>\<^sub>\<infinity>n::int. standard_gaussian (0 + of_int n))"
    by (rule sym[OF lhs])
  also have "\<dots> =
    (\<Sum>\<^sub>\<infinity>k::int.
      of_real (exp (- ((2 * pi * of_int k)\<^sup>2) / 2)) *
      cis (2 * pi * of_int k * 0))"
    by (rule standard_gaussian_poisson)
  also have "\<dots> =
    (\<Sum>\<^sub>\<infinity>k::int.
      of_real (exp (- ((2 * pi * of_int k)\<^sup>2) / 2)))"
    by (rule rhs)
  finally show ?thesis .
qed

end
