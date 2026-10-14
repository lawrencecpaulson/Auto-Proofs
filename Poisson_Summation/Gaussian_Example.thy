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

lemma gaussian_quadratic_bound_positive:
  fixes c x :: real
  assumes c: "0 < c"
  shows "exp (-(c * x\<^sup>2)) \<le>
    (4 * (1 + 1 / c)) / (1 + \<bar>x\<bar>)\<^sup>2"
proof -
  let ?d = "(1 + \<bar>x\<bar>)\<^sup>2"
  let ?e = "exp (c * x\<^sup>2)"
  have poly: "?d \<le> 4 * (1 + x\<^sup>2)"
  proof -
    have square_nonneg: "0 \<le> (\<bar>x\<bar> - 1)\<^sup>2" by simp
    have square: "\<bar>x\<bar>\<^sup>2 = x\<^sup>2" by simp
    have eq:
      "4 * (1 + x\<^sup>2) =
        ?d + (\<bar>x\<bar> - 1)\<^sup>2 + 2 + 2 * x\<^sup>2"
      using square by (simp add: power2_eq_square; algebra)
    have x2: "0 \<le> x\<^sup>2" by simp
    show ?thesis using eq square_nonneg x2 by linarith
  qed
  have ratio: "1 + x\<^sup>2 \<le> (1 + 1 / c) * (1 + c * x\<^sup>2)"
    using c by (simp add: field_simps algebra_simps)
  have exp_bound: "1 + c * x\<^sup>2 \<le> ?e" by simp
  have factor: "0 \<le> 1 + 1 / c" using c by simp
  have bound: "?d \<le> (4 * (1 + 1 / c)) * ?e"
  proof -
    have "?d \<le> 4 * (1 + x\<^sup>2)" by (rule poly)
    also have "\<dots> \<le> 4 * ((1 + 1 / c) * (1 + c * x\<^sup>2))"
      using ratio by simp
    also have "\<dots> \<le> (4 * (1 + 1 / c)) * ?e"
    proof -
      have mid: "(4 * (1 + 1 / c)) * (1 + c * x\<^sup>2) \<le>
        (4 * (1 + 1 / c)) * ?e"
        by (rule mult_left_mono[OF exp_bound]) (use factor in auto)
      have eq: "4 * ((1 + 1 / c) * (1 + c * x\<^sup>2)) =
        (4 * (1 + 1 / c)) * (1 + c * x\<^sup>2)"
        by algebra
      show ?thesis using mid eq by metis
    qed
    finally show ?thesis .
  qed
  have "exp (-(c * x\<^sup>2)) = 1 / ?e"
    by (simp add: exp_minus inverse_eq_divide)
  also have "\<dots> \<le> (4 * (1 + 1 / c)) / ?d"
    using bound by (simp add: divide_le_eq)
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

definition dilated_standard_gaussian :: "real \<Rightarrow> real \<Rightarrow> complex" where
  "dilated_standard_gaussian a x = of_real a * standard_gaussian (a * x)"

lemma standard_gaussian_integrable:
  "integrable lebesgue standard_gaussian"
proof -
  have measurable: "standard_gaussian \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF standard_gaussian_continuous]
    by simp
  have int_lborel: "integrable lborel standard_gaussian"
    unfolding standard_gaussian_def
    by (rule integrable_of_real) simp
  show ?thesis
    using integrable_completion[OF measurable] int_lborel by simp
qed

lemma dilated_standard_gaussian_continuous:
  "continuous_on UNIV (dilated_standard_gaussian a)"
proof -
  have scaled: "continuous_on UNIV (\<lambda>x. standard_gaussian (a * x))"
    by (rule continuous_on_compose2[OF standard_gaussian_continuous])
      (auto intro: continuous_intros)
  show ?thesis
    unfolding dilated_standard_gaussian_def
    by (intro continuous_intros scaled)
qed

lemma dilated_standard_gaussian_fourier_transform:
  assumes a: "0 < a"
  shows "real_fourier_transform (dilated_standard_gaussian a) \<xi> =
    of_real (exp (- ((2 * pi * (\<xi> / a))\<^sup>2) / 2))"
proof -
  let ?f = "\<lambda>x. standard_gaussian (a * x)"
  have continuous_f: "continuous_on UNIV ?f"
    by (rule continuous_on_compose2[OF standard_gaussian_continuous])
      (auto intro: continuous_intros)
  have measurable_f: "?f \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF continuous_f] by simp
  have int_lborel: "integrable lborel ?f"
  proof -
    have measurable_std:
      "standard_gaussian \<in> borel_measurable lborel"
      using borel_measurable_continuous_onI[OF standard_gaussian_continuous]
      by simp
    have int_std: "integrable lborel standard_gaussian"
      using integrable_completion[OF measurable_std]
        standard_gaussian_integrable by simp
    show ?thesis
      using lborel_integrable_real_affine[OF int_std, of a 0] a by simp
  qed
  have int_f: "integrable lebesgue ?f"
    using integrable_completion[OF measurable_f] int_lborel by simp
  have "real_fourier_transform (dilated_standard_gaussian a) \<xi> =
    of_real a * real_fourier_transform ?f \<xi>"
    unfolding dilated_standard_gaussian_def
    by (rule real_fourier_transform_cmult[OF continuous_f int_f])
  also have "\<dots> =
    of_real a * (real_fourier_transform standard_gaussian (\<xi> / a) / of_real a)"
    by (simp add: real_fourier_transform_scale[OF standard_gaussian_continuous a])
  also have "\<dots> = of_real (exp (- ((2 * pi * (\<xi> / a))\<^sup>2) / 2))"
    using a by (simp add: standard_gaussian_fourier_transform)
  finally show ?thesis .
qed

lemma dilated_standard_gaussian_decay:
  assumes a: "0 < a"
  shows "norm (dilated_standard_gaussian a x) \<le>
    (4 * a * (1 + 1 / (a\<^sup>2 / 2))) * (1 + \<bar>x\<bar>) powr (-2)"
proof -
  let ?c = "a\<^sup>2 / 2"
  have c: "0 < ?c" using a by simp
  have sqrt_ge: "1 \<le> sqrt (2 * pi)"
    using pi_ge_two by simp
  have normal_le:
    "norm (standard_gaussian (a * x)) \<le> exp (- ?c * x\<^sup>2)"
  proof -
    have square_eq: "(a * x)\<^sup>2 / 2 = ?c * x\<^sup>2"
      by (simp add: power2_eq_square; algebra)
    have mul_le:
      "exp (- (a * x)\<^sup>2 / 2) \<le>
        exp (- (a * x)\<^sup>2 / 2) * sqrt (2 * pi)"
      using mult_left_mono[OF sqrt_ge, of "exp (- (a * x)\<^sup>2 / 2)"]
      by simp
    show ?thesis
      using mul_le sqrt_ge square_eq
      by (simp add: standard_gaussian_def std_normal_density_def
          norm_divide divide_le_eq)
  qed
  have norm_le:
    "norm (dilated_standard_gaussian a x) \<le> a * exp (- ?c * x\<^sup>2)"
    using mult_left_mono[OF normal_le, of a] a
    by (simp add: dilated_standard_gaussian_def norm_mult)
  have gaussian_le:
    "exp (- (?c * x\<^sup>2)) \<le>
      (4 * (1 + 1 / ?c)) / (1 + \<bar>x\<bar>)\<^sup>2"
    by (rule gaussian_quadratic_bound_positive[OF c])
  have "norm (dilated_standard_gaussian a x) \<le>
    a * ((4 * (1 + 1 / ?c)) / (1 + \<bar>x\<bar>)\<^sup>2)"
    using norm_le mult_left_mono[OF gaussian_le, of a] a by simp
  then show ?thesis
    by (simp add: powr_minus_divide mult_ac)
qed

lemma dilated_standard_gaussian_transform_decay:
  assumes a: "0 < a"
  shows "norm (real_fourier_transform (dilated_standard_gaussian a) \<xi>) \<le>
    (4 * (1 + 1 / ((2 * pi / a)\<^sup>2 / 2))) *
      (1 + \<bar>\<xi>\<bar>) powr (-2)"
proof -
  let ?c = "(2 * pi / a)\<^sup>2 / 2"
  have c: "0 < ?c" using a by simp
  have square_eq:
    "((2 * pi * (\<xi> / a))\<^sup>2) / 2 = ?c * \<xi>\<^sup>2"
    by (simp add: power2_eq_square; algebra)
  have exponent_eq:
    "- ((2 * pi * (\<xi> / a))\<^sup>2) / 2 = - (?c * \<xi>\<^sup>2)"
    using square_eq by linarith
  have gaussian_le:
    "exp (- ((2 * pi * (\<xi> / a))\<^sup>2) / 2) \<le>
      (4 * (1 + 1 / ?c)) / (1 + \<bar>\<xi>\<bar>)\<^sup>2"
    using gaussian_quadratic_bound_positive[OF c, of \<xi>] exponent_eq
    by metis
  show ?thesis
    using gaussian_le
    by (simp add: dilated_standard_gaussian_fourier_transform[OF a]
        powr_minus_divide)
qed

theorem dilated_standard_gaussian_poisson:
  assumes a: "0 < a"
  shows "(\<Sum>\<^sub>\<infinity>n::int.
      dilated_standard_gaussian a (x + of_int n)) =
    (\<Sum>\<^sub>\<infinity>k::int.
      of_real (exp (- ((2 * pi * (of_int k / a))\<^sup>2) / 2)) *
      cis (2 * pi * of_int k * x))"
proof -
  let ?A = "4 * a * (1 + 1 / (a\<^sup>2 / 2))"
  let ?B = "4 * (1 + 1 / ((2 * pi / a)\<^sup>2 / 2))"
  have A: "0 \<le> ?A" using a by simp
  have B: "0 \<le> ?B" using a by simp
  have summation:
    "(\<Sum>\<^sub>\<infinity>n::int.
        dilated_standard_gaussian a (x + of_int n)) =
      (\<Sum>\<^sub>\<infinity>k::int.
        real_fourier_transform (dilated_standard_gaussian a) (of_int k) *
        cis (2 * pi * of_int k * x))"
  proof (rule poisson_summation_power_decay
      [where A="?A" and B="?B" and p=2 and q=2])
    show "continuous_on UNIV (dilated_standard_gaussian a)"
      by (rule dilated_standard_gaussian_continuous)
    show "0 \<le> ?A" by (rule A)
    show "0 \<le> ?B" by (rule B)
    show "(1::real) < 2" by simp
    show "(1::real) < 2" by simp
    show "norm (dilated_standard_gaussian a y) \<le>
      ?A * (1 + \<bar>y\<bar>) powr (-2)" for y
      by (rule dilated_standard_gaussian_decay[OF a])
    show "norm (real_fourier_transform (dilated_standard_gaussian a) y) \<le>
      ?B * (1 + \<bar>y\<bar>) powr (-2)" for y
      by (rule dilated_standard_gaussian_transform_decay[OF a])
  qed
  show ?thesis
    using summation
    by (simp add: dilated_standard_gaussian_fourier_transform[OF a])
qed

definition jacobi_theta :: "real \<Rightarrow> complex" where
  "jacobi_theta t =
    (\<Sum>\<^sub>\<infinity>n::int.
      of_real (exp (- pi * t * (of_int n)\<^sup>2)))"

lemma jacobi_theta_summable:
  assumes t: "0 < t"
  shows "(\<lambda>n::int.
      (of_real (exp (- pi * t * (of_int n)\<^sup>2)) :: complex))
    summable_on UNIV"
proof -
  let ?c = "pi * t"
  let ?B = "4 * (1 + 1 / ?c)"
  let ?M = "\<lambda>n::int. ?B * (1 + \<bar>real_of_int n\<bar>) powr (-2)"
  have c: "0 < ?c" using t by simp
  have w: "(\<lambda>n::int. (1 + \<bar>real_of_int n\<bar>) powr (-2))
    summable_on UNIV"
    by (rule summable_int_power_decay) simp
  have M: "?M summable_on UNIV"
    by (rule summable_on_cmult_right[OF w])
  have bound:
    "norm (of_real (exp (- pi * t * (of_int n)\<^sup>2)) :: complex) \<le>
      ?M n" for n :: int
    using gaussian_quadratic_bound_positive[OF c, of "of_int n"]
    by (simp add: powr_minus_divide mult_ac)
  have "(\<lambda>n::int.
    norm (of_real (exp (- pi * t * (of_int n)\<^sup>2)) :: complex))
    summable_on UNIV"
    by (rule Infinite_Sum.abs_summable_on_comparison_test'[OF M])
      (use bound in auto)
  then show ?thesis by (rule abs_summable_summable)
qed

lemma dilated_standard_gaussian_sqrt:
  assumes t: "0 < t"
  shows "dilated_standard_gaussian (sqrt (2 * pi * t)) x =
    of_real (sqrt t) * of_real (exp (- pi * t * x\<^sup>2))"
proof -
  have sqrt_pos: "0 < sqrt (2 * pi)" by simp
  have scale:
    "sqrt (2 * pi * t) / sqrt (2 * pi) = sqrt t"
    using sqrt_pos t
    by (simp add: real_sqrt_mult mult_ac)
  have exponent:
    "(sqrt (2 * pi * t) * x)\<^sup>2 / 2 = pi * t * x\<^sup>2"
    using t by (simp add: power_mult power2_eq_square mult_ac)
  have density_eq:
    "sqrt (2 * pi * t) *
      normal_density 0 1 (sqrt (2 * pi * t) * x) =
      sqrt t * exp (- pi * t * x\<^sup>2)"
  proof -
    have "sqrt (2 * pi * t) *
        normal_density 0 1 (sqrt (2 * pi * t) * x) =
      (sqrt (2 * pi * t) / sqrt (2 * pi)) *
        exp (- (sqrt (2 * pi * t) * x)\<^sup>2 / 2)"
      by (simp add: std_normal_density_def; algebra)
    also have "\<dots> = sqrt t * exp (- pi * t * x\<^sup>2)"
      using scale exponent by simp
    finally show ?thesis .
  qed
  show ?thesis
    using density_eq
    by (metis dilated_standard_gaussian_def standard_gaussian_def
        of_real_mult)
qed

lemma dilated_standard_gaussian_sqrt_fourier:
  assumes t: "0 < t"
  shows "real_fourier_transform
      (dilated_standard_gaussian (sqrt (2 * pi * t))) \<xi> =
    of_real (exp (- pi * \<xi>\<^sup>2 / t))"
proof -
  let ?a = "sqrt (2 * pi * t)"
  have a: "0 < ?a" using t by simp
  have a2: "?a\<^sup>2 = 2 * pi * t"
    using t by simp
  have exponent:
    "((2 * pi * (\<xi> / ?a))\<^sup>2) / 2 = pi * \<xi>\<^sup>2 / t"
    using a a2 t
    by (simp add: power_divide power_mult power2_eq_square field_simps)
  show ?thesis
    using dilated_standard_gaussian_fourier_transform[OF a, of \<xi>]
      exponent by simp
qed

theorem jacobi_theta_transformation:
  assumes t: "0 < t"
  shows "of_real (sqrt t) * jacobi_theta t = jacobi_theta (1 / t)"
proof -
  let ?a = "sqrt (2 * pi * t)"
  have a: "0 < ?a" using t by simp
  have lhs:
    "(\<Sum>\<^sub>\<infinity>n::int. dilated_standard_gaussian ?a (0 + of_int n)) =
      of_real (sqrt t) * jacobi_theta t"
  proof -
    have "(\<Sum>\<^sub>\<infinity>n::int.
        dilated_standard_gaussian ?a (0 + of_int n)) =
      (\<Sum>\<^sub>\<infinity>n::int.
        of_real (sqrt t) *
        of_real (exp (- pi * t * (of_int n)\<^sup>2)))"
      by (rule infsum_cong)
        (simp add: dilated_standard_gaussian_sqrt[OF t])
    also have "\<dots> = of_real (sqrt t) * jacobi_theta t"
      by (simp add: jacobi_theta_def infsum_cmult_right')
    finally show ?thesis .
  qed
  have rhs:
    "(\<Sum>\<^sub>\<infinity>k::int.
        of_real (exp (- ((2 * pi * (of_int k / ?a))\<^sup>2) / 2)) *
        cis (2 * pi * of_int k * 0)) =
      jacobi_theta (1 / t)"
  proof -
    have pointwise:
      "(of_real (exp (- ((2 * pi * (of_int k / ?a))\<^sup>2) / 2)) :: complex) =
        of_real (exp (- pi * (of_int k)\<^sup>2 / t))"
      for k :: int
    proof -
      show ?thesis
        using dilated_standard_gaussian_fourier_transform[OF a, of "of_int k"]
          dilated_standard_gaussian_sqrt_fourier[OF t, of "of_int k"]
        by metis
    qed
    have "(\<Sum>\<^sub>\<infinity>k::int.
        of_real (exp (- ((2 * pi * (of_int k / ?a))\<^sup>2) / 2)) *
        cis (2 * pi * of_int k * 0)) =
      (\<Sum>\<^sub>\<infinity>k::int.
        of_real (exp (- pi * (of_int k)\<^sup>2 / t)))"
      by (rule infsum_cong)
        (simp only: mult_zero_right cis_zero mult_1_right pointwise;
          simp add: times_divide_eq_right)
    also have "\<dots> = jacobi_theta (1 / t)"
      by (simp add: jacobi_theta_def field_simps)
    finally show ?thesis .
  qed
  show ?thesis
    using dilated_standard_gaussian_poisson[OF a, of 0] lhs rhs by simp
qed

end
