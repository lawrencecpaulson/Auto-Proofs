theory Complex_Fourier_Series
  imports "Fourier.Fourier" "HOL-Analysis.Complex_Transcendental"
begin

text \<open>Complex exponential Fourier coefficients on a circle of circumference 2pi.
  The normalization agrees with the usual coefficients of a 2pi-periodic function.\<close>

definition complex_fourier_coefficient :: "(real \<Rightarrow> complex) \<Rightarrow> int \<Rightarrow> complex" where
  "complex_fourier_coefficient g k =
    (\<integral>x. g x * cis (-(of_int k * x)) \<partial>(lebesgue_on {-pi..pi})) / of_real (2*pi)"

lemma complex_fourier_coefficient_zero_iff:
  "complex_fourier_coefficient g k = 0 \<longleftrightarrow>
    (\<integral>x. g x * cis (-(of_int k * x)) \<partial>(lebesgue_on {-pi..pi})) = 0"
  by (simp add: complex_fourier_coefficient_def)

lemma integrable_complex_cis:
  assumes g: "continuous_on UNIV g"
  shows "integrable (lebesgue_on {-pi..pi})
    (\<lambda>x. g x * cis (of_int k * x))"
proof (rule continuous_imp_integrable_real)
  show "continuous_on {-pi..pi} (\<lambda>x. g x * cis (of_int k * x))"
    using g by (intro continuous_intros continuous_on_subset[OF g]) auto
qed

lemma cis_add_inverse:
  "cis a + cis (-a) = 2 * of_real (cos a)"
  by (simp add: cis.ctr complex_eq_iff)

lemma cis_sub_inverse:
  "cis a - cis (-a) = 2 * \<i> * of_real (sin a)"
  by (simp add: cis.ctr complex_eq_iff)

lemma complex_cos_moment_zero:
  assumes g: "continuous_on UNIV g"
    and coeff: "\<And>k. complex_fourier_coefficient g k = 0"
  shows "(\<integral>x. g x * of_real (cos (of_int k * x))
      \<partial>(lebesgue_on {-pi..pi})) = 0"
proof -
  let ?M = "lebesgue_on {-pi..pi}"
  let ?a = "\<lambda>x. of_int k * x"
  have pos: "(\<integral>x. g x * cis (?a x) \<partial>?M) = 0"
    using coeff[of "-k"] by (simp add: complex_fourier_coefficient_zero_iff)
  have neg: "(\<integral>x. g x * cis (-?a x) \<partial>?M) = 0"
    using coeff[of k] by (simp add: complex_fourier_coefficient_zero_iff)
  have eq: "(\<lambda>x. g x * of_real (cos (?a x))) =
      (\<lambda>x. (g x * cis (?a x) + g x * cis (-?a x)) / 2)"
    by (rule ext) (simp add: cis_add_inverse algebra_simps flip: distrib_left)
  show ?thesis
    unfolding eq using pos neg integrable_complex_cis[OF g, of k]
      integrable_complex_cis[OF g, of "-k"]
    by (simp add: algebra_simps)
qed

lemma complex_sin_moment_zero:
  assumes g: "continuous_on UNIV g"
    and coeff: "\<And>k. complex_fourier_coefficient g k = 0"
  shows "(\<integral>x. g x * of_real (sin (of_int k * x))
      \<partial>(lebesgue_on {-pi..pi})) = 0"
proof -
  let ?M = "lebesgue_on {-pi..pi}"
  let ?a = "\<lambda>x. of_int k * x"
  have pos: "(\<integral>x. g x * cis (?a x) \<partial>?M) = 0"
    using coeff[of "-k"] by (simp add: complex_fourier_coefficient_zero_iff)
  have neg: "(\<integral>x. g x * cis (-?a x) \<partial>?M) = 0"
    using coeff[of k] by (simp add: complex_fourier_coefficient_zero_iff)
  have sine_difference: "g x * cis (?a x) - g x * cis (-?a x) =
      (2 * \<i>) * (g x * of_real (sin (?a x)))" for x
    using cis_sub_inverse[of "?a x"] by (simp add: algebra_simps)
  have eq: "(\<lambda>x. g x * of_real (sin (?a x))) =
      (\<lambda>x. (g x * cis (?a x) - g x * cis (-?a x)) / (2 * \<i>))"
    by (rule ext) (simp add: sine_difference)
  show ?thesis
    unfolding eq using pos neg integrable_complex_cis[OF g, of k]
      integrable_complex_cis[OF g, of "-k"]
    by (simp add: algebra_simps)
qed

lemma integrable_complex_trig:
  fixes g :: "real \<Rightarrow> complex"
  assumes g: "continuous_on UNIV g"
  shows "integrable (lebesgue_on {-pi..pi})
    (\<lambda>x. g x * of_real (cos (of_int k * x)))"
    and "integrable (lebesgue_on {-pi..pi})
    (\<lambda>x. g x * of_real (sin (of_int k * x)))"
proof -
  show "integrable (lebesgue_on {-pi..pi})
    (\<lambda>x. g x * of_real (cos (of_int k * x)))"
    by (rule continuous_imp_integrable_real)
      (use g in \<open>auto intro!: continuous_intros intro: continuous_on_subset\<close>)
  show "integrable (lebesgue_on {-pi..pi})
    (\<lambda>x. g x * of_real (sin (of_int k * x)))"
    by (rule continuous_imp_integrable_real)
      (use g in \<open>auto intro!: continuous_intros intro: continuous_on_subset\<close>)
qed

lemma component_cos_moment_zero:
  assumes g: "continuous_on UNIV g"
    and coeff: "\<And>k. complex_fourier_coefficient g k = 0"
  shows "(\<integral>x. Re (g x) * cos (of_int k * x)
      \<partial>(lebesgue_on {-pi..pi})) = 0"
    and "(\<integral>x. Im (g x) * cos (of_int k * x)
      \<partial>(lebesgue_on {-pi..pi})) = 0"
proof -
  note z = complex_cos_moment_zero[OF g coeff, of k]
  show "(\<integral>x. Re (g x) * cos (of_int k * x)
      \<partial>(lebesgue_on {-pi..pi})) = 0"
    using arg_cong[OF z, of Re] integrable_complex_trig[OF g, of k]
    by (subst (asm) integral_Re[symmetric]) simp_all
  show "(\<integral>x. Im (g x) * cos (of_int k * x)
      \<partial>(lebesgue_on {-pi..pi})) = 0"
    using arg_cong[OF z, of Im] integrable_complex_trig[OF g, of k]
    by (subst (asm) integral_Im[symmetric]) simp_all
qed

lemma component_sin_moment_zero:
  assumes g: "continuous_on UNIV g"
    and coeff: "\<And>k. complex_fourier_coefficient g k = 0"
  shows "(\<integral>x. Re (g x) * sin (of_int k * x)
      \<partial>(lebesgue_on {-pi..pi})) = 0"
    and "(\<integral>x. Im (g x) * sin (of_int k * x)
      \<partial>(lebesgue_on {-pi..pi})) = 0"
proof -
  note z = complex_sin_moment_zero[OF g coeff, of k]
  show "(\<integral>x. Re (g x) * sin (of_int k * x)
      \<partial>(lebesgue_on {-pi..pi})) = 0"
    using arg_cong[OF z, of Re] integrable_complex_trig[OF g, of k]
    by (subst (asm) integral_Re[symmetric]) simp_all
  show "(\<integral>x. Im (g x) * sin (of_int k * x)
      \<partial>(lebesgue_on {-pi..pi})) = 0"
    using arg_cong[OF z, of Im] integrable_complex_trig[OF g, of k]
    by (subst (asm) integral_Im[symmetric]) simp_all
qed

lemma Fourier_coefficient_zero_from_moments:
  fixes h :: "real \<Rightarrow> real"
  assumes cos: "\<And>k::int. (\<integral>x. h x * cos (of_int k * x)
    \<partial>(lebesgue_on {-pi..pi})) = 0"
    and sin: "\<And>k::int. (\<integral>x. h x * sin (of_int k * x)
    \<partial>(lebesgue_on {-pi..pi})) = 0"
  shows "Fourier_coefficient h n = 0"
proof -
  let ?M = "lebesgue_on {-pi..pi}"
  have base: "(\<integral>x. h x \<partial>?M) = 0"
    using cos[of 0] by simp
  have moment: "(\<integral>x. trigonometric_set n x * h x \<partial>?M) = 0"
  proof (cases "n=0")
    case True
    then show ?thesis using base
      by (simp add: trigonometric_set_def)
  next
    case False
    note nonzero = False
    show ?thesis
    proof (cases "odd n")
      case True
      have "(\<integral>x. h x * sin (real (Suc (n div 2)) * x) \<partial>?M) = 0"
        using sin[of "int (Suc (n div 2))"] by simp
      then show ?thesis using True nonzero
        by (simp add: trigonometric_set_def mult.commute)
    next
      case False
      have "(\<integral>x. h x * cos (real (n div 2) * x) \<partial>?M) = 0"
        using cos[of "int (n div 2)"] by simp
      moreover have "real n / 2 = real (n div 2)"
      proof -
        have "2 * (n div 2) = n" using False by presburger
        then show ?thesis by (simp add: of_nat_mult)
      qed
      ultimately show ?thesis using False nonzero
        by (simp add: trigonometric_set_def mult.commute)
    qed
  qed
  show ?thesis using moment
    by (simp add: Fourier_coefficient_def orthonormal_coeff_def l2product_def)
qed

lemma complex_fourier_coefficients_unique:
  fixes g :: "real \<Rightarrow> complex"
  assumes continuous: "continuous_on UNIV g"
    and periodic: "\<And>x. g (x + 2*pi) = g x"
    and coefficients: "\<And>k. complex_fourier_coefficient g k = 0"
  shows "g x = 0"
proof -
  have re_coeff: "Fourier_coefficient (\<lambda>x. Re (g x)) n = 0" for n
    by (rule Fourier_coefficient_zero_from_moments)
      (use component_cos_moment_zero[OF continuous coefficients]
           component_sin_moment_zero[OF continuous coefficients] in auto)
  have im_coeff: "Fourier_coefficient (\<lambda>x. Im (g x)) n = 0" for n
    by (rule Fourier_coefficient_zero_from_moments)
      (use component_cos_moment_zero[OF continuous coefficients]
           component_sin_moment_zero[OF continuous coefficients] in auto)
  have re_cont: "continuous_on UNIV (\<lambda>x. Re (g x))"
    using continuous by (intro continuous_intros)
  have im_cont: "continuous_on UNIV (\<lambda>x. Im (g x))"
    using continuous by (intro continuous_intros)
  have re_zero: "Re (g x) = 0"
    using Fourier_Fejer_Cesaro_summable_simple[OF re_cont, of x]
    by (simp add: re_coeff periodic LIMSEQ_const_iff)
  have im_zero: "Im (g x) = 0"
    using Fourier_Fejer_Cesaro_summable_simple[OF im_cont, of x]
    by (simp add: im_coeff periodic LIMSEQ_const_iff)
  show ?thesis using re_zero im_zero by (simp add: complex_eq_iff)
qed

end
