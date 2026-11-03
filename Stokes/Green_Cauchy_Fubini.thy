theory Green_Cauchy_Fubini
  imports Green_Cauchy_Area
begin

context
  fixes u :: "complex \<Rightarrow> complex"
    and g v :: "real \<Rightarrow> complex"
    and R C B :: real
  assumes uc: "continuous_on UNIV u"
    and C: "\<And>z. norm (u z) \<le> C"
    and supp: "\<And>z. z \<notin> cball 0 R \<Longrightarrow> u z = 0"
    and R: "0 \<le> R"
    and Cnonneg: "0 \<le> C"
    and gc: "continuous_on {0..1} g"
    and gb: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (g t) \<le> B"
    and vi: "v absolutely_integrable_on {0..1}"
begin

lemma green_cauchy_area_path_product_integrable:
  shows "integrable ((lebesgue_on {0..1}) \<Otimes>\<^sub>M
      (lborel :: complex measure))
    (\<lambda>(t,z). u z * v t / (z - g t))"
proof -
  let ?I = "{0..1::real}"
  let ?M = "lebesgue_on ?I"
  let ?N = "(lborel :: complex measure)"
  let ?K = "\<lambda>(t,z). u z * v t / (z - g t)"
  have Imeas: "?I \<in> sets lebesgue"
    by simp
  have gmeas: "g \<in> borel_measurable ?M"
    by (rule continuous_imp_measurable_on_sets_lebesgue[OF gc Imeas])
  have vmeas: "v \<in> borel_measurable ?M"
    using vi Imeas by (simp add: absolutely_integrable_measurable)
  have vnorm_int: "integrable ?M (\<lambda>t. norm (v t))"
    using vi Imeas by (simp add: absolutely_integrable_measurable comp_def)
  have umeas: "u \<in> borel_measurable ?N"
    using uc by (simp add: borel_measurable_continuous_onI)
  have Kmeas: "?K \<in> borel_measurable (?M \<Otimes>\<^sub>M ?N)"
    using gmeas vmeas umeas by measurable
  have zeroI: "(0::real) \<in> ?I"
    by simp
  have Bnonneg: "0 \<le> B"
    using gb[OF zeroI] norm_ge_zero[of "g 0"] by linarith
  have Radd: "0 \<le> R + B"
    using R Bnonneg by linarith
  let ?J = "\<integral>z. indicator (cball 0 (R + B)) z *\<^sub>R
    (1 / norm z) \<partial>?N"
  have Jint: "integrable ?N
      (\<lambda>z::complex. indicator (cball 0 (R + B)) z *\<^sub>R
        (1 / norm z))"
    by (rule green_inverse_cmod_integrable_cball[OF Radd])
  have Jnonneg: "0 \<le> ?J"
    by (rule Bochner_Integration.integral_nonneg) (auto simp: indicator_def)
  have inner: "integrable ?N (\<lambda>z. ?K (t,z))" if t: "t \<in> ?I" for t
  proof -
    have Kint: "integrable ?N (\<lambda>z. u z / (z - g t))"
      by (rule green_cauchy_area_kernel_integrable[OF uc C supp R Cnonneg])
    have int: "integrable ?N (\<lambda>z. v t * (u z / (z - g t)))"
      by (rule Bochner_Integration.integrable_mult_right[OF Kint])
    show ?thesis
      using int by (simp add: algebra_simps)
  qed
  have point_bound:
    "(\<integral>z. norm (?K (t,z)) \<partial>?N) \<le> C * ?J * norm (v t)"
    if t: "t \<in> ?I" for t
  proof -
    have eq: "norm (?K (t,z)) =
        norm (v t) * norm (u z / (z - g t))" for z
      by (simp add: norm_mult norm_divide)
    have eq_int: "(\<integral>z. norm (?K (t,z)) \<partial>?N) =
        norm (v t) *
          (\<integral>z. norm (u z / (z - g t)) \<partial>?N)"
      by (simp only: eq Bochner_Integration.integral_mult_right_zero)
    have b: "(\<integral>z. norm (u z / (z - g t)) \<partial>?N) \<le> C * ?J"
      by (rule green_cauchy_area_kernel_integral_bound
        [OF uc C supp R Cnonneg gb[OF t]])
    show ?thesis
      unfolding eq_int
      using mult_left_mono[OF b norm_ge_zero[of "v t"]]
      by (simp add: algebra_simps)
  qed
  have outer_meas: "(\<lambda>t. \<integral>z. norm (?K (t,z)) \<partial>?N)
      \<in> borel_measurable ?M"
    by (rule lborel.borel_measurable_lebesgue_integral)
      (use Kmeas in measurable)
  have outer_maj: "integrable ?M (\<lambda>t. C * ?J * norm (v t))"
    by (rule Bochner_Integration.integrable_mult_right[OF vnorm_int])
  have outer: "integrable ?M
      (\<lambda>t. \<integral>z. norm (?K (t,z)) \<partial>?N)"
    by (rule Bochner_Integration.integrable_bound[OF outer_maj outer_meas])
      (use point_bound Jnonneg Cnonneg in auto)
  have finM: "finite_measure ?M"
    by (rule finite_measure_lebesgue_on) simp
  have sigmaM: "sigma_finite_measure ?M"
    using finM by (rule finite_measure.axioms(1))
  have pair: "pair_sigma_finite ?M ?N"
    by (rule pair_sigma_finite.intro[OF sigmaM sigma_finite_lborel])
  show ?thesis
    by (rule pair_sigma_finite.Fubini_integrable[OF pair Kmeas outer])
      (use inner in auto)
qed

theorem green_cauchy_area_path_Fubini:
  shows "(\<integral>z. (\<integral>t. u z * v t / (z - g t)
      \<partial>(lebesgue_on {0..1})) \<partial>(lborel :: complex measure)) =
    (\<integral>t. (\<integral>z. u z * v t / (z - g t)
      \<partial>(lborel :: complex measure)) \<partial>(lebesgue_on {0..1}))"
proof -
  have prod: "integrable ((lebesgue_on {0..1}) \<Otimes>\<^sub>M
      (lborel :: complex measure))
    (\<lambda>(t,z). u z * v t / (z - g t))"
    by (rule green_cauchy_area_path_product_integrable)
  have pair: "pair_sigma_finite (lebesgue_on {0..1::real})
      (lborel :: complex measure)"
  proof (rule pair_sigma_finite.intro)
    have "finite_measure (lebesgue_on {0..1::real})"
      by (rule finite_measure_lebesgue_on) simp
    then show "sigma_finite_measure (lebesgue_on {0..1::real})"
      by (rule finite_measure.axioms(1))
    show "sigma_finite_measure (lborel :: complex measure)"
      by (rule sigma_finite_lborel)
  qed
  show ?thesis
    by (rule pair_sigma_finite.Fubini_integral[OF pair prod])
qed

end

lemma green_ac_cauchy_area_time_contour:
  fixes g v :: "real \<Rightarrow> complex"
    and u :: "complex \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (g has_vector_derivative v t) (at t)"
    and away: "z \<notin> path_image g"
    and tint: "integrable (lebesgue_on {0..1})
      (\<lambda>t. u z * v t / (z - g t))"
  shows "(\<integral>t. u z * v t / (z - g t)
      \<partial>(lebesgue_on {0..1})) =
    contour_integral g (\<lambda>w. u z / (z - w))"
proof -
  have ne: "z - w \<noteq> 0" if "w \<in> path_image g" for w
    using away that by auto
  have cont: "continuous_on (path_image g) (\<lambda>w. u z / (z - w))"
    by (intro continuous_intros) (use ne in auto)
  have contour: "contour_integral g (\<lambda>w. u z / (z - w)) =
      integral {0..1} (\<lambda>t. (u z / (z - g t)) * v t)"
    by (rule green_ac_contour_integral[OF ac null deriv cont])
  have lebesgue: "(\<integral>t. u z * v t / (z - g t)
      \<partial>(lebesgue_on {0..1})) =
      integral {0..1} (\<lambda>t. u z * v t / (z - g t))"
    by (rule lebesgue_integral_eq_integral[OF tint]) simp
  show ?thesis
    using lebesgue contour by (simp add: algebra_simps)
qed

end
