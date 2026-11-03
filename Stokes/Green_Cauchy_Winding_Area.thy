theory Green_Cauchy_Winding_Area
  imports Green_Cauchy_Fubini
begin

definition green_cauchy_area_transform ::
    "(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> complex" where
  "green_cauchy_area_transform u w =
    (\<integral>z. u z / (z - w) \<partial>(lborel :: complex measure))"

lemma green_cauchy_area_transform_translate:
  fixes u :: "complex \<Rightarrow> complex"
  assumes uc: "continuous_on UNIV u"
  shows "green_cauchy_area_transform u w =
    (\<integral>y. u (y + w) / y \<partial>(lborel :: complex measure))"
proof -
  let ?H = "\<lambda>z::complex. u z / (z - w)"
  have Tmeas: "((+) w) \<in> (lborel :: complex measure) \<rightarrow>\<^sub>M borel"
    by measurable
  have Hmeas: "?H \<in> borel_measurable (borel :: complex measure)"
    using uc by (intro borel_measurable_divide)
      (auto intro!: borel_measurable_continuous_onI continuous_intros)
  have "(\<integral>z. ?H z \<partial>(lborel :: complex measure)) =
      (\<integral>y. ?H (w + y) \<partial>lborel)"
    using integral_distr[OF Tmeas Hmeas]
    by (simp add: lborel_distr_plus)
  then show ?thesis
    by (simp add: green_cauchy_area_transform_def add.commute)
qed

lemma green_cauchy_area_transform_continuous:
  fixes u :: "complex \<Rightarrow> complex"
  assumes uc: "continuous_on UNIV u"
    and C: "\<And>z. norm (u z) \<le> C"
    and supp: "\<And>z. z \<notin> cball 0 R \<Longrightarrow> u z = 0"
    and R: "0 \<le> R"
    and Cnonneg: "0 \<le> C"
  shows "continuous_on UNIV (green_cauchy_area_transform u)"
proof (rule continuous_on_sequentiallyI)
  fix a :: "nat \<Rightarrow> complex" and w :: complex
  assume arange: "\<forall>n. a n \<in> UNIV" and win: "w \<in> UNIV"
    and aw: "a \<longlonglongrightarrow> w"
  obtain B where B: "\<And>n. norm (a n) \<le> B"
    using convergent_imp_bounded[OF aw]
    by (auto simp: bounded_iff)
  have Bnonneg: "0 \<le> B"
    using B[of 0] norm_ge_zero[of "a 0"] by linarith
  let ?T = "R + B"
  let ?H = "\<lambda>y::complex. indicator (cball 0 ?T) y *\<^sub>R (1 / norm y)"
  let ?F = "\<lambda>b y::complex. u (y + b) / y"
  have Tnonneg: "0 \<le> ?T"
    using R Bnonneg by linarith
  have Hint: "integrable (lborel :: complex measure) ?H"
    by (rule green_inverse_cmod_integrable_cball[OF Tnonneg])
  have Hmeas: "integrable (lborel :: complex measure) (\<lambda>y. C * ?H y)"
    by (rule Bochner_Integration.integrable_mult_right[OF Hint])
  have Fmeas: "?F b \<in> borel_measurable (lborel :: complex measure)" for b
  proof -
    have cont: "continuous_on UNIV (\<lambda>y::complex. u (y + b))"
      by (rule continuous_on_compose2[OF uc])
        (auto intro!: continuous_intros)
    have umeas: "(\<lambda>y::complex. u (y + b)) \<in>
        borel_measurable (lborel :: complex measure)"
      using cont by (simp add: borel_measurable_continuous_onI)
    show ?thesis
      using umeas by measurable
  qed
  have bound: "norm (?F (a n) y) \<le> C * ?H y" for n y
  proof (cases "y \<in> cball 0 ?T")
    case True
    then show ?thesis
      using C[of "y + a n"] Cnonneg
      by (simp add: indicator_def norm_divide divide_right_mono)
  next
    case False
    have tri: "norm y \<le> norm (y + a n) + norm (a n)"
      using norm_triangle_ineq[of "y + a n" "-a n"] by simp
    have gt: "?T < norm y"
      using False by simp
    have gtR: "R < norm (y + a n)"
      using gt tri B[of n] by linarith
    have "y + a n \<notin> cball 0 R"
      using gtR by simp
    then show ?thesis
      using Cnonneg by (simp add: supp indicator_def False)
  qed
  have lim: "AE y in (lborel :: complex measure).
      (\<lambda>n. ?F (a n) y) \<longlonglongrightarrow> ?F w y"
  proof (rule AE_mp[OF AE_lborel_singleton[of 0]])
    show "AE y in (lborel :: complex measure).
      y \<noteq> 0 \<longrightarrow> (\<lambda>n. ?F (a n) y) \<longlonglongrightarrow> ?F w y"
    proof (rule AE_I2, intro impI)
      fix y :: complex
      assume "y \<noteq> 0"
      have yl: "(\<lambda>n. y + a n) \<longlonglongrightarrow> y + w"
        using aw by (intro tendsto_intros)
      have ul: "(\<lambda>n. u (y + a n)) \<longlonglongrightarrow> u (y + w)"
        by (rule continuous_on_tendsto_compose[OF uc yl]) simp_all
      show "(\<lambda>n. ?F (a n) y) \<longlonglongrightarrow> ?F w y"
        using ul \<open>y \<noteq> 0\<close> by (intro tendsto_intros)
    qed
  qed
  have ilim: "(\<lambda>n. \<integral>y. ?F (a n) y
      \<partial>(lborel :: complex measure)) \<longlonglongrightarrow>
      (\<integral>y. ?F w y \<partial>(lborel :: complex measure))"
    by (rule integral_dominated_convergence[OF Fmeas Fmeas Hmeas lim])
      (use bound Cnonneg in \<open>auto simp: indicator_def\<close>)
  show "(\<lambda>n. green_cauchy_area_transform u (a n))
      \<longlonglongrightarrow> green_cauchy_area_transform u w"
    using ilim by (simp only: green_cauchy_area_transform_translate[OF uc])
qed

lemma green_cauchy_area_inner_eq:
  fixes u :: "complex \<Rightarrow> complex"
  shows "(\<integral>z. u z * c / (z - w)
      \<partial>(lborel :: complex measure)) =
    c * green_cauchy_area_transform u w"
proof -
  have eq: "(\<lambda>z. u z * c / (z - w)) =
      (\<lambda>z. c * (u z / (z - w)))"
    by (rule ext) (simp add: algebra_simps)
  show ?thesis
    unfolding green_cauchy_area_transform_def
    by (simp only: eq Bochner_Integration.integral_mult_right_zero)
qed

definition green_winding_off_path :: "(real \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> complex" where
  "green_winding_off_path g z =
    (if z \<in> path_image g then 0 else winding_number g z)"

lemma green_winding_off_path_measurable:
  fixes g :: "real \<Rightarrow> complex"
  assumes path: "path g"
  shows "green_winding_off_path g \<in>
    borel_measurable (lborel :: complex measure)"
proof -
  have closed: "closed (path_image g)"
    by (rule compact_imp_closed) (rule compact_path_image[OF path])
  have sets: "path_image g \<in> sets (borel :: complex measure)"
    using closed by simp
  have cont: "continuous_on (- path_image g)
      (\<lambda>z. winding_number g z)"
    by (rule continuous_on_winding_number[OF path])
  have H: "(\<lambda>z. if z \<in> path_image g then 0 else winding_number g z)
      \<in> borel_measurable (borel :: complex measure)"
    by (rule borel_measurable_continuous_on_if[OF sets])
      (use cont in auto)
  have eq: "green_winding_off_path g =
      (\<lambda>z. if z \<in> path_image g then 0 else winding_number g z)"
    by (rule ext) (simp add: green_winding_off_path_def)
  then show ?thesis
    using H unfolding eq by simp
qed

lemma green_ac_path_image_lborel_null:
  fixes g :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
  shows "path_image g \<in> null_sets (lborel :: complex measure)"
proof -
  have path: "path g"
    by (rule green_ac_path_is_path[OF ac])
  have closed: "closed (path_image g)"
    by (rule compact_imp_closed) (rule compact_path_image[OF path])
  have sets: "path_image g \<in> sets (lborel :: complex measure)"
    using closed by simp
  have null: "path_image g \<in> null_sets (lebesgue :: complex measure)"
    using green_ac_path_image_negligible[OF ac]
    by (simp add: negligible_iff_null_sets)
  show ?thesis
    using null sets
    by (simp add: null_sets_completion_iff)
qed

context
  fixes g v :: "real \<Rightarrow> complex"
    and N :: "real set"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (g has_vector_derivative v t) (at t)"
begin

lemma green_ac_cauchy_area_time_winding:
  fixes u :: "complex \<Rightarrow> complex"
  assumes away: "z \<notin> path_image g"
    and tint: "integrable (lebesgue_on {0..1})
      (\<lambda>t. u z * v t / (z - g t))"
  shows "(\<integral>t. u z * v t / (z - g t)
      \<partial>(lebesgue_on {0..1})) =
    -(2 * pi * \<i>) * u z * winding_number g z"
proof -
  have time: "(\<integral>t. u z * v t / (z - g t)
      \<partial>(lebesgue_on {0..1})) =
    contour_integral g (\<lambda>w. u z / (z - w))"
    by (rule green_ac_cauchy_area_time_contour)
      (use ac null deriv away tint in auto)
  have eq: "u z / (z - w) = (-u z) * (1 / (w - z))" for w
  proof -
    have denom: "z - w = -(w - z)" by (simp add: algebra_simps)
    have "u z / (z - w) = u z / (-(w - z))"
      by (simp only: denom)
    also have "\<dots> = (-u z) * (1 / (w - z))"
      by (simp only: divide_inverse inverse_minus_eq
        minus_mult_right[symmetric] minus_mult_left mult_1_left)
    finally show ?thesis .
  qed
  have factor: "contour_integral g (\<lambda>w. u z / (z - w)) =
      (-u z) * contour_integral g (\<lambda>w. 1 / (w - z))"
    by (simp only: eq contour_integral_lmul)
  interpret V: green_ac_velocity g v N
    by standard (use ac null deriv in auto)
  have wind: "contour_integral g (\<lambda>w. 1 / (w - z)) =
      2 * pi * \<i> * winding_number g z"
    by (rule V.cauchy_kernel_contour_integral[OF away])
  show ?thesis
    using time factor wind by (simp add: algebra_simps)
qed

context
  fixes u :: "complex \<Rightarrow> complex"
    and C R B :: real
  assumes uc: "continuous_on UNIV u"
    and C: "\<And>z. norm (u z) \<le> C"
    and supp: "\<And>z. z \<notin> cball 0 R \<Longrightarrow> u z = 0"
    and R: "0 \<le> R"
    and Cnonneg: "0 \<le> C"
    and gb: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (g t) \<le> B"
begin

theorem green_ac_cauchy_winding_area:
  shows "integrable (lborel :: complex measure)
    (\<lambda>z. u z * green_winding_off_path g z)"
    and "(\<integral>t. (\<integral>z. u z * v t / (z - g t)
        \<partial>(lborel :: complex measure))
      \<partial>(lebesgue_on {0..1})) =
      -(2 * pi * \<i>) *
        (\<integral>z. u z * green_winding_off_path g z
          \<partial>(lborel :: complex measure))"
    and "(\<integral>t. v t * green_cauchy_area_transform u (g t)
      \<partial>(lebesgue_on {0..1})) =
      -(2 * pi * \<i>) *
        (\<integral>z. u z * green_winding_off_path g z
          \<partial>(lborel :: complex measure))"
    and "integrable (lebesgue_on {0..1})
      (\<lambda>t. v t * green_cauchy_area_transform u (g t))"
proof -
  let ?M = "lebesgue_on {0..1::real}"
  let ?L = "\<lambda>z::complex. \<integral>t. u z * v t / (z - g t) \<partial>?M"
  let ?W = "\<lambda>z::complex. u z * green_winding_off_path g z"
  have gc: "continuous_on {0..1} g"
    by (rule absolutely_continuous_on_imp_continuous[OF ac is_interval_cc])
  have vi: "v absolutely_integrable_on {0..1}"
    by (rule green_ac_velocity_absolutely_integrable[OF ac null])
      (use deriv in auto)
  have prod: "integrable (?M \<Otimes>\<^sub>M (lborel :: complex measure))
      (\<lambda>(t,z). u z * v t / (z - g t))"
    by (rule green_cauchy_area_path_product_integrable
      [OF uc C supp R Cnonneg gc gb vi])
  have finM: "finite_measure ?M"
    by (rule finite_measure_lebesgue_on) simp
  have sigmaM: "sigma_finite_measure ?M"
    using finM by (rule finite_measure.axioms(1))
  have pair: "pair_sigma_finite ?M (lborel :: complex measure)"
    by (rule pair_sigma_finite.intro[OF sigmaM sigma_finite_lborel])
  have Lint: "integrable (lborel :: complex measure) ?L"
    by (rule pair_sigma_finite.integrable_snd[OF pair prod])
  have ae_tint: "AE z in (lborel :: complex measure).
      integrable ?M (\<lambda>t. u z * v t / (z - g t))"
    by (rule pair_sigma_finite.AE_integrable_snd[OF pair prod])
  have ae_away: "AE z in (lborel :: complex measure).
      z \<notin> path_image g"
    by (rule AE_not_in[OF green_ac_path_image_lborel_null[OF ac]])
  have ae_eq: "AE z in (lborel :: complex measure).
      ?L z = -(2 * pi * \<i>) * ?W z"
    using ae_tint ae_away
  proof eventually_elim
    fix z :: complex
    assume tint: "integrable ?M (\<lambda>t. u z * v t / (z - g t))"
      and away: "z \<notin> path_image g"
    have "?L z = -(2 * pi * \<i>) * u z * winding_number g z"
      by (rule green_ac_cauchy_area_time_winding)
        (use away tint in auto)
    then show "?L z = -(2 * pi * \<i>) * ?W z"
      using away by (simp add: green_winding_off_path_def algebra_simps)
  qed
  have path: "path g"
    by (rule green_ac_path_is_path[OF ac])
  have umeas: "u \<in> borel_measurable (lborel :: complex measure)"
    using uc by (simp add: borel_measurable_continuous_onI)
  have Wmeas: "?W \<in> borel_measurable (lborel :: complex measure)"
    using umeas green_winding_off_path_measurable[OF path] by measurable
  have scale_meas: "(\<lambda>z. -(2 * pi * \<i>) * ?W z)
      \<in> borel_measurable (lborel :: complex measure)"
    using Wmeas by measurable
  have Lmeas: "?L \<in> borel_measurable (lborel :: complex measure)"
    using Lint by (rule borel_measurable_integrable)
  have scale_int: "integrable (lborel :: complex measure)
      (\<lambda>z. -(2 * pi * \<i>) * ?W z)"
    using Lint integrable_cong_AE[OF Lmeas scale_meas ae_eq] by blast
  have scale_ne: "-(2 * pi * \<i>) \<noteq> 0"
    by simp
  have unscaled_int: "integrable (lborel :: complex measure)
      (\<lambda>z. inverse (-(2 * pi * \<i>)) *
        (-(2 * pi * \<i>) * ?W z))"
    by (rule Bochner_Integration.integrable_mult_right[OF scale_int])
  have unscaled_eq: "(\<lambda>z. inverse (-(2 * pi * \<i>)) *
        (-(2 * pi * \<i>) * ?W z)) = ?W"
    by (simp only: fun_eq_iff mult.assoc[symmetric]
      left_inverse[OF scale_ne] mult_1_left refl; simp)
  have Wint: "integrable (lborel :: complex measure) ?W"
    using unscaled_int by (simp only: unscaled_eq)
  show "integrable (lborel :: complex measure) ?W"
    by (rule Wint)
  have eq_int: "(\<integral>z. ?L z \<partial>(lborel :: complex measure)) =
      (\<integral>z. -(2 * pi * \<i>) * ?W z \<partial>lborel)"
    by (rule integral_cong_AE[OF Lmeas scale_meas ae_eq])
  have Fubini: "(\<integral>z. ?L z \<partial>(lborel :: complex measure)) =
      (\<integral>t. (\<integral>z. u z * v t / (z - g t)
        \<partial>(lborel :: complex measure)) \<partial>?M)"
    by (rule green_cauchy_area_path_Fubini
      [OF uc C supp R Cnonneg gc gb vi])
  have main: "(\<integral>t. (\<integral>z. u z * v t / (z - g t)
        \<partial>(lborel :: complex measure)) \<partial>?M) =
      -(2 * pi * \<i>) *
        (\<integral>z. ?W z \<partial>(lborel :: complex measure))"
    using Fubini eq_int
    by (simp only: Bochner_Integration.integral_mult_right_zero)
  show "(\<integral>t. (\<integral>z. u z * v t / (z - g t)
        \<partial>(lborel :: complex measure)) \<partial>?M) =
      -(2 * pi * \<i>) *
        (\<integral>z. ?W z \<partial>(lborel :: complex measure))"
    by (rule main)
  have area_eq: "(\<integral>z. u z * v t / (z - g t)
      \<partial>(lborel :: complex measure)) =
      v t * green_cauchy_area_transform u (g t)" for t
    by (rule green_cauchy_area_inner_eq)
  show "(\<integral>t. v t * green_cauchy_area_transform u (g t)
      \<partial>?M) =
      -(2 * pi * \<i>) *
        (\<integral>z. ?W z \<partial>(lborel :: complex measure))"
    using main by (simp only: area_eq)
  have timeint: "integrable ?M
      (\<lambda>t. \<integral>z. u z * v t / (z - g t)
        \<partial>(lborel :: complex measure))"
    by (rule pair_sigma_finite.integrable_fst[OF pair prod])
  show "integrable ?M
      (\<lambda>t. v t * green_cauchy_area_transform u (g t))"
    using timeint by (simp only: area_eq)
qed

theorem green_ac_cauchy_contour_winding_area:
  shows "green_cauchy_area_transform u contour_integrable_on g"
    and "contour_integral g (green_cauchy_area_transform u) =
      -(2 * pi * \<i>) *
        (\<integral>z. u z * green_winding_off_path g z
          \<partial>(lborel :: complex measure))"
proof -
  let ?M = "lebesgue_on {0..1::real}"
  have cont: "continuous_on (path_image g)
      (green_cauchy_area_transform u)"
    by (rule continuous_on_subset
      [OF green_cauchy_area_transform_continuous
        [OF uc C supp R Cnonneg]]) simp_all
  show "green_cauchy_area_transform u contour_integrable_on g"
    by (rule green_ac_contour_integrable[OF ac null deriv cont])
  have tint: "integrable ?M
      (\<lambda>t. v t * green_cauchy_area_transform u (g t))"
    by (rule green_ac_cauchy_winding_area(4))
  have contour: "contour_integral g (green_cauchy_area_transform u) =
      (\<integral>t. v t * green_cauchy_area_transform u (g t)
        \<partial>?M)"
  proof -
    have rint: "contour_integral g (green_cauchy_area_transform u) =
        integral {0..1} (\<lambda>t.
          green_cauchy_area_transform u (g t) * v t)"
      by (rule green_ac_contour_integral[OF ac null deriv cont])
    have lint: "(\<integral>t. v t * green_cauchy_area_transform u (g t)
        \<partial>?M) =
        integral {0..1} (\<lambda>t.
          v t * green_cauchy_area_transform u (g t))"
      by (rule lebesgue_integral_eq_integral[OF tint]) simp
    show ?thesis
      using rint lint by (simp add: mult.commute)
  qed
  show "contour_integral g (green_cauchy_area_transform u) =
      -(2 * pi * \<i>) *
        (\<integral>z. u z * green_winding_off_path g z
          \<partial>(lborel :: complex measure))"
    unfolding contour
    by (rule green_ac_cauchy_winding_area(3))
qed

end

end

end
