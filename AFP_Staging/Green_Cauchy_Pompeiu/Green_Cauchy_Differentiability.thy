theory Green_Cauchy_Differentiability
  imports Green_Cauchy_Winding_Area
begin

lemma green_cauchy_translated_kernel_integrable:
  fixes u :: "complex \<Rightarrow> complex"
  assumes uc: "continuous_on UNIV u"
    and bound: "\<And>z. norm (u z) \<le> C"
    and supp: "\<And>z. z \<notin> cball 0 R \<Longrightarrow> u z = 0"
    and R: "0 \<le> R"
    and C: "0 \<le> C"
  shows "integrable (lborel :: complex measure)
    (\<lambda>y. u (y + w) / y)"
proof -
  have Kint: "integrable (lborel :: complex measure)
      (\<lambda>z. u z / (z - w))"
    by (rule green_cauchy_area_kernel_integrable[OF uc bound supp R C])
  have Tmeas: "((+) w) \<in> (lborel :: complex measure) \<rightarrow>\<^sub>M borel"
    by measurable
  have "integrable (lborel :: complex measure)
      (\<lambda>y. u (w + y) / ((w + y) - w))"
    by (rule integrable_distr[OF Tmeas])
      (use Kint in \<open>simp add: lborel_distr_plus\<close>)
  then show ?thesis
    by (simp add: add.commute)
qed

lemma green_cauchy_translated_derivative_integrable:
  fixes Du :: "complex \<Rightarrow> complex \<Rightarrow> complex"
  assumes Du_cont: "\<And>h. continuous_on UNIV (\<lambda>z. Du z h)"
    and Du_bound: "\<And>z h. norm (Du z h) \<le> D * norm h"
    and Du_supp: "\<And>z h. z \<notin> cball 0 R \<Longrightarrow> Du z h = 0"
    and R: "0 \<le> R"
    and D: "0 \<le> D"
  shows "integrable (lborel :: complex measure)
    (\<lambda>y. Du (y + w) h / y)"
  by (rule green_cauchy_translated_kernel_integrable
    [OF Du_cont Du_bound Du_supp R])
    (use D in auto)

lemma green_cauchy_translated_kernel_bound:
  fixes u :: "complex \<Rightarrow> complex"
  assumes ub: "\<And>z. norm (u z) \<le> C"
    and supp: "\<And>z. z \<notin> cball 0 R \<Longrightarrow> u z = 0"
    and C: "0 \<le> C"
    and T: "R + norm w \<le> T"
  shows "norm (u (y + w) / y) \<le>
    C * (indicator (cball 0 T) y *\<^sub>R (1 / norm y))"
proof -
  have "norm (u (y + w) / ((y + w) - w)) \<le>
      C * (indicator (cball w T) (y + w) *\<^sub>R
        (1 / norm ((y + w) - w)))"
    by (rule green_cauchy_area_kernel_pointwise_bound
      [OF ub supp C T])
  then show ?thesis
    by (simp add: dist_norm indicator_def)
qed

lemma green_cauchy_translated_integral_bound:
  fixes u :: "complex \<Rightarrow> complex"
  assumes uc: "continuous_on UNIV u"
    and ub: "\<And>z. norm (u z) \<le> C"
    and supp: "\<And>z. z \<notin> cball 0 R \<Longrightarrow> u z = 0"
    and R: "0 \<le> R"
    and C: "0 \<le> C"
    and T: "R + norm w \<le> T"
  shows "norm (\<integral>y. u (y + w) / y
      \<partial>(lborel :: complex measure)) \<le>
    C * (\<integral>y. indicator (cball 0 T) y *\<^sub>R (1 / norm y)
      \<partial>(lborel :: complex measure))"
proof -
  let ?M = "(lborel :: complex measure)"
  let ?K = "\<lambda>y::complex. indicator (cball 0 T) y *\<^sub>R (1 / norm y)"
  have T0: "0 \<le> T" using R T norm_ge_zero[of w] by linarith
  have Kint: "integrable ?M ?K"
    by (rule green_inverse_cmod_integrable_cball[OF T0])
  have Fint: "integrable ?M (\<lambda>y. u (y + w) / y)"
    by (rule green_cauchy_translated_kernel_integrable[OF uc ub supp R C])
  have Nint: "integrable ?M (\<lambda>y. norm (u (y + w) / y))"
    using Fint by (rule integrable_norm)
  have CKint: "integrable ?M (\<lambda>y. C * ?K y)"
    by (rule Bochner_Integration.integrable_mult_right[OF Kint])
  have "norm (\<integral>y. u (y + w) / y \<partial>?M) \<le>
      (\<integral>y. norm (u (y + w) / y) \<partial>?M)"
    by (rule integral_norm_bound)
  also have "\<dots> \<le> (\<integral>y. C * ?K y \<partial>?M)"
    by (rule Bochner_Integration.integral_mono[OF Nint CKint])
      (use green_cauchy_translated_kernel_bound[OF ub supp C T] in auto)
  also have "\<dots> = C * (\<integral>y. ?K y \<partial>?M)"
    by (rule integral_mult_right_zero)
  finally show ?thesis .
qed

lemma green_cauchy_integrated_derivative_bounded_linear:
  fixes Du :: "complex \<Rightarrow> complex \<Rightarrow> complex"
  assumes Du_lin: "\<And>z. linear (Du z)"
    and Du_cont: "\<And>h. continuous_on UNIV (\<lambda>z. Du z h)"
    and Du_bound: "\<And>z h. norm (Du z h) \<le> D * norm h"
    and Du_supp: "\<And>z h. z \<notin> cball 0 R \<Longrightarrow> Du z h = 0"
    and R: "0 \<le> R"
    and D: "0 \<le> D"
  shows "bounded_linear
    (\<lambda>h. \<integral>y. Du (y + w) h / y
      \<partial>(lborel :: complex measure))"
proof (rule bounded_linear_intro[where K=
    "D * (\<integral>y. indicator (cball 0 (R + norm w)) y *\<^sub>R
      (1 / norm y) \<partial>(lborel :: complex measure))"])
  let ?M = "(lborel :: complex measure)"
  have dint: "integrable ?M (\<lambda>y. Du (y + w) h / y)" for h
    by (rule green_cauchy_translated_derivative_integrable
      [OF Du_cont Du_bound Du_supp R D])
  have scale: "Du z (r *\<^sub>R h) = r *\<^sub>R Du z h" for z r h
    using Du_lin[of z] by (simp add: linear_iff)
  show "(\<integral>y. Du (y + w) (h + k) / y \<partial>?M) =
      (\<integral>y. Du (y + w) h / y \<partial>?M) +
      (\<integral>y. Du (y + w) k / y \<partial>?M)" for h k
    using dint[of h] dint[of k]
    by (simp add: linear_add[OF Du_lin] integral_add
      add_divide_distrib)
  show "(\<integral>y. Du (y + w) (scaleR r h) / y \<partial>?M) =
      scaleR r (\<integral>y. Du (y + w) h / y \<partial>?M)" for r h
  proof -
    have "(\<lambda>y. Du (y + w) (scaleR r h) / y) =
        (\<lambda>y. scaleR r (Du (y + w) h / y))"
      by (rule ext) (simp only: scale; simp add: scaleR_conv_of_real algebra_simps)
    then show ?thesis
      by (simp only: integral_scaleR_right)
  qed
  show "norm (\<integral>y. Du (y + w) h / y \<partial>?M) \<le>
      norm h * (D * (\<integral>y. indicator (cball 0 (R + norm w)) y
        *\<^sub>R (1 / norm y) \<partial>?M))" for h
  proof -
    have "norm (\<integral>y. Du (y + w) h / y \<partial>?M) \<le>
        (D * norm h) *
          (\<integral>y. indicator (cball 0 (R + norm w)) y
            *\<^sub>R (1 / norm y) \<partial>?M)"
      by (rule green_cauchy_translated_integral_bound
        [OF Du_cont Du_bound Du_supp R _ order_refl])
        (use D in auto)
    then show ?thesis
      by (simp add: mult.commute mult.left_commute)
  qed
qed

lemma green_cauchy_density_uniform_linearization:
  fixes u :: "complex \<Rightarrow> complex"
    and Du :: "complex \<Rightarrow> complex \<Rightarrow> complex"
  assumes uder: "\<And>z. (u has_derivative Du z) (at z)"
    and modulus: "\<And>e. 0 < e \<Longrightarrow> \<exists>d>0. \<forall>z z'.
      norm (z' - z) < d \<longrightarrow> onorm (Du z' - Du z) \<le> e"
  shows "\<And>e. 0 < e \<Longrightarrow> \<exists>d>0. \<forall>z h.
    norm h < d \<longrightarrow>
      norm (u (z + h) - u z - Du z h) \<le> e * norm h"
proof -
  fix e :: real
  assume e: "0 < e"
  obtain d where d: "0 < d" and mod:
      "\<And>z z'. norm (z' - z) < d \<Longrightarrow>
        onorm (Du z' - Du z) \<le> e"
    using modulus[OF e] by blast
  show "\<exists>d>0. \<forall>z h. norm h < d \<longrightarrow>
      norm (u (z + h) - u z - Du z h) \<le> e * norm h"
  proof (intro exI[of _ d] conjI allI impI)
    show "0 < d" by (rule d)
    fix z h :: complex
    assume h: "norm h < d"
    let ?S = "ball z d"
    have seg: "z + t *\<^sub>R ((z + h) - z) \<in> ?S"
      if "t \<in> {0..1}" for t :: real
    proof -
      have "t * norm h \<le> 1 * norm h"
        by (rule mult_right_mono) (use that in auto)
      then show ?thesis
        using h that by (simp add: dist_norm norm_scaleR)
    qed
    have der: "(u has_derivative Du x) (at x within ?S)"
      if "x \<in> ?S" for x
      by (rule has_derivative_at_withinI[OF uder])
    have bd: "onorm (Du x - Du z) \<le> e" if "x \<in> ?S" for x
      using that by (intro mod) (simp add: dist_norm norm_minus_commute)
    have zin: "z \<in> ?S" using d by simp
    have "norm (u (z + h) - u z - Du z ((z + h) - z)) \<le>
        norm ((z + h) - z) * e"
      by (rule differentiable_bound_linearization
        [OF seg der bd zin])
    then show "norm (u (z + h) - u z - Du z h) \<le> e * norm h"
      by (simp add: mult.commute)
  qed
qed

locale green_cauchy_regular_density =
  fixes u :: "complex \<Rightarrow> complex"
    and Du :: "complex \<Rightarrow> complex \<Rightarrow> complex"
    and C D R :: real
  assumes uc: "continuous_on UNIV u"
    and uder: "\<And>z. (u has_derivative Du z) (at z)"
    and Du_cont: "\<And>h. continuous_on UNIV (\<lambda>z. Du z h)"
    and u_bound: "\<And>z. norm (u z) \<le> C"
    and Du_bound: "\<And>z h. norm (Du z h) \<le> D * norm h"
    and u_supp: "\<And>z. z \<notin> cball 0 R \<Longrightarrow> u z = 0"
    and Du_supp: "\<And>z h. z \<notin> cball 0 R \<Longrightarrow> Du z h = 0"
    and modulus: "\<And>e. 0 < e \<Longrightarrow> \<exists>d>0. \<forall>z z'.
      norm (z' - z) < d \<longrightarrow> onorm (Du z' - Du z) \<le> e"
    and R: "0 \<le> R"
    and C: "0 \<le> C"
    and D: "0 \<le> D"
begin

theorem green_cauchy_area_transform_has_derivative:
  shows "(green_cauchy_area_transform u has_derivative
    (\<lambda>h. \<integral>y. Du (y + w) h / y
      \<partial>(lborel :: complex measure))) (at w)"
proof -
  let ?M = "(lborel :: complex measure)"
  let ?A = "\<lambda>h. \<integral>y. Du (y + w) h / y \<partial>?M"
  let ?T = "R + 1 + norm w"
  let ?K = "\<lambda>y::complex. indicator (cball 0 ?T) y *\<^sub>R (1 / norm y)"
  let ?I = "\<integral>y. ?K y \<partial>?M"
  have Du_lin: "linear (Du z)" for z
    using has_derivative_bounded_linear[OF uder[of z]]
    by (rule bounded_linear.linear)
  have Alin: "bounded_linear ?A"
    by (rule green_cauchy_integrated_derivative_bounded_linear
      [OF Du_lin Du_cont Du_bound Du_supp R D])
  have T0: "0 \<le> ?T" using R by simp
  have Kint: "integrable ?M ?K"
    by (rule green_inverse_cmod_integrable_cball[OF T0])
  have I0: "0 \<le> ?I"
    by (rule Bochner_Integration.integral_nonneg)
      (auto simp: indicator_def)
  have lin: "\<And>e. 0 < e \<Longrightarrow> \<exists>d>0. \<forall>z h.
      norm h < d \<longrightarrow>
      norm (u (z + h) - u z - Du z h) \<le> e * norm h"
    by (rule green_cauchy_density_uniform_linearization[OF uder modulus])
  have small: "\<forall>e>0. \<exists>d>0. \<forall>z. norm (z - w) < d \<longrightarrow>
      norm (green_cauchy_area_transform u z -
        green_cauchy_area_transform u w - ?A (z - w))
        \<le> e * norm (z - w)"
  proof (intro allI impI)
    fix e :: real
    assume e: "0 < e"
    define q where "q = e / (?I + 1)"
    have I1: "0 < ?I + 1" using I0 by linarith
    have qpos: "0 < q"
      unfolding q_def by (rule divide_pos_pos[OF e I1])
    have qI: "q * ?I \<le> e"
    proof -
      have "q * ?I \<le> q * (?I + 1)"
        by (rule mult_left_mono) (use qpos in auto)
      also have "\<dots> = e"
        using I1 by (simp add: q_def)
      finally show ?thesis .
    qed
    obtain d where d: "0 < d" and rem:
        "\<And>x h. norm h < d \<Longrightarrow>
          norm (u (x + h) - u x - Du x h) \<le> q * norm h"
      using lin[OF qpos] by blast
    let ?delta = "min d 1"
    show "\<exists>d>0. \<forall>z. norm (z - w) < d \<longrightarrow>
        norm (green_cauchy_area_transform u z -
          green_cauchy_area_transform u w - ?A (z - w))
          \<le> e * norm (z - w)"
    proof (intro exI[of _ ?delta] conjI allI impI)
      show "0 < ?delta" using d by simp
      fix z :: complex
      assume zclose: "norm (z - w) < ?delta"
      let ?h = "z - w"
      let ?rho = "\<lambda>x::complex. u (x + ?h) - u x - Du x ?h"
      have hsmall: "norm ?h < d" "norm ?h < 1"
        using zclose by auto
      have shift_cont: "continuous_on UNIV (\<lambda>x. u (x + ?h))"
        by (rule continuous_on_compose2[OF uc])
          (auto intro!: continuous_intros)
      have rho_cont: "continuous_on UNIV ?rho"
        by (intro continuous_intros shift_cont uc Du_cont)
      have rho_bound: "norm (?rho x) \<le> q * norm ?h" for x
        by (rule rem[OF hsmall(1)])
      have rho_supp: "?rho x = 0" if "x \<notin> cball 0 (R + 1)"
        for x
      proof -
        have xgt: "R + 1 < norm x" using that by simp
        have tri: "norm x \<le> norm (x + ?h) + norm ?h"
          using norm_triangle_ineq[of "x + ?h" "-?h"]
          by (simp add: norm_minus_commute)
        have xhgt: "R < norm (x + ?h)"
          using xgt tri hsmall(2) by linarith
        have xout: "x \<notin> cball 0 R"
          using xgt by simp
        have xhout: "x + ?h \<notin> cball 0 R"
          using xhgt by simp
        show ?thesis
          by (simp add: u_supp[OF xout] u_supp[OF xhout]
            Du_supp[OF xout])
      qed
      have Rplus: "0 \<le> R + 1" using R by simp
      have qh: "0 \<le> q * norm ?h" using qpos by simp
      have rho_bnd: "norm (\<integral>y. ?rho (y + w) / y \<partial>?M)
          \<le> (q * norm ?h) * ?I"
        by (rule green_cauchy_translated_integral_bound
          [OF rho_cont rho_bound rho_supp Rplus qh order_refl])
      have int_z: "integrable ?M (\<lambda>y. u (y + z) / y)"
        by (rule green_cauchy_translated_kernel_integrable
          [OF uc u_bound u_supp R C])
      have int_w: "integrable ?M (\<lambda>y. u (y + w) / y)"
        by (rule green_cauchy_translated_kernel_integrable
          [OF uc u_bound u_supp R C])
      have int_D: "integrable ?M (\<lambda>y. Du (y + w) ?h / y)"
        by (rule green_cauchy_translated_derivative_integrable
          [OF Du_cont Du_bound Du_supp R D])
      have rho_eq: "(\<lambda>y. ?rho (y + w) / y) =
          (\<lambda>y. u (y + z) / y - u (y + w) / y -
            Du (y + w) ?h / y)"
        by (rule ext)
          (simp add: add_divide_distrib diff_divide_distrib algebra_simps)
      have eq_int: "(\<integral>y. ?rho (y + w) / y \<partial>?M) =
          green_cauchy_area_transform u z -
            green_cauchy_area_transform u w - ?A ?h"
        unfolding rho_eq
        using int_z int_w int_D
        by (simp add: integral_diff
          green_cauchy_area_transform_translate[OF uc])
      have "norm (green_cauchy_area_transform u z -
          green_cauchy_area_transform u w - ?A ?h)
          \<le> q * ?I * norm ?h"
        using rho_bnd unfolding eq_int by (simp add: algebra_simps)
      also have "\<dots> \<le> e * norm ?h"
        using mult_right_mono[OF qI norm_ge_zero[of ?h]]
        by (simp add: mult.commute)
      finally show "norm (green_cauchy_area_transform u z -
          green_cauchy_area_transform u w - ?A (z - w))
          \<le> e * norm (z - w)" .
    qed
  qed
  show ?thesis
    using Alin small by (simp add: has_derivative_at_alt)
qed

lemma green_cauchy_area_transform_frechet_derivative:
  "frechet_derivative (green_cauchy_area_transform u) (at w) h =
    green_cauchy_area_transform (\<lambda>z. Du z h) w"
proof -
  have deriv: "frechet_derivative (green_cauchy_area_transform u) (at w) =
      (\<lambda>h. \<integral>y. Du (y + w) h / y
        \<partial>(lborel :: complex measure))"
    by (rule frechet_derivative_at[symmetric])
      (rule green_cauchy_area_transform_has_derivative)
  show ?thesis
    by (simp add: deriv green_cauchy_area_transform_translate
      [OF Du_cont])
qed

theorem green_cauchy_area_transform_C1:
  "Ck_on 1 (green_cauchy_area_transform u) UNIV"
proof -
  have diff: "green_cauchy_area_transform u differentiable (at w)"
    for w
    unfolding differentiable_def
    using green_cauchy_area_transform_has_derivative by blast
  have cont: "continuous_on UNIV
      (\<lambda>w. frechet_derivative
        (green_cauchy_area_transform u) (at w) h)"
    for h
  proof -
    have bound: "norm (Du z h) \<le> D * norm h" for z
      by (rule Du_bound)
    have support: "Du z h = 0" if "z \<notin> cball 0 R" for z
      by (rule Du_supp[OF that])
    have "continuous_on UNIV
        (green_cauchy_area_transform (\<lambda>z. Du z h))"
      by (rule green_cauchy_area_transform_continuous
        [OF Du_cont bound support R])
        (use D in auto)
    then show ?thesis
      by (simp add: green_cauchy_area_transform_frechet_derivative)
  qed
  show ?thesis
    using diff cont
    by (simp add: One_nat_def Ck_on_Suc_iff Ck_on_0_iff)
qed

end

end
