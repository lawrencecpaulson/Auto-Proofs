theory Isoperimetric
  imports Arc_Length_Reparametrization "Fourier.Fourier" "Green.Green" "HOL-ex.Sketch_and_Explore" 
begin

text \<open>
  Formalisation of the isoperimetric inequality, following John Harrison's
  HOL Light proof in @{text "100/isoperimetric.ml"}.

  The proof has five parts:
  \<^enum> Convex curve lemmas (switching between views of a convex simple closed curve)
  \<^enum> The Wirtinger inequality
  \<^enum> A special case of Green's theorem for convex area
  \<^enum> The isoperimetric theorem for convex curves
  \<^enum> Convexification of an arbitrary rectifiable simple closed curve
  \<^enum> The full isoperimetric theorem

  Infrastructure is provided by the prerequisite theories:
  \<^item> @{text Bounded_Variation}: bounded variation and vector variation
  \<^item> @{text Absolute_Continuity}: absolute continuity and FTC
  \<^item> @{text Rectifiable_Path}: rectifiable paths and path length
  \<^item> @{text Arc_Length_Reparametrization}: arc length reparametrization

  AFP dependencies:
  \<^item> @{text Fourier}: trigonometric orthonormal system, Bessel inequality,
    L2 Fourier convergence (useful for Wirtinger inequality)
  \<^item> @{text Lp} (via Fourier): Hölder inequality, Minkowski inequality
  \<^item> @{text Green}: Green's theorem for type I/II regions, line integrals
\<close>

section \<open>Convex curve lemmas\<close>

text \<open>Switching between views of a convex simple closed curve.\<close>

lemma convex_hull_eq_closure_inside:
  fixes g :: "real \<Rightarrow> complex"
  assumes g: "simple_path g" "pathfinish g = pathstart g"
    and conv: "convex (inside (path_image g))"
  shows "convex hull (path_image g) = closure (inside (path_image g))"
proof (rule equalityI)
  have compact_pi: "compact (path_image g)"
    using compact_simple_path_image[OF assms(1)] .
  have bounded_inside: "bounded (inside (path_image g))"
    using Jordan_inside_outside g by blast
  have frontier_inside: "frontier (inside (path_image g)) = path_image g"
    using Jordan_inside_outside g by blast
  show "convex hull (path_image g) \<subseteq> closure (inside (path_image g))"
    by (metis Diff_subset conv convex_closure convex_hull_subset frontier_def
        frontier_inside hull_same)
  have "compact (closure (inside (path_image g)))"
    using compact_closure local.bounded_inside by blast
  then show "closure (inside (path_image g)) \<subseteq> convex hull (path_image g)"
    by (metis (no_types, lifting) Krein_Milman_frontier conv closure_closure convex_closure
        convex_interior_closure frontier_def frontier_inside order.refl)
qed


lemma frontier_convex_hull_eq_path_image:
  fixes g :: "real \<Rightarrow> complex"
  assumes g: "simple_path g" "pathfinish g = pathstart g"
    and conv: "convex (inside (path_image g))"
  shows "frontier (convex hull (path_image g)) = path_image g"
proof -
  have eq: "convex hull (path_image g) = closure (inside (path_image g))"
    by (rule convex_hull_eq_closure_inside[OF assms])
  have open_inside: "open (inside (path_image g))"
    and frontier_inside: "frontier (inside (path_image g)) = path_image g"
    using Jordan_inside_outside g by blast+
  have "frontier (convex hull (path_image g)) =
    closure (inside (path_image g)) - interior (closure (inside (path_image g)))"
    by (simp add: eq frontier_def)
  also have "\<dots> = closure (inside (path_image g)) - inside (path_image g)"
    using convex_interior_closure[OF assms(3)] interior_open[OF open_inside] by simp
  also have "\<dots> = frontier (inside (path_image g))"
    using interior_open[OF open_inside] by (simp add: frontier_def)
  also have "\<dots> = path_image g"
    by (rule frontier_inside)
  finally show ?thesis .
qed

lemma frontier_convex_hull_eq_path_image':
  fixes g :: "real \<Rightarrow> complex"
  assumes "simple_path g" "pathfinish g = pathstart g"
          "path_image g \<subseteq> frontier (convex hull (path_image g))"
  shows "frontier (convex hull (path_image g)) = path_image g"
proof (rule equalityI)
  show "frontier (convex hull path_image g) \<subseteq> path_image g"
  proof -
    have compact_pi: "compact (path_image g)"
      using compact_simple_path_image[OF assms(1)] .
    have closed_hull: "closed (convex hull (path_image g))"
      using compact_convex_hull[OF compact_pi] compact_imp_closed by blast
    have bounded_hull: "bounded (convex hull (path_image g))"
      using bounded_convex_hull compact_imp_bounded[OF compact_pi] by blast
    have convex_hull: "convex (convex hull (path_image g))"
      by (rule convex_convex_hull)
    \<comment> \<open>The interior of the convex hull is connected, bounded, and disjoint from path_image g\<close>
    have int_sub: "interior (convex hull (path_image g)) \<inter> path_image g = {}"
      using assms(3) frontier_def by auto
    have "connected (interior (convex hull (path_image g)))"
      using convex_connected convex_interior convex_hull by blast
    moreover have "bounded (interior (convex hull (path_image g)))"
      using bounded_hull bounded_interior by blast
    moreover have "interior (convex hull (path_image g)) \<subseteq> - path_image g"
      using int_sub by blast
    ultimately have int_inside: "interior (convex hull (path_image g)) \<subseteq> inside (path_image g)"
      using Jordan_inside_outside[of g] assms(1,2) 
      by (smt (verit, ccfv_threshold) Diff_eq_empty_iff compl_le_compl_iff connected_Int_frontier
          convex_hull double_compl hull_antimono inf.absorb_iff2 inside_outside int_sub interior_Int
          interior_eq outside_subset_convex subset_hull sup.coboundedI2)
    \<comment> \<open>Also inside \<subseteq> convex hull (since outside contains complement of hull)\<close>
    have "- (convex hull (path_image g)) \<subseteq> outside (path_image g)"
      by (simp add: hull_subset outside_subset_convex)
    hence inside_sub: "inside (path_image g) \<subseteq> convex hull (path_image g)"
      by (metis Un_subset_iff compl_le_swap2 union_with_inside)
    \<comment> \<open>Since inside is open and \<subseteq> convex hull, inside \<subseteq> interior (convex hull)\<close>
    have "open (inside (path_image g))"
      using Jordan_inside_outside assms(1,2) by blast
    hence "inside (path_image g) \<subseteq> interior (convex hull (path_image g))"
      using inside_sub open_subset_interior by blast
    \<comment> \<open>So interior (convex hull) = inside\<close>
    hence "interior (convex hull (path_image g)) = inside (path_image g)"
      using int_inside by blast
    \<comment> \<open>frontier (convex hull) = convex hull - interior (convex hull) = convex hull - inside\<close>
    with assms show ?thesis
      by (metis Diff_cancel  convex_convex_hull convex_interior diff_shunt
          frontier_convex_hull_eq_path_image)
  qed
  show "path_image g \<subseteq> frontier (convex hull path_image g)"
    by (rule assms(3))
qed

section \<open>Part 1: The Wirtinger inequality\<close>

text \<open>The Hölder bound for @{text "p = q = 2"} follows from @{thm Holder_inequality} in the
  AFP @{text Lp} entry.\<close>

lemma real_hoelder_bound_2:
  fixes f :: "real \<Rightarrow> real" and S :: "real set"
  assumes "S \<in> sets lebesgue" "S \<in> lmeasurable"
    "f \<in> borel_measurable lebesgue"
    "integrable lebesgue (\<lambda>x. indicator S x * (f x)\<^sup>2)"
  shows "(LINT x|lebesgue. indicator S x * f x)\<^sup>2 \<le>
    measure lebesgue S * (LINT x|lebesgue. indicator S x * (f x)\<^sup>2)"
proof -
  have ind_if: "\<And>g x. indicator S x * g x = (if x \<in> S then g x else (0::real))"
    by (simp add: indicator_def)
  have to_lebesgue_on: "\<And>g::real\<Rightarrow>real. (LINT x|lebesgue. indicator S x * g x) = integral\<^sup>L (lebesgue_on S) g"
    using assms(1) by (simp add: ind_if Lebesgue_Measure.integral_restrict_UNIV)
  \<comment> \<open>Convert to lebesgue_on S integrals\<close>
  have f_meas_on: "f \<in> borel_measurable (lebesgue_on S)"
    using assms(3) measurable_restrict_space1 by blast
  have f_sq_integ: "integrable (lebesgue_on S) (\<lambda>x. (f x)\<^sup>2)"
  proof -
    have "(\<lambda>x. indicator S x * (f x)\<^sup>2) = (\<lambda>x. if x \<in> S then (f x)\<^sup>2 else 0)"
      by (auto simp: indicator_times_eq_if)
    hence "integrable lebesgue (\<lambda>x. if x \<in> S then (f x)\<^sup>2 else 0)"
      using assms(4) by simp
    then show ?thesis
      by (simp add: Lebesgue_Measure.integrable_restrict_UNIV[OF assms(1), of "\<lambda>x. (f x)\<^sup>2"])
  qed
  have f_sq_int: "f square_integrable S"
    unfolding square_integrable_def using assms(1) f_meas_on f_sq_integ by blast

  \<comment> \<open>(\<lambda>x. 1) is square integrable since S has finite measure\<close>
  have one_sq_int: "(\<lambda>x. 1::real) square_integrable S"
    unfolding square_integrable_def
  proof (intro conjI)
    show "S \<in> sets lebesgue" by (rule assms(1))
    show "(\<lambda>x. 1::real) \<in> borel_measurable (lebesgue_on S)" by simp
    have "finite_measure (lebesgue_on S)"
      by (rule finite_measure_lebesgue_on[OF assms(2)])
    then show "integrable (lebesgue_on S) (\<lambda>x. (1::real)\<^sup>2)"
      by (simp add: finite_measure.integrable_const)
  qed
  \<comment> \<open>Schwartz inequality: |l2product S f 1| \<le> l2norm S f * l2norm S 1\<close>
  have schwartz: "\<bar>l2product S f (\<lambda>x. 1)\<bar> \<le> l2norm S f * l2norm S (\<lambda>x. 1)"
    by (rule Schwartz_inequality_abs[OF f_sq_int one_sq_int])
  \<comment> \<open>Rewrite goal in terms of l2product\<close>
  have If_eq: "LINT x|lebesgue. indicator S x * f x = l2product S f (\<lambda>x. 1)"
    by (simp add: to_lebesgue_on l2product_def)
  have If2_eq: "LINT x|lebesgue. indicator S x * (f x)\<^sup>2 = l2product S f f"
    by (simp add: to_lebesgue_on l2product_def power2_eq_square)
  have norm1_sq: "(l2norm S (\<lambda>x. 1))\<^sup>2 = measure lebesgue S"
  proof -
    have "(l2norm S (\<lambda>x. 1))\<^sup>2 = l2product S (\<lambda>x. 1) (\<lambda>x. 1)"
      by (rule l2norm_pow_2[OF one_sq_int])
    also have "\<dots> = LINT x|lebesgue_on S. 1"
      by (simp add: l2product_def)
    also have "\<dots> = measure (lebesgue_on S) S"
      using finite_measure_lebesgue_on[OF assms(2)]
      by simp
    also have "\<dots> = measure lebesgue S"
      by (metis assms(1) order.refl measure_restrict_space sets.Int_space_eq2)
    finally show ?thesis .
  qed
  have schwartz_sq: "(l2product S f (\<lambda>x. 1))\<^sup>2 \<le> (l2norm S f)\<^sup>2 * (l2norm S (\<lambda>x. 1))\<^sup>2"
  proof -
    have "\<bar>l2product S f (\<lambda>x. 1)\<bar> \<le> l2norm S f * l2norm S (\<lambda>x. 1)"
      by (rule schwartz)
    hence "(l2product S f (\<lambda>x. 1))\<^sup>2 \<le> (l2norm S f * l2norm S (\<lambda>x. 1))\<^sup>2"
      using real_sqrt_abs sqrt_le_D by presburger
    thus ?thesis by (simp add: power_mult_distrib)
  qed
  show ?thesis
    by (simp only: If_eq If2_eq norm1_sq l2norm_pow_2[OF f_sq_int])
      (use schwartz_sq norm1_sq l2norm_pow_2[OF f_sq_int] in \<open>simp add: mult.commute\<close>)
qed

theorem Wirtinger_inequality:
  fixes f f' :: "real \<Rightarrow> real"
  assumes f'hsd: "\<And>x. x \<in> {0..2*pi} \<Longrightarrow> (f' has_integral (f x - f 0)) {0..x}"
    and feq: "f (2*pi) = f 0"
    and f0: "(f has_integral 0) {0..2*pi}"
    and f'2: "(\<lambda>x. (f' x)\<^sup>2) integrable_on {0..2*pi}"
  shows "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
    and "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    and "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2) \<Longrightarrow>
         \<exists>c a. \<forall>x \<in> {0..2*pi}. f x = c * sin (x - a)"
proof -
  have f': \<open>f' integrable_on {0..2*pi}\<close>
    using f'hsd [of \<open>2*pi\<close>] by fastforce

  have f'abs: \<open>f' absolutely_integrable_on {0..2*pi}\<close>
  proof (rule absolutely_integrable_integrable_bound [where g = \<open>\<lambda>x. 1 + (f' x)\<^sup>2\<close>])
    show \<open>norm (f' x) \<le> 1 + (f' x)\<^sup>2\<close> for x
    proof -
      have \<open>0 \<le> (1 - f' x)\<^sup>2\<close> and \<open>0 \<le> (1 + f' x)\<^sup>2\<close>
        by (auto simp: power2_eq_square)
      then show \<open>norm (f' x) \<le> 1 + (f' x)\<^sup>2\<close>
        by (auto simp: power2_eq_square abs_le_iff algebra_simps)
    qed
    show \<open>f' integrable_on {0..2*pi}\<close> by (rule f')
    show \<open>(\<lambda>x. 1 + (f' x)\<^sup>2) integrable_on {0..2*pi}\<close>
      using integrable_add [OF integrable_const_ivl f'2] by simp
  qed

  have contf: \<open>continuous_on {0..2*pi} f\<close>
  proof (rule continuous_on_eq [of _ \<open>\<lambda>x. integral {0..x} f' + f 0\<close>])
    show \<open>continuous_on {0..2*pi} (\<lambda>x. integral {0..x} f' + f 0)\<close>
      by (intro continuous_on_add indefinite_integral_continuous_1 [OF f'] continuous_on_const)
    show \<open>\<And>x. x \<in> {0..2*pi} \<Longrightarrow> integral {0..x} f' + f 0 = f x\<close>
      using f'hsd by (auto simp: has_integral_integrable_integral)
  qed
  show "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
    by (intro integrable_continuous_interval continuous_on_power contf)

  obtain a where "0 \<le> a" "a < pi" "f (a + pi) = f a"
  proof -
    define g where "g \<equiv> \<lambda>x. f (x + pi) - f x"
    have gcont: "continuous_on {0..pi} g"
      unfolding g_def
    proof (intro continuous_on_diff)
      show "continuous_on {0..pi} (\<lambda>x. f (x + pi))"
      proof (rule continuous_on_compose2 [OF contf continuous_on_add [OF continuous_on_id continuous_on_const]])
        show "(\<lambda>x. x + pi) ` {0..pi} \<subseteq> {0..2*pi}"
          using pi_gt_zero by auto
      qed
      show "continuous_on {0..pi} f"
        using continuous_on_subset [OF contf] pi_gt_zero by auto
    qed
    have geq: "g 0 + g pi = 0"
      unfolding g_def using feq by simp
    have "0 \<in> g ` {0..pi}"
    proof -
      have iv: "is_interval (g ` {0..pi})"
        using is_interval_connected_1 connected_continuous_image [OF gcont connected_Icc]
        by blast
      have g0: "g 0 \<in> g ` {0..pi}" and gpi: "g pi \<in> g ` {0..pi}"
        using pi_gt_zero by auto
      consider "g 0 \<le> 0" | "g pi \<le> 0"
        using geq by linarith
      then show ?thesis
        by (metis add_le_same_cancel1 add_le_same_cancel2 g0 geq gpi iv mem_is_interval_1_I)
    qed
    then obtain a where "a \<in> {0..pi}" "g a = 0"
      by auto
    show thesis
    proof (cases "a = pi")
      case True
      then have "g 0 = 0" using geq \<open>g a = 0\<close> by auto
      then show thesis using that [of 0] pi_gt_zero by (auto simp: g_def)
    next
      case False
      then show thesis using that [of a] \<open>a \<in> {0..pi}\<close> \<open>g a = 0\<close>
        by (auto simp: g_def)
    qed
  qed

  define g where "g \<equiv> \<lambda>x. (f x - f a)\<^sup>2 / tan (x - a)"
  define g' where "g' \<equiv> \<lambda>x. (f' x)\<^sup>2 - (f x - f a)\<^sup>2 - (f' x - (f x - f a) / tan (x - a))\<^sup>2"

  text \<open>The integral over completely trouble-free intervals.\<close>
  have trouble_free:
    "(g' has_integral g d - g c) {c..d}"
    if cd: "c \<le> d"
      and sub_cd: "{c..d} \<subseteq> {0..2*pi}"
      and sin_nz: "\<And>x. x \<in> {c..d} \<Longrightarrow> sin (x - a) \<noteq> 0"
    for c d
  proof -
    text \<open>Apply integration by parts with
      \<^item> \<open>\<lambda>x. (f x - f a)²\<close> and its derivative \<open>\<lambda>x. 2 * (f x - f a) * f' x\<close>
      \<^item> \<open>\<lambda>x. inverse (tan (x - a))\<close> and its derivative \<open>\<lambda>x. - inverse (sin (x - a))²\<close>\<close>
    have f'_abs: "(\<lambda>x. 2 * (f x - f a) * f' x) absolutely_integrable_on {c..d}"
    proof -
      have f'_abs_cd: "f' absolutely_integrable_on {c..d}"
        using absolutely_integrable_on_subinterval[OF f'abs sub_cd] .
      have contf_cd: "continuous_on {c..d} f"
        using continuous_on_subset[OF contf sub_cd] .
      have cont_ffa: "continuous_on {c..d} (\<lambda>x. 2 * (f x - f a))"
        by (intro continuous_intros contf_cd)
      have meas: "(\<lambda>x. 2 * (f x - f a)) \<in> borel_measurable (lebesgue_on {c..d})"
        using cont_ffa by (intro continuous_imp_measurable_on_sets_lebesgue) auto
      have bdd: "bounded ((\<lambda>x. 2 * (f x - f a)) ` {c..d})"
        using cont_ffa compact_Icc compact_continuous_image compact_imp_bounded by blast
      show ?thesis
        using absolutely_integrable_bounded_measurable_product_real
          [OF meas _ bdd f'_abs_cd] by auto
    qed
    have g'_abs: "(\<lambda>x. - inverse ((sin (x - a))\<^sup>2)) absolutely_integrable_on {c..d}"
    proof (rule absolutely_integrable_continuous_real)
      show "continuous_on {c..d} (\<lambda>x. - inverse ((sin (x - a))\<^sup>2))"
        by (intro continuous_intros) (use sin_nz in auto)
    qed
    have f'_int: "((\<lambda>t. 2 * (f t - f a) * f' t) has_integral
                   ((f x - f a)\<^sup>2 - (f c - f a)\<^sup>2)) {c..x}"
      if xcd: "x \<in> {c..d}" for x
    proof -
      have cx: "c \<le> x" using xcd cd by auto
      have xd: "x \<le> d" using xcd by auto
      have sub_cx: "{c..x} \<subseteq> {0..2*pi}" using sub_cd xd by auto
          \<comment> \<open>f agrees with f 0 + integral {0..\<sqdot>} f' on {0..2*pi}\<close>
      have f_eq: "f t = f 0 + integral {0..t} f'" if "t \<in> {0..2*pi}" for t
        using f'hsd[OF that] by (auto simp: has_integral_integrable_integral)
          \<comment> \<open>f is absolutely continuous on {0..2*pi}\<close>
      have ac_f: "absolutely_continuous_on {0..2*pi} f"
        using absolute_integral_absolutely_continuous_derivative_eq f'abs f'hsd by blast
        \<comment> \<open>f - f a is absolutely continuous on {c..x}\<close>
      have ac_ffa: "absolutely_continuous_on {c..x} (\<lambda>t. f t - f a)"
        using absolutely_continuous_on_sub
          [OF absolutely_continuous_on_subset[OF ac_f sub_cx]
            absolutely_continuous_on_const] .
          \<comment> \<open>(f t - f a)^2 is absolutely continuous on {c..x}\<close>
      have ac_sq: "absolutely_continuous_on {c..x} (\<lambda>t. (f t - f a)\<^sup>2)"
        unfolding power2_eq_square
        using absolutely_continuous_on_mul[OF ac_ffa ac_ffa]
        by (simp add: scaleR_conv_of_real)
          \<comment> \<open>f has derivative f' a.e. on {0..2*pi}\<close>
      obtain k where negk: "negligible k"
        and derivf: "\<And>t. t \<in> {0..2*pi} - k \<Longrightarrow>
          ((\<lambda>u. integral {0..u} f') has_vector_derivative f' t) (at t within {0..2*pi})"
        using f' has_vector_derivative_indefinite_integral by blast
          \<comment> \<open>Hence (f t - f a)^2 has the right derivative a.e.\<close>
      have deriv_sq: "((\<lambda>t. (f t - f a)\<^sup>2) has_vector_derivative 2 * (f t - f a) * f' t)
          (at t within {c..x})"
        if "t \<in> {c..x} - k" for t
      proof -
        have t02pi: "t \<in> {0..2*pi}" using that sub_cx by auto
        have "t \<in> {0..2*pi} - k" using that sub_cx by auto
        then have hvd_int: "((\<lambda>u. integral {0..u} f') has_vector_derivative f' t)
            (at t within {0..2*pi})"
          using derivf by auto
            \<comment> \<open>Convert to has_vector_derivative of f\<close>
        have "((\<lambda>u. f u - f 0) has_vector_derivative f' t) (at t within {0..2*pi})"
        proof (rule has_vector_derivative_transform_within[OF hvd_int])
          show "0 < (1::real)" by simp
          show "t \<in> {0..2*pi}" using t02pi .
          fix u assume "u \<in> {0..2*pi}" "dist u t < 1"
          then show "integral {0..u} f' = f u - f 0"
            using f_eq f'hsd by blast
        qed
        then have "(f has_vector_derivative f' t) (at t within {0..2*pi})"
          using has_vector_derivative_diff_const by blast
        then have fderiv: "(f has_vector_derivative f' t) (at t within {c..x})"
          by (rule has_vector_derivative_within_subset) (use sub_cx in auto)
        have ffa_deriv: "((\<lambda>t. f t - f a) has_vector_derivative f' t) (at t within {c..x})"
          using has_vector_derivative_diff[OF fderiv has_vector_derivative_const] by simp
        show ?thesis
          unfolding power2_eq_square
          using has_vector_derivative_mult[OF ffa_deriv ffa_deriv]
          by (simp add: algebra_simps scaleR_conv_of_real)
      qed
      show ?thesis
        using fundamental_theorem_of_calculus_absolutely_continuous
          [OF negk cx ac_sq deriv_sq] by simp
    qed
    have g'_int: "((\<lambda>t. - inverse ((sin (t - a))\<^sup>2)) has_integral
                   (inverse (tan (x - a)) - inverse (tan (c - a)))) {c..x}"
      if xcd: "x \<in> {c..d}" for x
    proof -
      have cx: "c \<le> x" using xcd cd by auto
      have sub_cx: "{c..x} \<subseteq> {c..d}" using xcd by auto
          \<comment> \<open>inverse(tan(t-a)) = cos(t-a)/sin(t-a) when sin(t-a) \<noteq> 0\<close>
      have inv_tan_eq: "inverse (tan (t - a)) = cos (t - a) / sin (t - a)"
        if "t \<in> {c..x}" for t
        by (simp add: Multiseries_Expansion.tan_conv_sin_cos)
        \<comment> \<open>cos(t-a)/sin(t-a) has the right derivative\<close>
      have deriv: "((\<lambda>t. cos (t - a) / sin (t - a)) has_vector_derivative
                    - inverse ((sin (t - a))\<^sup>2)) (at t within {c..x})"
        if "t \<in> {c..x}" for t
      proof -
        have sin_nz_t: "sin (t - a) \<noteq> 0" using sin_nz that sub_cx by auto
        have "((\<lambda>t. cos (t - a) / sin (t - a)) has_real_derivative
              (- sin (t - a) * sin (t - a) - cos (t - a) * cos (t - a)) / (sin (t - a) * sin (t - a)))
              (at t within {c..x})"
          by (intro derivative_eq_intros | simp add: sin_nz_t)+
        also have "(- sin (t - a) * sin (t - a) - cos (t - a) * cos (t - a)) / (sin (t - a) * sin (t - a))
                 = - inverse ((sin (t - a))\<^sup>2)"
          by (smt (verit, ccfv_threshold) divide_real_def inverse_eq_divide more_arith_simps(10,7)
              power2_eq_square sin_cos_squared_add)
        finally show ?thesis
          by (simp add: has_real_derivative_iff_has_vector_derivative)
      qed
        \<comment> \<open>Apply FTC\<close>
      have "((\<lambda>t. - inverse ((sin (t - a))\<^sup>2)) has_integral
             (cos (x - a) / sin (x - a) - cos (c - a) / sin (c - a))) {c..x}"
        using fundamental_theorem_of_calculus[OF cx deriv] .
      then show ?thesis
        using inv_tan_eq[of x] inv_tan_eq[of c] cx by simp
    qed
    text \<open>The IBP conclusion gives us \<open>has_integral\<close> for the sum
      \<open>(f x - f a)² * (- inverse (sin (x - a)²)) + 2 * (f x - f a) * f' x * inverse (tan (x - a))\<close>,
      which after algebra equals \<open>g'\<close>, with value \<open>g d - g c\<close>.\<close>
    have ibp_int: "((\<lambda>x. (f x - f a)\<^sup>2 * (- inverse ((sin (x - a))\<^sup>2)) +
      2 * (f x - f a) * f' x * inverse (tan (x - a)))
      has_integral ((f y - f a)\<^sup>2 * inverse (tan (y - a)) -
                    (f c - f a)\<^sup>2 * inverse (tan (c - a)))) {c..y}"
      if "y \<in> {c..d}" for y
    proof (rule absolute_real_integration_by_parts_sum(2))
      show "c \<le> d" using cd .
      show "(\<lambda>x. 2 * (f x - f a) * f' x) absolutely_integrable_on {c..d}"
        using f'_abs .
      show "(\<lambda>x. - inverse ((sin (x - a))\<^sup>2)) absolutely_integrable_on {c..d}"
        using g'_abs .
      show "((\<lambda>t. 2 * (f t - f a) * f' t) has_integral
            ((f x - f a)\<^sup>2 - (f c - f a)\<^sup>2)) {c..x}"
        if "x \<in> {c..d}" for x using f'_int[OF that] .
      show "((\<lambda>t. - inverse ((sin (t - a))\<^sup>2)) has_integral
            (inverse (tan (x - a)) - inverse (tan (c - a)))) {c..x}"
        if "x \<in> {c..d}" for x using g'_int[OF that] .
      show "y \<in> {c..d}" using that .
    qed
      \<comment> \<open>The IBP integrand equals g' pointwise on {c..d}\<close>
    have integrand_eq: "(f x - f a)\<^sup>2 * (- inverse ((sin (x - a))\<^sup>2)) +
      2 * (f x - f a) * f' x * inverse (tan (x - a)) = g' x"
      if "x \<in> {c..d}" for x
    proof -
      have snz: "sin (x - a) \<noteq> 0" using sin_nz[OF that] .
      have snz2: "(sin (x - a))\<^sup>2 \<noteq> 0" using snz by auto
      let ?F = "f x - f a"
      let ?s = "sin (x - a)"
      let ?c = "cos (x - a)"
      have inv_tan: "inverse (tan (x - a)) = ?c / ?s"
        unfolding tan_def using snz by (simp add: field_simps)
      have sc1: "?s\<^sup>2 + ?c\<^sup>2 = 1"
        using sin_cos_squared_add[of "x - a"] by simp
          \<comment> \<open>Multiply both sides by s² and show equality\<close>
      have "((f x - f a)\<^sup>2 * (- inverse ((sin (x - a))\<^sup>2)) +
        2 * (f x - f a) * f' x * inverse (tan (x - a))) * ?s\<^sup>2 =
        - ?F\<^sup>2 + 2 * ?F * f' x * ?c * ?s"
        using snz snz2 unfolding tan_def
        by (simp add: field_simps power2_eq_square)

      moreover have "g' x * ?s\<^sup>2 = - ?F\<^sup>2 + 2 * ?F * f' x * ?c * ?s"
      proof -
        have expand: "g' x = (f' x)\<^sup>2 - ?F\<^sup>2 - (f' x - ?F * ?c / ?s)\<^sup>2"
          unfolding g'_def tan_def using snz by (simp add: field_simps)
        have "g' x * ?s\<^sup>2 =
          ((f' x)\<^sup>2 - ?F\<^sup>2) * ?s\<^sup>2 - (f' x * ?s - ?F * ?c)\<^sup>2"
          unfolding expand using snz
          by (simp add: field_simps power2_eq_square)
        also have "\<dots> = - ?F\<^sup>2 * ?s\<^sup>2 - ?F\<^sup>2 * ?c\<^sup>2 + 2 * ?F * f' x * ?c * ?s"
          by (simp add: power2_eq_square algebra_simps)
        also have "\<dots> = - ?F\<^sup>2 + 2 * ?F * f' x * ?c * ?s"
          using sc1 by algebra 
        finally show ?thesis .
      qed
      ultimately show ?thesis using snz2
        by (metis mult_right_cancel)
    qed
      \<comment> \<open>The IBP value equals g d - g c\<close>
    have value_eq: "(f d - f a)\<^sup>2 * inverse (tan (d - a)) -
      (f c - f a)\<^sup>2 * inverse (tan (c - a)) = g d - g c"
      unfolding g_def divide_inverse by (rule refl)
        \<comment> \<open>Combine using has_integral_eq\<close>
    show ?thesis
      using has_integral_eq ibp_int integrand_eq value_eq
      by (metis (no_types, lifting) atLeastAtMost_iff order.refl that(1))
  qed

  text \<open>Continuity of g.\<close>
  have g_cont: "continuous_on {0..2*pi} g"
    unfolding continuous_on_eq_continuous_within
  proof
    fix c assume c_in: "c \<in> {0..2*pi}"
    show "continuous (at c within {0..2*pi}) g"
    proof (cases "sin (c - a) = 0")
      case False
        \<comment> \<open>When sin(c - a) \<noteq> 0, g is a quotient of continuous functions.\<close>
      have g_eq: "g x = (f x - f a)\<^sup>2 * cos (x - a) / sin (x - a)" for x
        unfolding g_def tan_def by (simp add: field_simps)
      show ?thesis unfolding g_eq
      proof (intro continuous_intros)
        show "continuous (at c within {0..2*pi}) f"
          using contf c_in continuous_on_eq_continuous_within by blast
        show "sin (c - a) \<noteq> 0" by (rule False)
      qed
    next
      case True
        \<comment> \<open>When sin(c - a) = 0, g(c) = 0 and we need to show g(x) \<rightarrow> 0.\<close>
        \<comment> \<open>First establish that f(c) = f(a).\<close>
      have fca: "f c = f a"
      proof -
        from True obtain n :: int where npi: "c - a = of_int n * pi"
          using sin_zero_iff_int2 by auto
        have "n = 0 \<or> n = 1 \<or> n = 2"
        proof -
          from npi have "c = a + of_int n * pi" by simp
          with c_in \<open>0 \<le> a\<close> \<open>a < pi\<close> have "0 \<le> a + of_int n * pi" "a + of_int n * pi \<le> 2 * pi"
            by auto
          hence "of_int n * pi \<ge> -a" "of_int n * pi \<le> 2 * pi - a"
            by linarith+
          hence "of_int n \<ge> -a / pi" "of_int n \<le> (2 * pi - a) / pi"
            using pi_gt_zero by (simp_all add: field_simps)
          moreover have "-a / pi > -1" using \<open>0 \<le> a\<close> \<open>a < pi\<close> pi_gt_zero by (simp add: field_simps)
          moreover have "(2 * pi - a) / pi < 3"
            using \<open>0 \<le> a\<close> \<open>a < pi\<close> pi_gt_zero by (auto simp: divide_simps)
          ultimately have "of_int n > (-1 :: real)" "of_int n < (3 :: real)" by linarith+
          hence "n \<ge> 0" "n \<le> 2" by linarith+
          thus ?thesis by auto
        qed
        thus ?thesis
        proof (elim disjE)
          assume "n = 0" then show "f c = f a" using npi by simp
        next
          assume "n = 1" then show "f c = f a"
            using npi \<open>f (a + pi) = f a\<close> by (simp add: algebra_simps)
        next
          assume "n = 2"
          then have "c = a + 2 * pi" using npi by (simp add: algebra_simps)
          with c_in \<open>0 \<le> a\<close> \<open>a < pi\<close> pi_gt_zero have "a = 0" by auto
          thus "f c = f a" using \<open>c = a + 2 * pi\<close> feq by simp
        qed
      qed
        \<comment> \<open>Now g(c) = 0.\<close>
      have gc0: "g c = 0"
        unfolding g_def using fca by simp
          \<comment> \<open>The continuity reduces to showing g(x) \<rightarrow> 0.\<close>
      show ?thesis unfolding continuous_within gc0
      proof -
        \<comment> \<open>Derive tan(x - a) = tan(x - c) from sin(c - a) = 0.\<close>
        from True obtain n :: int where npi: "c - a = of_int n * pi"
          using sin_zero_iff_int2 by auto
        have tan_eq: "tan (x - a) = tan (x - c)" for x
          by (metis npi diff_add_cancel diff_diff_eq2 tan_periodic_int)
          \<comment> \<open>So g(x) = (f(x) - f(c))² / tan(x - c).\<close>
        have g_eq: "g x = (f x - f c)\<^sup>2 / tan (x - c)" for x
          unfolding g_def tan_eq using fca by simp
            \<comment> \<open>Rewrite as cos/sin form.\<close>
        have g_eq2: "g x = (f x - f c)\<^sup>2 * cos (x - c) / sin (x - c)" for x
          unfolding g_eq tan_def by (simp add: field_simps)
            \<comment> \<open>Show (g \<longlongrightarrow> 0) using the cos/sin form.\<close>
        show "(g \<longlongrightarrow> 0) (at c within {0..2*pi})"
        proof -
          \<comment> \<open>Cauchy-Schwarz bound: (f x - f c)² \<le> |x - c| * \<integral>_c^x (f')².\<close>
          have cs_bound: "(f x - f c)\<^sup>2 \<le> \<bar>x - c\<bar> * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
            if xin: "x \<in> {0..2*pi}" for x
          proof -
            \<comment> \<open>Helper: f' integrable on any subinterval of {0..2\<pi>}\<close>
            have f'_int_sub: "f' integrable_on {a..b}" if "{a..b} \<subseteq> {0..2*pi}" for a b
              using integrable_subinterval_real[OF set_lebesgue_integral_eq_integral(1)[OF f'abs] that] .
                \<comment> \<open>Helper: (f')² integrable on any subinterval of {0..2\<pi>}\<close>
            have f'2_int_sub: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {a..b}" if "{a..b} \<subseteq> {0..2*pi}" for a b
              using integrable_subinterval_real[OF f'2 that] .
                \<comment> \<open>Helper: FTC gives f(b) - f(a) = \<integral>_a^b f' for a,b \<in> {0..2\<pi>}\<close>
            have ftc_sub: "f b - f a = integral {a..b} f'"
              if "a \<in> {0..2*pi}" "b \<in> {0..2*pi}" "a \<le> b" for a b
            proof -
              have "integral {0..a} f' + integral {a..b} f' = integral {0..b} f'"
                by (meson Henstock_Kurzweil_Integration.integral_combine atLeastAtMost_iff f'hsd
                    has_integral_integrable that)
              moreover have "integral {0..a} f' = f a - f 0"
                using f'hsd that by (auto simp: has_integral_integrable_integral)
              moreover have "integral {0..b} f' = f b - f 0"
                using f'hsd that by (auto simp: has_integral_integrable_integral)
              ultimately show ?thesis by linarith
            qed
              \<comment> \<open>Helper: Cauchy-Schwarz (\<integral>_I f')² \<le> (b-a) * \<integral>_I (f')² for I = {a..b} \<subseteq> {0..2\<pi>}\<close>
            have cs_sub: "(integral {a..b} f')\<^sup>2 \<le> (b - a) * integral {a..b} (\<lambda>t. (f' t)\<^sup>2)"
              if sub: "{a..b} \<subseteq> {0..2*pi}" and ab: "a < b" for a b
            proof -
              define \<mu> where "\<mu> \<equiv> integral {a..b} f' / (b - a)"
              have f'I: "f' integrable_on {a..b}" by (rule f'_int_sub[OF sub])
              have f'2I: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {a..b}" by (rule f'2_int_sub[OF sub])
                  \<comment> \<open>(f' - \<mu>)² = (f')² - 2\<mu>f' + \<mu>², each integrable\<close>
              have int1: "(\<lambda>t. - (2 * \<mu>) * f' t) integrable_on {a..b}"
                using integrable_cmul[OF f'I, of "- (2 * \<mu>)"] by (simp add: scaleR_conv_of_real)
              have int2: "(\<lambda>t. \<mu>\<^sup>2) integrable_on {a..b}"
                by (rule integrable_const_ivl)
              have sub_int: "(\<lambda>t. (f' t - \<mu>)\<^sup>2) integrable_on {a..b}"
              proof -
                have "(\<lambda>t. (f' t)\<^sup>2 + (- (2 * \<mu>) * f' t + \<mu>\<^sup>2)) integrable_on {a..b}"
                  by (rule integrable_add[OF f'2I integrable_add[OF int1 int2]])
                moreover have "(f' t - \<mu>)\<^sup>2 = (f' t)\<^sup>2 + (- (2 * \<mu>) * f' t + \<mu>\<^sup>2)" for t
                  by (simp add: power2_eq_square algebra_simps)
                ultimately show ?thesis by (simp add: o_def)
              qed
              have "0 \<le> integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2)"
                by (rule integral_nonneg[OF sub_int]) (simp add: zero_le_power2)
              also have "integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2) =
                integral {a..b} (\<lambda>t. (f' t)\<^sup>2) + (- (2 * \<mu>) * integral {a..b} f' + \<mu>\<^sup>2 * (b - a))"
              proof -
                have "integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2) =
                  integral {a..b} (\<lambda>t. (f' t)\<^sup>2 + (- (2 * \<mu>) * f' t + \<mu>\<^sup>2))"
                  by (rule integral_cong) (simp add: power2_eq_square algebra_simps)
                also have "\<dots> = integral {a..b} (\<lambda>t. (f' t)\<^sup>2) +
                  integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t + \<mu>\<^sup>2)"
                  by (rule integral_add[OF f'2I integrable_add[OF int1 int2]])
                also have "integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t + \<mu>\<^sup>2) =
                  integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t) + integral {a..b} (\<lambda>t. \<mu>\<^sup>2)"
                  by (rule integral_add[OF int1 int2])
                also have "integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t) = - (2 * \<mu>) * integral {a..b} f'"
                  by simp
                also have "integral {a..b} (\<lambda>t. \<mu>\<^sup>2) = \<mu>\<^sup>2 * (b - a)"
                  using ab by simp
                finally show ?thesis by linarith
              qed
              also have "- (2 * \<mu>) * integral {a..b} f' + \<mu>\<^sup>2 * (b - a) =
                - (integral {a..b} f')\<^sup>2 / (b - a)"
              proof -
                have D: "b - a > 0" using ab by simp
                define I where "I \<equiv> integral {a..b} f'"
                have "- (2 * \<mu>) * I + \<mu>\<^sup>2 * (b - a) = - 2 * (I / (b - a)) * I + (I / (b - a))\<^sup>2 * (b - a)"
                  unfolding \<mu>_def I_def by simp
                also have "\<dots> = - 2 * I\<^sup>2 / (b - a) + I\<^sup>2 / (b - a)"
                  using D by (simp add: power2_eq_square divide_simps)
                also have "\<dots> = - I\<^sup>2 / (b - a)" by algebra
                finally show ?thesis unfolding I_def .
              qed
              finally have "(integral {a..b} f')\<^sup>2 / (b - a) \<le> integral {a..b} (\<lambda>t. (f' t)\<^sup>2)"
                by linarith
              thus ?thesis using ab by (simp add: pos_divide_le_eq mult.commute)
            qed
              \<comment> \<open>Main proof by cases\<close>
            show ?thesis
            proof (cases "c \<le> x")
              case True
              show ?thesis
              proof (cases "x = c")
                case True then show ?thesis by simp
              next
                case False
                with \<open>c \<le> x\<close> have cx: "c < x" by linarith
                have sub: "{c..x} \<subseteq> {0..2*pi}" using c_in xin \<open>c \<le> x\<close> by auto
                have "f x - f c = integral {c..x} f'"
                  by (rule ftc_sub) (use c_in xin \<open>c \<le> x\<close> in auto)
                hence "(f x - f c)\<^sup>2 = (integral {c..x} f')\<^sup>2" by simp
                also have "\<dots> \<le> (x - c) * integral {c..x} (\<lambda>t. (f' t)\<^sup>2)"
                  by (rule cs_sub[OF sub cx])
                also have "\<dots> = \<bar>x - c\<bar> * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
                  using \<open>c \<le> x\<close> by (simp add: min_absorb1 max_absorb2)
                finally show ?thesis .
              qed
            next
              case False
              hence xc: "x < c" by linarith
              have sub: "{x..c} \<subseteq> {0..2*pi}" using c_in xin xc by auto
              have "f c - f x = integral {x..c} f'"
                by (rule ftc_sub) (use c_in xin xc in auto)
              hence "(f x - f c)\<^sup>2 = (integral {x..c} f')\<^sup>2"
                by (simp add: power2_eq_square algebra_simps)
              also have "\<dots> \<le> (c - x) * integral {x..c} (\<lambda>t. (f' t)\<^sup>2)"
                by (rule cs_sub[OF sub xc])
              also have "\<dots> = \<bar>x - c\<bar> * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
                using xc by (simp add: min_absorb2 max_absorb1)
              finally show ?thesis .
            qed
          qed

          \<comment> \<open>The integral of f'² over a shrinking interval tends to 0.\<close>
          have f'2_int_tends_0:
            "((\<lambda>x. integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)) \<longlongrightarrow> 0) (at c within {0..2*pi})"
          proof -
            define F where "F \<equiv> \<lambda>x. integral {0..x} (\<lambda>t. (f' t)\<^sup>2)"
            have F_cont: "continuous_on {0..2*pi} F"
              unfolding F_def by (rule indefinite_integral_continuous_1[OF f'2])
            have F_eq: "integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2) = \<bar>F x - F c\<bar>"
              if "x \<in> {0..2*pi}" for x
            proof (cases "c \<le> x")
              case True
              have sub: "{c..x} \<subseteq> {0..2*pi}" using c_in that True by auto
              have "integral {0..c} (\<lambda>t. (f' t)\<^sup>2) + integral {c..x} (\<lambda>t. (f' t)\<^sup>2) =
                integral {0..x} (\<lambda>t. (f' t)\<^sup>2)"
                by (metis Henstock_Kurzweil_Integration.integral_combine True atLeastatMost_subset_iff f'2
                    integrable_on_subinterval le_numeral_extra(3) sub)
              hence "integral {c..x} (\<lambda>t. (f' t)\<^sup>2) = F x - F c"
                unfolding F_def by linarith
              moreover have "0 \<le> integral {c..x} (\<lambda>t. (f' t)\<^sup>2)"
                by (rule integral_nonneg[OF integrable_subinterval_real[OF f'2 sub]])
                  (simp add: zero_le_power2)
              ultimately show ?thesis using True by (simp add: min_def max_def)
            next
              case False
              hence xc: "x \<le> c" by simp
              have sub: "{x..c} \<subseteq> {0..2*pi}" using c_in that xc by auto
              have "integral {0..x} (\<lambda>t. (f' t)\<^sup>2) + integral {x..c} (\<lambda>t. (f' t)\<^sup>2) =
                integral {0..c} (\<lambda>t. (f' t)\<^sup>2)"
                by (metis Henstock_Kurzweil_Integration.integral_combine atLeastAtMost_iff
                    atLeastatMost_subset_iff c_in f'2 integrable_on_subinterval le_numeral_extra(3) that
                    xc)
              hence "integral {x..c} (\<lambda>t. (f' t)\<^sup>2) = F c - F x"
                unfolding F_def by linarith
              moreover have "0 \<le> integral {x..c} (\<lambda>t. (f' t)\<^sup>2)"
                by (rule integral_nonneg[OF integrable_subinterval_real[OF f'2 sub]])
                  (simp add: zero_le_power2)
              ultimately show ?thesis using xc by (simp add: min_def max_def)
            qed
            have "((\<lambda>x. \<bar>F x - F c\<bar>) \<longlongrightarrow> 0) (at c within {0..2*pi})"
              by (metis F_cont LIM_zero_iff c_in continuous_on_def tendsto_rabs_zero)
            thus ?thesis
              by (smt (verit, best) F_eq Lim_cong_within)
          qed
          
          \<comment> \<open>Combine: g(x) = (f(x)-f(c))² * cos(x-c) / sin(x-c) \<rightarrow> 0.\<close>
          \<comment> \<open>Show (x-c)/sin(x-c) \<rightarrow> 1 as x \<rightarrow> c, hence bounded near c.\<close>
          have sinc_ratio_bounded:
            "\<forall>\<^sub>F x in at c within {0..2*pi}. \<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> \<le> 2"
          proof -
            \<comment> \<open>sin(x)/x \<rightarrow> 1 at 0, so (x-c)/sin(x-c) \<rightarrow> 1 at c.\<close>
            have inv_lim: "(\<lambda>x. (x - c) / sin (x - c)) \<midarrow>c\<rightarrow> 1"
              by real_asymp
                \<comment> \<open>Extract: eventually |ratio| < 2.\<close>
            from tendstoD[OF inv_lim, of 1]
            have "\<forall>\<^sub>F x in at c. dist ((x - c) / sin (x - c)) 1 < 1"
              by simp
            hence "\<forall>\<^sub>F x in at c. \<bar>(x - c) / sin (x - c)\<bar> < 2"
              by (elim eventually_mono) (auto simp: dist_real_def abs_if split: if_splits)
            hence "\<forall>\<^sub>F x in at c. \<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> < 2"
              by (elim eventually_mono) (simp add: abs_divide)
            thus ?thesis
              by (metis (no_types, lifting) UNIV_I eventually_at_topological less_imp_le)
          qed

          \<comment> \<open>Now combine everything.\<close>
          show ?thesis
          proof (rule Lim_null_comparison[where g = "\<lambda>x. 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"])
            \<comment> \<open>g(x) is eventually bounded by 2 * \<integral>(f')².\<close>
            show "\<forall>\<^sub>F x in at c within {0..2*pi}. norm (g x) \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
            proof -
              have mem: "\<forall>\<^sub>F x in at c within {0..2*pi}. x \<in> {0..2*pi}"
                unfolding at_within_def eventually_inf_principal by simp
              show ?thesis
              proof (rule eventually_mono[OF eventually_conj[OF sinc_ratio_bounded mem]])
                fix x assume H: "\<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> \<le> 2 \<and> x \<in> {0..2*pi}"
                hence ratio_bd: "\<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> \<le> 2" and xin: "x \<in> {0..2*pi}" by auto
                have "\<bar>g x\<bar> = \<bar>(f x - f c)\<^sup>2 * cos (x - c) / sin (x - c)\<bar>"
                  using g_eq2 by simp
                also have "\<dots> = (f x - f c)\<^sup>2 * \<bar>cos (x - c)\<bar> / \<bar>sin (x - c)\<bar>"
                  by (simp add: abs_mult abs_divide)
                also have "\<dots> \<le> (f x - f c)\<^sup>2 * 1 / \<bar>sin (x - c)\<bar>"
                  by (meson abs_cos_le_one abs_ge_zero divide_right_mono
                      ordered_comm_semiring_class.comm_mult_left_mono zero_le_power2)
                also have "\<dots> = (f x - f c)\<^sup>2 / \<bar>sin (x - c)\<bar>" by simp
                also have "\<dots> \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
                proof -
                  have sub: "{min c x..max c x} \<subseteq> {0..2*pi}" using c_in xin by auto
                  have f'2I: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {min c x..max c x}"
                    by (rule integrable_subinterval_real[OF f'2 sub])
                  show ?thesis
                  proof (cases "sin (x - c) = 0")
                    case True
                    then show ?thesis
                      using integral_nonneg[OF f'2I] by simp
                  next
                    case False
                    hence sinpos: "\<bar>sin (x - c)\<bar> > 0" by simp
                    define I where "I = integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
                    have Ige: "I \<ge> 0"
                      unfolding I_def by (rule integral_nonneg[OF f'2I]) (simp add: zero_le_power2)
                    have "(f x - f c)\<^sup>2 \<le> \<bar>x - c\<bar> * I"
                      unfolding I_def by (rule cs_bound[OF xin])
                    hence "(f x - f c)\<^sup>2 / \<bar>sin (x - c)\<bar> \<le> \<bar>x - c\<bar> * I / \<bar>sin (x - c)\<bar>"
                      by (intro divide_right_mono) simp_all
                    also have "\<dots> = (\<bar>x - c\<bar> / \<bar>sin (x - c)\<bar>) * I"
                      by (simp add: field_simps)
                    also have "\<dots> \<le> 2 * I"
                      by (rule mult_right_mono[OF ratio_bd Ige])
                    finally show ?thesis unfolding I_def .
                  qed
                qed
                finally show "norm (g x) \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)" by simp
              qed
            qed
              \<comment> \<open>2 * \<integral>(f')² \<rightarrow> 0.\<close>
            show "((\<lambda>x. 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)) \<longlongrightarrow> 0) (at c within {0..2*pi})"
              using tendsto_mult_right_zero[OF f'2_int_tends_0] by simp
          qed
        qed
      qed
    qed
  qed


  text \<open>The integral over mainly trouble-free intervals:
    we only need \<open>sin(x - a) \<noteq> 0\<close> on the open interior, allowing zeros at the endpoints.\<close>
  have mainly_trouble_free:
    "(g' has_integral g d - g c) {c..d}"
    if "c \<le> d" and "{c..d} \<subseteq> {0..2*pi}"
      and "\<And>x. x \<in> {c<..<d} \<Longrightarrow> sin (x - a) \<noteq> 0"
    for c d
  proof -
    have "g' absolutely_integrable_on {c..d}"
    proof -
      have f'2_abs: "(\<lambda>x. (f' x)\<^sup>2) absolutely_integrable_on {0..2*pi}"
        by (rule abs_absolutely_integrableI_1[OF f'2]) (simp add: integrable_eq[OF f'2])
      have ffa_abs: "(\<lambda>x. (f x - f a)\<^sup>2) absolutely_integrable_on {0..2*pi}"
        by (rule absolutely_integrable_continuous_real)
          (intro continuous_intros contf)
      note cd_le = \<open>c \<le> d\<close> and cd_sub = \<open>{c..d} \<subseteq> {0..2*pi}\<close>
        and sin_nz = \<open>\<And>x. x \<in> {c<..<d} \<Longrightarrow> sin (x - a) \<noteq> 0\<close>
      have g'_int_sub: "g' integrable_on {u..v}" if uv_sub: "{u..v} \<subseteq> {c<..<d}" for u v
      proof (cases "u \<le> v")
        case False
        then show ?thesis by (simp add: not_le integrable_on_empty)
      next
        case True
        then have uv_mem: "u \<in> {c<..<d}" "v \<in> {c<..<d}"
          using uv_sub by auto
        have uv_cd: "{u..v} \<subseteq> {c..d}"
          using uv_sub greaterThanLessThan_subseteq_atLeastAtMost_iff by blast
        then have uv_2pi: "{u..v} \<subseteq> {0..2*pi}" using cd_sub by auto
        have sin_nz': "sin (x - a) \<noteq> 0" if "x \<in> {u..v}" for x
        proof -
          have "x \<in> {c<..<d}" using that uv_sub by blast
          then show ?thesis using sin_nz by auto
        qed
        show ?thesis
          using has_integral_integrable[OF trouble_free[OF True uv_2pi sin_nz']] by auto
      qed
      have g'_int: "g' integrable_on {c'..d'}" if "{c'..d'} \<subseteq> {c<..<d}" for c' d'
        using \<open>{c'..d'} \<subseteq> {c<..<d}\<close> g'_int_sub by blast
      have abs_g_cont: \<open>continuous_on {0..2 * pi} (\<lambda>x. \<bar>g x\<bar>)\<close>
        by (intro continuous_intros g_cont)
      obtain h where h_abs: "h absolutely_integrable_on {c..d}" 
                 and h_bounded: "(\<forall>x\<in>{c..d}. g' x \<le> h x) \<or> (\<forall>x\<in>{c..d}. h x \<le> g' x)"
      proof -
        have abs: \<open>(\<lambda>x. (f' x)\<^sup>2) absolutely_integrable_on {c..d}\<close>
          using absolutely_integrable_on_subinterval[OF f'2_abs cd_sub] .
        have bnd: \<open>\<forall>x\<in>{c..d}. g' x \<le> (f' x)\<^sup>2\<close>
        proof (intro ballI)
          fix x assume \<open>x \<in> {c..d}\<close>
          show \<open>g' x \<le> (f' x)\<^sup>2\<close>
            unfolding g'_def by simp
        qed
        show ?thesis
          using abs bnd by (intro that[of \<open>\<lambda>x. (f' x)\<^sup>2\<close>]) auto
      qed
      show ?thesis
      proof (intro g'_int absolutely_integrable_improper [of c d , unfolded box_real])
        obtain w where "w\<in>{0..2 * pi}" "\<forall>y\<in>{0..2 * pi}. \<bar>g y\<bar> \<le> \<bar>g w\<bar>"
          using continuous_attains_sup [of \<open>{0..2*pi}\<close> \<open>\<lambda>x. \<bar>g x\<bar>\<close>]
          by (metis add_increasing atLeastatMost_empty_iff compact_Icc abs_g_cont mult_2
              pi_ge_zero)        
        show "bounded {integral {c'..d'} g' |c' d'. {c'..d'} \<subseteq> {c<..<d}}"
        proof (rule boundedI[where B = "2 * \<bar>g w\<bar>"])
          fix x assume "x \<in> {integral {c'..d'} g' |c' d'. {c'..d'} \<subseteq> {c<..<d}}"
          then obtain c' d' where cd': "{c'..d'} \<subseteq> {c<..<d}" and xeq: "x = integral {c'..d'} g'"
            by auto
          show "norm x \<le> 2 * \<bar>g w\<bar>"
          proof (cases "c' \<le> d'")
            case False
            then have "{c'..d'} = {}" by auto
            then show ?thesis by (simp add: xeq)
          next
            case True
            then have mem: "c' \<in> {c<..<d}" "d' \<in> {c<..<d}" using cd' by auto
            have sub_2pi: "{c'..d'} \<subseteq> {0..2*pi}"
              using cd' cd_sub greaterThanLessThan_subseteq_atLeastAtMost_iff by blast
            have sin_nz': "sin (t - a) \<noteq> 0" if "t \<in> {c'..d'}" for t
              using that cd' sin_nz by (meson greaterThanLessThan_subseteq_atLeastAtMost_iff subsetD)
            have hi: "(g' has_integral g d' - g c') {c'..d'}"
              using trouble_free[OF True sub_2pi sin_nz'] .
            then have "integral {c'..d'} g' = g d' - g c'"
              using has_integral_integrable_integral g'_int_sub[OF cd'] by auto
            then have "\<bar>x\<bar> = \<bar>g d' - g c'\<bar>" by (simp add: xeq)
            also have "\<dots> \<le> \<bar>g d'\<bar> + \<bar>g c'\<bar>" by linarith
            also have "\<dots> \<le> \<bar>g w\<bar> + \<bar>g w\<bar>"
            proof -
              have "c' \<in> {0..2*pi}" "d' \<in> {0..2*pi}"
                using mem cd_sub greaterThanLessThan_subseteq_atLeastAtMost_iff by blast+
              then show ?thesis
                using \<open>\<forall>y\<in>{0..2 * pi}. \<bar>g y\<bar> \<le> \<bar>g w\<bar>\<close> by (meson add_mono)
            qed
            also have "\<dots> = 2 * \<bar>g w\<bar>" by algebra
            finally show ?thesis by (simp add: xeq)
          qed
        qed
      qed (use h_abs h_bounded in auto)
    qed
    show ?thesis
    proof -
      note cd_le = \<open>c \<le> d\<close> and cd_sub = \<open>{c..d} \<subseteq> {0..2*pi}\<close>
        and sin_nz = \<open>\<And>x. x \<in> {c<..<d} \<Longrightarrow> sin (x - a) \<noteq> 0\<close>
      have g'_int: "g' integrable_on {c..d}"
        using \<open>g' absolutely_integrable_on {c..d}\<close> set_lebesgue_integral_eq_integral by blast
      have g_cont_cd: "continuous_on {c..d} g"
        using continuous_on_subset[OF g_cont cd_sub] .
      have goal: "integral {c..d} g' = g d - g c"
      proof (cases "c < d")
        case False
        then have "c = d" using cd_le by linarith
        then show ?thesis by simp
      next
        case True
        \<comment> \<open>Pick sequences c_n \<rightarrow> c and d_n \<rightarrow> d from inside (c,d)\<close>
        define c_n where "c_n \<equiv> \<lambda>n. c + (d - c) / (real n + 2)"
        define d_n where "d_n \<equiv> \<lambda>n. d - (d - c) / (real n + 2)"
        have pos: "0 < (d - c) / (real n + 2)" for n
          using True by auto
        have lt_dc: "(d - c) / (real n + 2) < d - c" for n
        proof -
          have "real n + 2 > 1" by auto
          then show ?thesis using True by (simp add: divide_less_eq)
        qed
        have c_n_in: "c_n n \<in> {c<..<d}" for n
          using pos[of n] lt_dc[of n] unfolding c_n_def by auto
        have d_n_in: "d_n n \<in> {c<..<d}" for n
          using pos[of n] lt_dc[of n] unfolding d_n_def by auto
        have c_n_le_d_n: "c_n n \<le> d_n n" for n
        proof -
          have "0 \<le> real n" by simp
          then have "c * real n \<le> d * real n"
            using True by (intro mult_right_mono) linarith+
          then have "2 * ((d - c) / (real n + 2)) \<le> d - c"
            using True by (simp add: field_simps)
          then show ?thesis unfolding c_n_def d_n_def by linarith
        qed
        have frac_lim: "(\<lambda>n. (d - c) / (real n + 2)) \<longlonglongrightarrow> 0"
        proof (rule real_tendsto_sandwich)
          show "\<forall>\<^sub>F n in sequentially. 0 \<le> (d - c) / (real n + 2)"
            using True by (intro always_eventually allI) (auto simp: field_simps)
          show "\<forall>\<^sub>F n in sequentially. (d - c) / (real n + 2) \<le> (d - c) * (1 / real n)"
            using True by (intro eventually_sequentiallyI[of 1]) (auto simp: field_simps)
          show "(\<lambda>_. (0::real)) \<longlonglongrightarrow> 0" by simp
          show "(\<lambda>n. (d - c) * (1 / real n)) \<longlonglongrightarrow> 0"
            using tendsto_mult_right_zero[OF lim_inverse_n'] by simp
        qed
        have c_n_lim: "c_n \<longlonglongrightarrow> c"
          unfolding c_n_def using tendsto_add[OF tendsto_const frac_lim] by simp
        have d_n_lim: "d_n \<longlonglongrightarrow> d"
          unfolding d_n_def using tendsto_diff[OF tendsto_const frac_lim] by simp
        \<comment> \<open>On each [c_n, d_n], trouble_free applies\<close>
        have sub_n: "{c_n n..d_n n} \<subseteq> {c<..<d}" for n
          using c_n_in[of n] d_n_in[of n] c_n_le_d_n[of n] by auto
        have sub_2pi_n: "{c_n n..d_n n} \<subseteq> {0..2*pi}" for n
          using sub_n[of n] cd_sub greaterThanLessThan_subseteq_atLeastAtMost_iff by blast
        have sin_nz_n: "sin (x - a) \<noteq> 0" if "x \<in> {c_n n..d_n n}" for n x
          using that sub_n[of n] sin_nz
          by (meson greaterThanLessThan_subseteq_atLeastAtMost_iff subsetD)
        have tf_n: "(g' has_integral g (d_n n) - g (c_n n)) {c_n n..d_n n}" for n
          using trouble_free[OF c_n_le_d_n sub_2pi_n sin_nz_n] .
        have int_n: "integral {c_n n..d_n n} g' = g (d_n n) - g (c_n n)" for n
          using tf_n[of n] by (rule integral_unique)
        \<comment> \<open>The integrals converge to integral {c..d} g'\<close>
        have int_lim: "(\<lambda>n. integral {c_n n..d_n n} g') \<longlonglongrightarrow> integral {c..d} g'"
        proof -
          have indef_cont: "continuous_on {c..d} (\<lambda>x. integral {c..x} g')"
            by (rule indefinite_integral_continuous_1[OF g'_int])
          have c_n_cd: "c_n n \<in> {c..d}" for n
            using c_n_in[of n] by (meson atLeastAtMost_iff greaterThanLessThan_iff less_imp_le)
          have d_n_cd: "d_n n \<in> {c..d}" for n
            using d_n_in[of n] by (meson atLeastAtMost_iff greaterThanLessThan_iff less_imp_le)
          have split: "integral {c_n n..d_n n} g' = integral {c..d_n n} g' - integral {c..c_n n} g'" for n
          proof -
            have cn_le: "c \<le> c_n n" using c_n_in[of n] by auto
            have int_cdn: "g' integrable_on {c..d_n n}"
              by (rule integrable_subinterval_real[OF g'_int])
                 (use d_n_cd[of n] cd_le in auto)
            have "integral {c..c_n n} g' + integral {c_n n..d_n n} g' = integral {c..d_n n} g'"
              by (rule Henstock_Kurzweil_Integration.integral_combine[OF cn_le c_n_le_d_n int_cdn])
            then show ?thesis by linarith
          qed
          have "(\<lambda>n. integral {c..d_n n} g') \<longlonglongrightarrow> integral {c..d} g'"
            by (rule continuous_on_tendsto_compose[OF indef_cont d_n_lim])
               (use d_n_cd cd_le in \<open>auto intro: always_eventually\<close>)
          moreover have "(\<lambda>n. integral {c..c_n n} g') \<longlonglongrightarrow> integral {c..c} g'"
            by (rule continuous_on_tendsto_compose[OF indef_cont c_n_lim])
               (use c_n_cd cd_le in \<open>auto intro: always_eventually\<close>)
          moreover have "integral {c..c} g' = 0" by simp
          ultimately have "(\<lambda>n. integral {c..d_n n} g' - integral {c..c_n n} g') \<longlonglongrightarrow> integral {c..d} g' - 0"
            by (intro tendsto_diff) simp_all
          then show ?thesis using split by simp
        qed
        \<comment> \<open>The RHS converges to g d - g c by continuity\<close>
        moreover have "(\<lambda>n. g (d_n n) - g (c_n n)) \<longlonglongrightarrow> g d - g c"
        proof (intro tendsto_diff)
          have d_n_cd: "d_n n \<in> {c..d}" for n
            using d_n_in[of n] by (meson atLeastAtMost_iff greaterThanLessThan_iff less_imp_le)
          have c_n_cd: "c_n n \<in> {c..d}" for n
            using c_n_in[of n] by (meson atLeastAtMost_iff greaterThanLessThan_iff less_imp_le)
          show "(\<lambda>n. g (d_n n)) \<longlonglongrightarrow> g d"
            by (rule continuous_on_tendsto_compose[OF g_cont_cd d_n_lim])
               (use d_n_cd cd_le in \<open>auto intro: always_eventually\<close>)
          show "(\<lambda>n. g (c_n n)) \<longlonglongrightarrow> g c"
            by (rule continuous_on_tendsto_compose[OF g_cont_cd c_n_lim])
               (use c_n_cd cd_le in \<open>auto intro: always_eventually\<close>)
        qed
        ultimately show ?thesis
          using int_n LIMSEQ_unique by auto
      qed
      show ?thesis
        using integrable_integral[OF g'_int] goal by auto
    qed
  qed
  show "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
  proof -
    \<comment> \<open>Zeros of sin(x - a) in [0, 2\<pi>] are exactly at x = a and x = a + \<pi>.\<close>
    have sin_nz_1: "sin (x - a) \<noteq> 0" if "a + pi < x" "x < 2*pi" for x
      by (smt (verit) \<open>0 \<le> a\<close> sin_lt_zero that)
    have sin_nz_2: "sin (x - a) \<noteq> 0" if "a < x" "x < a + pi" for x
      by (smt (verit, ccfv_threshold) sin_gt_zero that)
    have sin_nz_3: "sin (x - a) \<noteq> 0" if "0 < x" "x < a" for x
    proof -
      have "0 < a - x" "a - x < pi" using that \<open>a < pi\<close> by auto
      hence "0 < sin (a - x)" by (rule sin_gt_zero)
      moreover have "sin (x - a) = - sin (a - x)"
        by (metis sin_minus minus_diff_eq)
      ultimately show ?thesis by simp
    qed
    \<comment> \<open>Apply mainly_trouble_free on three intervals.\<close>
    have int1: "(g' has_integral g (2*pi) - g (a + pi)) {a + pi..2*pi}"
      by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_1 in auto)
    have int2: "(g' has_integral g (a + pi) - g a) {a..a + pi}"
      by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_2 in auto)
    have int3: "(g' has_integral g a - g 0) {0..a}"
      by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_3 in auto)
    \<comment> \<open>Combine the three integrals using has_integral_combine.\<close>
    have api_le: "a \<le> a + pi" and api_le2: "a + pi \<le> 2*pi"
      using \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
    have a_le_2pi: "a \<le> 2*pi" using \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
    have int12: "(g' has_integral (g (a + pi) - g a) + (g (2*pi) - g (a + pi))) {a..2*pi}"
      by (rule has_integral_combine[OF api_le api_le2 int2 int1])
    have int_all: "(g' has_integral (g a - g 0) + ((g (a + pi) - g a) + (g (2*pi) - g (a + pi)))) {0..2*pi}"
      by (rule has_integral_combine[OF \<open>0 \<le> a\<close> a_le_2pi int3 int12])
    \<comment> \<open>Simplify: the telescoping sum gives g(2\<pi>) - g(0).\<close>
    have int_all': "(g' has_integral g (2*pi) - g 0) {0..2*pi}"
      using int_all by (simp add: algebra_simps)
    \<comment> \<open>Show g(2\<pi>) = g(0), so the integral of g' is 0.\<close>
    have "g (2*pi) = g 0"
      unfolding g_def using feq by (simp add: tan_def)
    hence g'_zero: "(g' has_integral 0) {0..2*pi}"
      using int_all' by simp
    \<comment> \<open>Extract the inequality from \<integral>g' = 0.\<close>
    \<comment> \<open>g'(x) = (f'(x))² − (f(x)−f(a))² − rest(x)², so (f'(x))² − g'(x) = (f(x)−f(a))² + rest(x)² \<ge> (f(x)−f(a))².\<close>
    have ffa_int: "(\<lambda>x. (f x - f a)\<^sup>2) integrable_on {0..2*pi}"
      by (intro integrable_continuous_interval continuous_intros contf)
    have g'_int: "g' integrable_on {0..2*pi}"
      using g'_zero by (auto simp: has_integral_integrable_integral)
    \<comment> \<open>(f')² − g' is integrable and its integral = \<integral>(f')² − 0 = \<integral>(f')².\<close>
    have diff_int: "((\<lambda>x. (f' x)\<^sup>2 - g' x) has_integral integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2) - 0) {0..2*pi}"
      by (rule has_integral_diff[OF integrable_integral[OF f'2] g'_zero])
    \<comment> \<open>(f')²(x) − g'(x) = (f(x)−f(a))² + rest(x)² \<ge> (f(x)−f(a))².\<close>
    have diff_eq: "(f' x)\<^sup>2 - g' x = (f x - f a)\<^sup>2 + (f' x - (f x - f a) / tan (x - a))\<^sup>2" for x
      unfolding g'_def by (simp add: algebra_simps)
    have diff_ge: "(f' x)\<^sup>2 - g' x \<ge> (f x - f a)\<^sup>2" for x
      unfolding diff_eq by (simp add: zero_le_power2)
    \<comment> \<open>Therefore \<integral>(f')² \<ge> \<integral>(f(x)−f(a))².\<close>
    have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2 - g' x)"
      by (rule integral_le[OF ffa_int]) (use diff_int has_integral_integrable_integral in \<open>auto intro: diff_ge\<close>)
    also have "\<dots> = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
      using diff_int has_integral_integrable_integral by auto
    finally have ineq_ffa: "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)" .
    \<comment> \<open>Show \<integral>(f(x))² \<le> \<integral>(f(x)−f(a))² using \<integral>f = 0.\<close>
    have "(f x)\<^sup>2 \<le> (f x - f a)\<^sup>2 + 2 * f a * f x - (f a)\<^sup>2" for x
      by (simp add: power2_eq_square algebra_simps)
    \<comment> \<open>Actually: (f(x)−f(a))² = (f(x))² − 2\<sqdot>f(a)\<sqdot>f(x) + (f(a))², so (f(x))² = (f(x)−f(a))² + 2\<sqdot>f(a)\<sqdot>f(x) − (f(a))².\<close>
    have fx_eq: "(f x)\<^sup>2 = (f x - f a)\<^sup>2 + 2 * f a * f x - (f a)\<^sup>2" for x
      by (simp add: power2_eq_square algebra_simps)
    have f_int: "f integrable_on {0..2*pi}"
      by (rule integrable_continuous_interval[OF contf])
    \<comment> \<open>\<integral>f = 0 by assumption.\<close>
    have f_integral_0: "integral {0..2*pi} f = 0"
      using f0 by (auto simp: has_integral_integrable_integral)
    \<comment> \<open>\<integral>(f(x)−f(a))² = \<integral>(f(x))² + (f(a))²\<sqdot>2\<pi>  (using \<integral>f = 0).\<close>
    have ffa_2fa_int: "(\<lambda>x. 2 * f a * f x) integrable_on {0..2*pi}"
    proof -
      have "(\<lambda>x. (2 * f a) *\<^sub>R f x) integrable_on {0..2*pi}"
        by (rule integrable_cmul[OF f_int])
      thus ?thesis by simp
    qed
    have ffa_expand: "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) =
      integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) - 2 * f a * integral {0..2*pi} f +
      (f a)\<^sup>2 * (2*pi)"
    proof -
      have eq: "(f x - f a)\<^sup>2 = (f x)\<^sup>2 - 2 * f a * f x + (f a)\<^sup>2" for x
        by (simp add: power2_eq_square algebra_simps)
      have fx2_int: "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
        by (intro integrable_continuous_interval continuous_intros contf)
      have const_int: "(\<lambda>x::real. (f a)\<^sup>2) integrable_on {0..2*pi}"
        by blast
      \<comment> \<open>Split: (f−fa)² = f² − 2\<sqdot>fa\<sqdot>f + fa²\<close>
      have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x + (f a)\<^sup>2)"
        by (rule integral_cong) (simp add: eq)
      also have "\<dots> = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x) + integral {0..2*pi} (\<lambda>x. (f a)\<^sup>2)"
        by (rule Henstock_Kurzweil_Integration.integral_add)
          (auto intro: integrable_diff fx2_int ffa_2fa_int)
      also have "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x) =
        integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) - integral {0..2*pi} (\<lambda>x. 2 * f a * f x)"
        by (rule Henstock_Kurzweil_Integration.integral_diff[OF fx2_int ffa_2fa_int])
      also have "integral {0..2*pi} (\<lambda>x. 2 * f a * f x) = 2 * f a * integral {0..2*pi} f"
        using integral_cmul by simp
      also have "integral {0..2*pi} (\<lambda>x. (f a)\<^sup>2) = (f a)\<^sup>2 * (2*pi)"
        by simp
      finally show ?thesis by linarith
    qed
    have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) =
      integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) + (f a)\<^sup>2 * (2*pi)"
      using ffa_expand f_integral_0 by simp
    hence "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) =
      integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) - (f a)\<^sup>2 * (2*pi)"
      by linarith
    moreover have "(f a)\<^sup>2 * (2*pi) \<ge> 0" by (simp add: zero_le_power2)
    ultimately have "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2)"
      by linarith
    thus ?thesis using ineq_ffa by linarith
  qed
  show "\<exists>c a. \<forall>x \<in> {0..2*pi}. f x = c * sin (x - a)"
    if "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
  proof -
    \<comment> \<open>From the equality, all intermediate inequalities are equalities.\<close>
    note eq_hyp = that
    \<comment> \<open>Re-derive key intermediate facts.\<close>
    have ffa_2fa_int: "(\<lambda>x. 2 * f a * f x) integrable_on {0..2*pi}"
    proof -
      have "(\<lambda>x. (2 * f a) *\<^sub>R f x) integrable_on {0..2*pi}"
        by (rule integrable_cmul[OF integrable_continuous_interval[OF contf]])
      thus ?thesis by simp
    qed
    have fx2_int: "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
      by (intro integrable_continuous_interval continuous_intros contf)
    have ffa_int: "(\<lambda>x. (f x - f a)\<^sup>2) integrable_on {0..2*pi}"
      by (intro integrable_continuous_interval continuous_intros contf)
    have ffa_eq: "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) =
      integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) + (f a)\<^sup>2 * (2*pi)"
    proof -
      have eq: "(f x - f a)\<^sup>2 = (f x)\<^sup>2 - 2 * f a * f x + (f a)\<^sup>2" for x
        by (simp add: power2_eq_square algebra_simps)
      have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) =
        integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x + (f a)\<^sup>2)"
        by (rule integral_cong) (simp add: eq)
      also have "\<dots> = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x) +
        integral {0..2*pi} (\<lambda>x. (f a)\<^sup>2)"
        by (rule Henstock_Kurzweil_Integration.integral_add)
          (auto intro: integrable_diff fx2_int ffa_2fa_int)
      also have "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x) =
        integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) - integral {0..2*pi} (\<lambda>x. 2 * f a * f x)"
        by (rule Henstock_Kurzweil_Integration.integral_diff[OF fx2_int ffa_2fa_int])
      also have "integral {0..2*pi} (\<lambda>x. 2 * f a * f x) = 2 * f a * integral {0..2*pi} f"
        using integral_cmul by simp
      also have "integral {0..2*pi} (\<lambda>x. (f a)\<^sup>2) = (f a)\<^sup>2 * (2*pi)"
        by simp
      finally show ?thesis using f0 by (auto simp: has_integral_integrable_integral)
    qed
    \<comment> \<open>Re-derive g'_zero: (g' has_integral 0) {0..2\<pi>}.\<close>
    have sin_nz_1: "sin (x - a) \<noteq> 0" if "a + pi < x" "x < 2*pi" for x
      by (smt (verit) \<open>0 \<le> a\<close> sin_lt_zero that)
    have sin_nz_2: "sin (x - a) \<noteq> 0" if "a < x" "x < a + pi" for x
      by (smt (verit, ccfv_threshold) sin_gt_zero that)
    have sin_nz_3: "sin (x - a) \<noteq> 0" if "0 < x" "x < a" for x
    proof -
      have "0 < a - x" "a - x < pi" using that \<open>a < pi\<close> by auto
      hence "0 < sin (a - x)" by (rule sin_gt_zero)
      moreover have "sin (x - a) = - sin (a - x)"
        by (metis sin_minus minus_diff_eq)
      ultimately show ?thesis by simp
    qed
    have int1: "(g' has_integral g (2*pi) - g (a + pi)) {a + pi..2*pi}"
      by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_1 in auto)
    have int2: "(g' has_integral g (a + pi) - g a) {a..a + pi}"
      by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_2 in auto)
    have int3: "(g' has_integral g a - g 0) {0..a}"
      by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_3 in auto)
    have api_le: "a \<le> a + pi" and api_le2: "a + pi \<le> 2*pi"
      using \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
    have a_le_2pi: "a \<le> 2*pi" using \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
    have int12: "(g' has_integral (g (a + pi) - g a) + (g (2*pi) - g (a + pi))) {a..2*pi}"
      by (rule has_integral_combine[OF api_le api_le2 int2 int1])
    have int_all: "(g' has_integral (g a - g 0) + ((g (a + pi) - g a) + (g (2*pi) - g (a + pi)))) {0..2*pi}"
      by (rule has_integral_combine[OF \<open>0 \<le> a\<close> a_le_2pi int3 int12])
    have int_all': "(g' has_integral g (2*pi) - g 0) {0..2*pi}"
      using int_all by (simp add: algebra_simps)
    have "g (2*pi) = g 0"
      unfolding g_def using feq by (simp add: tan_def)
    hence g'_zero: "(g' has_integral 0) {0..2*pi}"
      using int_all' by simp
    have ineq_ffa: "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) \<le>
      integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    proof -
      have diff_ge: "(f' x)\<^sup>2 - g' x \<ge> (f x - f a)\<^sup>2" for x
        unfolding g'_def by (simp add: zero_le_power2)
      have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) \<le>
        integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2 - g' x)"
        by (rule integral_le[OF ffa_int])
          (use has_integral_diff[OF integrable_integral[OF f'2] g'_zero]
               has_integral_integrable_integral diff_ge in auto)
      also have "\<dots> = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
        using has_integral_diff[OF integrable_integral[OF f'2] g'_zero]
              has_integral_integrable_integral by auto
      finally show ?thesis .
    qed
    \<comment> \<open>Step 1: f(a) = 0.\<close>
    have fa0: "f a = 0"
    proof -
      have fa2_nonneg: "(f a)\<^sup>2 * (2*pi) \<ge> 0" by (simp add: zero_le_power2)
      have "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le>
        integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2)"
        using ffa_eq fa2_nonneg by linarith
      hence "(f a)\<^sup>2 * (2*pi) \<le> 0"
        using ineq_ffa eq_hyp ffa_eq by linarith
      hence "(f a)\<^sup>2 * (2*pi) = 0" using fa2_nonneg by linarith
      thus "f a = 0" using pi_gt_zero by (simp add: power2_eq_square)
    qed
    \<comment> \<open>Integral of c * sin(x - a) via the fundamental theorem of calculus.\<close>
    have csin_integral: "integral {u..v} (\<lambda>x. c * sin (x - a)) =
        c * (cos (u - a) - cos (v - a))" if "u \<le> v" for u v c
    proof -
      have "((\<lambda>x. - (c * cos (x - a))) has_real_derivative c * sin (x - a)) (at x)" for x
        by (auto intro!: derivative_eq_intros simp: algebra_simps)
      hence hvd: "((\<lambda>x. - (c * cos (x - a))) has_vector_derivative c * sin (x - a))
        (at x within {u..v})" for x
        by (meson has_real_derivative_iff_has_vector_derivative has_vector_derivative_at_within)
      hence "((\<lambda>x. c * sin (x - a)) has_integral
        (- (c * cos (v - a)) - (- (c * cos (u - a))))) {u..v}"
        using that by (intro fundamental_theorem_of_calculus) auto
      thus ?thesis
        by (simp add: has_integral_integrable_integral algebra_simps)
    qed
    show ?thesis
    proof (cases "a=0")
      case True

      then show ?thesis
      proof -
        obtain c1 where c1: "\<And>x. x \<in> {0..pi} \<Longrightarrow> f x = c1 * sin (x - a)"
          sorry
        obtain c2 where c2: "\<And>x. x \<in> {pi..2*pi} \<Longrightarrow> f x = c2 * sin (x - a)"
          sorry
        \<comment> \<open>Use \<integral>f = 0 and csin_integral to show c1 = c2.\<close>
        have eq1: "integral {0..pi} f = c1 * (cos (0 - a) - cos (pi - a))"
        proof -
          have "integral {0..pi} f = integral {0..pi} (\<lambda>x. c1 * sin (x - a))"
            by (rule integral_cong) (use c1 in auto)
          also have "\<dots> = c1 * (cos (0 - a) - cos (pi - a))"
            by (rule csin_integral) (use pi_ge_zero in auto)
          finally show ?thesis .
        qed
        have eq2: "integral {pi..2*pi} f = c2 * (cos (pi - a) - cos (2*pi - a))"
        proof -
          have "integral {pi..2*pi} f = integral {pi..2*pi} (\<lambda>x. c2 * sin (x - a))"
            by (rule integral_cong) (use c2 in auto)
          also have "\<dots> = c2 * (cos (pi - a) - cos (2*pi - a))"
            by (rule csin_integral) (use pi_ge_zero in auto)
          finally show ?thesis .
        qed
        have int_split: "integral {0..2*pi} f = integral {0..pi} f + integral {pi..2*pi} f"
        proof -
          have f_int: "f integrable_on {0..2*pi}"
            using f0 has_integral_integrable by blast
          show ?thesis
            using Henstock_Kurzweil_Integration.integral_combine[OF pi_ge_zero _ f_int]
              pi_ge_zero by linarith
        qed
        have "integral {0..2*pi} f = 0"
          using f0 by (simp add: has_integral_integrable_integral)
        hence "c1 * (cos (0 - a) - cos (pi - a)) + c2 * (cos (pi - a) - cos (2*pi - a)) = 0"
          using int_split eq1 eq2 by linarith
        hence c_eq: "c1 = c2" using True
          by (simp add: cos_two_pi cos_pi)
        show "\<exists>c a. \<forall>x\<in>{0..2 * pi}. f x = c * sin (x - a)"
        proof (intro exI ballI)
          fix x assume "x \<in> {0..2*pi}"
          show "f x = c1 * sin (x - a)"
          proof (cases "x \<le> pi")
            case True
            then show ?thesis using c1[of x] \<open>x \<in> {0..2*pi}\<close> by auto
          next
            case False
            then show ?thesis using c2[of x] c_eq \<open>x \<in> {0..2*pi}\<close> by auto
          qed
        qed
      qed
    next
      case False
      then show ?thesis sorry
    qed
  qed
qed

theorem scaled_Wirtinger_inequality:
  fixes f f' :: "real \<Rightarrow> real"
  assumes "\<And>x. x \<in> {0..1} \<Longrightarrow>
    (f' has_integral (f x - f 0)) {0..x}"
    and "f 1 = f 0"
    and "(f has_integral 0) {0..1}"
    and "(\<lambda>x. (f' x)\<^sup>2) integrable_on {0..1}"
  shows "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..1}"
    and "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) \<le> integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    and "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2) \<Longrightarrow>
      \<exists>c a. \<forall>x \<in> {0..1}. f x = c * sin (2*pi*x - a)"
  sorry 

section \<open>Part 2: Green's theorem for convex area\<close>

text \<open>Area under/above an arc, and the signed area formula for a convex closed curve.\<close>

lemma area_below_arclet:
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
  assumes "u \<le> v"
    and "Re (g u) \<le> Re (g v)"
    and "absolutely_continuous_on {u..v} g"
    and "g ` {u..v} \<subseteq> {z. Im z \<ge> 0}"
    and "inj_on g {u..v}"
    and "\<And>x y. x \<in> g ` {u..v} \<Longrightarrow> y \<in> g ` {u..v} \<Longrightarrow> Re x = Re y \<Longrightarrow> x = y"
    and "negligible S"
    and "\<And>t. t \<in> {u..v} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
    and "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
  sorry 

lemma area_above_arclet:
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
  assumes "u \<le> v"
    and "Re (g v) \<le> Re (g u)"
    and "absolutely_continuous_on {u..v} g"
    and "g ` {u..v} \<subseteq> {z. Im z \<le> 0}"
    and "inj_on g {u..v}"
    and "\<And>x y. x \<in> g ` {u..v} \<Longrightarrow> y \<in> g ` {u..v} \<Longrightarrow> Re x = Re y \<Longrightarrow> x = y"
    and "negligible S"
    and "\<And>t. t \<in> {u..v} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
    and "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
  sorry

theorem green_area_theorem:
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
    and a b :: "complex"
  assumes "simple_path g" "pathstart g = a" "pathfinish g = a"
    and "b \<in> path_image g" "Re a < Re b" "Im a = Im b"
    and "dist a b = diameter (path_image g)"
    and "convex (inside (path_image g))"
    and "absolutely_continuous_on {0..1} g"
    and "negligible U"
    and "\<And>t. t \<in> {0..1} - U \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {0..1}"
    and "\<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> =
      measure lebesgue (inside (path_image g))"
  sorry

section \<open>Part 3: Isoperimetric theorem for convex curves\<close>

theorem isoperimetric_theorem_convex:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "convex (inside (path_image g))"
    "path_length g = L"
  shows "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
      \<exists>a r. path_image g = sphere a r"
  sorry

section \<open>Part 4: Convexification\<close>

text \<open>The step lemma: replacing an arc that deviates from the convex hull frontier
  with a straight segment shortens the path while preserving the convex hull.\<close>

lemma step_lemma:
  fixes g :: "real \<Rightarrow> complex"
  assumes "simple_path g" "pathfinish g = pathstart g"
    and "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g x) (g y) \<le> L * dist x y"
    and "a < b"
    and "a \<in> {0..1}" "b \<in> {0..1}"
    and "g a \<in> frontier (convex hull (path_image g))"
    and "g b \<in> frontier (convex hull (path_image g))"
    and "g ` {a<..<b} \<inter> frontier (convex hull (path_image g)) = {}"
  shows "\<exists>h. simple_path h \<and>
    pathstart h = pathstart g \<and> pathfinish h = pathstart g \<and>
    (\<forall>x \<in> {0..1}. \<forall>y \<in> {0..1}. dist (h x) (h y) \<le> L * dist x y) \<and>
    path_length h < path_length g \<and>
    convex hull (path_image h) = convex hull (path_image g) \<and>
    (\<forall>x. x \<notin> {a<..<b} \<longrightarrow> h x = g x) \<and>
    h ` {a..b} \<subseteq> frontier (convex hull (path_image g))"
  sorry

theorem isoperimetric_convexification:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
  shows "\<exists>h. rectifiable_path h \<and> simple_path h \<and>
    pathfinish h = pathstart h \<and>
    path_length h \<le> path_length g \<and>
    convex hull (path_image h) = convex hull (path_image g) \<and>
    path_image h = frontier (convex hull (path_image g))"
  sorry

theorem isoperimetric_convexification_strict:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "\<not> convex (inside (path_image g))"
  shows "\<exists>h. rectifiable_path h \<and> simple_path h \<and>
    pathfinish h = pathstart h \<and>
    path_length h \<le> path_length g \<and>
    convex hull (path_image h) = convex hull (path_image g) \<and>
    path_image h = frontier (convex hull (path_image g)) \<and>
    measure lebesgue (inside (path_image g)) < measure lebesgue (inside (path_image h))"
  sorry

section \<open>Part 5: The isoperimetric theorem\<close>

theorem isoperimetric_theorem:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "path_length g = L"
  shows "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
      \<exists>a r. path_image g = sphere a r"
proof -
  show ineq: "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
  proof (cases "convex (inside (path_image g))")
    case True
    show ?thesis
      using isoperimetric_theorem_convex(1)[OF assms(1-3) True assms(4)] .
  next
    case False
    obtain h where h: "rectifiable_path h" "simple_path h"
      "pathfinish h = pathstart h"
      "path_length h \<le> path_length g"
      "convex hull (path_image h) = convex hull (path_image g)"
      "path_image h = frontier (convex hull (path_image g))"
      "measure lebesgue (inside (path_image g)) < measure lebesgue (inside (path_image h))"
      using isoperimetric_convexification_strict[OF assms(1-3) False] by blast
    have bounded_hull: "bounded (convex hull (path_image g))"
      by (intro bounded_convex_hull compact_imp_bounded compact_simple_path_image assms(2))
    have eq_int: "inside (path_image h) = interior (convex hull (path_image g))"
      using inside_frontier_eq_interior[OF bounded_hull convex_convex_hull] h(6) by simp
    have convex_h: "convex (inside (path_image h))"
      using eq_int convex_interior[OF convex_convex_hull] by simp
    have ineq_h: "measure lebesgue (inside (path_image h)) \<le> (path_length h)\<^sup>2 / (4 * pi)"
      using isoperimetric_theorem_convex(1)[OF h(1-3) convex_h refl] .
    have mono: "(path_length h)\<^sup>2 / (4 * pi) \<le> L\<^sup>2 / (4 * pi)"
      by (intro divide_right_mono power_mono)
        (use h(4) assms(4) path_length_pos_le[OF h(1)] pi_gt_zero in simp_all)
    show ?thesis using h(7) ineq_h mono by linarith
  qed
  show "\<exists>a r. path_image g = sphere a r"
    if eq: "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi)"
  proof (cases "convex (inside (path_image g))")
    case True
    show ?thesis
      using isoperimetric_theorem_convex(2)[OF assms(1-3) True assms(4)] eq .
  next
    case False
    obtain h where h: "rectifiable_path h" "simple_path h"
      "pathfinish h = pathstart h"
      "path_length h \<le> path_length g"
      "convex hull (path_image h) = convex hull (path_image g)"
      "path_image h = frontier (convex hull (path_image g))"
      "measure lebesgue (inside (path_image g)) < measure lebesgue (inside (path_image h))"
      using isoperimetric_convexification_strict[OF assms(1-3) False] by blast
    have bounded_hull: "bounded (convex hull (path_image g))"
      by (intro bounded_convex_hull compact_imp_bounded compact_simple_path_image assms(2))
    have eq_int: "inside (path_image h) = interior (convex hull (path_image g))"
      using inside_frontier_eq_interior[OF bounded_hull convex_convex_hull] h(6) by simp
    have convex_h: "convex (inside (path_image h))"
      using eq_int convex_interior[OF convex_convex_hull] by simp
    have ineq_h: "measure lebesgue (inside (path_image h)) \<le> (path_length h)\<^sup>2 / (4 * pi)"
      using isoperimetric_theorem_convex(1)[OF h(1-3) convex_h refl] .
    have mono: "(path_length h)\<^sup>2 / (4 * pi) \<le> L\<^sup>2 / (4 * pi)"
      by (intro divide_right_mono power_mono)
        (use h(4) assms(4) path_length_pos_le[OF h(1)] pi_gt_zero in simp_all)
    have "measure lebesgue (inside (path_image g)) < L\<^sup>2 / (4 * pi)"
      using h(7) ineq_h mono by linarith
    with eq show ?thesis by simp
  qed
qed

end
