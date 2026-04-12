theory Isoperimetric
  imports Arc_Length_Reparametrization "Fourier.Fourier" "Green.Green"
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
      proof (rule absolutely_continuous_on_eq[rotated])
        show "absolutely_continuous_on {0..2*pi} (\<lambda>t. f 0 + integral {0..t} f')"
          using absolutely_continuous_on_add[OF absolutely_continuous_on_const
                  absolutely_continuous_indefinite_integral_right[OF f'abs]] .
        fix t assume "t \<in> {0..2*pi}"
        then show "f 0 + integral {0..t} f' = f t" using f_eq by presburger
      qed
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
        using has_vector_derivative_indefinite_integral
          [OF set_lebesgue_integral_eq_integral(1)[OF f'abs]]
        by metis
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
      proof -
        have "sin (t - a) \<noteq> 0" using sin_nz that sub_cx by auto
        show ?thesis unfolding tan_def
          by (simp add: field_simps \<open>sin (t - a) \<noteq> 0\<close>)
      qed
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
        proof -
          have "sin (t - a) * sin (t - a) + cos (t - a) * cos (t - a) = 1"
            using sin_cos_squared_add[of "t - a"] by (simp add: power2_eq_square)
          then show ?thesis using sin_nz_t apply (simp add: inverse_eq_divide power2_eq_square)
          by (metis arith_simps(56) diff_diff_add minus_divide_left)
        qed
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
    note ibp = absolute_real_integration_by_parts_sum
      [where f = "\<lambda>x. (f x - f a)\<^sup>2"
         and g = "\<lambda>x. inverse (tan (x - a))"
         and f' = "\<lambda>x. 2 * (f x - f a) * f' x"
         and g' = "\<lambda>x. - inverse ((sin (x - a))\<^sup>2)"
         and a = c and b = d,
       OF that(1) f'_abs g'_abs f'_int g'_int]
    text \<open>The IBP conclusion gives us \<open>has_integral\<close> for the sum
      \<open>(f x - f a)² * (- inverse (sin (x - a)²)) + 2 * (f x - f a) * f' x * inverse (tan (x - a))\<close>,
      which after algebra equals \<open>g'\<close>, with value \<open>g d - g c\<close>.\<close>
    \<comment> \<open>Specialize IBP at d to get has_integral on {c..d}\<close>
    have ibp_int: "((\<lambda>x. (f x - f a)\<^sup>2 * (- inverse ((sin (x - a))\<^sup>2)) +
      2 * (f x - f a) * f' x * inverse (tan (x - a)))
      has_integral ((f d - f a)\<^sup>2 * inverse (tan (d - a)) -
                    (f c - f a)\<^sup>2 * inverse (tan (c - a)))) {c..d}"
      using ibp(2)[of d] cd by auto
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
        proof -
          have "?F\<^sup>2 * ?s\<^sup>2 + ?F\<^sup>2 * ?c\<^sup>2 = ?F\<^sup>2"
            using sc1 by (simp add: distrib_left[symmetric])
          then show ?thesis by linarith
        qed
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
      by (metis (no_types, lifting) has_integral_eq ibp_int integrand_eq value_eq)
  qed

  show "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    sorry
  show "\<exists>c a. \<forall>x \<in> {0..2*pi}. f x = c * sin (x - a)"
    if "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    sorry
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
