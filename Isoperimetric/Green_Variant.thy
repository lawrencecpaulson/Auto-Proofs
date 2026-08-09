theory Green_Variant
  imports Arc_Length_Reparametrization "Fourier.Square_Integrable"

begin

subsection \<open>Convex curve lemmas\<close>

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

lemma frontier_convex_hull_subset_path_image:
  fixes g :: "real \<Rightarrow> complex"
  assumes "simple_path g" "pathfinish g = pathstart g"
    "path_image g \<subseteq> frontier (convex hull (path_image g))"
  shows "frontier (convex hull path_image g) \<subseteq> path_image g"
proof -
  have bounded_hull: "bounded (convex hull (path_image g))"
    by (simp add: assms(1) bounded_convex_hull bounded_simple_path_image)
      \<comment> \<open>The interior of the convex hull is connected, bounded, and disjoint from @{term "path_image g"}\<close>
  have int_sub: "interior (convex hull (path_image g)) \<inter> path_image g = {}"
    using assms(3) frontier_def by auto
  have "connected (interior (convex hull (path_image g)))"
    by (simp add: convex_connected)
  moreover have "bounded (interior (convex hull (path_image g)))"
    using bounded_hull bounded_interior by blast
  moreover have "interior (convex hull (path_image g)) \<subseteq> - path_image g"
    using int_sub by blast
  moreover have "inside (path_image g) \<subseteq> convex hull path_image g"
    by (metis Un_subset_iff compl_le_swap2 convex_convex_hull hull_subset
        outside_subset_convex union_with_inside)
  ultimately have int_inside: "interior (convex hull (path_image g)) \<subseteq> inside (path_image g)"
    using Jordan_inside_outside[OF \<open>simple_path g\<close>] assms
    by (smt (verit) connected_Int_frontier diff_shunt inf.commute int_sub interior_Int
        interior_eq le_iff_inf)
  have "- (convex hull (path_image g)) \<subseteq> outside (path_image g)"
    by (simp add: hull_subset outside_subset_convex)
  hence inside_sub: "inside (path_image g) \<subseteq> convex hull (path_image g)"
    by (metis Un_subset_iff compl_le_swap2 union_with_inside)
      \<comment> \<open>Since @{term "inside (path_image g)"} is open and contained in the convex hull, it lies in the interior of the hull\<close>
  have "inside (path_image g) \<subseteq> interior (convex hull (path_image g))"
    by (simp add: Jordan_inside_outside assms inside_sub interior_maximal)
  with assms show ?thesis
    using frontier_convex_hull_eq_path_image int_inside by auto
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

  have f_meas_on: "f \<in> borel_measurable (lebesgue_on S)"
    using assms(3) measurable_restrict_space1 by blast
  have f_sq_integ: "integrable (lebesgue_on S) (\<lambda>x. (f x)\<^sup>2)"
    using Lebesgue_Measure.integrable_restrict_UNIV[OF assms(1), of "\<lambda>x. (f x)\<^sup>2"]
    by (simp add: assms(1,4) integrable_restrict_space)
  have f_sq_int: "f square_integrable S"
    unfolding square_integrable_def using assms(1) f_meas_on f_sq_integ by blast

  have one_sq_int: "(\<lambda>x. 1::real) square_integrable S"
    unfolding square_integrable_def 
    using finite_measure_lebesgue_on assms finite_measure.integrable_const by blast

  have schwartz: "\<bar>l2product S f (\<lambda>x. 1)\<bar> \<le> l2norm S f * l2norm S (\<lambda>x. 1)"
    by (rule Schwartz_inequality_abs[OF f_sq_int one_sq_int])

  have "(l2norm S (\<lambda>x. 1))\<^sup>2 = l2product S (\<lambda>x. 1) (\<lambda>x. 1)"
    by (rule l2norm_pow_2[OF one_sq_int])
  also have "\<dots> = measure lebesgue S"
    using finite_measure_lebesgue_on[OF assms(2)]
    by (simp add: l2product_def assms(1) measure_restrict_space)
  finally have "(l2norm S (\<lambda>x. 1))\<^sup>2 = measure lebesgue S" .
  moreover have "(l2product S f (\<lambda>x. 1))\<^sup>2 \<le> (l2norm S f)\<^sup>2 * (l2norm S (\<lambda>x. 1))\<^sup>2"
    by (metis power_mult_distrib real_sqrt_abs schwartz sqrt_le_D)
  moreover
  have "LINT x|lebesgue. indicator S x * f x = l2product S f (\<lambda>x. 1)" 
       "LINT x|lebesgue. indicator S x * (f x)\<^sup>2 = l2product S f f"
    by (simp_all add: to_lebesgue_on l2product_def power2_eq_square)
  ultimately show ?thesis
    by (metis f_sq_int l2norm_pow_2 mult.commute)
qed

locale W =
  fixes f f' :: "real \<Rightarrow> real" and a::real
  assumes f'hsd: "\<And>x. x \<in> {0..2*pi} \<Longrightarrow> (f' has_integral (f x - f 0)) {0..x}"
    and feq: "f (2*pi) = f 0"
    and f0: "(f has_integral 0) {0..2*pi}"
    and f'2: "(\<lambda>x. (f' x)\<^sup>2) integrable_on {0..2*pi}"
    and a: "0 \<le> a" "a < pi" "f (a + pi) = f a"

begin

definition g where "g \<equiv> \<lambda>x. (f x - f a)\<^sup>2 / tan (x - a)"
definition g' where "g' \<equiv> \<lambda>x. (f' x)\<^sup>2 - (f x - f a)\<^sup>2 - (f' x - (f x - f a) / tan (x - a))\<^sup>2"

lemma f': \<open>f' integrable_on {0..2*pi}\<close>
  using f'hsd [of \<open>2*pi\<close>] by fastforce

lemma f'abs: \<open>f' absolutely_integrable_on {0..2*pi}\<close>
proof (rule absolutely_integrable_integrable_bound)
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

lemma contf: \<open>continuous_on {0..2*pi} f\<close>
proof (rule continuous_on_eq)
  show \<open>continuous_on {0..2*pi} (\<lambda>x. integral {0..x} f' + f 0)\<close>
    by (intro continuous_on_add indefinite_integral_continuous_1 [OF f'] continuous_on_const)
  show \<open>\<And>x. x \<in> {0..2*pi} \<Longrightarrow> integral {0..x} f' + f 0 = f x\<close>
    using f'hsd by (auto simp: has_integral_integrable_integral)
qed

text \<open>The integral over completely trouble-free intervals.\<close>
lemma trouble_free: "(g' has_integral g d - g c) {c..d}"
  if cd: "c \<le> d"
    and sub_cd: "{c..d} \<subseteq> {0..2*pi}"
    and sin_nz: "\<And>x. x \<in> {c..d} \<Longrightarrow> sin (x - a) \<noteq> 0"
  for c d
proof -
  have f'_int: "((\<lambda>t. 2 * (f t - f a) * f' t) has_integral
                   ((f x - f a)\<^sup>2 - (f c - f a)\<^sup>2)) {c..x}"
    if xcd: "x \<in> {c..d}" for x
  proof -
    have cx: "c \<le> x" and xd: "x \<le> d" using xcd cd by auto
    have sub_cx: "{c..x} \<subseteq> {0..2*pi}" using sub_cd xd by auto
    have ac_f: "absolutely_continuous_on {0..2*pi} f"
      using absolute_integral_absolutely_continuous_derivative_eq f'abs f'hsd by blast
    have ac_sq: "absolutely_continuous_on {c..x} (\<lambda>t. (f t - f a)\<^sup>2)"
      unfolding power2_eq_square using absolutely_continuous_on_subset ac_f sub_cx 
      by(intro continuous_intros) fastforce+
    obtain k where negk: "negligible k"
      and derivf: "\<And>t. t \<in> {0..2*pi} - k \<Longrightarrow>
          ((\<lambda>u. integral {0..u} f') has_vector_derivative f' t) (at t within {0..2*pi})"
      using f' has_vector_derivative_indefinite_integral by blast
    have deriv_sq: "((\<lambda>t. (f t - f a)\<^sup>2) has_vector_derivative 2 * (f t - f a) * f' t) (at t within {c..x})"
      if "t \<in> {c..x} - k" for t
    proof -
      have hvd_int: "((\<lambda>u. integral {0..u} f') has_vector_derivative f' t) (at t within {0..2*pi})"
        using derivf that sub_cx by auto
      have "((\<lambda>u. f u - f 0) has_vector_derivative f' t) (at t within {0..2*pi})"
      proof (rule has_vector_derivative_transform_within[OF hvd_int])
        fix u assume "u \<in> {0..2*pi}" "dist u t < 1"
        then show "integral {0..u} f' = f u - f 0"
          using f'hsd by blast
      qed (use that sub_cx in auto)
      then have fderiv: "(f has_vector_derivative f' t) (at t within {c..x})"
        using has_vector_derivative_diff_const has_vector_derivative_within_subset sub_cx by blast
      then show ?thesis
        unfolding power2_eq_square has_vector_derivative_def
        by - (rule derivative_eq_intros | simp add: algebra_simps)+
    qed
    show ?thesis
      using fundamental_theorem_of_calculus_absolutely_continuous [OF negk cx ac_sq deriv_sq] by simp
  qed
  text \<open>Apply integration by parts with
      \<^item> \<open>\<lambda>x. (f x - f a)²\<close> and its derivative \<open>\<lambda>x. 2 * (f x - f a) * f' x\<close>
      \<^item> \<open>\<lambda>x. inverse (tan (x - a))\<close> and its derivative \<open>\<lambda>x. - inverse (sin (x - a))²\<close>\<close>
  have ibp_int: "((\<lambda>x. (f x - f a)\<^sup>2 * (- inverse ((sin (x - a))\<^sup>2)) +
      2 * (f x - f a) * f' x * inverse (tan (x - a)))
      has_integral ((f y - f a)\<^sup>2 * inverse (tan (y - a)) -
                    (f c - f a)\<^sup>2 * inverse (tan (c - a)))) {c..y}"
    if "y \<in> {c..d}" for y
  proof (rule absolute_real_integration_by_parts_sum(2))
    show "c \<le> d" using cd .
    show "(\<lambda>x. 2 * (f x - f a) * f' x) absolutely_integrable_on {c..d}"
    proof -
      have f'_abs_cd: "f' absolutely_integrable_on {c..d}"
        using absolutely_integrable_on_subinterval[OF f'abs sub_cd] .
      have cont_ffa: "continuous_on {c..d} (\<lambda>x. 2 * (f x - f a))"
        using sub_cd by (intro continuous_intros continuous_on_subset [OF contf]) auto
      have meas: "(\<lambda>x. 2 * (f x - f a)) \<in> borel_measurable (lebesgue_on {c..d})"
        using cont_ffa by (intro continuous_imp_measurable_on_sets_lebesgue) auto
      have bdd: "bounded ((\<lambda>x. 2 * (f x - f a)) ` {c..d})"
        using cont_ffa compact_Icc compact_continuous_image compact_imp_bounded by blast
      show ?thesis
        using absolutely_integrable_bounded_measurable_product_real
          [OF meas _ bdd f'_abs_cd] by auto
    qed
    show "(\<lambda>x. - inverse ((sin (x - a))\<^sup>2)) absolutely_integrable_on {c..d}"
      by (intro absolutely_integrable_continuous_real continuous_intros) (use sin_nz in auto)
    show "((\<lambda>t. 2 * (f t - f a) * f' t) has_integral
            ((f x - f a)\<^sup>2 - (f c - f a)\<^sup>2)) {c..x}"
      if "x \<in> {c..d}" for x using f'_int[OF that] .
    show "((\<lambda>t. - inverse ((sin (t-a))\<^sup>2)) has_integral
            (inverse (tan (x - a)) - inverse (tan (c - a)))) {c..x}"
      if "x \<in> {c..d}" for x 
    proof -
      have cx: "c \<le> x" and sub_cx: "{c..x} \<subseteq> {c..d}"
        using that by auto
      have inv_tan_eq: "inverse (tan (t-a)) = cos (t-a) / sin (t-a)"
        if "t \<in> {c..x}" for t
        by (simp add: Multiseries_Expansion.tan_conv_sin_cos)
      have deriv: "((\<lambda>t. cos (t-a) / sin (t-a)) has_vector_derivative
                    - inverse ((sin (t-a))\<^sup>2)) (at t within {c..x})"
        if "t \<in> {c..x}" for t
      proof -
        have sin_nz_t: "sin (t-a) \<noteq> 0" using sin_nz that sub_cx by auto
        have "((\<lambda>t. cos (t-a) / sin (t-a)) has_real_derivative
              (- sin (t-a) * sin (t-a) - cos (t-a) * cos (t-a)) / (sin (t-a) * sin (t-a)))
              (at t within {c..x})"
          by (intro derivative_eq_intros | simp add: sin_nz_t)+
        also have "(- sin (t-a) * sin (t-a) - cos (t-a) * cos (t-a)) / (sin (t-a) * sin (t-a))
                 = - inverse ((sin (t-a))\<^sup>2)"
          using sin_cos_squared_add3 [of "t-a"]
          by (simp (no_asm_simp) add: divide_simps power2_eq_square)
        finally show ?thesis
          by (simp add: has_real_derivative_iff_has_vector_derivative)
      qed
        \<comment> \<open>Apply FTC\<close>
      show ?thesis
        using fundamental_theorem_of_calculus[OF cx deriv] inv_tan_eq inv_tan_eq cx
        by simp
    qed
    show "y \<in> {c..d}" using that .
  qed
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
    have "((f x - f a)\<^sup>2 * (- inverse (?s\<^sup>2)) + 2 * (f x - f a) * f' x * inverse (tan (x - a))) * ?s\<^sup>2
          = - ?F\<^sup>2 + 2 * ?F * f' x * ?c * ?s"
      using snz snz2 by (simp add: tan_def field_simps power2_eq_square)
    moreover have "g' x * ?s\<^sup>2 = ((f' x)\<^sup>2 - ?F\<^sup>2) * ?s\<^sup>2 - (f' x * ?s - ?F * ?c)\<^sup>2"
      using snz by (simp add: g'_def tan_def field_simps)
    moreover have "\<dots>  = - ?F\<^sup>2 + 2 * ?F * f' x * ?c * ?s"
      using sc1 by algebra 
    ultimately show ?thesis using snz2
      by (metis mult_right_cancel)
  qed
    \<comment> \<open>Combine using has_integral_eq\<close>
  show ?thesis
    using has_integral_eq ibp_int integrand_eq unfolding g_def divide_inverse
    by (metis (no_types, lifting) atLeastAtMost_iff order.refl that(1))
qed

text \<open>Continuity of @{term g}.\<close>
lemma g_cont: "continuous_on {0..2*pi} g"
  unfolding continuous_on_eq_continuous_within
proof
  fix c assume c_in: "c \<in> {0..2*pi}"
  show "continuous (at c within {0..2*pi}) g"
  proof (cases "sin (c - a) = 0")
    case False
      \<comment> \<open>When $\sin(c - a) \neq 0$, @{term g} is a quotient of continuous functions.\<close>
    have g_eq: "g x = (f x - f a)\<^sup>2 * cos (x - a) / sin (x - a)" for x
      unfolding g_def tan_def by (simp add: field_simps)
    have "continuous (at c within {0..2*pi}) f"
      using contf c_in continuous_on_eq_continuous_within by blast
    then show ?thesis unfolding g_eq
      using False by (auto simp: continuous_intros)
  next
    case True
      \<comment> \<open>When $\sin(c - a) = 0$, we have $g(c) = 0$ and need to show $g(x) \to 0$.\<close>
    have fca: "f c = f a"
    proof -
      from True obtain n :: int where npi: "c - a = of_int n * pi"
        using sin_zero_iff_int2 by auto
      have "of_int n \<ge> -a / pi" "of_int n \<le> (2 * pi - a) / pi"
        using a npi c_in pi_gt_zero by (simp_all add: field_simps)
      moreover have "-a / pi > -1" using a pi_gt_zero by (simp add: field_simps)
      moreover have "(2 * pi - a) / pi < 3"
        using a pi_gt_zero by (auto simp: divide_simps)
      ultimately have "of_int n > (-1 :: real)" "of_int n < (3 :: real)" by linarith+
      then have "n = 0 \<or> n = 1 \<or> n = 2"
        by auto
      thus ?thesis
      proof (elim disjE)
        assume "n = 2"
        then have "c = a + 2 * pi" using npi by (simp add: algebra_simps)
        with c_in a pi_gt_zero have "a = 0" by auto
        thus "f c = f a" using \<open>c = a + 2 * pi\<close> feq by simp
      qed (use npi a in \<open>auto simp: algebra_simps\<close>)
    qed
    have gc0: "g c = 0"
      unfolding g_def using fca by simp
    show ?thesis unfolding continuous_within gc0
    proof -
      \<comment> \<open>Derive $\tan(x - a) = \tan(x - c)$ from $\sin(c - a) = 0$.\<close>
      from True obtain n :: int where npi: "c - a = of_int n * pi"
        using sin_zero_iff_int2 by auto
      have tan_eq: "tan (x - a) = tan (x - c)" for x
        by (metis npi diff_add_cancel diff_diff_eq2 tan_periodic_int)
      have g_eq2: "g x = (f x - f c)\<^sup>2 * cos (x - c) / sin (x - c)" for x
        unfolding g_def by (metis fca divide_divide_eq_right local.tan_eq tan_def)
      show "(g \<longlongrightarrow> 0) (at c within {0..2*pi})"
      proof -
        \<comment> \<open>Cauchy--Schwarz bound: $(f(x) - f(c))^2 \le |x - c| \cdot \int_c^x (f')^2$.\<close>
        have cs_bound: "(f x - f c)\<^sup>2 \<le> \<bar>x - c\<bar> * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
          if xin: "x \<in> {0..2*pi}" for x
        proof -
          have f'_int_sub: "f' integrable_on {a..b}" if "{a..b} \<subseteq> {0..2*pi}" for a b
            using integrable_subinterval_real[OF set_lebesgue_integral_eq_integral(1)[OF f'abs] that] .
          have f'2_int_sub: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {a..b}" if "{a..b} \<subseteq> {0..2*pi}" for a b
            using integrable_subinterval_real[OF f'2 that] .
              \<comment> \<open>Helper: the FTC gives $f(b) - f(a) = \int_a^b f'$ for $a, b \in \{0..2\pi\}$\<close>
          have ftc_sub: "f b - f a = integral {a..b} f'"
            if "a \<in> {0..2*pi}" "b \<in> {0..2*pi}" "a \<le> b" for a b
          proof -
            have "integral {0..a} f' + integral {a..b} f' = integral {0..b} f'"
              by (meson Henstock_Kurzweil_Integration.integral_combine atLeastAtMost_iff f'hsd
                  has_integral_integrable that)
            moreover have "integral {0..a} f' = f a - f 0" and "integral {0..b} f' = f b - f 0"
              using f'hsd that by (auto simp: has_integral_integrable_integral)
            ultimately show ?thesis by linarith
          qed
            \<comment> \<open>Helper: Cauchy--Schwarz $\left(\int_I f'\right)^2 \le (b-a) \cdot \int_I (f')^2$ for $I = \{a..b\} \subseteq \{0..2\pi\}$\<close>
          have cs_sub: "(integral {a..b} f')\<^sup>2 \<le> (b-a) * integral {a..b} (\<lambda>t. (f' t)\<^sup>2)"
            if sub: "{a..b} \<subseteq> {0..2*pi}" and ab: "a < b" for a b
          proof -
            define \<mu> where "\<mu> \<equiv> integral {a..b} f' / (b-a)"
            have f'I: "f' integrable_on {a..b}" by (rule f'_int_sub[OF sub])
            have f'2I: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {a..b}" by (rule f'2_int_sub[OF sub])
            have int1: "(\<lambda>t. - (2 * \<mu>) * f' t) integrable_on {a..b}"
              using integrable_cmul[OF f'I, of "- (2 * \<mu>)"] by (simp add: scaleR_conv_of_real)
            have sub_int: "(\<lambda>t. (f' t - \<mu>)\<^sup>2) integrable_on {a..b}"
              using integrable_add[OF f'2I integrable_add[OF int1 integrable_const_ivl]]
              by (simp add: power2_eq_square algebra_simps)
            have "0 \<le> integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2)"
              by (rule integral_nonneg[OF sub_int]) (simp add: zero_le_power2)
            also have "integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2) =
                integral {a..b} (\<lambda>t. (f' t)\<^sup>2) + (- (2 * \<mu>) * integral {a..b} f' + \<mu>\<^sup>2 * (b-a))"
            proof -
              have "integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2) =
                  integral {a..b} (\<lambda>t. (f' t)\<^sup>2 + (- (2 * \<mu>) * f' t + \<mu>\<^sup>2))"
                by (rule integral_cong) (simp add: power2_eq_square algebra_simps)
              also have "\<dots> = integral {a..b} (\<lambda>t. (f' t)\<^sup>2) +
                  integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t + \<mu>\<^sup>2)"
                by (rule integral_add[OF f'2I integrable_add[OF int1 integrable_const_ivl]])
              also have "integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t + \<mu>\<^sup>2) =
                  integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t) + integral {a..b} (\<lambda>t. \<mu>\<^sup>2)"
                by (rule integral_add[OF int1 integrable_const_ivl])
              finally show ?thesis using ab by simp
            qed
            also have "- (2 * \<mu>) * integral {a..b} f' + \<mu>\<^sup>2 * (b-a) = - (integral {a..b} f')\<^sup>2 / (b-a)"
              using ab unfolding \<mu>_def by (simp add: power2_eq_square divide_simps)
            finally show ?thesis using ab by (simp add: pos_divide_le_eq mult.commute)
          qed
          show ?thesis
          proof (cases "c \<le> x")
            case True
            show ?thesis using cs_sub \<open>c \<le> x\<close> c_in xin ftc_sub by fastforce
          next
            case False
            hence \<section>: "x < c" "{x..c} \<subseteq> {0..2*pi}" using c_in xin by auto
            then show ?thesis
              by (simp add: cs_sub ftc_sub power2_commute)
          qed
        qed
          \<comment> \<open>The integral of $(f')^2$ over a shrinking interval tends to $0$.\<close>
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
                  integrable_on_subinterval order_refl sub)
            hence "integral {c..x} (\<lambda>t. (f' t)\<^sup>2) = F x - F c"
              unfolding F_def by linarith
            moreover have "0 \<le> integral {c..x} (\<lambda>t. (f' t)\<^sup>2)"
              by (metis integral_nonneg not_integrable_integral order.refl zero_le_power2)
            ultimately show ?thesis using True by (simp add: min_def max_def)
          next
            case False
            hence xc: "x \<le> c" by simp
            have sub: "{x..c} \<subseteq> {0..2*pi}" using c_in that xc by auto
            have "integral {0..x} (\<lambda>t. (f' t)\<^sup>2) + integral {x..c} (\<lambda>t. (f' t)\<^sup>2) 
                  = integral {0..c} (\<lambda>t. (f' t)\<^sup>2)"
              by (metis Henstock_Kurzweil_Integration.integral_combine atLeastatMost_subset_iff f'2
                  integrable_subinterval_real order.refl sub xc)
            moreover have "0 \<le> integral {x..c} (\<lambda>t. (f' t)\<^sup>2)"
              by (metis integral_nonneg not_integrable_integral order.refl zero_le_power2)
            ultimately show ?thesis using xc by (simp add: F_def min_def max_def)
          qed
          have "((\<lambda>x. \<bar>F x - F c\<bar>) \<longlongrightarrow> 0) (at c within {0..2*pi})"
            by (metis F_cont LIM_zero_iff c_in continuous_on_def tendsto_rabs_zero)
          thus ?thesis
            by (smt (verit, best) F_eq Lim_cong_within)
        qed
        have "\<forall>\<^sub>F x in at c. \<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> < 2"
          by real_asymp
        then have sinc_ratio_bounded:
          "\<forall>\<^sub>F x in at c within {0..2*pi}. \<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> \<le> 2"
          by (metis (no_types, lifting) UNIV_I eventually_at_topological less_imp_le)
            \<comment> \<open>Now combine everything.\<close>
        show ?thesis
        proof (rule Lim_null_comparison[where g = "\<lambda>x. 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"])
          show "\<forall>\<^sub>F x in at c within {0..2*pi}. norm (g x) \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
          proof -
            have mem: "\<forall>\<^sub>F x in at c within {0..2*pi}. x \<in> {0..2*pi}"
              unfolding at_within_def eventually_inf_principal by simp
            show ?thesis
            proof (rule eventually_mono[OF eventually_conj[OF sinc_ratio_bounded mem]])
              fix x assume H: "\<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> \<le> 2 \<and> x \<in> {0..2*pi}"
              have "\<bar>g x\<bar> = (f x - f c)\<^sup>2 * \<bar>cos (x - c)\<bar> / \<bar>sin (x - c)\<bar>"
                using g_eq2 by (simp add: abs_mult)
              also have "\<dots> \<le> (f x - f c)\<^sup>2 * 1 / \<bar>sin (x - c)\<bar>"
                by (meson abs_cos_le_one abs_ge_zero divide_right_mono
                    ordered_comm_semiring_class.comm_mult_left_mono zero_le_power2)
              also have "\<dots> = (f x - f c)\<^sup>2 / \<bar>sin (x - c)\<bar>" by simp
              also have "\<dots> \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
              proof -
                have sub: "{min c x..max c x} \<subseteq> {0..2*pi}" using c_in H by auto
                have f'2I: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {min c x..max c x}"
                  by (rule integrable_subinterval_real[OF f'2 sub])
                show ?thesis
                proof (cases "sin (x - c) = 0")
                  case False
                  define I where "I = integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
                  have Ige: "I \<ge> 0"
                    unfolding I_def by (rule integral_nonneg[OF f'2I]) auto
                  have "(f x - f c)\<^sup>2 / \<bar>sin (x - c)\<bar> \<le> \<bar>x - c\<bar> * I / \<bar>sin (x - c)\<bar>"
                    using H by (simp add: I_def cs_bound divide_right_mono)
                  also have "\<dots> = (\<bar>x - c\<bar> / \<bar>sin (x - c)\<bar>) * I"
                    by (simp add: field_simps)
                  also have "\<dots> \<le> 2 * I"
                    by (meson H Ige mult_mono order.refl zero_le_numeral)
                  finally show ?thesis unfolding I_def .
                qed (use integral_nonneg[OF f'2I] in auto)
              qed
              finally show "norm (g x) \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)" by simp
            qed
          qed
          show "((\<lambda>x. 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)) \<longlongrightarrow> 0) (at c within {0..2*pi})"
            using tendsto_mult_right_zero[OF f'2_int_tends_0] by simp
        qed
      qed
    qed
  qed
qed

text \<open>The integral over mainly trouble-free intervals:
    we only need \<open>sin(x - a) \<noteq> 0\<close> on the open interior, allowing zeros at the endpoints.\<close>
lemma mainly_trouble_free: "(g' has_integral g d - g c) {c..d}"
  if "c \<le> d" and "{c..d} \<subseteq> {0..2*pi}" and "\<And>x. x \<in> {c<..<d} \<Longrightarrow> sin (x - a) \<noteq> 0"
  for c d
proof -
  note cd_le = \<open>c \<le> d\<close> and cd_sub = \<open>{c..d} \<subseteq> {0..2*pi}\<close>
    and sin_nz = \<open>\<And>x. x \<in> {c<..<d} \<Longrightarrow> sin (x - a) \<noteq> 0\<close>
  have "g' absolutely_integrable_on {c..d}"
  proof -
    have f'2_abs: "(\<lambda>x. (f' x)\<^sup>2) absolutely_integrable_on {0..2*pi}"
      by (rule abs_absolutely_integrableI_1[OF f'2]) (simp add: integrable_eq[OF f'2])
    have ffa_abs: "(\<lambda>x. (f x - f a)\<^sup>2) absolutely_integrable_on {0..2*pi}"
      by (rule absolutely_integrable_continuous_real)
        (intro continuous_intros contf)
    have g'_int_sub: "g' integrable_on {u..v}" if uv_sub: "{u..v} \<subseteq> {c<..<d}" for u v
    proof (cases "u \<le> v")
      case True
      then have uv_mem: "u \<in> {c<..<d}" "v \<in> {c<..<d}" and  uv_2pi: "{u..v} \<subseteq> {0..2*pi}"
        using uv_sub cd_sub by auto
      have sin_nz': "sin (x - a) \<noteq> 0" if "x \<in> {u..v}" for x
        using sin_nz that uv_sub by blast
      show ?thesis
        using has_integral_integrable[OF trouble_free[OF True uv_2pi sin_nz']] by auto
    qed (simp add: not_le integrable_on_empty)
    have g'_int: "g' integrable_on {c'..d'}" if "{c'..d'} \<subseteq> {c<..<d}" for c' d'
      using \<open>{c'..d'} \<subseteq> {c<..<d}\<close> g'_int_sub by blast
    have abs_g_cont: \<open>continuous_on {0..2 * pi} (\<lambda>x. \<bar>g x\<bar>)\<close>
      by (intro continuous_intros g_cont)
    obtain h where h_abs: "h absolutely_integrable_on {c..d}" 
      and h_bounded: "(\<forall>x\<in>{c..d}. g' x \<le> h x) \<or> (\<forall>x\<in>{c..d}. h x \<le> g' x)"
      using absolutely_integrable_on_subinterval[OF f'2_abs cd_sub]
      by (simp add: g'_def) 
    show ?thesis
    proof (intro g'_int absolutely_integrable_improper [of c d , unfolded box_real])
      obtain w where "0 \<le> w" "w \<le> 2*pi" and w: "\<forall>y. 0\<le>y \<longrightarrow> y \<le> 2*pi \<longrightarrow> \<bar>g y\<bar> \<le> \<bar>g w\<bar>"
        using continuous_attains_sup [of \<open>{0..2*pi}\<close> \<open>\<lambda>x. \<bar>g x\<bar>\<close>]
        by (metis Arg2pi abs_g_cont atLeastAtMost_iff compact_Icc empty_iff less_eq_real_def)
      show "bounded {integral {c'..d'} g' |c' d'. {c'..d'} \<subseteq> {c<..<d}}"
      proof (rule boundedI)
        fix x assume "x \<in> {integral {c'..d'} g' |c' d'. {c'..d'} \<subseteq> {c<..<d}}"
        then obtain c' d' where cd': "{c'..d'} \<subseteq> {c<..<d}" and xeq: "x = integral {c'..d'} g'"
          by auto
        show "norm x \<le> 2 * \<bar>g w\<bar>"
        proof (cases "c' \<le> d'")
          case True
          have sub_2pi: "{c'..d'} \<subseteq> {0..2*pi}"
            using cd' cd_sub greaterThanLessThan_subseteq_atLeastAtMost_iff by blast
          have "sin (t-a) \<noteq> 0" if "t \<in> {c'..d'}" for t
            using that cd' sin_nz by (meson greaterThanLessThan_subseteq_atLeastAtMost_iff subsetD)
          then have "integral {c'..d'} g' = g d' - g c'"
            using True sub_2pi trouble_free by blast
          then have "\<bar>x\<bar> \<le> \<bar>g d'\<bar> + \<bar>g c'\<bar>"
            using xeq by linarith
          also have "\<dots> \<le> \<bar>g w\<bar> + \<bar>g w\<bar>"
            by (metis True w add_mono atLeastatMost_subset_iff order_trans sub_2pi)
          also have "\<dots> = 2 * \<bar>g w\<bar>" by algebra
          finally show ?thesis by (simp add: xeq)
        qed (simp add: xeq)
      qed
    qed (use h_abs h_bounded in auto)
  qed
  show ?thesis
  proof -
    have g'_int: "g' integrable_on {c..d}"
      using \<open>g' absolutely_integrable_on {c..d}\<close> set_lebesgue_integral_eq_integral by blast
    have g_cont_cd: "continuous_on {c..d} g"
      using continuous_on_subset[OF g_cont cd_sub] .
    have goal: "integral {c..d} g' = g d - g c"
    proof (cases "c < d")
      case False with cd_le show ?thesis by simp
    next
      case True
        \<comment> \<open>Pick sequences $c_n \to c$ and $d_n \to d$ from inside $(c,d)$\<close>
      define c_n where "c_n \<equiv> \<lambda>n. c + (d - c) / (real n + 2)"
      define d_n where "d_n \<equiv> \<lambda>n. d - (d - c) / (real n + 2)"
      have pos: "0 < (d - c) / (real n + 2)" for n
        using True by auto
      have lt_dc: "(d - c) / (real n + 2) < d - c" for n
        using True by (simp add: divide_less_eq)
      have c_n_le_d_n: "c_n n \<le> d_n n" for n
      proof -
        have "c * real n \<le> d * real n"
          using True by (intro mult_right_mono) auto
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
          \<comment> \<open>On each $\{c_n..d_n\}$, \<open>trouble_free\<close> applies\<close>
      have c_n_in: "c_n n \<in> {c<..<d}" and d_n_in: "d_n n \<in> {c<..<d}" for n
        using pos[of n] lt_dc[of n] unfolding c_n_def d_n_def by auto
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
            by (rule integrable_subinterval_real[OF g'_int]) (use d_n_cd[of n] cd_le in auto)
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
      moreover have "(\<lambda>n. g (d_n n) - g (c_n n)) \<longlonglongrightarrow> g d - g c"
      proof (intro tendsto_diff)
        obtain d_n_cd: "d_n n \<in> {c..d}" and c_n_cd: "c_n n \<in> {c..d}" for n
          using c_n_in d_n_in less_eq_real_def by force
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

end

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
  obtain a where a: "0 \<le> a" "a < pi" "f (a + pi) = f a"
  proof -
    have contf: \<open>continuous_on {0..2*pi} f\<close>
    proof (rule continuous_on_eq)
      show \<open>continuous_on {0..2*pi} (\<lambda>x. integral {0..x} f' + f 0)\<close>
        using f'hsd [of \<open>2*pi\<close>] 
        by (intro continuous_on_add indefinite_integral_continuous_1  continuous_on_const) auto
      show \<open>\<And>x. x \<in> {0..2*pi} \<Longrightarrow> integral {0..x} f' + f 0 = f x\<close>
        using f'hsd by (auto simp: has_integral_integrable_integral)
    qed
    define h where "h \<equiv> \<lambda>x. f (x + pi) - f x"
    have hcont: "continuous_on {0..pi} h"
      unfolding h_def
      by (intro continuous_intros continuous_on_compose2 [OF contf]) auto
    have heq: "h 0 + h pi = 0"
      unfolding h_def using feq by simp
    have iv: "is_interval (h ` {0..pi})"
      using is_interval_connected_1 connected_continuous_image [OF hcont connected_Icc]
      by blast
    have"h 0 \<in> h ` {0..pi}"  "h pi \<in> h ` {0..pi}"
      using pi_gt_zero by auto
    with heq obtain a where "a \<in> {0..pi}" "h a = 0"
      by (smt (verit, best) imageE is_interval_1 iv)
    show thesis
    proof (cases "a = pi")
      case True
      then have "h 0 = 0" using heq \<open>h a = 0\<close> by auto
      then show thesis using that [of 0] pi_gt_zero by (auto simp: h_def)
    next
      case False
      then show thesis using that [of a] \<open>a \<in> {0..pi}\<close> \<open>h a = 0\<close>
        by (auto simp: h_def)
    qed
  qed

  interpret W f f' a
    using W.intro a assms by blast

  show "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
    by (intro integrable_continuous_interval continuous_on_power contf)

\<comment> \<open>Zeros of sin(x - a) in [0, 2\<pi>] are exactly at x = a and x = a + \<pi>.\<close>
  have sin_nz_1: "sin (x - a) \<noteq> 0" if "a + pi < x" "x < 2*pi" for x
    by (smt (verit) \<open>0 \<le> a\<close> sin_lt_zero that)
  have sin_nz_2: "sin (x - a) \<noteq> 0" if "a < x" "x < a + pi" for x
    by (smt (verit, ccfv_threshold) sin_gt_zero that)
  have sin_nz_3: "sin (x - a) \<noteq> 0" if "0 < x" "x < a" for x
    using \<open>a < pi\<close> sin_zero_pi_iff that by auto
      \<comment> \<open>Apply \<open>mainly_trouble_free\<close> on three intervals.\<close>
  have int1: "(g' has_integral g (2*pi) - g (a + pi)) {a + pi..2*pi}"
    by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_1 in auto)
  have int2: "(g' has_integral g (a + pi) - g a) {a..a + pi}"
    by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_2 in auto)
  have int3: "(g' has_integral g a - g 0) {0..a}"
    by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_3 in auto)
      \<comment> \<open>Combine the three integrals using \<open>has_integral_combine\<close>.\<close>
  have api_le: "a \<le> a + pi" and api_le2: "a + pi \<le> 2*pi"
    using \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
  have a_le_2pi: "a \<le> 2*pi" using \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
  have int12: "(g' has_integral (g (a + pi) - g a) + (g (2*pi) - g (a + pi))) {a..2*pi}"
    by (rule has_integral_combine[OF api_le api_le2 int2 int1])
  have int_all: "(g' has_integral (g a - g 0) + ((g (a + pi) - g a) + (g (2*pi) - g (a + pi)))) {0..2*pi}"
    by (rule has_integral_combine[OF \<open>0 \<le> a\<close> a_le_2pi int3 int12])
      \<comment> \<open>Simplify: the telescoping sum gives $g(2\pi) - g(0)$.\<close>
  have int_all': "(g' has_integral g (2*pi) - g 0) {0..2*pi}"
    using int_all by (simp add: algebra_simps)
      \<comment> \<open>Show $g(2\pi) = g(0)$, so the integral of $g'$ is $0$.\<close>
  have "g (2*pi) = g 0"
    unfolding g_def using feq by (simp add: tan_def)
  hence g'_zero: "(g' has_integral 0) {0..2*pi}"
    using int_all' by simp
      \<comment> \<open>Extract the inequality from $\int g' = 0$.\<close>
  have ffa_int: "(\<lambda>x. (f x - f a)\<^sup>2) integrable_on {0..2*pi}"
    by (intro integrable_continuous_interval continuous_intros contf)
  have g'_int: "g' integrable_on {0..2*pi}"
    using g'_zero by (auto simp: has_integral_integrable_integral)
  have diff_int: "((\<lambda>x. (f' x)\<^sup>2 - g' x) has_integral integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2) - 0) {0..2*pi}"
    by (rule has_integral_diff[OF integrable_integral[OF f'2] g'_zero])
  have diff_eq: "(f' x)\<^sup>2 - g' x = (f x - f a)\<^sup>2 + (f' x - (f x - f a) / tan (x - a))\<^sup>2" for x
    unfolding g'_def by (simp add: algebra_simps)
  have diff_ge: "(f' x)\<^sup>2 - g' x \<ge> (f x - f a)\<^sup>2" for x
    unfolding diff_eq by (simp add: zero_le_power2)
  have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2 - g' x)"
    by (rule integral_le[OF ffa_int]) (use diff_int has_integral_integrable_integral in \<open>auto intro: diff_ge\<close>)
  also have "\<dots> = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    using diff_int has_integral_integrable_integral by auto
  finally have ineq_ffa: "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)" .
      \<comment> \<open>Show $\int f(x)^2 \le \int (f(x)-f(a))^2$ using $\int f = 0$.\<close>
  have "(f x)\<^sup>2 \<le> (f x - f a)\<^sup>2 + 2 * f a * f x - (f a)\<^sup>2" for x
    by (simp add: power2_eq_square algebra_simps)
  have fx_eq: "(f x)\<^sup>2 = (f x - f a)\<^sup>2 + 2 * f a * f x - (f a)\<^sup>2" for x
    by (simp add: power2_eq_square algebra_simps)
  have f_int: "f integrable_on {0..2*pi}"
    by (rule integrable_continuous_interval[OF contf])
  have f_integral_0: "integral {0..2*pi} f = 0"
    using f0 by (auto simp: has_integral_integrable_integral)
  have eq: "(f x - f a)\<^sup>2 = (f x)\<^sup>2 - 2 * f a * f x + (f a)\<^sup>2" for x
    by (simp add: power2_eq_square algebra_simps)
  have fx2_int: "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
    by (intro integrable_continuous_interval continuous_intros contf)
  have ffa_2fa_int: "(\<lambda>x. 2 * f a * f x) integrable_on {0..2*pi}"
    using f_int integrable_on_mult_right by blast
  have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x + (f a)\<^sup>2)"
    by (simp add: eq)
  also have "\<dots> = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x) + integral {0..2*pi} (\<lambda>x. (f a)\<^sup>2)"
    by (rule Henstock_Kurzweil_Integration.integral_add)
      (auto intro: integrable_diff fx2_int ffa_2fa_int)
  also have "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x) =
        integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) - integral {0..2*pi} (\<lambda>x. 2 * f a * f x)"
    by (rule Henstock_Kurzweil_Integration.integral_diff[OF fx2_int ffa_2fa_int])
  also have "integral {0..2*pi} (\<lambda>x. 2 * f a * f x) = 0"
    using integral_cmul by (simp add: f_integral_0)
  also have "integral {0..2*pi} (\<lambda>x. (f a)\<^sup>2) = (f a)\<^sup>2 * (2*pi)"
    by simp
  finally have ffa_eq: "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) 
                      = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) + (f a)\<^sup>2 * (2*pi)"
    by linarith
  then have ffa_ineq': "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2)"
    by auto
  thus "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    using ineq_ffa by linarith
  show "\<exists>c a. \<forall>x \<in> {0..2*pi}. f x = c * sin (x - a)"
    if "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
  proof -
    \<comment> \<open>From the equality, all intermediate inequalities are equalities.\<close>
    have fa0: "f a = 0"
      by (smt (verit, best) ffa_ineq' a ffa_eq ineq_ffa mult_eq_0_iff power_eq_0_iff that)
    \<comment> \<open>The "rest" term integrates to 0.\<close>
    define rest where "rest \<equiv> \<lambda>x. f' x - (f x - f a) / tan (x - a)"
    have diff_eq: "(f' x)\<^sup>2 - g' x = (f x - f a)\<^sup>2 + (rest x)\<^sup>2" for x
      unfolding g'_def rest_def by (simp add: algebra_simps)
    have rest_sq_int: "(\<lambda>x. (rest x)\<^sup>2) integrable_on {0..2*pi}"
    proof -
      have diff_int: "(\<lambda>x. (f' x)\<^sup>2 - g' x) integrable_on {0..2*pi}"
        using has_integral_diff[OF integrable_integral[OF f'2] g'_zero]
              has_integral_integrable by blast
      have eq: "(\<lambda>x. (rest x)\<^sup>2) = (\<lambda>x. (f' x)\<^sup>2 - g' x - (f x - f a)\<^sup>2)"
        by (rule ext) (use diff_eq in \<open>simp add: algebra_simps\<close>)
      show ?thesis unfolding eq
        by (rule integrable_diff[OF diff_int ffa_int])
    qed
    have rest_sq_zero: "integral {0..2*pi} (\<lambda>x. (rest x)\<^sup>2) = 0"
    proof -
      have "integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2 - g' x) =
        integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
        using has_integral_diff[OF integrable_integral[OF f'2] g'_zero]
              has_integral_integrable_integral by auto
      moreover have "integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2 - g' x) =
        integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) + integral {0..2*pi} (\<lambda>x. (rest x)\<^sup>2)"
      proof -
        have eq: "(f' x)\<^sup>2 - g' x = (f x - f a)\<^sup>2 + (rest x)\<^sup>2" for x
          using diff_eq by auto
        have "integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2 - g' x) =
          integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2 + (rest x)\<^sup>2)"
          by (rule integral_cong) (use eq in auto)
        also have "\<dots> = integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) +
          integral {0..2*pi} (\<lambda>x. (rest x)\<^sup>2)"
          by (rule Henstock_Kurzweil_Integration.integral_add[OF ffa_int rest_sq_int])
        finally show ?thesis .
      qed
      moreover have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2)"
        using ffa_eq fa0 by simp
      ultimately show ?thesis using that by linarith
    qed
    \<comment> \<open>Integral of $c \sin(x - a)$ via the fundamental theorem of calculus.\<close>
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
    \<comment> \<open>Key fact: on intervals where $\sin(x-a) \neq 0$, @{term f} equals $c \sin(x-a)$.\<close>
    have key_fact: "\<exists>c. \<forall>x\<in>{u..v}. f x = c * sin (x - a)"
      if huv: "0 \<le> u" "u < v" "v \<le> 2*pi"
        and hsin: "\<And>x. x \<in> {u<..<v} \<Longrightarrow> sin (x - a) \<noteq> 0"
      for u v
    proof -
      \<comment> \<open>Open-interval version (to be proved later).\<close>
      have open_ver: "\<exists>c. \<forall>x\<in>{u<..<v}. f x = c * sin (x - a)"
      proof -
        \<comment> \<open>Step 1: $\int_u^v \mathit{rest}^2 = 0$ from $\int_0^{2\pi} \mathit{rest}^2 = 0$ and nonnegativity.\<close>
        have rest_sq_sub: "(\<lambda>x. (rest x)\<^sup>2) integrable_on {u..v}"
          by (rule integrable_subinterval_real[OF rest_sq_int])
             (use huv in auto)
        have rest_sq_nonneg: "0 \<le> (rest x)\<^sup>2" for x
          by (rule zero_le_power2)
        have "integral {u..v} (\<lambda>x. (rest x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (rest x)\<^sup>2)"
          by (rule integral_subset_le[OF _ rest_sq_sub rest_sq_int])
             (use huv rest_sq_nonneg in auto)
        moreover have "0 \<le> integral {u..v} (\<lambda>x. (rest x)\<^sup>2)"
          by (rule integral_nonneg[OF rest_sq_sub]) (use rest_sq_nonneg in auto)
        ultimately have rest_sq_sub_zero: "integral {u..v} (\<lambda>x. (rest x)\<^sup>2) = 0"
          using rest_sq_zero by linarith
        \<comment> \<open>Step 2: $\mathit{rest} = 0$ a.e. on $\{u..v\}$ via Lebesgue theory.\<close>
        have rest_ae_zero: "AE x in lebesgue_on {u..v}. rest x = 0"
        proof -
          have uv_meas: "{u..v} \<in> sets lebesgue" by simp
          have rest_sq_abs: "(\<lambda>x. (rest x)\<^sup>2) absolutely_integrable_on {u..v}"
            by (rule nonnegative_absolutely_integrable_1[OF rest_sq_sub])
               (use rest_sq_nonneg in auto)
          have rest_sq_leb: "integrable (lebesgue_on {u..v}) (\<lambda>x. (rest x)\<^sup>2)"
            by (rule absolutely_integrable_imp_integrable[OF rest_sq_abs uv_meas])
          have "integral\<^sup>L (lebesgue_on {u..v}) (\<lambda>x. (rest x)\<^sup>2) = integral {u..v} (\<lambda>x. (rest x)\<^sup>2)"
            by (rule lebesgue_integral_eq_integral[OF rest_sq_leb uv_meas])
          hence leb_zero: "integral\<^sup>L (lebesgue_on {u..v}) (\<lambda>x. (rest x)\<^sup>2) = 0"
            using rest_sq_sub_zero by simp
          have "AE x in lebesgue_on {u..v}. (rest x)\<^sup>2 = 0"
            using integral_nonneg_eq_0_iff_AE[OF rest_sq_leb] leb_zero
            by (simp add: zero_le_power2)
          thus ?thesis
            by (rule AE_mp) (auto simp: power2_eq_square)
        qed
        \<comment> \<open>Step 3: $h(x) = f(x)/\sin(x-a)$ is constant on $(u,v)$.
           For any $\{s..t\} \subseteq (u,v)$, @{term h} is absolutely continuous and $h' = \mathit{rest}/\sin$ a.e.,
           so $h(t) - h(s) = \int_s^t \mathit{rest}/\sin = 0$.\<close>
        have h_const: "f s / sin (s - a) = f t / sin (t-a)"
          if hst: "s \<in> {u<..<v}" "t \<in> {u<..<v}" for s t
        proof (cases "s = t")
          case True thus ?thesis by simp
        next
          case False
          \<comment> \<open>WLOG s < t\<close>
          define s' where "s' = min s t"
          define t' where "t' = max s t"
          have st': "u < s'" "t' < v" "s' < t'"
            using hst False unfolding s'_def t'_def by auto
          have st'_sub: "{s'..t'} \<subseteq> {u<..<v}"
            using st' by auto
          have st'_sub2: "{s'..t'} \<subseteq> {0..2*pi}"
            using st' huv by auto
          \<comment> \<open>$\sin(x - a) \neq 0$ on $\{s'..t'\}$\<close>
          have sin_nz_st: "sin (x - a) \<noteq> 0" if "x \<in> {s'..t'}" for x
            using hsin st'_sub that by auto
          \<comment> \<open>$h = f/\sin$ is absolutely continuous on $\{s'..t'\}$\<close>
          define h where "h \<equiv> \<lambda>x. f x / sin (x - a)"
          have ac_f: "absolutely_continuous_on {0..2*pi} f"
            using absolute_integral_absolutely_continuous_derivative_eq f'abs f'hsd by blast
          have ac_f_st: "absolutely_continuous_on {s'..t'} f"
            using absolutely_continuous_on_subset[OF ac_f st'_sub2] .
          \<comment> \<open>$1/\sin(x-a)$ is absolutely continuous on $\{s'..t'\}$ via a Lipschitz bound\<close>
          have ac_inv_sin: "absolutely_continuous_on {s'..t'} (\<lambda>x. inverse (sin (x - a)))"
          proof -
            \<comment> \<open>The derivative $-\cos/\sin^2$ is bounded on $\{s'..t'\}$ since $\sin$ is bounded away from $0$\<close>
            define deriv where "deriv \<equiv> \<lambda>x::real. - cos (x - a) / (sin (x - a))\<^sup>2"
            have cont_deriv: "continuous_on {s'..t'} deriv"
              unfolding deriv_def
              by (intro continuous_intros) (use sin_nz_st in auto)
            have bdd: "bounded (deriv ` {s'..t'})"
              using compact_continuous_image compact_imp_bounded cont_deriv by blast
            then obtain B where B: "\<And>x. x \<in> {s'..t'} \<Longrightarrow> \<bar>deriv x\<bar> \<le> B"
              by (meson bounded_real imageI)
            have lipschitz: "\<bar>inverse (sin (x - a)) - inverse (sin (y - a))\<bar> \<le> B * \<bar>x - y\<bar>"
              if hx: "s' \<le> x" "x \<le> t'" and hy: "s' \<le> y" "y \<le> t'" for x y
            proof -
              have deriv_at: "((\<lambda>x. inverse (sin (x - a))) has_real_derivative deriv z)
                              (at z within {s'..t'})"
                if hz: "z \<in> {s'..t'}" for z
              proof -
                have snz: "sin (z - a) \<noteq> 0" using sin_nz_st[OF hz] .
                have "((\<lambda>x. sin (x - a)) has_real_derivative cos (z - a))
                       (at z within {s'..t'})"
                  by (intro derivative_eq_intros | simp)+
                moreover have "- (cos (z - a) * inverse (sin (z - a) ^ Suc (Suc 0)))
                              = deriv z"
                  unfolding deriv_def power2_eq_square
                  by (simp add: field_simps)
                ultimately show ?thesis
                  by (metis DERIV_inverse_fun snz)
              qed
              have "norm (inverse (sin (x - a)) - inverse (sin (y - a)))
                    \<le> B * norm (x - y)"
              proof (rule field_differentiable_bound[OF convex_real_interval(5)])
                fix z assume "z \<in> {s'..t'}"
                then show "((\<lambda>x. inverse (sin (x - a))) has_field_derivative deriv z)
                           (at z within {s'..t'})"
                  using deriv_at by auto
              next
                fix z assume "z \<in> {s'..t'}"
                then show "norm (deriv z) \<le> B" using B by (auto simp: abs_le_iff)
              next
                show "x \<in> {s'..t'}" using hx by auto
              next
                show "y \<in> {s'..t'}" using hy by auto
              qed
              then show ?thesis by (simp add: real_norm_def)
            qed
            then show ?thesis
              by (intro Lipschitz_imp_absolutely_continuous strip; auto)
          qed
          \<comment> \<open>$h = f \cdot (1/\sin)$ is AC on $\{s'..t'\}$\<close>
          have ac_h: "absolutely_continuous_on {s'..t'} h"
            using absolutely_continuous_on_mul[OF ac_f_st ac_inv_sin]
            by (simp add: divide_real_def h_def)
          \<comment> \<open>@{term h} has derivative $\mathit{rest}/\sin$ a.e. on $\{s'..t'\}$\<close>
          obtain k where negk: "negligible k"
            and derivf: "\<And>t. t \<in> {0..2*pi} - k \<Longrightarrow>
              ((\<lambda>u. integral {0..u} f') has_vector_derivative f' t)
              (at t within {0..2*pi})"
            using f' has_vector_derivative_indefinite_integral by blast
          have f_eq: "f t = f 0 + integral {0..t} f'" if "t \<in> {0..2*pi}" for t
            using f'hsd[OF that] by (auto simp: has_integral_integrable_integral)
          have fderiv: "(f has_vector_derivative f' t) (at t within {s'..t'})"
            if "t \<in> {s'..t'} - k" for t
          proof -
            have t02: "t \<in> {0..2*pi}" using that st'_sub2 by auto
            have "t \<in> {0..2*pi} - k" using that st'_sub2 by auto
            then have "((\<lambda>u. integral {0..u} f') has_vector_derivative f' t)
                       (at t within {0..2*pi})"
              using derivf by auto
            then have "((\<lambda>u. f u - f 0) has_vector_derivative f' t)
                       (at t within {0..2*pi})"
              using has_vector_derivative_transform_within t02
              by (smt (verit, best) f_eq has_vector_derivative_transform)
            then have "(f has_vector_derivative f' t) (at t within {0..2*pi})"
              using has_vector_derivative_diff_const by blast
            then show ?thesis
              by (rule has_vector_derivative_within_subset) (use st'_sub2 in auto)
          qed
          \<comment> \<open>Derivative of $h = f/\sin$ via the quotient rule\<close>
          have hderiv: "(h has_vector_derivative (f' t * sin (t-a) - f t * cos (t-a)) / (sin (t-a))\<^sup>2)
              (at t within {s'..t'})"
            if "t \<in> {s'..t'} - k" for t
          proof -
            have fd: "(f has_real_derivative f' t) (at t within {s'..t'})"
              using fderiv that by (simp add: has_real_derivative_iff_has_vector_derivative)
            have sd: "((\<lambda>x. sin (x - a)) has_real_derivative cos (t-a))
                      (at t within {s'..t'})"
              by (auto intro!: derivative_eq_intros)
            have "((\<lambda>x. f x / sin (x - a)) has_real_derivative
                   (f' t * sin (t-a) - f t * cos (t-a)) / (sin (t-a))\<^sup>2)
                  (at t within {s'..t'})"
              using DERIV_quotient[OF fd sd] sin_nz_st that
              by (simp add: power2_eq_square algebra_simps)
            then show ?thesis unfolding h_def
              by (simp add: has_real_derivative_iff_has_vector_derivative)
          qed
          \<comment> \<open>The derivative of @{term h} equals $\mathit{rest}/\sin$\<close>
          have hderiv_eq: "(f' t * sin (t-a) - f t * cos (t-a)) / (sin (t-a))\<^sup>2
                          = rest t / sin (t-a)"
            if "t \<in> {s'..t'}" for t
            using that unfolding rest_def fa0
            by (simp add: power2_eq_square divide_simps Multiseries_Expansion.tan_conv_sin_cos)
          have hderiv': "(h has_vector_derivative rest t / sin (t-a))
              (at t within {s'..t'})"
            if "t \<in> {s'..t'} - k" for t
            using hderiv[OF that] hderiv_eq[of t] that by auto
          \<comment> \<open>$\mathit{rest} = 0$ a.e. on $\{u..v\}$, so obtain a negligible set @{term N}\<close>
          obtain N where negN: "negligible N" and restN: "\<And>x. x \<in> {u..v} - N \<Longrightarrow> rest x = 0"
          proof -
            from rest_ae_zero[unfolded eventually_ae_filter[of _ "lebesgue_on {u..v}"]]
            obtain N0 where N0: "N0 \<in> null_sets (lebesgue_on {u..v})"
              and sub: "{x \<in> space (lebesgue_on {u..v}). rest x \<noteq> 0} \<subseteq> N0"
              by auto
            have "negligible N0"
              using null_sets_restrict_space[of "{u..v}"] N0 negligible_iff_null_sets 
              by auto
            moreover have "rest x = 0" if "x \<in> {u..v} - N0" for x
              using sub that by (auto simp: space_lebesgue_on)
            ultimately show ?thesis using that by blast
          qed
          \<comment> \<open>@{term h} has derivative $0$ a.e. on $\{s'..t'\}$\<close>
          have hderiv_zero: "(h has_vector_derivative 0) (at t within {s'..t'})"
            if "t \<in> {s'..t'} - (k \<union> N)" for t
            using restN[of t] that st'_sub hderiv' using st'(2) by fastforce
          have neg_kN: "negligible (k \<union> N)"
            using negk negN by (rule negligible_Un)
          \<comment> \<open>By the FTC for AC functions: $h(t') - h(s') = \int 0 = 0$\<close>
          have "h t' - h s' = integral {s'..t'} (\<lambda>x. 0::real)"
            using fundamental_theorem_of_calculus_absolutely_continuous [OF neg_kN _ ac_h hderiv_zero]
            using st' by auto
          then have "h s' = h t'" by simp
          \<comment> \<open>Translate back to $f/\sin$\<close>
          then show ?thesis
            unfolding h_def s'_def t'_def by (auto split: if_splits)
        qed
        obtain x where "x \<in> {u<..<v}"
          using huv(2) dense by (metis greaterThanLessThan_iff)
        with eq_divide_eq hsin h_const that show ?thesis
          by metis
      qed
      then obtain c where hc: "\<forall>x\<in>{u<..<v}. f x = c * sin (x - a)"
        by auto
      \<comment> \<open>Extend to the closed interval by continuity.\<close>
      have "f x = c * sin (x - a)" if "x \<in> {u..v}" for x
      proof -
        have "f x - c * sin (x - a) = 0"
        proof (rule continuous_constant_on_closure[of "{u<..<v}" "\<lambda>x. f x - c * sin (x - a)" 0])
          show "continuous_on (closure {u<..<v}) (\<lambda>x. f x - c * sin (x - a))"
            unfolding closure_greaterThanLessThan[OF huv(2)]
            by (intro continuous_intros continuous_on_subset[OF contf])
               (use huv in auto)
          show "\<And>y. y \<in> {u<..<v} \<Longrightarrow> f y - c * sin (y - a) = 0"
            using hc by simp
          show "x \<in> closure {u<..<v}"
            unfolding closure_greaterThanLessThan[OF huv(2)] using that by auto
        qed
        thus ?thesis by simp
      qed
      thus ?thesis by auto
    qed
    show ?thesis
    proof (cases "a=0")
      case True
      then show ?thesis
      proof -
        obtain c1 where c1: "\<forall>x\<in>{0..pi}. f x = c1 * sin (x - a)"
          using key_fact[of 0 pi] sin_nz_2 True pi_gt_zero by auto
        obtain c2 where c2: "\<forall>x\<in>{pi..2*pi}. f x = c2 * sin (x - a)"
          using key_fact[of pi "2*pi"] sin_nz_1 True pi_gt_zero by auto
        \<comment> \<open>Use $\int f = 0$ and \<open>csin_integral\<close> to show $c_1 = c_2$.\<close>
        have eq1: "integral {0..pi} f = c1 * (cos (0 - a) - cos (pi - a))"
          by (metis (lifting) integral_cong True add_0 api_le c1 csin_integral)
        have eq2: "integral {pi..2*pi} f = c2 * (cos (pi - a) - cos (2*pi - a))"
          by (metis (lifting) integral_cong True add_0 api_le2 c2 csin_integral)
        have int_split: "integral {0..2*pi} f = integral {0..pi} f + integral {pi..2*pi} f"
            using Henstock_Kurzweil_Integration.integral_combine[OF pi_ge_zero]
            by (metis True add_cancel_left_left api_le2 assms(3) integrable_on_def)
        have "integral {0..2*pi} f = 0"
          using f0 by (simp add: has_integral_integrable_integral)
        hence "c1 * (cos (0 - a) - cos (pi - a)) + c2 * (cos (pi - a) - cos (2*pi - a)) = 0"
          using int_split eq1 eq2 by linarith
        hence "c1 = c2" using True
          by (simp add: cos_two_pi cos_pi)
        then show ?thesis
          by (metis atLeastAtMost_iff c1 c2 nle_le)
      qed
    next
      case False
      then show ?thesis
      proof -
        have a_pos: "0 < a" using \<open>0 \<le> a\<close> False by auto
        \<comment> \<open>Three intervals where $\sin(x-a) \neq 0$\<close>
        obtain c1 where c1: "\<forall>x\<in>{0..a}. f x = c1 * sin (x - a)"
          using key_fact[of 0 a] sin_nz_3 a_pos \<open>a < pi\<close> by auto
        obtain c2 where c2: "\<forall>x\<in>{a..a+pi}. f x = c2 * sin (x - a)"
          using key_fact[of a "a+pi"] sin_nz_2 a_pos \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
        obtain c3 where c3: "\<forall>x\<in>{a+pi..2*pi}. f x = c3 * sin (x - a)"
          using key_fact[of "a+pi" "2*pi"] sin_nz_1 \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
        \<comment> \<open>Show $c_1 = c_3$ using $f(2\pi) = f(0)$\<close>
        have sin_a_nz: "sin a \<noteq> 0"
          using sin_gt_zero[OF a_pos \<open>a < pi\<close>] by (simp add: less_imp_le)
        have f0_eq: "f 0 = c1 * sin (0 - a)"
          using c1 \<open>0 \<le> a\<close> by auto
        have f2pi_eq: "f (2*pi) = c3 * sin (2*pi - a)"
          using c3 \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
        \<comment> \<open>Compute integrals on each interval\<close>
        have eq1: "integral {0..a} f = c1 * (cos (0 - a) - cos (a - a))"
          by (metis (no_types, lifting) integral_cong \<open>0 \<le> a\<close> c1 csin_integral)
        have eq2: "integral {a..a+pi} f = c2 * (cos (a - a) - cos ((a+pi) - a))"
          by (metis (no_types, lifting) api_le integral_cong c2 csin_integral)
        have eq3: "integral {a+pi..2*pi} f = c3 * (cos ((a+pi) - a) - cos (2*pi - a))"
          by (metis (mono_tags, lifting) integral_cong api_le2 c3 csin_integral)
        \<comment> \<open>Split the integral into three parts\<close>
        have f_int: "f integrable_on {0..2*pi}"
          using f0 has_integral_integrable by blast
        have a_le: "a \<le> a + pi" using pi_gt_zero by linarith
        have api_le: "a + pi \<le> 2 * pi" using \<open>a < pi\<close> by linarith
        have a_le_2pi: "a \<le> 2 * pi" using a_pos \<open>a < pi\<close> by linarith
        have int_split: "integral {0..2*pi} f =
          integral {0..a} f + integral {a..a+pi} f + integral {a+pi..2*pi} f"
        proof -
          have "integral {0..2*pi} f = integral {0..a+pi} f + integral {a+pi..2*pi} f"
            using Henstock_Kurzweil_Integration.integral_combine [OF _ api_le f_int] 
                  a_pos pi_gt_zero by auto
          moreover have "f integrable_on {0..a+pi}"
            using integrable_subinterval_real[OF f_int] a_pos api_le by auto
          ultimately show ?thesis
            by (metis Henstock_Kurzweil_Integration.integral_combine \<open>0 \<le> a\<close> a_le)
        qed
        \<comment> \<open>Use $\int f = 0$ to show $c_1 = c_2$\<close>
        have "integral {0..2*pi} f = 0"
          using f0 by (simp add: has_integral_integrable_integral)
        hence sum_eq: "c1 * (cos (0 - a) - cos (a - a)) + c2 * (cos (a - a) - cos ((a+pi) - a)) +
          c3 * (cos ((a+pi) - a) - cos (2*pi - a)) = 0"
          using int_split eq1 eq2 eq3 by linarith
        have "c1 * (cos a - 1) + 2 * c2 + c1 * (- 1 - cos a) = 0"
          using f0_eq f2pi_eq feq sin_a_nz sum_eq by fastforce
        hence c12_eq: "c1 = c2"
          by (simp add: algebra_simps)
        show "\<exists>c a. \<forall>x\<in>{0..2 * pi}. f x = c * sin (x - a)"
          using f0_eq feq sin_a_nz c1 c2 c3 c12_eq by fastforce
      qed
    qed
  qed
qed

theorem scaled_Wirtinger_inequality:
  fixes f f' :: "real \<Rightarrow> real"
  assumes f': "\<And>x. x \<in> {0..1} \<Longrightarrow> (f' has_integral (f x - f 0)) {0..x}"
    and "f 1 = f 0"
    and f_int: "(f has_integral 0) {0..1}"
    and f'_int: "(\<lambda>x. (f' x)\<^sup>2) integrable_on {0..1}"
  shows "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..1}"
    and "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) \<le> integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    and "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2) \<Longrightarrow>
      \<exists>c a. \<forall>x \<in> {0..1}. f x = c * sin (2*pi*x - a)"
proof -
  define g where "g \<equiv> \<lambda>x. f (x / (2*pi))"
  define g' where "g' \<equiv> \<lambda>x. (1/(2*pi)) * f' (x / (2*pi))"
  have twopi_pos: "2 * pi > 0" and twopi_nz: "2 * pi \<noteq> 0"
    and inv_twopi_pos: "1/(2*pi) > 0" and inv_twopi_nz: "1/(2*pi) \<noteq> (0::real)"
    using pi_gt_zero by auto
  have img: "(\<lambda>x. x / (1/(2*pi))) ` {0..1} = {0..2*pi}"
    using image_divide_atLeastAtMost[OF inv_twopi_pos] by simp
  have prec1: "\<And>x. x \<in> {0..2*pi} \<Longrightarrow> (g' has_integral (g x - g 0)) {0..x}"
  proof -
    fix x :: real assume x: "x \<in> {0..2*pi}"
    have *: "((\<lambda>s. f' (1/(2*pi) * s)) has_integral (2*pi) *\<^sub>R (f (x/(2*pi)) - f 0))
                 ((\<lambda>s. s / (1/(2*pi))) ` {0..x/(2*pi)})"
      using x has_integral_stretch_real[OF f' inv_twopi_nz] inv_twopi_pos by simp
    have **: "((\<lambda>s. f' (s/(2*pi))) has_integral (2*pi) * (f (x/(2*pi)) - f 0)) {0..x}"
      using * image_divide_atLeastAtMost[OF inv_twopi_pos, of 0 "x/(2*pi)"]
      using twopi_pos by (simp add: field_simps)
    have val: "1/(2*pi) * ((2*pi) * (f (x/(2*pi)) - f 0)) = f (x/(2*pi)) - f 0"
      using twopi_nz by simp
    show "(g' has_integral (g x - g 0)) {0..x}"
      using has_integral_mult_right[OF **, of "1/(2*pi)"] twopi_nz 
      unfolding g'_def g_def val by (simp add: field_simps)
  qed
  have prec2: "g (2*pi) = g 0"
    unfolding g_def using assms(2) by simp
  have prec3: "(g has_integral 0) {0..2*pi}"
    using has_integral_stretch_real_iff[OF inv_twopi_nz, of f 0 0 1]  f_int g_def img by auto
  have int: "(\<lambda>x. (f' (x/(2*pi)))\<^sup>2) integrable_on {0..2*pi}"
    using f'_int integrable_stretch_real[OF _ inv_twopi_nz, of "\<lambda>x. (f' x)\<^sup>2" 0 1] img 
    by (simp add: field_simps)
  then have prec4: "(\<lambda>x. (g' x)\<^sup>2) integrable_on {0..2*pi}"
    unfolding g'_def power_mult_distrib
    using integrable_on_cmult_left[OF int, of "(1/(2*pi))\<^sup>2"] by (simp add: algebra_simps)
  text \<open>Apply unscaled Wirtinger inequality\<close>
  have W1: "(\<lambda>x. (g x)\<^sup>2) integrable_on {0..2*pi}"
    and W2: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2)"
    and W3: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) \<Longrightarrow>
         \<exists>c a. \<forall>x \<in> {0..2*pi}. g x = c * sin (x - a)"
    using Wirtinger_inequality[OF prec1 prec2 prec3 prec4] by auto
  text \<open>Transfer conclusions back to scaled domain\<close>
  have g_unfold: "\<And>x. (g x)\<^sup>2 = (f (1/(2*pi) * x))\<^sup>2"
    unfolding g_def by (simp add: field_simps)
  have g'_unfold: "\<And>x. (g' x)\<^sup>2 = (1/(2*pi))\<^sup>2 * (f' (1/(2*pi) * x))\<^sup>2"
    unfolding g'_def by (simp add: power_mult_distrib field_simps)
  text \<open>Show 1: integrability of $f(x)^2$ on $\{0..1\}$\<close>
  show int_f2: "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..1}"
    using integrable_stretch_real_iff[OF inv_twopi_nz, of "\<lambda>x. (f x)\<^sup>2" 0 1] W1 g_def img by force 
  text \<open>Show 2: the scaled inequality\<close>
  show "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) \<le> integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
  proof -
    have lhs_stretch: "integral ((\<lambda>x. x / (1/(2*pi))) ` {0..1}) (\<lambda>x. (f (1/(2*pi) * x))\<^sup>2)
             = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
      using integral_stretch_real[OF inv_twopi_nz, of 0 1 "\<lambda>x. (f x)\<^sup>2"] by simp
    have lhs_val: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = 2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
      using lhs_stretch img inv_twopi_pos by (simp add: g_unfold)
    have rhs_stretch: "integral ((\<lambda>x. x / (1/(2*pi))) ` {0..1}) (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' (1/(2*pi) * x))\<^sup>2)
             = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2)"
      using integral_stretch_real[OF inv_twopi_nz, of 0 1 "\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2"] by simp
    have factor_out: "integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2) = (1/(2*pi))\<^sup>2 * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      by (simp add: integral_mult_right)
    have "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2)"
      using img rhs_stretch by (simp add: g'_unfold)
    also have "\<dots> = 2*pi * ((1/(2*pi))\<^sup>2 * integral {0..1} (\<lambda>x. (f' x)\<^sup>2))"
      using inv_twopi_pos factor_out by simp
    finally have rhs_val: "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) 
                 = 2*pi * ((1/(2*pi))\<^sup>2 * integral {0..1} (\<lambda>x. (f' x)\<^sup>2))" .
    have rhs_simp: "2*pi * ((1/(2*pi))\<^sup>2 * integral {0..1} (\<lambda>x. (f' x)\<^sup>2))
                  = (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      using twopi_pos by (simp add: power2_eq_square field_simps)
    from W2 lhs_val rhs_val rhs_simp
    have ineq: "2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2) \<le> (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      by linarith
    then have "(2*pi)\<^sup>2 * integral {0..1} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      using twopi_pos by (simp add: power2_eq_square field_simps)
    then show ?thesis
      by (simp add: power_mult_distrib)
  qed
  text \<open>Show 3: the equality case\<close>
  show "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2) \<Longrightarrow>
      \<exists>c a. \<forall>x \<in> {0..1}. f x = c * sin (2*pi*x - a)"
  proof -
    assume eq: "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    have "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
      using img integral_stretch_real[OF inv_twopi_nz, of 0 1 "\<lambda>x. (f x)\<^sup>2"] by (simp add: g_unfold)
    also have "\<dots> = 2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
      using inv_twopi_pos by simp
    finally have lhs: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = 2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2)" .
    have rhs: "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) 
             = (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    proof -
      have "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) 
          = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2)"
        using integral_stretch_real[OF inv_twopi_nz, of 0 1 "\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2"] img 
        by (simp add: g'_unfold)
      also have "\<dots> = (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
        using twopi_pos by (simp add: power2_eq_square field_simps)
      finally show ?thesis .
    qed
    have "(2*pi)\<^sup>2 * integral {0..1} (\<lambda>x. (f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      using eq by (simp add: power_mult_distrib)
    then have "2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2) = (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      using twopi_pos by (simp add: power2_eq_square field_simps)
    then have weq: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2)"
      using lhs rhs by linarith
    from W3[OF weq] obtain c a where ca: "\<forall>x \<in> {0..2*pi}. g x = c * sin (x - a)" by auto
    have "f x = c * sin (2*pi*x - a)" if "x \<in> {0..1}" for x
    proof  -
      have "2*pi*x \<in> {0..2*pi}" using twopi_pos
        using that by auto
      with ca show "f x = c * sin (2*pi*x - a)"
        by (metis g_def nonzero_mult_div_cancel_left twopi_nz)
    qed
    then show "\<exists>c a. \<forall>x \<in> {0..1}. f x = c * sin (2*pi*x - a)" by auto
  qed
qed

section \<open>Part 2: a very special case of Green's theorem for a convex area\<close>

subsection \<open>Area under an arc.\<close>

locale Area =
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex" and u v S
  assumes uv: "u \<le> v"
    and Re_g_le: "Re (g u) \<le> Re (g v)"
    and acont_g: "absolutely_continuous_on {u..v} g"
    and gim: "g ` {u..v} \<subseteq> {z. Im z \<ge> 0}"
    and inj_g: "inj_on g {u..v}"
    and inj_Re: "inj_on Re (g ` {u..v})"
    and negS: "negligible S"
    and gder: "\<And>t. t \<in> {u..v} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"

begin

lemma below_arclet:
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
    and "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
proof -
  obtain h where h: "\<And>x. x \<in> {u..v} \<Longrightarrow> h (Re (g x)) = x"
    by (metis inj_g inj_Re comp_def comp_inj_on inv_into_f_f)
  define ax where "ax \<equiv> (\<lambda>t. Re (g t)) ` {u..v}"
  have cont_h: "continuous_on ax h"
    unfolding ax_def
    by (simp add: absolutely_continuous_on_imp_continuous acont_g continuous_on_Re continuous_on_inv h)
  show "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
  proof -
    have cont_g: "continuous_on {u..v} g"
      by (simp add: absolutely_continuous_on_imp_continuous acont_g)
    have gp_ai: "g' absolutely_integrable_on {u..v}"
      by (meson absolutely_integrable_absolutely_continuous_derivative acont_g gder
          has_vector_derivative_at_within negS)
    have Re_gp_ai: "(\<lambda>t. Re (g' t)) absolutely_integrable_on {u..v}"
      using Re_absolutely_integrable_on gp_ai by blast
    have Im_g_cont: "continuous_on {u..v} (\<lambda>t. Im (g t))"
      by (intro continuous_intros cont_g)
    have Im_g_bdd: "bounded ((\<lambda>t. Im (g t)) ` {u..v})"
      by (intro compact_imp_bounded compact_continuous_image[OF Im_g_cont compact_Icc])
    have Im_g_meas: "(\<lambda>t. Im (g t)) \<in> borel_measurable (lebesgue_on {u..v})"
      using continuous_imp_measurable_on_sets_lebesgue[OF Im_g_cont] atLeastAtMost_borel lborelD
      by (metis sets_completionI_sets)
    show ?thesis
      using absolutely_integrable_bounded_measurable_product_real [OF Im_g_meas _ Im_g_bdd Re_gp_ai]
      by (simp add: mult.commute)
  qed
  have cont_g: "continuous_on {u..v} g"
    using acont_g absolutely_continuous_on_imp_continuous is_interval_cc by blast
  have cont_Reg: "continuous_on {u..v} (\<lambda>t. Re (g t))"
    by (intro continuous_intros cont_g)
  have inj_Reg: "inj_on (\<lambda>t. Re (g t)) {u..v}"
    using comp_inj_on[OF inj_g inj_Re] by (simp add: o_def)
  have ax: "ax = {Re (g u)..Re (g v)}"
  proof (rule antisym)
    show "ax \<subseteq> {Re (g u)..Re (g v)}"
    proof (cases "u = v")
      case False
      with uv 
      have "strict_mono_on {u..v} (\<lambda>t. Re (g t)) \<or> strict_antimono_on {u..v} (\<lambda>t. Re (g t))"
        using injective_eq_monotone_map[OF is_interval_cc cont_Reg] inj_Reg by auto
      with False \<open>u \<le> v\<close> have mono: "strict_mono_on {u..v} (\<lambda>t. Re (g t))"
        by (smt (verit, ccfv_threshold) Re_g_le atLeastAtMost_iff monotone_onD)
      show ?thesis
        using mono by (auto simp: monotone_on_def ax_def less_eq_real_def)
    qed (auto simp: ax_def)
  next
    show "{Re (g u)..Re (g v)} \<subseteq> ax"
      using ivt_increasing_component_on_1[OF uv cont_g, of 1] by (force simp: ax_def)
  qed
  show "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
  proof -
    define f where "f \<equiv> (\<lambda>x. Im (g (h x)))"
    have h_range: "h ` ax \<subseteq> {u..v}"
      using h by (force simp: ax_def)
    have cont_f: "continuous_on ax f"
      using cont_g cont_h continuous_on_Im continuous_on_compose2 f_def h_range by blast
    have f_nonneg: "\<And>x. x \<in> ax \<Longrightarrow> f x \<ge> 0"
      unfolding f_def using gim h_range by blast
    have mono_Reg: "Re (g x) \<le> Re (g y)" if "x \<in> {u..v}" "y \<in> {u..v}" "x \<le> y" for x y
    proof -
      have "strict_mono_on {u..v} (\<lambda>t. Re (g t)) \<or>
            strict_antimono_on {u..v} (\<lambda>t. Re (g t))"
        using injective_eq_monotone_map[OF is_interval_cc cont_Reg] inj_Reg by auto
      with Re_g_le atLeastAtMost_iff leD  order_le_less uv 
      have "mono_on {u..v} (\<lambda>t. Re (g t))"
        unfolding monotone_on_def by metis
      with that show "Re (g x) \<le> Re (g y)" by (auto simp: mono_on_def)
    qed
    have acont_Reg: "absolutely_continuous_on {u..v} (\<lambda>t. Re (g t))"
      using absolutely_continuous_on_compose_linear[OF acont_g bounded_linear_Re[THEN bounded_linear.linear]]
      by (simp add: o_def)
    have deriv_Reg: "\<And>t. t \<in> {u..v} - S \<Longrightarrow> ((\<lambda>t. Re (g t)) has_vector_derivative Re (g' t)) (at t)"
      using bounded_linear_Re[THEN bounded_linear.has_vector_derivative] gder by blast
    \<comment> \<open>Apply substitution: $\int_{Re(g\,u)}^{Re(g\,v)} f = \int_u^v Re(g') \cdot f(Re(g)) = \int_u^v Re(g') \cdot Im(g)$\<close>
    have subst: "((\<lambda>t. Re (g' t) * f (Re (g t))) has_integral (integral {Re (g u)..Re (g v)} f)) {u..v}"
      using has_integral_substitution_ac[OF uv Re_g_le acont_Reg negS deriv_Reg _ mono_Reg] cont_f ax
      using negS by blast
    \<comment> \<open>Since $f(Re(g\,t)) = Im(g\,t)$, the left-hand side simplifies\<close>
    have "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) = integral {Re (g u)..Re (g v)} f"
      using h has_integral_spike[OF negligible_empty _ subst] integral_unique
      by (fastforce simp: f_def)
    \<comment> \<open>Apply area-under-curve: measure of the subgraph $= \int f$\<close>
    also have "\<dots> = measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
    proof -
      \<comment> \<open>First show the subgraph set equals the area under the graph of @{term f}\<close>
      have set_eq: "{z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w} =
                    {z. Re (g u) \<le> Re z \<and> Re z \<le> Re (g v) \<and> 0 \<le> Im z \<and> Im z \<le> f (Re z)}" (is "?L=?R")
      proof (intro antisym subsetI)
        fix z assume "z \<in> ?L"
        then obtain w t where wt: "t \<in> {u..v}" "w = g t" "Re w = Re z" "0 \<le> Im z" "Im z \<le> Im w"
          by auto
        have "Re z \<in> ax" unfolding ax_def using wt by force
        then show "z \<in> ?R"
          using f_def h wt ax by fastforce
      next
        fix z assume z: "z \<in> ?R"
        then have Rez: "Re z \<in> ax" using ax by auto
        then show "z \<in> ?L"
          unfolding ax_def using h z by (fastforce simp: f_def)
      qed
      \<comment> \<open>Then apply area-under-curve (Fubini/Cavalieri)\<close>
      show ?thesis unfolding set_eq
        using has_integral_area_under_curve[OF Re_g_le _ _] cont_f f_nonneg ax
        by (metis (no_types, lifting))
    qed
    finally show ?thesis .
  qed
qed

end

subsection \<open>Area above an arc.\<close>

lemma area_above_arclet:
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
  assumes "u \<le> v"
    and Re_g_ge: "Re (g v) \<le> Re (g u)"
    and ac_g: "absolutely_continuous_on {u..v} g"
    and gim: "g ` {u..v} \<subseteq> {z. Im z \<le> 0}"
    and injg: "inj_on g {u..v}"
    and injRe: "inj_on Re (g ` {u..v})"
    and "negligible S"
    and vder_g: "\<And>t. t \<in> {u..v} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
    and "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
proof -
  \<comment> \<open>Symmetry: define $h(t) = \overline{g(u+v-t)}$ and apply \<open>area_below_arclet\<close>\<close>
  define \<phi> where "\<phi> \<equiv> \<lambda>t. u + v - t"
  define h where "h \<equiv> cnj \<circ> g \<circ> \<phi>"
  define h' where "h' \<equiv> \<lambda>t. - cnj (g' (\<phi> t))"
  interpret Area h h' u v "\<phi> ` S"
  proof
    show "u \<le> v"
      by fact
    show "Re (h u) \<le> Re (h v)"
      by (simp add: \<phi>_def Re_g_ge h_def)
    show "absolutely_continuous_on {u..v} h"
      by (simp add: \<phi>_def absolutely_continuous_on_compose_linear absolutely_continuous_on_reflect assms(3)
          h_def linear_cnj)
    show "h ` {u..v} \<subseteq> {z. 0 \<le> Im z}"
      using gim by (auto simp: h_def \<phi>_def image_subset_iff)
    show "inj_on h {u..v}"
      using injg by (fastforce simp: inj_on_def h_def \<phi>_def)
    show "inj_on Re (h ` {u..v})"
      using injRe by (fastforce simp: inj_on_def h_def \<phi>_def)
    have "\<phi> ` S = (+) (u + v) ` (uminus ` S)"
      unfolding \<phi>_def image_image by (simp add: algebra_simps)
    then show "negligible (\<phi> ` S)"
      by (simp add: \<open>negligible S\<close> linear_uminus negligible_linear_image negligible_translation)
    show "\<And>t. t \<in> {u..v} - (\<phi>`S) \<Longrightarrow> (h has_vector_derivative h' t) (at t)"
      unfolding has_vector_derivative_def h_def h'_def \<phi>_def 
      by (rule vder_g [unfolded has_vector_derivative_def] derivative_eq_intros | force)+
  qed
  have integrand_eq: "\<And>t. Re (h' t) * Im (h t) = Re (g' (\<phi> t)) * Im (g (\<phi> t))"
    unfolding h_def h'_def by (simp add: o_def cnj.sel)
  have integral_eq: "integral {u..v} (\<lambda>t. Re (g' (\<phi> t)) * Im (g (\<phi> t))) =
                     integral {u..v} (\<lambda>t. Re (g' t) * Im (g t))"
  proof -
    define f where "f \<equiv> \<lambda>t. Re (g' t) * Im (g t)"
    have comp_eq: "(f \<circ> (+) (u + v)) \<circ> uminus = f \<circ> \<phi>"
      unfolding \<phi>_def comp_def by (simp add: algebra_simps)
    have "(f \<circ> \<phi>) absolutely_integrable_on {u..v}"
      using below_arclet(1) f_def integrand_eq set_integrable_cong by fastforce
    then have "integral {u..v} (f \<circ> \<phi>) = integral (uminus ` {u..v}) (f \<circ> (+) (u + v))"
      by (subst integral_change_of_variables_linear[OF linear_uminus]) (auto simp: comp_eq)
    also have "\<dots> = integral {u..v} f"
      using integral_shift_Icc_real[of "-v" "-u" f "u+v"] by (simp add: algebra_simps)
    finally show ?thesis 
      by (simp add: f_def comp_def)
  qed
  show "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
  proof -
    have Re_gp_ai: "(\<lambda>t. Re (g' t)) absolutely_integrable_on {u..v}"
      using Re_absolutely_integrable_on has_vector_derivative_at_within assms
      by (metis vder_g absolutely_integrable_absolutely_continuous_derivative)
    have Im_g_cont: "continuous_on {u..v} (\<lambda>t. Im (g t))"
      by (simp add: absolutely_continuous_on_imp_continuous assms(3) continuous_on_Im)
    have Im_g_bdd: "bounded ((\<lambda>t. Im (g t)) ` {u..v})"
      by (intro compact_imp_bounded compact_continuous_image[OF Im_g_cont compact_Icc])
    have Im_g_meas: "(\<lambda>t. Im (g t)) \<in> borel_measurable (lebesgue_on {u..v})"
      using Im_g_cont integrable_continuous_real integrable_imp_measurable by blast
    show ?thesis
      using absolutely_integrable_bounded_measurable_product_real [OF Im_g_meas _ Im_g_bdd Re_gp_ai]
      by (simp add: mult.commute)
  qed
  have measure_eq: "measure lebesgue {z. \<exists>w \<in> h ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w} =
                    measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
  proof -
    have \<phi>_image: "\<phi> ` {u..v} = {u..v}"
      using assms(1) unfolding \<phi>_def by (auto simp: image_iff)
    have h_image: "h ` {u..v} = cnj ` (g ` {u..v})"
      by (metis \<phi>_image h_def image_comp)
    define A where "A \<equiv> {z. \<exists>w \<in> h ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
    define B where "B \<equiv> {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
    have AB: "A = cnj ` B"
      unfolding A_def h_image B_def by (force simp: in_image_cnj_iff)
    have cont_g_uv: "continuous_on {u..v} g"
      using assms(3) absolutely_continuous_on_imp_continuous is_interval_cc by blast
    have "compact B"
    proof -
      \<comment> \<open>@{term B} is the continuous image of the compact set @{term "{u..v} \<times> {0..1}"}\<close>
      define \<psi> where "\<psi> \<equiv> \<lambda>(t,s). Complex (Re (g t)) ((1 - s) * Im (g t))"
      have cont_\<psi>: "continuous_on ({u..v} \<times> {0..1}) \<psi>"
        unfolding \<psi>_def split_def
        by (intro continuous_intros continuous_on_compose2[OF continuous_on_Re[OF cont_g_uv]]
            continuous_on_compose2[OF continuous_on_Im[OF cont_g_uv]] continuous_on_fst) auto
      have img: "\<psi> ` ({u..v} \<times> {0..1}) = B"
      proof (rule set_eqI)
        fix z :: complex
        show "z \<in> \<psi> ` ({u..v} \<times> {0..1}) \<longleftrightarrow> z \<in> B"
        proof
          assume "z \<in> \<psi> ` ({u..v} \<times> {0..1})"
          then obtain t s where ts: "t \<in> {u..v}" "s \<in> {0..1}" 
            "z = Complex (Re (g t)) ((1 - s) * Im (g t))"
            unfolding \<psi>_def by auto
          have Im_le: "Im (g t) \<le> 0"
            using assms(4) ts(1) by (auto simp: image_subset_iff)
          have "g t \<in> g ` {u..v}" using ts(1) by auto
          moreover have "Im (g t) \<le> Im z"
            using ts Im_le mult_right_mono_neg by (simp add: mult_le_cancel_right1)
          moreover have "Im z \<le> 0"
            using ts Im_le mult_nonneg_nonpos[of "1-s" "Im (g t)"] by auto
          ultimately show "z \<in> B" unfolding B_def using ts by auto
        next
          assume "z \<in> B"
          then obtain w t where wt: "t \<in> {u..v}" "w = g t" "Re w = Re z" "Im w \<le> Im z" "Im z \<le> 0"
            unfolding B_def by auto
          show "z \<in> \<psi> ` ({u..v} \<times> {0..1})"
          proof (cases "Im (g t) = 0")
            case True
            then show ?thesis 
              using wt by (force simp: image_iff \<psi>_def complex_eq_iff)
          next
            case False
            then have neg: "Im (g t) < 0"
              using wt by force
            define s where "s \<equiv> 1 - Im z / Im (g t)"
            have "0 \<le> Im z / Im (g t)" 
              using wt(5) neg by (simp add: field_simps)
            then have "s \<in> {0..1}" 
              using neg s_def wt(2,4) by force
            moreover have "z = \<psi> (t, s)" unfolding \<psi>_def s_def
              using wt(2,3) False by (simp add: complex_eq_iff field_simps)
            ultimately show ?thesis using wt(1) by auto
          qed
        qed
      qed
      then show ?thesis
        using img compact_continuous_image[OF cont_\<psi>] by (simp add: compact_Times)
    qed
    then have B_meas: "B \<in> lmeasurable" using lmeasurable_compact by blast    
    show ?thesis
      using AB measure_linear_image[OF linear_cnj B_meas] det_complex
      by (simp add: A_def B_def)
  qed
  show "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
    using below_arclet(2) integrand_eq integral_eq measure_eq by (simp add: o_def)
qed

subsection \<open>Lemmas for Green's theorem\<close>

definition Green_concl :: "(real \<Rightarrow> complex) \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> bool" where
  "Green_concl g g' \<equiv> (\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {0..1}
    \<and> \<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> = measure lebesgue (inside (path_image g))"

text \<open>At most two points on the frontier of a $2$-dimensional convex body can share the same
  inner product with a non-zero vector. Consequence: if three distinct points
  on the frontier have the same @{term Re} (or @{term Im}), the body must lie on one side.\<close>
lemma frontier_vertical_at_most_two:
  fixes S :: "complex set" and c :: real
  assumes "convex S" "compact S" "interior S \<noteq> {}"
    and sides: "\<exists>p \<in> S. Re p < c" "\<exists>q \<in> S. c < Re q"
    and xyz: "x \<in> frontier S" "y \<in> frontier S" "z \<in> frontier S"
      "Re x = c" "Re y = c" "Re z = c"
  shows "\<not> (x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z)"
proof -
  define T where "T \<equiv> {w :: complex. 1 \<bullet> w = c}"
  have aff_T: "affine T" unfolding T_def by (rule affine_hyperplane)
  have T_eq: "T = {w. Re w = c}" unfolding T_def by (simp add: complex_inner_1)
  have xT: "x \<in> T" "y \<in> T" "z \<in> T"
    using xyz unfolding T_eq by auto
  \<comment> \<open>The interior of @{term S} intersects @{term T}\<close>
  have int_T: "interior S \<inter> T \<noteq> {}"
  proof -
    have cl: "closed S" using assms(2) compact_imp_closed by blast
    have cl_int: "closure (interior S) = S"
      using convex_closure_interior[OF assms(1) assms(3)] cl
      by (simp add: closure_closed)
    \<comment> \<open>Find interior points on each side of $Re = c$\<close>
    obtain p where p: "p \<in> interior S" "Re p < c"
    proof -
      obtain p0 where p0: "p0 \<in> S" "Re p0 < c" using sides(1) by auto
      then have "p0 \<in> closure (interior S)" using cl_int by simp
      then obtain ps where ps: "\<forall>n. ps n \<in> interior S" "ps \<longlonglongrightarrow> p0"
        by (meson closure_sequential)
      have "(\<lambda>n. Re (ps n)) \<longlonglongrightarrow> Re p0" by (rule tendsto_Re[OF ps(2)])
      from order_tendstoD(2)[OF this p0(2)]
      obtain n where "Re (ps n) < c" using eventually_sequentially by auto
      then show thesis using that ps(1) by auto
    qed
    obtain q where q: "q \<in> interior S" "c < Re q"
    proof -
      obtain q0 where q0: "q0 \<in> S" "c < Re q0" using sides(2) by auto
      then have "q0 \<in> closure (interior S)" using cl_int by simp
      then obtain qs where qs: "\<forall>n. qs n \<in> interior S" "qs \<longlonglongrightarrow> q0"
        by (meson closure_sequential)
      have "(\<lambda>n. Re (qs n)) \<longlonglongrightarrow> Re q0" by (rule tendsto_Re[OF qs(2)])
      from order_tendstoD(1)[OF this q0(2)]
      obtain n where "c < Re (qs n)" using eventually_sequentially by auto
      then show thesis using that qs(1) by auto
    qed
    \<comment> \<open>IVT on the segment $\{p..q\} \subseteq \mathit{interior}\ S$\<close>
    have conv_int: "convex (interior S)" using convex_interior assms(1) by auto
    then have seg_sub: "closed_segment p q \<subseteq> interior S"
      using closed_segment_subset p(1) q(1) by auto
    obtain r where "r \<in> closed_segment p q" "Re r = c"
    proof -
      have "1 \<bullet> p \<le> c" using p(2) by (simp add: complex_inner_1)
      moreover have "c \<le> 1 \<bullet> q" using q(2) by (simp add: complex_inner_1)
      moreover have "p \<in> closed_segment p q" "q \<in> closed_segment p q"
        by (auto simp: ends_in_segment)
      ultimately obtain r where "r \<in> closed_segment p q" "1 \<bullet> r = c"
        using connected_ivt_hyperplane[OF connected_segment] by blast
      then show thesis using that by (simp add: complex_inner_1)
    qed
    then have "r \<in> interior S \<inter> T" using seg_sub T_eq by auto
    then show ?thesis by auto
  qed

  \<comment> \<open>Apply \<open>convex_affine_rel_frontier_Int\<close>\<close>
  have rf_eq: "rel_frontier (S \<inter> T) = frontier S \<inter> T"
    using convex_affine_rel_frontier_Int[OF assms(1) aff_T int_T] .
  \<comment> \<open>@{term "S \<inter> T"} is a compact convex collinear set, hence a closed segment\<close>
  have ST_ne: "S \<inter> T \<noteq> {}"
    using int_T interior_subset by blast
  have ST_compact: "compact (S \<inter> T)"
  proof -
    have "closed T" unfolding T_def by (rule closed_hyperplane)
    then show ?thesis using assms(2) compact_Int_closed by auto
  qed
  have ST_convex: "convex (S \<inter> T)"
    using assms(1) convex_Int aff_T affine_imp_convex by auto
  have ST_collinear: "collinear (S \<inter> T)"
  proof -
    have "aff_dim T = int (DIM(complex) - 1)"
      unfolding T_def by (rule aff_dim_hyperplane) simp
    then have "aff_dim T = 1" by simp
    moreover have "aff_dim (S \<inter> T) \<le> aff_dim T"
      by (rule aff_dim_subset) auto
    ultimately have "aff_dim (S \<inter> T) \<le> 1" by linarith
    then show ?thesis using collinear_aff_dim by auto
  qed
  obtain p q where pq: "S \<inter> T = closed_segment p q"
    using compact_convex_collinear_segment[OF ST_ne ST_compact ST_convex ST_collinear] by auto
  \<comment> \<open>The @{term rel_frontier} of a closed segment has at most two elements\<close>
  have rf_sub: "rel_frontier (S \<inter> T) \<subseteq> {p, q}"
  proof (cases "p = q")
    case True
    then show ?thesis unfolding pq by (simp add: rel_frontier_sing)
  next
    case False
    have "rel_frontier (closed_segment p q) = closed_segment p q - rel_interior (closed_segment p q)"
      unfolding rel_frontier_def by (simp add: closure_closed_segment)
    also have "\<dots> = closed_segment p q - open_segment p q"
      using rel_interior_closed_segment[of p q] False by simp
    also have "\<dots> = {p, q}"
    proof -
      have "closed_segment p q = open_segment p q \<union> {p, q}"
        by (rule closed_segment_eq_open)
      moreover have "p \<notin> open_segment p q" "q \<notin> open_segment p q"
        by (simp_all add: open_segment_def)
      ultimately show ?thesis by auto
    qed
    finally show ?thesis using pq by simp
  qed
  \<comment> \<open>@{term x}, @{term y}, @{term z} all lie in @{term "rel_frontier (S \<inter> T)"} $=$ @{term "frontier S \<inter> T"} $\subseteq \{p, q\}$\<close>
  have "x \<in> {p, q}" "y \<in> {p, q}" "z \<in> {p, q}"
    using xyz(1,2,3) xT rf_eq rf_sub by auto
  then show ?thesis by auto
qed


locale Green =
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
    and U :: "real set"
    and a b :: "complex"
  assumes g: "simple_path g" "pathstart g = a" "pathfinish g = a"
    and b: "b \<in> path_image g" "Re a < Re b" "Im a = Im b"
    and dab: "dist a b = diameter (path_image g)"
    and conv: "convex (inside (path_image g))"
    and cont: "absolutely_continuous_on {0..1} g"
    and U: "negligible U"
    and vder: "\<And>t. t \<in> {0..1} - U \<Longrightarrow> (g has_vector_derivative g' t) (at t)"

begin

definition "gop \<equiv> cnj \<circ> reversepath g"
definition "gop' \<equiv> uminus \<circ> cnj \<circ> reversepath g'"

lemma cnj_rev: "Green gop gop' ((\<lambda>t. 1-t) ` U) (cnj a) (cnj b)"
proof
  show "simple_path gop"
    using g by (simp add: simple_path_def gop_def loop_free_reversepath loop_free_cnj)
  show "pathstart gop = cnj a"
    using g by (simp add: gop_def pathstart_compose)
  show "pathfinish gop = cnj a"
    using g by (simp add: gop_def pathfinish_compose)
  show "cnj b \<in> path_image gop"
    using b by (simp add: gop_def path_image_compose)
  show "Re (cnj a) < Re (cnj b)" "Im (cnj a) = Im (cnj b)"
    using b by auto
  show "dist (cnj a) (cnj b) = diameter (path_image gop)"
    by (simp add: gop_def dab diameter_image_cnj path_image_compose flip: dab)
  show "convex (inside (path_image gop))"
    unfolding gop_def
    by (metis conv convex_linear_vimage image_cnj_conv_vimage_cnj 
        inside_cnj_image linear_cnj path_image_compose path_image_reversepath)
  show "absolutely_continuous_on {0..1} gop"
    using cont unfolding gop_def
    by (simp add: absolutely_continuous_on_compose_linear absolutely_continuous_on_reflect linear_cnj
        reversepath_o)
  have "negligible (uminus ` U)"
    by (simp add: U linear_uminus negligible_linear_image_eq)
  then have "negligible (((+)1) ` uminus ` U)"
    using negligible_translation by blast
  then show "negligible ((-) 1 ` U)"
    by (smt (verit, best) image_cong image_image)
next
  fix t :: real
  note vder [unfolded has_vector_derivative_def, derivative_intros]
  assume "t \<in> {0..1} - (-) 1 ` U"
  then have "0 \<le> t" "t \<le> 1" "1-t \<notin> U"
    by (auto simp: image_iff)
  then show "(gop has_vector_derivative gop' t) (at t)"
    unfolding gop_def gop'_def has_vector_derivative_def reversepath_o
    by - (rule derivative_eq_intros | simp add: o_def | assumption)+
qed

lemma rev: "Green (reversepath g) (uminus \<circ> reversepath g') ((\<lambda>t. 1-t) ` U) a b"
proof
  show "simple_path (reversepath g)"
    using g by (simp add: simple_path_def loop_free_reversepath)
  show "pathstart (reversepath g) = a"
    using g by (simp add: pathstart_compose)
  show "pathfinish (reversepath g) = a"
    using g by (simp add: pathfinish_compose)
  show "b \<in> path_image (reversepath g)"
    using b by (simp add: path_image_compose)
  show "Re a < Re b" "Im a = Im b"
    using b by auto
  show "dist a b = diameter (path_image (reversepath g))"
    by (simp add: gop_def dab path_image_compose flip: dab)
  show "convex (inside (path_image (reversepath g)))"
    unfolding gop_def
    by (metis conv convex_linear_vimage image_cnj_conv_vimage_cnj 
        inside_cnj_image linear_cnj path_image_compose path_image_reversepath)
  show "absolutely_continuous_on {0..1} (reversepath g)"
    using cont unfolding gop_def
    by (simp add: absolutely_continuous_on_compose_linear absolutely_continuous_on_reflect linear_cnj
        reversepath_o)
  have "negligible (uminus ` U)"
    by (simp add: U linear_uminus negligible_linear_image_eq)
  then have "negligible (((+)1) ` uminus ` U)"
    using negligible_translation by blast
  then show "negligible ((-) 1 ` U)"
    by (smt (verit, best) image_cong image_image)
next
  fix t :: real
  note vder [unfolded has_vector_derivative_def, derivative_intros]
  assume "t \<in> {0..1} - (-) 1 ` U"
  then have "0 \<le> t" "t \<le> 1" "1-t \<notin> U"
    by (auto simp: image_iff)
  then show "((reversepath g) has_vector_derivative (uminus \<circ> reversepath g') t) (at t)"
    unfolding gop_def gop'_def has_vector_derivative_def reversepath_o
    by - (rule derivative_eq_intros | simp add: o_def | assumption)+
qed


lemma f_abs_int: "(\<lambda>s. Re (g' s) * Im (g s)) absolutely_integrable_on {0..1}"
proof -
  have cont_g: "continuous_on {0..1} g"
    using simple_path_imp_path[OF g(1)] by (simp add: path_def)
  have Im_g_cont: "continuous_on {0..1} (\<lambda>t. Im (g t))"
    by (intro continuous_intros cont_g)
  have Im_g_bdd: "bounded ((\<lambda>t. Im (g t)) ` {0..1})"
    by (intro compact_imp_bounded compact_continuous_image[OF Im_g_cont compact_Icc])
  have Im_g_meas: "(\<lambda>t. Im (g t)) \<in> borel_measurable (lebesgue_on {0..1})"
    using continuous_imp_measurable_on_sets_lebesgue[OF Im_g_cont]
      atLeastAtMost_borel lborelD
    by (metis sets_completionI_sets)
  have gp_ai: "g' absolutely_integrable_on {0..1}"
    using absolutely_integrable_absolutely_continuous_derivative[OF cont U]
      vder has_vector_derivative_at_within by blast
  then show ?thesis
    using absolutely_integrable_bounded_measurable_product_real[OF Im_g_meas _ Im_g_bdd Re_absolutely_integrable_on]
    by (simp add: mult.commute)
qed

lemma arc_inj_on: "inj_on g {u..v}"
  if huv: "0 \<le> u" "v \<le> 1" "u < v" and hne: "u > 0 \<or> v < 1" 
proof (rule inj_onI)
  fix s1 s2 assume s1: "s1 \<in> {u..v}" and s2: "s2 \<in> {u..v}" and eq: "g s1 = g s2"
  have s1_01: "s1 \<in> {0..1}" using s1 huv by auto
  have s2_01: "s2 \<in> {0..1}" using s2 huv by auto
  show "s1 = s2"
  proof (rule ccontr)
    assume neq: "s1 \<noteq> s2"
    from g(1) have lf: "loop_free g" by (simp add: simple_path_def)
    have "s1 = s2 \<or> s1 = 0 \<and> s2 = 1 \<or> s1 = 1 \<and> s2 = 0"
      using eq lf loop_free_def s1_01 s2_01 by blast
    with neq show False using s1 s2 huv hne by auto
  qed
qed

lemma arc_Re_inj_on: "inj_on Re (g ` {u..v})"
  if hinj: "inj_on g {u..v}"
    and hRe: "\<And>s1 s2. \<lbrakk>s1 \<in> {u..v}; s2 \<in> {u..v}; Re (g s1) = Re (g s2); s1 \<noteq> s2\<rbrakk>
               \<Longrightarrow> Re (g u) = Re (g v)"
    and hne: "Re (g u) \<noteq> Re (g v)"
proof (rule inj_onI)
  fix x y assume "x \<in> g ` {u..v}" "y \<in> g ` {u..v}" "Re x = Re y"
  then obtain s1 s2 where s1: "s1 \<in> {u..v}" "x = g s1"
    and s2: "s2 \<in> {u..v}" "y = g s2" by auto
  then have Re_eq: "Re (g s1) = Re (g s2)" using \<open>Re x = Re y\<close> by simp
  show "x = y"
  proof (cases "s1 = s2")
    case True then show ?thesis using s1 s2 by simp
  next
    case False
    then have "Re (g u) = Re (g v)" using hRe[OF s1(1) s2(1) Re_eq] by auto
    then show ?thesis using hne by simp
  qed
qed

lemma Re_inj_upper_gen: 
  assumes s1t: "s1 \<in> {0..t}" and s2t: "s2 \<in> {0..t}"
    and Re_eq: "Re (g s1) = Re (g s2)" and neq: "s1 \<noteq> s2"
    and geq0: "g 0 = 0" "g 1 = 0"
    and ht: "0 < t" "t < 1" "g t = b"
  shows "(s1 = 0 \<and> s2 = t) \<or> (s1 = t \<and> s2 = 0)"
proof (rule ccontr)
  assume not_endpts: "\<not> ((s1 = 0 \<and> s2 = t) \<or> (s1 = t \<and> s2 = 0))"
    \<comment> \<open>Define @{term "S \<equiv> convex hull (path_image g)"}. This is the right set for
       \<open>frontier_vertical_at_most_two\<close>.\<close>
  define S where "S \<equiv> convex hull (path_image g)"
  have S_convex: "convex S" unfolding S_def by (rule convex_convex_hull)
  have S_compact: "compact S" unfolding S_def
    using compact_simple_path_image[OF g(1)] compact_convex_hull by auto
  have frontier_S: "frontier S = path_image g"
    unfolding S_def using frontier_convex_hull_eq_path_image[OF g(1) _ conv] g(2,3) by auto
  have S_int_ne: "interior S \<noteq> {}"
  proof -
    have "inside (path_image g) \<noteq> {}"
      using Jordan_inside_outside[OF g(1)] g(2,3) by auto
    moreover have "closure (inside (path_image g)) = S"
      unfolding S_def using convex_hull_eq_closure_inside[OF g(1) _ conv] g(2,3) by auto
    moreover have "interior (closure (inside (path_image g))) = inside (path_image g)"
      using convex_interior_closure[OF conv] interior_open
      using Jordan_inside_outside[OF g(1)] g(2,3) by auto
    ultimately show ?thesis by auto
  qed
    \<comment> \<open>Step 1: At least one of $s_1$, $s_2$ is in the open interval $(0,t)$.\<close>
  have interior_param: "s1 \<in> {0<..<t} \<or> s2 \<in> {0<..<t}"
    using s1t s2t neq not_endpts by auto
      \<comment> \<open>Step 2: $g\,s_1 \neq g\,s_2$ (from injectivity of @{term g} on $\{0..t\}$, which is a proper sub-arc).\<close>
  have inj_sub: "inj_on g {0..t}"
    using arc_inj_on[of 0 t] ht by auto
  have g_neq: "g s1 \<noteq> g s2"
    by (meson neq inj_on_def inj_sub s1t s2t)
    \<comment> \<open>Step 3: Both $g\,s_1$ and $g\,s_2$ are on @{term "frontier S"} $=$ @{term "path_image g"}.\<close>
  have s1_01: "s1 \<in> {0..1}" using s1t ht(2) by auto
  have s2_01: "s2 \<in> {0..1}" using s2t ht(2) by auto
  have gs1_frontier: "g s1 \<in> frontier S"
    using frontier_S s1_01 by (auto simp: path_image_def)
  have gs2_frontier: "g s2 \<in> frontier S"
    using frontier_S s2_01 by (auto simp: path_image_def)
      \<comment> \<open>Step 4: Find a third distinct point on @{term "frontier S"} with the same real part.
       Key insight: one of $g(0)=0$ or $g(t)=b$ has a \emph{different} parameter from $s_1$ and $s_2$,
       and since @{term g} is injective on $\{0..t\}$, it gives a distinct point.
       But we need it to have the \emph{same} real part --- that is only possible if $Re(g\,s_1) \in \{0, Re\,b\}$.
       If $Re(g\,s_1) = 0$ then $g\,s_1 = g\,0$ (since $Re(g\,0) = 0$) --- but then $s_1 = 0$ by injectivity.
       Similarly if $Re(g\,s_1) = Re\,b$ then $s_1 = t$.
       So we need a different approach: the third point comes from the \emph{other} arc $\{t..1\}$.
       On the other arc, @{term g} goes from $b$ back to $0$, so $Re$ goes from $Re\,b$ back to $0$.
       By the IVT (since @{term g} is continuous), for any $c \in (0, Re\,b)$ there exists $s_3 \in \{t..1\}$ with
       $Re(g\,s_3) = c$. This $s_3$ gives a third point on @{term "frontier S"}.\<close>
  define c where "c \<equiv> Re (g s1)"
    \<comment> \<open>Step 4a: Show $c \in \{0, Re\,b\}$ forces $s_1$ or $s_2$ to an endpoint, contradicting \<open>not_endpts\<close>.\<close>
  have c_strict: "0 < c \<and> c < Re b"
  proof -
    have a0: "a = 0" using geq0(1) g(2) by (simp add: pathstart_def)
    have Imb: "Im b = 0" using b(3) a0 by simp
    have Reb: "Re b > 0" using b(2) a0 by simp
    have bdd: "bounded (path_image g)"
      using compact_simple_path_image[OF g(1)] compact_imp_bounded by blast
    have gs1_pi: "g s1 \<in> path_image g" using s1_01 by (auto simp: path_image_def)
    have gs2_pi: "g s2 \<in> path_image g" using s2_01 by (auto simp: path_image_def)
    have g0_pi: "0 \<in> path_image g" using geq0(1) by (metis pathstart_def pathstart_in_path_image)
    have diam_eq: "dist 0 b = diameter (path_image g)" using dab a0 by simp
    have dist_0b: "dist 0 b = Re b"
      using Imb Reb cmod_eq_Re by auto
    \<comment> \<open>Every point on the curve is within distance $Re\,b$ of both $0$ and $b$\<close>
    have d1: "dist (g s1) b \<le> Re b"
      using diameter_bounded_bound[OF bdd gs1_pi b(1)] diam_eq dist_0b by simp
    have d2: "dist 0 (g s1) \<le> Re b"
      using diameter_bounded_bound[OF bdd g0_pi gs1_pi] diam_eq dist_0b by simp
    \<comment> \<open>Helper: from $\mathit{cmod}\ z \le Re\,b$, derive $(Re\,z)^2 + (Im\,z)^2 \le (Re\,b)^2$\<close>
    have cmod_sq: "(Re z)\<^sup>2 + (Im z)\<^sup>2 \<le> (Re b)\<^sup>2" if "cmod z \<le> Re b" for z
      by (metis cmod_power2 norm_ge_zero power_mono that)
    \<comment> \<open>Helper: from $\mathit{cmod}\,(z - b) \le Re\,b$, derive $(Re\,z - Re\,b)^2 + (Im\,z)^2 \le (Re\,b)^2$\<close>
    have cmod_sq_b: "(Re z - Re b)\<^sup>2 + (Im z)\<^sup>2 \<le> (Re b)\<^sup>2" if "cmod (z - b) \<le> Re b" for z
      using Imb cmod_sq that by force
    \<comment> \<open>Helper: injectivity gives $s = 0$ from $g\,s = 0$, and $s = t$ from $g\,s = b$\<close>
    have eq_0: "s = 0" if "g s = 0" "s \<in> {0..t}" for s
      using geq0(1) inj_onD inj_sub that by fastforce
    have eq_t: "s = t" if "g s = b" "s \<in> {0..t}" for s
      using ht(3) inj_on_contraD inj_sub that by fastforce
    \<comment> \<open>Case $c = 0$: $Re(g\,s_1) = 0$, and $\mathit{dist}\,(g\,s_1)\,b \le Re\,b$ forces $Im(g\,s_1) = 0$, so $g\,s_1 = 0$\<close>
    have "c \<noteq> 0"
    proof
      assume "c = 0"
      then have Re0: "Re (g s1) = 0" unfolding c_def by simp
      have "(Re (g s1) - Re b)\<^sup>2 + (Im (g s1))\<^sup>2 \<le> (Re b)\<^sup>2"
        using cmod_sq_b d1 by (simp add: dist_norm)
      then have "(Im (g s1))\<^sup>2 \<le> 0" using Re0 by (simp add: power2_eq_square)
      then have "g s1 = 0" using Re0 by (auto simp: complex_eq_iff)
      then have "s1 = 0" using eq_0 s1t by simp
      moreover have "Re (g s2) = 0" using Re_eq \<open>c = 0\<close> c_def by simp
      then have "(Re (g s2) - Re b)\<^sup>2 + (Im (g s2))\<^sup>2 \<le> (Re b)\<^sup>2"
        using cmod_sq_b[of "g s2"] diameter_bounded_bound[OF bdd gs2_pi b(1)]
          diam_eq dist_0b by (simp add: dist_norm)
      then have "(Im (g s2))\<^sup>2 \<le> 0" using \<open>Re (g s2) = 0\<close> by (simp add: power2_eq_square)
      then have "g s2 = 0" using \<open>Re (g s2) = 0\<close> by (auto simp: complex_eq_iff)
      then have "s2 = 0" using eq_0 s2t by simp
      ultimately show False using neq by simp
    qed
    \<comment> \<open>Case $c = Re\,b$: $\mathit{dist}\,0\,(g\,s_1) \le Re\,b$ forces $Im(g\,s_1) = 0$, so $g\,s_1 = b$\<close>
    moreover have "c \<noteq> Re b"
    proof
      assume "c = Re b"
      then have ReB: "Re (g s1) = Re b" unfolding c_def by simp
      have "(Re (g s1))\<^sup>2 + (Im (g s1))\<^sup>2 \<le> (Re b)\<^sup>2"
        using cmod_sq d2 by (simp add: dist_norm)
      then have "(Im (g s1))\<^sup>2 \<le> 0" using ReB by (simp add: power2_eq_square)
      then have "g s1 = b" using ReB Imb by (auto simp: complex_eq_iff)
      then have "s1 = t" using eq_t s1t by simp
      moreover have "Re (g s2) = Re b" using Re_eq \<open>c = Re b\<close> c_def by simp
      then have "(Re (g s2))\<^sup>2 + (Im (g s2))\<^sup>2 \<le> (Re b)\<^sup>2"
        using cmod_sq[of "g s2"] diameter_bounded_bound[OF bdd g0_pi gs2_pi]
          diam_eq dist_0b by (simp add: dist_norm)
      then have "(Im (g s2))\<^sup>2 \<le> 0" using \<open>Re (g s2) = Re b\<close> by (simp add: power2_eq_square)
      then have "g s2 = b" using \<open>Re (g s2) = Re b\<close> Imb by (auto simp: complex_eq_iff)
      then have "s2 = t" using eq_t s2t by simp
      ultimately show False using neq by simp
    qed
    \<comment> \<open>$c$ is bounded: $0 \le c \le Re\,b$ from the diameter bound\<close>
    moreover have "0 \<le> c"
    proof -
      \<comment> \<open>From $\mathit{dist}\,(g\,s_1)\,b \le Re\,b$: $|Re(g\,s_1) - Re\,b| \le \mathit{cmod}\,(g\,s_1 - b) \le Re\,b$\<close>
      have "\<bar>Re (g s1) - Re b\<bar> \<le> cmod (g s1 - b)"
        using abs_Re_le_cmod[of "g s1 - b"] by simp
      also have "\<dots> \<le> Re b" using d1 by (simp add: dist_norm)
      finally show ?thesis unfolding c_def by linarith
    qed
    moreover have "c \<le> Re b"
      by (smt (verit) c_def complex_Re_le_cmod d2 dist_0_norm)
    ultimately show ?thesis by linarith
  qed
      \<comment> \<open>Step 4b: By the IVT on $\{t..1\}$, find $s_3$ with $Re(g\,s_3) = c$.\<close>
  have cont_Re_g: "continuous_on {t..1} (Re \<circ> g)"
    using absolutely_continuous_on_imp_continuous assms(2) cont continuous_on_Re
      continuous_on_eq continuous_on_subset by fastforce
  obtain s3 where s3: "s3 \<in> {t..1}" "Re (g s3) = c"
  proof -
    have img_conn: "connected ((Re \<circ> g) ` {t..1})"
      by (intro connected_continuous_image cont_Re_g connected_Icc)
    then have img_iv: "is_interval ((Re \<circ> g) ` {t..1})"
      using is_interval_connected_1 by auto
    have "Re (g t) \<in> (Re \<circ> g) ` {t..1}" using ht(1,2) by (auto simp: image_def)
    then have Regt_in: "Re b \<in> (Re \<circ> g) ` {t..1}" using ht(3) by simp
    have "Re (g 1) \<in> (Re \<circ> g) ` {t..1}" using ht(2) by (auto simp: image_def)
    then have Re0_in: "0 \<in> (Re \<circ> g) ` {t..1}" using geq0 by simp
    have "c \<in> (Re \<circ> g) ` {t..1}"
      using img_iv[unfolded is_interval_1] Regt_in Re0_in c_strict by auto
    then show ?thesis using that by (auto simp: image_def)
  qed
    \<comment> \<open>Step 4c: $g\,s_3$ is on @{term "frontier S"} and distinct from $g\,s_1$ and $g\,s_2$.\<close>
  have s3_01: "s3 \<in> {0..1}" using s3(1) ht(1) by auto
  have loopfr_g: "loop_free g" using g by (simp add: simple_path_def)
  have gs3_frontier: "g s3 \<in> frontier S"
    using frontier_S s3_01 by (auto simp: path_image_def)
  have gs3_ne_gs1: "g s3 \<noteq> g s1"
  proof
    assume eq: "g s3 = g s1"
    with loopfr_g have "s3 = s1 \<or> s3 = 0 \<and> s1 = 1 \<or> s3 = 1 \<and> s1 = 0"
      using eq loop_free_def s1_01 s3_01 by blast
    then show False
      using assms(1) c_def c_strict eq geq0(2) ht(3) s3(1) by auto
  qed
  have gs3_ne_gs2: "g s3 \<noteq> g s2"
  proof
    assume eq: "g s3 = g s2"
    with loopfr_g have "s3 = s2 \<or> s3 = 0 \<and> s2 = 1 \<or> s3 = 1 \<and> s2 = 0"
      using eq loop_free_def s2_01 s3_01 by blast
    then show False
      using assms(2) c_strict geq0(2) ht(3) s3(1,2) by fastforce
  qed
    \<comment> \<open>Step 5: The ``sides'' condition for \<open>frontier_vertical_at_most_two\<close>.\<close>
  have side_left: "\<exists>p \<in> S. Re p < c"
    by (metis S_def assms(5) c_strict hull_inc pathstart_def pathstart_in_path_image
        zero_complex.sel(1))
  have side_right: "\<exists>q \<in> S. c < Re q"
    by (metis S_def b(1) c_strict hull_inc)
    \<comment> \<open>Step 6: Apply \<open>frontier_vertical_at_most_two\<close> for the contradiction.\<close>
  have three_distinct: "g s1 \<noteq> g s2 \<and> g s1 \<noteq> g s3 \<and> g s2 \<noteq> g s3"
    using g_neq gs3_ne_gs1 gs3_ne_gs2 by auto
  have Re_all_c: "Re (g s1) = c" "Re (g s2) = c" "Re (g s3) = c"
    unfolding c_def using Re_eq s3(2) c_def by auto
  have "\<not> (g s1 \<noteq> g s2 \<and> g s1 \<noteq> g s3 \<and> g s2 \<noteq> g s3)"
    using frontier_vertical_at_most_two[OF S_convex S_compact S_int_ne side_left side_right
        gs1_frontier gs2_frontier gs3_frontier Re_all_c] .
  then show False using three_distinct by auto
qed

lemma not_all_above:
  assumes Reb: "Re b > 0"
  assumes "a = 0"
  assumes real_on_curve: "\<And>z. z \<in> path_image g \<Longrightarrow> Im z = 0 \<Longrightarrow> z = 0 \<or> z = b"
  shows "\<not> (path_image g \<subseteq> {z. 0 \<le> Im z})"
proof -
  have seg_infinite: "\<not> finite (open_segment a b)"
    using Reb assms by force
  have seg_Im0: "open_segment a b \<subseteq> {z. Im z = 0}"
    using assms b by (auto simp: in_segment complex_eq_iff)
  then have seg_in_closure: "open_segment a b \<subseteq> closure (inside (path_image g))"
    by (metis b(1) conv convex_contains_open_segment convex_convex_hull convex_hull_eq_closure_inside
        g hull_inc pathfinish_in_path_image)
  have frontier_eq: "frontier (inside (path_image g)) = path_image g"
    using Jordan_inside_outside g by blast

  show ?thesis
  proof
    assume "path_image g \<subseteq> {z. 0 \<le> Im z}"
    then have "convex hull (path_image g) \<subseteq> {z. 0 \<le> Im z}"
      by (intro hull_minimal convex_halfspace_Im_ge)
    then have "inside (path_image g) \<subseteq> {z. (0::real) \<le> \<i> \<bullet> z}"
      using closure_subset conv convex_hull_eq_closure_inside g by auto
    then have "inside (path_image g) \<subseteq> interior {z. (0::real) \<le> \<i> \<bullet> z}"
      using interior_maximal open_inside Jordan_inside_outside g by blast
    also have "\<dots> = {z. 0 < \<i> \<bullet> z}"
      by (rule interior_halfspace_ge) simp
    finally have "inside (path_image g) \<subseteq> {z. 0 < Im z}"
      by simp
    then have "open_segment a b \<subseteq> {z \<in> path_image g. Im z = 0}"
      using Jordan_inside_outside[of g] frontier_def g interior_open seg_Im0 seg_in_closure
      by fastforce
    also have "\<dots> \<subseteq> {0, b}"
      using real_on_curve by blast
    finally show False using seg_infinite finite_subset by blast
  qed
qed

end


context Green
begin

interpretation CR: Green gop gop' "(\<lambda>t. 1-t) ` U" "cnj a" "cnj b"
  by (rule cnj_rev)

lemma Green_area_zero_A:
  assumes "a = 0" 
    and t: "0 < t" "t < 1"
    and hgt: "g t = b"
    and above: "g ` {0..t} \<subseteq> {z. 0 \<le> Im z}"
    and below: "g ` {t..1} \<subseteq> {z. Im z \<le> 0}"
  shows "Green_concl g g'"
proof -
  \<comment> \<open>Common facts used by both split_case and split_case'\<close>
  have g0: "g 0 = 0" using assms g(2) by (simp add: pathstart_def)
  have g1: "g 1 = 0" using assms g(3) by (simp add: pathfinish_def)
  have lfg: "loop_free g" using g by (simp add: simple_path_def)
  have Reb: "Re b > 0" using b(2) assms by simp
  have Imb: "Im b = 0" using b(3) assms by simp
    \<comment> \<open>Re-injectivity: on each arc, @{term "Re \<circ> g"} is injective (except at endpoints).
       Otherwise \<open>frontier_vertical_at_most_two\<close> gives a contradiction via three points
       on $\mathit{frontier}\,(\mathit{closure}\,(\mathit{inside}))$ with the same real part.\<close>
  have Re_inj_upper: "\<lbrakk>s1 \<in> {0..t}; s2 \<in> {0..t}; Re (g s1) = Re (g s2); s1 \<noteq> s2\<rbrakk>
        \<Longrightarrow> (s1 = 0 \<and> s2 = t) \<or> (s1 = t \<and> s2 = 0)" for s1 s2
    using Re_inj_upper_gen g0 g1 using hgt t by presburger
  have Re_inj_lower: "\<lbrakk>s1 \<in> {t..1}; s2 \<in> {t..1}; Re (g s1) = Re (g s2); s1 \<noteq> s2\<rbrakk>
        \<Longrightarrow> (s1 = t \<and> s2 = 1) \<or> (s1 = 1 \<and> s2 = t)" for s1 s2
    using CR.Re_inj_upper_gen[of "1-s1" "1-t" "1-s2"] hgt t using g g0 g1 assms
    by (auto simp add: gop_def reversepath_def)
      \<comment> \<open>Step 0: absolute integrability (needed for integral splitting)\<close>
  define f where "f \<equiv> \<lambda>s. Re (g' s) * Im (g s)"
  have f_int: "f integrable_on {0..1}"
    using set_lebesgue_integral_eq_integral(1)[OF f_abs_int] f_def by argo
  have split_int: "integral {0..1} f = integral {0..t} f + integral {t..1} f"
    using Henstock_Kurzweil_Integration.integral_combine[of 0 t 1 f] t f_int by auto
      \<comment> \<open>Upper arc integral $\ge 0$.
       By the change of variables $x = Re(g(s))$ and Re-injectivity, the integral
       $\int_0^t Re(g') \cdot Im(g)\,ds = \int_0^{Re\,b} f_{\mathit{upper}}(x)\,dx \ge 0$
       since $f_{\mathit{upper}} = Im \circ g \circ Re^{-1} \ge 0$ on the upper arc.\<close>
  interpret A0t: Area g g' 0 t U
  proof
    show "Re (g 0) \<le> Re (g t)" 
      using g0 hgt Reb by simp
    show "absolutely_continuous_on {0..t} g"
      using absolutely_continuous_on_subset[OF cont] t by auto
    show "inj_on g {0..t}"
      using arc_inj_on t less_eq_real_def by presburger
    then show "inj_on Re (g ` {0..t})"
      using Reb Re_inj_upper g0 t
      by (intro arc_Re_inj_on; fastforce simp: assms b(2))
  qed (use above U vder t in auto)
  have upper_int: "integral {0..t} f \<ge> 0"
    unfolding f_def using A0t.below_arclet(2) by auto
    \<comment> \<open>Lower arc integral $\ge 0$ as well.\<close>
  have Re_le': "Re (g 1) \<le> Re (g t)" using g1 hgt Reb by simp
  have ac_sub': "absolutely_continuous_on {t..1} g"
    using absolutely_continuous_on_subset[OF cont] t by auto
  have inj_g_lower: "inj_on g {t..1}"
    using arc_inj_on t(2) less_eq_real_def t by presburger
  then have inj_Re_lower: "inj_on Re (g ` {t..1})"
    using Reb Re_inj_lower g1 t
    by (intro arc_Re_inj_on; fastforce simp: assms b(2))
  have lower_int: "integral {t..1} f \<ge> 0"
    unfolding f_def
    using t vder area_above_arclet(2)[OF _ Re_le' ac_sub' below inj_g_lower inj_Re_lower U]
    by auto
    \<comment> \<open>Total integral $=$ area of the inside.
       The inside decomposes as the region between the two arcs:
       $\mathit{inside}\,(\mathit{path\_image}\ g) = \{z \mid Re\,z \in (0, Re\,b) \wedge f_{\mathit{lower}}(Re\,z) < Im\,z < f_{\mathit{upper}}(Re\,z)\}$.
       By Fubini, its area $= \int_0^{Re\,b} (f_{\mathit{upper}}(x) - f_{\mathit{lower}}(x))\,dx$,
       and by the change-of-variables computations above, this equals
       @{term "integral {0..t} f + integral {t..1} f"} $=$ @{term "integral {0..1} f"}.\<close>
  have area_decomp: "measure lebesgue (inside (path_image g)) = integral {0..t} f + integral {t..1} f"
  proof -
    \<comment> \<open>Re-derive the integral-equals-measure identities (proved locally in \<open>upper_int\<close>/\<open>lower_int\<close>)\<close>
    have Re_le: "Re (g 0) \<le> Re (g t)" and Re_le': "Re (g 1) \<le> Re (g t)" 
      using g0 g1 hgt Reb by auto
    have inj_Re_upper: "inj_on Re (g ` {0..t})"
      using Reb Re_inj_upper g0 arc_inj_on[of 0 t] t
      by (intro arc_Re_inj_on; fastforce simp: assms b(2))
        \<comment> \<open>The integral-equals-measure identities\<close>
    define Au where "Au \<equiv> {z. \<exists>w \<in> g ` {0..t}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
    define Al where "Al \<equiv> {z. \<exists>w \<in> g ` {t..1}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
    have int_upper: "integral {0..t} f = measure lebesgue Au"
      using A0t.below_arclet(2) unfolding f_def Au_def by auto
    have int_lower: "integral {t..1} f = measure lebesgue Al"
      using t vder area_above_arclet(2)[OF _ Re_le' ac_sub' below inj_g_lower inj_Re_lower U]
      unfolding f_def Al_def by auto
        \<comment> \<open>Step A: @{term Au} and @{term Al} are measurable (compact, hence @{term lmeasurable})\<close>
    have cont_g_upper: "continuous_on {0..t} g"
      by (simp add: absolutely_continuous_on_imp_continuous A0t.acont_g)
    define \<phi> where "\<phi> \<equiv> \<lambda>(s,r). Complex (Re (g s)) (r * Im (g s))"
    have cont_\<phi>: "continuous_on ({0..t} \<times> {0..1}) \<phi>"
      unfolding \<phi>_def split_def
      by (intro continuous_intros continuous_on_compose2[OF cont_g_upper] continuous_on_fst) auto
    have img: "\<phi> ` ({0..t} \<times> {0..1}) = Au"
    proof (rule set_eqI)
      fix z 
      show "z \<in> \<phi> ` ({0..t} \<times> {0..1}) \<longleftrightarrow> z \<in> Au"
      proof
        assume "z \<in> \<phi> ` ({0..t} \<times> {0..1})"
        then obtain s r where sr: "s \<in> {0..t}" "r \<in> {0..1}" "z = Complex (Re (g s)) (r * Im (g s))"
          unfolding \<phi>_def by auto
        have Im_ge: "Im (g s) \<ge> 0"
          using subsetD[OF above imageI[OF sr(1)]] by simp
        have "g s \<in> g ` {0..t}" using sr(1) by auto
        moreover have "Im z \<le> Im (g s)" 
          using sr Im_ge by (auto simp: mult_left_le_one_le)
        ultimately show "z \<in> Au" using sr Im_ge unfolding Au_def by auto
      next
        assume "z \<in> Au"
        then obtain w where w: "w \<in> g ` {0..t}" "Re w = Re z" "0 \<le> Im z" "Im z \<le> Im w"
          unfolding Au_def by auto
        then obtain s where s: "s \<in> {0..t}" "w = g s" by auto
        show "z \<in> \<phi> ` ({0..t} \<times> {0..1})"
        proof (cases "Im w = 0")
          case True 
          then have "z = \<phi> (s, 0)" unfolding \<phi>_def using w s(2) by (simp add: complex_eq_iff)
          then show ?thesis using s(1) by auto
        next
          case False
          define r where "r \<equiv> Im z / Im w"
          have "Im w > 0" using False w(3,4) by linarith
          moreover have "z = \<phi> (s, r)"
            unfolding \<phi>_def r_def using False w s(2) by (simp add: field_simps complex_eq_iff)
          ultimately show ?thesis using w s(1) by (auto simp: r_def)
        qed
      qed
    qed
    have Au_meas: "Au \<in> lmeasurable"
      using img compact_continuous_image[OF cont_\<phi>] lmeasurable_compact by (metis compact_Icc compact_Times)
    have cont_g_lower: "continuous_on {t..1} g"
      using absolutely_continuous_on_imp_continuous[OF ac_sub'] is_interval_cc by blast
    define \<psi> where "\<psi> \<equiv> \<lambda>(s::real, r::real). Complex (Re (g s)) (r * Im (g s))"
    have cont_\<psi>: "continuous_on ({t..1} \<times> {0..1}) \<psi>"
      unfolding \<psi>_def split_def
      by (intro continuous_intros continuous_on_compose2[OF cont_g_lower] continuous_on_fst) auto
    have img: "\<psi> ` ({t..1} \<times> {0..1}) = Al"
    proof (rule set_eqI)
      fix z :: complex
      show "z \<in> \<psi> ` ({t..1} \<times> {0..1}) \<longleftrightarrow> z \<in> Al"
      proof
        assume "z \<in> \<psi> ` ({t..1} \<times> {0..1})"
        then obtain s r where sr: "s \<in> {t..1}" "r \<in> {0..1}" "z = Complex (Re (g s)) (r * Im (g s))"
          unfolding \<psi>_def by auto
        have Im_le: "Im (g s) \<le> 0"
          using subsetD[OF below imageI[OF sr(1)]] by simp
        then have "Im (g s) \<le> Im z"
          using less_eq_real_def sr by fastforce
        moreover have "Im z \<le> 0"
          using sr Im_le mult_nonneg_nonpos[of r "Im (g s)"] by simp
        ultimately show "z \<in> Al" 
          unfolding Al_def using sr by auto
      next
        assume "z \<in> Al"
        then obtain w where w: "w \<in> g ` {t..1}" "Re w = Re z" "Im w \<le> Im z" "Im z \<le> 0"
          unfolding Al_def by auto
        then obtain s where s: "s \<in> {t..1}" "w = g s" by auto
        show "z \<in> \<psi> ` ({t..1} \<times> {0..1})"
        proof (cases "Im w = 0")
          case True
          then have "z = \<psi> (s, 0)" unfolding \<psi>_def using w s(2) by (simp add: complex_eq_iff)
          then show ?thesis using s(1) by auto
        next
          case False
          define r where "r \<equiv> Im z / Im w"
          have "r \<in> {0..1}" unfolding r_def using w
            using False by (auto simp: field_simps)
          moreover have "z = \<psi> (s, r)"
            unfolding \<psi>_def r_def using False w(2) s(2) by (simp add: complex_eq_iff)
          ultimately show ?thesis using s(1) by auto
        qed
      qed
    qed
    have "compact ({t..1} \<times> {0..1::real})" by (intro compact_Times compact_Icc)
    then have Al_meas: "Al \<in> lmeasurable" \<comment> \<open>duality\<close>
      using img compact_continuous_image[OF cont_\<psi>] lmeasurable_compact by blast

    have ch_eq: "convex hull (path_image g) = closure (inside (path_image g))"
      using convex_hull_eq_closure_inside[OF g(1) _ conv] g(2,3) by auto
    have zero_in_ch: "0 \<in> convex hull (path_image g)"
      using hull_subset[of "path_image g" convex] g0
      by (auto simp: path_image_def intro!: imageI[of 0])
    have b_in_ch: "b \<in> convex hull (path_image g)"
      using hull_subset[of "path_image g" convex] b(1) by auto
    have bdd_pi: "bounded (path_image g)"
      using compact_simple_path_image[OF g(1)] compact_imp_bounded by blast
        \<comment> \<open>Key fact: every point on the path has $Re \in [0, Re\,b]$\<close>
    have zero_in_pi: "(0::complex) \<in> path_image g"
      using g0 by (auto simp: path_image_def intro!: imageI[of 0])
    have Re_bounds: "0 \<le> Re w \<and> Re w \<le> Re b" if "w \<in> path_image g" for w
    proof -
      have "diameter (path_image g) = dist 0 b" using dab g0 g1 assms by simp
      then have diam_eq: "diameter (path_image g) = Re b"
        using Imb Re_le cmod_eq_Re g0 hgt by auto
      have "cmod w \<le> Re b" 
        using diameter_bounded_bound[OF bdd_pi that zero_in_pi] diam_eq by (simp add: dist_norm)
      moreover have "cmod (w - b) \<le> Re b" 
        using diameter_bounded_bound[OF bdd_pi that b(1)] diam_eq by (simp add: dist_norm)
      ultimately show ?thesis using abs_Re_le_cmod[of w] abs_Re_le_cmod[of "w - b"] by auto
    qed
      \<comment> \<open>Sublemma: @{term "Complex (Re w) 0 \<in> closed_segment 0 b"} for any @{term w} on the path\<close>
    have real_point_in_seg: "Complex (Re w) 0 \<in> closed_segment 0 b"
      if "w \<in> path_image g" for w
    proof -
      have bds: "0 \<le> Re w" "Re w \<le> Re b" using Re_bounds[OF that] by auto
      define u where "u \<equiv> Re w / Re b"
      have "0 \<le> u" "u \<le> 1" unfolding u_def using bds Reb by auto
      have "Complex (Re w) 0 = (1 - u) *\<^sub>R 0 + u *\<^sub>R b"
        unfolding u_def using Reb Imb
        by (simp add: complex_eq_iff scaleR_complex.ctr)
      then show ?thesis using \<open>0 \<le> u\<close> \<open>u \<le> 1\<close>
        unfolding closed_segment_def by auto
    qed
      \<comment> \<open>Sublemma: any @{term z} between $p = \mathit{Complex}\,(Re\,w)\,0$ and @{term w} is in the convex hull\<close>
    have in_ch_via_seg: "z \<in> convex hull (path_image g)"
      if w_pi: "w \<in> path_image g"
        and Re_eq: "Re w = Re z"
        and Im_between: "(0 \<le> Im z \<and> Im z \<le> Im w) \<or> (Im w \<le> Im z \<and> Im z \<le> 0)"
      for z w
    proof -
      define p where "p \<equiv> Complex (Re w) 0"
      have p_in_ch: "p \<in> convex hull (path_image g)"
        using b_in_ch closed_segment_subset p_def real_point_in_seg w_pi zero_in_ch by blast
      have w_in_ch: "w \<in> convex hull (path_image g)"
        using hull_subset[of "path_image g" convex] w_pi by auto
      show "z \<in> convex hull (path_image g)"
      proof (cases "Im w = 0")
        case True
        with that show ?thesis using p_in_ch
          by (metis complex.exhaust_sel p_def verit_la_disequality)
      next
        case False
        define u where "u \<equiv> Im z / Im w"
        have "0 \<le> u" "u \<le> 1" unfolding u_def using Im_between False
          by (auto simp: field_simps split: if_splits)
        have "z = (1 - u) *\<^sub>R p + u *\<^sub>R w"
          using False by (simp add: Re_eq p_def u_def complex_eq_iff scaleR_complex.ctr field_simps)
        then show ?thesis
          by (simp add: \<open>0 \<le> u\<close> \<open>u \<le> 1\<close> convexD_alt p_in_ch w_in_ch)
      qed
    qed
    have Au_sub: "Au \<subseteq> convex hull (path_image g)"
    proof (rule subsetI)
      fix z assume "z \<in> Au"
      then obtain w where "w \<in> g ` {0..t}" "Re w = Re z" "0 \<le> Im z" "Im z \<le> Im w"
        unfolding Au_def by auto
      then show "z \<in> convex hull (path_image g)"
        using t in_ch_via_seg[of w z] by (auto simp: path_image_def)
    qed
    have Al_sub: "Al \<subseteq> convex hull (path_image g)"
    proof (rule subsetI)
      fix z assume "z \<in> Al"
      then obtain w where "w \<in> g ` {t..1}" "Re w = Re z" "Im w \<le> Im z" "Im z \<le> 0"
        unfolding Al_def by auto
      then show "z \<in> convex hull (path_image g)"
        using t in_ch_via_seg[of w z] by (auto simp: path_image_def)
    qed
    have Au_Al_sub_closure: "Au \<union> Al \<subseteq> closure (inside (path_image g))"
      using Au_sub Al_sub ch_eq by auto

    have inside_sub_Au_Al: "inside (path_image g) \<subseteq> Au \<union> Al"
    proof (rule subsetI)
      fix z assume z_in: "z \<in> inside (path_image g)"
        \<comment> \<open>Set up the convex hull S and its key properties\<close>
      define S where "S \<equiv> convex hull (path_image g)"
      have S_bounded: "bounded S"
        by (simp add: S_def bounded_convex_hull bounded_simple_path_image g)
      have frontier_S: "frontier S = path_image g"
        unfolding S_def using frontier_convex_hull_eq_path_image[OF g(1) _ conv] g(2,3) by auto
      have inside_eq_int: "inside (path_image g) = interior S"
        using S_bounded S_def frontier_S inside_frontier_eq_interior by force
      have S_int_ne: "interior S \<noteq> {}"
        using z_in inside_eq_int by auto
      have rel_fr_eq: "rel_frontier S = frontier S"
        using rel_frontier_nonempty_interior[OF S_int_ne] .
      have z_int: "z \<in> interior S" and z_rel_int: "z \<in> rel_interior S" 
        using z_in inside_eq_int rel_interior_nonempty_interior by auto
          \<comment> \<open>@{term S} is full-dimensional, so @{term "affine hull S = UNIV"}\<close>
      have aff_S: "affine hull S = UNIV"
        by (simp add: S_int_ne affine_hull_nonempty_interior)
          \<comment> \<open>Case split on the sign of $Im\,z$\<close>
      show "z \<in> Au \<union> Al"
      proof (cases "Im z \<ge> 0")
        case True
          \<comment> \<open>Shoot a ray upward from @{term z} in direction @{term \<i>}.
             By \<open>ray_to_rel_frontier\<close>, we hit a point on @{term "frontier S"} $=$ @{term "path_image g"}.\<close>
        obtain d where d: "d > 0" "z + d *\<^sub>R \<i> \<in> rel_frontier S"
          by (metis S_bounded complex_i_not_zero ray_to_frontier rel_fr_eq z_int)
        define w where "w \<equiv> z + d *\<^sub>R \<i>"
        have w_on_path: "w \<in> path_image g"
          using d(2) rel_fr_eq frontier_S w_def by auto
        have Re_w: "Re w = Re z" and Im_w: "Im w = Im z + d" unfolding w_def by auto
        have Im_w_pos: "Im w > 0" using True d(1) Im_w by linarith
        \<comment> \<open>Since $Im\,w > 0$ and the lower arc has $Im \le 0$, @{term w} must be on the upper arc\<close>
        have "{0..1} = {0..t} \<union> {t..1}" using t by (auto simp: ivl_disj_un_two_touch)
        then have w_upper: "w \<in> g ` {0..t}"
          using w_on_path Im_w_pos below subsetD by (fastforce simp: path_image_def)
        show "z \<in> Au \<union> Al"
          using Au_def Im_w Re_w True d(1) w_upper by auto
      next
        case False
        then have Im_z_neg: "Im z \<le> 0" by simp
            \<comment> \<open>Shoot a ray downward from @{term z} in direction @{term "-\<i>"}\<close>
        obtain d where d: "d > 0" "z + d *\<^sub>R (-\<i>) \<in> frontier S"
          by (metis S_bounded complex_i_not_zero neg_equal_0_iff_equal ray_to_frontier z_int)
        have d2: "z - d *\<^sub>R \<i> \<in> rel_frontier S"
          using d(2) rel_fr_eq by (simp add: real_vector.scale_minus_right)
        define w where "w \<equiv> z - d *\<^sub>R \<i>"
        have w_on_path: "w \<in> path_image g"
          using d2 rel_fr_eq frontier_S w_def by auto
        have Re_w: "Re w = Re z" and Im_w: "Im w = Im z - d" unfolding w_def by auto
        have Im_w_neg: "Im w < 0" using Im_z_neg d(1) Im_w by linarith
            \<comment> \<open>Since $Im\,w < 0$, @{term w} must be on the lower arc\<close>
        have w_lower: "w \<in> g ` {t..1}"
        proof -
          have "{0..1} = {0..t} \<union> {t..1}" using t by (auto simp: ivl_disj_un_two_touch)
          then have "path_image g = g ` {0..t} \<union> g ` {t..1}"
            unfolding path_image_def by (simp add: image_Un)
          then have "w \<in> g ` {0..t} \<union> g ` {t..1}" using w_on_path by simp
          moreover have "w \<notin> g ` {0..t}"
            using above Im_w_neg by (auto simp: subset_iff)
          ultimately show ?thesis by blast
        qed
        show "z \<in> Au \<union> Al"
          using Al_def Im_w Im_z_neg Re_w d(1) w_lower by auto
      qed
    qed
    have inside_eq: "measure lebesgue (inside (path_image g)) = measure lebesgue (Au \<union> Al)"
    proof -
      have bdd_inside: "bounded (inside (path_image g))"
       and frontier_inside: "frontier (inside (path_image g)) = path_image g"
        using Jordan_inside_outside g by auto
      have neg_frontier: "negligible (frontier (inside (path_image g)))"
        using negligible_convex_frontier[OF conv] .
      have inside_meas: "inside (path_image g) \<in> lmeasurable"
        using measurable_Jordan[OF bdd_inside neg_frontier] .
          \<comment> \<open>The symmetric difference is contained in @{term "path_image g"}, which is negligible\<close>
      have "inside (path_image g) \<Delta> (Au \<union> Al) \<subseteq> path_image g"
        by (metis Au_Al_sub_closure Diff_mono Diff_subset_conv closure_Un_frontier frontier_inside 
            inside_sub_Au_Al le_iff_sup)
      then show ?thesis
        using measure_negligible_symdiff[OF inside_meas] negligible_subset neg_frontier frontier_inside
        by metis
    qed
      \<comment> \<open>Step D: @{term "Au \<inter> Al \<subseteq> {z. Im z = 0}"}, which is negligible in $\mathbb{R}^2$.
         Therefore $\mathit{measure}\,(Au \cup Al) = \mathit{measure}\,Au + \mathit{measure}\,Al$.\<close>
    have inter_null: "Au \<inter> Al \<subseteq> {z. Im z = 0}"
      unfolding Au_def Al_def by auto
    have "measure lebesgue (Au \<union> Al) = measure lebesgue Au + measure lebesgue Al"
    proof -
      have "negligible (Au \<inter> Al)"
        using negligible_hyperplane[of \<i> 0] negligible_subset inter_null by auto
      then have "measure lebesgue (Au \<inter> Al) = 0"
        by (rule negligible_imp_measure0)
      moreover have "measure lebesgue (Au \<union> Al) = measure lebesgue Au + measure lebesgue Al - measure lebesgue (Au \<inter> Al)"
        using measure_Un3[of Au lebesgue Al] Au_meas Al_meas by auto
      ultimately show ?thesis by simp
    qed
    show ?thesis
      using inside_eq \<open>measure lebesgue (Au \<union> Al) = measure lebesgue Au + measure lebesgue Al\<close>
        int_upper int_lower by simp
  qed
  have int_eq: "\<bar>integral {0..1} f\<bar> = measure lebesgue (inside (path_image g))"
    using split_int area_decomp upper_int lower_int by linarith
  show ?thesis unfolding Green_concl_def f_def
    using int_eq f_abs_int unfolding f_def by auto
qed

end

subsection \<open>Green's theorem special case at zero\<close>

context Green
begin

interpretation CR: Green gop gop' "(\<lambda>t. 1-t) ` U" "cnj a" "cnj b"
  by (rule cnj_rev)

interpretation R: Green "reversepath g" "uminus \<circ> reversepath g'" "(\<lambda>t. 1-t) ` U" a b
  by (rule rev)

lemma Green_area_zero:
  assumes "a = 0"
  shows "Green_concl g g'"
proof -
  have g0: "g 0 = 0" using assms g(2) by (simp add: pathstart_def)
  have g1: "g 1 = 0" using assms g(3) by (simp add: pathfinish_def)
  define f where "f \<equiv> \<lambda>s. Re (g' s) * Im (g s)"
  have split_case: "Green_concl g g'"
    if assms: "a = 0"
      and t: "0 < t" "t < 1"
      and hgt: "g t = b"
      and above: "g ` {0..t} \<subseteq> {z. 0 \<le> Im z}"
      and below: "g ` {t..1} \<subseteq> {z. Im z \<le> 0}"
    for t :: real
    using Green_area_zero_A[OF assms t hgt above below] .
  have split_case': "Green_concl g g'"
    if assms: "a = 0"
      and t: "0 < t" "t < 1"
      and hgt: "g t = b"
      and below: "g ` {0..t} \<subseteq> {z. Im z \<le> 0}"
      and above: "g ` {t..1} \<subseteq> {z. 0 \<le> Im z}"
    for t :: real
  proof -
    have "Green_concl (reversepath g) (uminus \<circ> reversepath g')"
    proof (intro R.Green_area_zero_A)
      show "a=0" "0 < 1-t" "1-t < 1"
        using assms t by auto
      show "reversepath g (1-t) = b"
        by (simp add: hgt reversepath_def)
      show "reversepath g ` {0..1-t} \<subseteq> {z. 0 \<le> Im z}"
        using above by (force simp: reversepath_def image_subset_iff)
      show "reversepath g ` {1-t..1} \<subseteq> {z. Im z \<le> 0}"
        using below by (force simp: reversepath_def image_subset_iff)
    qed
    moreover have "integral {0..1} (\<lambda>t. Re (reversepath g' t) * Im (reversepath g t)) 
                 = integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))"
      using has_integral_affinity [of f _ 0 1 "-1" 1] f_abs_int
      by (fastforce simp add: reversepath_def f_def absolutely_integrable_on_def)
    ultimately show ?thesis
      using f_abs_int by (auto simp: Green_concl_def)
  qed

  have Reb: "Re b > 0" using b(2) assms by simp
  have Im_a: "Im a = 0" using assms by simp
  have Im_b: "Im b = 0" using b(3) Im_a by simp
  have path_g: "path g" using g(1) simple_path_imp_path by blast
  have cont_g: "continuous_on {0..1} g"
    using path_g by (simp add: path_def)
  obtain t where t: "g t = b" "0 < t" "t < 1"
  proof -
    obtain t where t0: "g t = b" "t \<in> {0..1}"
      using b by (auto simp: path_image_def)
    have "0 < t"
      by (metis atLeastAtMost_iff b(2) g(2) not_le order_eq_iff pathstart_def t0)
    moreover have "t < 1"
      by (smt (verit, best) b(2) box_real(2) g(3) mem_box_real(2) pathfinish_def t0)
    ultimately show thesis using t0 that by blast
  qed
  have "g ` {0..t} \<subseteq> {z. 0 \<le> Im z} \<and> g ` {t..1} \<subseteq> {z. Im z \<le> 0} \<or>
        g ` {0..t} \<subseteq> {z. Im z \<le> 0} \<and> g ` {t..1} \<subseteq> {z. 0 \<le> Im z}"
  proof -
    have "open_segment 0 b \<subseteq> frontier (inside (path_image g)) \<or>
          open_segment 0 b \<subseteq> interior (inside (path_image g))"
    proof (rule convex_open_segment_cases_alt)
      show "convex (inside (path_image g))"
        by (simp add: conv)
      show "0 \<in> closure (inside (path_image g))"
        using hull_inc convex_hull_eq_closure_inside
        by (metis assms conv g pathfinish_in_path_image)
      show "b \<in> closure (inside (path_image g))"
        using hull_inc convex_hull_eq_closure_inside
        using R.g(2) b(1) conv g(1,2) by fastforce
    qed
    then consider "open_segment 0 b \<subseteq> path_image g" 
      | "open_segment 0 b \<subseteq> inside (path_image g)"
      by (metis Jordan_inside_outside g interior_subset subset_trans)
    then show ?thesis
    proof cases
      case 1
      have *: "connectedin euclidean (open_segment 0 b)"
        by (simp add: convex_connected)
      with 1 have conn: "connectedin (subtopology euclidean (path_image g))
                         (open_segment 0 b)"
        by (simp add: connectedin_subtopology)
      have pi1: "g ` {0<..<t} \<subseteq> path_image g" and pi2: "g ` {t<..<1} \<subseteq> path_image g"
        using t by (auto simp: path_image_def image_iff)
      have cl1: "g ` {0<..<t} \<inter> path_image g \<inter> closure (path_image g \<inter> g ` {t<..<1}) = {}"
      proof -
        have lf: "loop_free g" using g(1) by (simp add: simple_path_def)
        have inj: "inj_on g {0<..<1}" using lf loop_free_inj_on by blast
        have disj: "g ` {0<..<t} \<inter> g ` {t..1} = {}"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          then obtain x y where xy: "x \<in> {0<..<t}" "y \<in> {t..1}" "g x = g y"
            by blast
          have x01: "x \<in> {0..1}" using xy(1) t(3) by auto
          have y01: "y \<in> {0..1}" using xy(2)
            using t(2) by auto
          have "x \<noteq> y" using xy(1,2) by auto
          then have "x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
            using lf xy(3) x01 y01 unfolding loop_free_def by blast
          then show False using xy(1,2) by auto
        qed
        have closed_img: "closed (g ` {t..1})"
          using compact_continuous_image[OF continuous_on_subset[OF cont_g]]
          by (simp add: compact_imp_closed less_eq_real_def t(2))
        have "closure (g ` {t<..<1}) \<subseteq> g ` {t..1}"
          using closed_img closure_minimal by (meson closure_minimal image_mono greaterThanLessThan_subseteq_atLeastAtMost_iff order.refl less_imp_le)
        then have "closure (path_image g \<inter> g ` {t<..<1}) \<subseteq> g ` {t..1}"
          by (meson Int_lower2 closure_mono dual_order.trans)
        then show ?thesis using disj by auto
      qed
      have cl2: "g ` {t<..<1} \<inter> path_image g \<inter> closure (path_image g \<inter> g ` {0<..<t}) = {}"
      proof -
        have lf: "loop_free g" using g(1) by (simp add: simple_path_def)
        have disj: "g ` {t<..<1} \<inter> g ` {0..t} = {}"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          then obtain x y where xy: "x \<in> {t<..<1}" "y \<in> {0..t}" "g x = g y"
            by blast
          have x01: "x \<in> {0..1}" using xy(1) using t(2) by force
          have y01: "y \<in> {0..1}" using xy(2) t(3) by auto
          have "x \<noteq> y" using xy(1,2) by auto
          then have "x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
            using lf xy(3) x01 y01 unfolding loop_free_def by blast
          then show False using xy(1,2) by auto
        qed
        have closed_img: "closed (g ` {0..t})"
          using compact_continuous_image[OF continuous_on_subset[OF cont_g] _]
          by (meson atLeastatMost_subset_iff compact_imp_closed compact_interval
              eucl_less_le_not_le order.refl t(3))
        have "closure (g ` {0<..<t}) \<subseteq> g ` {0..t}"
          using closed_img closure_minimal by (meson closure_minimal image_mono greaterThanLessThan_subseteq_atLeastAtMost_iff order.refl less_imp_le)
        then have "closure (path_image g \<inter> g ` {0<..<t}) \<subseteq> g ` {0..t}"
          by (meson Int_lower2 closure_mono dual_order.trans)
        then show ?thesis using disj by auto
      qed
      have sub: "open_segment 0 b \<subseteq> g ` {0<..<t} \<union> g ` {t<..<1}"
      proof -
        have decomp: "path_image g \<subseteq> g ` {0<..<t} \<union> g ` {t<..<1} \<union> {0, b}"
        proof
          fix z assume "z \<in> path_image g"
          then obtain s where s: "s \<in> {0..1}" "g s = z" by (auto simp: path_image_def)
          then consider "s = 0" | "s \<in> {0<..<t}" | "s = t" | "s \<in> {t<..<1}" | "s = 1"
            using t by force
          then show "z \<in> g ` {0<..<t} \<union> g ` {t<..<1} \<union> {0, b}"
            using \<open>g s = z\<close> t g0 g1 by blast 
        qed
        have "open_segment 0 b \<inter> {0, b} = {}"
          unfolding open_segment_def by auto
        then show ?thesis using 1 decomp by auto
      qed
      have sep: "separatedin (subtopology euclidean (path_image g))
                              (g ` {0<..<t}) (g ` {t<..<1})"
      proof -
        have d1: "g ` {0<..<t} \<inter> closure (g ` {t<..<1}) = {}"
          by (metis cl1 inf.absorb_iff2 inf.commute pi1 pi2)
        have d2: "g ` {t<..<1} \<inter> closure (g ` {0<..<t}) = {}"
          by (metis Int_absorb1 Int_commute cl2 pi1 pi2)
        have "separatedin euclidean (g ` {0<..<t}) (g ` {t<..<1})"
          unfolding separatedin_def using d1 d2
          by (simp add: euclidean_closure_of topspace_euclidean)
        then show ?thesis
          using pi1 pi2 by (simp add: separatedin_subtopology)
      qed
      have "open_segment 0 b \<subseteq> g ` {0<..<t} \<or> open_segment 0 b \<subseteq> g ` {t<..<1}"
        using connectedin_subset_separated_union[OF conn sep sub] .
      then have "closed_segment 0 b \<subseteq> g ` {0..t} \<or> closed_segment 0 b \<subseteq> g ` {t..1}"
        unfolding closed_segment_eq_open
        by (elim disj_forward) (use g0 g1 t in auto)
      then have seg_eq: "g ` {0..t} = closed_segment 0 b \<or> g ` {t..1} = closed_segment 0 b"
      proof (elim disjE)
        assume sub: "closed_segment 0 b \<subseteq> g ` {0..t}"
        have inj: "inj_on g {0..t}" using arc_inj_on[of 0 t] t by auto
        have "continuous_on {0..t} g"
          using continuous_on_subset[OF cont_g] t by auto
        then have cont_inv: "continuous_on (g ` {0..t}) (the_inv_into {0..t} g)"
          using continuous_on_inv_into[OF _ compact_Icc inj] by metis
        have inv_mem: "the_inv_into {0..t} g z \<in> {0..t}" if "z \<in> closed_segment 0 b" for z
          using the_inv_into_into[OF inj _ order_refl] sub that by blast
        have eq0: "the_inv_into {0..t} g 0 = 0"
          using the_inv_into_f_f[OF inj, of 0] g0 t by auto
        have eqt: "the_inv_into {0..t} g b = t"
          using the_inv_into_f_f[OF inj, of t] t by auto
        have conn: "connected (the_inv_into {0..t} g ` closed_segment 0 b)"
          by (intro connected_continuous_image continuous_on_subset[OF cont_inv sub]
              connected_segment)
        have "0 \<in> the_inv_into {0..t} g ` closed_segment 0 b"
          using eq0 by (auto intro: rev_image_eqI ends_in_segment)
        moreover have "t \<in> the_inv_into {0..t} g ` closed_segment 0 b"
          using eqt by (auto intro: rev_image_eqI ends_in_segment)
        ultimately have "{0..t} \<subseteq> the_inv_into {0..t} g ` closed_segment 0 b"
          using connected_contains_Icc[OF conn] by auto
        then have "g ` {0..t} \<subseteq> g ` (the_inv_into {0..t} g ` closed_segment 0 b)"
          by (rule image_mono)
        also have "\<dots> \<subseteq> closed_segment 0 b"
          using f_the_inv_into_f[OF inj] sub by (auto simp: image_image)
        finally show ?thesis using sub by auto
      next
        assume sub: "closed_segment 0 b \<subseteq> g ` {t..1}"
        have inj: "inj_on g {t..1}" using arc_inj_on[of t 1] t by auto
        have cont_sub: "continuous_on {t..1} g"
          using continuous_on_subset[OF cont_g] t by auto
        have cont_inv: "continuous_on (g ` {t..1}) (the_inv_into {t..1} g)"
          using continuous_on_inv_into[OF cont_sub compact_Icc inj] .
        have inv_mem: "the_inv_into {t..1} g z \<in> {t..1}" if "z \<in> closed_segment 0 b" for z
          using the_inv_into_into[OF inj _ order_refl] sub that by blast
        have eqt: "the_inv_into {t..1} g b = t"
          using the_inv_into_f_f[OF inj, of t] t by auto
        have eq1: "the_inv_into {t..1} g 0 = 1"
          using the_inv_into_f_f[OF inj, of 1] g1 t by auto
        have conn: "connected (the_inv_into {t..1} g ` closed_segment 0 b)"
          by (intro connected_continuous_image continuous_on_subset[OF cont_inv sub]
              connected_segment)
        have "t \<in> the_inv_into {t..1} g ` closed_segment 0 b"
          using eqt by (auto intro: rev_image_eqI ends_in_segment)
        moreover have "1 \<in> the_inv_into {t..1} g ` closed_segment 0 b"
          using eq1 by (auto intro: rev_image_eqI ends_in_segment)
        ultimately have "{t..1} \<subseteq> the_inv_into {t..1} g ` closed_segment 0 b"
          using connected_contains_Icc[OF conn] by auto
        then have "g ` {t..1} \<subseteq> g ` (the_inv_into {t..1} g ` closed_segment 0 b)"
          by (rule image_mono)
        also have "\<dots> \<subseteq> closed_segment 0 b"
          using f_the_inv_into_f[OF inj] sub by (auto simp: image_image)
        finally show ?thesis using sub by auto
      qed
        \<comment> \<open>Use \<open>convex_triple_rel_frontier\<close> to show the inside is on one side of $Im = 0$\<close>
      have inside_side: "inside (path_image g) \<subseteq> {z. Im z \<le> 0} \<or>
                         inside (path_image g) \<subseteq> {z. 0 \<le> Im z}"
      proof -
        have J: "inside (path_image g) \<noteq> {}" "open (inside (path_image g))"
          "frontier (inside (path_image g)) = path_image g"
          using Jordan_inside_outside g by blast+
        have intne: "interior (inside (path_image g)) \<noteq> {}"
          using J(1,2) interior_eq by auto
        have rf_eq: "rel_frontier (inside (path_image g)) = frontier (inside (path_image g))"
          using rel_frontier_nonempty_interior intne by blast
        have mid_on: "midpoint 0 b \<in> path_image g"
          using "1" Reb by force
        have rf0: "(0::complex) \<in> rel_frontier (inside (path_image g))"
          using rf_eq J(3) g0 by (auto simp: path_image_def intro!: image_eqI[of _ _ 0])
        have rfb: "b \<in> rel_frontier (inside (path_image g))"
          using rf_eq J(3) b(1) by auto
        have rfm: "midpoint 0 b \<in> rel_frontier (inside (path_image g))"
          using rf_eq J(3) mid_on by auto
        have ne1: "(0::complex) \<noteq> b" using b(2) assms by (auto simp: complex_eq_iff)
        have ne2: "(0::complex) \<noteq> midpoint 0 b"
          using ne1 by (simp add: midpoint_def complex_eq_iff)
        have ne3: "b \<noteq> midpoint 0 b"
          using ne1 by (simp add: midpoint_def complex_eq_iff)
        have \<section>: "\<i> \<bullet> midpoint 0 b = 0"
          using Im_b by (simp add: midpoint_def complex_inner_i_left)
        show ?thesis
          using Im_b convex_triple_rel_frontier[OF conv rf0 rfb rfm ne1 ne2 ne3 _ _ \<section>] 
          by (auto simp: midpoint_def complex_inner_i_left)
      qed
      have pi_sub: "path_image g \<subseteq> closure (inside (path_image g))"
        using hull_subset[of "path_image g" convex] convex_hull_eq_closure_inside[OF g(1)] g(2,3) conv by force
          \<comment> \<open>The closed segment from $0$ to $b$ has $Im = 0$, so lies in both half-planes.\<close>
      have seg_both: "closed_segment 0 b \<subseteq> {z. Im z \<le> 0}" "closed_segment 0 b \<subseteq> {z. 0 \<le> Im z}"
        using Im_b by (auto simp: closed_segment_def)
          \<comment> \<open>If the inside is contained in a half-plane, then so is @{term "path_image g"} (by closure).\<close>
      have "inside (path_image g) \<subseteq> {z. Im z \<le> 0} \<Longrightarrow> path_image g \<subseteq> {z. Im z \<le> 0}"
        using pi_sub closure_minimal[OF _ closed_halfspace_le[of \<i> 0, simplified complex_inner_i_left]]
        by auto
      moreover
      have "inside (path_image g) \<subseteq> {z. 0 \<le> Im z} \<Longrightarrow> path_image g \<subseteq> {z. 0 \<le> Im z}"
        using pi_sub closure_minimal[OF _ closed_halfspace_ge[of 0 \<i>, simplified complex_inner_i_left]]
        by auto
      ultimately show ?thesis
        using seg_eq inside_side seg_both
        by (auto simp add: path_image_def image_subset_iff)
    next
      case seg_inside:2
      have real_on_curve: "z = 0 \<or> z = b" 
        if z_on: "z \<in> path_image g" and z_real: "Im z = 0" for z
      proof (rule ccontr)
        assume non: "\<not> ?thesis"
          \<comment> \<open>diameter bounds force @{term z} into @{term "closed_segment 0 b"}.\<close>
        have bdd: "bounded (path_image g)"
          using g(1) bounded_simple_path_image by blast
        have z0_on: "0 \<in> path_image g"
          using pathstart_in_path_image[of g] g(2) \<open>a=0\<close> by simp
        have diam_eq: "diameter (path_image g) = Re b"
          using dab \<open>a=0\<close> Im_b Reb by (simp add: dist_complex_def cmod_eq_Re)
        have d1: "dist 0 z \<le> Re b"
          using diameter_bounded_bound[OF bdd z0_on z_on] diam_eq by simp
        have d2: "dist z b \<le> Re b"
          using diameter_bounded_bound[OF bdd z_on b(1)] diam_eq by simp
        have Re_le: "Re z \<le> Re b"
          using d1 z_real by (simp add: dist_complex_def cmod_eq_Re)
        have Re_ge: "Re z \<ge> 0"
          using d2 z_real Im_b by (simp add: dist_complex_def cmod_eq_Re minus_complex.sel)
        have z_eq: "z = of_real (Re z)"
          using z_real complex_is_Real_iff of_real_Re by metis
        have b_eq: "b = of_real (Re b)"
          using Im_b complex_is_Real_iff of_real_Re by metis
        have z_in_seg: "z \<in> closed_segment 0 b"
          by (metis Re_ge Re_le Reb atLeastAtMost_iff b_eq closed_segment_eq_real_ivl1
              less_eq_real_def of_real_0 of_real_closed_segment z_eq)
          \<comment> \<open>Step 4: @{term z} is on the curve, so @{term "z \<notin> inside (path_image g)"}. Hence @{term "z \<notin> open_segment 0 b"}.
       Combined with @{term "z \<in> closed_segment 0 b"}, we get $z = 0 \vee z = b$.\<close>
        have "z \<notin> inside (path_image g)"
          using inside_no_overlap z_on by blast
        then have "z \<notin> open_segment 0 b"
          using seg_inside by blast
        then show False
          using non z_in_seg by (auto simp: closed_segment_eq_open)
      qed

\<comment> \<open>@{term "Im \<circ> g"} doesn't change sign on either arc: if it did, the IVT gives a real point
     in the interior of the arc, contradicting \<open>real_on_curve\<close> and injectivity.\<close>
      have no_cross: "(\<forall>s \<in> {u..v}. Im (g s) \<ge> 0) \<or> (\<forall>s \<in> {u..v}. Im (g s) \<le> 0)"
        if huv: "u < v" "{u..v} \<subseteq> {0..1}" and hinj: "inj_on g {u..v}"
          and hend: "Im (g u) = 0" "Im (g v) = 0" for u v
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then obtain s\<^sub>1 s\<^sub>2 where s1: "s\<^sub>1 \<in> {u..v}" "Im (g s\<^sub>1) > 0"
          and s2: "s\<^sub>2 \<in> {u..v}" "Im (g s\<^sub>2) < 0"
          by (meson linorder_not_le)
        have cont_uv: "continuous_on {u..v} g"
          using cont_g continuous_on_subset huv(2) by blast
            \<comment> \<open>The IVT gives $s \in (u,v)$ with $Im(g\,s) = 0$\<close>
        obtain s where s: "s \<in> {u..v}" "Im (g s) = 0" "s \<noteq> u" "s \<noteq> v"
        proof (cases "s\<^sub>1 \<le> s\<^sub>2")
          case True
          obtain s where hs: "s \<in> {s\<^sub>1..s\<^sub>2}" "Im (g s) = 0"
            using ivt_decreasing_component_on_1[OF True, of g \<i> 0] continuous_on_subset[OF cont_uv] s1 s2
            by (force simp: complex_inner_i_right)
          then obtain "s \<noteq> u" "s \<noteq> v" "s \<in> {u..v}"
            using s1 s2 by force
          then show thesis using that hs by blast
        next
          case False
          then have le: "s\<^sub>2 \<le> s\<^sub>1" by linarith
          obtain s where hs: "s \<in> {s\<^sub>2..s\<^sub>1}" "Im (g s) = 0"
            using ivt_increasing_component_on_1[OF le, of g \<i> 0] continuous_on_subset[OF cont_uv] s1 s2
            by (force simp: complex_inner_i_right)
          then obtain  "s \<noteq> u" "s \<noteq> v" "s \<in> {u..v}"
            using s1 s2 by force
          then show thesis using that hs by blast
        qed

        \<comment> \<open>$g\,s$ is on the path, so @{term "g s \<in> {0, b}"} by \<open>real_on_curve\<close>\<close>
        have "g s = 0 \<or> g s = b" using real_on_curve s(2)
          by (metis subsetD imageI path_image_def s(1) that(2))
        \<comment> \<open>But @{term g} is injective on $\{u..v\}$ and $s \in (u,v)$, so $g\,s \neq g\,u$ and $g\,s \neq g\,v$\<close>
        moreover have "g s \<noteq> g u" "g s \<noteq> g v"
          using inj_onD[OF hinj] s by auto
            \<comment> \<open>Since @{term "{g u, g v} \<subseteq> {0, b}"}, this gives the contradiction\<close>
        moreover have "g u \<in> {0, b}" "g v \<in> {0, b}"
          using real_on_curve hend huv by (auto simp: path_image_def subset_iff)
        ultimately show False
          using \<open>u < v\<close> inj_onD [OF hinj] by (auto simp: order_class.less_le)
      qed
      have no_cross_1: "(\<forall>s \<in> {0..t}. Im (g s) \<ge> 0) \<or> (\<forall>s \<in> {0..t}. Im (g s) \<le> 0)"
        using no_cross[of 0 t] arc_inj_on[of 0 t] t g0 Im_b by auto
      have no_cross_2: "(\<forall>s \<in> {t..1}. Im (g s) \<ge> 0) \<or> (\<forall>s \<in> {t..1}. Im (g s) \<le> 0)"
        using no_cross[of t 1] arc_inj_on[of t 1] t g1 Im_b by auto
      \<comment> \<open>Eliminate the case where both arcs are on the same side of the real axis.\<close>
      have not_all_above: "\<not> (path_image g \<subseteq> {z. 0 \<le> Im z})"
        using Reb assms not_all_above real_on_curve t Im_b by blast
      have not_all_below: "\<not> (path_image g \<subseteq> {z. Im z \<le> 0})"
        using CR.not_all_above using g g0 g1 assms Reb real_on_curve
        by (force simp add: gop_def  path_image_compose)
          \<comment> \<open>With the elimination, the 4-way case split from \<open>no_cross_1\<close>/\<open>no_cross_2\<close> reduces to two\<close>
      have "path_image g = g ` {0..t} \<union> g ` {t..1}"
        unfolding path_image_def using t
        by (metis image_Un ivl_disj_un_two_touch(4) less_eq_real_def)
      with no_cross_1 no_cross_2 not_all_above not_all_below
      show ?thesis by (auto simp: image_subset_iff)
    qed
  qed
  then show ?thesis
    using assms split_case split_case' t by blast
qed


subsection \<open>Conclusion of Green's theorem and the signed area formula for a convex closed curve.\<close>

lemma Green_invariant:
  assumes "\<And>g g' U b. Green g g' U 0 b \<Longrightarrow> Green_concl g g'"
  shows "Green_concl g g'"
proof -
  have *: "Green_concl ((\<lambda>x. -a+x) \<circ> g) g'"
  proof (intro assms)
    show "Green ((+) (- a) \<circ> g) g' U 0 (-a+b)"
    proof
      show "simple_path ((+) (- a) \<circ> g)"
        by (simp add: g simple_path_translation_eq)
      show "pathstart ((+) (- a) \<circ> g) = 0"
        by (simp add: g pathstart_compose)
      show "pathfinish ((+) (- a) \<circ> g) = 0"
        by (simp add: g pathfinish_compose)
      show "- a + b \<in> path_image ((+) (- a) \<circ> g)"
        by (simp add: b path_image_translation)
       show "dist 0 (- a + b) = diameter (path_image ((+) (- a) \<circ> g))"
         by (metis add.commute dab diameter_translation dist_0_norm dist_commute dist_norm path_image_compose pth_2)
      show "convex (inside (path_image ((+) (- a) \<circ> g)))"
        by (metis path_image_translation inside_translation convex_translation_eq conv)
      show "absolutely_continuous_on {0..1} ((+) (- a) \<circ> g)"
        by (metis (no_types, lifting) ext absolutely_continuous_on_add absolutely_continuous_on_const cont o_apply)
    next
      fix t
      assume "t \<in> {0..1} - U"
      then show "((+) (- a) \<circ> g has_vector_derivative g' t) (at t)"
        using has_vector_derivative_shift vder by blast
    qed (use b U in auto)
  qed
  let ?G = "\<lambda>t. Re (g' t) * Im (g t)"
  show ?thesis
    unfolding Green_concl_def
  proof (intro conjI f_abs_int)
    have meas_eq: "measure lebesgue (inside (path_image ((+) (- a) \<circ> g)))
                 = measure lebesgue (inside (path_image g))"
      by (metis path_image_translation inside_translation measure_translation)
    have "(g' has_integral (g 1 - g 0)) {0..1}"
      using fundamental_theorem_of_calculus_absolutely_continuous[OF U _ cont, of g']
      by (metis zero_le_one vder has_vector_derivative_at_within)
    then have int_g': "(g' has_integral 0) {0..1}" 
      using g by (simp add: pathstart_def pathfinish_def)
    have Re_has_int: "((\<lambda>t. Re (g' t)) has_integral 0) {0..1}"
      using has_integral_Re[OF int_g'] by simp
    have Ima_has_int: "((\<lambda>t. Im a * Re (g' t)) has_integral 0) {0..1}"
      using has_integral_mult_right[OF Re_has_int] by simp
    have ai_translated: "(\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t)) integrable_on {0..1}"
      using * unfolding Green_concl_def absolutely_integrable_on_def by auto
    have Ima_integrable: "(\<lambda>t. Im a * Re (g' t)) integrable_on {0..1}"
      using Ima_has_int by (rule has_integral_integrable)
    have "integral {0..1} ?G
          = integral {0..1} (\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t) + Im a * Re (g' t))"
      by (simp add: o_def plus_complex.sel uminus_complex.sel algebra_simps)
    also have "\<dots> = integral {0..1} (\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t))"
      using integral_add[OF ai_translated has_integral_integrable] 
        Ima_has_int integral_unique[OF Ima_has_int] by force
    finally show "\<bar>integral {0..1} ?G\<bar> = Sigma_Algebra.measure lebesgue (inside (path_image g))"
      using * meas_eq unfolding Green_concl_def by auto
  qed
qed

theorem area_theorem:
  obtains "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {0..1}"
    and "\<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> =
      measure lebesgue (inside (path_image g))"
  using Green.Green_area_zero Green_concl_def Green_invariant by blast

end

end
