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
    show \<open>\<And>x. x \<in> {0..2*pi} \<Longrightarrow> norm (f' x) \<le> 1 + (f' x)\<^sup>2\<close>
    proof -
      fix x :: real
      have \<open>0 \<le> (1 - f' x)\<^sup>2\<close> and \<open>0 \<le> (1 + f' x)\<^sup>2\<close>
        by (auto simp: power2_eq_square)
      then show \<open>norm (f' x) \<le> 1 + (f' x)\<^sup>2\<close>
        by (auto simp: power2_eq_square abs_le_iff real_norm_def algebra_simps)
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
      proof cases
        case 1
        then have "0 \<le> g pi" using geq by linarith
        then show ?thesis using mem_is_interval_1_I [OF iv g0 gpi, of 0] 1 by auto
      next
        case 2
        then have "0 \<le> g 0" using geq by linarith
        then show ?thesis using mem_is_interval_1_I [OF iv gpi g0, of 0] 2 by auto
      qed
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
