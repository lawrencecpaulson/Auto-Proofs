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
    hence eq_int: "interior (convex hull (path_image g)) = inside (path_image g)"
      using int_inside by blast
    \<comment> \<open>frontier (convex hull) = convex hull - interior (convex hull) = convex hull - inside\<close>
    have "frontier (convex hull (path_image g)) =
      convex hull (path_image g) - inside (path_image g)"
      using closed_hull by (simp add: frontier_def eq_int)
    also have "\<dots> \<subseteq> path_image g"
    proof -
      have "convex hull (path_image g) \<subseteq> inside (path_image g) \<union> path_image g"
        by (metis Un_commute assms(1,2) closed_simple_path_image closure_inside_subset
            convex_convex_hull convex_hull_eq_closure_inside convex_interior eq_int)
      thus ?thesis by blast
    qed
    finally show ?thesis .
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

theorem wirtinger_inequality:
  fixes f f' :: "real \<Rightarrow> real"
  assumes "\<And>x. x \<in> {0..2*pi} \<Longrightarrow>
    (f' has_integral (f x - f 0)) {0..x}"
    and "f (2*pi) = f 0"
    and "(f has_integral 0) {0..2*pi}"
    and "(\<lambda>x. (f' x)\<^sup>2) integrable_on {0..2*pi}"
  shows "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
    and "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    and "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2) \<Longrightarrow>
      \<exists>c a. \<forall>x \<in> {0..2*pi}. f x = c * sin (x - a)"
  sorry 

theorem scaled_wirtinger_inequality:
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
      measure {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
  sorry 

lemma area_above_arclet:
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
  assumes "u \<le> v"
    and "Re (g v) \<le> Re (g u)"
    and "absolutely_continuous_on g {u..v}"
    and "g ` {u..v} \<subseteq> {z. Im z \<le> 0}"
    and "inj_on g {u..v}"
    and "\<And>x y. x \<in> g ` {u..v} \<Longrightarrow> y \<in> g ` {u..v} \<Longrightarrow> Re x = Re y \<Longrightarrow> x = y"
    and "negligible S"
    and "\<And>t. t \<in> {u..v} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
    and "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
  sorry

theorem green_area_theorem:
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
    and a b :: "complex"
  assumes "simple_path g" "pathstart g = a" "pathfinish g = a"
    and "b \<in> path_image g" "Re a < Re b" "Im a = Im b"
    and "dist a b = diameter (path_image g)"
    and "convex (inside (path_image g))"
    and "absolutely_continuous_on g {0..1}"
    and "negligible U"
    and "\<And>t. t \<in> {0..1} - U \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {0..1}"
    and "\<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> =
      measure (inside (path_image g))"
  sorry

section \<open>Part 3: Isoperimetric theorem for convex curves\<close>

theorem isoperimetric_theorem_convex:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "convex (inside (path_image g))"
    "path_length g = L"
  shows "measure (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
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
    measure (inside (path_image g)) < measure (inside (path_image h))"
  sorry

section \<open>Part 5: The isoperimetric theorem\<close>

theorem isoperimetric_theorem:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "path_length g = L"
  shows "measure (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
      \<exists>a r. path_image g = sphere a r"
  sorry

end
