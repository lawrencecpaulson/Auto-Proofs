theory Body_Overlap
  imports Boundary_Integration
begin

lemma negligible_product_face:
  "negligible {p::real \<times> (real ^ 'n::finite).
    fst p = 0}"
proof -
  have nonzero: "(1::real, 0::real ^ 'n) \<noteq> 0"
    by (simp add: zero_prod_def)
  have plane: "{p::real \<times> (real ^ 'n).
      (1::real, 0::real ^ 'n) \<bullet> p = 0} =
    {p. fst p = 0}"
    by (auto simp: inner_Pair_0)
  show ?thesis
    using negligible_hyperplane[of "(1::real, 0::real ^ 'n)" 0]
      nonzero
    by (simp only: plane) simp
qed

context positively_oriented_C2_halfspace_atlas
begin

lemma body_chart_integral_eq_interior:
  fixes f :: "real \<times> (real ^ 'n) \<Rightarrow> real"
  assumes i: "i \<in> I"
  shows "integral (C i) f =
    integral (C i \<inter> open_halfspace) f"
proof -
  have C_half: "C i \<subseteq> closed_halfspace"
    by (rule halfspace_chart.codomain_subset_halfspace
      [OF chart[OF i]])
  have negligible_diff: "negligible
      {x \<in> C i - (C i \<inter> open_halfspace).
        f x \<noteq> 0}"
    by (rule negligible_subset[OF negligible_product_face])
       (use C_half in
         \<open>auto simp: closed_halfspace_def
           open_halfspace_def\<close>)
  have negligible_reverse: "negligible
      {x \<in> (C i \<inter> open_halfspace) - C i.
        f x \<noteq> 0}"
  proof -
    have "{x \<in> (C i \<inter> open_halfspace) - C i.
        f x \<noteq> 0} = {}"
      by blast
    then show ?thesis
      by (simp only: negligible_empty)
  qed
  show ?thesis
    by (rule integral_spike_set
      [where S="C i" and T="C i \<inter> open_halfspace"
        and f=f, OF negligible_diff negligible_reverse])
qed

definition body_overlap ::
    "'i \<Rightarrow> 'i \<Rightarrow>
      (real \<times> (real ^ 'n)) set"
  where "body_overlap i j =
    coordinate_overlap i j \<inter> open_halfspace"

lemma body_overlap_open:
  assumes i: "i \<in> I" and j: "j \<in> I"
  shows "open (body_overlap i j)"
proof -
  obtain U where U: "open U"
    "coordinate_overlap i j = closed_halfspace \<inter> U"
    using coordinate_overlap_open[OF i j]
    by (auto simp: openin_open)
  have sub: "open_halfspace \<subseteq>
      (closed_halfspace ::
        (real \<times> (real ^ 'n)) set)"
    by (auto simp: open_halfspace_def
      closed_halfspace_def)
  have overlap_eq: "((closed_halfspace ::
      (real \<times> (real ^ 'n)) set) \<inter> U)
      \<inter> open_halfspace = open_halfspace \<inter> U"
    using sub
    by (auto simp only: set_eq_iff Int_iff subset_iff)
  have "body_overlap i j = open_halfspace \<inter> U"
    by (simp only: body_overlap_def U(2)
      overlap_eq)
  then show ?thesis
    using U(1) open_open_halfspace by auto
qed

lemma coordinate_transition_body_overlap:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and x: "x \<in> body_overlap i j"
  shows "coordinate_transition i j x
    \<in> body_overlap j i"
proof -
  let ?p = "from_chart i x"
  have overlap: "x \<in> coordinate_overlap i j"
    and positive_x: "0 < fst x"
    using x by (auto simp: body_overlap_def
      open_halfspace_def)
  have xi: "x \<in> C i" and pj: "?p \<in> D j"
    using overlap by (auto simp: coordinate_overlap_def)
  have pi: "?p \<in> D i"
    using halfspace_chart.inverse_image[OF chart[OF i]]
      xi by auto
  have chart_i: "to_chart i ?p = x"
    by (rule halfspace_chart.from_to[OF chart[OF i] xi])
  have not_boundary: "?p \<notin> boundary_carrier"
    using boundary_chart_classify[OF i pi]
      chart_i positive_x by auto
  have overlap_ji: "coordinate_transition i j x
      \<in> coordinate_overlap j i"
    by (rule coordinate_transition_inverse(1)
      [OF i j overlap])
  have chart_j: "coordinate_transition i j x =
      to_chart j ?p"
    by (simp add: coordinate_transition_def)
  have zC: "coordinate_transition i j x \<in> C j"
    using overlap_ji by (auto simp: coordinate_overlap_def)
  have nonzero: "fst (coordinate_transition i j x)
      \<noteq> 0"
    using boundary_chart_classify[OF j pj]
      not_boundary chart_j by auto
  have nonnegative: "0 \<le>
      fst (coordinate_transition i j x)"
    using halfspace_chart.codomain_subset_halfspace
      [OF chart[OF j]] zC
    by (auto simp: closed_halfspace_def)
  show ?thesis
    using overlap_ji nonzero nonnegative
    by (auto simp: body_overlap_def
      open_halfspace_def)
qed

lemma coordinate_transition_body_image:
  assumes i: "i \<in> I" and j: "j \<in> I"
  shows "coordinate_transition i j `
    body_overlap i j = body_overlap j i"
proof
  show "coordinate_transition i j `
      body_overlap i j \<subseteq> body_overlap j i"
    using coordinate_transition_body_overlap[OF i j]
    by auto
  show "body_overlap j i \<subseteq>
      coordinate_transition i j ` body_overlap i j"
  proof
    fix z
    assume z: "z \<in> body_overlap j i"
    have zji: "z \<in> coordinate_overlap j i"
      using z by (simp add: body_overlap_def)
    have x: "coordinate_transition j i z
        \<in> body_overlap i j"
      by (rule coordinate_transition_body_overlap
        [OF j i z])
    have eq: "coordinate_transition i j
      (coordinate_transition j i z) = z"
      by (rule coordinate_transition_inverse(2)
        [OF j i zji])
    show "z \<in> coordinate_transition i j `
      body_overlap i j"
    proof -
      have "coordinate_transition i j
          (coordinate_transition j i z)
          \<in> coordinate_transition i j `
            body_overlap i j"
        by (rule imageI[OF x])
      then show ?thesis
        by (simp only: eq)
    qed
  qed
qed

lemma coordinate_transition_body_inj:
  assumes i: "i \<in> I" and j: "j \<in> I"
  shows "inj_on (coordinate_transition i j)
    (body_overlap i j)"
proof (rule inj_onI)
  fix x y
  assume x: "x \<in> body_overlap i j"
    and y: "y \<in> body_overlap i j"
    and eq: "coordinate_transition i j x =
      coordinate_transition i j y"
  have xij: "x \<in> coordinate_overlap i j"
    and yij: "y \<in> coordinate_overlap i j"
    using x y by (auto simp: body_overlap_def)
  have inv_x: "coordinate_transition j i
      (coordinate_transition i j x) = x"
    by (rule coordinate_transition_inverse(2)
      [OF i j xij])
  have inv_y: "coordinate_transition j i
      (coordinate_transition i j y) = y"
    by (rule coordinate_transition_inverse(2)
      [OF i j yij])
  show "x = y"
  proof -
    have "x = coordinate_transition j i
        (coordinate_transition i j x)"
      by (simp only: inv_x)
    also have "\<dots> = coordinate_transition j i
        (coordinate_transition i j y)"
      by (simp only: eq)
    also have "\<dots> = y"
      by (simp only: inv_y)
    finally show ?thesis .
  qed
qed

lemma body_chart_integral_localized:
  fixes alpha :: "real \<times> (real ^ 'n) \<Rightarrow> real"
  assumes i: "i \<in> I"
    and zero: "\<And>x. x \<in> C i \<inter> open_halfspace
      \<Longrightarrow> x \<notin> body_overlap i j
      \<Longrightarrow> alpha x = 0"
  shows "integral (C i) alpha =
    integral (body_overlap i j) alpha"
proof -
  let ?E = "C i \<inter> open_halfspace"
  let ?S = "body_overlap i j"
  have subset: "?S \<subseteq> ?E"
    by (auto simp: body_overlap_def
      coordinate_overlap_def)
  have "integral (C i) alpha = integral ?E alpha"
    by (rule body_chart_integral_eq_interior[OF i])
  also have "\<dots> =
    integral ?E (\<lambda>x. if x \<in> ?S then alpha x else 0)"
    by (rule integral_cong) (use zero in auto)
  also have "\<dots> = integral ?S alpha"
    using subset
    by (simp add: integral_restrict_Int inf.absorb1)
  finally show ?thesis .
qed

theorem body_overlap_integral:
  fixes alpha beta :: "real \<times> (real ^ 'n) \<Rightarrow> real"
  assumes i: "i \<in> I" and j: "j \<in> I"
    and smooth: "Ck_on 2 (coordinate_transition i j)
      (body_overlap i j)"
    and positive: "\<And>x. x \<in> body_overlap i j
      \<Longrightarrow> 0 < eucl.det
        (frechet_derivative (coordinate_transition i j)
          (at x))"
    and integrable: "beta absolutely_integrable_on
      body_overlap j i"
    and compatible: "\<And>x. x \<in> body_overlap i j
      \<Longrightarrow> alpha x =
        eucl.det (frechet_derivative
          (coordinate_transition i j) (at x)) *
        beta (coordinate_transition i j x)"
  shows "integral (body_overlap i j) alpha =
    integral (body_overlap j i) beta"
proof -
  let ?S = "body_overlap i j"
  let ?g = "coordinate_transition i j"
  have measurable: "?S \<in> sets lebesgue"
    using body_overlap_open[OF i j]
    by (metis borel_open sets_lborel sets_completionI_sets)
  have smooth1: "Ck_on (Suc 0) ?g ?S"
    by (rule Ck_on_mono[OF smooth]) simp
  have diff: "?g differentiable (at x)" if x: "x \<in> ?S"
    for x
    using Ck_on_Suc_iff[of 0 ?g ?S, THEN iffD1,
      OF smooth1] x by blast
  have der: "(?g has_derivative
      frechet_derivative ?g (at x))
      (at x within ?S)" if x: "x \<in> ?S" for x
    using diff[OF x]
    by (simp add: frechet_derivative_works
      has_derivative_at_withinI)
  have int_image: "beta absolutely_integrable_on
      (?g ` ?S)"
    using integrable
    by (simp only: coordinate_transition_body_image
      [OF i j])
  have change: "integral (?g ` ?S) beta =
    integral ?S (\<lambda>x.
      \<bar>eucl.det (frechet_derivative ?g (at x))\<bar> *\<^sub>R
        beta (?g x))"
  proof (rule integral_change_of_variables
      [where f=beta and g="coordinate_transition i j"
        and g'="\<lambda>x. frechet_derivative
          (coordinate_transition i j) (at x)"
        and S="body_overlap i j"])
    show "?S \<in> sets lebesgue"
      by (rule measurable)
    show "\<And>x. x \<in> ?S \<Longrightarrow>
      (?g has_derivative frechet_derivative ?g (at x))
        (at x within ?S)"
      by (rule der)
    show "inj_on ?g ?S"
      by (rule coordinate_transition_body_inj[OF i j])
    show "beta absolutely_integrable_on (?g ` ?S) \<or>
      (\<lambda>x. \<bar>eucl.det
        (frechet_derivative ?g (at x))\<bar> *\<^sub>R
        beta (?g x)) absolutely_integrable_on ?S"
      using int_image by (rule disjI1)
  qed
  have eq: "integral ?S alpha =
    integral ?S (\<lambda>x.
      \<bar>eucl.det (frechet_derivative ?g (at x))\<bar> *\<^sub>R
        beta (?g x))"
    by (rule integral_cong)
       (use compatible positive in
        \<open>auto simp: abs_of_pos\<close>)
  show ?thesis
    using change eq
    by (simp only: coordinate_transition_body_image
      [OF i j])
qed

theorem body_localized_chart_integral_eq:
  fixes alpha beta :: "real \<times> (real ^ 'n) \<Rightarrow> real"
  assumes i: "i \<in> I" and j: "j \<in> I"
    and smooth: "Ck_on 2 (coordinate_transition i j)
      (body_overlap i j)"
    and positive: "\<And>x. x \<in> body_overlap i j
      \<Longrightarrow> 0 < eucl.det
        (frechet_derivative (coordinate_transition i j)
          (at x))"
    and integrable: "beta absolutely_integrable_on
      body_overlap j i"
    and compatible: "\<And>x. x \<in> body_overlap i j
      \<Longrightarrow> alpha x =
        eucl.det (frechet_derivative
          (coordinate_transition i j) (at x)) *
        beta (coordinate_transition i j x)"
    and zero_i: "\<And>x. x \<in> C i \<inter> open_halfspace
      \<Longrightarrow> x \<notin> body_overlap i j
      \<Longrightarrow> alpha x = 0"
    and zero_j: "\<And>x. x \<in> C j \<inter> open_halfspace
      \<Longrightarrow> x \<notin> body_overlap j i
      \<Longrightarrow> beta x = 0"
  shows "integral (C i) alpha = integral (C j) beta"
proof -
  have left: "integral (C i) alpha =
    integral (body_overlap i j) alpha"
    by (rule body_chart_integral_localized[OF i zero_i])
  have change: "integral (body_overlap i j) alpha =
    integral (body_overlap j i) beta"
    by (rule body_overlap_integral
      [OF i j smooth positive integrable compatible])
  have right: "integral (C j) beta =
    integral (body_overlap j i) beta"
    by (rule body_chart_integral_localized[OF j zero_j])
  show ?thesis
    using left change right by simp
qed

end

end
