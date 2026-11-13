theory Boundary_Integration
  imports
    Boundary_Charts
    Oriented_Integration
begin

context positively_oriented_C2_halfspace_atlas
begin

lemma compact_boundary_restriction:
  assumes compact: "compact K"
    and K_M: "K \<subseteq> M"
  shows "compact (K \<inter> boundary_carrier)"
proof -
  obtain T where T: "closed T"
    "boundary_carrier = M \<inter> T"
    using boundary_carrier_closed
    by (auto simp: closedin_closed)
  have eq: "K \<inter> boundary_carrier = K \<inter> T"
    using T(2) K_M by auto
  show ?thesis
    unfolding eq
    by (rule compact_Int_closed[OF compact T(1)])
qed

lemma boundary_carrier_locally_compact:
  "locally_compact_space (top_of_set boundary_carrier)"
proof (unfold locally_compact_space_def, intro ballI)
  fix p
  assume p: "p \<in> topspace (top_of_set boundary_carrier)"
  obtain i V K where V: "openin (top_of_set boundary_carrier) V"
    "p \<in> V" "compact K" "V \<subseteq> K"
    "K \<subseteq> boundary_carrier \<inter> D i"
    by (rule boundary_compact_relative_neighborhood)
       (use p in auto)
  have "compactin (top_of_set boundary_carrier) K"
    using V(3,5)
    by (simp add: compactin_subtopology)
  then show "\<exists>U K.
      openin (top_of_set boundary_carrier) U \<and>
      compactin (top_of_set boundary_carrier) K \<and>
      p \<in> U \<and> U \<subseteq> K"
    using V by blast
qed

definition boundary_top_coeff_compatible ::
    "('i \<Rightarrow> real ^ 'n \<Rightarrow> real) \<Rightarrow> bool"
  where "boundary_top_coeff_compatible alpha \<longleftrightarrow>
    (\<forall>i\<in>I. \<forall>j\<in>I. \<forall>y\<in>boundary_overlap i j.
      alpha i y =
        pull_top (boundary_transition i j) (alpha j) y)"

definition boundary_form_support ::
    "('i \<Rightarrow> real ^ 'n \<Rightarrow> real) \<Rightarrow> 'a set"
  where "boundary_form_support alpha =
    {p\<in>boundary_carrier. \<exists>i\<in>I.
      p \<in> D i \<and> alpha i (snd (to_chart i p)) \<noteq> 0}"

definition weight_boundary_coeff ::
    "('a \<Rightarrow> real) \<Rightarrow>
      ('i \<Rightarrow> real ^ 'n \<Rightarrow> real) \<Rightarrow>
      'i \<Rightarrow> real ^ 'n \<Rightarrow> real"
  where "weight_boundary_coeff rho alpha i y =
    rho (from_chart i (0,y)) * alpha i y"

lemma weight_boundary_coeff_compatible:
  assumes compatible: "boundary_top_coeff_compatible alpha"
  shows "boundary_top_coeff_compatible
    (weight_boundary_coeff rho alpha)"
proof (unfold boundary_top_coeff_compatible_def, intro ballI)
  fix i j y
  assume i: "i \<in> I" and j: "j \<in> I"
    and y: "y \<in> boundary_overlap i j"
  have coeff: "alpha i y =
    pull_top (boundary_transition i j) (alpha j) y"
    using compatible i j y
    by (auto simp: boundary_top_coeff_compatible_def)
  have point: "from_chart j
      (0,boundary_transition i j y) =
    from_chart i (0,y)"
    by (rule boundary_transition_chart_point[OF i j y])
  show "weight_boundary_coeff rho alpha i y =
    pull_top (boundary_transition i j)
      (weight_boundary_coeff rho alpha j) y"
    using coeff point
    by (simp add: weight_boundary_coeff_def
      pull_top_def algebra_simps)
qed

lemma boundary_form_support_chart:
  assumes compatible: "boundary_top_coeff_compatible alpha"
    and i: "i \<in> I" and p: "p \<in> boundary_carrier \<inter> D i"
  shows "p \<in> boundary_form_support alpha \<longleftrightarrow>
    alpha i (snd (to_chart i p)) \<noteq> 0"
proof
  let ?y = "snd (to_chart i p)"
  have pD: "p \<in> D i" using p by auto
  have i0: "fst (to_chart i p) = 0"
    using p boundary_chart_classify[OF i pD] by auto
  have xy: "(0,?y) = to_chart i p"
    using i0 by (cases "to_chart i p") auto
  have yi: "(0,?y) \<in> C i"
    using halfspace_chart.chart_image[OF chart[OF i]]
      pD xy by auto
  have pfrom: "from_chart i (0,?y) = p"
    using halfspace_chart.to_from[OF chart[OF i] pD]
      xy by simp
  assume supp: "p \<in> boundary_form_support alpha"
  then obtain j where j: "j \<in> I" "p \<in> D j"
    "alpha j (snd (to_chart j p)) \<noteq> 0"
    by (auto simp: boundary_form_support_def)
  have overlap: "?y \<in> boundary_overlap i j"
    using yi pfrom j(2)
    by (simp add: boundary_overlap_def halfspace_face_def)
  have trans: "boundary_transition i j ?y =
      snd (to_chart j p)"
    using pfrom by (simp add: boundary_transition_def)
  have coeff: "alpha i ?y =
      Determinants.det
        (jacobian (boundary_transition i j) (at ?y)) *
      alpha j (snd (to_chart j p))"
    using compatible i j(1) overlap trans
    by (auto simp: boundary_top_coeff_compatible_def
      pull_top_def)
  have positive: "0 < Determinants.det
      (jacobian (boundary_transition i j) (at ?y))"
    by (rule positive_boundary_transition[OF i j(1) overlap])
  show "alpha i ?y \<noteq> 0"
    using coeff positive j(3) by simp
next
  assume nonzero: "alpha i (snd (to_chart i p)) \<noteq> 0"
  show "p \<in> boundary_form_support alpha"
    using p i nonzero
    by (auto simp: boundary_form_support_def)
qed

lemma boundary_chart_coeff_absolutely_integrable:
  assumes compatible: "boundary_top_coeff_compatible alpha"
    and i: "i \<in> I"
    and compact: "compact K"
    and Kchart: "K \<subseteq> boundary_carrier \<inter> D i"
    and support: "boundary_form_support alpha \<subseteq> K"
    and continuous: "continuous_on (halfspace_face (C i))
      (alpha i)"
  shows "alpha i absolutely_integrable_on
    halfspace_face (C i)"
proof -
  let ?b = "\<lambda>p. snd (to_chart i p)"
  let ?E = "halfspace_face (C i)"
  have homeo: "homeomorphism
      (boundary_carrier \<inter> D i) ?E
      ?b (\<lambda>y. from_chart i (0,y))"
    by (rule boundary_restricted_homeomorphism[OF i])
  have cont: "continuous_on K ?b"
    by (rule continuous_on_subset
      [OF homeomorphism_cont1[OF homeo] Kchart])
  have compact_image: "compact (?b ` K)"
    by (rule compact_continuous_image[OF cont compact])
  have subset_image: "?b ` K \<subseteq> ?E"
    using Kchart homeomorphism_image1[OF homeo] by auto
  have continuous_image: "continuous_on (?b ` K) (alpha i)"
    by (rule continuous_on_subset[OF continuous subset_image])
  have zero: "alpha i y = 0"
    if y: "y \<in> ?E" "y \<notin> ?b ` K" for y
  proof -
    let ?p = "from_chart i (0,y)"
    have p: "?p \<in> boundary_carrier \<inter> D i"
      using homeomorphism_image2[OF homeo] y(1)
      by auto
    have py: "?b ?p = y"
      by (rule homeomorphism_apply2[OF homeo y(1)])
    have pnot: "?p \<notin> K"
      using y(2) py by (metis imageI)
    have "?p \<notin> boundary_form_support alpha"
      using support pnot by blast
    then show ?thesis
      using boundary_form_support_chart[OF compatible i p] py
      by auto
  qed
  show ?thesis
    by (rule absolutely_integrable_compact_support
      [OF compact_image continuous_image subset_image zero])
qed

lemma boundary_form_support_weight:
  shows "boundary_form_support
      (weight_boundary_coeff rho alpha)
    \<subseteq> boundary_form_support alpha \<inter>
      {p\<in>boundary_carrier. rho p \<noteq> 0}"
proof
  fix p
  assume p: "p \<in> boundary_form_support
    (weight_boundary_coeff rho alpha)"
  then obtain i where i: "i \<in> I" "p \<in> D i"
    "weight_boundary_coeff rho alpha i
      (snd (to_chart i p)) \<noteq> 0"
    by (auto simp: boundary_form_support_def)
  have pB: "p \<in> boundary_carrier"
    using p by (simp add: boundary_form_support_def)
  have i0: "fst (to_chart i p) = 0"
    using boundary_chart_classify[OF i(1,2)] pB by simp
  have pfrom: "from_chart i
      (0,snd (to_chart i p)) = p"
  proof -
    have "(0,snd (to_chart i p)) = to_chart i p"
      using i0 by (cases "to_chart i p") auto
    then show ?thesis
      using halfspace_chart.to_from[OF
        chart[OF i(1)] i(2)]
      by simp
  qed
  have nz: "rho p * alpha i
      (snd (to_chart i p)) \<noteq> 0"
    using i(3) pfrom
    by (simp add: weight_boundary_coeff_def)
  show "p \<in> boundary_form_support alpha \<inter>
      {p\<in>boundary_carrier. rho p \<noteq> 0}"
    using pB i nz by (auto simp: boundary_form_support_def)
qed

lemma weight_boundary_coeff_continuous:
  assumes i: "i \<in> I"
    and rho_cont: "continuous_on boundary_carrier rho"
    and alpha_cont: "continuous_on
      (halfspace_face (C i)) (alpha i)"
  shows "continuous_on (halfspace_face (C i))
    (weight_boundary_coeff rho alpha i)"
proof -
  let ?E = "halfspace_face (C i)"
  have homeo: "homeomorphism
      (boundary_carrier \<inter> D i) ?E
      (\<lambda>p. snd (to_chart i p))
      (\<lambda>y. from_chart i (0,y))"
    by (rule boundary_restricted_homeomorphism[OF i])
  have inverse_cont: "continuous_on ?E
      (\<lambda>y. from_chart i (0,y))"
    by (rule homeomorphism_cont2[OF homeo])
  have image: "(\<lambda>y. from_chart i (0,y)) ` ?E
      \<subseteq> boundary_carrier"
    using homeomorphism_image2[OF homeo] by auto
  have rho_chart: "continuous_on ?E
      (\<lambda>y. rho (from_chart i (0,y)))"
    by (rule continuous_on_compose2
      [OF rho_cont inverse_cont image])
  show ?thesis
    using rho_chart alpha_cont
    by (auto simp: weight_boundary_coeff_def
      intro!: continuous_intros)
qed

lemma boundary_weight_absolutely_integrable:
  assumes compatible: "boundary_top_coeff_compatible alpha"
    and i: "i \<in> I"
    and compactK: "compact K"
    and supportK: "boundary_form_support alpha \<subseteq> K"
    and closedL: "closed L"
    and supportL: "{p\<in>boundary_carrier. rho p \<noteq> 0}
      \<subseteq> L"
    and local: "K \<inter> L \<subseteq> boundary_carrier \<inter> D i"
    and rho_cont: "continuous_on boundary_carrier rho"
    and alpha_cont: "continuous_on
      (halfspace_face (C i)) (alpha i)"
  shows "weight_boundary_coeff rho alpha i
    absolutely_integrable_on halfspace_face (C i)"
proof -
  have compactKL: "compact (K \<inter> L)"
    by (rule compact_Int_closed[OF compactK closedL])
  have support: "boundary_form_support
      (weight_boundary_coeff rho alpha) \<subseteq> K \<inter> L"
    using boundary_form_support_weight[of rho alpha]
      supportK supportL by auto
  have compatible': "boundary_top_coeff_compatible
      (weight_boundary_coeff rho alpha)"
    by (rule weight_boundary_coeff_compatible[OF compatible])
  have cont: "continuous_on (halfspace_face (C i))
      (weight_boundary_coeff rho alpha i)"
    using weight_boundary_coeff_continuous
      [where i=i and rho=rho and alpha=alpha]
      i rho_cont alpha_cont by blast
  show ?thesis
    by (rule boundary_chart_coeff_absolutely_integrable
      [OF compatible' i compactKL local support cont])
qed

lemma boundary_transition_image:
  assumes i: "i \<in> I" and j: "j \<in> I"
  shows "boundary_transition i j ` boundary_overlap i j =
    boundary_overlap j i"
  by (rule homeomorphism_image1
    [OF boundary_transition_homeomorphism[OF i j]])

lemma boundary_transition_inj:
  assumes i: "i \<in> I" and j: "j \<in> I"
  shows "inj_on (boundary_transition i j)
    (boundary_overlap i j)"
proof (rule inj_onI)
  fix x y
  assume x: "x \<in> boundary_overlap i j"
    and y: "y \<in> boundary_overlap i j"
    and eq: "boundary_transition i j x =
      boundary_transition i j y"
  have ix: "boundary_transition j i
      (boundary_transition i j x) = x"
    by (rule homeomorphism_apply1
      [OF boundary_transition_homeomorphism[OF i j] x])
  have iy: "boundary_transition j i
      (boundary_transition i j y) = y"
    by (rule homeomorphism_apply1
      [OF boundary_transition_homeomorphism[OF i j] y])
  show "x = y" using eq ix iy by metis
qed

lemma boundary_transition_differentiable:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and y: "y \<in> boundary_overlap i j"
  shows "boundary_transition i j differentiable (at y)"
proof -
  have C2: "Ck_on 2 (boundary_transition i j)
      (boundary_overlap i j)"
    by (rule boundary_transition_C2[OF i j])
  have C1: "Ck_on (Suc 0) (boundary_transition i j)
      (boundary_overlap i j)"
    by (rule Ck_on_mono[OF C2]) simp
  show ?thesis
    using Ck_on_Suc_iff[of 0 "boundary_transition i j"
      "boundary_overlap i j", THEN iffD1, OF C1] y
    by blast
qed

theorem boundary_overlap_integral:
  fixes alpha beta :: "real ^ 'n \<Rightarrow> real"
  assumes i: "i \<in> I" and j: "j \<in> I"
    and integrable: "beta absolutely_integrable_on
      boundary_overlap j i"
    and compatible: "\<And>y. y \<in> boundary_overlap i j
      \<Longrightarrow> alpha y =
        pull_top (boundary_transition i j) beta y"
  shows "integral (boundary_overlap i j) alpha =
    integral (boundary_overlap j i) beta"
proof -
  have measurable: "boundary_overlap i j \<in> sets lebesgue"
    using boundary_overlap_open[OF i j]
    by (metis borel_open sets_lborel sets_completionI_sets)
  have integrable': "beta absolutely_integrable_on
      (boundary_transition i j ` boundary_overlap i j)"
    using integrable by (simp add: boundary_transition_image[OF i j])
  have change: "integral (boundary_overlap i j) alpha =
      integral
        (boundary_transition i j ` boundary_overlap i j) beta"
    by (rule oriented_chart_overlap_integral
      [OF measurable boundary_transition_differentiable[OF i j]
        boundary_transition_inj[OF i j]
        positive_boundary_transition[OF i j]
        integrable' compatible])
  show ?thesis
    using change by (simp add: boundary_transition_image[OF i j])
qed

lemma boundary_chart_integral_localized:
  assumes i: "i \<in> I"
    and localized: "\<And>p. p \<in> boundary_carrier
      \<Longrightarrow> rho p \<noteq> 0
      \<Longrightarrow> p \<in> D i \<inter> D j"
  shows "integral (halfspace_face (C i))
      (weight_boundary_coeff rho alpha i) =
    integral (boundary_overlap i j)
      (weight_boundary_coeff rho alpha i)"
proof -
  let ?E = "halfspace_face (C i)"
  have zero: "weight_boundary_coeff rho alpha i y = 0"
    if y: "y \<in> ?E" "y \<notin> boundary_overlap i j" for y
  proof -
    let ?p = "from_chart i (0,y)"
    have xi: "(0,y) \<in> C i"
      using y by (simp add: halfspace_face_def)
    have pi: "?p \<in> D i"
      using halfspace_chart.inverse_image[OF chart[OF i]]
        xi by auto
    have pB: "?p \<in> boundary_carrier"
      using boundary_chart_classify[OF i pi]
        halfspace_chart.from_to[OF chart[OF i] xi]
      by simp
    have pj: "?p \<notin> D j"
      using y by (simp add: boundary_overlap_def)
    have "rho ?p = 0"
      using localized[OF pB] pj by auto
    then show ?thesis
      by (simp add: weight_boundary_coeff_def)
  qed
  have subset: "boundary_overlap i j \<subseteq> ?E"
    by (auto simp: boundary_overlap_def)
  have "integral ?E (weight_boundary_coeff rho alpha i) =
    integral ?E (\<lambda>y. if y \<in> boundary_overlap i j
      then weight_boundary_coeff rho alpha i y else 0)"
    by (rule integral_cong) (use zero in auto)
  also have "\<dots> =
    integral (boundary_overlap i j)
      (weight_boundary_coeff rho alpha i)"
    using subset by (simp add: integral_restrict_Int inf.absorb1)
  finally show ?thesis .
qed

lemma boundary_localized_chart_integral_eq:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and compatible: "boundary_top_coeff_compatible alpha"
    and localized: "\<And>p. p \<in> boundary_carrier
      \<Longrightarrow> rho p \<noteq> 0
      \<Longrightarrow> p \<in> D i \<inter> D j"
    and integrable: "weight_boundary_coeff rho alpha j
      absolutely_integrable_on boundary_overlap j i"
  shows "integral (halfspace_face (C i))
      (weight_boundary_coeff rho alpha i) =
    integral (halfspace_face (C j))
      (weight_boundary_coeff rho alpha j)"
proof -
  have compatible': "boundary_top_coeff_compatible
      (weight_boundary_coeff rho alpha)"
    by (rule weight_boundary_coeff_compatible[OF compatible])
  have coeff: "\<And>y. y \<in> boundary_overlap i j
      \<Longrightarrow> weight_boundary_coeff rho alpha i y =
        pull_top (boundary_transition i j)
          (weight_boundary_coeff rho alpha j) y"
    using compatible' i j
    by (auto simp: boundary_top_coeff_compatible_def)
  have localized': "\<And>p. p \<in> boundary_carrier
      \<Longrightarrow> rho p \<noteq> 0
      \<Longrightarrow> p \<in> D j \<inter> D i"
    using localized by auto
  have "integral (halfspace_face (C i))
      (weight_boundary_coeff rho alpha i) =
    integral (boundary_overlap i j)
      (weight_boundary_coeff rho alpha i)"
    by (rule boundary_chart_integral_localized[OF i localized])
  also have "\<dots> =
    integral (boundary_overlap j i)
      (weight_boundary_coeff rho alpha j)"
    by (rule boundary_overlap_integral
      [OF i j integrable coeff])
  also have "\<dots> =
    integral (halfspace_face (C j))
      (weight_boundary_coeff rho alpha j)"
    by (rule boundary_chart_integral_localized
      [OF j localized', symmetric])
  finally show ?thesis .
qed

lemma boundary_chart_integral_localized_form:
  assumes compatible: "boundary_top_coeff_compatible alpha"
    and i: "i \<in> I"
    and localized: "\<And>p. p \<in> boundary_form_support alpha
      \<Longrightarrow> rho p \<noteq> 0 \<Longrightarrow> p \<in> D j"
  shows "integral (halfspace_face (C i))
      (weight_boundary_coeff rho alpha i) =
    integral (boundary_overlap i j)
      (weight_boundary_coeff rho alpha i)"
proof -
  let ?E = "halfspace_face (C i)"
  have zero: "weight_boundary_coeff rho alpha i y = 0"
    if y: "y \<in> ?E" "y \<notin> boundary_overlap i j"
    for y
  proof -
    let ?p = "from_chart i (0,y)"
    have xi: "(0,y) \<in> C i"
      using y by (simp add: halfspace_face_def)
    have pi: "?p \<in> D i"
      using halfspace_chart.inverse_image[OF chart[OF i]]
        xi by auto
    have pB: "?p \<in> boundary_carrier"
      using boundary_chart_classify[OF i pi]
        halfspace_chart.from_to[OF chart[OF i] xi]
      by simp
    have py: "snd (to_chart i ?p) = y"
      using halfspace_chart.from_to[OF chart[OF i] xi]
      by simp
    have pj: "?p \<notin> D j"
      using y by (simp add: boundary_overlap_def)
    show ?thesis
    proof (cases "alpha i y = 0")
      case True
      then show ?thesis
        by (simp add: weight_boundary_coeff_def)
    next
      case False
      have supp: "?p \<in> boundary_form_support alpha"
        using boundary_form_support_chart[OF compatible i]
          pB pi py False by auto
      have "rho ?p = 0"
        using localized[OF supp] pj by auto
      then show ?thesis
        by (simp add: weight_boundary_coeff_def)
    qed
  qed
  have subset: "boundary_overlap i j \<subseteq> ?E"
    by (auto simp: boundary_overlap_def)
  have "integral ?E (weight_boundary_coeff rho alpha i) =
    integral ?E (\<lambda>y. if y \<in> boundary_overlap i j
      then weight_boundary_coeff rho alpha i y else 0)"
    by (rule integral_cong) (use zero in auto)
  also have "\<dots> =
    integral (boundary_overlap i j)
      (weight_boundary_coeff rho alpha i)"
    using subset by (simp add: integral_restrict_Int inf.absorb1)
  finally show ?thesis .
qed

lemma boundary_localized_chart_integral_eq_form:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and compatible: "boundary_top_coeff_compatible alpha"
    and localized: "\<And>p. p \<in> boundary_form_support alpha
      \<Longrightarrow> rho p \<noteq> 0
      \<Longrightarrow> p \<in> D i \<inter> D j"
    and integrable: "weight_boundary_coeff rho alpha j
      absolutely_integrable_on boundary_overlap j i"
  shows "integral (halfspace_face (C i))
      (weight_boundary_coeff rho alpha i) =
    integral (halfspace_face (C j))
      (weight_boundary_coeff rho alpha j)"
proof -
  have compatible': "boundary_top_coeff_compatible
      (weight_boundary_coeff rho alpha)"
    by (rule weight_boundary_coeff_compatible[OF compatible])
  have coeff: "\<And>y. y \<in> boundary_overlap i j
      \<Longrightarrow> weight_boundary_coeff rho alpha i y =
        pull_top (boundary_transition i j)
          (weight_boundary_coeff rho alpha j) y"
    using compatible' i j
    by (auto simp: boundary_top_coeff_compatible_def)
  have loc_i: "\<And>p. p \<in> boundary_form_support alpha
      \<Longrightarrow> rho p \<noteq> 0 \<Longrightarrow> p \<in> D j"
    using localized by auto
  have loc_j: "\<And>p. p \<in> boundary_form_support alpha
      \<Longrightarrow> rho p \<noteq> 0 \<Longrightarrow> p \<in> D i"
    using localized by auto
  have "integral (halfspace_face (C i))
      (weight_boundary_coeff rho alpha i) =
    integral (boundary_overlap i j)
      (weight_boundary_coeff rho alpha i)"
    by (rule boundary_chart_integral_localized_form
      [OF compatible i loc_i])
  also have "\<dots> =
    integral (boundary_overlap j i)
      (weight_boundary_coeff rho alpha j)"
    by (rule boundary_overlap_integral
      [OF i j integrable coeff])
  also have "\<dots> =
    integral (halfspace_face (C j))
      (weight_boundary_coeff rho alpha j)"
    by (rule boundary_chart_integral_localized_form
      [OF compatible j loc_j, symmetric])
  finally show ?thesis .
qed

lemma weight_boundary_coeff_partition:
  assumes i: "i \<in> I"
    and y: "y \<in> halfspace_face (C i)"
    and compatible: "boundary_top_coeff_compatible alpha"
    and unity: "\<And>p. p \<in> boundary_form_support alpha
      \<Longrightarrow> (\<Sum>j\<in>J. psi j p) = 1"
  shows "weight_boundary_coeff rho alpha i y =
    (\<Sum>j\<in>J. weight_boundary_coeff
      (\<lambda>p. rho p * psi j p) alpha i y)"
proof -
  let ?p = "from_chart i (0,y)"
  have homeo: "homeomorphism
      (boundary_carrier \<inter> D i)
      (halfspace_face (C i))
      (\<lambda>p. snd (to_chart i p))
      (\<lambda>z. from_chart i (0,z))"
    by (rule boundary_restricted_homeomorphism[OF i])
  have p: "?p \<in> boundary_carrier \<inter> D i"
    using homeomorphism_image2[OF homeo] y by auto
  have py: "snd (to_chart i ?p) = y"
    by (rule homeomorphism_apply2[OF homeo y])
  show ?thesis
  proof (cases "alpha i y = 0")
    case True
    then show ?thesis
      by (simp add: weight_boundary_coeff_def)
  next
    case False
    have "?p \<in> boundary_form_support alpha"
      using boundary_form_support_chart[OF compatible i p]
        py False by simp
    then have "(\<Sum>j\<in>J. psi j ?p) = 1"
      by (rule unity)
    then show ?thesis
      by (simp add: weight_boundary_coeff_def
        sum_distrib_left[symmetric]
        sum_distrib_right[symmetric] algebra_simps)
  qed
qed

lemma boundary_chart_integral_partition:
  assumes i: "i \<in> I" and finite: "finite J"
    and compatible: "boundary_top_coeff_compatible alpha"
    and unity: "\<And>p. p \<in> boundary_form_support alpha
      \<Longrightarrow> (\<Sum>j\<in>J. psi j p) = 1"
    and integrable: "\<And>j. j \<in> J \<Longrightarrow>
      weight_boundary_coeff (\<lambda>p. rho p * psi j p)
        alpha i integrable_on halfspace_face (C i)"
  shows "integral (halfspace_face (C i))
      (weight_boundary_coeff rho alpha i) =
    (\<Sum>j\<in>J. integral (halfspace_face (C i))
      (weight_boundary_coeff
        (\<lambda>p. rho p * psi j p) alpha i))"
proof -
  have "integral (halfspace_face (C i))
      (weight_boundary_coeff rho alpha i) =
    integral (halfspace_face (C i))
      (\<lambda>y. \<Sum>j\<in>J.
        weight_boundary_coeff
          (\<lambda>p. rho p * psi j p) alpha i y)"
    by (rule integral_cong)
       (use weight_boundary_coeff_partition
         [OF i _ compatible unity] in auto)
  also have "\<dots> =
    (\<Sum>j\<in>J. integral (halfspace_face (C i))
      (weight_boundary_coeff
        (\<lambda>p. rho p * psi j p) alpha i))"
    by (rule integral_sum[OF finite integrable])
  finally show ?thesis .
qed

definition boundary_chart_partition_integral ::
    "('i \<Rightarrow> real ^ 'n \<Rightarrow> real) \<Rightarrow>
      ('i \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow>
      'i set \<Rightarrow> real"
  where "boundary_chart_partition_integral alpha phi F =
    (\<Sum>i\<in>F. integral (halfspace_face (C i))
      (weight_boundary_coeff (phi i) alpha i))"

theorem boundary_chart_partition_integral_independent:
  assumes compatible: "boundary_top_coeff_compatible alpha"
    and finiteF: "finite F" and finiteG: "finite G"
    and F: "F \<subseteq> I" and G: "G \<subseteq> I"
    and unityF: "\<And>p. p \<in> boundary_form_support alpha
      \<Longrightarrow> (\<Sum>i\<in>F. phi i p) = 1"
    and unityG: "\<And>p. p \<in> boundary_form_support alpha
      \<Longrightarrow> (\<Sum>j\<in>G. psi j p) = 1"
    and supportF: "\<And>i p. i \<in> F \<Longrightarrow>
      p \<in> boundary_carrier \<Longrightarrow>
      phi i p \<noteq> 0 \<Longrightarrow> p \<in> D i"
    and supportG: "\<And>j p. j \<in> G \<Longrightarrow>
      p \<in> boundary_carrier \<Longrightarrow>
      psi j p \<noteq> 0 \<Longrightarrow> p \<in> D j"
    and integrableF: "\<And>i j. i \<in> F \<Longrightarrow> j \<in> G
      \<Longrightarrow> weight_boundary_coeff
        (\<lambda>p. phi i p * psi j p) alpha i
        absolutely_integrable_on halfspace_face (C i)"
    and integrableG: "\<And>i j. i \<in> F \<Longrightarrow> j \<in> G
      \<Longrightarrow> weight_boundary_coeff
        (\<lambda>p. phi i p * psi j p) alpha j
        absolutely_integrable_on halfspace_face (C j)"
  shows "boundary_chart_partition_integral alpha phi F =
    boundary_chart_partition_integral alpha psi G"
proof -
  have local: "integral (halfspace_face (C i))
      (weight_boundary_coeff
        (\<lambda>p. phi i p * psi j p) alpha i) =
    integral (halfspace_face (C j))
      (weight_boundary_coeff
        (\<lambda>p. phi i p * psi j p) alpha j)"
    if ii: "i \<in> F" and jj: "j \<in> G" for i j
  proof -
    have loc: "\<And>p. p \<in> boundary_carrier \<Longrightarrow>
      phi i p * psi j p \<noteq> 0 \<Longrightarrow>
      p \<in> D i \<inter> D j"
      using supportF[OF ii] supportG[OF jj] by auto
    have measurable: "boundary_overlap j i \<in> sets lebesgue"
      using boundary_overlap_open[OF subsetD[OF G jj]
        subsetD[OF F ii]]
      by (metis borel_open sets_lborel sets_completionI_sets)
    have subset: "boundary_overlap j i
      \<subseteq> halfspace_face (C j)"
      by (auto simp: boundary_overlap_def)
    have abs_overlap: "weight_boundary_coeff
        (\<lambda>p. phi i p * psi j p) alpha j
        absolutely_integrable_on boundary_overlap j i"
      using set_integrable_subset
        [OF integrableG[OF ii jj] measurable subset] .
    show ?thesis
      by (rule boundary_localized_chart_integral_eq
        [OF subsetD[OF F ii] subsetD[OF G jj]
          compatible loc abs_overlap])
  qed
  have intF: "weight_boundary_coeff
      (\<lambda>p. phi i p * psi j p) alpha i
      integrable_on halfspace_face (C i)"
    if "i \<in> F" "j \<in> G" for i j
    using integrableF[OF that]
    by (simp add: absolutely_integrable_on_def)
  have intG: "weight_boundary_coeff
      (\<lambda>p. psi j p * phi i p) alpha j
      integrable_on halfspace_face (C j)"
    if "i \<in> F" "j \<in> G" for i j
  proof -
    have eq: "weight_boundary_coeff
      (\<lambda>p. psi j p * phi i p) alpha j =
      weight_boundary_coeff
        (\<lambda>p. phi i p * psi j p) alpha j"
      by (simp add: weight_boundary_coeff_def mult.commute)
    show ?thesis
      unfolding eq using integrableG[OF that]
      by (simp add: absolutely_integrable_on_def)
  qed
  have left: "boundary_chart_partition_integral alpha phi F =
    (\<Sum>i\<in>F. \<Sum>j\<in>G.
      integral (halfspace_face (C i))
        (weight_boundary_coeff
          (\<lambda>p. phi i p * psi j p) alpha i))"
    unfolding boundary_chart_partition_integral_def
    by (rule sum.cong[OF refl])
       (use F finiteG compatible unityG intF in
        \<open>auto intro: boundary_chart_integral_partition\<close>)
  have right: "boundary_chart_partition_integral alpha psi G =
    (\<Sum>j\<in>G. \<Sum>i\<in>F.
      integral (halfspace_face (C j))
        (weight_boundary_coeff
          (\<lambda>p. phi i p * psi j p) alpha j))"
  proof -
    have "boundary_chart_partition_integral alpha psi G =
      (\<Sum>j\<in>G. \<Sum>i\<in>F.
        integral (halfspace_face (C j))
          (weight_boundary_coeff
            (\<lambda>p. psi j p * phi i p) alpha j))"
      unfolding boundary_chart_partition_integral_def
      by (rule sum.cong[OF refl])
         (use G finiteF compatible unityF intG in
          \<open>auto intro: boundary_chart_integral_partition\<close>)
    also have "\<dots> =
      (\<Sum>j\<in>G. \<Sum>i\<in>F.
        integral (halfspace_face (C j))
          (weight_boundary_coeff
            (\<lambda>p. phi i p * psi j p) alpha j))"
      by (simp add: weight_boundary_coeff_def mult.commute)
    finally show ?thesis .
  qed
  have "(\<Sum>i\<in>F. \<Sum>j\<in>G.
      integral (halfspace_face (C i))
        (weight_boundary_coeff
          (\<lambda>p. phi i p * psi j p) alpha i)) =
    (\<Sum>i\<in>F. \<Sum>j\<in>G.
      integral (halfspace_face (C j))
        (weight_boundary_coeff
          (\<lambda>p. phi i p * psi j p) alpha j))"
    by (rule sum.cong[OF refl], rule sum.cong[OF refl])
       (use local in auto)
  also have "\<dots> =
    (\<Sum>j\<in>G. \<Sum>i\<in>F.
      integral (halfspace_face (C j))
        (weight_boundary_coeff
          (\<lambda>p. phi i p * psi j p) alpha j))"
    by (rule sum.swap)
  finally show ?thesis using left right by simp
qed

definition admissible_boundary_partition ::
    "('i \<Rightarrow> real ^ 'n \<Rightarrow> real) \<Rightarrow>
      ('i \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow>
      'i set \<Rightarrow> bool"
  where "admissible_boundary_partition alpha phi F \<longleftrightarrow>
    finite F \<and> F \<subseteq> I \<and>
    (\<forall>p\<in>boundary_form_support alpha.
      (\<Sum>i\<in>F. phi i p) = 1) \<and>
    (\<forall>i\<in>F.
      continuous_on boundary_carrier (phi i) \<and>
      (\<exists>L. closed L \<and>
        {p\<in>boundary_carrier. phi i p \<noteq> 0} \<subseteq> L \<and>
        L \<subseteq> boundary_carrier \<inter> D i))"

theorem boundary_partition_integral_independent_admissible:
  assumes compatible: "boundary_top_coeff_compatible alpha"
    and compact: "compact K"
    and support: "boundary_form_support alpha \<subseteq> K"
    and coeff_cont: "\<And>i. i \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C i)) (alpha i)"
    and phi: "admissible_boundary_partition alpha phi F"
    and psi: "admissible_boundary_partition alpha psi G"
  shows "boundary_chart_partition_integral alpha phi F =
    boundary_chart_partition_integral alpha psi G"
proof (rule boundary_chart_partition_integral_independent
    [OF compatible])
  show "finite F" and "finite G"
    using phi psi by (auto simp: admissible_boundary_partition_def)
  show "F \<subseteq> I" and "G \<subseteq> I"
    using phi psi by (auto simp: admissible_boundary_partition_def)
  show "\<And>p. p \<in> boundary_form_support alpha
      \<Longrightarrow> (\<Sum>i\<in>F. phi i p) = 1"
    using phi by (auto simp: admissible_boundary_partition_def)
  show "\<And>p. p \<in> boundary_form_support alpha
      \<Longrightarrow> (\<Sum>j\<in>G. psi j p) = 1"
    using psi by (auto simp: admissible_boundary_partition_def)
  show "\<And>i p. i \<in> F \<Longrightarrow>
      p \<in> boundary_carrier \<Longrightarrow>
      phi i p \<noteq> 0 \<Longrightarrow> p \<in> D i"
    using phi unfolding admissible_boundary_partition_def
    by blast
  show "\<And>j p. j \<in> G \<Longrightarrow>
      p \<in> boundary_carrier \<Longrightarrow>
      psi j p \<noteq> 0 \<Longrightarrow> p \<in> D j"
    using psi unfolding admissible_boundary_partition_def
    by blast
  fix i j
  assume ii: "i \<in> F" and jj: "j \<in> G"
  obtain L where L: "closed L"
    "{p\<in>boundary_carrier. phi i p \<noteq> 0} \<subseteq> L"
    "L \<subseteq> boundary_carrier \<inter> D i"
    and cont_phi: "continuous_on boundary_carrier (phi i)"
    using phi ii
    by (auto simp: admissible_boundary_partition_def)
  obtain N where N: "closed N"
    "{p\<in>boundary_carrier. psi j p \<noteq> 0} \<subseteq> N"
    "N \<subseteq> boundary_carrier \<inter> D j"
    and cont_psi: "continuous_on boundary_carrier (psi j)"
    using psi jj
    by (auto simp: admissible_boundary_partition_def)
  have closedLN: "closed (L \<inter> N)"
    by (rule closed_Int[OF L(1) N(1)])
  have supportLN: "{p\<in>boundary_carrier.
      phi i p * psi j p \<noteq> 0} \<subseteq> L \<inter> N"
    using L(2) N(2) by auto
  have cont: "continuous_on boundary_carrier
      (\<lambda>p. phi i p * psi j p)"
    using cont_phi cont_psi by (auto intro!: continuous_intros)
  have local_i: "K \<inter> (L \<inter> N)
      \<subseteq> boundary_carrier \<inter> D i"
    using L(3) by auto
  have local_j: "K \<inter> (L \<inter> N)
      \<subseteq> boundary_carrier \<inter> D j"
    using N(3) by auto
  have iI: "i \<in> I"
    using phi ii by (auto simp: admissible_boundary_partition_def)
  have jI: "j \<in> I"
    using psi jj by (auto simp: admissible_boundary_partition_def)
  show "weight_boundary_coeff
      (\<lambda>p. phi i p * psi j p) alpha i
      absolutely_integrable_on halfspace_face (C i)"
    by (rule boundary_weight_absolutely_integrable
      [OF compatible iI compact support closedLN supportLN
        local_i cont coeff_cont[OF iI]])
  show "weight_boundary_coeff
      (\<lambda>p. phi i p * psi j p) alpha j
      absolutely_integrable_on halfspace_face (C j)"
    by (rule boundary_weight_absolutely_integrable
      [OF compatible jI compact support closedLN supportLN
        local_j cont coeff_cont[OF jI]])
qed

definition integral_boundary_top ::
    "('i \<Rightarrow> real ^ 'n \<Rightarrow> real) \<Rightarrow> real"
  where "integral_boundary_top alpha =
    (SOME z. \<exists>phi F.
      admissible_boundary_partition alpha phi F \<and>
      z = boundary_chart_partition_integral alpha phi F)"

theorem integral_boundary_top_eq_partition:
  assumes compatible: "boundary_top_coeff_compatible alpha"
    and compact: "compact K"
    and support: "boundary_form_support alpha \<subseteq> K"
    and coeff_cont: "\<And>i. i \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C i)) (alpha i)"
    and partition: "admissible_boundary_partition alpha phi F"
  shows "integral_boundary_top alpha =
    boundary_chart_partition_integral alpha phi F"
proof -
  let ?P = "\<lambda>z. \<exists>psi G.
      admissible_boundary_partition alpha psi G \<and>
      z = boundary_chart_partition_integral alpha psi G"
  have "\<exists>z. ?P z"
    using partition by blast
  then have "?P (SOME z. ?P z)"
    by (rule someI_ex)
  then obtain psi G where psi:
      "admissible_boundary_partition alpha psi G"
    and eq: "(SOME z. ?P z) =
      boundary_chart_partition_integral alpha psi G"
    by blast
  show ?thesis
    unfolding integral_boundary_top_def
    using eq boundary_partition_integral_independent_admissible
      [OF compatible compact support coeff_cont psi partition]
    by simp
qed

theorem integral_boundary_top_local_chart:
  assumes i: "i \<in> I"
    and compatible: "boundary_top_coeff_compatible alpha"
    and compact: "compact K"
    and Kchart: "K \<subseteq> boundary_carrier \<inter> D i"
    and support: "boundary_form_support alpha \<subseteq> K"
    and coeff_cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (alpha j)"
    and partition: "admissible_boundary_partition alpha phi F"
  shows "integral_boundary_top alpha =
    integral (halfspace_face (C i)) (alpha i)"
proof -
  have finite: "finite F"
    and FI: "F \<subseteq> I"
    and unity: "\<And>p. p \<in> boundary_form_support alpha
      \<Longrightarrow> (\<Sum>j\<in>F. phi j p) = 1"
    using partition by (auto simp: admissible_boundary_partition_def)
  have int_i: "weight_boundary_coeff (phi j) alpha i
      absolutely_integrable_on halfspace_face (C i)"
    if jj: "j \<in> F" for j
  proof -
    obtain L where L: "closed L"
      "{p\<in>boundary_carrier. phi j p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> boundary_carrier \<inter> D j"
      and cont: "continuous_on boundary_carrier (phi j)"
      using partition jj
      by (auto simp: admissible_boundary_partition_def)
    have local: "K \<inter> L \<subseteq> boundary_carrier \<inter> D i"
      using Kchart by auto
    show ?thesis
      by (rule boundary_weight_absolutely_integrable
        [OF compatible i compact support L(1,2)
          local cont coeff_cont[OF i]])
  qed
  have local: "integral (halfspace_face (C j))
      (weight_boundary_coeff (phi j) alpha j) =
    integral (halfspace_face (C i))
      (weight_boundary_coeff (phi j) alpha i)"
    if jj: "j \<in> F" for j
  proof -
    obtain L where L: "closed L"
      "{p\<in>boundary_carrier. phi j p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> boundary_carrier \<inter> D j"
      using partition jj
      by (auto simp: admissible_boundary_partition_def)
    have loc: "\<And>p. p \<in> boundary_form_support alpha
      \<Longrightarrow> phi j p \<noteq> 0
      \<Longrightarrow> p \<in> D j \<inter> D i"
      using L support Kchart
      by (auto simp: boundary_form_support_def)
    have measurable: "boundary_overlap i j \<in> sets lebesgue"
      using boundary_overlap_open[OF i subsetD[OF FI jj]]
      by (metis borel_open sets_lborel sets_completionI_sets)
    have subset: "boundary_overlap i j
      \<subseteq> halfspace_face (C i)"
      by (auto simp: boundary_overlap_def)
    have int_overlap: "weight_boundary_coeff
        (phi j) alpha i
        absolutely_integrable_on boundary_overlap i j"
      by (rule set_integrable_subset
        [OF int_i[OF jj] measurable subset])
    show ?thesis
      by (rule boundary_localized_chart_integral_eq_form
        [OF subsetD[OF FI jj] i compatible loc int_overlap])
  qed
  have expansion: "integral (halfspace_face (C i)) (alpha i) =
    (\<Sum>j\<in>F. integral (halfspace_face (C i))
      (weight_boundary_coeff (phi j) alpha i))"
  proof -
    have int: "weight_boundary_coeff
      (\<lambda>p. (1::real) * phi j p) alpha i
      integrable_on halfspace_face (C i)"
      if jj: "j \<in> F" for j
      using int_i[OF jj]
      by (simp add: absolutely_integrable_on_def)
    have eq: "weight_boundary_coeff (\<lambda>_. 1)
      alpha i = alpha i"
      by (rule ext) (simp add: weight_boundary_coeff_def)
    have "integral (halfspace_face (C i))
      (weight_boundary_coeff (\<lambda>_. 1) alpha i) =
    (\<Sum>j\<in>F. integral (halfspace_face (C i))
      (weight_boundary_coeff
        (\<lambda>p. (1::real) * phi j p) alpha i))"
      by (rule boundary_chart_integral_partition
        [OF i finite compatible unity int])
    then show ?thesis
      by (simp add: eq weight_boundary_coeff_def)
  qed
  have "integral_boundary_top alpha =
    boundary_chart_partition_integral alpha phi F"
    by (rule integral_boundary_top_eq_partition
      [OF compatible compact support coeff_cont partition])
  also have "\<dots> =
    (\<Sum>j\<in>F. integral (halfspace_face (C i))
      (weight_boundary_coeff (phi j) alpha i))"
    unfolding boundary_chart_partition_integral_def
    by (rule sum.cong[OF refl]) (use local in auto)
  also have "\<dots> =
    integral (halfspace_face (C i)) (alpha i)"
    using expansion by simp
  finally show ?thesis .
qed

theorem boundary_single_chart_integral_independent:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and compatible: "boundary_top_coeff_compatible alpha"
    and compact_i: "compact K_i"
    and K_i_chart: "K_i \<subseteq> boundary_carrier \<inter> D i"
    and support_i: "boundary_form_support alpha \<subseteq> K_i"
    and compact_j: "compact K_j"
    and K_j_chart: "K_j \<subseteq> boundary_carrier \<inter> D j"
    and support_j: "boundary_form_support alpha \<subseteq> K_j"
    and cont_j: "continuous_on (halfspace_face (C j))
      (alpha j)"
  shows "integral (halfspace_face (C i)) (alpha i) =
    integral (halfspace_face (C j)) (alpha j)"
proof -
  have localized: "\<And>p. p \<in> boundary_form_support alpha
      \<Longrightarrow> (1::real) \<noteq> 0
      \<Longrightarrow> p \<in> D i \<inter> D j"
    using K_i_chart support_i K_j_chart support_j
    by auto
  have int_j: "alpha j absolutely_integrable_on
      halfspace_face (C j)"
    by (rule boundary_chart_coeff_absolutely_integrable
      [OF compatible j compact_j K_j_chart support_j
        cont_j])
  have measurable: "boundary_overlap j i \<in> sets lebesgue"
    using boundary_overlap_open[OF j i]
    by (metis borel_open sets_lborel sets_completionI_sets)
  have subset: "boundary_overlap j i
      \<subseteq> halfspace_face (C j)"
    by (auto simp: boundary_overlap_def)
  have int_overlap: "alpha j absolutely_integrable_on
      boundary_overlap j i"
    by (rule set_integrable_subset
      [OF int_j measurable subset])
  have weight_eq: "\<And>k. weight_boundary_coeff
      (\<lambda>_. 1) alpha k = alpha k"
    by (rule ext) (simp add: weight_boundary_coeff_def)
  have int_overlap_weight: "weight_boundary_coeff
      (\<lambda>_. 1) alpha j absolutely_integrable_on
        boundary_overlap j i"
    using int_overlap by (simp only: weight_eq)
  have eq: "integral (halfspace_face (C i))
      (weight_boundary_coeff (\<lambda>_. 1) alpha i) =
    integral (halfspace_face (C j))
      (weight_boundary_coeff (\<lambda>_. 1) alpha j)"
    by (rule boundary_localized_chart_integral_eq_form
      [OF i j compatible localized int_overlap_weight])
  show ?thesis
    using eq by (simp only: weight_eq)
qed

definition admissible_boundary_single_chart ::
    "('i \<Rightarrow> real ^ 'n \<Rightarrow> real) \<Rightarrow>
      'i \<Rightarrow> 'a set \<Rightarrow> bool"
  where "admissible_boundary_single_chart alpha i K
    \<longleftrightarrow>
      i \<in> I \<and> compact K \<and>
      K \<subseteq> boundary_carrier \<inter> D i \<and>
      boundary_form_support alpha \<subseteq> K"

definition integral_boundary_single_top ::
    "('i \<Rightarrow> real ^ 'n \<Rightarrow> real) \<Rightarrow> real"
  where "integral_boundary_single_top alpha =
    (if \<exists>i K. admissible_boundary_single_chart alpha i K
      then (SOME z. \<exists>i K.
        admissible_boundary_single_chart alpha i K \<and>
        z = integral (halfspace_face (C i)) (alpha i))
      else 0)"

theorem integral_boundary_single_top_local_chart:
  assumes chart_i:
      "admissible_boundary_single_chart alpha i K"
    and compatible: "boundary_top_coeff_compatible alpha"
    and coeff_cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (alpha j)"
  shows "integral_boundary_single_top alpha =
    integral (halfspace_face (C i)) (alpha i)"
proof -
  let ?P = "\<lambda>z. \<exists>j L.
      admissible_boundary_single_chart alpha j L \<and>
      z = integral (halfspace_face (C j)) (alpha j)"
  have ex: "\<exists>j K. admissible_boundary_single_chart
      alpha j K"
    using chart_i by blast
  have some: "?P (SOME z. ?P z)"
    by (rule someI_ex) (use chart_i in blast)
  then obtain j L where chart_j:
      "admissible_boundary_single_chart alpha j L"
    and eq: "(SOME z. ?P z) =
      integral (halfspace_face (C j)) (alpha j)"
    by blast
  have i: "i \<in> I" and compact_i: "compact K"
    and K_i_chart: "K \<subseteq> boundary_carrier \<inter> D i"
    and support_i: "boundary_form_support alpha \<subseteq> K"
    using chart_i
    by (auto simp: admissible_boundary_single_chart_def)
  have j: "j \<in> I" and compact_j: "compact L"
    and K_j_chart: "L \<subseteq> boundary_carrier \<inter> D j"
    and support_j: "boundary_form_support alpha \<subseteq> L"
    using chart_j
    by (auto simp: admissible_boundary_single_chart_def)
  have chart_eq: "integral (halfspace_face (C j))
      (alpha j) =
    integral (halfspace_face (C i)) (alpha i)"
    by (rule boundary_single_chart_integral_independent
      [OF j i compatible compact_j K_j_chart support_j
        compact_i K_i_chart support_i coeff_cont[OF i]])
  show ?thesis
    using eq chart_eq ex
    by (simp only: integral_boundary_single_top_def
      if_True)
qed

theorem integral_boundary_single_top_eq_partition:
  assumes chart_i:
      "admissible_boundary_single_chart alpha i K"
    and compatible: "boundary_top_coeff_compatible alpha"
    and coeff_cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (alpha j)"
    and partition:
      "admissible_boundary_partition alpha phi F"
  shows "integral_boundary_single_top alpha =
    integral_boundary_top alpha"
proof -
  have i: "i \<in> I" and compact: "compact K"
    and Kchart: "K \<subseteq> boundary_carrier \<inter> D i"
    and support: "boundary_form_support alpha \<subseteq> K"
    using chart_i
    by (auto simp: admissible_boundary_single_chart_def)
  have local: "integral_boundary_single_top alpha =
      integral (halfspace_face (C i)) (alpha i)"
    by (rule integral_boundary_single_top_local_chart
      [OF chart_i compatible coeff_cont])
  have global: "integral_boundary_top alpha =
      integral (halfspace_face (C i)) (alpha i)"
    by (rule integral_boundary_top_local_chart
      [OF i compatible compact Kchart support
        coeff_cont partition])
  show ?thesis
    using local global by simp
qed

lemma boundary_single_chart_lborel_eq_integral:
  assumes chart_i:
      "admissible_boundary_single_chart alpha i K"
    and compatible: "boundary_top_coeff_compatible alpha"
    and continuous: "continuous_on
      (halfspace_face (C i)) (alpha i)"
  shows "(LINT y : halfspace_face (C i) | lborel.
      alpha i y) =
    integral (halfspace_face (C i)) (alpha i)"
proof -
  have i: "i \<in> I" and compact: "compact K"
    and Kchart: "K \<subseteq> boundary_carrier \<inter> D i"
    and support: "boundary_form_support alpha \<subseteq> K"
    using chart_i
    by (auto simp: admissible_boundary_single_chart_def)
  have abs_i: "alpha i absolutely_integrable_on
      halfspace_face (C i)"
    by (rule boundary_chart_coeff_absolutely_integrable
      [OF compatible i compact Kchart support continuous])
  have open_face: "open (halfspace_face (C i))"
    by (rule halfspace_face_open)
       (rule halfspace_chart.open_C[OF chart[OF i]])
  have face_borel: "halfspace_face (C i) \<in> sets borel"
    using open_face by (rule borel_open)
  have measurable: "(\<lambda>y. indicator
      (halfspace_face (C i)) y *\<^sub>R alpha i y)
      \<in> borel_measurable lborel"
    using borel_measurable_continuous_on_indicator
      [OF face_borel continuous]
    by (simp add: sets_lborel)
  have lborel_int: "set_integrable lborel
      (halfspace_face (C i)) (alpha i)"
    using abs_i measurable
    by (simp add: absolutely_integrable_on_def
      set_integrable_def integrable_completion)
  show ?thesis
    by (rule set_borel_integral_eq_integral(2)
      [OF lborel_int])
qed

lemma integral_boundary_single_top_zero_coeff:
  "integral_boundary_single_top (\<lambda>j y. 0) = 0"
proof (cases "\<exists>i K. admissible_boundary_single_chart
    (\<lambda>j y. 0) i K")
  case False
  then show ?thesis
    by (simp only: integral_boundary_single_top_def
      if_False)
next
  case True
  let ?P = "\<lambda>z. \<exists>i K.
      admissible_boundary_single_chart
        (\<lambda>j y. 0) i K \<and>
      z = integral (halfspace_face (C i))
        ((\<lambda>j y. 0) i)"
  have ex: "\<exists>z. ?P z"
    using True by blast
  have some: "?P (SOME z. ?P z)"
    by (rule someI_ex[OF ex])
  have eq: "(SOME z. ?P z) = 0"
    using some by auto
  show ?thesis
    unfolding integral_boundary_single_top_def
    using True eq by simp
qed

lemma integral_boundary_top_zero_coeff:
  "integral_boundary_top (\<lambda>j y. 0) = 0"
proof -
  have compatible: "boundary_top_coeff_compatible
      (\<lambda>j y. 0)"
    by (simp add: boundary_top_coeff_compatible_def
      pull_top_def)
  have support: "boundary_form_support
      (\<lambda>j y. 0) \<subseteq> {}"
    by (simp add: boundary_form_support_def)
  have continuous: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j))
        ((\<lambda>j y. 0) j)"
    by (intro continuous_intros)
  have partition: "admissible_boundary_partition
      (\<lambda>j y. 0) (\<lambda>j p. 0) {}"
    by (simp add: admissible_boundary_partition_def
      boundary_form_support_def)
  have "integral_boundary_top (\<lambda>j y. 0) =
    boundary_chart_partition_integral
      (\<lambda>j y. 0) (\<lambda>j p. 0) {}"
    by (rule integral_boundary_top_eq_partition
      [OF compatible compact_empty support continuous
        partition])
  then show ?thesis
    by (simp add: boundary_chart_partition_integral_def)
qed

lemma boundary_zero_integrals_agree:
  "integral_boundary_single_top (\<lambda>j y. 0) =
    integral_boundary_top (\<lambda>j y. 0)"
  by (simp only: integral_boundary_single_top_zero_coeff
    integral_boundary_top_zero_coeff)

theorem integral_boundary_top_empty:
  assumes empty: "boundary_carrier = {}"
  shows "integral_boundary_top alpha = 0"
proof -
  have compatible: "boundary_top_coeff_compatible alpha"
  proof (unfold boundary_top_coeff_compatible_def,
      intro ballI)
    fix i j y
    assume i: "i \<in> I" and "j \<in> I"
      and y: "y \<in> boundary_overlap i j"
    have "boundary_overlap i j = {}"
      using boundary_overlap_image[OF i]
      by (simp add: empty)
    with y show "alpha i y =
      pull_top (boundary_transition i j) (alpha j) y"
      by simp
  qed
  have support: "boundary_form_support alpha \<subseteq> {}"
    by (simp add: boundary_form_support_def empty)
  have coeff_cont: "continuous_on
      (halfspace_face (C i)) (alpha i)" if i: "i \<in> I"
    for i
  proof -
    have "halfspace_face (C i) = {}"
      using homeomorphism_image1
        [OF boundary_restricted_homeomorphism[OF i]]
      by (simp add: empty)
    then show ?thesis by simp
  qed
  have partition: "admissible_boundary_partition alpha
      (\<lambda>_. \<lambda>_. 0) {}"
    by (simp add: admissible_boundary_partition_def
      boundary_form_support_def empty)
  have "integral_boundary_top alpha =
    boundary_chart_partition_integral alpha
      (\<lambda>_. \<lambda>_. 0) {}"
    by (rule integral_boundary_top_eq_partition
      [OF compatible _ support coeff_cont partition])
       simp
  then show ?thesis
    by (simp add: boundary_chart_partition_integral_def)
qed

end

end
