theory Stokes_One_Dimensional_Manifold
  imports Stokes_One_Dimensional_Atlas_Gluing
    "HOL-Analysis.Change_Of_Vars"
    "HOL-Analysis.Higher_Differentiability_Multi"
    "HOL-Analysis.Abstract_Topological_Spaces"
begin

theorem oriented_real_integral_change_of_variables:
  fixes g :: "real \<Rightarrow> real"
    and g' :: "real \<Rightarrow> real \<Rightarrow> real"
    and alpha beta :: "real \<Rightarrow> real"
  assumes measurable: "S \<in> sets lebesgue"
    and derivative: "\<And>x. x \<in> S \<Longrightarrow>
      (g has_derivative g' x) (at x within S)"
    and injective: "inj_on g S"
    and integrable: "beta absolutely_integrable_on (g ` S)"
    and chart_sign: "eps_j * eps_j = 1"
    and oriented: "\<And>x. x \<in> S \<Longrightarrow>
      \<bar>eucl.det (g' x)\<bar> =
        eps_i * eps_j * eucl.det (g' x)"
    and compatible: "\<And>x. x \<in> S \<Longrightarrow>
      alpha x = eucl.det (g' x) * beta (g x)"
  shows "eps_i * integral S alpha =
    eps_j * integral (g ` S) beta"
proof -
  have change: "integral (g ` S) beta =
    integral S (\<lambda>x.
      \<bar>eucl.det (g' x)\<bar> *\<^sub>R beta (g x))"
  proof (rule integral_change_of_variables
      [where f=beta and g=g and g'=g' and S=S])
    show "S \<in> sets lebesgue"
      by (rule measurable)
    show "\<And>x. x \<in> S \<Longrightarrow>
      (g has_derivative g' x) (at x within S)"
      by (rule derivative)
    show "inj_on g S"
      by (rule injective)
    show "beta absolutely_integrable_on g ` S \<or>
      (\<lambda>x. \<bar>eucl.det (g' x)\<bar> *\<^sub>R beta (g x))
        absolutely_integrable_on S"
      using integrable by blast
  qed
  have pointwise: "eps_i * alpha x =
      eps_j * (\<bar>eucl.det (g' x)\<bar> *\<^sub>R beta (g x))"
    if x: "x \<in> S" for x
  proof -
    have "eps_j * \<bar>eucl.det (g' x)\<bar> =
        eps_i * eucl.det (g' x)"
      using oriented[OF x] chart_sign
      by (simp add: mult_ac)
    then show ?thesis
      by (simp add: compatible[OF x] mult_ac)
  qed
  have "integral S (\<lambda>x. eps_i * alpha x) =
      integral S (\<lambda>x.
        eps_j *
          (\<bar>eucl.det (g' x)\<bar> *\<^sub>R beta (g x)))"
    by (rule integral_cong) (use pointwise in auto)
  then show ?thesis
    by (simp add: change)
qed

locale halfline_chart =
  fixes M :: "'a::t2_space set"
    and D :: "'a set"
    and C :: "real set"
    and to_chart :: "'a \<Rightarrow> real"
    and from_chart :: "real \<Rightarrow> 'a"
  assumes open_D: "openin (top_of_set M) D"
    and open_C: "openin (top_of_set {0::real..}) C"
    and homeo: "homeomorphism D C to_chart from_chart"
begin

lemma domain_subset_carrier: "D \<subseteq> M"
  using open_D by (auto simp: openin_open)

lemma codomain_subset_halfline: "C \<subseteq> {0..}"
  using open_C by (auto simp: openin_open)

lemma to_from:
  assumes "p \<in> D"
  shows "from_chart (to_chart p) = p"
  by (rule homeomorphism_apply1[OF homeo assms])

lemma from_to:
  assumes "t \<in> C"
  shows "to_chart (from_chart t) = t"
  by (rule homeomorphism_apply2[OF homeo assms])

lemma chart_image: "to_chart ` D = C"
  by (rule homeomorphism_image1[OF homeo])

lemma inverse_image: "from_chart ` C = D"
  by (rule homeomorphism_image2[OF homeo])

lemma chart_continuous:
  "continuous_on D to_chart"
  by (rule homeomorphism_cont1[OF homeo])

lemma compact_relative_neighborhood:
  assumes p: "p \<in> D"
  obtains V K where
    "openin (top_of_set M) V"
    "p \<in> V"
    "compact K"
    "V \<subseteq> K"
    "K \<subseteq> D"
proof -
  let ?x = "to_chart p"
  have xC: "?x \<in> C"
    using chart_image p by auto
  obtain U where U: "open U"
    "C = {0..} \<inter> U"
    using open_C by (auto simp: openin_open)
  have xU: "?x \<in> U" and xH: "?x \<in> {0..}"
    using xC U by auto
  obtain e :: real where e: "0 < e"
    "cball ?x e \<subseteq> U"
    using open_contains_cball[THEN iffD1, OF U(1)]
      xU by blast
  let ?Bc = "ball ?x e \<inter> {0..}"
  let ?Kc = "cball ?x e \<inter> {0..}"
  let ?V = "from_chart ` ?Bc"
  let ?K = "from_chart ` ?Kc"
  have ballU: "ball ?x e \<subseteq> U"
    using e(2) by auto
  have Bc: "?Bc = C \<inter> ball ?x e"
    using ballU U(2) by auto
  have Kc: "?Kc \<subseteq> C"
    using e(2) U(2) by auto
  have Bopen: "openin (top_of_set C) ?Bc"
    using Bc
    by (auto simp: openin_open
      intro!: exI[of _ "ball ?x e"])
  have inv_homeo: "homeomorphism C D
      from_chart to_chart"
    by (rule homeomorphism_symD[OF homeo])
  have Vopen_D: "openin (top_of_set D) ?V"
    by (rule homeomorphism_imp_open_map
      [OF inv_homeo Bopen])
  have Vopen: "openin (top_of_set M) ?V"
    by (rule openin_trans[OF Vopen_D open_D])
  have xB: "?x \<in> ?Bc"
    using e(1) xH by simp
  have pV: "p \<in> ?V"
    using to_from[OF p] xB by (metis imageI)
  have compactKc: "compact ?Kc"
    by (rule compact_Int_closed)
       (simp_all add: closed_atLeast)
  have cont_inv: "continuous_on C from_chart"
    by (rule homeomorphism_cont2[OF homeo])
  have cont_Kc: "continuous_on ?Kc from_chart"
    by (rule continuous_on_subset[OF cont_inv Kc])
  have compactK: "compact ?K"
    by (rule compact_continuous_image[OF cont_Kc compactKc])
  have VK: "?V \<subseteq> ?K" by auto
  have KD: "?K \<subseteq> D"
    using Kc inverse_image by auto
  show ?thesis
    by (rule that[OF Vopen pV compactK VK KD])
qed


end

locale halfline_atlas =
  fixes M :: "'a::t2_space set"
    and I :: "'i set"
    and D :: "'i \<Rightarrow> 'a set"
    and C :: "'i \<Rightarrow> real set"
    and to_chart :: "'i \<Rightarrow> 'a \<Rightarrow> real"
    and from_chart :: "'i \<Rightarrow> real \<Rightarrow> 'a"
  assumes chart: "\<And>i. i \<in> I \<Longrightarrow>
      halfline_chart M (D i) (C i)
        (to_chart i) (from_chart i)"
    and cover: "M \<subseteq> (\<Union>i\<in>I. D i)"
    and face_compatible: "\<And>i j p.
      i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
      p \<in> D i \<Longrightarrow> p \<in> D j \<Longrightarrow>
      (to_chart i p = 0 \<longleftrightarrow>
        to_chart j p = 0)"
begin

definition overlap where
  "overlap i j = to_chart i ` (D i \<inter> D j)"

definition transition where
  "transition i j t = to_chart j (from_chart i t)"

lemma overlap_subset_codomain:
  assumes i: "i \<in> I"
  shows "overlap i j \<subseteq> C i"
  using halfline_chart.chart_image[OF chart[OF i]]
  by (auto simp: overlap_def)

lemma overlap_preimage:
  assumes i: "i \<in> I"
  shows "overlap i j =
    {t\<in>C i. from_chart i t \<in> D j}"
proof
  show "overlap i j \<subseteq>
    {t\<in>C i. from_chart i t \<in> D j}"
    using halfline_chart.chart_image[OF chart[OF i]]
      halfline_chart.to_from[OF chart[OF i]]
    by (auto simp: overlap_def)
  show "{t\<in>C i. from_chart i t \<in> D j}
      \<subseteq> overlap i j"
  proof
    fix t assume t: "t \<in> {t\<in>C i. from_chart i t \<in> D j}"
    have p: "from_chart i t \<in> D i"
      using t halfline_chart.inverse_image[OF chart[OF i]]
      by auto
    have "to_chart i (from_chart i t) = t"
      by (rule halfline_chart.from_to[OF chart[OF i]])
         (use t in auto)
    moreover have
      "to_chart i (from_chart i t) \<in>
        to_chart i ` (D i \<inter> D j)"
      using p t by blast
    ultimately have "t \<in> to_chart i ` (D i \<inter> D j)"
      by simp
    then show "t \<in> overlap i j"
      by (simp add: overlap_def)
  qed
qed

lemma overlap_open:
  assumes i: "i \<in> I" and j: "j \<in> I"
  shows "openin (top_of_set (C i)) (overlap i j)"
proof -
  have di: "D i \<subseteq> M"
    by (rule halfline_chart.domain_subset_carrier
      [OF chart[OF i]])
  have dj: "openin (top_of_set M) (D j)"
    by (rule halfline_chart.open_D[OF chart[OF j]])
  have rel: "openin (top_of_set (D i)) (D i \<inter> D j)"
    using di dj
    by (auto simp: openin_open)
  show ?thesis
    by (rule homeomorphism_imp_open_map
      [OF halfline_chart.homeo[OF chart[OF i]] rel,
        folded overlap_def])
qed

lemma overlap_measurable:
  assumes i: "i \<in> I" and j: "j \<in> I"
  shows "overlap i j \<in> sets lebesgue"
proof -
  have measurable_halfline:
      "{0::real..} \<in> sets lebesgue"
    by (simp add: sets_completionI_sets sets_lborel)
  have measurable_C: "C i \<in> sets lebesgue"
    by (rule lebesgue_openin
      [OF halfline_chart.open_C[OF chart[OF i]]
        measurable_halfline])
  show ?thesis
    using overlap_open[OF i j] measurable_C
    by (rule lebesgue_openin)
qed

lemma transition_overlap:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and t: "t \<in> overlap i j"
  shows "transition i j t \<in> overlap j i"
proof -
  have tC: "t \<in> C i"
    using t overlap_subset_codomain[OF i] by auto
  have p: "from_chart i t \<in> D i \<inter> D j"
    using t overlap_preimage[OF i]
      halfline_chart.inverse_image[OF chart[OF i]]
    by auto
  show ?thesis
    using p by (auto simp: transition_def overlap_def)
qed

lemma transition_inverse:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and t: "t \<in> overlap i j"
  shows "transition j i (transition i j t) = t"
proof -
  have tC: "t \<in> C i"
    using t overlap_subset_codomain[OF i] by auto
  have p: "from_chart i t \<in> D j"
    using t overlap_preimage[OF i] by auto
  show ?thesis
    using halfline_chart.to_from[OF chart[OF j] p]
      halfline_chart.from_to[OF chart[OF i] tC]
    by (simp add: transition_def)
qed

lemma transition_point:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and t: "t \<in> overlap i j"
  shows "from_chart j (transition i j t) =
    from_chart i t"
proof -
  have p: "from_chart i t \<in> D j"
    using t overlap_preimage[OF i] by auto
  show ?thesis
    using halfline_chart.to_from[OF chart[OF j] p]
    by (simp add: transition_def)
qed

lemma transition_injective:
  assumes i: "i \<in> I" and j: "j \<in> I"
  shows "inj_on (transition i j) (overlap i j)"
proof (rule inj_onI)
  fix x y
  assume x: "x \<in> overlap i j"
    and y: "y \<in> overlap i j"
    and eq: "transition i j x = transition i j y"
  have x_id: "transition j i (transition i j x) = x"
    by (rule transition_inverse[OF i j x])
  have y_id: "transition j i (transition i j y) = y"
    by (rule transition_inverse[OF i j y])
  have "transition j i (transition i j x) =
      transition j i (transition i j y)"
    using eq by simp
  then show "x = y"
    using x_id y_id by argo
qed

lemma transition_image:
  assumes i: "i \<in> I" and j: "j \<in> I"
  shows "transition i j ` overlap i j = overlap j i"
proof
  show "transition i j ` overlap i j \<subseteq> overlap j i"
  proof
    fix t assume "t \<in> transition i j ` overlap i j"
    then obtain u where u: "u \<in> overlap i j"
      and t: "t = transition i j u"
      by blast
    show "t \<in> overlap j i"
      unfolding t by (rule transition_overlap[OF i j u])
  qed
  show "overlap j i \<subseteq> transition i j ` overlap i j"
  proof
    fix t assume t: "t \<in> overlap j i"
    have p: "transition j i t \<in> overlap i j"
      by (rule transition_overlap[OF j i t])
    have "transition i j (transition j i t) = t"
      by (rule transition_inverse[OF j i t])
    moreover have
      "transition i j (transition j i t) \<in>
        transition i j ` overlap i j"
      using p by blast
    ultimately have "t \<in> transition i j ` overlap i j"
      by simp
    then show "t \<in> transition i j ` overlap i j" .
  qed
qed

definition boundary_carrier where
  "boundary_carrier =
    {p\<in>M. \<exists>i\<in>I.
      p \<in> D i \<and> to_chart i p = 0}"

definition interior_carrier where
  "interior_carrier = M - boundary_carrier"

lemma domain_subset_carrier:
  assumes i: "i \<in> I"
  shows "D i \<subseteq> M"
  by (rule halfline_chart.domain_subset_carrier[OF chart[OF i]])

lemma boundary_subset_carrier:
  "boundary_carrier \<subseteq> M"
  by (auto simp: boundary_carrier_def)

lemma boundary_chart_classify:
  assumes i: "i \<in> I"
    and p: "p \<in> D i"
  shows "p \<in> boundary_carrier \<longleftrightarrow>
    to_chart i p = 0"
proof
  assume "p \<in> boundary_carrier"
  then obtain j where j: "j \<in> I" "p \<in> D j"
    "to_chart j p = 0"
    by (auto simp: boundary_carrier_def)
  show "to_chart i p = 0"
    using face_compatible[OF i j(1) p j(2)] j(3)
    by simp
next
  assume "to_chart i p = 0"
  moreover have "p \<in> M"
    using domain_subset_carrier[OF i] p by auto
  ultimately show "p \<in> boundary_carrier"
    using i p by (auto simp: boundary_carrier_def)
qed

lemma boundary_chart_singleton:
  assumes i: "i \<in> I"
    and p: "p \<in> boundary_carrier \<inter> D i"
  shows "boundary_carrier \<inter> D i = {p}"
proof
  show "boundary_carrier \<inter> D i \<subseteq> {p}"
  proof
    fix q assume q: "q \<in> boundary_carrier \<inter> D i"
    have p0: "to_chart i p = 0"
      using p boundary_chart_classify[OF i] by auto
    have q0: "to_chart i q = 0"
      using q boundary_chart_classify[OF i] by auto
    have "q = from_chart i (to_chart i q)"
      using q
      by (simp add: halfline_chart.to_from[OF chart[OF i]])
    also have "\<dots> = from_chart i (to_chart i p)"
      by (simp add: p0 q0)
    also have "\<dots> = p"
      using p
      by (simp add: halfline_chart.to_from[OF chart[OF i]])
    finally show "q \<in> {p}" by simp
  qed
  show "{p} \<subseteq> boundary_carrier \<inter> D i"
    using p by simp
qed

lemma boundary_singleton_open:
  assumes p: "p \<in> boundary_carrier"
  shows "openin (top_of_set boundary_carrier) {p}"
proof -
  have pM: "p \<in> M"
    using boundary_subset_carrier p by auto
  obtain i where i: "i \<in> I" "p \<in> D i"
    using cover pM by blast
  have d_open: "openin (top_of_set M) (D i)"
    by (rule halfline_chart.open_D[OF chart[OF i(1)]])
  obtain U where U: "open U" "D i = M \<inter> U"
    using d_open by (auto simp: openin_open)
  have pDi: "p \<in> boundary_carrier \<inter> D i"
    using p i by auto
  have eqD: "boundary_carrier \<inter> D i = {p}"
    by (rule boundary_chart_singleton[OF i(1) pDi])
  have eq: "{p} = boundary_carrier \<inter> U"
    using eqD U boundary_subset_carrier
    by auto
  show ?thesis
    unfolding eq
    using U(1) by (auto simp: openin_open)
qed

lemma boundary_discrete:
  "discrete_topology boundary_carrier =
    top_of_set boundary_carrier"
  by (simp add: discrete_topology_unique
    boundary_singleton_open)

lemma chart_interior_open:
  assumes i: "i \<in> I"
  shows "openin (top_of_set M)
    {p\<in>D i. 0 < to_chart i p}"
proof -
  have d_open: "openin (top_of_set M) (D i)"
    by (rule halfline_chart.open_D[OF chart[OF i]])
  have cont: "continuous_on (D i) (to_chart i)"
    by (rule halfline_chart.chart_continuous
      [OF chart[OF i]])
  have U_open: "open ({0<..}::real set)"
    by simp
  have rel: "openin (top_of_set (D i))
      (D i \<inter> (to_chart i) -` {0<..})"
    using cont U_open
    by (simp add: continuous_openin_preimage_eq)
  have "openin (top_of_set M)
      (D i \<inter> (to_chart i) -` {0<..})"
    by (rule openin_trans[OF rel d_open])
  moreover have
      "D i \<inter> (to_chart i) -` {0<..} =
        {p\<in>D i. 0 < to_chart i p}"
    by auto
  ultimately show ?thesis by simp
qed

lemma interior_carrier_union:
  "interior_carrier =
    (\<Union>i\<in>I. {p\<in>D i. 0 < to_chart i p})"
proof
  show "interior_carrier \<subseteq>
    (\<Union>i\<in>I. {p\<in>D i. 0 < to_chart i p})"
  proof
    fix p assume p: "p \<in> interior_carrier"
    then have pM: "p \<in> M"
      by (simp add: interior_carrier_def)
    obtain i where i: "i \<in> I" "p \<in> D i"
      using cover pM by blast
    have nonnegative: "0 \<le> to_chart i p"
      using halfline_chart.chart_image[OF chart[OF i(1)]]
        halfline_chart.codomain_subset_halfline
          [OF chart[OF i(1)]] i(2)
      by auto
    have nonzero: "to_chart i p \<noteq> 0"
      using p boundary_chart_classify[OF i]
      by (auto simp: interior_carrier_def)
    with nonnegative show
      "p \<in> (\<Union>i\<in>I.
        {p\<in>D i. 0 < to_chart i p})"
      using i by auto
  qed
  show "(\<Union>i\<in>I.
      {p\<in>D i. 0 < to_chart i p}) \<subseteq>
      interior_carrier"
    using domain_subset_carrier
      boundary_chart_classify
    by (auto simp: interior_carrier_def)
qed

lemma interior_carrier_open:
  "openin (top_of_set M) interior_carrier"
  unfolding interior_carrier_union
  by (intro openin_Union)
     (auto intro: chart_interior_open)

lemma boundary_carrier_closed:
  "closedin (top_of_set M) boundary_carrier"
  using boundary_subset_carrier interior_carrier_open
  by (auto simp: closedin_def interior_carrier_def)

lemma carrier_locally_compact:
  "locally_compact_space (top_of_set M)"
proof (unfold locally_compact_space_def, intro ballI)
  fix p
  assume p: "p \<in> topspace (top_of_set M)"
  obtain i where i: "i \<in> I" "p \<in> D i"
    using p cover by auto
  interpret c: halfline_chart M "D i" "C i"
    "to_chart i" "from_chart i"
    by (rule chart[OF i(1)])
  obtain V K where V: "openin (top_of_set M) V"
    "p \<in> V" "compact K" "V \<subseteq> K"
    "K \<subseteq> D i"
    by (rule c.compact_relative_neighborhood[OF i(2)])
  have "compactin (top_of_set M) K"
    using V(3,5) domain_subset_carrier[OF i(1)]
    by (simp add: compactin_subtopology)
  then show "\<exists>U K. openin (top_of_set M) U \<and>
      compactin (top_of_set M) K \<and>
      p \<in> U \<and> U \<subseteq> K"
    using V by blast
qed

lemma carrier_Hausdorff:
  "Hausdorff_space (top_of_set M)"
proof (unfold Hausdorff_space_def, intro allI impI)
  fix p q
  assume pq: "p \<in> topspace (top_of_set M) \<and>
      q \<in> topspace (top_of_set M) \<and> p \<noteq> q"
  obtain U V where UV: "open U" "open V"
    "p \<in> U" "q \<in> V" "U \<inter> V = {}"
    using separation_t2[of p q] pq by blast
  let ?P = "M \<inter> U"
  let ?Q = "M \<inter> V"
  have openP: "openin (top_of_set M) ?P"
    unfolding openin_open
    by (rule exI[where x=U]) (use UV(1) in simp)
  have openQ: "openin (top_of_set M) ?Q"
    unfolding openin_open
    by (rule exI[where x=V]) (use UV(2) in simp)
  have pP: "p \<in> ?P" using pq UV(3) by simp
  have qQ: "q \<in> ?Q" using pq UV(4) by simp
  have disjoint: "disjnt ?P ?Q"
    using UV(5) unfolding disjnt_def by blast
  show "\<exists>P Q.
      openin (top_of_set M) P \<and>
      openin (top_of_set M) Q \<and>
      p \<in> P \<and> q \<in> Q \<and> disjnt P Q"
    by (rule exI[where x="?P"],
        rule exI[where x="?Q"])
       (intro conjI openP openQ pP qQ disjoint)
qed

lemma compact_boundary_finite:
  assumes compact: "compact K"
    and KM: "K \<subseteq> M"
  shows "finite (K \<inter> boundary_carrier)"
proof -
  have compM: "compactin (top_of_set M) K"
    using compact KM
    by (simp add: compactin_subtopology)
  have compMB:
      "compactin (top_of_set M)
        (K \<inter> boundary_carrier)"
    by (rule compact_Int_closedin
      [OF compM boundary_carrier_closed])
  have compB:
      "compactin (top_of_set boundary_carrier)
        (K \<inter> boundary_carrier)"
    using compMB
    by (simp add: compactin_subtopology)
  have comp_discrete:
      "compactin (discrete_topology boundary_carrier)
        (K \<inter> boundary_carrier)"
    using compB
    by (simp add: boundary_discrete)
  show ?thesis
    using comp_discrete
    by (simp add: compactin_discrete_topology)
qed

lemma compact_chart_subcover:
  assumes compact: "compact K"
    and KM: "K \<subseteq> M"
  obtains F where "finite F" "F \<subseteq> I"
    "K \<subseteq> (\<Union>i\<in>F. D i)"
proof -
  have compactM: "compactin (top_of_set M) K"
    using compact KM by (simp add: compactin_subtopology)
  have open_cover:
    "\<And>U. U \<in> D ` I \<Longrightarrow>
      openin (top_of_set M) U"
    using halfline_chart.open_D[OF chart] by auto
  have coverK: "K \<subseteq> \<Union>(D ` I)"
    using KM cover by auto
  obtain T where T: "finite T" "T \<subseteq> D ` I"
    "K \<subseteq> \<Union>T"
    using compactinD[OF compactM open_cover coverK]
    by blast
  obtain F where F: "F \<subseteq> I" "finite F"
    "D ` F = T"
    using finite_subset_image[OF T(1,2)] by blast
  show thesis
    by (rule that[OF F(2) F(1)])
       (use F T in auto)
qed

definition selected_boundary where
  "selected_boundary F =
    (\<lambda>i. from_chart i 0) `
      {i\<in>F. 0 \<in> C i}"

lemma selected_boundary_finite:
  assumes "finite F"
  shows "finite (selected_boundary F)"
  using assms by (simp add: selected_boundary_def)

lemma selected_boundary_subset:
  assumes FI: "F \<subseteq> I"
  shows "selected_boundary F \<subseteq> boundary_carrier"
proof
  fix p assume "p \<in> selected_boundary F"
  then obtain i where i: "i \<in> F" "0 \<in> C i"
    and p: "p = from_chart i 0"
    by (auto simp: selected_boundary_def)
  have iI: "i \<in> I"
    using FI i by auto
  have pD: "p \<in> D i"
    using halfline_chart.inverse_image[OF chart[OF iI]]
      i(2) p by auto
  have p0: "to_chart i p = 0"
    using halfline_chart.from_to[OF chart[OF iI] i(2)]
      p by simp
  have "p \<in> M"
    using domain_subset_carrier[OF iI] pD by auto
  then show "p \<in> boundary_carrier"
    using iI pD p0
    by (auto simp: boundary_carrier_def)
qed

lemma selected_boundary_on_compact_support:
  assumes FI: "F \<subseteq> I"
    and coverF: "K \<subseteq> (\<Union>i\<in>F. D i)"
  shows "K \<inter> selected_boundary F =
    K \<inter> boundary_carrier"
proof
  show "K \<inter> selected_boundary F \<subseteq>
    K \<inter> boundary_carrier"
    using selected_boundary_subset[OF FI] by auto
  show "K \<inter> boundary_carrier \<subseteq>
    K \<inter> selected_boundary F"
  proof
    fix p assume p: "p \<in> K \<inter> boundary_carrier"
    then obtain i where i: "i \<in> F" "p \<in> D i"
      using coverF by auto
    have iI: "i \<in> I"
      using FI i by auto
    have p0: "to_chart i p = 0"
      using boundary_chart_classify[OF iI i(2)]
        p by auto
    have zeroC: "0 \<in> C i"
      using halfline_chart.chart_image[OF chart[OF iI]]
        i(2) p0 by auto
    have "from_chart i 0 = p"
      using halfline_chart.to_from[OF chart[OF iI] i(2)]
        p0 by simp
    then show "p \<in> K \<inter> selected_boundary F"
      using p i(1) zeroC
      by (auto simp: selected_boundary_def)
  qed
qed

end

locale oriented_C1_halfline_atlas =
  halfline_atlas M I D C to_chart from_chart
  for M :: "'a::t2_space set"
    and I :: "'i set"
    and D :: "'i \<Rightarrow> 'a set"
    and C :: "'i \<Rightarrow> real set"
    and to_chart :: "'i \<Rightarrow> 'a \<Rightarrow> real"
    and from_chart :: "'i \<Rightarrow> real \<Rightarrow> 'a" +
  fixes eps :: "'i \<Rightarrow> real"
    and transition_deriv ::
      "'i \<Rightarrow> 'i \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  assumes chart_sign: "\<And>i. i \<in> I \<Longrightarrow>
      eps i * eps i = 1"
    and transition_differentiable:
      "\<And>i j t. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
        t \<in> overlap i j \<Longrightarrow>
        (transition i j has_derivative
          transition_deriv i j t)
          (at t within overlap i j)"
    and transition_oriented:
      "\<And>i j t. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
        t \<in> overlap i j \<Longrightarrow>
        \<bar>eucl.det (transition_deriv i j t)\<bar> =
          eps i * eps j *
            eucl.det (transition_deriv i j t)"
    and local_transition_C1:
      "\<And>i j t. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
        t \<in> overlap i j \<Longrightarrow>
        \<exists>U F. open U \<and> t \<in> U \<and>
          Ck_on 1 F U \<and>
          (\<forall>s\<in>U \<inter> overlap i j.
            F s = transition i j s)"
    and boundary_chart_sign:
      "\<And>i j p. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
        p \<in> boundary_carrier \<Longrightarrow>
        p \<in> D i \<Longrightarrow> p \<in> D j \<Longrightarrow>
        eps i = eps j"
begin

lemma oriented_transition_integral:
  fixes alpha beta :: "real \<Rightarrow> real"
  assumes i: "i \<in> I" and j: "j \<in> I"
    and integrable:
      "beta absolutely_integrable_on overlap j i"
    and compatible: "\<And>t. t \<in> overlap i j \<Longrightarrow>
      alpha t =
        eucl.det (transition_deriv i j t) *
          beta (transition i j t)"
  shows "eps i * integral (overlap i j) alpha =
    eps j * integral (overlap j i) beta"
proof -
  have change: "eps i * integral (overlap i j) alpha =
      eps j *
        integral (transition i j ` overlap i j) beta"
    by (rule oriented_real_integral_change_of_variables
      [where g="transition i j"
        and g'="transition_deriv i j"
        and S="overlap i j" and alpha=alpha
        and beta=beta and eps_i="eps i"
        and eps_j="eps j",
        OF overlap_measurable[OF i j]
          transition_differentiable[OF i j]
          transition_injective[OF i j]])
       (use integrable chart_sign[OF j]
         transition_oriented[OF i j] compatible
         transition_image[OF i j] in auto)
  show ?thesis
    using change transition_image[OF i j] by simp
qed

definition boundary_orientation where
  "boundary_orientation p =
    (SOME s. \<exists>i\<in>I.
      p \<in> D i \<and> to_chart i p = 0 \<and>
      s = - eps i)"

lemma boundary_orientation_chart:
  assumes p: "p \<in> boundary_carrier"
    and i: "i \<in> I" "p \<in> D i"
  shows "boundary_orientation p = - eps i"
proof -
  have zero: "to_chart i p = 0"
    using boundary_chart_classify[OF i] p by auto
  have witness: "\<exists>k\<in>I. p \<in> D k \<and>
      to_chart k p = 0 \<and> - eps i = - eps k"
    using i zero by blast
  have unique: "s = - eps i"
    if "\<exists>k\<in>I.
      p \<in> D k \<and> to_chart k p = 0 \<and>
      s = - eps k" for s
    using that boundary_chart_sign[OF i(1) _ p i(2)]
    by auto
  show ?thesis
    unfolding boundary_orientation_def
    by (rule someI2
      [where P="\<lambda>s. \<exists>k\<in>I.
        p \<in> D k \<and> to_chart k p = 0 \<and>
        s = - eps k" and a="- eps i",
        OF witness unique])
qed

theorem oriented_one_dimensional_finite_atlas_stokes:
  fixes omega :: "'a \<Rightarrow> real"
    and phi :: "'i \<Rightarrow> 'a \<Rightarrow> real"
    and G g :: "'i \<Rightarrow> real \<Rightarrow> real"
  assumes finiteF: "finite F"
    and FI: "F \<subseteq> I"
    and coverF: "K \<subseteq> (\<Union>i\<in>F. D i)"
    and omega_support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and partition: "\<And>p. p \<in> K
      \<Longrightarrow> (\<Sum>i\<in>F. phi i p) = 1"
    and phi_outside: "\<And>i p. i \<in> F \<Longrightarrow>
      p \<in> M \<Longrightarrow> p \<notin> D i
      \<Longrightarrow> phi i p = 0"
    and compactL: "\<And>i. i \<in> F \<Longrightarrow>
      compact (L i)"
    and LC: "\<And>i. i \<in> F \<Longrightarrow>
      L i \<subseteq> C i"
    and zeroG: "\<And>i t. i \<in> F \<Longrightarrow>
      t \<in> C i \<Longrightarrow> t \<notin> L i
      \<Longrightarrow> G i t = 0"
    and deriv: "\<And>i t. i \<in> F \<Longrightarrow>
      t \<in> C i \<Longrightarrow>
      (G i has_vector_derivative g i t)
        (at t within {0..})"
    and cont: "\<And>i. i \<in> F \<Longrightarrow>
      continuous_on (C i) (g i)"
    and boundary_value: "\<And>i. i \<in> F \<Longrightarrow>
      0 \<in> C i \<Longrightarrow>
      G i 0 =
        phi i (from_chart i 0) *
          omega (from_chart i 0)"
  shows "(\<Sum>i\<in>F.
      eps i *
        (LINT t : C i | lborel. g i t)) =
    finite_boundary_zero_integral
      (K \<inter> boundary_carrier)
      (\<lambda>p. boundary_orientation p * omega p)"
proof -
  let ?B = "selected_boundary F"
  have finiteB: "finite ?B"
    by (rule selected_boundary_finite[OF finiteF])
  have subsetB: "?B \<subseteq> boundary_carrier"
    by (rule selected_boundary_subset[OF FI])
  have unity: "(\<Sum>i\<in>F.
      if 0 \<in> C i \<and> from_chart i 0 = p
      then phi i p else 0) = 1"
    if p: "p \<in> ?B" and nz: "omega p \<noteq> 0"
    for p
  proof -
    have pM: "p \<in> M"
      using subsetB p boundary_subset_carrier by auto
    have pK: "p \<in> K"
      using omega_support[OF pM] nz by auto
    have eq: "(if 0 \<in> C i \<and> from_chart i 0 = p
        then phi i p else 0) = phi i p"
      if iF: "i \<in> F" for i
    proof (cases "p \<in> D i")
      case True
      have iI: "i \<in> I"
        using FI iF by auto
      have zero: "to_chart i p = 0"
        using boundary_chart_classify[OF iI True]
          subsetB p by auto
      have zeroC: "0 \<in> C i"
        using halfline_chart.chart_image[OF chart[OF iI]]
          True zero by auto
      have "from_chart i 0 = p"
        using halfline_chart.to_from[OF chart[OF iI] True]
          zero by simp
      then show ?thesis using zeroC by simp
    next
      case False
      have pM: "p \<in> M"
        using subsetB p boundary_subset_carrier by auto
      then show ?thesis
        using phi_outside[OF iF pM False]
        by simp
    qed
    have "(\<Sum>i\<in>F.
      if 0 \<in> C i \<and> from_chart i 0 = p
      then phi i p else 0) =
      (\<Sum>i\<in>F. phi i p)"
      by (rule sum.cong[OF refl]) (use eq in auto)
    then show ?thesis
      using partition[OF pK] by simp
  qed
  have glued: "(\<Sum>i\<in>F.
      eps i * (LINT t : C i | lborel. g i t)) =
    finite_boundary_zero_integral ?B
      (\<lambda>p. boundary_orientation p * omega p)"
  proof -
    have eq: "(\<Sum>i\<in>F.
      eps i * (LINT t : C i | lborel. g i t)) =
      finite_boundary_zero_integral ?B
        (\<lambda>p.
          - (- boundary_orientation p) * omega p)"
    proof (rule Stokes_one_dimensional_finite_atlas_gluing
      [where F=F and B="?B"
        and C=C and K=L and G=G and g=g
        and eps=eps and phi=phi and omega=omega
        and face="\<lambda>i. 0 \<in> C i"
        and point="\<lambda>i. from_chart i 0"
        and sigma="\<lambda>p. - boundary_orientation p"])
      show "finite F" by (rule finiteF)
      show "finite ?B" by (rule finiteB)
      show "\<And>i. i \<in> F \<Longrightarrow>
        openin (top_of_set {0::real..}) (C i)"
        using FI halfline_chart.open_C[OF chart]
        by auto
      show "\<And>i. i \<in> F \<Longrightarrow> compact (L i)"
        by (rule compactL)
      show "\<And>i. i \<in> F \<Longrightarrow> L i \<subseteq> C i"
        by (rule LC)
      show "\<And>i t. i \<in> F \<Longrightarrow>
        t \<in> C i \<Longrightarrow> t \<notin> L i
        \<Longrightarrow> G i t = 0"
        by (rule zeroG)
      show "\<And>i t. i \<in> F \<Longrightarrow> t \<in> C i
        \<Longrightarrow>
        (G i has_vector_derivative g i t)
          (at t within {0..})"
        by (rule deriv)
      show "\<And>i. i \<in> F \<Longrightarrow>
        continuous_on (C i) (g i)"
        by (rule cont)
      show "\<And>i. i \<in> F \<Longrightarrow>
        (0 \<in> C i) = (0 \<in> C i)"
        by simp
      show "\<And>i. i \<in> F \<Longrightarrow>
        0 \<in> C i \<Longrightarrow>
        from_chart i 0 \<in> ?B"
        by (auto simp: selected_boundary_def)
      show "\<And>i. i \<in> F \<Longrightarrow>
        0 \<in> C i \<Longrightarrow>
        G i 0 =
          phi i (from_chart i 0) *
            omega (from_chart i 0)"
        by (rule boundary_value)
      show "\<And>i. i \<in> F \<Longrightarrow>
        0 \<in> C i \<Longrightarrow>
        eps i = - boundary_orientation (from_chart i 0)"
      proof -
        fix i assume iF: "i \<in> F"
          and zero: "0 \<in> C i"
        have iI: "i \<in> I"
          using FI iF by auto
        have pB: "from_chart i 0 \<in> ?B"
          using iF zero
          by (auto simp: selected_boundary_def)
        have pD: "from_chart i 0 \<in> D i"
          using halfline_chart.inverse_image
            [OF chart[OF iI]] zero by auto
        have "boundary_orientation
            (from_chart i 0) = - eps i"
          by (rule boundary_orientation_chart
            [OF _ iI pD])
             (use subsetB pB in auto)
        then show "eps i =
          - boundary_orientation (from_chart i 0)"
          by simp
      qed
      show "\<And>p. p \<in> ?B \<Longrightarrow>
        omega p \<noteq> 0 \<Longrightarrow>
        (\<Sum>i\<in>F.
          if 0 \<in> C i \<and> from_chart i 0 = p
          then phi i p else 0) = 1"
        by (rule unity)
    qed
    show ?thesis
      using eq by simp
  qed
  have boundary_restrict:
    "finite_boundary_zero_integral ?B
      (\<lambda>p. boundary_orientation p * omega p) =
    finite_boundary_zero_integral
      (K \<inter> boundary_carrier)
      (\<lambda>p. boundary_orientation p * omega p)"
  proof -
    have sum_eq:
      "(\<Sum>p\<in>?B.
        boundary_orientation p * omega p) =
      (\<Sum>p\<in>?B \<inter> K.
        boundary_orientation p * omega p)"
      by (rule sum.mono_neutral_right[OF finiteB])
         (use omega_support subsetB
           boundary_subset_carrier in auto)
    have "?B \<inter> K = K \<inter> boundary_carrier"
      using selected_boundary_on_compact_support
        [OF FI coverF] by auto
    then show ?thesis
      using sum_eq
      by (simp add: finite_boundary_zero_integral_def)
  qed
  show ?thesis using glued boundary_restrict by simp
qed

end

end
