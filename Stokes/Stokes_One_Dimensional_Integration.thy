theory Stokes_One_Dimensional_Integration
  imports Stokes_One_Dimensional_Global
begin

lemma halfline_openin_at_within:
  fixes S :: "real set"
  assumes openS: "openin (top_of_set {0..}) S"
    and tS: "t \<in> S"
  shows "at t within S = at t within {0..}"
proof -
  obtain W where W: "open W" "S = {0..} \<inter> W"
    using openS by (auto simp: openin_open)
  show ?thesis
    by (rule at_within_nhd[where S=W])
      (use W tS in auto)
qed

lemma real_absolutely_integrable_compact_support:
  fixes f :: "real \<Rightarrow> real"
  assumes compact: "compact Q"
    and continuous: "continuous_on Q f"
    and subset: "Q \<subseteq> S"
    and zero: "\<And>x. x \<in> S \<Longrightarrow> x \<notin> Q \<Longrightarrow> f x = 0"
  shows "f absolutely_integrable_on S"
proof -
  have bounded: "bounded (f ` Q)"
    by (rule compact_imp_bounded)
      (rule compact_continuous_image[OF continuous compact])
  obtain B where B: "0 < B"
    "\<And>x. x \<in> Q \<Longrightarrow> norm (f x) \<le> B"
    using bounded unfolding bounded_pos by auto
  have Q_borel: "Q \<in> sets borel"
    using compact by (auto intro: borel_closed compact_imp_closed)
  have Q_measurable: "Q \<in> lmeasurable"
    by (rule lmeasurable_compact[OF compact])
  have fm_borel: "(\<lambda>x. indicator Q x *\<^sub>R f x)
      \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_on_indicator
      [OF Q_borel continuous])
  have fm_lebesgue: "(\<lambda>x. indicator Q x *\<^sub>R f x)
      \<in> borel_measurable lebesgue"
    using fm_borel by (simp add: measurable_completion)
  have intQ: "f absolutely_integrable_on Q"
  proof (rule set_integrable_bound
      [where f="\<lambda>_. B" and M=lebesgue and A=Q])
    show "(\<lambda>_. B) absolutely_integrable_on Q"
      using Q_measurable by simp
    show "set_borel_measurable lebesgue Q f"
      using fm_lebesgue
      by (simp add: set_borel_measurable_def)
    show "AE x in lebesgue.
      x \<in> Q \<longrightarrow> norm (f x) \<le> norm ((\<lambda>_. B) x)"
      using B by (auto intro: always_eventually)
  qed
  have eq: "(\<lambda>x. indicator S x *\<^sub>R f x) =
    (\<lambda>x. indicator Q x *\<^sub>R f x)"
  proof (rule ext)
    fix x
    show "indicator S x *\<^sub>R f x =
      indicator Q x *\<^sub>R f x"
      using subset zero[of x]
      by (cases "x \<in> Q"; cases "x \<in> S") auto
  qed
  show ?thesis
    using intQ unfolding set_integrable_def eq by simp
qed

lemma real_lborel_integrable_compact_support:
  fixes f :: "real \<Rightarrow> real"
  assumes compact: "compact Q"
    and continuous: "continuous_on Q f"
    and subset: "Q \<subseteq> S"
    and zero: "\<And>x. x \<in> S \<Longrightarrow>
      x \<notin> Q \<Longrightarrow> f x = 0"
  shows "set_integrable lborel S f"
proof -
  have abs: "f absolutely_integrable_on S"
    by (rule real_absolutely_integrable_compact_support
      [OF compact continuous subset zero])
  have Q_borel: "Q \<in> sets borel"
    using compact by (auto intro: borel_closed compact_imp_closed)
  have measurableQ:
    "(\<lambda>x. indicator Q x *\<^sub>R f x)
      \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_on_indicator
      [OF Q_borel continuous])
  have eq: "(\<lambda>x. indicator S x *\<^sub>R f x) =
    (\<lambda>x. indicator Q x *\<^sub>R f x)"
  proof (rule ext)
    fix x
    show "indicator S x *\<^sub>R f x =
      indicator Q x *\<^sub>R f x"
      using subset zero[of x]
      by (cases "x \<in> Q"; cases "x \<in> S") auto
  qed
  have measurableS:
    "(\<lambda>x. indicator S x *\<^sub>R f x)
      \<in> borel_measurable lborel"
  proof -
    have measurableQlb:
      "(\<lambda>x. indicator Q x *\<^sub>R f x)
        \<in> borel_measurable lborel"
      using measurableQ by (simp add: sets_lborel)
    show ?thesis
      using measurableQlb by (simp only: eq)
  qed
  show ?thesis
    using abs measurableS
    by (simp add: set_integrable_def
      integrable_completion)
qed

lemma halfline_derivative_zero_outside_compact:
  fixes F g :: "real \<Rightarrow> real"
  assumes openC: "openin (top_of_set {0::real..}) C"
    and compactQ: "compact Q"
    and zeroF: "\<And>t. t \<in> C \<Longrightarrow>
      t \<notin> Q \<Longrightarrow> F t = 0"
    and deriv: "\<And>t. t \<in> C \<Longrightarrow>
      (F has_vector_derivative g t)
      (at t within {0..})"
    and t: "t \<in> C" "t \<notin> Q"
  shows "g t = 0"
proof -
  obtain U where U: "open U"
    "C = {0..} \<inter> U"
    using openC by (auto simp: openin_open)
  have closedQ: "closed Q"
    by (rule compact_imp_closed[OF compactQ])
  have tH: "0 \<le> t"
    using t U(2) by auto
  have cont_id: "continuous_on UNIV (id::real \<Rightarrow> real)"
    by (rule continuous_on_id')
  have fun_eq: "(\<lambda>s. F (id s)) = F"
    by (rule ext) (simp add: id_def)
  have raw_deriv:
      "((\<lambda>s. F (id s)) has_vector_derivative g t)
        (at t within {0..})"
    using deriv[OF t(1)] by (simp only: fun_eq)
  show ?thesis
    by (rule vector_derivative_zero_on_relative_open
      [where c=id and H="{0..}" and U=U and
        K=Q and S="{0..}" and F=F and t=t,
        OF U(1) closedQ cont_id])
      (use t tH U zeroF raw_deriv
        halfline_at_within_nontrivial[OF tH]
        in auto)
qed

context oriented_C1_halfline_atlas
begin

definition exact_one_form where
  "exact_one_form omega i t =
    vector_derivative
      (\<lambda>s. omega (from_chart i s))
      (at t within {0..})"

definition one_form_compatible where
  "one_form_compatible A \<longleftrightarrow>
    (\<forall>i\<in>I. \<forall>j\<in>I. \<forall>t\<in>overlap i j.
      A i t =
        eucl.det (transition_deriv i j t) *
          A j (transition i j t))"

lemma chartwise_C1_exact_derivative:
  assumes smooth: "chartwise_C1_scalar omega"
    and i: "i \<in> I" and t: "t \<in> C i"
  shows "((\<lambda>s. omega (from_chart i s))
    has_vector_derivative exact_one_form omega i t)
      (at t within {0..})"
proof -
  obtain g where g:
    "\<forall>t\<in>C i.
      ((\<lambda>s. omega (from_chart i s))
        has_vector_derivative g t)
        (at t within {0..})"
    using chartwise_C1_halfline_derivative_data
      [OF smooth i] by blast
  have nontrivial: "at t within {0::real..} \<noteq> bot"
    by (rule halfline_at_within_nontrivial)
      (use t halfline_chart.codomain_subset_halfline
        [OF chart[OF i]] in auto)
  have eq: "exact_one_form omega i t = g t"
    unfolding exact_one_form_def
    by (rule vector_derivative_within
      [OF nontrivial])
      (use g t in auto)
  show ?thesis using g t eq by simp
qed

lemma exact_one_form_continuous:
  assumes smooth: "chartwise_C1_scalar omega"
    and i: "i \<in> I"
  shows "continuous_on (C i) (exact_one_form omega i)"
proof -
  obtain g where g:
    "\<forall>t\<in>C i.
      ((\<lambda>s. omega (from_chart i s))
        has_vector_derivative g t)
        (at t within {0..})"
    "continuous_on (C i) g"
    using chartwise_C1_halfline_derivative_data
      [OF smooth i] by blast
  have eq: "exact_one_form omega i t = g t"
    if t: "t \<in> C i" for t
  proof -
    have "0 \<le> t"
      using t halfline_chart.codomain_subset_halfline
        [OF chart[OF i]] by auto
    then have nontrivial:
      "at t within {0::real..} \<noteq> bot"
      by (rule halfline_at_within_nontrivial)
    show ?thesis
      unfolding exact_one_form_def
      by (rule vector_derivative_within
        [OF nontrivial])
        (use g t in auto)
  qed
  show ?thesis
    by (rule continuous_on_eq[OF g(2)])
      (use eq in auto)
qed

lemma chartwise_C1_pullback_continuous:
  assumes smooth: "chartwise_C1_scalar omega"
    and i: "i \<in> I"
  shows "continuous_on (C i)
    (\<lambda>t. omega (from_chart i t))"
proof (rule continuous_on_vector_derivative)
  fix t assume t: "t \<in> C i"
  have sub: "C i \<subseteq> {0::real..}"
    by (rule halfline_chart.codomain_subset_halfline
      [OF chart[OF i]])
  show "((\<lambda>s. omega (from_chart i s))
    has_vector_derivative exact_one_form omega i t)
    (at t within C i)"
    by (rule has_vector_derivative_within_subset
      [OF chartwise_C1_exact_derivative[OF smooth i t]
        sub])
qed

lemma transition_has_vector_derivative:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and t: "t \<in> overlap i j"
  shows "(transition i j has_vector_derivative
      eucl.det (transition_deriv i j t))
      (at t within overlap i j)"
proof -
  have der: "(transition i j has_derivative
      transition_deriv i j t)
      (at t within overlap i j)"
    by (rule transition_differentiable[OF i j t])
  obtain c where c: "transition_deriv i j t =
    (\<lambda>x. x * c)"
    using real_bounded_linear
      has_derivative_bounded_linear[OF der]
    by metis
  have "c = eucl.det (transition_deriv i j t)"
    by (simp add: c)
  then show ?thesis
    using der
    by (simp add: c has_vector_derivative_def
      algebra_simps)
qed

lemma exact_one_form_compatible:
  assumes smooth: "chartwise_C1_scalar omega"
  shows "one_form_compatible (exact_one_form omega)"
  unfolding one_form_compatible_def
proof (intro ballI)
  fix i j t
  assume i: "i \<in> I" and j: "j \<in> I"
    and t: "t \<in> overlap i j"
  let ?T = "transition i j"
  let ?fi = "\<lambda>s. omega (from_chart i s)"
  let ?fj = "\<lambda>s. omega (from_chart j s)"
  have tCi: "t \<in> C i"
    using overlap_subset_codomain[OF i] t by auto
  have sCj: "?T t \<in> C j"
    using transition_overlap[OF i j t]
      overlap_subset_codomain[OF j] by auto
  have di: "(?fi has_vector_derivative
      exact_one_form omega i t)
      (at t within {0..})"
    by (rule chartwise_C1_exact_derivative
      [OF smooth i tCi])
  have dj: "(?fj has_vector_derivative
      exact_one_form omega j (?T t))
      (at (?T t) within {0..})"
    by (rule chartwise_C1_exact_derivative
      [OF smooth j sCj])
  have over_i: "openin (top_of_set {0..})
      (overlap i j)"
    by (rule openin_trans
      [OF overlap_open[OF i j]
        halfline_chart.open_C[OF chart[OF i]]])
  have over_j: "overlap j i \<subseteq> {0::real..}"
    using overlap_subset_codomain[OF j]
      halfline_chart.codomain_subset_halfline
        [OF chart[OF j]] by auto
  have dj_overlap: "(?fj has_vector_derivative
      exact_one_form omega j (?T t))
      (at (?T t) within overlap j i)"
    by (rule has_vector_derivative_within_subset
      [OF dj over_j])
  have chain: "((?fj \<circ> ?T) has_vector_derivative
      eucl.det (transition_deriv i j t) *
        exact_one_form omega j (?T t))
      (at t within overlap i j)"
  proof -
    have d: "(?fj has_vector_derivative
        exact_one_form omega j (?T t))
        (at (?T t) within ?T ` overlap i j)"
      using dj_overlap transition_image[OF i j]
      by simp
    show ?thesis
      using vector_diff_chain_within
        [OF transition_has_vector_derivative[OF i j t] d]
      by (simp add: o_def)
  qed
  have eq: "\<And>s. s \<in> overlap i j \<Longrightarrow>
      (?fj \<circ> ?T) s = ?fi s"
    by (simp add: transition_point[OF i j] o_def)
  have chain_i: "(?fi has_vector_derivative
      eucl.det (transition_deriv i j t) *
        exact_one_form omega j (?T t))
      (at t within overlap i j)"
    by (rule has_vector_derivative_transform
      [OF t _ chain])
      (use eq in auto)
  have nontrivial: "at t within overlap i j \<noteq> bot"
    using halfline_openin_at_within[OF over_i t]
      halfline_at_within_nontrivial t over_i
    by (auto simp: openin_open)
  have di_overlap: "(?fi has_vector_derivative
      exact_one_form omega i t)
      (at t within overlap i j)"
    by (rule has_vector_derivative_within_subset
      [OF di])
      (use overlap_subset_codomain[OF i]
        halfline_chart.codomain_subset_halfline
          [OF chart[OF i]] in auto)
  show "exact_one_form omega i t =
    eucl.det (transition_deriv i j t) *
      exact_one_form omega j (transition i j t)"
    by (rule vector_derivative_unique_within
      [OF nontrivial di_overlap chain_i])
qed

lemma exact_one_form_closed_support:
  assumes closed: "closed K"
    and support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and smooth: "chartwise_C1_scalar omega"
    and i: "i \<in> I" and tC: "t \<in> C i"
    and out: "from_chart i t \<notin> K"
  shows "exact_one_form omega i t = 0"
proof -
  have openB: "open (- K)"
    by (rule open_Compl[OF closed])
  have from_cont:
    "continuous_on (C i) (from_chart i)"
    by (rule homeomorphism_cont2
      [OF halfline_chart.homeo[OF chart[OF i]]])
  have local:
    "\<exists>W. open W \<and> t \<in> W \<and>
      (\<forall>s\<in>C i. s \<in> W \<longrightarrow>
        from_chart i s \<in> - K)"
    using continuous_on_topological[THEN iffD1,
      OF from_cont] tC openB out
    by blast
  obtain W where W: "open W" "t \<in> W"
    "\<And>s. s \<in> C i \<Longrightarrow> s \<in> W \<Longrightarrow>
      from_chart i s \<notin> K"
    using local by auto
  obtain U where U: "open U"
    "C i = {0..} \<inter> U"
    using halfline_chart.open_C[OF chart[OF i]]
    by (auto simp: openin_open)
  have tU: "t \<in> U"
    using U(2) tC by auto
  have openV: "open (U \<inter> W)"
    using U(1) W(1) by auto
  have tV: "t \<in> U \<inter> W"
    using tU W(2) by auto
  obtain d :: real where d: "0 < d"
    "ball t d \<subseteq> U \<inter> W"
    using open_contains_ball[THEN iffD1, OF openV]
      tV by blast
  have tH: "t \<in> {0::real..}"
    using tC U(2) by auto
  have zero_near: "omega (from_chart i s) = 0"
    if sH: "s \<in> {0::real..}"
      and near: "dist s t < d" for s
  proof -
    have sV: "s \<in> U \<inter> W"
      using d(2) near by (auto simp: dist_commute)
    have sC: "s \<in> C i"
      using sH sV U(2) by auto
    have pM: "from_chart i s \<in> M"
      using halfline_chart.inverse_image[OF chart[OF i]]
        domain_subset_carrier[OF i] sC by auto
    have pnot: "from_chart i s \<notin> K"
      by (rule W(3)[OF sC])
        (use sV in auto)
    show ?thesis
      by (rule support[OF pM pnot])
  qed
  have der0: "((\<lambda>s. omega (from_chart i s))
      has_vector_derivative 0)
      (at t within {0..})"
  proof (rule has_vector_derivative_transform_within
      [OF _ d(1) tH])
    show "((\<lambda>_. 0::real) has_vector_derivative 0)
      (at t within {0..})"
      by (auto simp: has_vector_derivative_def
        intro!: derivative_intros)
    show "\<And>s. s \<in> {0::real..} \<Longrightarrow>
      dist s t < d \<Longrightarrow>
      (0::real) = omega (from_chart i s)"
      using zero_near by auto
  qed
  have der: "((\<lambda>s. omega (from_chart i s))
      has_vector_derivative exact_one_form omega i t)
      (at t within {0..})"
    by (rule chartwise_C1_exact_derivative
      [OF smooth i tC])
  have nontrivial: "at t within {0::real..} \<noteq> bot"
    by (rule halfline_at_within_nontrivial)
      (use tH in auto)
  show ?thesis
    by (rule vector_derivative_unique_within
      [OF nontrivial der der0])
qed

lemma exact_one_form_compact_support:
  assumes compact: "compact K"
    and support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and smooth: "chartwise_C1_scalar omega"
    and i: "i \<in> I" and tC: "t \<in> C i"
    and out: "from_chart i t \<notin> K"
  shows "exact_one_form omega i t = 0"
  by (rule exact_one_form_closed_support
    [OF compact_imp_closed[OF compact] support
      smooth i tC out])

lemma exact_one_form_product:
  assumes omega: "chartwise_C1_scalar omega"
    and phi: "chartwise_C1_scalar phi"
    and i: "i \<in> I" and t: "t \<in> C i"
  shows "exact_one_form (\<lambda>p. phi p * omega p) i t =
    phi (from_chart i t) * exact_one_form omega i t +
      exact_one_form phi i t * omega (from_chart i t)"
proof -
  have dp: "((\<lambda>s. phi (from_chart i s))
    has_vector_derivative exact_one_form phi i t)
    (at t within {0..})"
    by (rule chartwise_C1_exact_derivative[OF phi i t])
  have dw: "((\<lambda>s. omega (from_chart i s))
    has_vector_derivative exact_one_form omega i t)
    (at t within {0..})"
    by (rule chartwise_C1_exact_derivative[OF omega i t])
  have dprod: "((\<lambda>s. phi (from_chart i s) *
      omega (from_chart i s)) has_vector_derivative
      phi (from_chart i t) * exact_one_form omega i t +
        exact_one_form phi i t * omega (from_chart i t))
      (at t within {0..})"
    by (rule has_vector_derivative_mult[OF dp dw])
  have nontrivial: "at t within {0::real..} \<noteq> bot"
    by (rule halfline_at_within_nontrivial)
      (use t halfline_chart.codomain_subset_halfline
        [OF chart[OF i]] in auto)
  show ?thesis
    unfolding exact_one_form_def
    by (rule vector_derivative_within
      [OF nontrivial
        dprod[unfolded exact_one_form_def]])
qed

lemma exact_partition_derivative_cancel:
  assumes finiteF: "finite F"
    and unity: "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i p) = 1"
    and support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and smooth: "chartwise_C1_scalar omega"
    and phiC1: "\<And>i. i \<in> F \<Longrightarrow>
      chartwise_C1_scalar (phi i)"
    and j: "j \<in> I" and t: "t \<in> C j"
  shows "omega (from_chart j t) *
    (\<Sum>i\<in>F. exact_one_form (phi i) j t) = 0"
proof (cases "omega (from_chart j t) = 0")
  case True
  then show ?thesis by simp
next
  case False
  let ?w = "\<lambda>s. omega (from_chart j s)"
  let ?f = "\<lambda>s. \<Sum>i\<in>F. phi i (from_chart j s)"
  have wcont: "continuous_on (C j) ?w"
    by (rule chartwise_C1_pullback_continuous
      [OF smooth j])
  have openB: "open (- {0::real})"
    by (rule open_Compl) simp
  have tB: "?w t \<in> - {0::real}"
    using False by simp
  have local: "\<exists>W. open W \<and> t \<in> W \<and>
    (\<forall>s\<in>C j. s \<in> W \<longrightarrow>
      ?w s \<in> - {0::real})"
    using continuous_on_topological[THEN iffD1,
      OF wcont] t openB tB
    by blast
  obtain W where W: "open W" "t \<in> W"
    "\<And>s. s \<in> C j \<Longrightarrow> s \<in> W \<Longrightarrow>
      ?w s \<noteq> 0"
    using local by auto
  obtain U where U: "open U"
    "C j = {0..} \<inter> U"
    using halfline_chart.open_C[OF chart[OF j]]
    by (auto simp: openin_open)
  have tU: "t \<in> U"
    using t U(2) by auto
  have openV: "open (U \<inter> W)"
    using U(1) W(1) by auto
  have tV: "t \<in> U \<inter> W"
    using tU W(2) by auto
  obtain d :: real where d: "0 < d"
    "ball t d \<subseteq> U \<inter> W"
    using open_contains_ball[THEN iffD1, OF openV]
      tV by blast
  have tH: "t \<in> {0::real..}"
    using t U(2) by auto
  have one_near: "?f s = 1"
    if sH: "s \<in> {0::real..}"
      and near: "dist s t < d" for s
  proof -
    have sV: "s \<in> U \<inter> W"
      using d(2) near by (auto simp: dist_commute)
    have sC: "s \<in> C j"
      using sH sV U(2) by auto
    have pM: "from_chart j s \<in> M"
      using halfline_chart.inverse_image[OF chart[OF j]]
        domain_subset_carrier[OF j] sC by auto
    have pK: "from_chart j s \<in> K"
      using support[OF pM] W(3)[OF sC] sV
      by auto
    show ?thesis
      by (rule unity[OF pK])
  qed
  have der_sum: "(?f has_vector_derivative
      (\<Sum>i\<in>F. exact_one_form (phi i) j t))
      (at t within {0..})"
  proof (rule has_vector_derivative_sum)
    fix i assume iF: "i \<in> F"
    show "((\<lambda>s. phi i (from_chart j s))
      has_vector_derivative exact_one_form (phi i) j t)
      (at t within {0..})"
      by (rule chartwise_C1_exact_derivative
        [OF phiC1[OF iF] j t])
  qed
  have der0: "(?f has_vector_derivative 0)
      (at t within {0..})"
  proof (rule has_vector_derivative_transform_within
      [OF _ d(1) tH])
    show "((\<lambda>_. 1::real) has_vector_derivative 0)
      (at t within {0..})"
      by (auto simp: has_vector_derivative_def
        intro!: derivative_intros)
    show "\<And>s. s \<in> {0::real..} \<Longrightarrow>
      dist s t < d \<Longrightarrow>
      (1::real) = ?f s"
      using one_near by auto
  qed
  have nontrivial: "at t within {0::real..} \<noteq> bot"
    by (rule halfline_at_within_nontrivial)
      (use tH in auto)
  have zero: "(\<Sum>i\<in>F.
      exact_one_form (phi i) j t) = 0"
    by (rule vector_derivative_unique_within
      [OF nontrivial der_sum der0])
  show ?thesis
    by (simp add: zero)
qed

definition one_form_chart_value where
  "one_form_chart_value F phi A =
    (\<Sum>i\<in>F. eps i *
      integral (C i)
        (\<lambda>t. phi i (from_chart i t) * A i t))"

lemma one_form_cross_change:
  fixes A :: "'i \<Rightarrow> real \<Rightarrow> real"
    and phi psi :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes i: "i \<in> I" and j: "j \<in> I"
    and compatible: "one_form_compatible A"
    and integrable:
      "(\<lambda>s. psi j (from_chart j s) *
        phi i (from_chart j s) * A j s)
        absolutely_integrable_on overlap j i"
  shows "eps i *
      integral (overlap i j)
        (\<lambda>t. phi i (from_chart i t) *
          psi j (from_chart i t) * A i t) =
    eps j *
      integral (overlap j i)
        (\<lambda>s. psi j (from_chart j s) *
          phi i (from_chart j s) * A j s)"
proof (rule oriented_transition_integral
    [OF i j integrable])
  fix t assume t: "t \<in> overlap i j"
  have point: "from_chart j (transition i j t) =
    from_chart i t"
    by (rule transition_point[OF i j t])
  have A: "A i t =
      eucl.det (transition_deriv i j t) *
        A j (transition i j t)"
    using compatible i j t
    by (auto simp: one_form_compatible_def)
  show "phi i (from_chart i t) *
      psi j (from_chart i t) * A i t =
    eucl.det (transition_deriv i j t) *
      (psi j (from_chart j (transition i j t)) *
        phi i (from_chart j (transition i j t)) *
        A j (transition i j t))"
    by (simp add: point A algebra_simps)
qed

lemma one_form_chart_refinement:
  fixes A :: "'i \<Rightarrow> real \<Rightarrow> real"
    and phi psi :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes i: "i \<in> I"
    and finiteH: "finite H"
    and HI: "H \<subseteq> I"
    and unity: "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>j\<in>H. psi j p) = 1"
    and support: "\<And>t. t \<in> C i \<Longrightarrow>
      from_chart i t \<notin> K \<Longrightarrow> A i t = 0"
    and psi_outside: "\<And>j p. j \<in> H \<Longrightarrow>
      p \<in> M \<Longrightarrow> p \<notin> D j
      \<Longrightarrow> psi j p = 0"
    and integrable: "\<And>j. j \<in> H \<Longrightarrow>
      (\<lambda>t. phi i (from_chart i t) *
        psi j (from_chart i t) * A i t)
        absolutely_integrable_on C i"
  shows "integral (C i)
      (\<lambda>t. phi i (from_chart i t) * A i t) =
    (\<Sum>j\<in>H. integral (overlap i j)
      (\<lambda>t. phi i (from_chart i t) *
        psi j (from_chart i t) * A i t))"
proof -
  let ?f = "\<lambda>j t. phi i (from_chart i t) *
    psi j (from_chart i t) * A i t"
  have pointwise: "phi i (from_chart i t) * A i t =
      (\<Sum>j\<in>H. ?f j t)"
    if t: "t \<in> C i" for t
  proof -
    have pM: "from_chart i t \<in> M"
      using halfline_chart.inverse_image[OF chart[OF i]]
        domain_subset_carrier[OF i] t by auto
    show ?thesis
    proof (cases "from_chart i t \<in> K")
      case True
      have factor: "(\<Sum>j\<in>H. ?f j t) =
        (phi i (from_chart i t) * A i t) *
          (\<Sum>j\<in>H. psi j (from_chart i t))"
        by (simp add: sum_distrib_left[symmetric]
          algebra_simps)
      then show ?thesis
        using unity[OF True] by simp
    next
      case False
      then show ?thesis
        using support[OF t] by simp
    qed
  qed
  have int: "?f j integrable_on C i"
    if j: "j \<in> H" for j
    using integrable[OF j]
    by (simp add: absolutely_integrable_on_def)
  have split: "integral (C i)
      (\<lambda>t. phi i (from_chart i t) * A i t) =
      (\<Sum>j\<in>H. integral (C i) (?f j))"
  proof -
    have "integral (C i)
      (\<lambda>t. phi i (from_chart i t) * A i t) =
      integral (C i) (\<lambda>t. \<Sum>j\<in>H. ?f j t)"
      by (rule integral_cong) (use pointwise in auto)
    also have "\<dots> =
      (\<Sum>j\<in>H. integral (C i) (?f j))"
      by (rule integral_sum[OF finiteH int])
    finally show ?thesis .
  qed
  have restrict: "integral (C i) (?f j) =
      integral (overlap i j) (?f j)"
    if j: "j \<in> H" for j
  proof -
    have eq: "?f j t = 0"
      if t: "t \<in> C i"
        and out: "t \<notin> overlap i j" for t
    proof -
      have pM: "from_chart i t \<in> M"
        using halfline_chart.inverse_image[OF chart[OF i]]
          domain_subset_carrier[OF i] t by auto
      have pnotD: "from_chart i t \<notin> D j"
        using t out overlap_preimage[OF i] by auto
      show ?thesis
        using psi_outside[OF j pM pnotD] by simp
    qed
    have "integral (C i) (?f j) =
      integral (C i)
        (\<lambda>t. if t \<in> overlap i j
          then ?f j t else 0)"
      by (rule integral_cong) (use eq in auto)
    also have "\<dots> =
      integral (overlap i j \<inter> C i) (?f j)"
      by (rule integral_restrict_Int)
    also have "\<dots> = integral (overlap i j) (?f j)"
    proof -
      have "overlap i j \<inter> C i = overlap i j"
        using overlap_subset_codomain[OF i] by auto
      then show ?thesis by simp
    qed
    finally show ?thesis .
  qed
  show ?thesis
    using split
    by (simp add: sum.cong[OF refl, OF restrict])
qed

lemma one_form_cross_integrable:
  fixes A :: "'i \<Rightarrow> real \<Rightarrow> real"
    and phi psi :: "'a \<Rightarrow> real"
  assumes i: "i \<in> I" and j: "j \<in> I"
    and compact: "compact K"
    and Acont: "continuous_on (C i) (A i)"
    and Asupport: "\<And>t. t \<in> C i \<Longrightarrow>
      from_chart i t \<notin> K \<Longrightarrow> A i t = 0"
    and phicont: "continuous_on M phi"
    and psicont: "continuous_on M psi"
    and closedL: "closed L" and LD: "L \<subseteq> D i"
    and phisupport:
      "{p\<in>M. phi p \<noteq> 0} \<subseteq> L"
    and closedR: "closed R" and RD: "R \<subseteq> D j"
    and psisupport:
      "{p\<in>M. psi p \<noteq> 0} \<subseteq> R"
  shows
    "(\<lambda>t. phi (from_chart i t) *
      psi (from_chart i t) * A i t)
      absolutely_integrable_on C i"
    "(\<lambda>t. phi (from_chart i t) *
      psi (from_chart i t) * A i t)
      absolutely_integrable_on overlap i j"
proof -
  let ?f = "\<lambda>t. phi (from_chart i t) *
      psi (from_chart i t) * A i t"
  let ?Q = "to_chart i ` (K \<inter> L \<inter> R)"
  have KL: "compact (K \<inter> L \<inter> R)"
    by (rule compact_Int_closed
      [OF compact_Int_closed[OF compact closedL] closedR])
  have KLD: "K \<inter> L \<inter> R \<subseteq> D i"
    using LD by auto
  have KRj: "K \<inter> L \<inter> R \<subseteq> D j"
    using RD by auto
  have to_cont: "continuous_on (D i) (to_chart i)"
    by (rule halfline_chart.chart_continuous
      [OF chart[OF i]])
  have compactQ: "compact ?Q"
    by (rule compact_continuous_image)
      (use to_cont KL KLD in
        \<open>auto intro: continuous_on_subset\<close>)
  have QC: "?Q \<subseteq> C i"
    using halfline_chart.chart_image[OF chart[OF i]]
      KLD by auto
  have Qover: "?Q \<subseteq> overlap i j"
    using KLD KRj
    by (auto simp: overlap_def)
  have from_cont:
    "continuous_on (C i) (from_chart i)"
    by (rule homeomorphism_cont2
      [OF halfline_chart.homeo[OF chart[OF i]]])
  have fromM: "from_chart i ` C i \<subseteq> M"
    using halfline_chart.inverse_image[OF chart[OF i]]
      domain_subset_carrier[OF i] by auto
  have phiC: "continuous_on (C i)
      (\<lambda>t. phi (from_chart i t))"
    by (rule continuous_on_compose2
      [OF phicont from_cont fromM])
  have psiC: "continuous_on (C i)
      (\<lambda>t. psi (from_chart i t))"
    by (rule continuous_on_compose2
      [OF psicont from_cont fromM])
  have fC: "continuous_on (C i) ?f"
    by (intro continuous_on_mult phiC psiC Acont)
  have fQ: "continuous_on ?Q ?f"
    by (rule continuous_on_subset[OF fC QC])
  have zero: "?f t = 0"
    if tC: "t \<in> C i" and out: "t \<notin> ?Q" for t
  proof (rule ccontr)
    assume nz: "?f t \<noteq> 0"
    let ?p = "from_chart i t"
    have pD: "?p \<in> D i"
      using halfline_chart.inverse_image
        [OF chart[OF i]] tC by auto
    have pM: "?p \<in> M"
      using domain_subset_carrier[OF i] pD by auto
    have pK: "?p \<in> K"
      using Asupport[OF tC] nz by auto
    have pL: "?p \<in> L"
      using phisupport pM nz by auto
    have pR: "?p \<in> R"
      using psisupport pM nz by auto
    have "to_chart i ?p = t"
      by (rule halfline_chart.from_to
        [OF chart[OF i] tC])
    moreover have "to_chart i ?p \<in> ?Q"
      using pK pL pR by blast
    ultimately show False
      using out by simp
  qed
  show "?f absolutely_integrable_on C i"
    by (rule real_absolutely_integrable_compact_support
      [OF compactQ fQ QC zero])
  show "?f absolutely_integrable_on overlap i j"
  proof (rule real_absolutely_integrable_compact_support
      [OF compactQ fQ Qover])
    fix t
    assume t: "t \<in> overlap i j" "t \<notin> ?Q"
    have "t \<in> C i"
      using t overlap_subset_codomain[OF i] by auto
    then show "?f t = 0"
      by (rule zero[OF _ t(2)])
  qed
qed

lemma one_form_weighted_integrable:
  fixes A :: "'i \<Rightarrow> real \<Rightarrow> real"
    and psi :: "'a \<Rightarrow> real"
  assumes i: "i \<in> I" and j: "j \<in> I"
    and compact: "compact K"
    and Acont: "continuous_on (C i) (A i)"
    and AsupportK: "\<And>t. t \<in> C i \<Longrightarrow>
      from_chart i t \<notin> K \<Longrightarrow> A i t = 0"
    and AsupportL: "\<And>t. t \<in> C i \<Longrightarrow>
      from_chart i t \<notin> L \<Longrightarrow> A i t = 0"
    and closedL: "closed L"
    and psicont: "continuous_on M psi"
    and closedR: "closed R"
    and domains: "L \<inter> R \<subseteq> D i \<inter> D j"
    and psisupport:
      "{p\<in>M. psi p \<noteq> 0} \<subseteq> R"
  shows
    "(\<lambda>t. psi (from_chart i t) * A i t)
      absolutely_integrable_on C i"
    "(\<lambda>t. psi (from_chart i t) * A i t)
      absolutely_integrable_on overlap i j"
proof -
  let ?f = "\<lambda>t. psi (from_chart i t) * A i t"
  let ?Q = "to_chart i ` (K \<inter> L \<inter> R)"
  have KL: "compact (K \<inter> L \<inter> R)"
    by (rule compact_Int_closed
      [OF compact_Int_closed[OF compact closedL] closedR])
  have KLD: "K \<inter> L \<inter> R \<subseteq> D i"
    using domains by auto
  have KRj: "K \<inter> L \<inter> R \<subseteq> D j"
    using domains by auto
  have to_cont: "continuous_on (D i) (to_chart i)"
    by (rule halfline_chart.chart_continuous
      [OF chart[OF i]])
  have compactQ: "compact ?Q"
    by (rule compact_continuous_image)
      (use to_cont KL KLD in
        \<open>auto intro: continuous_on_subset\<close>)
  have QC: "?Q \<subseteq> C i"
    using halfline_chart.chart_image[OF chart[OF i]]
      KLD by auto
  have Qover: "?Q \<subseteq> overlap i j"
    using KLD KRj
    by (auto simp: overlap_def)
  have from_cont:
    "continuous_on (C i) (from_chart i)"
    by (rule homeomorphism_cont2
      [OF halfline_chart.homeo[OF chart[OF i]]])
  have fromM: "from_chart i ` C i \<subseteq> M"
    using halfline_chart.inverse_image[OF chart[OF i]]
      domain_subset_carrier[OF i] by auto
  have psiC: "continuous_on (C i)
      (\<lambda>t. psi (from_chart i t))"
    by (rule continuous_on_compose2
      [OF psicont from_cont fromM])
  have fC: "continuous_on (C i) ?f"
    by (intro continuous_on_mult psiC Acont)
  have fQ: "continuous_on ?Q ?f"
    by (rule continuous_on_subset[OF fC QC])
  have zero: "?f t = 0"
    if tC: "t \<in> C i" and out: "t \<notin> ?Q"
    for t
  proof (rule ccontr)
    assume nz: "?f t \<noteq> 0"
    let ?p = "from_chart i t"
    have pD: "?p \<in> D i"
      using halfline_chart.inverse_image
        [OF chart[OF i]] tC by auto
    have pM: "?p \<in> M"
      using domain_subset_carrier[OF i] pD by auto
    have pK: "?p \<in> K"
      using AsupportK[OF tC] nz by auto
    have pL: "?p \<in> L"
      using AsupportL[OF tC] nz by auto
    have pR: "?p \<in> R"
      using psisupport pM nz by auto
    have "to_chart i ?p = t"
      by (rule halfline_chart.from_to
        [OF chart[OF i] tC])
    moreover have "to_chart i ?p \<in> ?Q"
      using pK pL pR by blast
    ultimately show False
      using out by simp
  qed
  show "?f absolutely_integrable_on C i"
    by (rule real_absolutely_integrable_compact_support
      [OF compactQ fQ QC zero])
  show "?f absolutely_integrable_on overlap i j"
  proof (rule real_absolutely_integrable_compact_support
      [OF compactQ fQ Qover])
    fix t
    assume t: "t \<in> overlap i j" "t \<notin> ?Q"
    have "t \<in> C i"
      using t overlap_subset_codomain[OF i] by auto
    then show "?f t = 0"
      by (rule zero[OF _ t(2)])
  qed
qed

lemma one_form_localized_integrable:
  fixes A :: "'i \<Rightarrow> real \<Rightarrow> real"
    and phi :: "'a \<Rightarrow> real"
  assumes i: "i \<in> I" and compact: "compact K"
    and Acont: "continuous_on (C i) (A i)"
    and Asupport: "\<And>t. t \<in> C i \<Longrightarrow>
      from_chart i t \<notin> K \<Longrightarrow> A i t = 0"
    and phicont: "continuous_on M phi"
    and closedL: "closed L" and LD: "L \<subseteq> D i"
    and phisupport:
      "{p\<in>M. phi p \<noteq> 0} \<subseteq> L"
  shows "(\<lambda>t. phi (from_chart i t) * A i t)
    absolutely_integrable_on C i"
proof -
  let ?f = "\<lambda>t. phi (from_chart i t) * A i t"
  let ?Q = "to_chart i ` (K \<inter> L)"
  have KL: "compact (K \<inter> L)"
    by (rule compact_Int_closed[OF compact closedL])
  have KLD: "K \<inter> L \<subseteq> D i"
    using LD by auto
  have to_cont: "continuous_on (D i) (to_chart i)"
    by (rule halfline_chart.chart_continuous
      [OF chart[OF i]])
  have compactQ: "compact ?Q"
    by (rule compact_continuous_image)
      (use to_cont KL KLD in
        \<open>auto intro: continuous_on_subset\<close>)
  have QC: "?Q \<subseteq> C i"
    using halfline_chart.chart_image[OF chart[OF i]]
      KLD by auto
  have from_cont:
    "continuous_on (C i) (from_chart i)"
    by (rule homeomorphism_cont2
      [OF halfline_chart.homeo[OF chart[OF i]]])
  have fromM: "from_chart i ` C i \<subseteq> M"
    using halfline_chart.inverse_image[OF chart[OF i]]
      domain_subset_carrier[OF i] by auto
  have phiC: "continuous_on (C i)
      (\<lambda>t. phi (from_chart i t))"
    by (rule continuous_on_compose2
      [OF phicont from_cont fromM])
  have fC: "continuous_on (C i) ?f"
    by (intro continuous_on_mult phiC Acont)
  have fQ: "continuous_on ?Q ?f"
    by (rule continuous_on_subset[OF fC QC])
  have zero: "?f t = 0"
    if tC: "t \<in> C i" and out: "t \<notin> ?Q"
    for t
  proof (rule ccontr)
    assume nz: "?f t \<noteq> 0"
    let ?p = "from_chart i t"
    have pD: "?p \<in> D i"
      using halfline_chart.inverse_image
        [OF chart[OF i]] tC by auto
    have pM: "?p \<in> M"
      using domain_subset_carrier[OF i] pD by auto
    have pK: "?p \<in> K"
      using Asupport[OF tC] nz by auto
    have pL: "?p \<in> L"
      using phisupport pM nz by auto
    have "to_chart i ?p = t"
      by (rule halfline_chart.from_to
        [OF chart[OF i] tC])
    moreover have "to_chart i ?p \<in> ?Q"
      using pK pL by blast
    ultimately show False
      using out by simp
  qed
  show ?thesis
    by (rule real_absolutely_integrable_compact_support
      [OF compactQ fQ QC zero])
qed

theorem one_form_chart_value_independent:
  fixes A :: "'i \<Rightarrow> real \<Rightarrow> real"
    and phi psi :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes finiteF: "finite F" and FI: "F \<subseteq> I"
    and finiteH: "finite H" and HI: "H \<subseteq> I"
    and compatible: "one_form_compatible A"
    and support: "\<And>i t. i \<in> I \<Longrightarrow> t \<in> C i \<Longrightarrow>
      from_chart i t \<notin> K \<Longrightarrow> A i t = 0"
    and unityF: "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i p) = 1"
    and unityH: "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>j\<in>H. psi j p) = 1"
    and outsideF: "\<And>i p. i \<in> F \<Longrightarrow> p \<in> M \<Longrightarrow>
      p \<notin> D i \<Longrightarrow> phi i p = 0"
    and outsideH: "\<And>j p. j \<in> H \<Longrightarrow> p \<in> M \<Longrightarrow>
      p \<notin> D j \<Longrightarrow> psi j p = 0"
    and crossF: "\<And>i j. i \<in> F \<Longrightarrow> j \<in> H \<Longrightarrow>
      (\<lambda>t. phi i (from_chart i t) *
        psi j (from_chart i t) * A i t)
        absolutely_integrable_on C i"
    and crossH: "\<And>i j. i \<in> F \<Longrightarrow> j \<in> H \<Longrightarrow>
      (\<lambda>t. psi j (from_chart j t) *
        phi i (from_chart j t) * A j t)
        absolutely_integrable_on C j"
    and overlapH: "\<And>i j. i \<in> F \<Longrightarrow> j \<in> H \<Longrightarrow>
      (\<lambda>t. psi j (from_chart j t) *
        phi i (from_chart j t) * A j t)
        absolutely_integrable_on overlap j i"
  shows "one_form_chart_value F phi A =
    one_form_chart_value H psi A"
proof -
  have refineF:
    "integral (C i)
      (\<lambda>t. phi i (from_chart i t) * A i t) =
    (\<Sum>j\<in>H. integral (overlap i j)
      (\<lambda>t. phi i (from_chart i t) *
        psi j (from_chart i t) * A i t))"
    if i: "i \<in> F" for i
    by (rule one_form_chart_refinement
      [OF _ finiteH HI unityH _ outsideH])
      (use i FI support crossF in auto)
  have refineH:
    "integral (C j)
      (\<lambda>t. psi j (from_chart j t) * A j t) =
    (\<Sum>i\<in>F. integral (overlap j i)
      (\<lambda>t. psi j (from_chart j t) *
        phi i (from_chart j t) * A j t))"
    if j: "j \<in> H" for j
    by (rule one_form_chart_refinement
      [OF _ finiteF FI unityF _ outsideF])
      (use j HI support crossH in auto)
  have cross:
    "eps i * integral (overlap i j)
       (\<lambda>t. phi i (from_chart i t) *
         psi j (from_chart i t) * A i t) =
     eps j * integral (overlap j i)
       (\<lambda>t. psi j (from_chart j t) *
         phi i (from_chart j t) * A j t)"
    if i: "i \<in> F" and j: "j \<in> H" for i j
    by (rule one_form_cross_change)
      (use i j FI HI compatible overlapH[OF i j]
        in auto)
  have "one_form_chart_value F phi A =
    (\<Sum>i\<in>F. \<Sum>j\<in>H.
      eps i * integral (overlap i j)
        (\<lambda>t. phi i (from_chart i t) *
          psi j (from_chart i t) * A i t))"
    unfolding one_form_chart_value_def
    by (rule sum.cong[OF refl])
      (use refineF in \<open>simp add: sum_distrib_left\<close>)
  also have "\<dots> =
    (\<Sum>j\<in>H. \<Sum>i\<in>F.
      eps i * integral (overlap i j)
        (\<lambda>t. phi i (from_chart i t) *
          psi j (from_chart i t) * A i t))"
    by (rule sum.swap)
  also have "\<dots> =
    (\<Sum>j\<in>H. \<Sum>i\<in>F.
      eps j * integral (overlap j i)
        (\<lambda>t. psi j (from_chart j t) *
          phi i (from_chart j t) * A j t))"
    by (rule sum.cong[OF refl],
        rule sum.cong[OF refl])
      (use cross in auto)
  also have "\<dots> =
    one_form_chart_value H psi A"
    unfolding one_form_chart_value_def
    by (rule sum.cong[OF refl])
      (use refineH in \<open>simp add: sum_distrib_left\<close>)
  finally show ?thesis .
qed

definition one_form_regular where
  "one_form_regular K A \<longleftrightarrow>
    one_form_compatible A \<and>
    (\<forall>i\<in>I. continuous_on (C i) (A i)) \<and>
    (\<forall>i\<in>I. \<forall>t\<in>C i.
      from_chart i t \<notin> K \<longrightarrow> A i t = 0)"

lemma exact_one_form_regular:
  assumes compact: "compact K"
    and support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and smooth: "chartwise_C1_scalar omega"
  shows "one_form_regular K (exact_one_form omega)"
  unfolding one_form_regular_def
  using exact_one_form_compatible[OF smooth]
    exact_one_form_continuous[OF smooth]
    exact_one_form_compact_support
      [OF compact support smooth]
  by auto

lemma exact_chart_data_product_derivative:
  assumes data: "exact_chart_data K omega F phi Q g"
    and smooth: "chartwise_C1_scalar omega"
    and phiC1: "\<And>i. i \<in> F \<Longrightarrow>
      chartwise_C1_scalar (phi i)"
    and iF: "i \<in> F" and t: "t \<in> C i"
  shows "g i t =
    phi i (from_chart i t) * exact_one_form omega i t +
      exact_one_form (phi i) i t *
        omega (from_chart i t)"
proof -
  have iI: "i \<in> I"
    using data iF by (auto simp: exact_chart_data_def)
  have old: "((\<lambda>s. phi i (from_chart i s) *
      omega (from_chart i s))
      has_vector_derivative g i t)
      (at t within {0..})"
    using data iF t
    by (auto simp: exact_chart_data_def)
  have prodC1: "chartwise_C1_scalar
      (\<lambda>p. phi i p * omega p)"
    by (rule chartwise_C1_scalar_mult
      [OF phiC1[OF iF] smooth])
  have new: "((\<lambda>s. phi i (from_chart i s) *
      omega (from_chart i s))
      has_vector_derivative
        exact_one_form
          (\<lambda>p. phi i p * omega p) i t)
      (at t within {0..})"
    by (rule chartwise_C1_exact_derivative
      [OF prodC1 iI t])
  have nontrivial: "at t within {0::real..} \<noteq> bot"
    by (rule halfline_at_within_nontrivial)
      (use t halfline_chart.codomain_subset_halfline
        [OF chart[OF iI]] in auto)
  have eq: "g i t =
    exact_one_form
      (\<lambda>p. phi i p * omega p) i t"
    by (rule vector_derivative_unique_within
      [OF nontrivial old new])
  show ?thesis
    by (simp add: eq exact_one_form_product
      [OF smooth phiC1[OF iF] iI t])
qed

lemma exact_chart_data_integrable:
  fixes omega :: "'a \<Rightarrow> real"
    and phi :: "'i \<Rightarrow> 'a \<Rightarrow> real"
    and g :: "'i \<Rightarrow> real \<Rightarrow> real"
  assumes data: "exact_chart_data K omega F phi Q g"
    and iF: "i \<in> F"
  shows "(g i) absolutely_integrable_on C i"
proof -
  have iI: "i \<in> I"
    using data iF by (auto simp: exact_chart_data_def)
  have compactQ: "compact (Q i)"
    and QC: "Q i \<subseteq> C i"
    and zeroF: "\<And>t. t \<in> C i \<Longrightarrow>
      t \<notin> Q i \<Longrightarrow>
      phi i (from_chart i t) *
        omega (from_chart i t) = 0"
    and deriv: "\<And>t. t \<in> C i \<Longrightarrow>
      ((\<lambda>s. phi i (from_chart i s) *
        omega (from_chart i s))
        has_vector_derivative g i t)
        (at t within {0..})"
    and cont: "continuous_on (C i) (g i)"
    using data iF
    by (auto simp: exact_chart_data_def)
  have gzero: "g i t = 0"
    if t: "t \<in> C i" "t \<notin> Q i" for t
    by (rule halfline_derivative_zero_outside_compact
      [where F="\<lambda>s. phi i (from_chart i s) *
        omega (from_chart i s)"
        and g="g i" and C="C i" and Q="Q i"
        and t=t])
      (use halfline_chart.open_C[OF chart[OF iI]]
        compactQ zeroF deriv t in auto)
  have contQ: "continuous_on (Q i) (g i)"
    by (rule continuous_on_subset[OF cont QC])
  show ?thesis
    by (rule real_absolutely_integrable_compact_support
      [OF compactQ contQ QC gzero])
qed

lemma exact_chart_data_lebesgue_eq_integral:
  fixes omega :: "'a \<Rightarrow> real"
    and phi :: "'i \<Rightarrow> 'a \<Rightarrow> real"
    and g :: "'i \<Rightarrow> real \<Rightarrow> real"
  assumes data: "exact_chart_data K omega F phi Q g"
    and iF: "i \<in> F"
  shows "(LINT t : C i | lborel. g i t) =
    integral (C i) (g i)"
proof (rule set_borel_integral_eq_integral(2))
  have iI: "i \<in> I"
    using data iF by (auto simp: exact_chart_data_def)
  have compactQ: "compact (Q i)"
    and QC: "Q i \<subseteq> C i"
    and cont: "continuous_on (C i) (g i)"
    using data iF by (auto simp: exact_chart_data_def)
  have zeroF: "\<And>t. t \<in> C i \<Longrightarrow>
    t \<notin> Q i \<Longrightarrow>
    phi i (from_chart i t) *
      omega (from_chart i t) = 0"
    and deriv: "\<And>t. t \<in> C i \<Longrightarrow>
      ((\<lambda>s. phi i (from_chart i s) *
        omega (from_chart i s))
        has_vector_derivative g i t)
        (at t within {0..})"
    using data iF by (auto simp: exact_chart_data_def)
  have zero: "g i t = 0"
    if t: "t \<in> C i" "t \<notin> Q i" for t
    by (rule halfline_derivative_zero_outside_compact
      [where F="\<lambda>s. phi i (from_chart i s) *
        omega (from_chart i s)"
        and g="g i" and C="C i" and Q="Q i"
        and t=t])
      (use halfline_chart.open_C[OF chart[OF iI]]
        compactQ zeroF deriv t in auto)
  show "set_integrable lborel (C i) (g i)"
    by (rule real_lborel_integrable_compact_support
      [OF compactQ _ QC zero])
      (rule continuous_on_subset[OF cont QC])
qed

definition scalar_derivative_form where
  "scalar_derivative_form omega phi i t =
    omega (from_chart i t) *
      exact_one_form phi i t"

lemma scalar_derivative_form_compatible:
  assumes smooth: "chartwise_C1_scalar phi"
  shows "one_form_compatible
    (scalar_derivative_form omega phi)"
  unfolding one_form_compatible_def
proof (intro ballI)
  fix i j t
  assume i: "i \<in> I" and j: "j \<in> I"
    and t: "t \<in> overlap i j"
  have deriv: "exact_one_form phi i t =
    eucl.det (transition_deriv i j t) *
      exact_one_form phi j (transition i j t)"
    using exact_one_form_compatible[OF smooth]
      i j t
    by (auto simp: one_form_compatible_def)
  have point: "from_chart j (transition i j t) =
    from_chart i t"
    by (rule transition_point[OF i j t])
  show "scalar_derivative_form omega phi i t =
    eucl.det (transition_deriv i j t) *
      scalar_derivative_form omega phi j
        (transition i j t)"
    by (simp add: scalar_derivative_form_def
      point deriv algebra_simps)
qed

lemma scalar_derivative_form_closed_support:
  assumes closed: "closed L"
    and phi_support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> L \<Longrightarrow> phi p = 0"
    and smooth: "chartwise_C1_scalar phi"
    and i: "i \<in> I" and t: "t \<in> C i"
    and out: "from_chart i t \<notin> L"
  shows "scalar_derivative_form omega phi i t = 0"
  unfolding scalar_derivative_form_def
  by (simp add: exact_one_form_closed_support
    [OF closed phi_support smooth i t out])

lemma scalar_derivative_form_weighted_integrable:
  assumes k: "k \<in> I" and m: "m \<in> I"
    and compact: "compact K"
    and omega_support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and omega_smooth: "chartwise_C1_scalar omega"
    and phi_smooth: "chartwise_C1_scalar phi"
    and closedL: "closed L"
    and phi_support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> L \<Longrightarrow> phi p = 0"
    and psi_cont: "continuous_on M psi"
    and closedR: "closed R"
    and psi_support:
      "{p\<in>M. psi p \<noteq> 0} \<subseteq> R"
    and domains: "L \<inter> R \<subseteq> D k \<inter> D m"
  shows
    "(\<lambda>t. psi (from_chart k t) *
      scalar_derivative_form omega phi k t)
      absolutely_integrable_on C k"
    "(\<lambda>t. psi (from_chart k t) *
      scalar_derivative_form omega phi k t)
      absolutely_integrable_on overlap k m"
proof -
  have Acont: "continuous_on (C k)
      (scalar_derivative_form omega phi k)"
    unfolding scalar_derivative_form_def
    by (intro continuous_on_mult
      chartwise_C1_pullback_continuous[OF omega_smooth k]
      exact_one_form_continuous[OF phi_smooth k])
  have AsupportK:
    "scalar_derivative_form omega phi k t = 0"
    if t: "t \<in> C k"
      and out: "from_chart k t \<notin> K" for t
  proof -
    have pM: "from_chart k t \<in> M"
      using halfline_chart.inverse_image[OF chart[OF k]]
        domain_subset_carrier[OF k] t by auto
    show ?thesis
      using omega_support[OF pM out]
      by (simp add: scalar_derivative_form_def)
  qed
  have AsupportL:
    "scalar_derivative_form omega phi k t = 0"
    if t: "t \<in> C k"
      and out: "from_chart k t \<notin> L" for t
    by (rule scalar_derivative_form_closed_support
      [OF closedL phi_support phi_smooth k t out])
  show "(\<lambda>t. psi (from_chart k t) *
      scalar_derivative_form omega phi k t)
      absolutely_integrable_on C k"
    by (rule one_form_weighted_integrable(1))
      (use k m compact Acont AsupportK
        AsupportL closedL psi_cont closedR
        psi_support domains in auto)
  show "(\<lambda>t. psi (from_chart k t) *
      scalar_derivative_form omega phi k t)
      absolutely_integrable_on overlap k m"
    by (rule one_form_weighted_integrable(2))
      (use k m compact Acont AsupportK
        AsupportL closedL psi_cont closedR
        psi_support domains in auto)
qed

definition one_form_partition ::
  "'a set \<Rightarrow> 'i set \<Rightarrow>
    ('i \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool" where
  "one_form_partition K F phi \<longleftrightarrow>
    finite F \<and> F \<subseteq> I \<and>
    (\<forall>p\<in>K. (\<Sum>i\<in>F. phi i p) = 1) \<and>
    (\<forall>i\<in>F. continuous_on M (phi i)) \<and>
    (\<forall>i\<in>F. \<exists>L. closed L \<and>
      {p\<in>M. phi i p \<noteq> 0} \<subseteq> L \<and>
      L \<subseteq> D i)"

theorem one_form_chart_value_independent_regular:
  assumes compact: "compact K"
    and regular: "one_form_regular K A"
    and first: "one_form_partition K F phi"
    and second: "one_form_partition K H psi"
  shows "one_form_chart_value F phi A =
    one_form_chart_value H psi A"
proof -
  have F: "finite F" "F \<subseteq> I"
    "\<forall>p\<in>K. (\<Sum>i\<in>F. phi i p) = 1"
    "\<forall>i\<in>F. continuous_on M (phi i)"
    "\<forall>i\<in>F. \<exists>L. closed L \<and>
      {p\<in>M. phi i p \<noteq> 0} \<subseteq> L \<and>
      L \<subseteq> D i"
    using first by (auto simp: one_form_partition_def)
  have H: "finite H" "H \<subseteq> I"
    "\<forall>p\<in>K. (\<Sum>j\<in>H. psi j p) = 1"
    "\<forall>j\<in>H. continuous_on M (psi j)"
    "\<forall>j\<in>H. \<exists>R. closed R \<and>
      {p\<in>M. psi j p \<noteq> 0} \<subseteq> R \<and>
      R \<subseteq> D j"
    using second by (auto simp: one_form_partition_def)
  have compatible: "one_form_compatible A"
    and cont: "\<forall>i\<in>I.
      continuous_on (C i) (A i)"
    and support: "\<forall>i\<in>I. \<forall>t\<in>C i.
      from_chart i t \<notin> K \<longrightarrow> A i t = 0"
    using regular by (auto simp: one_form_regular_def)
  have outsideF: "phi i p = 0"
    if "i \<in> F" "p \<in> M" "p \<notin> D i"
    for i p
    using F(5) that by auto
  have outsideH: "psi j p = 0"
    if "j \<in> H" "p \<in> M" "p \<notin> D j"
    for j p
    using H(5) that by auto
  have cross:
    "(\<lambda>t. phi i (from_chart i t) *
      psi j (from_chart i t) * A i t)
      absolutely_integrable_on C i"
    "(\<lambda>t. psi j (from_chart j t) *
      phi i (from_chart j t) * A j t)
      absolutely_integrable_on C j"
    "(\<lambda>t. psi j (from_chart j t) *
      phi i (from_chart j t) * A j t)
      absolutely_integrable_on overlap j i"
    if i: "i \<in> F" and j: "j \<in> H" for i j
  proof -
    have iI: "i \<in> I" and jI: "j \<in> I"
      using F(2) H(2) i j by auto
    obtain L where L: "closed L"
      "{p\<in>M. phi i p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> D i"
      using F(5) i by blast
    obtain R where R: "closed R"
      "{p\<in>M. psi j p \<noteq> 0} \<subseteq> R"
      "R \<subseteq> D j"
      using H(5) j by blast
    have Ai: "continuous_on (C i) (A i)"
      using cont iI by auto
    have Aj: "continuous_on (C j) (A j)"
      using cont jI by auto
    have Si: "\<And>t. t \<in> C i \<Longrightarrow>
      from_chart i t \<notin> K \<Longrightarrow> A i t = 0"
      using support iI by auto
    have Sj: "\<And>t. t \<in> C j \<Longrightarrow>
      from_chart j t \<notin> K \<Longrightarrow> A j t = 0"
      using support jI by auto
    have phiC: "continuous_on M (phi i)"
      using F(4) i by auto
    have psiC: "continuous_on M (psi j)"
      using H(4) j by auto
    show "(\<lambda>t. phi i (from_chart i t) *
      psi j (from_chart i t) * A i t)
      absolutely_integrable_on C i"
      by (rule one_form_cross_integrable(1))
        (use iI jI compact Ai Si phiC psiC
          L R in auto)
    have pairC:
      "(\<lambda>t. psi j (from_chart j t) *
        phi i (from_chart j t) * A j t)
        absolutely_integrable_on C j"
      by (rule one_form_cross_integrable(1))
        (use jI iI compact Aj Sj psiC phiC
          R L in auto)
    have pairO:
      "(\<lambda>t. psi j (from_chart j t) *
        phi i (from_chart j t) * A j t)
        absolutely_integrable_on overlap j i"
      by (rule one_form_cross_integrable(2))
        (use jI iI compact Aj Sj psiC phiC
          R L in auto)
    show
      "(\<lambda>t. psi j (from_chart j t) *
        phi i (from_chart j t) * A j t)
        absolutely_integrable_on C j"
      "(\<lambda>t. psi j (from_chart j t) *
        phi i (from_chart j t) * A j t)
        absolutely_integrable_on overlap j i"
      using pairC pairO by auto
  qed
  show ?thesis
  proof (rule one_form_chart_value_independent
      [OF F(1) F(2) H(1) H(2) compatible])
    show "\<And>i t. i \<in> I \<Longrightarrow> t \<in> C i \<Longrightarrow>
      from_chart i t \<notin> K \<Longrightarrow> A i t = 0"
      using support by auto
    show "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i p) = 1"
      using F(3) by auto
    show "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>j\<in>H. psi j p) = 1"
      using H(3) by auto
    show "\<And>i p. i \<in> F \<Longrightarrow> p \<in> M \<Longrightarrow>
      p \<notin> D i \<Longrightarrow> phi i p = 0"
      by (rule outsideF)
    show "\<And>j p. j \<in> H \<Longrightarrow> p \<in> M \<Longrightarrow>
      p \<notin> D j \<Longrightarrow> psi j p = 0"
      by (rule outsideH)
    show "\<And>i j. i \<in> F \<Longrightarrow> j \<in> H \<Longrightarrow>
      (\<lambda>t. phi i (from_chart i t) *
        psi j (from_chart i t) * A i t)
        absolutely_integrable_on C i"
      by (rule cross(1))
    show "\<And>i j. i \<in> F \<Longrightarrow> j \<in> H \<Longrightarrow>
      (\<lambda>t. psi j (from_chart j t) *
        phi i (from_chart j t) * A j t)
        absolutely_integrable_on C j"
      by (rule cross(2))
    show "\<And>i j. i \<in> F \<Longrightarrow> j \<in> H \<Longrightarrow>
      (\<lambda>t. psi j (from_chart j t) *
        phi i (from_chart j t) * A j t)
        absolutely_integrable_on overlap j i"
      by (rule cross(3))
  qed
qed

definition one_form_body_integral ::
  "'a set \<Rightarrow> ('i \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real" where
  "one_form_body_integral K A =
    (SOME v. \<exists>F phi.
      one_form_partition K F phi \<and>
      v = one_form_chart_value F phi A)"

lemma one_form_body_integral_chart_value:
  assumes compact: "compact K"
    and regular: "one_form_regular K A"
    and part: "one_form_partition K F phi"
  shows "one_form_body_integral K A =
    one_form_chart_value F phi A"
proof -
  let ?P = "\<lambda>v. \<exists>H psi.
    one_form_partition K H psi \<and>
    v = one_form_chart_value H psi A"
  have witness: "?P (one_form_chart_value F phi A)"
    using part by blast
  have chosen: "?P (one_form_body_integral K A)"
    unfolding one_form_body_integral_def
    by (rule someI[where x="one_form_chart_value F phi A"])
      (rule witness)
  then obtain H psi where H:
    "one_form_partition K H psi"
    "one_form_body_integral K A =
      one_form_chart_value H psi A"
    by blast
  show ?thesis
    using H(2)
      one_form_chart_value_independent_regular
        [OF compact regular H(1) part]
    by simp
qed

theorem one_form_local_cancellation:
  fixes B :: "'i \<Rightarrow> 'i \<Rightarrow> real \<Rightarrow> real"
    and psi :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes finiteF: "finite F" and FI: "F \<subseteq> I"
    and finiteH: "finite H" and HI: "H \<subseteq> I"
    and unity: "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>j\<in>H. psi j p) = 1"
    and outsideH: "\<And>j p. j \<in> H \<Longrightarrow>
      p \<in> M \<Longrightarrow> p \<notin> D j
      \<Longrightarrow> psi j p = 0"
    and compatible: "\<And>i. i \<in> F \<Longrightarrow>
      one_form_compatible (B i)"
    and support: "\<And>i k t. i \<in> F \<Longrightarrow>
      k \<in> I \<Longrightarrow> t \<in> C k \<Longrightarrow>
      from_chart k t \<notin> K \<Longrightarrow> B i k t = 0"
    and local_zero: "\<And>i j t. i \<in> F \<Longrightarrow>
      j \<in> H \<Longrightarrow> t \<in> C j \<Longrightarrow>
      t \<notin> overlap j i \<Longrightarrow> B i j t = 0"
    and sum_zero: "\<And>j t. j \<in> H \<Longrightarrow>
      t \<in> C j \<Longrightarrow>
      (\<Sum>i\<in>F. B i j t) = 0"
    and intF: "\<And>i j. i \<in> F \<Longrightarrow> j \<in> H \<Longrightarrow>
      (\<lambda>t. psi j (from_chart i t) * B i i t)
      absolutely_integrable_on C i"
    and intH: "\<And>i j. i \<in> F \<Longrightarrow> j \<in> H \<Longrightarrow>
      (\<lambda>t. psi j (from_chart j t) * B i j t)
      absolutely_integrable_on C j"
    and intO: "\<And>i j. i \<in> F \<Longrightarrow> j \<in> H \<Longrightarrow>
      (\<lambda>t. psi j (from_chart j t) * B i j t)
      absolutely_integrable_on overlap j i"
  shows "(\<Sum>i\<in>F.
    eps i * integral (C i) (B i i)) = 0"
proof -
  have refine:
    "integral (C i) (B i i) =
      (\<Sum>j\<in>H.
        integral (overlap i j)
          (\<lambda>t. psi j (from_chart i t) * B i i t))"
    if i: "i \<in> F" for i
  proof -
    have iI: "i \<in> I"
      using FI i by auto
    have base:
      "integral (C i)
        (\<lambda>t. 1 * B i i t) =
      (\<Sum>j\<in>H. integral (overlap i j)
        (\<lambda>t. 1 * psi j (from_chart i t) *
          B i i t))"
    proof (rule one_form_chart_refinement
        [OF iI finiteH HI unity])
      show "\<And>t. t \<in> C i \<Longrightarrow>
        from_chart i t \<notin> K \<Longrightarrow>
        B i i t = 0"
        by (rule support[OF i iI])
      show "\<And>j p. j \<in> H \<Longrightarrow>
        p \<in> M \<Longrightarrow> p \<notin> D j
        \<Longrightarrow> psi j p = 0"
        by (rule outsideH)
      show "\<And>j. j \<in> H \<Longrightarrow>
        (\<lambda>t. 1 * psi j (from_chart i t) *
          B i i t) absolutely_integrable_on C i"
        using intF[OF i] by simp
    qed
    show ?thesis
      using base by simp
  qed
  have change:
    "eps i *
      integral (overlap i j)
        (\<lambda>t. psi j (from_chart i t) *
          B i i t) =
     eps j *
      integral (overlap j i)
        (\<lambda>t. psi j (from_chart j t) *
          B i j t)"
    if i: "i \<in> F" and j: "j \<in> H" for i j
  proof -
    have iI: "i \<in> I" and jI: "j \<in> I"
      using FI HI i j by auto
    have base:
      "eps i * integral (overlap i j)
        (\<lambda>t. 1 * psi j (from_chart i t) *
          B i i t) =
       eps j * integral (overlap j i)
        (\<lambda>t. psi j (from_chart j t) *
          1 * B i j t)"
      by (rule one_form_cross_change)
        (use iI jI compatible[OF i] intO[OF i j]
          in auto)
    show ?thesis
      using base by simp
  qed
  have restrict:
    "integral (overlap j i)
      (\<lambda>t. psi j (from_chart j t) * B i j t) =
     integral (C j)
      (\<lambda>t. psi j (from_chart j t) * B i j t)"
    if i: "i \<in> F" and j: "j \<in> H" for i j
  proof -
    let ?f = "\<lambda>t. psi j (from_chart j t) * B i j t"
    have jI: "j \<in> I"
      using HI j by auto
    have eq: "?f t = 0"
      if t: "t \<in> C j" "t \<notin> overlap j i"
      for t
      using local_zero[OF i j t] by simp
    have "integral (C j) ?f =
      integral (C j)
        (\<lambda>t. if t \<in> overlap j i
          then ?f t else 0)"
      by (rule integral_cong) (use eq in auto)
    also have "\<dots> =
      integral (overlap j i \<inter> C j) ?f"
      by (rule integral_restrict_Int)
    also have "\<dots> =
      integral (overlap j i) ?f"
      using overlap_subset_codomain[OF jI]
      by (simp add: Int_absorb2)
    finally show ?thesis by simp
  qed
  have inner_zero:
    "(\<Sum>i\<in>F. integral (C j)
      (\<lambda>t. psi j (from_chart j t) * B i j t)) =
      0"
    if j: "j \<in> H" for j
  proof -
    have int: "(\<lambda>t.
      psi j (from_chart j t) * B i j t)
      integrable_on C j" if i: "i \<in> F" for i
      using intH[OF i j]
      by (simp add: absolutely_integrable_on_def)
    have "(\<Sum>i\<in>F. integral (C j)
      (\<lambda>t. psi j (from_chart j t) * B i j t)) =
      integral (C j)
        (\<lambda>t. \<Sum>i\<in>F.
          psi j (from_chart j t) * B i j t)"
      by (rule integral_sum[OF finiteF int, symmetric])
    also have "\<dots> = 0"
    proof -
      have eq: "(\<Sum>i\<in>F.
        psi j (from_chart j t) * B i j t) = 0"
        if t: "t \<in> C j" for t
        using sum_zero[OF j t]
        by (simp add: sum_distrib_left[symmetric])
      have "integral (C j)
        (\<lambda>t. \<Sum>i\<in>F.
          psi j (from_chart j t) * B i j t) =
        integral (C j) (\<lambda>_. 0::real)"
        by (rule integral_cong) (use eq in auto)
      then show ?thesis by simp
    qed
    finally show ?thesis .
  qed
  have "(\<Sum>i\<in>F.
    eps i * integral (C i) (B i i)) =
    (\<Sum>i\<in>F. \<Sum>j\<in>H.
      eps i * integral (overlap i j)
        (\<lambda>t. psi j (from_chart i t) *
          B i i t))"
    by (rule sum.cong[OF refl])
      (use refine in \<open>simp add: sum_distrib_left\<close>)
  also have "\<dots> =
    (\<Sum>j\<in>H. \<Sum>i\<in>F.
      eps i * integral (overlap i j)
        (\<lambda>t. psi j (from_chart i t) *
          B i i t))"
    by (rule sum.swap)
  also have "\<dots> =
    (\<Sum>j\<in>H. \<Sum>i\<in>F.
      eps j * integral (C j)
        (\<lambda>t. psi j (from_chart j t) *
          B i j t))"
    by (rule sum.cong[OF refl],
        rule sum.cong[OF refl])
      (use change restrict in auto)
  also have "\<dots> = 0"
    using inner_zero
    by (simp add: sum_distrib_left[symmetric])
  finally show ?thesis .
qed

theorem scalar_derivative_form_partition_cancel:
  assumes compact: "compact K"
    and omega_support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and omega_smooth: "chartwise_C1_scalar omega"
    and first: "one_form_partition K F phi"
    and phi_smooth: "\<And>i. i \<in> F \<Longrightarrow>
      chartwise_C1_scalar (phi i)"
    and second: "one_form_partition K H psi"
  shows "(\<Sum>i\<in>F. eps i *
    integral (C i)
      (scalar_derivative_form omega (phi i) i)) = 0"
proof -
  have F: "finite F" "F \<subseteq> I"
    "\<forall>p\<in>K. (\<Sum>i\<in>F. phi i p) = 1"
    "\<forall>i\<in>F. \<exists>L. closed L \<and>
      {p\<in>M. phi i p \<noteq> 0} \<subseteq> L \<and>
      L \<subseteq> D i"
    using first by (auto simp: one_form_partition_def)
  have H: "finite H" "H \<subseteq> I"
    "\<forall>p\<in>K. (\<Sum>j\<in>H. psi j p) = 1"
    "\<forall>j\<in>H. continuous_on M (psi j)"
    "\<forall>j\<in>H. \<exists>R. closed R \<and>
      {p\<in>M. psi j p \<noteq> 0} \<subseteq> R \<and>
      R \<subseteq> D j"
    using second by (auto simp: one_form_partition_def)
  have outsideH: "psi j p = 0"
    if "j \<in> H" "p \<in> M" "p \<notin> D j"
    for j p
    using H(5) that by auto
  have local_zero:
    "scalar_derivative_form omega (phi i) j t = 0"
    if i: "i \<in> F" and j: "j \<in> H"
      and t: "t \<in> C j"
      and out: "t \<notin> overlap j i"
    for i j t
  proof -
    have jI: "j \<in> I"
      using H(2) j by auto
    obtain L where L: "closed L"
      "{p\<in>M. phi i p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> D i"
      using F(4) i by blast
    have pM: "from_chart j t \<in> M"
      using halfline_chart.inverse_image[OF chart[OF jI]]
        domain_subset_carrier[OF jI] t by auto
    have pnotDi: "from_chart j t \<notin> D i"
      using out t overlap_preimage[OF jI] by auto
    have pnotL: "from_chart j t \<notin> L"
      using pnotDi L(3) by auto
    have phi_zero: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> L \<Longrightarrow> phi i p = 0"
      using L(2) by auto
    show ?thesis
      by (rule scalar_derivative_form_closed_support
        [OF L(1) phi_zero phi_smooth[OF i]
          jI t pnotL])
  qed
  have weighted:
    "(\<lambda>t. psi j (from_chart i t) *
      scalar_derivative_form omega (phi i) i t)
      absolutely_integrable_on C i"
    "(\<lambda>t. psi j (from_chart j t) *
      scalar_derivative_form omega (phi i) j t)
      absolutely_integrable_on C j"
    "(\<lambda>t. psi j (from_chart j t) *
      scalar_derivative_form omega (phi i) j t)
      absolutely_integrable_on overlap j i"
    if i: "i \<in> F" and j: "j \<in> H" for i j
  proof -
    have iI: "i \<in> I" and jI: "j \<in> I"
      using F(2) H(2) i j by auto
    obtain L where L: "closed L"
      "{p\<in>M. phi i p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> D i"
      using F(4) i by blast
    obtain R where R: "closed R"
      "{p\<in>M. psi j p \<noteq> 0} \<subseteq> R"
      "R \<subseteq> D j"
      using H(5) j by blast
    have phi_zero: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> L \<Longrightarrow> phi i p = 0"
      using L(2) by auto
    have psi_cont: "continuous_on M (psi j)"
      using H(4) j by auto
    have domains_ij:
      "L \<inter> R \<subseteq> D i \<inter> D j"
      using L(3) R(3) by auto
    have domains_ji:
      "L \<inter> R \<subseteq> D j \<inter> D i"
      using L(3) R(3) by auto
    show "(\<lambda>t. psi j (from_chart i t) *
      scalar_derivative_form omega (phi i) i t)
      absolutely_integrable_on C i"
      by (rule scalar_derivative_form_weighted_integrable(1))
        (use iI jI compact omega_support
          omega_smooth phi_smooth[OF i]
          L(1) phi_zero psi_cont R(1) R(2)
          domains_ij in auto)
    show "(\<lambda>t. psi j (from_chart j t) *
      scalar_derivative_form omega (phi i) j t)
      absolutely_integrable_on C j"
      by (rule scalar_derivative_form_weighted_integrable(1))
        (use jI iI compact omega_support
          omega_smooth phi_smooth[OF i]
          L(1) phi_zero psi_cont R(1) R(2)
          domains_ji in auto)
    show "(\<lambda>t. psi j (from_chart j t) *
      scalar_derivative_form omega (phi i) j t)
      absolutely_integrable_on overlap j i"
      by (rule scalar_derivative_form_weighted_integrable(2))
        (use jI iI compact omega_support
          omega_smooth phi_smooth[OF i]
          L(1) phi_zero psi_cont R(1) R(2)
          domains_ji in auto)
  qed
  show ?thesis
  proof (rule one_form_local_cancellation
      [OF F(1) F(2) H(1) H(2),
        where B="\<lambda>i k t.
          scalar_derivative_form omega (phi i) k t"
        and K=K and psi=psi])
    show "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>j\<in>H. psi j p) = 1"
      using H(3) by auto
    show "\<And>j p. j \<in> H \<Longrightarrow>
      p \<in> M \<Longrightarrow> p \<notin> D j
      \<Longrightarrow> psi j p = 0"
      by (rule outsideH)
    show "\<And>i. i \<in> F \<Longrightarrow>
      one_form_compatible
        (scalar_derivative_form omega (phi i))"
      using phi_smooth
      by (auto intro: scalar_derivative_form_compatible)
    show "\<And>i k t. i \<in> F \<Longrightarrow>
      k \<in> I \<Longrightarrow> t \<in> C k \<Longrightarrow>
      from_chart k t \<notin> K \<Longrightarrow>
      scalar_derivative_form omega (phi i) k t = 0"
    proof -
      fix i k t
      assume "i \<in> F" and k: "k \<in> I"
        and t: "t \<in> C k"
        and out: "from_chart k t \<notin> K"
      have pM: "from_chart k t \<in> M"
        using halfline_chart.inverse_image
          [OF chart[OF k]]
          domain_subset_carrier[OF k] t by auto
      show "scalar_derivative_form omega (phi i) k t = 0"
        using omega_support[OF pM out]
        by (simp add: scalar_derivative_form_def)
    qed
    show "\<And>i j t. i \<in> F \<Longrightarrow>
      j \<in> H \<Longrightarrow> t \<in> C j \<Longrightarrow>
      t \<notin> overlap j i \<Longrightarrow>
      scalar_derivative_form omega (phi i) j t = 0"
      by (rule local_zero)
    show "\<And>j t. j \<in> H \<Longrightarrow>
      t \<in> C j \<Longrightarrow>
      (\<Sum>i\<in>F.
        scalar_derivative_form omega (phi i) j t) = 0"
    proof -
      fix j t
      assume j: "j \<in> H" and t: "t \<in> C j"
      have jI: "j \<in> I"
        using H(2) j by auto
      have zero: "omega (from_chart j t) *
        (\<Sum>i\<in>F.
          exact_one_form (phi i) j t) = 0"
        by (rule exact_partition_derivative_cancel
          [OF F(1) _ omega_support omega_smooth
            phi_smooth jI t])
          (use F(3) in auto)
      show "(\<Sum>i\<in>F.
        scalar_derivative_form omega (phi i) j t) = 0"
        using zero
        by (simp add: scalar_derivative_form_def
          sum_distrib_left[symmetric])
    qed
    show "\<And>i j. i \<in> F \<Longrightarrow> j \<in> H \<Longrightarrow>
      (\<lambda>t. psi j (from_chart i t) *
        scalar_derivative_form omega (phi i) i t)
        absolutely_integrable_on C i"
      by (rule weighted(1))
    show "\<And>i j. i \<in> F \<Longrightarrow> j \<in> H \<Longrightarrow>
      (\<lambda>t. psi j (from_chart j t) *
        scalar_derivative_form omega (phi i) j t)
        absolutely_integrable_on C j"
      by (rule weighted(2))
    show "\<And>i j. i \<in> F \<Longrightarrow> j \<in> H \<Longrightarrow>
      (\<lambda>t. psi j (from_chart j t) *
        scalar_derivative_form omega (phi i) j t)
        absolutely_integrable_on overlap j i"
      by (rule weighted(3))
  qed
qed

theorem exact_chart_data_one_form_bridge:
  fixes omega :: "'a \<Rightarrow> real"
    and phi :: "'i \<Rightarrow> 'a \<Rightarrow> real"
    and g :: "'i \<Rightarrow> real \<Rightarrow> real"
  assumes compact: "compact K"
    and support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and smooth: "chartwise_C1_scalar omega"
    and data: "exact_chart_data K omega F phi Q g"
    and part: "one_form_partition K F phi"
    and phi_smooth: "\<And>i. i \<in> F \<Longrightarrow>
      chartwise_C1_scalar (phi i)"
  shows "exact_chart_value F g =
    one_form_chart_value F phi (exact_one_form omega)"
proof -
  have finiteF: "finite F" and FI: "F \<subseteq> I"
    and phi_cont: "\<And>i. i \<in> F \<Longrightarrow>
      continuous_on M (phi i)"
    and support_phi:
      "\<And>i. i \<in> F \<Longrightarrow>
        \<exists>L. closed L \<and>
          {p\<in>M. phi i p \<noteq> 0} \<subseteq> L \<and>
          L \<subseteq> D i"
    using part by (auto simp: one_form_partition_def)
  have g_integral:
    "integral (C i) (g i) =
      integral (C i)
        (\<lambda>t. phi i (from_chart i t) *
          exact_one_form omega i t) +
      integral (C i)
        (scalar_derivative_form omega (phi i) i)"
    if iF: "i \<in> F" for i
  proof -
    have iI: "i \<in> I"
      using FI iF by auto
    obtain L where L: "closed L"
      "{p\<in>M. phi i p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> D i"
      using support_phi[OF iF] by blast
    have intG: "(g i) integrable_on C i"
      using exact_chart_data_integrable[OF data iF]
      by (simp add: absolutely_integrable_on_def)
    have intA:
      "(\<lambda>t. phi i (from_chart i t) *
        exact_one_form omega i t)
        integrable_on C i"
    proof -
      have Acont:
        "continuous_on (C i) (exact_one_form omega i)"
        by (rule exact_one_form_continuous[OF smooth iI])
      have Asupport: "\<And>t. t \<in> C i \<Longrightarrow>
        from_chart i t \<notin> K \<Longrightarrow>
        exact_one_form omega i t = 0"
        by (rule exact_one_form_compact_support
          [OF compact support smooth iI])
      have abs:
        "(\<lambda>t. phi i (from_chart i t) *
          exact_one_form omega i t)
          absolutely_integrable_on C i"
        by (rule one_form_localized_integrable)
          (use iI compact Acont Asupport
            phi_cont[OF iF] L in auto)
      show ?thesis
        using abs by (simp add: absolutely_integrable_on_def)
    qed
    let ?a = "\<lambda>t. phi i (from_chart i t) *
      exact_one_form omega i t"
    let ?b = "scalar_derivative_form omega (phi i) i"
    have eq: "g i t = ?a t + ?b t"
      if t: "t \<in> C i" for t
      using exact_chart_data_product_derivative
        [OF data smooth phi_smooth iF t]
      by (simp add: scalar_derivative_form_def
        algebra_simps)
    have intB: "?b integrable_on C i"
    proof -
      have diff: "(\<lambda>t. g i t - ?a t)
        integrable_on C i"
        by (rule integrable_diff[OF intG intA])
      show ?thesis
        by (rule integrable_eq[OF diff])
          (use eq in auto)
    qed
    have "integral (C i) (g i) =
      integral (C i) (\<lambda>t. ?a t + ?b t)"
      by (rule integral_cong) (use eq in auto)
    also have "\<dots> =
      integral (C i) ?a + integral (C i) ?b"
      by (rule integral_add[OF intA intB])
    finally show ?thesis .
  qed
  have cancel:
    "(\<Sum>i\<in>F. eps i *
      integral (C i)
        (scalar_derivative_form omega (phi i) i)) = 0"
    by (rule scalar_derivative_form_partition_cancel
      [OF compact support smooth part phi_smooth part])
  have "exact_chart_value F g =
    (\<Sum>i\<in>F. eps i * integral (C i) (g i))"
    unfolding exact_chart_value_def
    by (rule sum.cong[OF refl])
      (use exact_chart_data_lebesgue_eq_integral
        [OF data] in auto)
  also have "\<dots> =
    one_form_chart_value F phi (exact_one_form omega) +
    (\<Sum>i\<in>F. eps i *
      integral (C i)
        (scalar_derivative_form omega (phi i) i))"
    using g_integral
    by (simp add: one_form_chart_value_def
      sum.distrib algebra_simps)
  also have "\<dots> =
    one_form_chart_value F phi (exact_one_form omega)"
    by (simp add: cancel)
  finally show ?thesis .
qed

theorem one_form_body_integral_stokes:
  fixes omega :: "'a \<Rightarrow> real"
  assumes compact: "compact K"
    and KM: "K \<subseteq> M"
    and support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and smooth: "chartwise_C1_scalar omega"
  shows "one_form_body_integral K (exact_one_form omega) =
    finite_boundary_zero_integral
      (K \<inter> boundary_carrier)
      (\<lambda>p. boundary_orientation p * omega p)"
proof (rule compact_support_one_dimensional_stokes
    [OF compact KM support smooth])
  fix F phi Q g
  assume F: "finite F" "F \<subseteq> I"
    "K \<subseteq> (\<Union>i\<in>F. D i)"
    and unity: "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i p) = 1"
    and phi_C1: "\<And>i. i \<in> F \<Longrightarrow>
      chartwise_C1_scalar (phi i)"
    and phi_cont: "\<And>i. i \<in> F \<Longrightarrow>
      continuous_on M (phi i)"
    and phi_support: "\<And>i. i \<in> F \<Longrightarrow>
      \<exists>L. closed L \<and>
        {p\<in>M. phi i p \<noteq> 0} \<subseteq> L \<and>
        L \<subseteq> D i"
    and compactQ: "\<And>i. i \<in> F \<Longrightarrow>
      compact (Q i)"
    and QC: "\<And>i. i \<in> F \<Longrightarrow>
      Q i \<subseteq> C i"
    and zero: "\<And>i t. i \<in> F \<Longrightarrow>
      t \<in> C i \<Longrightarrow> t \<notin> Q i
      \<Longrightarrow> phi i (from_chart i t) *
        omega (from_chart i t) = 0"
    and deriv: "\<And>i t. i \<in> F \<Longrightarrow>
      t \<in> C i \<Longrightarrow>
      ((\<lambda>s. phi i (from_chart i s) *
        omega (from_chart i s))
        has_vector_derivative g i t)
        (at t within {0..})"
    and cont: "\<And>i. i \<in> F \<Longrightarrow>
      continuous_on (C i) (g i)"
    and stokes: "(\<Sum>i\<in>F.
      eps i * (LINT t : C i | lborel. g i t)) =
      finite_boundary_zero_integral
        (K \<inter> boundary_carrier)
        (\<lambda>p. boundary_orientation p * omega p)"
  have outside: "phi i p = 0"
    if iF: "i \<in> F" and pM: "p \<in> M"
      and out: "p \<notin> D i" for i p
    using phi_support[OF iF] pM out
    by auto
  have data: "exact_chart_data K omega F phi Q g"
    using F unity outside compactQ QC zero
      deriv cont
    by (auto simp: exact_chart_data_def)
  have part: "one_form_partition K F phi"
    using F unity phi_cont phi_support
    by (auto simp: one_form_partition_def)
  have regular: "one_form_regular K
    (exact_one_form omega)"
    by (rule exact_one_form_regular
      [OF compact support smooth])
  have bridge: "exact_chart_value F g =
    one_form_chart_value F phi (exact_one_form omega)"
    by (rule exact_chart_data_one_form_bridge
      [OF compact support smooth data part phi_C1])
  have chosen: "one_form_body_integral K
      (exact_one_form omega) =
    one_form_chart_value F phi (exact_one_form omega)"
    by (rule one_form_body_integral_chart_value
      [OF compact regular part])
  have exact: "exact_chart_value F g =
    finite_boundary_zero_integral
      (K \<inter> boundary_carrier)
      (\<lambda>p. boundary_orientation p * omega p)"
    using stokes
    by (simp add: exact_chart_value_def)
  show "one_form_body_integral K
      (exact_one_form omega) =
    finite_boundary_zero_integral
      (K \<inter> boundary_carrier)
      (\<lambda>p. boundary_orientation p * omega p)"
    using chosen bridge exact by simp
qed

corollary one_form_body_integral_eq_exact_body_integral:
  fixes omega :: "'a \<Rightarrow> real"
  assumes compact: "compact K"
    and KM: "K \<subseteq> M"
    and support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and smooth: "chartwise_C1_scalar omega"
  shows "one_form_body_integral K (exact_one_form omega) =
    exact_body_integral K omega"
  using one_form_body_integral_stokes
      [OF compact KM support smooth]
    exact_body_integral_stokes
      [OF compact KM support smooth]
  by simp


end

end
