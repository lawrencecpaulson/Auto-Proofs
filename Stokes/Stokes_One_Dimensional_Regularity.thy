theory Stokes_One_Dimensional_Regularity
  imports Stokes_One_Dimensional_Partition
begin

lemma halfline_has_vector_derivative_of_local_C1:
  fixes H F :: "real \<Rightarrow> real"
  assumes openC: "openin (top_of_set {0::real..}) C"
    and tC: "t \<in> C"
    and smooth: "Ck_on 1 F U"
    and tU: "t \<in> U"
    and agree: "\<And>s. s \<in> U \<inter> C \<Longrightarrow>
      H s = F s"
  shows "(H has_vector_derivative
      vector_derivative F (at t))
      (at t within {0..})"
proof -
  obtain W where W: "open W"
    "C = {0::real..} \<inter> W"
    using openC by (auto simp: openin_open)
  have tH: "t \<in> {0::real..}"
    and tW: "t \<in> W"
    using tC W by auto
  have openU: "open U"
    by (rule Ck_on_open[OF smooth])
  have diffF: "F differentiable (at t)"
    using Ck_onD[OF smooth tU]
    by (simp add: Ck_at.simps)
  have derF: "(F has_vector_derivative
      vector_derivative F (at t)) (at t within {0..})"
    by (rule has_vector_derivative_at_within)
       (use diffF in \<open>simp add: vector_derivative_works\<close>)
  have openV: "open (U \<inter> W)"
    using openU W(1) by auto
  have tV: "t \<in> U \<inter> W"
    using tU tW by auto
  obtain d :: real where d: "0 < d"
    "ball t d \<subseteq> U \<inter> W"
    using open_contains_ball[THEN iffD1, OF openV]
      tV by blast
  show ?thesis
  proof (rule has_vector_derivative_transform_within
      [OF derF d(1) tH])
    fix s
    assume sH: "s \<in> {0..}"
      and near: "dist s t < d"
    have "s \<in> U \<inter> C"
      using d(2) sH near W(2)
      by (auto simp: dist_commute)
    then show "F s = H s"
      by (simp add: agree)
  qed
qed

lemma halfline_at_within_nontrivial:
  assumes "0 \<le> t"
  shows "at t within {0::real..} \<noteq> bot"
proof -
  have limpt: "t islimpt {t..t+1}"
    by (simp add: islimpt_Icc)
  have "{t..t+1} \<subseteq> {0::real..}"
    using assms by auto
  then have "t islimpt {0::real..}"
    by (rule islimpt_subset[OF limpt])
  then show ?thesis
    by (simp add: trivial_limit_within)
qed

lemma halfline_vector_derivative_of_local_C1:
  fixes H F :: "real \<Rightarrow> real"
  assumes openC: "openin (top_of_set {0::real..}) C"
    and tC: "t \<in> C"
    and smooth: "Ck_on 1 F U"
    and tU: "t \<in> U"
    and agree: "\<And>s. s \<in> U \<inter> C \<Longrightarrow>
      H s = F s"
  shows "vector_derivative H (at t within {0..}) =
    vector_derivative F (at t)"
proof -
  have "0 \<le> t"
    using tC openC by (auto simp: openin_open)
  then have nontrivial: "at t within {0::real..} \<noteq> bot"
    by (rule halfline_at_within_nontrivial)
  show ?thesis
    by (rule vector_derivative_within[OF nontrivial])
       (rule halfline_has_vector_derivative_of_local_C1
         [OF openC tC smooth tU agree])
qed

theorem halfline_C1_derivative_data:
  fixes H :: "real \<Rightarrow> real"
  assumes openC: "openin (top_of_set {0::real..}) C"
    and local: "\<And>t. t \<in> C \<Longrightarrow>
      \<exists>U F. Ck_on 1 F U \<and> t \<in> U \<and>
        (\<forall>s\<in>U \<inter> C. H s = F s)"
  shows "\<exists>g. (\<forall>t\<in>C.
      (H has_vector_derivative g t)
        (at t within {0..})) \<and>
    continuous_on C g"
proof -
  let ?g = "\<lambda>t. vector_derivative H (at t within {0..})"
  have der: "(H has_vector_derivative ?g t)
      (at t within {0..})" if tC: "t \<in> C" for t
  proof -
    obtain U F where UF: "Ck_on 1 F U" "t \<in> U"
      "\<forall>s\<in>U \<inter> C. H s = F s"
      using local[OF tC] by blast
    have d: "(H has_vector_derivative
        vector_derivative F (at t))
        (at t within {0..})"
      by (rule halfline_has_vector_derivative_of_local_C1
        [OF openC tC UF(1,2)])
         (use UF(3) in auto)
    have eq: "?g t = vector_derivative F (at t)"
      by (rule halfline_vector_derivative_of_local_C1
        [OF openC tC UF(1,2)])
         (use UF(3) in auto)
    show ?thesis using d eq by simp
  qed
  have cont: "continuous_on C ?g"
  proof (simp add: continuous_on_eq_continuous_within,
      intro ballI)
    fix t assume tC: "t \<in> C"
    obtain U F where UF: "Ck_on 1 F U" "t \<in> U"
      "\<forall>s\<in>U \<inter> C. H s = F s"
      using local[OF tC] by blast
    have openU: "open U"
      by (rule Ck_on_open[OF UF(1)])
    have C1_iff:
      "Ck_on 1 F U \<longleftrightarrow>
        F C1_differentiable_on U"
      by (rule Ck_on_1_iff_C1_differentiable_on
        [OF openU])
    have C1: "F C1_differentiable_on U"
      using C1_iff UF(1) by blast
    have contF: "continuous_on U
      (\<lambda>s. vector_derivative F (at s))"
      using C1
      by (simp add: C1_differentiable_on_eq)
    have cont_at: "continuous (at t within C)
      (\<lambda>s. vector_derivative F (at s))"
      using contF openU UF(2)
      by (meson continuous_on_eq_continuous_at
        continuous_at_imp_continuous_within)
    obtain d :: real where d: "0 < d"
      "ball t d \<subseteq> U"
      using open_contains_ball[THEN iffD1, OF openU]
        UF(2) by blast
    show "continuous (at t within C) ?g"
    proof (rule continuous_transform_within
        [OF cont_at d(1) tC])
      fix s
      assume sC: "s \<in> C"
        and near: "dist s t < d"
      have sU: "s \<in> U"
        using d(2) near
        by (auto simp: dist_commute)
      show "vector_derivative F (at s) = ?g s"
        using halfline_vector_derivative_of_local_C1
          [OF openC sC UF(1) sU]
          UF(3) by auto
    qed
  qed
  show ?thesis
    by (rule exI[where x="?g"])
       (use der cont in auto)
qed

context oriented_C1_halfline_atlas
begin

lemma chartwise_C1_halfline_derivative_data:
  assumes smooth: "chartwise_C1_scalar f"
    and i: "i \<in> I"
  shows "\<exists>g. (\<forall>t\<in>C i.
      ((\<lambda>s. f (from_chart i s))
        has_vector_derivative g t)
        (at t within {0..})) \<and>
    continuous_on (C i) g"
proof (rule halfline_C1_derivative_data
    [OF halfline_chart.open_C[OF chart[OF i]]])
  fix t assume t: "t \<in> C i"
  have at_i: "\<forall>t\<in>C i.
      \<exists>U F. Ck_on 1 F U \<and> t \<in> U \<and>
        (\<forall>s\<in>U \<inter> C i.
          F s = f (from_chart i s))"
    using smooth i
    unfolding chartwise_C1_scalar_def
    by blast
  have at_t: "\<exists>U F. Ck_on 1 F U \<and> t \<in> U \<and>
      (\<forall>s\<in>U \<inter> C i.
        F s = f (from_chart i s))"
    using at_i t by blast
  obtain U F where UF: "Ck_on 1 F U" "t \<in> U"
    "\<forall>s\<in>U \<inter> C i.
      F s = f (from_chart i s)"
    using at_t by blast
  show "\<exists>U F. Ck_on 1 F U \<and> t \<in> U \<and>
    (\<forall>s\<in>U \<inter> C i.
      f (from_chart i s) = F s)"
    by (rule exI[where x=U],
        rule exI[where x=F])
       (use UF in auto)
qed

lemma localized_chart_derivative_data:
  fixes omega phi :: "'a \<Rightarrow> real"
  assumes i: "i \<in> I"
    and compact: "compact K"
    and omega_support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and phi_closed: "closed L"
    and LD: "L \<subseteq> D i"
    and phi_support:
      "{p\<in>M. phi p \<noteq> 0} \<subseteq> L"
    and omega_C1: "chartwise_C1_scalar omega"
    and phi_C1: "chartwise_C1_scalar phi"
  obtains Q g where
    "compact Q"
    "Q \<subseteq> C i"
    "\<And>t. t \<in> C i \<Longrightarrow> t \<notin> Q \<Longrightarrow>
      phi (from_chart i t) *
        omega (from_chart i t) = 0"
    "\<And>t. t \<in> C i \<Longrightarrow>
      ((\<lambda>s. phi (from_chart i s) *
        omega (from_chart i s))
        has_vector_derivative g t)
        (at t within {0..})"
    "continuous_on (C i) g"
proof -
  let ?Q = "to_chart i ` (K \<inter> L)"
  have KL: "compact (K \<inter> L)"
    by (rule compact_Int_closed[OF compact phi_closed])
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
  have prod_C1:
    "chartwise_C1_scalar (\<lambda>p. phi p * omega p)"
    by (rule chartwise_C1_scalar_mult
      [OF phi_C1 omega_C1])
  obtain g where g:
    "\<forall>t\<in>C i.
      ((\<lambda>s.
        phi (from_chart i s) *
          omega (from_chart i s))
        has_vector_derivative g t)
        (at t within {0..})"
    "continuous_on (C i) g"
    using chartwise_C1_halfline_derivative_data
      [OF prod_C1 i] by blast
  have zero: "phi (from_chart i t) *
      omega (from_chart i t) = 0"
    if tC: "t \<in> C i" and out: "t \<notin> ?Q"
    for t
  proof (rule ccontr)
    assume nz: "phi (from_chart i t) *
        omega (from_chart i t) \<noteq> 0"
    have pD: "from_chart i t \<in> D i"
      using halfline_chart.inverse_image
        [OF chart[OF i]] tC by auto
    have pM: "from_chart i t \<in> M"
      using domain_subset_carrier[OF i] pD
      by auto
    have pK: "from_chart i t \<in> K"
      using omega_support[OF pM] nz by auto
    have pL: "from_chart i t \<in> L"
      using phi_support pM nz by auto
    have eq: "to_chart i (from_chart i t) = t"
      by (rule halfline_chart.from_to[OF chart[OF i] tC])
    have "to_chart i (from_chart i t) \<in> ?Q"
      using pK pL by auto
    then show False using out eq by simp
  qed
  show thesis
    by (rule that[where Q="?Q" and g=g])
       (use compactQ QC zero g in auto)
qed

end

end
