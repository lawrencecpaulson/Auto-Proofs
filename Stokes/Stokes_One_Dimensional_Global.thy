theory Stokes_One_Dimensional_Global
  imports Stokes_One_Dimensional_Regularity
begin

context oriented_C1_halfline_atlas
begin

theorem compact_support_one_dimensional_stokes:
  fixes omega :: "'a \<Rightarrow> real"
  assumes compact: "compact K"
    and KM: "K \<subseteq> M"
    and support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and smooth: "chartwise_C1_scalar omega"
  obtains F phi Q g where
    "finite F"
    "F \<subseteq> I"
    "K \<subseteq> (\<Union>i\<in>F. D i)"
    "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i p) = 1"
    "\<And>i. i \<in> F \<Longrightarrow>
      chartwise_C1_scalar (phi i)"
    "\<And>i. i \<in> F \<Longrightarrow>
      \<exists>L. closed L \<and>
        {p\<in>M. phi i p \<noteq> 0} \<subseteq> L \<and>
        L \<subseteq> D i"
    "\<And>i. i \<in> F \<Longrightarrow> compact (Q i)"
    "\<And>i. i \<in> F \<Longrightarrow> Q i \<subseteq> C i"
    "\<And>i t. i \<in> F \<Longrightarrow>
      t \<in> C i \<Longrightarrow> t \<notin> Q i
      \<Longrightarrow> phi i (from_chart i t) *
        omega (from_chart i t) = 0"
    "\<And>i t. i \<in> F \<Longrightarrow> t \<in> C i \<Longrightarrow>
      ((\<lambda>s.
        phi i (from_chart i s) *
          omega (from_chart i s))
        has_vector_derivative g i t)
        (at t within {0..})"
    "\<And>i. i \<in> F \<Longrightarrow>
      continuous_on (C i) (g i)"
    "(\<Sum>i\<in>F.
      eps i *
        (LINT t : C i | lborel. g i t)) =
      finite_boundary_zero_integral
        (K \<inter> boundary_carrier)
        (\<lambda>p.
          boundary_orientation p * omega p)"
proof -
  obtain phi F where F:
      "finite F" "F \<subseteq> I"
      "\<forall>p\<in>K. (\<Sum>i\<in>F. phi i p) = 1"
      "\<forall>i\<in>F. continuous_on M (phi i)"
      "\<forall>i\<in>F. chartwise_C1_scalar (phi i)"
      "\<forall>i\<in>F. \<exists>L. closed L \<and>
        {p\<in>M. phi i p \<noteq> 0} \<subseteq> L \<and>
        L \<subseteq> D i"
      "\<forall>i\<in>F. \<forall>p.
        0 \<le> phi i p \<and> phi i p \<le> 1"
    using compact_C1_partition_exists[OF compact KM]
    by blast
  let ?P = "\<lambda>i L. closed L \<and>
    {p\<in>M. phi i p \<noteq> 0} \<subseteq> L \<and>
    L \<subseteq> D i"
  have exL: "\<forall>i\<in>F. \<exists>L. ?P i L"
    using F(6) by simp
  obtain L where L:
    "\<forall>i\<in>F. ?P i (L i)"
    using bchoice[OF exL] by blast
  let ?G = "\<lambda>i t.
    phi i (from_chart i t) *
      omega (from_chart i t)"
  let ?Pdata = "\<lambda>i z.
    compact (fst z) \<and>
    fst z \<subseteq> C i \<and>
    (\<forall>t\<in>C i. t \<notin> fst z \<longrightarrow>
      ?G i t = 0) \<and>
    (\<forall>t\<in>C i.
      (?G i has_vector_derivative
        snd z t) (at t within {0..})) \<and>
    continuous_on (C i) (snd z)"
  have data_ex: "\<forall>i\<in>F.
    \<exists>z. ?Pdata i z"
  proof (intro ballI)
    fix i assume iF: "i \<in> F"
    have iI: "i \<in> I"
      using F(2) iF by auto
    have Li: "?P i (L i)"
      using L iF by auto
    have closedLi: "closed (L i)"
      using Li by simp
    have LDi: "L i \<subseteq> D i"
      using Li by simp
    have supportLi:
      "{p\<in>M. phi i p \<noteq> 0} \<subseteq> L i"
      using Li by simp
    have phiC1: "chartwise_C1_scalar (phi i)"
      using F(5) iF by auto
    show "\<exists>z. ?Pdata i z"
    proof (rule localized_chart_derivative_data
        [OF iI compact support
          closedLi LDi supportLi smooth phiC1])
      fix Q g
      assume q: "compact Q" "Q \<subseteq> C i"
        "\<And>t. t \<in> C i \<Longrightarrow> t \<notin> Q
          \<Longrightarrow> ?G i t = 0"
        "\<And>t. t \<in> C i \<Longrightarrow>
          (?G i has_vector_derivative g t)
          (at t within {0..})"
        "continuous_on (C i) g"
      show "\<exists>z. ?Pdata i z"
        by (rule exI[where x="(Q,g)"])
           (use q in auto)
    qed
  qed
  obtain Z where Z:
    "\<forall>i\<in>F. ?Pdata i (Z i)"
    using bchoice[OF data_ex] by blast
  let ?Q = "\<lambda>i. fst (Z i)"
  let ?g = "\<lambda>i. snd (Z i)"
  have coverF: "K \<subseteq> (\<Union>i\<in>F. D i)"
  proof
    fix p assume pK: "p \<in> K"
    have pM: "p \<in> M"
      using KM pK by auto
    have sum: "(\<Sum>i\<in>F. phi i p) = 1"
      using F(3) pK by auto
    obtain i where iF: "i \<in> F"
      and nz: "phi i p \<noteq> 0"
      using sum
      by (metis sum.neutral zero_neq_one)
    have pDi: "p \<in> D i"
      using F(6) iF pM nz by auto
    show "p \<in> (\<Union>i\<in>F. D i)"
      using iF pDi by auto
  qed
  have eq: "(\<Sum>i\<in>F.
      eps i *
        (LINT t : C i | lborel. ?g i t)) =
      finite_boundary_zero_integral
        (K \<inter> boundary_carrier)
        (\<lambda>p.
          boundary_orientation p * omega p)"
  proof (rule oriented_one_dimensional_finite_atlas_stokes
      [where F=F and K=K and phi=phi and
        G="?G" and g="?g" and L="?Q"])
    show "finite F" by (rule F(1))
    show "F \<subseteq> I" by (rule F(2))
    show "K \<subseteq> (\<Union>i\<in>F. D i)"
      by (rule coverF)
    show "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
      by (rule support)
    show "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i p) = 1"
      using F(3) by auto
    show "\<And>i p. i \<in> F \<Longrightarrow>
      p \<in> M \<Longrightarrow> p \<notin> D i
      \<Longrightarrow> phi i p = 0"
      using F(6) by auto
    show "\<And>i. i \<in> F \<Longrightarrow>
      compact (?Q i)"
      using Z by auto
    show "\<And>i. i \<in> F \<Longrightarrow>
      ?Q i \<subseteq> C i"
      using Z by auto
    show "\<And>i t. i \<in> F \<Longrightarrow>
      t \<in> C i \<Longrightarrow> t \<notin> ?Q i
      \<Longrightarrow> ?G i t = 0"
      using Z by auto
    show "\<And>i t. i \<in> F \<Longrightarrow>
      t \<in> C i \<Longrightarrow>
      (?G i has_vector_derivative ?g i t)
        (at t within {0..})"
      using Z by auto
    show "\<And>i. i \<in> F \<Longrightarrow>
      continuous_on (C i) (?g i)"
      using Z by auto
    show "\<And>i. i \<in> F \<Longrightarrow>
      0 \<in> C i \<Longrightarrow>
      ?G i 0 =
        phi i (from_chart i 0) *
          omega (from_chart i 0)"
      by simp
  qed
  show thesis
    by (rule that[where F=F and phi=phi
      and Q="?Q" and g="?g"])
       (use F Z eq coverF in auto)
qed

definition exact_chart_data where
  "exact_chart_data K omega F phi Q g \<longleftrightarrow>
    finite F \<and> F \<subseteq> I \<and>
    K \<subseteq> (\<Union>i\<in>F. D i) \<and>
    (\<forall>p\<in>K. (\<Sum>i\<in>F. phi i p) = 1) \<and>
    (\<forall>i\<in>F. \<forall>p\<in>M - D i. phi i p = 0) \<and>
    (\<forall>i\<in>F.
      compact (Q i) \<and> Q i \<subseteq> C i \<and>
      (\<forall>t\<in>C i. t \<notin> Q i \<longrightarrow>
        phi i (from_chart i t) *
          omega (from_chart i t) = 0) \<and>
      (\<forall>t\<in>C i.
        ((\<lambda>s. phi i (from_chart i s) *
          omega (from_chart i s))
          has_vector_derivative g i t)
          (at t within {0..})) \<and>
      continuous_on (C i) (g i))"

definition exact_chart_value where
  "exact_chart_value F g =
    (\<Sum>i\<in>F.
      eps i * (LINT t : C i | lborel. g i t))"

theorem exact_chart_data_stokes:
  fixes omega :: "'a \<Rightarrow> real"
  assumes support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and data: "exact_chart_data K omega F phi Q g"
  shows "exact_chart_value F g =
    finite_boundary_zero_integral
      (K \<inter> boundary_carrier)
      (\<lambda>p.
        boundary_orientation p * omega p)"
  unfolding exact_chart_value_def
proof (rule oriented_one_dimensional_finite_atlas_stokes
    [where F=F and K=K and phi=phi and
      L=Q and g=g and
      G="\<lambda>i t.
        phi i (from_chart i t) *
          omega (from_chart i t)"])
  show "finite F"
    using data by (simp add: exact_chart_data_def)
  show "F \<subseteq> I"
    using data by (simp add: exact_chart_data_def)
  show "K \<subseteq> (\<Union>i\<in>F. D i)"
    using data by (simp add: exact_chart_data_def)
  show "\<And>p. p \<in> M \<Longrightarrow>
    p \<notin> K \<Longrightarrow> omega p = 0"
    by (rule support)
  show "\<And>p. p \<in> K \<Longrightarrow>
    (\<Sum>i\<in>F. phi i p) = 1"
    using data by (auto simp: exact_chart_data_def)
  show "\<And>i p. i \<in> F \<Longrightarrow>
    p \<in> M \<Longrightarrow> p \<notin> D i
    \<Longrightarrow> phi i p = 0"
    using data by (auto simp: exact_chart_data_def)
  show "\<And>i. i \<in> F \<Longrightarrow> compact (Q i)"
    using data by (auto simp: exact_chart_data_def)
  show "\<And>i. i \<in> F \<Longrightarrow> Q i \<subseteq> C i"
    using data by (auto simp: exact_chart_data_def)
  show "\<And>i t. i \<in> F \<Longrightarrow>
    t \<in> C i \<Longrightarrow> t \<notin> Q i \<Longrightarrow>
    phi i (from_chart i t) *
      omega (from_chart i t) = 0"
    using data by (auto simp: exact_chart_data_def)
  show "\<And>i t. i \<in> F \<Longrightarrow> t \<in> C i
    \<Longrightarrow>
    ((\<lambda>s. phi i (from_chart i s) *
      omega (from_chart i s))
      has_vector_derivative g i t)
      (at t within {0..})"
    using data by (auto simp: exact_chart_data_def)
  show "\<And>i. i \<in> F \<Longrightarrow>
    continuous_on (C i) (g i)"
    using data by (auto simp: exact_chart_data_def)
  show "\<And>i. i \<in> F \<Longrightarrow>
    0 \<in> C i \<Longrightarrow>
    phi i (from_chart i 0) *
      omega (from_chart i 0) =
    phi i (from_chart i 0) *
      omega (from_chart i 0)"
    by simp
qed

corollary exact_chart_value_independent:
  fixes omega :: "'a \<Rightarrow> real"
  assumes support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and first: "exact_chart_data K omega F phi Q g"
    and second: "exact_chart_data K omega H psi R h"
  shows "exact_chart_value F g =
    exact_chart_value H h"
  using exact_chart_data_stokes[OF support first]
    exact_chart_data_stokes[OF support second]
  by simp

theorem exact_chart_data_exists:
  fixes omega :: "'a \<Rightarrow> real"
  assumes compact: "compact K"
    and KM: "K \<subseteq> M"
    and support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and smooth: "chartwise_C1_scalar omega"
  shows "\<exists>F phi Q g.
    exact_chart_data K omega F phi Q g"
proof (rule compact_support_one_dimensional_stokes
    [OF compact KM support smooth])
  fix F phi Q g
  assume F: "finite F" "F \<subseteq> I"
    "K \<subseteq> (\<Union>i\<in>F. D i)"
    and unity: "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i p) = 1"
    and phi_C1: "\<And>i. i \<in> F \<Longrightarrow>
      chartwise_C1_scalar (phi i)"
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
        (\<lambda>p.
          boundary_orientation p * omega p)"
  have outside: "phi i p = 0"
    if iF: "i \<in> F" and pM: "p \<in> M"
      and out: "p \<notin> D i" for i p
  proof -
    obtain L where L: "closed L"
      "{p\<in>M. phi i p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> D i"
      using phi_support[OF iF] by blast
    show ?thesis using L pM out by auto
  qed
  have data: "exact_chart_data K omega F phi Q g"
    using F unity outside compactQ QC zero
      deriv cont
    by (auto simp: exact_chart_data_def)
  show "\<exists>F phi Q g.
    exact_chart_data K omega F phi Q g"
    by (rule exI[where x=F],
        rule exI[where x=phi],
        rule exI[where x=Q],
        rule exI[where x=g])
       (rule data)
qed

definition exact_body_integral where
  "exact_body_integral K omega =
    (SOME v. \<exists>F phi Q g.
      exact_chart_data K omega F phi Q g \<and>
      v = exact_chart_value F g)"

lemma exact_body_integral_chart_value:
  fixes omega :: "'a \<Rightarrow> real"
  assumes support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and data: "exact_chart_data K omega F phi Q g"
  shows "exact_body_integral K omega =
    exact_chart_value F g"
proof -
  let ?P = "\<lambda>v. \<exists>F phi Q g.
      exact_chart_data K omega F phi Q g \<and>
      v = exact_chart_value F g"
  have ex: "\<exists>v. ?P v"
    using data by blast
  have chosen: "?P (exact_body_integral K omega)"
    unfolding exact_body_integral_def
    by (rule someI_ex[OF ex])
  obtain H psi R h where other:
      "exact_chart_data K omega H psi R h"
      "exact_body_integral K omega =
        exact_chart_value H h"
    using chosen by blast
  show ?thesis
    using other(2)
      exact_chart_value_independent
        [OF support other(1) data]
    by simp
qed

theorem exact_body_integral_stokes:
  fixes omega :: "'a \<Rightarrow> real"
  assumes compact: "compact K"
    and KM: "K \<subseteq> M"
    and support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and smooth: "chartwise_C1_scalar omega"
  shows "exact_body_integral K omega =
    finite_boundary_zero_integral
      (K \<inter> boundary_carrier)
      (\<lambda>p.
        boundary_orientation p * omega p)"
proof -
  obtain F phi Q g where data:
    "exact_chart_data K omega F phi Q g"
    using exact_chart_data_exists
      [OF compact KM support smooth] by blast
  show ?thesis
    using exact_body_integral_chart_value
        [OF support data]
      exact_chart_data_stokes[OF support data]
    by simp
qed

corollary exact_body_integral_support_independent:
  fixes omega :: "'a \<Rightarrow> real"
  assumes compactK: "compact K"
    and KM: "K \<subseteq> M"
    and supportK: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and compactL: "compact L"
    and LM: "L \<subseteq> M"
    and supportL: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> L \<Longrightarrow> omega p = 0"
    and smooth: "chartwise_C1_scalar omega"
  shows "exact_body_integral K omega =
    exact_body_integral L omega"
proof -
  let ?f = "\<lambda>p.
    boundary_orientation p * omega p"
  let ?S = "K \<inter> L \<inter> boundary_carrier"
  have finiteK: "finite (K \<inter> boundary_carrier)"
    by (rule compact_boundary_finite[OF compactK KM])
  have finiteL: "finite (L \<inter> boundary_carrier)"
    by (rule compact_boundary_finite[OF compactL LM])
  have sumK: "(\<Sum>p\<in>K \<inter> boundary_carrier. ?f p) =
    (\<Sum>p\<in>?S. ?f p)"
    by (rule sum.mono_neutral_right[OF finiteK])
       (use supportL KM in auto)
  have sumL: "(\<Sum>p\<in>L \<inter> boundary_carrier. ?f p) =
    (\<Sum>p\<in>?S. ?f p)"
    by (rule sum.mono_neutral_right[OF finiteL])
       (use supportK LM in auto)
  show ?thesis
    using exact_body_integral_stokes
        [OF compactK KM supportK smooth]
      exact_body_integral_stokes
        [OF compactL LM supportL smooth]
      sumK sumL
    by (simp add: finite_boundary_zero_integral_def
      Int_ac)
qed

corollary exact_body_integral_empty_boundary:
  fixes omega :: "'a \<Rightarrow> real"
  assumes compact: "compact K"
    and KM: "K \<subseteq> M"
    and support: "\<And>p. p \<in> M \<Longrightarrow>
      p \<notin> K \<Longrightarrow> omega p = 0"
    and smooth: "chartwise_C1_scalar omega"
    and empty: "boundary_carrier = {}"
  shows "exact_body_integral K omega = 0"
  using exact_body_integral_stokes
    [OF compact KM support smooth]
  by (simp add: empty finite_boundary_zero_integral_def)

corollary exact_body_integral_compact_carrier:
  fixes omega :: "'a \<Rightarrow> real"
  assumes compact: "compact M"
    and smooth: "chartwise_C1_scalar omega"
  shows "exact_body_integral M omega =
    finite_boundary_zero_integral boundary_carrier
      (\<lambda>p.
        boundary_orientation p * omega p)"
proof -
  have eq: "M \<inter> boundary_carrier =
      boundary_carrier"
    using boundary_subset_carrier by auto
  have support: "\<And>p. p \<in> M \<Longrightarrow>
    p \<notin> M \<Longrightarrow> omega p = 0"
    by simp
  show ?thesis
    using exact_body_integral_stokes
      [OF compact order_refl support smooth]
    by (simp add: eq)
qed

end

end
