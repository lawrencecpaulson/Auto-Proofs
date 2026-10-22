theory Stokes_Manifold_Integration
  imports
    "Smooth_Manifolds.Partition_Of_Unity"
    Stokes_Oriented_Integration
begin

definition chart_overlap ::
    "('a::topological_space, 'e::euclidean_space) chart \<Rightarrow>
      ('a, 'e) chart \<Rightarrow> 'e set"
  where "chart_overlap c d = c ` (domain c \<inter> domain d)"

definition chart_transition ::
    "('a::topological_space, 'e::euclidean_space) chart \<Rightarrow>
      ('a, 'e) chart \<Rightarrow> 'e \<Rightarrow> 'e"
  where "chart_transition c d = d \<circ> inv_chart c"

lemma chart_overlap_open:
  "open (chart_overlap c d)"
  unfolding chart_overlap_def
  by (rule open_chart_image) auto

lemma chart_transition_image:
  "chart_transition c d ` chart_overlap c d =
    chart_overlap d c"
  by (auto simp: chart_transition_def chart_overlap_def
    image_iff)

lemma chart_transition_inj:
  "inj_on (chart_transition c d) (chart_overlap c d)"
proof (rule inj_onI)
  fix x y
  assume x: "x \<in> chart_overlap c d"
    and y: "y \<in> chart_overlap c d"
    and eq: "chart_transition c d x = chart_transition c d y"
  obtain u where u: "u \<in> domain c" "u \<in> domain d" "x = c u"
    using x by (auto simp: chart_overlap_def)
  obtain v where v: "v \<in> domain c" "v \<in> domain d" "y = c v"
    using y by (auto simp: chart_overlap_def)
  have "d u = d v"
    using eq u v
    by (simp add: chart_transition_def)
  then have "u = v"
    using inj_on_apply_chart[of d] u v
    by (auto simp: inj_on_def)
  then show "x = y" using u v by simp
qed

theorem chart_overlap_integral:
  fixes c d :: "('a::topological_space, real ^ 'n::finite) chart"
    and alpha beta :: "real ^ 'n \<Rightarrow> real"
  assumes differentiable: "\<And>x. x \<in> chart_overlap c d \<Longrightarrow>
      chart_transition c d differentiable (at x)"
    and positive: "\<And>x. x \<in> chart_overlap c d \<Longrightarrow>
      0 < Determinants.det
        (jacobian (chart_transition c d) (at x))"
    and integrable: "beta absolutely_integrable_on
      chart_overlap d c"
    and compatible: "\<And>x. x \<in> chart_overlap c d \<Longrightarrow>
      alpha x = pull_top (chart_transition c d) beta x"
  shows "integral (chart_overlap c d) alpha =
    integral (chart_overlap d c) beta"
proof -
  have measurable: "chart_overlap c d \<in> sets lebesgue"
    using chart_overlap_open[of c d]
    by (metis borel_open sets_lborel sets_completionI_sets)
  have integrable': "beta absolutely_integrable_on
      (chart_transition c d ` chart_overlap c d)"
    using integrable by (simp add: chart_transition_image)
  have change: "integral (chart_overlap c d) alpha =
    integral (chart_transition c d ` chart_overlap c d) beta"
    by (rule oriented_chart_overlap_integral
      [OF measurable differentiable
        chart_transition_inj positive integrable' compatible])
  show ?thesis using change
    by (simp add: chart_transition_image)
qed

context c_manifold
begin

lemma diff_fun_chart_continuous:
  assumes c: "c \<in> atlas"
    and diff: "diff_fun k charts rho"
  shows "continuous_on (codomain c) (rho \<circ> inv_chart c)"
proof (cases "domain c = {}")
  case True
  then have "codomain c = {}"
    using image_domain_eq[of c] by simp
  then show ?thesis by simp
next
  case False
  then obtain p where p: "p \<in> domain c" by auto
  interpret R: diff_fun k charts rho
    by (rule diff)
  have "k-smooth_on (codomain c) (rho \<circ> inv_chart c)"
    by (rule R.diff_fun_between_chartsD[OF c p])
  then show ?thesis
    by (rule smooth_on_imp_continuous_on)
qed

lemma chart_transition_differentiable:
  assumes c: "c \<in> atlas" and d: "d \<in> atlas"
    and k: "k \<noteq> 0"
    and x: "x \<in> chart_overlap c d"
  shows "chart_transition c d differentiable (at x)"
proof -
  have smooth: "k-smooth_on (chart_overlap c d)
      (chart_transition c d)"
    unfolding chart_overlap_def chart_transition_def
    by (rule smooth_compat_D1[OF atlas_is_atlas[OF c d]])
  have d_on: "chart_transition c d
      differentiable_on chart_overlap c d"
    by (rule smooth_on_imp_differentiable_on[OF smooth k])
  have d_within: "chart_transition c d
      differentiable (at x within chart_overlap c d)"
    using d_on x by (auto simp: differentiable_on_def)
  have at_eq: "at x within chart_overlap c d = at x"
    by (rule at_within_open[OF x chart_overlap_open])
  show ?thesis
    using d_within by (simp only: at_eq)
qed

lemma finite_partition_on_compact:
  fixes K :: "'a set"
  assumes lf: "locally_finite_on carrier I
      (\<lambda>i. csupport_on carrier (phi i))"
    and unity: "\<And>x. x \<in> carrier \<Longrightarrow>
      (\<Sum>i\<in>{i\<in>I. phi i x \<noteq> 0}. phi i x) = 1"
    and compact: "compact K"
    and Kcarrier: "K \<subseteq> carrier"
  obtains F where "finite F" "F \<subseteq> I"
    "\<And>x. x \<in> K \<Longrightarrow> (\<Sum>i\<in>F. phi i x) = 1"
proof -
  let ?F = "{i\<in>I. csupport_on carrier (phi i) \<inter> K \<noteq> {}}"
  have finite: "finite ?F"
    by (rule locally_finite_compactD[OF lf compact Kcarrier])
  have subset: "?F \<subseteq> I" by auto
  have support_subset: "{i\<in>I. phi i x \<noteq> 0} \<subseteq> ?F"
    if "x \<in> K" for x
  proof
    fix i
    assume i: "i \<in> {i\<in>I. phi i x \<noteq> 0}"
    have "x \<in> carrier" using Kcarrier that by auto
    with i have "x \<in> support_on carrier (phi i)"
      by (auto simp: support_on_def)
    then have "x \<in> csupport_on carrier (phi i)"
      unfolding csupport_on_def
      using closure_subset by blast
    with i that show "i \<in> ?F" by auto
  qed
  have sum_eq: "(\<Sum>i\<in>?F. phi i x) = 1"
    if "x \<in> K" for x
  proof -
    let ?A = "{i\<in>I. phi i x \<noteq> 0}"
    have "(\<Sum>i\<in>?A. phi i x) = (\<Sum>i\<in>?F. phi i x)"
      by (rule sum.mono_neutral_cong_left
        [OF finite support_subset[OF that]]) auto
    then show ?thesis using unity Kcarrier that by auto
  qed
  show ?thesis
    by (rule that[OF finite subset sum_eq])
qed

lemma compact_partition_of_unityE:
  fixes X :: "'i \<Rightarrow> 'a set"
  assumes cover: "carrier \<subseteq> (\<Union>i\<in>I. X i)"
    and openX: "\<And>i. i \<in> I \<Longrightarrow> open (X i)"
    and compact: "compact K"
    and Kcarrier: "K \<subseteq> carrier"
  shows "\<exists>(phi::'i \<Rightarrow> 'a \<Rightarrow> real) (F::'i set).
    finite F \<and> F \<subseteq> I \<and>
    (\<forall>x\<in>K. (\<Sum>i\<in>F. phi i x) = 1) \<and>
    (\<forall>i\<in>F. diff_fun k charts (phi i)) \<and>
    (\<forall>i\<in>F.
      csupport_on carrier (phi i) \<inter> carrier \<subseteq> X i)"
proof -
  show ?thesis
  proof (rule partitions_of_unityE[OF cover openX])
    fix phi :: "'i \<Rightarrow> 'a \<Rightarrow> real"
    assume diff: "\<And>i. i \<in> I \<Longrightarrow> diff_fun k charts (phi i)"
      and unity: "\<And>x. x \<in> carrier \<Longrightarrow>
        (\<Sum>i\<in>{i\<in>I. phi i x \<noteq> 0}. phi i x) = 1"
      and support: "\<And>i. i \<in> I \<Longrightarrow>
        csupport_on carrier (phi i) \<inter> carrier \<subseteq> X i"
      and lf: "locally_finite_on carrier I
        (\<lambda>i. csupport_on carrier (phi i))"
    show ?thesis
    proof (rule finite_partition_on_compact
        [OF lf unity compact Kcarrier])
      fix F
      assume finite: "finite F" and subset: "F \<subseteq> I"
        and sum: "\<And>x. x \<in> K \<Longrightarrow>
          (\<Sum>i\<in>F. phi i x) = 1"
      show ?thesis
        apply (rule exI[where x=phi])
        apply (rule exI[where x=F])
        using finite subset sum diff support by blast
    qed
  qed
qed

lemma compact_partition_decomposition:
  fixes f :: "'a \<Rightarrow> real"
  assumes unity: "\<And>x. x \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i x) = 1"
    and support: "support_on carrier f \<subseteq> K"
    and x: "x \<in> carrier"
  shows "f x = (\<Sum>i\<in>F. phi i x * f x)"
proof (cases "x \<in> K")
  case True
  then show ?thesis
    using unity[OF True]
    by (simp add: sum_distrib_right[symmetric])
next
  case False
  have "f x = 0"
    using support x False
    by (auto simp: support_on_def)
  then show ?thesis by simp
qed

end

theorem oriented_atlas_overlap_integral:
  fixes charts :: "('a::{second_countable_topology,t2_space},
      real ^ 'n::finite) chart set"
    and c d :: "('a, real ^ 'n) chart"
    and alpha beta :: "real ^ 'n \<Rightarrow> real"
  assumes manifold: "c_manifold charts k"
    and c: "c \<in> c_manifold.atlas charts k"
    and d: "d \<in> c_manifold.atlas charts k"
    and k: "k \<noteq> 0"
    and positive: "\<And>x. x \<in> chart_overlap c d \<Longrightarrow>
      0 < Determinants.det
        (jacobian (chart_transition c d) (at x))"
    and integrable: "beta absolutely_integrable_on
      chart_overlap d c"
    and compatible: "\<And>x. x \<in> chart_overlap c d \<Longrightarrow>
      alpha x = pull_top (chart_transition c d) beta x"
  shows "integral (chart_overlap c d) alpha =
    integral (chart_overlap d c) beta"
proof -
  interpret M: c_manifold charts k
    by (rule manifold)
  show ?thesis
    by (rule chart_overlap_integral)
       (use M.chart_transition_differentiable[OF c d k]
         positive integrable compatible in auto)
qed

locale oriented_c_manifold =
  c_manifold charts k
  for charts :: "('a::{second_countable_topology,t2_space},
      real ^ 'n::finite) chart set" and k +
  fixes oriented_charts :: "('a, real ^ 'n) chart set"
  assumes oriented_subset: "oriented_charts \<subseteq> atlas"
    and oriented_cover:
      "carrier \<subseteq> (\<Union>c\<in>oriented_charts. domain c)"
    and positive_overlap: "\<And>c d x.
      c \<in> oriented_charts \<Longrightarrow>
      d \<in> oriented_charts \<Longrightarrow>
      x \<in> chart_overlap c d \<Longrightarrow>
      0 < Determinants.det
        (jacobian (chart_transition c d) (at x))"
    and smooth_rank: "k \<noteq> 0"
begin

definition top_coeff_compatible ::
    "(('a, real ^ 'n) chart \<Rightarrow>
      real ^ 'n \<Rightarrow> real) \<Rightarrow> bool"
  where "top_coeff_compatible alpha \<longleftrightarrow>
    (\<forall>c\<in>oriented_charts. \<forall>d\<in>oriented_charts.
      \<forall>x\<in>chart_overlap c d.
        alpha c x =
          pull_top (chart_transition c d) (alpha d) x)"

definition top_form_support ::
    "(('a, real ^ 'n) chart \<Rightarrow>
      real ^ 'n \<Rightarrow> real) \<Rightarrow> 'a set"
  where "top_form_support alpha =
    {p\<in>carrier. \<exists>c\<in>oriented_charts.
      p \<in> domain c \<and> alpha c (c p) \<noteq> 0}"

definition weight_top_coeff ::
    "('a \<Rightarrow> real) \<Rightarrow>
      (('a, real ^ 'n) chart \<Rightarrow> real ^ 'n \<Rightarrow> real) \<Rightarrow>
      ('a, real ^ 'n) chart \<Rightarrow> real ^ 'n \<Rightarrow> real"
  where "weight_top_coeff
      (rho::'a \<Rightarrow> real)
      (alpha::('a, real ^ 'n) chart \<Rightarrow> real ^ 'n \<Rightarrow> real)
      (c::('a, real ^ 'n) chart)
      (x::real ^ 'n) =
    rho (inv_chart c x) * alpha c x"

lemma weight_top_coeff_compatible:
  assumes compatible: "top_coeff_compatible alpha"
  shows "top_coeff_compatible (weight_top_coeff rho alpha)"
proof (unfold top_coeff_compatible_def, intro ballI)
  fix c d x
  assume c: "c \<in> oriented_charts"
    and d: "d \<in> oriented_charts"
    and x: "x \<in> chart_overlap c d"
  obtain p where p: "p \<in> domain c" "p \<in> domain d"
    "x = c p"
    using x by (auto simp: chart_overlap_def)
  have coeff: "alpha c x =
    pull_top (chart_transition c d) (alpha d) x"
    using compatible c d x
    by (auto simp: top_coeff_compatible_def)
  show "weight_top_coeff rho alpha c x =
    pull_top (chart_transition c d)
      (weight_top_coeff rho alpha d) x"
    using coeff p
    by (simp add: weight_top_coeff_def pull_top_def
      chart_transition_def algebra_simps)
qed

lemma weight_top_coeff_continuous:
  assumes diff: "diff_fun k charts rho"
    and coeff_cont: "\<And>c. c \<in> oriented_charts \<Longrightarrow>
      continuous_on (codomain c) (alpha c)"
    and c: "c \<in> oriented_charts"
  shows "continuous_on (codomain c)
    (weight_top_coeff rho alpha c)"
proof -
  have "continuous_on (codomain c) (rho \<circ> inv_chart c)"
    by (rule diff_fun_chart_continuous
      [OF subsetD[OF oriented_subset c] diff])
  with coeff_cont[OF c] show ?thesis
    by (auto simp: weight_top_coeff_def o_def
      intro!: continuous_intros)
qed

lemma top_form_support_weight:
  assumes compatible: "top_coeff_compatible alpha"
  shows "top_form_support (weight_top_coeff rho alpha)
    \<subseteq> top_form_support alpha \<inter>
      csupport_on carrier rho"
proof
  fix p
  assume p: "p \<in> top_form_support
    (weight_top_coeff rho alpha)"
  then obtain c where c: "c \<in> oriented_charts"
    "p \<in> domain c"
    "weight_top_coeff rho alpha c (c p) \<noteq> 0"
    by (auto simp: top_form_support_def)
  have coeff: "rho p * alpha c (c p) \<noteq> 0"
    using c by (simp add: weight_top_coeff_def)
  have "p \<in> top_form_support alpha"
    using p c coeff
    by (auto simp: top_form_support_def)
  moreover have "p \<in> csupport_on carrier rho"
    using p coeff
    by (auto simp: top_form_support_def
      csupport_on_def support_on_def intro: in_closureI)
  ultimately show "p \<in> top_form_support alpha \<inter>
      csupport_on carrier rho"
    by auto
qed

lemma top_form_support_chart:
  assumes compatible: "top_coeff_compatible alpha"
    and c: "c \<in> oriented_charts"
    and p: "p \<in> domain c"
  shows "p \<in> top_form_support alpha \<longleftrightarrow>
    alpha c (c p) \<noteq> 0"
proof
  assume p_support: "p \<in> top_form_support alpha"
  then obtain d where d: "d \<in> oriented_charts"
    "p \<in> domain d" "alpha d (d p) \<noteq> 0"
    by (auto simp: top_form_support_def)
  have overlap: "c p \<in> chart_overlap c d"
    using p d by (auto simp: chart_overlap_def)
  have coeff: "alpha c (c p) =
      Determinants.det
        (jacobian (chart_transition c d) (at (c p))) *
      alpha d (d p)"
    using compatible c d overlap p
    by (auto simp: top_coeff_compatible_def pull_top_def
      chart_transition_def)
  have positive: "0 < Determinants.det
      (jacobian (chart_transition c d) (at (c p)))"
    by (rule positive_overlap[OF c d(1) overlap])
  show "alpha c (c p) \<noteq> 0"
    using coeff positive d by simp
next
  assume nonzero: "alpha c (c p) \<noteq> 0"
  have "p \<in> carrier"
    using c p oriented_subset
    by (auto intro: in_carrier_atlasI)
  with c p nonzero show "p \<in> top_form_support alpha"
    by (auto simp: top_form_support_def)
qed

lemma chart_weight_absolutely_integrable:
  assumes c: "c \<in> oriented_charts"
    and compatible: "top_coeff_compatible alpha"
    and compact: "compact K"
    and Kcarrier: "K \<subseteq> carrier"
    and support: "top_form_support alpha \<subseteq> K"
    and coeff_cont: "continuous_on (codomain c) (alpha c)"
    and diff: "diff_fun k charts rho"
    and rho_loc:
      "K \<inter> csupport_on carrier rho \<subseteq> domain c"
  shows "weight_top_coeff rho alpha c
    absolutely_integrable_on codomain c"
proof -
  let ?C = "K \<inter> csupport_on carrier rho"
  have compactC: "compact ?C"
    by (rule compact_Int_closed[OF compact]) simp
  have Cdom: "?C \<subseteq> domain c"
    using rho_loc .
  have continuous_c: "continuous_on ?C c"
    by (rule continuous_on_subset[OF continuous_on_domain Cdom])
  have compact_image: "compact (c ` ?C)"
    by (rule compact_continuous_image[OF continuous_c compactC])
  have subset_image: "c ` ?C \<subseteq> codomain c"
    using Cdom by auto
  have cont_rho: "continuous_on (codomain c)
      (rho \<circ> inv_chart c)"
    by (rule diff_fun_chart_continuous
      [OF subsetD[OF oriented_subset c] diff])
  have cont_weight: "continuous_on (codomain c)
      (weight_top_coeff rho alpha c)"
    using cont_rho coeff_cont
    by (auto simp: weight_top_coeff_def o_def
      intro!: continuous_intros)
  have cont_image: "continuous_on (c ` ?C)
      (weight_top_coeff rho alpha c)"
    by (rule continuous_on_subset[OF cont_weight subset_image])
  have zero: "weight_top_coeff rho alpha c x = 0"
    if x: "x \<in> codomain c" "x \<notin> c ` ?C" for x
  proof -
    let ?p = "inv_chart c x"
    have p: "?p \<in> domain c" and cp: "c ?p = x"
      using x by auto
    have carrier: "?p \<in> carrier"
      using c p oriented_subset
      by (auto intro: in_carrier_atlasI)
    have notC: "?p \<notin> ?C"
    proof
      assume "?p \<in> ?C"
      then have "c ?p \<in> c ` ?C" by blast
      with cp x show False by simp
    qed
    show ?thesis
    proof (cases "?p \<in> K")
      case False
      have "?p \<notin> top_form_support alpha"
        using support False by auto
      then have "alpha c x = 0"
        using top_form_support_chart[OF compatible c p] cp
        by auto
      then show ?thesis
        by (simp add: weight_top_coeff_def)
    next
      case True
      with notC have "?p \<notin> csupport_on carrier rho"
        by auto
      then have "rho ?p = 0"
        using carrier by (rule not_in_csupportD)
      then show ?thesis
        by (simp add: weight_top_coeff_def)
    qed
  qed
  show ?thesis
    by (rule absolutely_integrable_compact_support
      [OF compact_image cont_image subset_image zero])
qed

lemma compatible_overlap_integral:
  assumes c: "c \<in> oriented_charts"
    and d: "d \<in> oriented_charts"
    and compatible: "top_coeff_compatible alpha"
    and integrable: "alpha d absolutely_integrable_on
      chart_overlap d c"
  shows "integral (chart_overlap c d) (alpha c) =
    integral (chart_overlap d c) (alpha d)"
  by (rule oriented_atlas_overlap_integral
      [OF c_manifold_axioms
        subsetD[OF oriented_subset c]
        subsetD[OF oriented_subset d]
        smooth_rank])
     (use positive_overlap[OF c d]
       integrable compatible c d in
       \<open>auto simp: top_coeff_compatible_def\<close>)

lemma weighted_overlap_integral:
  assumes c: "c \<in> oriented_charts"
    and d: "d \<in> oriented_charts"
    and compatible: "top_coeff_compatible alpha"
    and integrable: "weight_top_coeff rho alpha d
      absolutely_integrable_on chart_overlap d c"
  shows "integral (chart_overlap c d)
      (weight_top_coeff rho alpha c) =
    integral (chart_overlap d c)
      (weight_top_coeff rho alpha d)"
  by (rule compatible_overlap_integral
    [OF c d weight_top_coeff_compatible[OF compatible]
      integrable])

lemma chart_integral_localized:
  assumes c: "c \<in> oriented_charts"
    and localized: "\<And>p. p \<in> carrier \<Longrightarrow>
      rho p \<noteq> 0 \<Longrightarrow> p \<in> domain c \<inter> domain d"
  shows "integral (codomain c) (weight_top_coeff rho alpha c) =
    integral (chart_overlap c d) (weight_top_coeff rho alpha c)"
proof -
  have zero: "weight_top_coeff rho alpha c x = 0"
    if x: "x \<in> codomain c" "x \<notin> chart_overlap c d"
    for x
  proof -
    let ?p = "inv_chart c x"
    have p: "?p \<in> domain c"
      using x by simp
    have carrier: "?p \<in> carrier"
      using c p oriented_subset
      by (auto intro: in_carrier_atlasI)
    have c_p: "c ?p = x"
      using x by simp
    have not_d: "?p \<notin> domain d"
    proof
      assume "?p \<in> domain d"
      with p have "?p \<in> domain c \<inter> domain d" by auto
      then have "c ?p \<in> chart_overlap c d"
        unfolding chart_overlap_def by blast
      with c_p x show False by simp
    qed
    have "rho ?p = 0"
      using localized[OF carrier] not_d by auto
    then show ?thesis
      by (simp add: weight_top_coeff_def)
  qed
  have subset: "chart_overlap c d \<subseteq> codomain c"
    by (auto simp: chart_overlap_def)
  have "integral (codomain c) (weight_top_coeff rho alpha c) =
    integral (codomain c)
      (\<lambda>x. if x \<in> chart_overlap c d then
        weight_top_coeff rho alpha c x else 0)"
    by (rule integral_cong) (use zero in auto)
  also have "\<dots> =
    integral (chart_overlap c d) (weight_top_coeff rho alpha c)"
    using subset by (simp add: integral_restrict_Int inf.absorb1)
  finally show ?thesis .
qed

lemma localized_chart_integral_eq:
  assumes c: "c \<in> oriented_charts"
    and d: "d \<in> oriented_charts"
    and compatible: "top_coeff_compatible alpha"
    and localized: "\<And>p. p \<in> carrier \<Longrightarrow>
      rho p \<noteq> 0 \<Longrightarrow> p \<in> domain c \<inter> domain d"
    and integrable: "weight_top_coeff rho alpha d
      absolutely_integrable_on chart_overlap d c"
  shows "integral (codomain c) (weight_top_coeff rho alpha c) =
    integral (codomain d) (weight_top_coeff rho alpha d)"
proof -
  have localized_d: "\<And>p. p \<in> carrier \<Longrightarrow>
      rho p \<noteq> 0 \<Longrightarrow> p \<in> domain d \<inter> domain c"
    using localized by auto
  have "integral (codomain c) (weight_top_coeff rho alpha c) =
    integral (chart_overlap c d) (weight_top_coeff rho alpha c)"
    by (rule chart_integral_localized[OF c localized])
  also have "\<dots> =
    integral (chart_overlap d c) (weight_top_coeff rho alpha d)"
    by (rule weighted_overlap_integral[OF c d compatible integrable])
  also have "\<dots> =
    integral (codomain d) (weight_top_coeff rho alpha d)"
    by (rule chart_integral_localized[OF d localized_d, symmetric])
  finally show ?thesis .
qed

lemma chart_integral_localized_form:
  assumes c: "c \<in> oriented_charts"
    and compatible: "top_coeff_compatible alpha"
    and localized: "\<And>p. p \<in> top_form_support alpha \<Longrightarrow>
      rho p \<noteq> 0 \<Longrightarrow> p \<in> domain d"
  shows "integral (codomain c) (weight_top_coeff rho alpha c) =
    integral (chart_overlap c d) (weight_top_coeff rho alpha c)"
proof -
  have zero: "weight_top_coeff rho alpha c x = 0"
    if x: "x \<in> codomain c" "x \<notin> chart_overlap c d"
    for x
  proof -
    let ?p = "inv_chart c x"
    have p: "?p \<in> domain c" and cp: "c ?p = x"
      using x by auto
    have not_d: "?p \<notin> domain d"
    proof
      assume "?p \<in> domain d"
      with p have "?p \<in> domain c \<inter> domain d" by auto
      then have "c ?p \<in> chart_overlap c d"
        unfolding chart_overlap_def by blast
      with cp x show False by simp
    qed
    show ?thesis
    proof (cases "alpha c x = 0")
      case True
      then show ?thesis
        by (simp add: weight_top_coeff_def)
    next
      case False
      have "?p \<in> top_form_support alpha"
        using top_form_support_chart[OF compatible c p] cp False
        by simp
      then have "rho ?p = 0"
        using localized not_d by auto
      then show ?thesis
        by (simp add: weight_top_coeff_def)
    qed
  qed
  have subset: "chart_overlap c d \<subseteq> codomain c"
    by (auto simp: chart_overlap_def)
  have "integral (codomain c) (weight_top_coeff rho alpha c) =
    integral (codomain c)
      (\<lambda>x. if x \<in> chart_overlap c d then
        weight_top_coeff rho alpha c x else 0)"
    by (rule integral_cong) (use zero in auto)
  also have "\<dots> =
    integral (chart_overlap c d) (weight_top_coeff rho alpha c)"
    using subset by (simp add: integral_restrict_Int inf.absorb1)
  finally show ?thesis .
qed

lemma localized_chart_integral_eq_form:
  assumes c: "c \<in> oriented_charts"
    and d: "d \<in> oriented_charts"
    and compatible: "top_coeff_compatible alpha"
    and localized: "\<And>p. p \<in> top_form_support alpha \<Longrightarrow>
      rho p \<noteq> 0 \<Longrightarrow> p \<in> domain c \<inter> domain d"
    and integrable: "weight_top_coeff rho alpha d
      absolutely_integrable_on chart_overlap d c"
  shows "integral (codomain c) (weight_top_coeff rho alpha c) =
    integral (codomain d) (weight_top_coeff rho alpha d)"
proof -
  have loc_c: "\<And>p. p \<in> top_form_support alpha \<Longrightarrow>
      rho p \<noteq> 0 \<Longrightarrow> p \<in> domain d"
    using localized by auto
  have loc_d: "\<And>p. p \<in> top_form_support alpha \<Longrightarrow>
      rho p \<noteq> 0 \<Longrightarrow> p \<in> domain c"
    using localized by auto
  have "integral (codomain c) (weight_top_coeff rho alpha c) =
    integral (chart_overlap c d) (weight_top_coeff rho alpha c)"
    by (rule chart_integral_localized_form
      [OF c compatible loc_c])
  also have "\<dots> =
    integral (chart_overlap d c) (weight_top_coeff rho alpha d)"
    by (rule weighted_overlap_integral[OF c d compatible integrable])
  also have "\<dots> =
    integral (codomain d) (weight_top_coeff rho alpha d)"
    by (rule chart_integral_localized_form
      [OF d compatible loc_d, symmetric])
  finally show ?thesis .
qed

lemma weight_top_coeff_partition:
  assumes c: "c \<in> oriented_charts"
    and x: "x \<in> codomain c"
    and compatible: "top_coeff_compatible alpha"
    and unity: "\<And>p. p \<in> top_form_support alpha \<Longrightarrow>
      (\<Sum>j\<in>J. psi j p) = 1"
  shows "weight_top_coeff rho alpha c x =
    (\<Sum>j\<in>J.
      weight_top_coeff (\<lambda>p. rho p * psi j p) alpha c x)"
proof -
  let ?p = "inv_chart c x"
  have p: "?p \<in> domain c" and cp: "c ?p = x"
    using x by auto
  show ?thesis
  proof (cases "alpha c x = 0")
    case True
    then show ?thesis
      by (simp add: weight_top_coeff_def)
  next
    case False
    have "?p \<in> top_form_support alpha"
      using top_form_support_chart[OF compatible c p] cp False
      by simp
    then have "(\<Sum>j\<in>J. psi j ?p) = 1"
      by (rule unity)
    then show ?thesis
      by (simp add: weight_top_coeff_def
        sum_distrib_left[symmetric] sum_distrib_right[symmetric]
        algebra_simps)
  qed
qed

lemma chart_integral_partition:
  assumes c: "c \<in> oriented_charts"
    and finite: "finite J"
    and compatible: "top_coeff_compatible alpha"
    and unity: "\<And>p. p \<in> top_form_support alpha \<Longrightarrow>
      (\<Sum>j\<in>J. psi j p) = 1"
    and integrable: "\<And>j. j \<in> J \<Longrightarrow>
      weight_top_coeff (\<lambda>p. rho p * psi j p) alpha c
        integrable_on codomain c"
  shows "integral (codomain c) (weight_top_coeff rho alpha c) =
    (\<Sum>j\<in>J. integral (codomain c)
      (weight_top_coeff (\<lambda>p. rho p * psi j p) alpha c))"
proof -
  have "integral (codomain c) (weight_top_coeff rho alpha c) =
    integral (codomain c)
      (\<lambda>x. \<Sum>j\<in>J.
        weight_top_coeff (\<lambda>p. rho p * psi j p) alpha c x)"
    by (rule integral_cong)
       (use weight_top_coeff_partition[OF c _ compatible unity] in auto)
  also have "\<dots> =
    (\<Sum>j\<in>J. integral (codomain c)
      (weight_top_coeff (\<lambda>p. rho p * psi j p) alpha c))"
    by (rule integral_sum[OF finite integrable])
  finally show ?thesis .
qed

definition chart_partition_integral ::
    "(('a, real ^ 'n) chart \<Rightarrow> real ^ 'n \<Rightarrow> real) \<Rightarrow>
      (('a, real ^ 'n) chart \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow>
      ('a, real ^ 'n) chart set \<Rightarrow> real"
  where "chart_partition_integral alpha phi F =
    (\<Sum>c\<in>F. integral (codomain c)
      (weight_top_coeff (phi c) alpha c))"

theorem chart_partition_integral_independent:
  assumes compatible: "top_coeff_compatible alpha"
    and finiteF: "finite F" and finiteG: "finite G"
    and F: "F \<subseteq> oriented_charts"
    and G: "G \<subseteq> oriented_charts"
    and unityF: "\<And>p. p \<in> top_form_support alpha \<Longrightarrow>
      (\<Sum>c\<in>F. phi c p) = 1"
    and unityG: "\<And>p. p \<in> top_form_support alpha \<Longrightarrow>
      (\<Sum>d\<in>G. psi d p) = 1"
    and supportF: "\<And>c p. c \<in> F \<Longrightarrow> p \<in> carrier \<Longrightarrow>
      phi c p \<noteq> 0 \<Longrightarrow> p \<in> domain c"
    and supportG: "\<And>d p. d \<in> G \<Longrightarrow> p \<in> carrier \<Longrightarrow>
      psi d p \<noteq> 0 \<Longrightarrow> p \<in> domain d"
    and integrableF: "\<And>c d. c \<in> F \<Longrightarrow> d \<in> G \<Longrightarrow>
      weight_top_coeff (\<lambda>p. phi c p * psi d p) alpha c
        absolutely_integrable_on codomain c"
    and integrableG: "\<And>c d. c \<in> F \<Longrightarrow> d \<in> G \<Longrightarrow>
      weight_top_coeff (\<lambda>p. phi c p * psi d p) alpha d
        absolutely_integrable_on codomain d"
  shows "chart_partition_integral alpha phi F =
    chart_partition_integral alpha psi G"
proof -
  have local: "integral (codomain c)
      (weight_top_coeff (\<lambda>p. phi c p * psi d p) alpha c) =
    integral (codomain d)
      (weight_top_coeff (\<lambda>p. phi c p * psi d p) alpha d)"
    if c: "c \<in> F" and d: "d \<in> G" for c d
  proof -
    have loc: "\<And>p. p \<in> carrier \<Longrightarrow>
      (\<lambda>p. phi c p * psi d p) p \<noteq> 0 \<Longrightarrow>
      p \<in> domain c \<inter> domain d"
      using supportF[OF c] supportG[OF d] by auto
    have measurable: "chart_overlap d c \<in> sets lebesgue"
      using chart_overlap_open[of d c]
      by (metis borel_open sets_lborel sets_completionI_sets)
    have subset: "chart_overlap d c \<subseteq> codomain d"
      by (auto simp: chart_overlap_def)
    have abs_overlap: "weight_top_coeff
        (\<lambda>p. phi c p * psi d p) alpha d
        absolutely_integrable_on chart_overlap d c"
      using set_integrable_subset[OF
        integrableG[OF c d] measurable subset] .
    show ?thesis
      by (rule localized_chart_integral_eq
        [OF subsetD[OF F c] subsetD[OF G d]
          compatible loc abs_overlap])
  qed
  have intF: "weight_top_coeff
      (\<lambda>p. phi c p * psi d p) alpha c
      integrable_on codomain c"
    if "c \<in> F" "d \<in> G" for c d
    using integrableF[OF that]
    by (simp add: absolutely_integrable_on_def)
  have intG: "weight_top_coeff
      (\<lambda>p. psi d p * phi c p) alpha d
      integrable_on codomain d"
    if "c \<in> F" "d \<in> G" for c d
  proof -
    have eq: "weight_top_coeff
        (\<lambda>p. psi d p * phi c p) alpha d =
      weight_top_coeff
        (\<lambda>p. phi c p * psi d p) alpha d"
      by (simp add: weight_top_coeff_def mult.commute)
    show ?thesis
      unfolding eq
      using integrableG[OF that]
      by (simp add: absolutely_integrable_on_def)
  qed
  have left: "chart_partition_integral alpha phi F =
    (\<Sum>c\<in>F. \<Sum>d\<in>G. integral (codomain c)
      (weight_top_coeff (\<lambda>p. phi c p * psi d p) alpha c))"
    unfolding chart_partition_integral_def
    by (rule sum.cong[OF refl])
       (use F finiteG compatible unityG intF in
        \<open>auto intro: chart_integral_partition\<close>)
  have right: "chart_partition_integral alpha psi G =
    (\<Sum>d\<in>G. \<Sum>c\<in>F. integral (codomain d)
      (weight_top_coeff (\<lambda>p. phi c p * psi d p) alpha d))"
  proof -
    have "chart_partition_integral alpha psi G =
      (\<Sum>d\<in>G. \<Sum>c\<in>F. integral (codomain d)
        (weight_top_coeff (\<lambda>p. psi d p * phi c p) alpha d))"
      unfolding chart_partition_integral_def
      by (rule sum.cong[OF refl])
         (use G finiteF compatible unityF intG in
          \<open>auto intro: chart_integral_partition\<close>)
    also have "\<dots> =
      (\<Sum>d\<in>G. \<Sum>c\<in>F. integral (codomain d)
        (weight_top_coeff (\<lambda>p. phi c p * psi d p) alpha d))"
      by (simp add: weight_top_coeff_def mult.commute)
    finally show ?thesis .
  qed
  have "(\<Sum>c\<in>F. \<Sum>d\<in>G. integral (codomain c)
      (weight_top_coeff (\<lambda>p. phi c p * psi d p) alpha c)) =
    (\<Sum>c\<in>F. \<Sum>d\<in>G. integral (codomain d)
      (weight_top_coeff (\<lambda>p. phi c p * psi d p) alpha d))"
    by (rule sum.cong[OF refl], rule sum.cong[OF refl])
       (use local in auto)
  also have "\<dots> =
    (\<Sum>d\<in>G. \<Sum>c\<in>F. integral (codomain d)
      (weight_top_coeff (\<lambda>p. phi c p * psi d p) alpha d))"
    by (rule sum.swap)
  finally show ?thesis
    using left right by simp
qed

theorem chart_partition_integral_independent_smooth:
  assumes compatible: "top_coeff_compatible alpha"
    and compact: "compact K"
    and Kcarrier: "K \<subseteq> carrier"
    and support: "top_form_support alpha \<subseteq> K"
    and coeff_cont: "\<And>c. c \<in> oriented_charts \<Longrightarrow>
      continuous_on (codomain c) (alpha c)"
    and finiteF: "finite F" and finiteG: "finite G"
    and F: "F \<subseteq> oriented_charts"
    and G: "G \<subseteq> oriented_charts"
    and unityF: "\<And>p. p \<in> top_form_support alpha \<Longrightarrow>
      (\<Sum>c\<in>F. phi c p) = 1"
    and unityG: "\<And>p. p \<in> top_form_support alpha \<Longrightarrow>
      (\<Sum>d\<in>G. psi d p) = 1"
    and diffF: "\<And>c. c \<in> F \<Longrightarrow> diff_fun k charts (phi c)"
    and diffG: "\<And>d. d \<in> G \<Longrightarrow> diff_fun k charts (psi d)"
    and locF: "\<And>c. c \<in> F \<Longrightarrow>
      csupport_on carrier (phi c) \<inter> carrier \<subseteq> domain c"
    and locG: "\<And>d. d \<in> G \<Longrightarrow>
      csupport_on carrier (psi d) \<inter> carrier \<subseteq> domain d"
  shows "chart_partition_integral alpha phi F =
    chart_partition_integral alpha psi G"
proof (rule chart_partition_integral_independent
    [OF compatible finiteF finiteG F G unityF unityG])
  show "\<And>c p. c \<in> F \<Longrightarrow> p \<in> carrier \<Longrightarrow>
      phi c p \<noteq> 0 \<Longrightarrow> p \<in> domain c"
    using locF
    by (auto simp: csupport_on_def support_on_def
      intro: in_closureI)
  show "\<And>d p. d \<in> G \<Longrightarrow> p \<in> carrier \<Longrightarrow>
      psi d p \<noteq> 0 \<Longrightarrow> p \<in> domain d"
    using locG
    by (auto simp: csupport_on_def support_on_def
      intro: in_closureI)
  fix c d
  assume c: "c \<in> F" and d: "d \<in> G"
  have diff: "diff_fun k charts
      (\<lambda>p. phi c p * psi d p)"
    using diff_fun_times[OF diffF[OF c] diffG[OF d]]
    by (simp add: times_fun_def)
  have loc_c: "K \<inter> csupport_on carrier
      (\<lambda>p. phi c p * psi d p) \<subseteq> domain c"
    using csupport_on_mono[of carrier
      "\<lambda>p. phi c p * psi d p" "phi c"] locF[OF c] Kcarrier
    by auto
  have loc_d: "K \<inter> csupport_on carrier
      (\<lambda>p. phi c p * psi d p) \<subseteq> domain d"
    using csupport_on_mono[of carrier
      "\<lambda>p. phi c p * psi d p" "psi d"] locG[OF d] Kcarrier
    by auto
  show "weight_top_coeff (\<lambda>p. phi c p * psi d p) alpha c
      absolutely_integrable_on codomain c"
    by (rule chart_weight_absolutely_integrable
      [OF subsetD[OF F c] compatible compact Kcarrier support
        coeff_cont[OF subsetD[OF F c]] diff loc_c])
  show "weight_top_coeff (\<lambda>p. phi c p * psi d p) alpha d
      absolutely_integrable_on codomain d"
    by (rule chart_weight_absolutely_integrable
      [OF subsetD[OF G d] compatible compact Kcarrier support
        coeff_cont[OF subsetD[OF G d]] diff loc_d])
qed

lemma oriented_compact_partition:
  assumes compact: "compact K" and Kcarrier: "K \<subseteq> carrier"
  shows "\<exists>(phi::(('a, real ^ 'n) chart \<Rightarrow> 'a \<Rightarrow> real)) F.
    finite F \<and> F \<subseteq> oriented_charts \<and>
    (\<forall>x\<in>K. (\<Sum>c\<in>F. phi c x) = 1) \<and>
    (\<forall>c\<in>F. diff_fun k charts (phi c)) \<and>
    (\<forall>c\<in>F.
      csupport_on carrier (phi c) \<inter> carrier \<subseteq> domain c)"
  by (rule compact_partition_of_unityE
    [OF oriented_cover _ compact Kcarrier]) auto

lemma oriented_partition_for_support:
  assumes compact: "compact K"
    and Kcarrier: "K \<subseteq> carrier"
    and support: "top_form_support alpha \<subseteq> K"
  shows "\<exists>(phi::(('a, real ^ 'n) chart \<Rightarrow> 'a \<Rightarrow> real)) F.
    finite F \<and> F \<subseteq> oriented_charts \<and>
    (\<forall>p\<in>top_form_support alpha.
      (\<Sum>c\<in>F. phi c p) = 1) \<and>
    (\<forall>c\<in>F. diff_fun k charts (phi c)) \<and>
    (\<forall>c\<in>F. \<forall>p\<in>carrier.
      phi c p \<noteq> 0 \<longrightarrow> p \<in> domain c)"
proof -
  obtain phi :: "('a, real ^ 'n) chart \<Rightarrow> 'a \<Rightarrow> real"
    and F where
    finite: "finite F" and F: "F \<subseteq> oriented_charts"
    and unity: "\<forall>p\<in>K. (\<Sum>c\<in>F. phi c p) = 1"
    and diff: "\<forall>c\<in>F. diff_fun k charts (phi c)"
    and csupport: "\<forall>c\<in>F.
      csupport_on carrier (phi c) \<inter> carrier \<subseteq> domain c"
    using oriented_compact_partition[OF compact Kcarrier] by blast
  have loc: "\<forall>c\<in>F. \<forall>p\<in>carrier.
      phi c p \<noteq> 0 \<longrightarrow> p \<in> domain c"
  proof (intro ballI impI)
    fix c p
    assume c: "c \<in> F" and p: "p \<in> carrier"
      and nz: "phi c p \<noteq> 0"
    have "p \<in> support_on carrier (phi c)"
      using p nz by (simp add: support_on_def)
    then have "p \<in> csupport_on carrier (phi c)"
      unfolding csupport_on_def
      using closure_subset by blast
    with csupport c p show "p \<in> domain c" by blast
  qed
  show ?thesis
    apply (rule exI[where x=phi])
    apply (rule exI[where x=F])
    using finite F unity diff loc support by blast
qed

definition admissible_top_partition ::
    "(('a, real ^ 'n) chart \<Rightarrow> real ^ 'n \<Rightarrow> real) \<Rightarrow>
      (('a, real ^ 'n) chart \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow>
      ('a, real ^ 'n) chart set \<Rightarrow> bool"
  where "admissible_top_partition alpha phi F \<longleftrightarrow>
    finite F \<and> F \<subseteq> oriented_charts \<and>
    (\<forall>p\<in>top_form_support alpha.
      (\<Sum>c\<in>F. phi c p) = 1) \<and>
    (\<forall>c\<in>F. diff_fun k charts (phi c)) \<and>
    (\<forall>c\<in>F.
      csupport_on carrier (phi c) \<inter> carrier \<subseteq> domain c)"

lemma admissible_top_partition_exists:
  assumes compact: "compact K"
    and Kcarrier: "K \<subseteq> carrier"
    and support: "top_form_support alpha \<subseteq> K"
  shows "\<exists>phi F. admissible_top_partition alpha phi F"
proof -
  obtain phi :: "('a, real ^ 'n) chart \<Rightarrow> 'a \<Rightarrow> real"
    and F where
    finite: "finite F" and F: "F \<subseteq> oriented_charts"
    and unity: "\<forall>p\<in>K. (\<Sum>c\<in>F. phi c p) = 1"
    and diff: "\<forall>c\<in>F. diff_fun k charts (phi c)"
    and loc: "\<forall>c\<in>F.
      csupport_on carrier (phi c) \<inter> carrier \<subseteq> domain c"
    using oriented_compact_partition[OF compact Kcarrier] by blast
  have "admissible_top_partition alpha phi F"
    using finite F unity diff loc support
    by (auto simp: admissible_top_partition_def)
  then show ?thesis by blast
qed

lemma admissible_top_partition_integral_unique:
  assumes compatible: "top_coeff_compatible alpha"
    and compact: "compact K"
    and Kcarrier: "K \<subseteq> carrier"
    and support: "top_form_support alpha \<subseteq> K"
    and coeff_cont: "\<And>c. c \<in> oriented_charts \<Longrightarrow>
      continuous_on (codomain c) (alpha c)"
    and phi: "admissible_top_partition alpha phi F"
    and psi: "admissible_top_partition alpha psi G"
  shows "chart_partition_integral alpha phi F =
    chart_partition_integral alpha psi G"
  using phi psi
  unfolding admissible_top_partition_def
  by (intro chart_partition_integral_independent_smooth
    [OF compatible compact Kcarrier support coeff_cont])
     auto

definition integral_top ::
    "(('a, real ^ 'n) chart \<Rightarrow> real ^ 'n \<Rightarrow> real) \<Rightarrow> real"
  where "integral_top alpha =
    (SOME I. \<exists>phi F.
      admissible_top_partition alpha phi F \<and>
      I = chart_partition_integral alpha phi F)"

lemma top_form_support_cong:
  assumes eq: "\<And>c x. c \<in> oriented_charts \<Longrightarrow>
    x \<in> codomain c \<Longrightarrow> alpha c x = beta c x"
  shows "top_form_support alpha = top_form_support beta"
proof -
  have coeff: "alpha c (c p) = beta c (c p)"
    if "c \<in> oriented_charts" "p \<in> domain c" for c p
    by (rule eq[OF that(1) chart_in_codomain[OF that(2)]])
  show ?thesis
    using coeff by (auto simp: top_form_support_def)
qed

lemma chart_partition_integral_cong:
  assumes eq: "\<And>c x. c \<in> oriented_charts \<Longrightarrow>
    x \<in> codomain c \<Longrightarrow> alpha c x = beta c x"
    and F: "F \<subseteq> oriented_charts"
  shows "chart_partition_integral alpha phi F =
    chart_partition_integral beta phi F"
  unfolding chart_partition_integral_def
proof (rule sum.cong[OF refl])
  fix c
  assume c: "c \<in> F"
  show "integral (codomain c)
      (weight_top_coeff (phi c) alpha c) =
    integral (codomain c)
      (weight_top_coeff (phi c) beta c)"
    by (rule integral_cong)
       (use eq[OF subsetD[OF F c]] in
        \<open>auto simp: weight_top_coeff_def\<close>)
qed

theorem integral_top_ext:
  assumes eq: "\<And>c x. c \<in> oriented_charts \<Longrightarrow>
    x \<in> codomain c \<Longrightarrow> alpha c x = beta c x"
  shows "integral_top alpha = integral_top beta"
proof -
  have support: "top_form_support alpha =
    top_form_support beta"
    by (rule top_form_support_cong[OF eq])
  have adm: "admissible_top_partition alpha phi F =
    admissible_top_partition beta phi F" for phi F
    by (simp add: admissible_top_partition_def support)
  have term_eq: "admissible_top_partition alpha phi F \<Longrightarrow>
    chart_partition_integral alpha phi F =
      chart_partition_integral beta phi F" for phi F
    using chart_partition_integral_cong[OF eq]
    by (auto simp: admissible_top_partition_def)
  have P: "(\<exists>phi F. admissible_top_partition alpha phi F \<and>
      I = chart_partition_integral alpha phi F) =
    (\<exists>phi F. admissible_top_partition beta phi F \<and>
      I = chart_partition_integral beta phi F)" for I
  proof
    assume "\<exists>phi F. admissible_top_partition alpha phi F \<and>
      I = chart_partition_integral alpha phi F"
    then obtain phi F where a: "admissible_top_partition alpha phi F"
      and i: "I = chart_partition_integral alpha phi F"
      by blast
    have b: "admissible_top_partition beta phi F"
      using a adm[of phi F] by simp
    have "I = chart_partition_integral beta phi F"
      using i term_eq[OF a] by simp
    with b show "\<exists>phi F. admissible_top_partition beta phi F \<and>
      I = chart_partition_integral beta phi F"
      by blast
  next
    assume "\<exists>phi F. admissible_top_partition beta phi F \<and>
      I = chart_partition_integral beta phi F"
    then obtain phi F where b: "admissible_top_partition beta phi F"
      and i: "I = chart_partition_integral beta phi F"
      by blast
    have a: "admissible_top_partition alpha phi F"
      using b adm[of phi F] by simp
    have "I = chart_partition_integral alpha phi F"
      using i term_eq[OF a] by simp
    with a show "\<exists>phi F. admissible_top_partition alpha phi F \<and>
      I = chart_partition_integral alpha phi F"
      by blast
  qed
  show ?thesis
    unfolding integral_top_def using P by simp
qed

theorem integral_top_eq_partition:
  assumes compatible: "top_coeff_compatible alpha"
    and compact: "compact K"
    and Kcarrier: "K \<subseteq> carrier"
    and support: "top_form_support alpha \<subseteq> K"
    and coeff_cont: "\<And>c. c \<in> oriented_charts \<Longrightarrow>
      continuous_on (codomain c) (alpha c)"
    and partition: "admissible_top_partition alpha phi F"
  shows "integral_top alpha =
    chart_partition_integral alpha phi F"
proof -
  let ?P = "\<lambda>I. \<exists>phi F.
      admissible_top_partition alpha phi F \<and>
      I = chart_partition_integral alpha phi F"
  have "\<exists>I. ?P I"
    using partition by blast
  then have "?P (SOME I. ?P I)"
    by (rule someI_ex)
  then obtain psi G where psi:
      "admissible_top_partition alpha psi G"
    and eq: "(SOME I. ?P I) =
      chart_partition_integral alpha psi G"
    by blast
  show ?thesis
    unfolding integral_top_def
    using eq admissible_top_partition_integral_unique
      [OF compatible compact Kcarrier support coeff_cont
        psi partition]
    by simp
qed

lemma top_coeff_compatible_add:
  assumes alpha: "top_coeff_compatible alpha"
    and beta: "top_coeff_compatible beta"
  shows "top_coeff_compatible
    (\<lambda>c x. alpha c x + beta c x)"
  using alpha beta
  by (auto simp: top_coeff_compatible_def pull_top_def
    algebra_simps)

lemma top_form_support_add:
  "top_form_support (\<lambda>c x. alpha c x + beta c x)
    \<subseteq> top_form_support alpha \<union> top_form_support beta"
  by (auto simp: top_form_support_def)

lemma chart_partition_integral_add:
  assumes finite: "finite F"
    and F: "F \<subseteq> oriented_charts"
    and compatible_alpha: "top_coeff_compatible alpha"
    and compatible_beta: "top_coeff_compatible beta"
    and compact: "compact K"
    and Kcarrier: "K \<subseteq> carrier"
    and support_alpha: "top_form_support alpha \<subseteq> K"
    and support_beta: "top_form_support beta \<subseteq> K"
    and cont_alpha: "\<And>c. c \<in> oriented_charts \<Longrightarrow>
      continuous_on (codomain c) (alpha c)"
    and cont_beta: "\<And>c. c \<in> oriented_charts \<Longrightarrow>
      continuous_on (codomain c) (beta c)"
    and diff: "\<And>c. c \<in> F \<Longrightarrow> diff_fun k charts (phi c)"
    and loc: "\<And>c. c \<in> F \<Longrightarrow>
      csupport_on carrier (phi c) \<inter> carrier \<subseteq> domain c"
  shows "chart_partition_integral
      (\<lambda>c x. alpha c x + beta c x) phi F =
    chart_partition_integral alpha phi F +
      chart_partition_integral beta phi F"
proof -
  have eq: "integral (codomain c)
      (weight_top_coeff (phi c)
        (\<lambda>c x. alpha c x + beta c x) c) =
    integral (codomain c) (weight_top_coeff (phi c) alpha c) +
      integral (codomain c) (weight_top_coeff (phi c) beta c)"
    if c: "c \<in> F" for c
  proof -
    have locK: "K \<inter> csupport_on carrier (phi c)
        \<subseteq> domain c"
      using loc[OF c] Kcarrier by auto
    have ia: "weight_top_coeff (phi c) alpha c
        integrable_on codomain c"
      using chart_weight_absolutely_integrable
        [OF subsetD[OF F c] compatible_alpha compact Kcarrier
          support_alpha cont_alpha[OF subsetD[OF F c]]
          diff[OF c] locK]
      by (simp add: absolutely_integrable_on_def)
    have ib: "weight_top_coeff (phi c) beta c
        integrable_on codomain c"
      using chart_weight_absolutely_integrable
        [OF subsetD[OF F c] compatible_beta compact Kcarrier
          support_beta cont_beta[OF subsetD[OF F c]]
          diff[OF c] locK]
      by (simp add: absolutely_integrable_on_def)
    have coeff: "weight_top_coeff (phi c)
        (\<lambda>c x. alpha c x + beta c x) c =
      (\<lambda>x. weight_top_coeff (phi c) alpha c x +
        weight_top_coeff (phi c) beta c x)"
      by (rule ext)
         (simp add: weight_top_coeff_def algebra_simps)
    show ?thesis
      unfolding coeff
      by (rule integral_add[OF ia ib])
  qed
  show ?thesis
    unfolding chart_partition_integral_def
    using eq
    by (simp add: sum.distrib finite)
qed

theorem integral_top_add:
  assumes compatible_alpha: "top_coeff_compatible alpha"
    and compatible_beta: "top_coeff_compatible beta"
    and compactA: "compact KA"
    and compactB: "compact KB"
    and KA: "KA \<subseteq> carrier"
    and KB: "KB \<subseteq> carrier"
    and supportA: "top_form_support alpha \<subseteq> KA"
    and supportB: "top_form_support beta \<subseteq> KB"
    and contA: "\<And>c. c \<in> oriented_charts \<Longrightarrow>
      continuous_on (codomain c) (alpha c)"
    and contB: "\<And>c. c \<in> oriented_charts \<Longrightarrow>
      continuous_on (codomain c) (beta c)"
  shows "integral_top
      (\<lambda>c x. alpha c x + beta c x) =
    integral_top alpha + integral_top beta"
proof -
  let ?K = "KA \<union> KB"
  have compact: "compact ?K"
    by (rule compact_Un[OF compactA compactB])
  have Kcarrier: "?K \<subseteq> carrier"
    using KA KB by auto
  have support_a: "top_form_support alpha \<subseteq> ?K"
    using supportA by auto
  have support_b: "top_form_support beta \<subseteq> ?K"
    using supportB by auto
  have support_sum: "top_form_support
      (\<lambda>c x. alpha c x + beta c x) \<subseteq> ?K"
  proof -
    have "top_form_support
        (\<lambda>c x. alpha c x + beta c x) \<subseteq>
      top_form_support alpha \<union> top_form_support beta"
      by (rule top_form_support_add)
    with support_a support_b show ?thesis by blast
  qed
  obtain phi :: "('a, real ^ 'n) chart \<Rightarrow> 'a \<Rightarrow> real"
    and F where
    finite: "finite F" and F: "F \<subseteq> oriented_charts"
    and unity: "\<forall>p\<in>?K. (\<Sum>c\<in>F. phi c p) = 1"
    and diff: "\<forall>c\<in>F. diff_fun k charts (phi c)"
    and loc: "\<forall>c\<in>F.
      csupport_on carrier (phi c) \<inter> carrier \<subseteq> domain c"
    using oriented_compact_partition[OF compact Kcarrier] by blast
  have part_a: "admissible_top_partition alpha phi F"
    using finite F unity diff loc support_a
    by (auto simp: admissible_top_partition_def)
  have part_b: "admissible_top_partition beta phi F"
    using finite F unity diff loc support_b
    by (auto simp: admissible_top_partition_def)
  have part_sum: "admissible_top_partition
      (\<lambda>c x. alpha c x + beta c x) phi F"
    using finite F unity diff loc support_sum
    by (auto simp: admissible_top_partition_def)
  have compatible_sum: "top_coeff_compatible
      (\<lambda>c x. alpha c x + beta c x)"
    by (rule top_coeff_compatible_add
      [OF compatible_alpha compatible_beta])
  have cont_sum: "continuous_on (codomain c)
      (\<lambda>x. alpha c x + beta c x)"
    if "c \<in> oriented_charts" for c
    using contA[OF that] contB[OF that]
    by (auto intro!: continuous_intros)
  have i_sum: "integral_top
      (\<lambda>c x. alpha c x + beta c x) =
    chart_partition_integral
      (\<lambda>c x. alpha c x + beta c x) phi F"
    by (rule integral_top_eq_partition
      [OF compatible_sum compact Kcarrier support_sum
        cont_sum part_sum])
  have ia: "integral_top alpha =
      chart_partition_integral alpha phi F"
    by (rule integral_top_eq_partition
      [OF compatible_alpha compact Kcarrier support_a
        contA part_a])
  have ib: "integral_top beta =
      chart_partition_integral beta phi F"
    by (rule integral_top_eq_partition
      [OF compatible_beta compact Kcarrier support_b
        contB part_b])
  show ?thesis
    using i_sum ia ib
      chart_partition_integral_add
        [OF finite F compatible_alpha compatible_beta
          compact Kcarrier support_a support_b
          contA contB]
      diff loc
    by auto
qed

theorem integral_top_local_chart:
  assumes c: "c \<in> oriented_charts"
    and compatible: "top_coeff_compatible alpha"
    and compact: "compact K"
    and Kcarrier: "K \<subseteq> carrier"
    and Kdomain: "K \<subseteq> domain c"
    and support: "top_form_support alpha \<subseteq> K"
    and coeff_cont: "\<And>d. d \<in> oriented_charts \<Longrightarrow>
      continuous_on (codomain d) (alpha d)"
  shows "integral_top alpha = integral (codomain c) (alpha c)"
proof -
  obtain phi F where partition:
      "admissible_top_partition alpha phi F"
    using admissible_top_partition_exists
      [OF compact Kcarrier support] by blast
  have finite: "finite F"
    and F: "F \<subseteq> oriented_charts"
    and unity: "\<And>p. p \<in> top_form_support alpha \<Longrightarrow>
      (\<Sum>d\<in>F. phi d p) = 1"
    and diff: "\<And>d. d \<in> F \<Longrightarrow>
      diff_fun k charts (phi d)"
    and loc: "\<And>d. d \<in> F \<Longrightarrow>
      csupport_on carrier (phi d) \<inter> carrier \<subseteq> domain d"
    using partition by (auto simp: admissible_top_partition_def)
  have int_c: "weight_top_coeff (phi d) alpha c
      absolutely_integrable_on codomain c"
    if d: "d \<in> F" for d
  proof -
    have locK: "K \<inter> csupport_on carrier (phi d)
        \<subseteq> domain c"
      using Kdomain by auto
    show ?thesis
      by (rule chart_weight_absolutely_integrable
        [OF c compatible compact Kcarrier support
          coeff_cont[OF c] diff[OF d] locK])
  qed
  have local: "integral (codomain d)
      (weight_top_coeff (phi d) alpha d) =
    integral (codomain c)
      (weight_top_coeff (phi d) alpha c)"
    if d: "d \<in> F" for d
  proof -
    have localized: "\<And>p. p \<in> top_form_support alpha \<Longrightarrow>
        phi d p \<noteq> 0 \<Longrightarrow> p \<in> domain d \<inter> domain c"
    proof -
      fix p
      assume ps: "p \<in> top_form_support alpha"
        and nz: "phi d p \<noteq> 0"
      have pc: "p \<in> carrier"
        using ps by (auto simp: top_form_support_def)
      have "p \<in> csupport_on carrier (phi d)"
        using pc nz by (auto simp: csupport_on_def
          support_on_def intro: in_closureI)
      then have "p \<in> domain d"
        using pc loc[OF d] by blast
      moreover have "p \<in> domain c"
        using ps support Kdomain by auto
      ultimately show "p \<in> domain d \<inter> domain c"
        by auto
    qed
    have measurable: "chart_overlap c d \<in> sets lebesgue"
      using chart_overlap_open[of c d]
      by (metis borel_open sets_lborel sets_completionI_sets)
    have subset: "chart_overlap c d \<subseteq> codomain c"
      by (auto simp: chart_overlap_def)
    have int_overlap: "weight_top_coeff (phi d) alpha c
        absolutely_integrable_on chart_overlap c d"
      by (rule set_integrable_subset
        [OF int_c[OF d] measurable subset])
    show ?thesis
      by (rule localized_chart_integral_eq_form
        [OF subsetD[OF F d] c compatible
          localized int_overlap])
  qed
  have expansion: "integral (codomain c) (alpha c) =
    (\<Sum>d\<in>F. integral (codomain c)
      (weight_top_coeff (phi d) alpha c))"
  proof -
    have int: "weight_top_coeff
        (\<lambda>p. (1::real) * phi d p) alpha c
        integrable_on codomain c"
      if d: "d \<in> F" for d
      using int_c[OF d]
      by (simp add: absolutely_integrable_on_def)
    have "integral (codomain c)
        (weight_top_coeff (\<lambda>_. 1) alpha c) =
      (\<Sum>d\<in>F. integral (codomain c)
        (weight_top_coeff
          (\<lambda>p. (1::real) * phi d p) alpha c))"
      by (rule chart_integral_partition
        [OF c finite compatible unity int])
    moreover have "weight_top_coeff (\<lambda>_. 1) alpha c =
      alpha c"
      by (rule ext) (simp add: weight_top_coeff_def)
    then show ?thesis
      using calculation by (simp add: weight_top_coeff_def)
  qed
  have "integral_top alpha =
    chart_partition_integral alpha phi F"
    by (rule integral_top_eq_partition
      [OF compatible compact Kcarrier support coeff_cont partition])
  also have "\<dots> =
    (\<Sum>d\<in>F. integral (codomain c)
      (weight_top_coeff (phi d) alpha c))"
    unfolding chart_partition_integral_def
    by (rule sum.cong[OF refl]) (use local in auto)
  also have "\<dots> = integral (codomain c) (alpha c)"
    using expansion by simp
  finally show ?thesis .
qed

lemma top_coeff_compatible_scale:
  assumes compatible: "top_coeff_compatible alpha"
  shows "top_coeff_compatible
    (\<lambda>c x. r * alpha c x)"
  using compatible
  by (auto simp: top_coeff_compatible_def pull_top_def
    algebra_simps)

lemma top_form_support_scale:
  "top_form_support (\<lambda>c x. r * alpha c x)
    \<subseteq> top_form_support alpha"
  by (auto simp: top_form_support_def)

lemma chart_partition_integral_scale:
  assumes finite: "finite F"
  shows "chart_partition_integral
      (\<lambda>c x. r * alpha c x) phi F =
    r * chart_partition_integral alpha phi F"
proof -
  have eq: "weight_top_coeff (phi c)
      (\<lambda>c x. r * alpha c x) c =
    (\<lambda>x. r * weight_top_coeff (phi c) alpha c x)"
    for c
    by (rule ext)
       (simp add: weight_top_coeff_def algebra_simps)
  show ?thesis
    unfolding chart_partition_integral_def
    by (simp add: eq sum_distrib_left finite)
qed

theorem integral_top_scale:
  assumes compatible: "top_coeff_compatible alpha"
    and compact: "compact K"
    and Kcarrier: "K \<subseteq> carrier"
    and support: "top_form_support alpha \<subseteq> K"
    and coeff_cont: "\<And>c. c \<in> oriented_charts \<Longrightarrow>
      continuous_on (codomain c) (alpha c)"
  shows "integral_top (\<lambda>c x. r * alpha c x) =
    r * integral_top alpha"
proof -
  obtain phi F where partition:
      "admissible_top_partition alpha phi F"
    using admissible_top_partition_exists
      [OF compact Kcarrier support] by blast
  have supp_scale: "top_form_support
      (\<lambda>c x. r * alpha c x) \<subseteq> K"
  proof -
    have "top_form_support
        (\<lambda>c x. r * alpha c x) \<subseteq>
      top_form_support alpha"
      by (rule top_form_support_scale)
    with support show ?thesis by auto
  qed
  have part_scale: "admissible_top_partition
      (\<lambda>c x. r * alpha c x) phi F"
    using partition top_form_support_scale
    by (auto simp: admissible_top_partition_def
      top_form_support_def)
  have cont_scale: "continuous_on (codomain c)
      (\<lambda>x. r * alpha c x)"
    if "c \<in> oriented_charts" for c
    using coeff_cont[OF that]
    by (auto intro!: continuous_intros)
  have i_scale: "integral_top
      (\<lambda>c x. r * alpha c x) =
    chart_partition_integral
      (\<lambda>c x. r * alpha c x) phi F"
    by (rule integral_top_eq_partition
      [OF top_coeff_compatible_scale[OF compatible]
        compact Kcarrier supp_scale cont_scale part_scale])
  have i_alpha: "integral_top alpha =
      chart_partition_integral alpha phi F"
    by (rule integral_top_eq_partition
      [OF compatible compact Kcarrier support
        coeff_cont partition])
  have finite: "finite F"
    using partition by (simp add: admissible_top_partition_def)
  show ?thesis
    using i_scale i_alpha chart_partition_integral_scale[OF finite]
    by simp
qed

lemma integral_top_zero:
  "integral_top (\<lambda>c x. 0) = 0"
proof -
  have compatible: "top_coeff_compatible (\<lambda>c x. 0)"
    by (simp add: top_coeff_compatible_def pull_top_def)
  have support: "top_form_support (\<lambda>c x. 0) = {}"
    by (simp add: top_form_support_def)
  have partition: "admissible_top_partition
      (\<lambda>c x. 0) (\<lambda>c p. 0) {}"
    by (simp add: admissible_top_partition_def support)
  have "integral_top (\<lambda>c x. 0) =
    chart_partition_integral
      (\<lambda>c x. 0) (\<lambda>c p. 0) {}"
    by (rule integral_top_eq_partition
      [where K="{}", OF compatible])
       (use support partition in auto)
  then show ?thesis
    by (simp add: chart_partition_integral_def)
qed

lemma linear_top_functional_sum:
  fixes L :: "(('i \<Rightarrow> 'e \<Rightarrow> real) \<Rightarrow> real)"
  assumes add: "\<And>alpha beta.
      L (\<lambda>c x. alpha c x + beta c x) =
        L alpha + L beta"
    and zero: "L (\<lambda>c x. 0) = 0"
    and finite: "finite F"
  shows "L (\<lambda>c x. \<Sum>i\<in>F. beta i c x) =
    (\<Sum>i\<in>F. L (beta i))"
  using finite
proof (induction F)
  case empty
  then show ?case using zero by simp
next
  case (insert i F)
  have eq: "(\<lambda>c x. \<Sum>j\<in>insert i F. beta j c x) =
    (\<lambda>c x. beta i c x + (\<Sum>j\<in>F. beta j c x))"
    by (rule ext)+ (simp add: insert.hyps)
  show ?case
    using insert.hyps insert.IH
    by (simp add: eq add)
qed

theorem integral_top_unique:
  fixes L :: "((('a, real ^ 'n) chart \<Rightarrow>
      real ^ 'n \<Rightarrow> real) \<Rightarrow> real)"
  assumes ext: "\<And>alpha beta.
      (\<And>c x. c \<in> oriented_charts \<Longrightarrow>
        x \<in> codomain c \<Longrightarrow>
        alpha c x = beta c x) \<Longrightarrow>
      L alpha = L beta"
    and add: "\<And>alpha beta.
      L (\<lambda>c x. alpha c x + beta c x) =
        L alpha + L beta"
    and zero: "L (\<lambda>c x. 0) = 0"
    and local: "\<And>beta c C.
      c \<in> oriented_charts \<Longrightarrow>
      top_coeff_compatible beta \<Longrightarrow>
      compact C \<Longrightarrow> C \<subseteq> carrier \<Longrightarrow>
      C \<subseteq> domain c \<Longrightarrow>
      top_form_support beta \<subseteq> C \<Longrightarrow>
      (\<And>d. d \<in> oriented_charts \<Longrightarrow>
        continuous_on (codomain d) (beta d)) \<Longrightarrow>
      L beta = integral (codomain c) (beta c)"
    and compatible: "top_coeff_compatible alpha"
    and compact: "compact K"
    and Kcarrier: "K \<subseteq> carrier"
    and support: "top_form_support alpha \<subseteq> K"
    and coeff_cont: "\<And>c. c \<in> oriented_charts \<Longrightarrow>
      continuous_on (codomain c) (alpha c)"
  shows "L alpha = integral_top alpha"
proof -
  obtain phi F where partition:
      "admissible_top_partition alpha phi F"
    using admissible_top_partition_exists
      [OF compact Kcarrier support] by blast
  have finite: "finite F"
    and F: "F \<subseteq> oriented_charts"
    and unity: "\<And>p. p \<in> top_form_support alpha \<Longrightarrow>
      (\<Sum>c\<in>F. phi c p) = 1"
    and diff: "\<And>c. c \<in> F \<Longrightarrow>
      diff_fun k charts (phi c)"
    and loc: "\<And>c. c \<in> F \<Longrightarrow>
      csupport_on carrier (phi c) \<inter> carrier \<subseteq> domain c"
    using partition by (auto simp: admissible_top_partition_def)
  have alpha_eq: "alpha d x =
    (\<Sum>c\<in>F. weight_top_coeff (phi c) alpha d x)"
    if d: "d \<in> oriented_charts" and x: "x \<in> codomain d"
    for d x
  proof -
    have "weight_top_coeff (\<lambda>_. 1) alpha d x =
      (\<Sum>c\<in>F.
        weight_top_coeff
          (\<lambda>p. (1::real) * phi c p) alpha d x)"
      by (rule weight_top_coeff_partition
        [OF d x compatible unity])
    then show ?thesis
      by (simp add: weight_top_coeff_def)
  qed
  have L_eq: "L alpha =
    L (\<lambda>d x. \<Sum>c\<in>F.
      weight_top_coeff (phi c) alpha d x)"
    by (rule ext) (use alpha_eq in auto)
  have L_sum: "L (\<lambda>d x. \<Sum>c\<in>F.
      weight_top_coeff (phi c) alpha d x) =
    (\<Sum>c\<in>F.
      L (weight_top_coeff (phi c) alpha))"
    by (rule linear_top_functional_sum[OF add zero finite])
  have L_piece: "L (weight_top_coeff (phi c) alpha) =
    integral (codomain c)
      (weight_top_coeff (phi c) alpha c)"
    if c: "c \<in> F" for c
  proof -
    let ?C = "K \<inter> csupport_on carrier (phi c)"
    have compactC: "compact ?C"
      by (rule compact_Int_closed[OF compact]) simp
    have Ccarrier: "?C \<subseteq> carrier"
      using Kcarrier by auto
    have Cdomain: "?C \<subseteq> domain c"
      using Kcarrier loc[OF c] by auto
    have support_piece:
      "top_form_support (weight_top_coeff (phi c) alpha)
        \<subseteq> ?C"
      using top_form_support_weight[OF compatible, of "phi c"]
        support by auto
    have cont_piece: "continuous_on (codomain d)
        (weight_top_coeff (phi c) alpha d)"
      if "d \<in> oriented_charts" for d
      by (rule weight_top_coeff_continuous
        [OF diff[OF c] coeff_cont that])
    show ?thesis
      by (rule local[OF subsetD[OF F c]
        weight_top_coeff_compatible[OF compatible]
        compactC Ccarrier Cdomain support_piece cont_piece])
  qed
  have "L alpha =
    (\<Sum>c\<in>F. integral (codomain c)
      (weight_top_coeff (phi c) alpha c))"
    using L_eq L_sum L_piece by simp
  also have "\<dots> = integral_top alpha"
    using integral_top_eq_partition
      [OF compatible compact Kcarrier support
        coeff_cont partition]
    by (simp add: chart_partition_integral_def)
  finally show ?thesis .
qed

end

end
