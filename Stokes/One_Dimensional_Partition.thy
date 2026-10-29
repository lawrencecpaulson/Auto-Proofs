theory One_Dimensional_Partition
  imports One_Dimensional_Manifold
    "HOL-Analysis.Higher_Differentiability_Multi"
    Smooth_Cutoff
begin

context oriented_C1_halfline_atlas
begin

definition chartwise_C1_scalar ::
    "('a \<Rightarrow> real) \<Rightarrow> bool"
  where "chartwise_C1_scalar rho \<longleftrightarrow>
    (\<forall>j\<in>I. \<forall>x\<in>C j. \<exists>U F.
      Ck_on 1 F U \<and> x \<in> U \<and>
      (\<forall>y\<in>U \<inter> C j.
        F y = rho (from_chart j y)))"

lemma chartwise_C1_scalar_const:
  "chartwise_C1_scalar (\<lambda>_. c)"
  unfolding chartwise_C1_scalar_def
  by (intro ballI
    exI[where x=UNIV]
    exI[where x="\<lambda>_. c"])
     (auto intro: Ck_on_const)

lemma chartwise_C1_scalar_binary:
  fixes h :: "real \<Rightarrow> real \<Rightarrow> real"
  assumes a: "chartwise_C1_scalar a"
    and b: "chartwise_C1_scalar b"
    and closure: "\<And>U
      (F :: real \<Rightarrow> real) G.
      Ck_on 1 F U \<Longrightarrow> Ck_on 1 G U \<Longrightarrow>
      Ck_on 1 (\<lambda>y. h (F y) (G y)) U"
  shows "chartwise_C1_scalar
    (\<lambda>p. h (a p) (b p))"
proof -
  have A: "chartwise_C1_scalar_on I C from_chart a"
    using a by (simp add: chartwise_C1_scalar_def chartwise_C1_scalar_on_def)
  have B: "chartwise_C1_scalar_on I C from_chart b"
    using b by (simp add: chartwise_C1_scalar_def chartwise_C1_scalar_on_def)
  have R: "chartwise_C1_scalar_on I C from_chart
      (\<lambda>p. h (a p) (b p))"
    by (rule chartwise_C1_scalar_on_binary[OF A B closure])
  show ?thesis using R
    by (simp add: chartwise_C1_scalar_def chartwise_C1_scalar_on_def)
qed

lemma chartwise_C1_scalar_add:
  assumes "chartwise_C1_scalar a"
    and "chartwise_C1_scalar b"
  shows "chartwise_C1_scalar (\<lambda>p. a p + b p)"
  by (rule chartwise_C1_scalar_binary
    [OF assms]) (rule Ck_on_add; assumption)

lemma chartwise_C1_scalar_sub:
  assumes "chartwise_C1_scalar a"
    and "chartwise_C1_scalar b"
  shows "chartwise_C1_scalar (\<lambda>p. a p - b p)"
  by (rule chartwise_C1_scalar_binary
    [OF assms]) (rule Ck_on_sub; assumption)

lemma chartwise_C1_scalar_mult:
  assumes "chartwise_C1_scalar a"
    and "chartwise_C1_scalar b"
  shows "chartwise_C1_scalar (\<lambda>p. a p * b p)"
  by (rule chartwise_C1_scalar_binary
    [OF assms]) (rule Ck_on_mult; assumption)

interpretation scalar_partition: scalar_partition_algebra chartwise_C1_scalar
  by unfold_locales
    (auto intro: chartwise_C1_scalar_const chartwise_C1_scalar_sub
      chartwise_C1_scalar_mult)

lemmas finite_C1_partition_from_cutoffs =
  scalar_partition.finite_C1_partition_from_cutoffs

lemmas finite_C1_chart_partition =
  scalar_partition.finite_C1_chart_partition

lemma chartwise_C1_scalar_of_local_cutoff:
  assumes i: "i \<in> I"
    and smooth: "Ck_on 1 g UNIV"
    and rho: "\<And>p. rho p =
      (if p \<in> D i then g (to_chart i p) else 0)"
    and closedL: "closed L"
    and LD: "L \<subseteq> D i"
    and support: "{p\<in>M. rho p \<noteq> 0} \<subseteq> L"
  shows "chartwise_C1_scalar rho"
proof (unfold chartwise_C1_scalar_def, intro ballI)
  fix j x
  assume j: "j \<in> I" and x: "x \<in> C j"
  let ?p = "from_chart j x"
  have pD: "?p \<in> D j"
    using halfline_chart.inverse_image[OF chart[OF j]]
      x by auto
  have pM: "?p \<in> M"
    using domain_subset_carrier[OF j] pD by auto
  show "\<exists>U F. Ck_on 1 F U \<and> x \<in> U \<and>
      (\<forall>y\<in>U \<inter> C j.
        F y = rho (from_chart j y))"
  proof (cases "?p \<in> D i")
    case True
    have xoverlap: "x \<in> overlap j i"
      using x True
      by (simp add: overlap_preimage[OF j])
    obtain U F where U: "open U" "x \<in> U"
      "Ck_on 1 F U"
      "\<And>y. y \<in> U \<inter> overlap j i
        \<Longrightarrow> F y = transition j i y"
      using local_transition_C1[OF j i xoverlap]
      by blast
    obtain W where W: "open W"
      "overlap j i = C j \<inter> W"
      using overlap_open[OF j i]
      by (auto simp: openin_open)
    have xW: "x \<in> W"
      using W(2) xoverlap by auto
    let ?V = "U \<inter> W"
    have openV: "open ?V"
      by (rule open_Int[OF U(1) W(1)])
    have xV: "x \<in> ?V"
      using U(2) xW by simp
    have F1: "Ck_on 1 F ?V"
      by (rule Ck_on_subset[OF U(3) openV])
         auto
    have gF: "Ck_on 1 (\<lambda>y. g (F y)) ?V"
      by (rule Ck_on_compose[OF smooth F1]) auto
    have eq: "g (F y) = rho (from_chart j y)"
      if y: "y \<in> ?V \<inter> C j" for y
    proof -
      have over: "y \<in> overlap j i"
        using y W(2) by auto
      have trans: "F y =
        to_chart i (from_chart j y)"
        using U(4)[of y] y over
        by (simp add: transition_def)
      have inDi: "from_chart j y \<in> D i"
        using over overlap_preimage[OF j] by auto
      show ?thesis
        using inDi trans by (simp add: rho)
    qed
    show ?thesis
      by (rule exI[where x="?V"],
          rule exI[where x="\<lambda>y. g (F y)"])
         (use gF xV eq in auto)
  next
    case False
    have pnotL: "?p \<notin> L"
      using LD False by auto
    have from_cont: "continuous_on (C j) (from_chart j)"
      by (rule homeomorphism_cont2
        [OF halfline_chart.homeo[OF chart[OF j]]])
    have openC: "openin (top_of_set (C j))
      (C j \<inter> (from_chart j) -` (-L))"
      using from_cont closedL
      by (simp only: continuous_openin_preimage_eq
        open_Compl)
    obtain W where W: "open W"
      "C j \<inter> (from_chart j) -` (-L) =
        C j \<inter> W"
      using openC by (auto simp: openin_open)
    have xW: "x \<in> W"
      using W(2) x pnotL by auto
    have zero: "rho (from_chart j y) = 0"
      if y: "y \<in> W \<inter> C j" for y
    proof -
      have ynotL: "from_chart j y \<notin> L"
        using W(2) y by auto
      have yp: "from_chart j y \<in> M"
        using halfline_chart.inverse_image
          [OF chart[OF j]] y
          domain_subset_carrier[OF j]
        by auto
      show ?thesis using support ynotL yp by auto
    qed
    have const: "Ck_on 1 (\<lambda>_. 0::real) W"
      by (rule Ck_on_const[OF W(1)])
    show ?thesis
      by (rule exI[where x=W],
          rule exI[where x="\<lambda>_. 0::real"])
         (use const xW zero in auto)
  qed
qed

lemma continuous_on_M_of_local_cutoff:
  assumes i: "i \<in> I"
    and smooth: "Ck_on 1 g UNIV"
    and rho: "\<And>p. rho p =
      (if p \<in> D i then g (to_chart i p) else 0)"
    and closedL: "closed L"
    and LD: "L \<subseteq> D i"
    and support: "{p\<in>M. rho p \<noteq> 0} \<subseteq> L"
  shows "continuous_on M rho"
proof -
  let ?T = "M - L"
  have DM: "D i \<subseteq> M"
    by (rule domain_subset_carrier[OF i])
  have coverM: "D i \<union> ?T = M"
    using DM LD by auto
  have openD: "openin (top_of_set M) (D i)"
    by (rule halfline_chart.open_D[OF chart[OF i]])
  have openT: "openin (top_of_set M) ?T"
    using closedL
    by (auto simp: openin_open)
  have g_cont: "continuous_on UNIV g"
    by (rule Ck_on_imp_continuous_on[OF smooth])
  have to_cont: "continuous_on (D i) (to_chart i)"
    by (rule homeomorphism_cont1
      [OF halfline_chart.homeo[OF chart[OF i]]])
  have cont_comp:
      "continuous_on (D i) (\<lambda>p. g (to_chart i p))"
    by (rule continuous_on_compose2
      [OF g_cont to_cont]) auto
  have contD: "continuous_on (D i) rho"
    using cont_comp
    by (simp add: rho)
  have zeroT: "rho p = 0" if p: "p \<in> ?T" for p
    using support p by auto
  have contT: "continuous_on ?T rho"
    by (rule continuous_on_eq[where f="\<lambda>_. 0"])
       (use zeroT in \<open>auto intro: continuous_intros\<close>)
  have "continuous_on (D i \<union> ?T) rho"
    by (rule continuous_on_Un_local_open)
       (use openD openT contD contT coverM in auto)
  then show ?thesis
    using coverM by simp
qed


lemma carrier_single_chart_smooth_cutoff_data:
  assumes i: "i \<in> I" and compact: "compact K"
    and Kchart: "K \<subseteq> D i"
  obtains rho :: "'a \<Rightarrow> real"
    and L :: "'a set"
    and g :: "real \<Rightarrow> real"
  where "Ck_on k g UNIV"
    "\<And>p. rho p =
      (if p \<in> D i then g (to_chart i p) else 0)"
    "compact L"
    "L \<subseteq> D i"
    "{p\<in>M. rho p \<noteq> 0} \<subseteq> L"
    "\<And>p. p \<in> K \<Longrightarrow> rho p = 1"
    "\<And>p. 0 \<le> rho p"
    "\<And>p. rho p \<le> 1"
proof -
  have homeo: "homeomorphism (D i) (C i)
      (to_chart i) (from_chart i)"
    by (rule halfline_chart.homeo[OF chart[OF i]])
  have to_cont: "continuous_on (D i) (to_chart i)"
    by (rule homeomorphism_cont1[OF homeo])
  have Qcompact: "compact (to_chart i ` K)"
    by (rule compact_continuous_image)
       (use to_cont compact Kchart in
        \<open>auto intro: continuous_on_subset\<close>)
  obtain U where openU: "open U"
    and Ci: "C i = {0..} \<inter> U"
    using halfline_chart.open_C[OF chart[OF i]]
    by (auto simp: openin_open)
  have KU: "to_chart i ` K \<subseteq> U"
    using halfline_chart.chart_image[OF chart[OF i]]
      Kchart Ci by auto
  show thesis
  proof (rule euclidean_smooth_compact_cutoff
      [OF Qcompact openU KU])
    fix g :: "real \<Rightarrow> real"
      and T :: "(real) set"
    assume smooth: "Ck_on k g UNIV"
      and compactT: "compact T"
      and TU: "T \<subseteq> U"
      and gT: "{x. g x \<noteq> 0} \<subseteq> T"
      and one: "\<And>x. x \<in> to_chart i ` K
        \<Longrightarrow> g x = 1"
      and nonneg: "\<And>x. 0 \<le> g x"
      and le_one: "\<And>x. g x \<le> 1"
    let ?S = "T \<inter> {0..}"
    let ?L = "from_chart i ` ?S"
    let ?rho = "\<lambda>p. if p \<in> D i then
      g (to_chart i p) else 0"
    have compactS: "compact ?S"
      by (rule compact_Int_closed
        [OF compactT closed_atLeast])
    have SC: "?S \<subseteq> C i"
      using TU Ci by auto
    have from_cont: "continuous_on (C i) (from_chart i)"
      by (rule homeomorphism_cont2[OF homeo])
    have compactL: "compact ?L"
      by (rule compact_continuous_image)
         (use from_cont compactS SC in
          \<open>auto intro: continuous_on_subset\<close>)
    have LD: "?L \<subseteq> D i"
      using halfline_chart.inverse_image[OF chart[OF i]]
        SC by auto
    have support: "{p\<in>M. ?rho p \<noteq> 0} \<subseteq> ?L"
    proof
      fix p
      assume p: "p \<in> {p\<in>M. ?rho p \<noteq> 0}"
      then have pD: "p \<in> D i"
        by (auto split: if_splits)
      have xC: "to_chart i p \<in> C i"
        using halfline_chart.chart_image
          [OF chart[OF i]] pD by auto
      have "to_chart i p \<in> ?S"
        using p pD xC gT Ci by auto
      then have "from_chart i (to_chart i p) \<in> ?L"
        by (rule imageI)
      then show "p \<in> ?L"
        using halfline_chart.to_from
          [OF chart[OF i] pD] by simp
    qed
    have oneK: "?rho p = 1" if p: "p \<in> K" for p
      using one[of "to_chart i p"] Kchart p
      by auto
    have nonneg_rho: "0 \<le> ?rho p" for p
      using nonneg[of "to_chart i p"] by auto
    have le_one_rho: "?rho p \<le> 1" for p
      using le_one[of "to_chart i p"] by auto
    show thesis
      by (rule that[where rho="?rho" and L="?L"
        and g=g])
         (use smooth compactL LD support oneK
           nonneg_rho le_one_rho in auto)
  qed
qed

lemma carrier_single_chart_C1_cutoff:
  assumes i: "i \<in> I" and compact: "compact K"
    and Kchart: "K \<subseteq> D i"
  obtains rho :: "'a \<Rightarrow> real" and L where
    "continuous_on M rho"
    "chartwise_C1_scalar rho"
    "compact L"
    "L \<subseteq> D i"
    "{p\<in>M. rho p \<noteq> 0} \<subseteq> L"
    "\<And>p. p \<in> K \<Longrightarrow> rho p = 1"
    "\<And>p. 0 \<le> rho p"
    "\<And>p. rho p \<le> 1"
proof -
  show thesis
  proof (rule carrier_single_chart_smooth_cutoff_data
      [where k=1, OF i compact Kchart])
    fix rho :: "'a \<Rightarrow> real"
      and L :: "'a set"
      and g :: "real \<Rightarrow> real"
    assume smooth: "Ck_on 1 g UNIV"
      and rho: "\<And>p. rho p =
        (if p \<in> D i then g (to_chart i p) else 0)"
      and compactL: "compact L"
      and LD: "L \<subseteq> D i"
      and support: "{p\<in>M. rho p \<noteq> 0} \<subseteq> L"
      and one: "\<And>p. p \<in> K \<Longrightarrow> rho p = 1"
      and nonneg: "\<And>p. 0 \<le> rho p"
      and le_one: "\<And>p. rho p \<le> 1"
    have closedL: "closed L"
      by (rule compact_imp_closed[OF compactL])
    have cont: "continuous_on M rho"
      by (rule continuous_on_M_of_local_cutoff
        [OF i smooth rho closedL LD support])
    have C1: "chartwise_C1_scalar rho"
      by (rule chartwise_C1_scalar_of_local_cutoff
        [OF i smooth rho closedL LD support])
    show thesis
      by (rule that[where rho=rho and L=L])
         (use cont C1 compactL LD support one
           nonneg le_one in auto)
  qed
qed

text \<open>A chartwise partition consists of finitely many chart-supported
scalar functions which sum to one on the chosen set.\<close>

definition chartwise_C1_partition where
  "chartwise_C1_partition K phi F \<longleftrightarrow>
    finite F \<and> F \<subseteq> I \<and>
    (\<forall>p\<in>K. (\<Sum>i\<in>F. phi i p) = 1) \<and>
    (\<forall>i\<in>F. continuous_on M (phi i)) \<and>
    (\<forall>i\<in>F. chartwise_C1_scalar (phi i)) \<and>
    (\<forall>i\<in>F. \<exists>L. closed L \<and>
      {p\<in>M. phi i p \<noteq> 0} \<subseteq> L \<and>
      L \<subseteq> D i) \<and>
    (\<forall>i\<in>F. \<forall>p. 0 \<le> phi i p \<and> phi i p \<le> 1)"

theorem compact_C1_partition_exists:
  assumes compact: "compact K"
    and KM: "K \<subseteq> M"
  shows "\<exists>phi F. chartwise_C1_partition K phi F"
proof -
  have compactin: "compactin (top_of_set M) K"
    using compact KM by (simp add: compactin_subtopology)
  have coverK: "K \<subseteq> (\<Union>i\<in>I. D i)"
    using KM cover by auto
  have openD: "openin (top_of_set M) (D i)"
    if i: "i \<in> I" for i
    by (rule halfline_chart.open_D[OF chart[OF i]])
  obtain F Q where F: "finite F" "F \<subseteq> I"
    and coverQ: "K \<subseteq> (\<Union>i\<in>F. Q i)"
    and compactQ: "\<And>i. i \<in> F \<Longrightarrow>
      compactin (top_of_set M) (Q i)"
    and QD: "\<And>i. i \<in> F \<Longrightarrow>
      Q i \<subseteq> D i"
    using finite_compact_chart_refinement
      [OF carrier_locally_compact carrier_Hausdorff
        compactin coverK openD]
    by blast
  have cutoff: "\<exists>r L.
      continuous_on M r \<and>
      chartwise_C1_scalar r \<and> closed L \<and>
      {p\<in>M. r p \<noteq> (0::real)} \<subseteq> L \<and>
      L \<subseteq> D i \<and>
      (\<forall>p\<in>Q i. r p = 1) \<and>
      (\<forall>p. 0 \<le> r p \<and> r p \<le> 1)"
    if ii: "i \<in> F" for i
  proof -
    have iI: "i \<in> I"
      using F(2) ii by auto
    have compact_abs: "compact (Q i)"
      using compactQ[OF ii]
      by (simp add: compactin_subtopology)
    show ?thesis
    proof (rule carrier_single_chart_C1_cutoff
        [OF iI compact_abs QD[OF ii]])
      fix r :: "'a \<Rightarrow> real" and L :: "'a set"
      assume cont: "continuous_on M r"
        and C1: "chartwise_C1_scalar r"
        and compactL: "compact L"
        and LD: "L \<subseteq> D i"
        and nonzero: "{p\<in>M. r p \<noteq> 0} \<subseteq> L"
        and one: "\<And>p. p \<in> Q i \<Longrightarrow> r p = 1"
        and nonneg: "\<And>p. 0 \<le> r p"
        and le_one: "\<And>p. r p \<le> 1"
      have closedL: "closed L"
        by (rule compact_imp_closed[OF compactL])
      show ?thesis
        apply (rule exI[where x=r])
        apply (rule exI[where x=L])
        using cont C1 closedL LD nonzero one
          nonneg le_one by auto
    qed
  qed
  show ?thesis
  proof (rule finite_C1_chart_partition
      [OF F(1) coverQ cutoff])
    fix phi :: "'i \<Rightarrow> 'a \<Rightarrow> real"
    assume unity: "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i p) = 1"
      and cont: "\<And>i. i \<in> F \<Longrightarrow>
        continuous_on M (phi i)"
      and C1: "\<And>i. i \<in> F \<Longrightarrow>
        chartwise_C1_scalar (phi i)"
      and local: "\<And>i. i \<in> F \<Longrightarrow>
        \<exists>L. closed L \<and>
          {p\<in>M. phi i p \<noteq> 0} \<subseteq> L \<and>
          L \<subseteq> D i"
      and bounds: "\<And>i p. i \<in> F \<Longrightarrow>
        0 \<le> phi i p \<and> phi i p \<le> 1"
    show ?thesis
      apply (rule exI[where x=phi])
      apply (rule exI[where x=F])
      using F unity cont C1 local bounds
      by (auto simp: chartwise_C1_partition_def)
  qed
qed


end

end
