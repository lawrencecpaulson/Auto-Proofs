theory Smooth_Partition
  imports Body_Local_Integration
    Smooth_Cutoff
begin

context smooth_oriented_C2_halfspace_atlas
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
      (F :: real \<times> (real ^ 'n) \<Rightarrow> real) G.
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

lemma local_coordinate_transition_C2:
  assumes j: "j \<in> I" and i: "i \<in> I"
    and x: "x \<in> coordinate_overlap j i"
  obtains U F where "open U" "x \<in> U"
    "Ck_on 2 F U"
    "\<And>y. y \<in> U \<inter> coordinate_overlap j i
      \<Longrightarrow> F y = coordinate_transition j i y"
proof (cases "0 < fst x")
  case True
  have xb: "x \<in> body_overlap j i"
    using x True by (auto simp: body_overlap_def
      open_halfspace_def)
  have openb: "open (body_overlap j i)"
    by (rule body_overlap_open[OF j i])
  have C2: "Ck_on 2 (coordinate_transition j i)
      (body_overlap j i)"
    using smooth_interior_transition[OF j i]
    by (simp add: body_overlap_def)
  show ?thesis
    by (rule that[where U="body_overlap j i"
      and F="coordinate_transition j i"])
       (use openb xb C2 in auto)
next
  case False
  have xC: "x \<in> C j"
    using x by (auto simp: coordinate_overlap_def)
  have xH: "x \<in> closed_halfspace"
    using halfspace_chart.codomain_subset_halfspace
      [OF chart[OF j]] xC by auto
  have x0: "fst x = 0"
    using False xH
    by (auto simp: closed_halfspace_def)
  have x_pair: "x = (0,snd x)"
    using x0 by (cases x) auto
  have yface: "snd x \<in> boundary_overlap j i"
    using x x_pair
    by (auto simp: boundary_overlap_def
      coordinate_overlap_def halfspace_face_def)
  obtain U F where U: "open U" "(0,snd x) \<in> U"
    "Ck_on 2 F U"
    "\<forall>y\<in>U \<inter> C j.
      from_chart j y \<in> D i \<longrightarrow>
        F y = to_chart i (from_chart j y)"
    using transition_extension[OF j i yface]
    by blast
  have agree: "F y = coordinate_transition j i y"
    if y: "y \<in> U \<inter> coordinate_overlap j i" for y
    using U(4) y
    by (auto simp: coordinate_overlap_def
      coordinate_transition_def)
  show ?thesis
    by (rule that[where U=U and F=F])
       (use U x_pair agree in auto)
qed

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
    using halfspace_chart.inverse_image[OF chart[OF j]]
      x by auto
  have pM: "?p \<in> M"
    using domain_subset_carrier[OF j] pD by auto
  show "\<exists>U F. Ck_on 1 F U \<and> x \<in> U \<and>
      (\<forall>y\<in>U \<inter> C j.
        F y = rho (from_chart j y))"
  proof (cases "?p \<in> D i")
    case True
    have xoverlap: "x \<in> coordinate_overlap j i"
      using x True
      by (simp add: coordinate_overlap_def)
    obtain U F where U: "open U" "x \<in> U"
      "Ck_on 2 F U"
      "\<And>y. y \<in> U \<inter> coordinate_overlap j i
        \<Longrightarrow> F y = coordinate_transition j i y"
    proof (rule local_coordinate_transition_C2
        [OF j i xoverlap])
      fix U F
      assume U: "open U" "x \<in> U" "Ck_on 2 F U"
        "\<And>y. y \<in> U \<inter> coordinate_overlap j i
          \<Longrightarrow> F y = coordinate_transition j i y"
      show thesis by (rule that[OF U])
    qed
    obtain W where W: "open W"
      "coordinate_overlap j i = closed_halfspace \<inter> W"
      using coordinate_overlap_open[OF j i]
      by (auto simp: openin_open)
    have CjH: "C j \<subseteq> closed_halfspace"
      by (rule halfspace_chart.codomain_subset_halfspace
        [OF chart[OF j]])
    have W_eq: "coordinate_overlap j i = C j \<inter> W"
      using W(2) CjH
      by (auto simp: coordinate_overlap_def)
    have xW: "x \<in> W"
      using W(2) xoverlap by auto
    let ?V = "U \<inter> W"
    have openV: "open ?V"
      by (rule open_Int[OF U(1) W(1)])
    have xV: "x \<in> ?V"
      using U(2) xW by simp
    have F1: "Ck_on 1 F ?V"
      by (rule Ck_on_mono[OF Ck_on_subset
        [OF U(3) openV _]]) (use W in auto)
    have gF: "Ck_on 1 (\<lambda>y. g (F y)) ?V"
      by (rule Ck_on_compose[OF smooth F1]) auto
    have eq: "g (F y) = rho (from_chart j y)"
      if y: "y \<in> ?V \<inter> C j" for y
    proof -
      have over: "y \<in> coordinate_overlap j i"
        using y W_eq by auto
      have trans: "F y =
        to_chart i (from_chart j y)"
        using U(4)[of y] y over
        by (simp add: coordinate_transition_def)
      show ?thesis
        using over trans
        by (simp add: rho coordinate_overlap_def)
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
        [OF halfspace_chart.homeo[OF chart[OF j]]])
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
        using halfspace_chart.inverse_image
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
    by (rule halfspace_chart.open_D[OF chart[OF i]])
  have openT: "openin (top_of_set M) ?T"
    using closedL
    by (auto simp: openin_open)
  have g_cont: "continuous_on UNIV g"
    by (rule Ck_on_imp_continuous_on[OF smooth])
  have to_cont: "continuous_on (D i) (to_chart i)"
    by (rule homeomorphism_cont1
      [OF halfspace_chart.homeo[OF chart[OF i]]])
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
    and g :: "real \<times> (real ^ 'n) \<Rightarrow> real"
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
    by (rule halfspace_chart.homeo[OF chart[OF i]])
  have to_cont: "continuous_on (D i) (to_chart i)"
    by (rule homeomorphism_cont1[OF homeo])
  have Qcompact: "compact (to_chart i ` K)"
    by (rule compact_continuous_image)
       (use to_cont compact Kchart in
        \<open>auto intro: continuous_on_subset\<close>)
  obtain U where openU: "open U"
    and Ci: "C i = closed_halfspace \<inter> U"
    using halfspace_chart.open_C[OF chart[OF i]]
    by (auto simp: openin_open)
  have KU: "to_chart i ` K \<subseteq> U"
    using halfspace_chart.chart_image[OF chart[OF i]]
      Kchart Ci by auto
  show thesis
  proof (rule euclidean_smooth_compact_cutoff
      [OF Qcompact openU KU])
    fix g :: "real \<times> (real ^ 'n) \<Rightarrow> real"
      and T :: "(real \<times> (real ^ 'n)) set"
    assume smooth: "Ck_on k g UNIV"
      and compactT: "compact T"
      and TU: "T \<subseteq> U"
      and gT: "{x. g x \<noteq> 0} \<subseteq> T"
      and one: "\<And>x. x \<in> to_chart i ` K
        \<Longrightarrow> g x = 1"
      and nonneg: "\<And>x. 0 \<le> g x"
      and le_one: "\<And>x. g x \<le> 1"
    let ?S = "T \<inter> closed_halfspace"
    let ?L = "from_chart i ` ?S"
    let ?rho = "\<lambda>p. if p \<in> D i then
      g (to_chart i p) else 0"
    have compactS: "compact ?S"
      by (rule compact_Int_closed
        [OF compactT closed_closed_halfspace])
    have SC: "?S \<subseteq> C i"
      using TU Ci by auto
    have from_cont: "continuous_on (C i) (from_chart i)"
      by (rule homeomorphism_cont2[OF homeo])
    have compactL: "compact ?L"
      by (rule compact_continuous_image)
         (use from_cont compactS SC in
          \<open>auto intro: continuous_on_subset\<close>)
    have LD: "?L \<subseteq> D i"
      using halfspace_chart.inverse_image[OF chart[OF i]]
        SC by auto
    have support: "{p\<in>M. ?rho p \<noteq> 0} \<subseteq> ?L"
    proof
      fix p
      assume p: "p \<in> {p\<in>M. ?rho p \<noteq> 0}"
      then have pD: "p \<in> D i"
        by (auto split: if_splits)
      have xC: "to_chart i p \<in> C i"
        using halfspace_chart.chart_image
          [OF chart[OF i]] pD by auto
      have "to_chart i p \<in> ?S"
        using p pD xC gT Ci by auto
      then have "from_chart i (to_chart i p) \<in> ?L"
        by (rule imageI)
      then show "p \<in> ?L"
        using halfspace_chart.to_from
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
      and g :: "real \<times> (real ^ 'n) \<Rightarrow> real"
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

lemma boundary_single_chart_C1_cutoff:
  assumes i: "i \<in> I" and compact: "compact K"
    and Kchart: "K \<subseteq> boundary_carrier \<inter> D i"
  obtains rho :: "'a \<Rightarrow> real" and L where
    "continuous_on boundary_carrier rho"
    "chartwise_C1_scalar rho"
    "compact L"
    "L \<subseteq> boundary_carrier \<inter> D i"
    "{p\<in>boundary_carrier. rho p \<noteq> 0} \<subseteq> L"
    "\<And>p. p \<in> K \<Longrightarrow> rho p = 1"
    "\<And>p. 0 \<le> rho p"
    "\<And>p. rho p \<le> 1"
proof -
  have KD: "K \<subseteq> D i" using Kchart by auto
  show thesis
  proof (rule carrier_single_chart_C1_cutoff
      [OF i compact KD])
    fix rho :: "'a \<Rightarrow> real" and T :: "'a set"
    assume cont: "continuous_on M rho"
      and C1: "chartwise_C1_scalar rho"
      and compactT: "compact T"
      and TD: "T \<subseteq> D i"
      and support: "{p\<in>M. rho p \<noteq> 0} \<subseteq> T"
      and one: "\<And>p. p \<in> K \<Longrightarrow> rho p = 1"
      and nonneg: "\<And>p. 0 \<le> rho p"
      and le_one: "\<And>p. rho p \<le> 1"
    let ?L = "T \<inter> boundary_carrier"
    have TM: "T \<subseteq> M"
      using TD domain_subset_carrier[OF i] by auto
    have compactL: "compact ?L"
      by (rule compact_boundary_restriction
        [OF compactT TM])
    have LD: "?L \<subseteq> boundary_carrier \<inter> D i"
      using TD by auto
    have supportL:
        "{p\<in>boundary_carrier. rho p \<noteq> 0} \<subseteq> ?L"
      using support boundary_subset_carrier by auto
    have contB: "continuous_on boundary_carrier rho"
      by (rule continuous_on_subset
        [OF cont boundary_subset_carrier])
    show thesis
      by (rule that[where rho=rho and L="?L"])
         (use contB C1 compactL LD supportL one
           nonneg le_one in auto)
  qed
qed

theorem body_C1_partition_exists:
  assumes compact: "compact K"
    and KM: "K \<subseteq> M"
    and support: "body_form_support alpha \<subseteq> K"
  shows "\<exists>phi F.
    admissible_body_partition alpha phi F \<and>
    (\<forall>p\<in>K. (\<Sum>i\<in>F. phi i p) = 1) \<and>
    (\<forall>i\<in>F. chartwise_C1_scalar (phi i)) \<and>
    (\<forall>i\<in>F. \<forall>p.
      0 \<le> phi i p \<and> phi i p \<le> 1)"
proof -
  have compactin: "compactin (top_of_set M) K"
    using compact KM by (simp add: compactin_subtopology)
  have coverK: "K \<subseteq> (\<Union>i\<in>I. D i)"
    using KM cover by auto
  have openD: "openin (top_of_set M) (D i)"
    if i: "i \<in> I" for i
    by (rule halfspace_chart.open_D[OF chart[OF i]])
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
    have iI: "i \<in> I" using F(2) ii by auto
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
        using cont C1 closedL LD nonzero one nonneg le_one
        by auto
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
    have part: "admissible_body_partition alpha phi F"
      using F unity cont local support
      by (auto simp: admissible_body_partition_def)
    show ?thesis
      apply (rule exI[where x=phi])
      apply (rule exI[where x=F])
      using part unity C1 bounds by auto
  qed
qed

lemma body_partition_restrict_boundary:
  assumes partition: "admissible_body_partition alpha phi F"
    and unity: "\<And>p. p \<in> boundary_form_support beta
      \<Longrightarrow> (\<Sum>i\<in>F. phi i p) = 1"
  shows "admissible_boundary_partition beta phi F"
proof -
  obtain T where T: "closed T"
    "boundary_carrier = M \<inter> T"
    using boundary_carrier_closed
    by (auto simp: closedin_closed)
  have finiteF: "finite F" and FI: "F \<subseteq> I"
    using partition
    by (auto simp: admissible_body_partition_def)
  have data: "continuous_on boundary_carrier (phi i) \<and>
      (\<exists>L. closed L \<and>
        {p\<in>boundary_carrier. phi i p \<noteq> 0}
          \<subseteq> L \<and>
        L \<subseteq> boundary_carrier \<inter> D i)"
    if ii: "i \<in> F" for i
  proof -
    obtain L where L: "closed L"
      "{p\<in>M. phi i p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> D i"
      and cont: "continuous_on M (phi i)"
      using partition ii
      by (auto simp: admissible_body_partition_def)
    have iI: "i \<in> I"
      using FI ii by auto
    have LM: "L \<subseteq> M"
      using L(3) domain_subset_carrier[OF iI]
      by auto
    let ?S = "L \<inter> boundary_carrier"
    have eq: "?S = L \<inter> T"
      using T(2) LM by auto
    have closedS: "closed ?S"
      unfolding eq
      by (rule closed_Int[OF L(1) T(1)])
    have supportS:
        "{p\<in>boundary_carrier. phi i p \<noteq> 0}
        \<subseteq> ?S"
      using L(2) boundary_subset_carrier by auto
    have SD: "?S \<subseteq> boundary_carrier \<inter> D i"
      using L(3) by auto
    have contB: "continuous_on boundary_carrier (phi i)"
      by (rule continuous_on_subset
        [OF cont boundary_subset_carrier])
    show ?thesis
      using contB closedS supportS SD by blast
  qed
  show ?thesis
    using finiteF FI unity data
    by (auto simp: admissible_boundary_partition_def)
qed

theorem body_boundary_C1_partition_exists:
  assumes compact: "compact K"
    and KM: "K \<subseteq> M"
    and body_support: "body_form_support alpha \<subseteq> K"
    and boundary_support:
      "boundary_form_support beta
        \<subseteq> K \<inter> boundary_carrier"
  shows "\<exists>phi F.
    admissible_body_partition alpha phi F \<and>
    admissible_boundary_partition beta phi F \<and>
    (\<forall>p\<in>K. (\<Sum>i\<in>F. phi i p) = 1) \<and>
    (\<forall>i\<in>F. chartwise_C1_scalar (phi i)) \<and>
    (\<forall>i\<in>F. \<forall>p.
      0 \<le> phi i p \<and> phi i p \<le> 1)"
proof -
  obtain phi F where partition:
      "admissible_body_partition alpha phi F"
    and unity: "\<forall>p\<in>K.
      (\<Sum>i\<in>F. phi i p) = 1"
    and C1: "\<forall>i\<in>F.
      chartwise_C1_scalar (phi i)"
    and bounds: "\<forall>i\<in>F. \<forall>p.
      0 \<le> phi i p \<and> phi i p \<le> 1"
    using body_C1_partition_exists
      [OF compact KM body_support]
    by blast
  have unityB: "(\<Sum>i\<in>F. phi i p) = 1"
    if p: "p \<in> boundary_form_support beta" for p
    using unity boundary_support p by auto
  have partitionB: "admissible_boundary_partition beta phi F"
    by (rule body_partition_restrict_boundary
      [OF partition unityB])
  show ?thesis
    apply (rule exI[where x=phi])
    apply (rule exI[where x=F])
    using partition partitionB unity C1 bounds
    by auto
qed

theorem common_C1_partition_integral_rules:
  assumes compact: "compact K"
    and KM: "K \<subseteq> M"
    and body_support: "body_form_support alpha \<subseteq> K"
    and boundary_support:
      "boundary_form_support beta
        \<subseteq> K \<inter> boundary_carrier"
    and body_compatible: "body_top_coeff_compatible alpha"
    and boundary_compatible: "boundary_top_coeff_compatible beta"
    and body_cont: "\<And>i. i \<in> I \<Longrightarrow>
      continuous_on (C i) (alpha i)"
    and boundary_cont: "\<And>i. i \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C i)) (beta i)"
  shows "\<exists>phi F.
    admissible_body_partition alpha phi F \<and>
    admissible_boundary_partition beta phi F \<and>
    (\<forall>p\<in>K. (\<Sum>i\<in>F. phi i p) = 1) \<and>
    (\<forall>i\<in>F. chartwise_C1_scalar (phi i)) \<and>
    (\<forall>i\<in>F. \<forall>p.
      0 \<le> phi i p \<and> phi i p \<le> 1) \<and>
    integral_body_top alpha =
      body_chart_partition_integral alpha phi F \<and>
    integral_boundary_top beta =
      boundary_chart_partition_integral beta phi F"
proof -
  obtain phi F where partM:
      "admissible_body_partition alpha phi F"
    and partB:
      "admissible_boundary_partition beta phi F"
    and unity: "\<forall>p\<in>K.
      (\<Sum>i\<in>F. phi i p) = 1"
    and C1: "\<forall>i\<in>F.
      chartwise_C1_scalar (phi i)"
    and bounds: "\<forall>i\<in>F. \<forall>p.
      0 \<le> phi i p \<and> phi i p \<le> 1"
    using body_boundary_C1_partition_exists
      [OF compact KM body_support boundary_support]
    by blast
  have body_eq: "integral_body_top alpha =
      body_chart_partition_integral alpha phi F"
    by (rule integral_body_top_eq_partition
      [OF body_compatible compact body_support body_cont partM])
  have boundary_eq: "integral_boundary_top beta =
      boundary_chart_partition_integral beta phi F"
    by (rule integral_boundary_top_eq_partition
      [OF boundary_compatible compact
        _ boundary_cont partB])
       (use boundary_support in auto)
  show ?thesis
    apply (rule exI[where x=phi])
    apply (rule exI[where x=F])
    using partM partB unity C1 bounds body_eq boundary_eq
    by auto
qed

theorem boundary_C1_partition_exists:
  assumes compact: "compact K"
    and KB: "K \<subseteq> boundary_carrier"
    and support: "boundary_form_support alpha \<subseteq> K"
  shows "\<exists>phi F.
    admissible_boundary_partition alpha phi F \<and>
    (\<forall>p\<in>K. (\<Sum>i\<in>F. phi i p) = 1) \<and>
    (\<forall>i\<in>F. chartwise_C1_scalar (phi i)) \<and>
    (\<forall>i\<in>F. \<forall>p.
      0 \<le> phi i p \<and> phi i p \<le> 1)"
proof -
  let ?E = "\<lambda>i. boundary_carrier \<inter> D i"
  have compactin:
      "compactin (top_of_set boundary_carrier) K"
    using compact KB by (simp add: compactin_subtopology)
  have coverK: "K \<subseteq> (\<Union>i\<in>I. ?E i)"
    using KB cover boundary_subset_carrier by auto
  have openE: "openin (top_of_set boundary_carrier) (?E i)"
    if i: "i \<in> I" for i
    by (rule boundary_chart_domain_open[OF i])
  obtain F Q where F: "finite F" "F \<subseteq> I"
    and coverQ: "K \<subseteq> (\<Union>i\<in>F. Q i)"
    and compactQ: "\<And>i. i \<in> F \<Longrightarrow>
      compactin (top_of_set boundary_carrier) (Q i)"
    and QD: "\<And>i. i \<in> F \<Longrightarrow>
      Q i \<subseteq> ?E i"
    using finite_compact_chart_refinement
      [OF boundary_carrier_locally_compact
        boundary_carrier_Hausdorff
        compactin coverK openE]
    by blast
  have cutoff: "\<exists>r L.
      continuous_on boundary_carrier r \<and>
      chartwise_C1_scalar r \<and> closed L \<and>
      {p\<in>boundary_carrier. r p \<noteq> (0::real)}
        \<subseteq> L \<and>
      L \<subseteq> ?E i \<and>
      (\<forall>p\<in>Q i. r p = 1) \<and>
      (\<forall>p. 0 \<le> r p \<and> r p \<le> 1)"
    if ii: "i \<in> F" for i
  proof -
    have iI: "i \<in> I" using F(2) ii by auto
    have compact_abs: "compact (Q i)"
      using compactQ[OF ii]
      by (simp add: compactin_subtopology)
    show ?thesis
    proof (rule boundary_single_chart_C1_cutoff
        [OF iI compact_abs QD[OF ii]])
      fix r :: "'a \<Rightarrow> real" and L :: "'a set"
      assume cont: "continuous_on boundary_carrier r"
        and C1: "chartwise_C1_scalar r"
        and compactL: "compact L"
        and LD: "L \<subseteq> ?E i"
        and nonzero:
          "{p\<in>boundary_carrier. r p \<noteq> 0} \<subseteq> L"
        and one: "\<And>p. p \<in> Q i \<Longrightarrow> r p = 1"
        and nonneg: "\<And>p. 0 \<le> r p"
        and le_one: "\<And>p. r p \<le> 1"
      have closedL: "closed L"
        by (rule compact_imp_closed[OF compactL])
      show ?thesis
        apply (rule exI[where x=r])
        apply (rule exI[where x=L])
        using cont C1 closedL LD nonzero one
          nonneg le_one
        by auto
    qed
  qed
  show ?thesis
  proof (rule finite_C1_chart_partition
      [OF F(1) coverQ cutoff])
    fix phi :: "'i \<Rightarrow> 'a \<Rightarrow> real"
    assume unity: "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i p) = 1"
      and cont: "\<And>i. i \<in> F \<Longrightarrow>
        continuous_on boundary_carrier (phi i)"
      and C1: "\<And>i. i \<in> F \<Longrightarrow>
        chartwise_C1_scalar (phi i)"
      and local: "\<And>i. i \<in> F \<Longrightarrow>
        \<exists>L. closed L \<and>
          {p\<in>boundary_carrier. phi i p \<noteq> 0}
            \<subseteq> L \<and> L \<subseteq> ?E i"
      and bounds: "\<And>i p. i \<in> F \<Longrightarrow>
        0 \<le> phi i p \<and> phi i p \<le> 1"
    have part: "admissible_boundary_partition alpha phi F"
      using F unity cont local support
      by (auto simp: admissible_boundary_partition_def)
    show ?thesis
      apply (rule exI[where x=phi])
      apply (rule exI[where x=F])
      using part unity C1 bounds by auto
  qed
qed

end

end
