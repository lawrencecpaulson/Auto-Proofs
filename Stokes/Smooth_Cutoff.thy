theory Smooth_Cutoff
  imports Halfline_Forms "HOL-Analysis.Real_Analytic"
    "HOL-Analysis.Abstract_Topological_Spaces"
begin

lemma compactin_open_compact_collar:
  assumes loc: "locally_compact_space X"
    and haus: "Hausdorff_space X"
    and compact: "compactin X K"
    and openW: "openin X W"
    and sub: "K \<subseteq> W"
  obtains V L where "openin X V" "compactin X L"
    "K \<subseteq> V" "V \<subseteq> L" "L \<subseteq> W"
proof -
  have regular: "regular_space X"
    by (rule locally_compact_Hausdorff_imp_regular_space
      [OF loc haus])
  have base: "neighbourhood_base_of (compactin X) X"
    by (rule locally_compact_imp_neighbourhood_base
      [OF loc regular])
  have witness: "\<And>p. p \<in> K \<Longrightarrow>
      \<exists>U L. openin X U \<and> compactin X L \<and>
        p \<in> U \<and> U \<subseteq> L \<and> L \<subseteq> W"
    using base openW sub by (auto simp: neighbourhood_base_of)
  obtain u l where data: "\<And>p. p \<in> K \<Longrightarrow>
      openin X (u p) \<and> compactin X (l p) \<and>
      p \<in> u p \<and> u p \<subseteq> l p \<and> l p \<subseteq> W"
    using witness by metis
  have cover: "K \<subseteq> \<Union>(u ` K)"
    using data by auto
  have open_cover: "\<And>T. T \<in> u ` K \<Longrightarrow> openin X T"
    using data by auto
  obtain F where F: "finite F" "F \<subseteq> u ` K"
    "K \<subseteq> \<Union>F"
    using compactinD[OF compact open_cover cover]
    by blast
  obtain P where P: "P \<subseteq> K" "finite P" "u ` P = F"
    using finite_subset_image[OF F(1,2)] by blast
  let ?V = "\<Union>(u ` P)"
  let ?L = "\<Union>(l ` P)"
  have openV: "openin X ?V"
    by (rule openin_Union) (use data P(1) in auto)
  have compactL: "compactin X ?L"
    by (rule compactin_Union)
       (use P data in auto)
  have KV: "K \<subseteq> ?V"
    using F(3) P(3) by simp
  have VL: "?V \<subseteq> ?L"
    using data P(1) by auto
  have LW: "?L \<subseteq> W"
    using data P(1) by auto
  show ?thesis
    by (rule that[OF openV compactL KV VL LW])
qed

lemma finite_compact_chart_refinement:
  fixes X :: "'a::topological_space topology"
    and D :: "'i \<Rightarrow> 'a set"
  assumes loc: "locally_compact_space X"
    and haus: "Hausdorff_space X"
    and compact: "compactin X K"
    and cover: "K \<subseteq> (\<Union>i\<in>I. D i)"
    and openD: "\<And>i. i \<in> I \<Longrightarrow> openin X (D i)"
  shows "\<exists>F Q. finite F \<and> F \<subseteq> I \<and>
    K \<subseteq> (\<Union>i\<in>F. Q i) \<and>
    (\<forall>i\<in>F. compactin X (Q i)) \<and>
    (\<forall>i\<in>F. Q i \<subseteq> D i)"
proof -
  have witness: "\<exists>i V L. i \<in> I \<and> openin X V \<and>
      p \<in> V \<and> compactin X L \<and> V \<subseteq> L \<and>
      L \<subseteq> D i" if p: "p \<in> K" for p
  proof -
    obtain i where i: "i \<in> I" "p \<in> D i"
      using cover p by auto
    have singleton: "compactin X {p}"
      using compactin_subset_topspace[OF compact] p
      by (intro finite_imp_compactin) auto
    obtain V L where V: "openin X V" "compactin X L"
      "{p} \<subseteq> V" "V \<subseteq> L" "L \<subseteq> D i"
      by (rule compactin_open_compact_collar
        [OF loc haus singleton openD[OF i(1)]])
         (use i(2) in auto)
    show ?thesis using i V by blast
  qed
  obtain j V L where data: "\<And>p. p \<in> K \<Longrightarrow>
      j p \<in> I \<and> openin X (V p) \<and> p \<in> V p \<and>
      compactin X (L p) \<and> V p \<subseteq> L p \<and>
      L p \<subseteq> D (j p)"
    using witness by metis
  have coverV: "K \<subseteq> \<Union>(V ` K)"
    using data by auto
  obtain T where T: "finite T" "T \<subseteq> V ` K"
      "K \<subseteq> \<Union>T"
    using compactinD[OF compact _ coverV] data
    by auto
  obtain P where P: "P \<subseteq> K" "finite P" "V ` P = T"
    using finite_subset_image[OF T(1,2)] by blast
  let ?F = "j ` P"
  let ?Q = "\<lambda>i. \<Union>p\<in>{p\<in>P. j p = i}. L p"
  have finiteF: "finite ?F" using P by simp
  have FI: "?F \<subseteq> I" using P data by auto
  have coverQ: "K \<subseteq> (\<Union>i\<in>?F. ?Q i)"
  proof
    fix x
    assume x: "x \<in> K"
    then obtain p where p: "p \<in> P" "x \<in> V p"
      using T(3) P(3) by auto
    have "x \<in> L p"
      using data[of p] P(1) p by auto
    then show "x \<in> (\<Union>i\<in>?F. ?Q i)"
      using p by blast
  qed
  have compactQ: "compactin X (?Q i)"
    if i: "i \<in> ?F" for i
    by (rule compactin_Union)
       (use P data in auto)
  have QD: "?Q i \<subseteq> D i"
    if i: "i \<in> ?F" for i
    using P data by auto
  show ?thesis
    apply (rule exI[where x="?F"])
    apply (rule exI[where x="?Q"])
    using finiteF FI coverQ compactQ QD by auto
qed

definition stokes_smooth_step :: "real \<Rightarrow> real"
  where "stokes_smooth_step t =
    exp_bump t / (exp_bump t + exp_bump (1 - t))"

lemma stokes_exp_bump_nonnegative:
  "0 \<le> exp_bump t"
  by (simp add: exp_bump_def)

lemma stokes_exp_bump_pos_iff:
  "0 < exp_bump t \<longleftrightarrow> 0 < t"
  by (simp add: exp_bump_def)

lemma stokes_smooth_step_denominator_pos:
  "0 < exp_bump t + exp_bump (1 - t)"
proof (cases "0 < t")
  case True
  then show ?thesis
    using stokes_exp_bump_pos_iff[of t]
      stokes_exp_bump_nonnegative[of "1 - t"]
    by linarith
next
  case False
  then have "0 < 1 - t" by simp
  then show ?thesis
    using stokes_exp_bump_pos_iff[of "1 - t"]
      stokes_exp_bump_nonnegative[of t]
    by linarith
qed

lemma stokes_smooth_step_zero:
  assumes "t \<le> 0"
  shows "stokes_smooth_step t = 0"
  using assms stokes_smooth_step_denominator_pos[of t]
  by (simp add: stokes_smooth_step_def exp_bump_def)

lemma stokes_smooth_step_one:
  assumes "1 \<le> t"
  shows "stokes_smooth_step t = 1"
  using assms stokes_smooth_step_denominator_pos[of t]
  by (simp add: stokes_smooth_step_def exp_bump_def)

lemma stokes_smooth_step_nonnegative:
  "0 \<le> stokes_smooth_step t"
  using stokes_smooth_step_denominator_pos[of t]
    stokes_exp_bump_nonnegative[of t]
  by (simp add: stokes_smooth_step_def)

lemma stokes_smooth_step_le_one:
  "stokes_smooth_step t \<le> 1"
  using stokes_smooth_step_denominator_pos[of t]
    stokes_exp_bump_nonnegative[of t]
    stokes_exp_bump_nonnegative[of "1 - t"]
  by (simp add: stokes_smooth_step_def)

lemma stokes_smooth_step_Ck_on:
  "Ck_on k stokes_smooth_step UNIV"
proof -
  have bump: "Ck_on k exp_bump UNIV"
    by (rule Cinfinity_on_imp_Ck_on
      [OF exp_bump_Cinfinity])
  have sub: "Ck_on k (\<lambda>t::real. 1 - t) UNIV"
    by (intro Ck_on_sub Ck_on_const Ck_on_id) auto
  have bump_sub:
      "Ck_on k (\<lambda>t. exp_bump (1 - t)) UNIV"
    by (rule Ck_on_compose[OF bump sub]) auto
  have den: "Ck_on k
      (\<lambda>t. exp_bump t + exp_bump (1 - t)) UNIV"
    by (rule Ck_on_add[OF bump bump_sub])
  have quotient: "Ck_on k
      (\<lambda>t. exp_bump t /
        (exp_bump t + exp_bump (1 - t))) UNIV"
  proof (rule Ck_on_divide[OF bump den])
    fix t :: real
    assume "t \<in> UNIV"
    show "exp_bump t + exp_bump (1 - t) \<noteq> 0"
      using stokes_smooth_step_denominator_pos[of t]
      by simp
  qed
  show ?thesis
    unfolding stokes_smooth_step_def
    by (rule quotient)
qed

definition stokes_ball_cutoff ::
    "'a::euclidean_space \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
      'a \<Rightarrow> real"
  where "stokes_ball_cutoff a r R x =
    stokes_smooth_step
      ((R\<^sup>2 - (norm (x - a))\<^sup>2) / (R\<^sup>2 - r\<^sup>2))"

lemma stokes_ball_cutoff_Ck_on:
  fixes a :: "'a::euclidean_space"
  assumes r: "0 \<le> r" and R: "r < R"
  shows "Ck_on k (stokes_ball_cutoff a r R) UNIV"
proof -
  have den_pos: "0 < R\<^sup>2 - r\<^sup>2"
    using power_strict_mono[OF R r, of 2] by simp
  have lin: "Ck_on k (\<lambda>x::'a. x - a) UNIV"
    by (intro Ck_on_sub Ck_on_id Ck_on_const) auto
  have norm_sq: "Ck_on k
      (\<lambda>x::'a. (norm (x - a))\<^sup>2) UNIV"
    by (rule Ck_on_norm_sq[OF lin])
  have num: "Ck_on k
      (\<lambda>x::'a. R\<^sup>2 - (norm (x - a))\<^sup>2) UNIV"
    by (intro Ck_on_sub Ck_on_const norm_sq) auto
  have den: "Ck_on k
      (\<lambda>x::'a. R\<^sup>2 - r\<^sup>2) UNIV"
    by (intro Ck_on_const) auto
  have quot: "Ck_on k
      (\<lambda>x::'a.
        (R\<^sup>2 - (norm (x - a))\<^sup>2) /
          (R\<^sup>2 - r\<^sup>2)) UNIV"
    by (rule Ck_on_divide[OF num den])
       (use den_pos in auto)
  have step: "Ck_on k stokes_smooth_step UNIV"
    by (rule stokes_smooth_step_Ck_on)
  show ?thesis
    unfolding stokes_ball_cutoff_def
    by (rule Ck_on_compose[OF step quot]) auto
qed

lemma stokes_ball_cutoff_one:
  fixes a :: "'a::euclidean_space"
  assumes r: "0 \<le> r" and R: "r < R"
    and x: "x \<in> cball a r"
  shows "stokes_ball_cutoff a r R x = 1"
proof -
  have den_pos: "0 < R\<^sup>2 - r\<^sup>2"
    using power_strict_mono[OF R r, of 2] by simp
  have norm_le: "norm (x - a) \<le> r"
    using x by (simp add: dist_norm norm_minus_commute)
  have sq_le: "(norm (x - a))\<^sup>2 \<le> r\<^sup>2"
    using norm_le r by (intro power_mono) auto
  have "1 \<le>
      (R\<^sup>2 - (norm (x - a))\<^sup>2) /
        (R\<^sup>2 - r\<^sup>2)"
    using den_pos sq_le
    by (simp add: le_divide_eq)
  then show ?thesis
    by (simp add: stokes_ball_cutoff_def
      stokes_smooth_step_one)
qed

lemma stokes_ball_cutoff_zero:
  fixes a :: "'a::euclidean_space"
  assumes r: "0 \<le> r" and R: "r < R"
    and x: "x \<notin> ball a R"
  shows "stokes_ball_cutoff a r R x = 0"
proof -
  have R0: "0 \<le> R" using r R by simp
  have den_pos: "0 < R\<^sup>2 - r\<^sup>2"
    using power_strict_mono[OF R r, of 2] by simp
  have norm_ge: "R \<le> norm (x - a)"
    using x by (simp add: dist_norm norm_minus_commute)
  have sq_ge: "R\<^sup>2 \<le> (norm (x - a))\<^sup>2"
    using norm_ge R0 by (intro power_mono) auto
  have "R\<^sup>2 - (norm (x - a))\<^sup>2 \<le> 0"
    using sq_ge by simp
  then show ?thesis
    unfolding stokes_ball_cutoff_def
    using den_pos
    by (intro stokes_smooth_step_zero)
       (simp add: divide_nonpos_pos)
qed

theorem euclidean_smooth_compact_cutoff:
  fixes K W :: "'a::euclidean_space set"
  assumes compact: "compact K"
    and openW: "open W"
    and KW: "K \<subseteq> W"
  obtains f :: "'a \<Rightarrow> real" and L where
    "Ck_on k f UNIV"
    "compact L"
    "L \<subseteq> W"
    "{x. f x \<noteq> 0} \<subseteq> L"
    "\<And>x. x \<in> K \<Longrightarrow> f x = 1"
    "\<And>x. 0 \<le> f x"
    "\<And>x. f x \<le> 1"
proof -
  let ?R = "\<lambda>p. SOME R. 0 < R \<and> cball p R \<subseteq> W"
  have radius: "0 < ?R p \<and> cball p (?R p) \<subseteq> W"
    if p: "p \<in> K" for p
  proof -
    have "\<exists>R. 0 < R \<and> cball p R \<subseteq> W"
      using openW KW p
      by (auto simp: open_contains_cball)
    then show ?thesis by (rule someI_ex)
  qed
  let ?V = "\<lambda>p. ball p (?R p / 2)"
  let ?L = "\<lambda>p. cball p (?R p)"
  have cover: "K \<subseteq> (\<Union>p\<in>K. ?V p)"
    using radius by auto
  obtain P where P: "P \<subseteq> K" "finite P"
    "K \<subseteq> (\<Union>p\<in>P. ?V p)"
    by (rule compactE_image[OF compact])
       (use cover in auto)
  let ?B = "\<lambda>p x. stokes_ball_cutoff
    p (?R p / 2) (?R p) x"
  let ?S = "\<lambda>x. \<Sum>p\<in>P. ?B p x"
  let ?f = "\<lambda>x. stokes_smooth_step (?S x)"
  let ?T = "\<Union>p\<in>P. ?L p"
  have r0: "0 \<le> ?R p / 2" and rR: "?R p / 2 < ?R p"
    if p: "p \<in> P" for p
    using radius[of p] P(1) p by auto
  have B_smooth: "Ck_on k (?B p) UNIV"
    if p: "p \<in> P" for p
    by (rule stokes_ball_cutoff_Ck_on[OF r0[OF p] rR[OF p]])
  have S_smooth: "Ck_on k ?S UNIV"
  proof (cases "P = {}")
    case True
    then show ?thesis
      by (simp add: Ck_on_const)
  next
    case False
    show ?thesis
      by (rule Ck_on_sum[OF P(2) False B_smooth])
  qed
  have f_smooth: "Ck_on k ?f UNIV"
    by (rule Ck_on_compose
      [OF stokes_smooth_step_Ck_on S_smooth]) auto
  have compactT: "compact ?T"
    by (rule compact_Union)
       (use P(2) in auto)
  have TW: "?T \<subseteq> W"
    using radius P(1) by auto
  have B_nonneg: "0 \<le> ?B p x" for p x
    unfolding stokes_ball_cutoff_def
    by (rule stokes_smooth_step_nonnegative)
  have S_ge_one: "1 \<le> ?S x" if x: "x \<in> K" for x
  proof -
    obtain p where p: "p \<in> P" "x \<in> ?V p"
      using P(3) x by auto
    have B_one: "?B p x = 1"
      by (rule stokes_ball_cutoff_one
        [OF r0[OF p(1)] rR[OF p(1)]])
         (use p in auto)
    have "?B p x \<le> ?S x"
      by (rule member_le_sum[OF p(1) _ P(2)])
         (use B_nonneg in auto)
    then show ?thesis using B_one by simp
  qed
  have oneK: "?f x = 1" if x: "x \<in> K" for x
    by (rule stokes_smooth_step_one[OF S_ge_one[OF x]])
  have support: "{x. ?f x \<noteq> 0} \<subseteq> ?T"
  proof
    fix x
    assume x: "x \<in> {x. ?f x \<noteq> 0}"
    have Spos: "0 < ?S x"
    proof (rule ccontr)
      assume "\<not> 0 < ?S x"
      then have "?S x \<le> 0" by simp
      then have "?f x = 0"
        by (rule stokes_smooth_step_zero)
      then show False using x by simp
    qed
    have nz: "\<exists>p\<in>P. ?B p x \<noteq> 0"
    proof (rule ccontr)
      assume "\<not> (\<exists>p\<in>P. ?B p x \<noteq> 0)"
      then have "(\<Sum>p\<in>P. ?B p x) = 0"
        by (intro sum.neutral) auto
      then show False using Spos by simp
    qed
    then obtain p where p: "p \<in> P" "?B p x \<noteq> 0"
      by auto
    have "x \<in> ball p (?R p)"
      using p r0[OF p(1)] rR[OF p(1)]
        stokes_ball_cutoff_zero[of "?R p / 2" "?R p" x p]
      by blast
    then have "x \<in> ?L p" by auto
    then show "x \<in> ?T"
      using p(1) by blast
  qed
  have nonneg: "0 \<le> ?f x" for x
    by (rule stokes_smooth_step_nonnegative)
  have le_one: "?f x \<le> 1" for x
    by (rule stokes_smooth_step_le_one)
  show thesis
    by (rule that[where f="?f" and L="?T"])
       (use f_smooth compactT TW support oneK
         nonneg le_one in auto)
qed

definition chartwise_C1_scalar_on ::
  "'i set \<Rightarrow> ('i \<Rightarrow> 'e::euclidean_space set) \<Rightarrow>
    ('i \<Rightarrow> 'e \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
  where "chartwise_C1_scalar_on I C from_chart rho \<longleftrightarrow>
    (\<forall>j\<in>I. \<forall>x\<in>C j. \<exists>U F.
      Ck_on 1 F U \<and> x \<in> U \<and>
      (\<forall>y\<in>U \<inter> C j.
        F y = rho (from_chart j y)))"

lemma chartwise_C1_scalar_on_binary:
  fixes C :: "'i \<Rightarrow> 'e::euclidean_space set"
    and from_chart :: "'i \<Rightarrow> 'e \<Rightarrow> 'a"
    and h :: "real \<Rightarrow> real \<Rightarrow> real"
  assumes a: "chartwise_C1_scalar_on I C from_chart a"
    and b: "chartwise_C1_scalar_on I C from_chart b"
    and closure: "\<And>U
      (F :: 'e \<Rightarrow> real) G.
      Ck_on 1 F U \<Longrightarrow> Ck_on 1 G U \<Longrightarrow>
      Ck_on 1 (\<lambda>y. h (F y) (G y)) U"
  shows "chartwise_C1_scalar_on I C from_chart
    (\<lambda>p. h (a p) (b p))"
proof (unfold chartwise_C1_scalar_on_def, intro ballI)
  fix j x
  assume j: "j \<in> I" and x: "x \<in> C j"
  have exF: "\<exists>U F. Ck_on 1 F U \<and> x \<in> U \<and>
    (\<forall>y\<in>U \<inter> C j. F y = a (from_chart j y))"
    using a j x
    by (auto simp: chartwise_C1_scalar_on_def)
  obtain U F where F: "Ck_on 1 F U" "x \<in> U"
    "\<forall>y\<in>U \<inter> C j. F y = a (from_chart j y)"
    using exF by blast
  have exG: "\<exists>V G. Ck_on 1 G V \<and> x \<in> V \<and>
    (\<forall>y\<in>V \<inter> C j. G y = b (from_chart j y))"
    using b j x
    by (auto simp: chartwise_C1_scalar_on_def)
  obtain V G where G: "Ck_on 1 G V" "x \<in> V"
    "\<forall>y\<in>V \<inter> C j. G y = b (from_chart j y)"
    using exG by blast
  let ?W = "U \<inter> V"
  have openW: "open ?W"
    by (rule open_Int)
       (use Ck_on_open[OF F(1)]
         Ck_on_open[OF G(1)] in auto)
  have FW: "Ck_on 1 F ?W"
    by (rule Ck_on_subset[OF F(1) openW]) auto
  have GW: "Ck_on 1 G ?W"
    by (rule Ck_on_subset[OF G(1) openW]) auto
  have hW: "Ck_on 1 (\<lambda>y. h (F y) (G y)) ?W"
    by (rule closure[OF FW GW])
  have eq: "h (F y) (G y) =
      h (a (from_chart j y)) (b (from_chart j y))"
    if y: "y \<in> ?W \<inter> C j" for y
    using F(3) G(3) y by auto
  show "\<exists>U H. Ck_on 1 H U \<and> x \<in> U \<and>
    (\<forall>y\<in>U \<inter> C j.
      H y = h (a (from_chart j y))
        (b (from_chart j y)))"
    by (rule exI[where x="?W"],
        rule exI[where x="\<lambda>y. h (F y) (G y)"])
       (use hW F(2) G(2) eq in auto)
qed

locale scalar_partition_algebra =
  fixes smooth :: "('a::topological_space \<Rightarrow> real) \<Rightarrow> bool"
  assumes smooth_const: "\<And>c. smooth (\<lambda>_. c)"
    and smooth_sub: "\<And>f g. smooth f \<Longrightarrow> smooth g \<Longrightarrow>
      smooth (\<lambda>p. f p - g p)"
    and smooth_mult: "\<And>f g. smooth f \<Longrightarrow> smooth g \<Longrightarrow>
      smooth (\<lambda>p. f p * g p)"
begin

lemma finite_C1_partition_from_cutoffs:
  fixes r :: "'i \<Rightarrow> 'a \<Rightarrow> real"
    and X :: "'a set"
  assumes finite: "finite F"
    and C1: "\<And>i. i \<in> F \<Longrightarrow>
      smooth (r i)"
    and bounds: "\<And>i p. i \<in> F \<Longrightarrow>
      0 \<le> r i p \<and> r i p \<le> 1"
    and cont: "\<And>i. i \<in> F \<Longrightarrow>
      continuous_on X (r i)"
  shows "\<exists>phi.
    (\<forall>i\<in>F. smooth (phi i)) \<and>
    (\<forall>i\<in>F. continuous_on X (phi i)) \<and>
    (\<forall>i\<in>F. \<forall>p. phi i p \<noteq> 0 \<longrightarrow> r i p \<noteq> 0) \<and>
    (\<forall>i\<in>F. \<forall>p. 0 \<le> phi i p \<and> phi i p \<le> 1) \<and>
    (\<forall>p. (\<Sum>i\<in>F. phi i p) =
      1 - (\<Prod>i\<in>F. (1 - r i p)))"
  using finite C1 bounds cont
proof (induction F rule: finite_induct)
  case empty
  show ?case
    by (rule exI[where x="\<lambda>i p. 0::real"])
       simp
next
  case (insert i F)
  have C1i: "smooth (r i)"
    using insert.prems by auto
  have C1F: "\<And>j. j \<in> F \<Longrightarrow>
      smooth (r j)"
    using insert.prems by auto
  have boundsi: "\<And>p. 0 \<le> r i p \<and> r i p \<le> 1"
    using insert.prems by auto
  have boundsF: "\<And>j p. j \<in> F \<Longrightarrow>
      0 \<le> r j p \<and> r j p \<le> 1"
    using insert.prems by auto
  have conti: "continuous_on X (r i)"
    using insert.prems by auto
  have contF: "\<And>j. j \<in> F \<Longrightarrow>
      continuous_on X (r j)"
    using insert.prems by auto
  obtain psi where psi:
    "\<forall>j\<in>F. smooth (psi j)"
    "\<forall>j\<in>F. continuous_on X (psi j)"
    "\<forall>j\<in>F. \<forall>p.
      psi j p \<noteq> 0 \<longrightarrow> r j p \<noteq> 0"
    "\<forall>j\<in>F. \<forall>p.
      0 \<le> psi j p \<and> psi j p \<le> 1"
    "\<forall>p. (\<Sum>j\<in>F. psi j p) =
      1 - (\<Prod>j\<in>F. (1 - r j p))"
    using insert.IH[OF C1F boundsF contF] by blast
  let ?phi = "\<lambda>j p. if j = i then r i p
    else (1 - r i p) * psi j p"
  have one_minus: "smooth
      (\<lambda>p. 1 - r i p)"
    by (rule smooth_sub
      [OF smooth_const C1i])
  have C1phi: "smooth (?phi j)"
    if j: "j \<in> insert i F" for j
  proof (cases "j = i")
    case True
    then show ?thesis using C1i by simp
  next
    case False
    have jF: "j \<in> F" using j False by auto
    have C1psi: "smooth (psi j)"
      using psi(1) jF by auto
    show ?thesis
      using False
      by (simp add: smooth_mult
        [OF one_minus C1psi])
  qed
  have cont_phi: "continuous_on X (?phi j)"
    if j: "j \<in> insert i F" for j
  proof (cases "j = i")
    case True
    then show ?thesis using conti by simp
  next
    case False
    have jF: "j \<in> F" using j False by auto
    have contpsi: "continuous_on X (psi j)"
      using psi(2) jF by auto
    show ?thesis
      using False conti contpsi
      by (auto intro!: continuous_intros)
  qed
  have support: "?phi j p \<noteq> 0 \<Longrightarrow> r j p \<noteq> 0"
    if j: "j \<in> insert i F" for j p
  proof -
    assume nz: "?phi j p \<noteq> 0"
    show "r j p \<noteq> 0"
    proof (cases "j = i")
      case True
      then show ?thesis using nz by simp
    next
      case False
      have jF: "j \<in> F" using j False by auto
      have imp: "psi j p \<noteq> 0 \<Longrightarrow> r j p \<noteq> 0"
        using psi(3) jF by auto
      show ?thesis
        using False imp nz by auto
    qed
  qed
  have bounds_phi: "0 \<le> ?phi j p \<and> ?phi j p \<le> 1"
    if j: "j \<in> insert i F" for j p
  proof (cases "j = i")
    case True
    then show ?thesis using boundsi by simp
  next
    case False
    have jF: "j \<in> F" using j False by auto
    have psib: "0 \<le> psi j p \<and> psi j p \<le> 1"
      using psi(4) jF by auto
    have rb: "0 \<le> r i p \<and> r i p \<le> 1"
      by (rule boundsi)
    show ?thesis
      using False rb psib
      by (simp add: mult_le_one)
  qed
  have formula: "(\<Sum>j\<in>insert i F. ?phi j p) =
      1 - (\<Prod>j\<in>insert i F. (1 - r j p))"
    for p
  proof -
    have eqF: "(\<Sum>j\<in>F. ?phi j p) =
      (\<Sum>j\<in>F. (1 - r i p) * psi j p)"
      by (rule sum.cong)
         (use insert.hyps(2) in auto)
    have IH_eq: "(\<Sum>j\<in>F. psi j p) =
      1 - (\<Prod>j\<in>F. (1 - r j p))"
      using psi(5) by auto
    have "(\<Sum>j\<in>insert i F. ?phi j p) =
      r i p + (1 - r i p) * (\<Sum>j\<in>F. psi j p)"
      using insert.hyps eqF
      by (simp add: sum_distrib_left)
    also have "\<dots> =
      1 - (1 - r i p) *
        (\<Prod>j\<in>F. (1 - r j p))"
      by (simp add: IH_eq algebra_simps)
    also have "\<dots> =
      1 - (\<Prod>j\<in>insert i F. (1 - r j p))"
      using insert.hyps by simp
    finally show ?thesis .
  qed
  show ?case
    by (rule exI[where x="?phi"])
       (use C1phi cont_phi support bounds_phi formula in auto)
qed

lemma finite_C1_chart_partition:
  fixes X :: "'a set" and E :: "'i \<Rightarrow> 'a set"
  assumes finite: "finite F"
    and cover: "K \<subseteq> (\<Union>i\<in>F. Q i)"
    and cutoff: "\<And>i. i \<in> F \<Longrightarrow>
      \<exists>r L. continuous_on X r \<and>
        smooth r \<and> closed L \<and>
        {p\<in>X. r p \<noteq> (0::real)} \<subseteq> L \<and>
        L \<subseteq> E i \<and>
        (\<forall>p\<in>Q i. r p = 1) \<and>
        (\<forall>p. 0 \<le> r p \<and> r p \<le> 1)"
  obtains phi :: "'i \<Rightarrow> 'a \<Rightarrow> real" where
    "\<And>p. p \<in> K \<Longrightarrow> (\<Sum>i\<in>F. phi i p) = 1"
    "\<And>i. i \<in> F \<Longrightarrow> continuous_on X (phi i)"
    "\<And>i. i \<in> F \<Longrightarrow>
      smooth (phi i)"
    "\<And>i. i \<in> F \<Longrightarrow>
      \<exists>L. closed L \<and>
        {p\<in>X. phi i p \<noteq> 0} \<subseteq> L \<and>
        L \<subseteq> E i"
    "\<And>i p. i \<in> F \<Longrightarrow>
      0 \<le> phi i p \<and> phi i p \<le> 1"
proof -
  let ?P = "\<lambda>i z. continuous_on X (fst z) \<and>
    smooth (fst z) \<and>
    closed (snd z) \<and>
    {p\<in>X. fst z p \<noteq> (0::real)} \<subseteq> snd z \<and>
    snd z \<subseteq> E i \<and>
    (\<forall>p\<in>Q i. fst z p = 1) \<and>
    (\<forall>p. 0 \<le> fst z p \<and> fst z p \<le> 1)"
  let ?h = "\<lambda>i. SOME z. ?P i z"
  let ?r = "\<lambda>i. fst (?h i)"
  let ?L = "\<lambda>i. snd (?h i)"
  have data: "?P i (?h i)" if i: "i \<in> F" for i
  proof -
    have "\<exists>z. ?P i z"
      using cutoff[OF i] by auto
    then show ?thesis by (rule someI_ex)
  qed
  have C1r: "smooth (?r i)"
    if i: "i \<in> F" for i
    using data[OF i] by simp
  have contr: "continuous_on X (?r i)"
    if i: "i \<in> F" for i
    using data[OF i] by simp
  have boundsr: "0 \<le> ?r i p \<and> ?r i p \<le> 1"
    if i: "i \<in> F" for i p
    using data[OF i] by simp
  let ?A = "\<lambda>phi :: 'i \<Rightarrow> 'a \<Rightarrow> real.
    (\<forall>i\<in>F. smooth (phi i)) \<and>
    (\<forall>i\<in>F. continuous_on X (phi i)) \<and>
    (\<forall>i\<in>F. \<forall>p.
      phi i p \<noteq> 0 \<longrightarrow> ?r i p \<noteq> 0) \<and>
    (\<forall>i\<in>F. \<forall>p.
      0 \<le> phi i p \<and> phi i p \<le> 1) \<and>
    (\<forall>p. (\<Sum>i\<in>F. phi i p) =
      1 - (\<Prod>i\<in>F. (1 - ?r i p)))"
  let ?phi = "SOME phi. ?A phi"
  have ex: "\<exists>phi. ?A phi"
    by (rule finite_C1_partition_from_cutoffs
      [OF finite C1r boundsr contr])
  have props: "?A ?phi"
    by (rule someI_ex[OF ex])
  have props_support:
      "\<forall>i\<in>F. \<forall>p.
        ?phi i p \<noteq> 0 \<longrightarrow> ?r i p \<noteq> 0"
    using props by simp
  have unity: "(\<Sum>i\<in>F. ?phi i p) = 1"
    if p: "p \<in> K" for p
  proof -
    obtain i where i: "i \<in> F" "p \<in> Q i"
      using cover p by auto
    have one: "?r i p = 1"
      using data[OF i(1)] i(2) by auto
    have zero: "(\<Prod>j\<in>F. (1 - ?r j p)) = 0"
      by (rule prod_zero[OF finite])
         (use i(1) one in auto)
    show ?thesis using props zero by auto
  qed
  have local: "\<exists>L. closed L \<and>
      {p\<in>X. ?phi i p \<noteq> 0} \<subseteq> L \<and>
      L \<subseteq> E i"
    if i: "i \<in> F" for i
  proof -
    have nz: "?phi i p \<noteq> 0 \<Longrightarrow>
        ?r i p \<noteq> 0" for p
      using props_support i by auto
    have rsub: "{p\<in>X. ?r i p \<noteq> 0} \<subseteq> ?L i"
      using data[OF i] by simp
    have sub: "{p\<in>X. ?phi i p \<noteq> 0} \<subseteq> ?L i"
      using nz rsub by auto
    show ?thesis
      using sub data[OF i] by blast
  qed
  show thesis
    by (rule that[where phi="?phi"])
       (use props unity local in auto)
qed

end

end
