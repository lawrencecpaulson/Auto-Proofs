theory Smooth_Cutoff
  imports Halfline_Forms "HOL-Analysis.Real_Analytic"
begin

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

end
