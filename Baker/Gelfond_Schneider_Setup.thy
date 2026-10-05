(*  Title:      Baker/Gelfond_Schneider_Setup.thy
    Author:     OpenAI Codex

Normalization data for a future standalone formalization of the
Gelfond-Schneider theorem. This mirrors the front end of the Lean development:
an alleged algebraic counterexample is reduced to a chosen logarithm together
with the basic irrational-scaling independence facts that the later auxiliary
function argument will need.
*)

theory Gelfond_Schneider_Setup
  imports Gelfond_Schneider_Preliminaries
begin

declare [[apply_timeout = 10]]

section \<open>Gelfond-Schneider Setup\<close>

record gelfond_schneider_data =
  gs_a :: complex
  gs_b :: complex
  gs_w :: complex
  gs_z :: complex

definition is_gelfond_schneider_data :: "gelfond_schneider_data \<Rightarrow> bool"
  where
    "is_gelfond_schneider_data d \<longleftrightarrow>
      algebraic (gs_a d) \<and>
      algebraic (gs_b d) \<and>
      algebraic (gs_w d) \<and>
      gs_a d \<noteq> 0 \<and>
      gs_a d \<noteq> 1 \<and>
      gs_b d \<notin> \<rat> \<and>
      gs_z d \<in> log_values (gs_a d) \<and>
      gs_b d * gs_z d \<in> log_values (gs_w d)"

lemma exists_int_mul_algebraic_int:
  fixes x :: complex
  assumes "algebraic x"
  shows "\<exists>c :: int. c \<noteq> 0 \<and> algebraic_int (of_int c * x)"
proof -
  from assms obtain p :: "int poly"
    where px: "ipoly p x = 0" and p_nz: "p \<noteq> 0"
    by (auto simp: algebraic_altdef_ipoly)
  define c :: int where "c = Polynomial.lead_coeff p"
  have c_nz: "c \<noteq> 0"
    unfolding c_def using p_nz by auto
  have "algebraic_int (of_int c * x)"
    unfolding c_def by (rule algebraic_imp_algebraic_int[OF px p_nz])
  with c_nz show ?thesis
    by blast
qed

definition gs_c0 :: "complex \<Rightarrow> int"
  where "gs_c0 x = (SOME c. c \<noteq> 0 \<and> algebraic_int (of_int c * x))"

lemma gs_c0_nonzero:
  assumes "algebraic x"
  shows "gs_c0 x \<noteq> 0"
proof -
  have ex: "\<exists>c :: int. c \<noteq> 0 \<and> algebraic_int (of_int c * x)"
    by (rule exists_int_mul_algebraic_int[OF assms])
  have "gs_c0 x \<noteq> 0 \<and> algebraic_int (of_int (gs_c0 x) * x)"
    unfolding gs_c0_def by (rule someI_ex[OF ex])
  then show ?thesis
    by blast
qed

lemma gs_c0_algebraic_int:
  assumes "algebraic x"
  shows "algebraic_int (of_int (gs_c0 x) * x)"
proof -
  have ex: "\<exists>c :: int. c \<noteq> 0 \<and> algebraic_int (of_int c * x)"
    by (rule exists_int_mul_algebraic_int[OF assms])
  have "gs_c0 x \<noteq> 0 \<and> algebraic_int (of_int (gs_c0 x) * x)"
    unfolding gs_c0_def by (rule someI_ex[OF ex])
  then show ?thesis
    by blast
qed

definition gs_c1 :: "gelfond_schneider_data \<Rightarrow> int"
  where "gs_c1 d = abs (gs_c0 (gs_a d) * gs_c0 (gs_b d) * gs_c0 (gs_w d))"

lemma algebraic_int_of_int_scale [intro]:
  assumes "algebraic_int (x :: complex)"
  shows "algebraic_int (of_int n * x)"
  using assms by auto

lemma algebraic_int_abs_scale:
  fixes x :: complex
  assumes "algebraic_int (of_int c * x)"
  shows "algebraic_int (of_int (abs c) * x)"
proof (cases "0 \<le> c")
  case True
  then show ?thesis
    using assms by simp
next
  case False
  have "algebraic_int (- (of_int c * x))"
    using assms by simp
  with False show ?thesis
    by (simp add: algebra_simps)
qed

lemma gelfond_schneider_data_a_exp:
  assumes d: "is_gelfond_schneider_data d"
  shows "exp (gs_z d) = gs_a d"
  using d unfolding is_gelfond_schneider_data_def by simp

lemma gelfond_schneider_data_w_exp:
  assumes d: "is_gelfond_schneider_data d"
  shows "exp (gs_b d * gs_z d) = gs_w d"
  using d unfolding is_gelfond_schneider_data_def by simp

lemma gelfond_schneider_data_w_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  shows "gs_w d \<noteq> 0"
proof -
  have "gs_b d * gs_z d \<in> log_values (gs_w d)"
    using d unfolding is_gelfond_schneider_data_def by blast
  then show ?thesis
    by auto
qed

lemma gelfond_schneider_data_b_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  shows "gs_b d \<noteq> 0"
proof
  assume "gs_b d = 0"
  moreover have "(0 :: complex) \<in> \<rat>"
    by simp
  ultimately show False
    using d unfolding is_gelfond_schneider_data_def by simp
qed

lemma gelfond_schneider_data_z_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  shows "gs_z d \<noteq> 0"
proof
  assume z0: "gs_z d = 0"
  have "gs_z d \<in> log_values (gs_a d)"
    using d unfolding is_gelfond_schneider_data_def by blast
  then have "gs_a d = 1"
    using z0 by simp
  with d show False
    unfolding is_gelfond_schneider_data_def by blast
qed

lemma gelfond_schneider_data_z_transcendental:
  assumes d: "is_gelfond_schneider_data d"
  shows "\<not> algebraic (gs_z d)"
proof -
  have alg_a: "algebraic (gs_a d)"
    using d unfolding is_gelfond_schneider_data_def by blast
  have a_nz: "gs_a d \<noteq> 0"
    using d unfolding is_gelfond_schneider_data_def by blast
  have a_not1: "gs_a d \<noteq> 1"
    using d unfolding is_gelfond_schneider_data_def by blast
  have log_z: "gs_z d \<in> log_values (gs_a d)"
    using d unfolding is_gelfond_schneider_data_def by blast
  show ?thesis
    by (rule algebraic_log_value_transcendental[OF alg_a a_nz a_not1 log_z])
qed

lemma gelfond_schneider_data_qindep:
  assumes d: "is_gelfond_schneider_data d"
  shows "rat_linearly_independent [gs_z d, gs_b d * gs_z d]"
proof -
  have z_nz: "gs_z d \<noteq> 0"
    by (rule gelfond_schneider_data_z_nonzero[OF d])
  have b_irr: "gs_b d \<notin> \<rat>"
    using d unfolding is_gelfond_schneider_data_def by blast
  show ?thesis
    by (rule rat_linearly_independent_pair_scale) (use z_nz b_irr in auto)
qed

lemma gelfond_schneider_data_c1_ge1:
  assumes d: "is_gelfond_schneider_data d"
  shows "1 \<le> gs_c1 d"
proof -
  have nz: "gs_c0 (gs_a d) * gs_c0 (gs_b d) * gs_c0 (gs_w d) \<noteq> 0"
  proof
    assume "gs_c0 (gs_a d) * gs_c0 (gs_b d) * gs_c0 (gs_w d) = 0"
    then have disj: "gs_c0 (gs_a d) = 0 \<or> gs_c0 (gs_b d) = 0 \<or> gs_c0 (gs_w d) = 0"
      by auto
    have alg_a: "algebraic (gs_a d)"
      using d unfolding is_gelfond_schneider_data_def by blast
    have alg_b: "algebraic (gs_b d)"
      using d unfolding is_gelfond_schneider_data_def by blast
    have alg_w: "algebraic (gs_w d)"
      using d unfolding is_gelfond_schneider_data_def by blast
    moreover have "gs_c0 (gs_a d) \<noteq> 0"
      by (rule gs_c0_nonzero[OF alg_a])
    moreover have "gs_c0 (gs_b d) \<noteq> 0"
      by (rule gs_c0_nonzero[OF alg_b])
    moreover have "gs_c0 (gs_w d) \<noteq> 0"
      by (rule gs_c0_nonzero[OF alg_w])
    from disj show False
    proof
      assume "gs_c0 (gs_a d) = 0"
      moreover have "gs_c0 (gs_a d) \<noteq> 0"
        by (rule gs_c0_nonzero[OF alg_a])
      ultimately show False
        by contradiction
    next
      assume "gs_c0 (gs_b d) = 0 \<or> gs_c0 (gs_w d) = 0"
      then show False
      proof
        assume "gs_c0 (gs_b d) = 0"
        moreover have "gs_c0 (gs_b d) \<noteq> 0"
          by (rule gs_c0_nonzero[OF alg_b])
        ultimately show False
          by contradiction
      next
        assume "gs_c0 (gs_w d) = 0"
        moreover have "gs_c0 (gs_w d) \<noteq> 0"
          by (rule gs_c0_nonzero[OF alg_w])
        ultimately show False
          by contradiction
      qed
    qed
  qed
  have "0 < abs (gs_c0 (gs_a d) * gs_c0 (gs_b d) * gs_c0 (gs_w d))"
    using nz by simp
  then show ?thesis
    unfolding gs_c1_def by linarith
qed

lemma gelfond_schneider_data_c1_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  shows "gs_c1 d \<noteq> 0"
  using gelfond_schneider_data_c1_ge1[OF d] by linarith

lemma gelfond_schneider_data_c1_a_algebraic_int:
  assumes d: "is_gelfond_schneider_data d"
  shows "algebraic_int (of_int (gs_c1 d) * gs_a d)"
proof -
  have alg_a: "algebraic (gs_a d)"
    using d unfolding is_gelfond_schneider_data_def by blast
  have "algebraic_int (of_int (gs_c0 (gs_a d) * gs_c0 (gs_b d) * gs_c0 (gs_w d)) * gs_a d)"
  proof -
    have "algebraic_int (of_int (gs_c0 (gs_a d)) * gs_a d)"
      by (rule gs_c0_algebraic_int[OF alg_a])
    then have h1: "algebraic_int (of_int (gs_c0 (gs_b d)) * (of_int (gs_c0 (gs_a d)) * gs_a d))"
      by (rule algebraic_int_of_int_scale)
    from h1 have "algebraic_int (of_int (gs_c0 (gs_w d)) *
      (of_int (gs_c0 (gs_b d)) * (of_int (gs_c0 (gs_a d)) * gs_a d)))"
      by (rule algebraic_int_of_int_scale)
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  then show ?thesis
    unfolding gs_c1_def by (rule algebraic_int_abs_scale)
qed

lemma gelfond_schneider_data_c1_b_algebraic_int:
  assumes d: "is_gelfond_schneider_data d"
  shows "algebraic_int (of_int (gs_c1 d) * gs_b d)"
proof -
  have alg_b: "algebraic (gs_b d)"
    using d unfolding is_gelfond_schneider_data_def by blast
  have "algebraic_int (of_int (gs_c0 (gs_a d) * gs_c0 (gs_b d) * gs_c0 (gs_w d)) * gs_b d)"
  proof -
    have "algebraic_int (of_int (gs_c0 (gs_b d)) * gs_b d)"
      by (rule gs_c0_algebraic_int[OF alg_b])
    then have h1: "algebraic_int (of_int (gs_c0 (gs_a d)) * (of_int (gs_c0 (gs_b d)) * gs_b d))"
      by (rule algebraic_int_of_int_scale)
    from h1 have "algebraic_int (of_int (gs_c0 (gs_w d)) *
      (of_int (gs_c0 (gs_a d)) * (of_int (gs_c0 (gs_b d)) * gs_b d)))"
      by (rule algebraic_int_of_int_scale)
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  then show ?thesis
    unfolding gs_c1_def by (rule algebraic_int_abs_scale)
qed

lemma gelfond_schneider_data_c1_w_algebraic_int:
  assumes d: "is_gelfond_schneider_data d"
  shows "algebraic_int (of_int (gs_c1 d) * gs_w d)"
proof -
  have alg_w: "algebraic (gs_w d)"
    using d unfolding is_gelfond_schneider_data_def by blast
  have "algebraic_int (of_int (gs_c0 (gs_a d) * gs_c0 (gs_b d) * gs_c0 (gs_w d)) * gs_w d)"
  proof -
    have "algebraic_int (of_int (gs_c0 (gs_w d)) * gs_w d)"
      by (rule gs_c0_algebraic_int[OF alg_w])
    then have h1: "algebraic_int (of_int (gs_c0 (gs_b d)) * (of_int (gs_c0 (gs_w d)) * gs_w d))"
      by (rule algebraic_int_of_int_scale)
    from h1 have "algebraic_int (of_int (gs_c0 (gs_a d)) *
      (of_int (gs_c0 (gs_b d)) * (of_int (gs_c0 (gs_w d)) * gs_w d)))"
      by (rule algebraic_int_of_int_scale)
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  then show ?thesis
    unfolding gs_c1_def by (rule algebraic_int_abs_scale)
qed

theorem exists_gelfond_schneider_data_of_counterexample:
  fixes a b w :: complex
  assumes algs: "algebraic a" "algebraic b" "algebraic w"
  assumes nontriv: "a \<noteq> 0" "a \<noteq> 1"
  assumes b_irr: "b \<notin> \<rat>"
  assumes wmem: "w \<in> power_values a b"
  shows "\<exists>d. is_gelfond_schneider_data d"
proof -
  from power_value_log_valueE[OF wmem]
  obtain z where z: "z \<in> log_values a" "b * z \<in> log_values w" .
  define d :: gelfond_schneider_data
    where "d = \<lparr>gs_a = a, gs_b = b, gs_w = w, gs_z = z\<rparr>"
  have "is_gelfond_schneider_data d"
    unfolding d_def is_gelfond_schneider_data_def
    using algs nontriv b_irr z by auto
  then show ?thesis
    by blast
qed

theorem gelfond_schneider_counterexample_witness:
  fixes a b w :: complex
  assumes algs: "algebraic a" "algebraic b" "algebraic w"
  assumes nontriv: "a \<noteq> 0" "a \<noteq> 1"
  assumes b_irr: "b \<notin> \<rat>"
  assumes wmem: "w \<in> power_values a b"
  obtains z where
    "z \<in> log_values a"
    "b * z \<in> log_values w"
    "\<not> algebraic z"
    "rat_linearly_independent [z, b * z]"
proof -
  from power_value_log_valueE[OF wmem]
  obtain z where z: "z \<in> log_values a" "b * z \<in> log_values w" .
  have z_trans: "\<not> algebraic z"
    by (rule algebraic_log_value_transcendental[OF algs(1) nontriv z(1)])
  have z_nz: "z \<noteq> 0"
    using nontriv(2) z(1) by auto
  have indep: "rat_linearly_independent [z, b * z]"
    by (rule rat_linearly_independent_pair_scale) (use z_nz b_irr in auto)
  show thesis
    by (rule that[OF z z_trans indep])
qed

end
