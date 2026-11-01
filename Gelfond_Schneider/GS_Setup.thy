(*  Title:      Gelfond_Schneider/GS_Setup.thy
    Author:     OpenAI Codex

Normalization data for the Gelfond-Schneider theorem. An alleged algebraic
counterexample is reduced to a chosen logarithm for the auxiliary-function
argument.
*)

theory GS_Setup
  imports GS_Preliminaries
begin

section \<open>Gelfond-Schneider Setup\<close>

locale gs_normalized_data =
  fixes alpha beta omega zeta :: complex
  assumes alpha_alg: "algebraic alpha"
    and beta_alg: "algebraic beta"
    and omega_alg: "algebraic omega"
    and alpha_nonzero: "alpha \<noteq> 0"
    and alpha_nonunit: "alpha \<noteq> 1"
    and beta_irrational: "beta \<notin> \<rat>"
    and zeta_log_alpha: "zeta \<in> log_values alpha"
    and beta_zeta_log_omega: "beta * zeta \<in> log_values omega"

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

lemma algebraic_int_of_int_scale [intro]:
  assumes "algebraic_int (x :: complex)"
  shows "algebraic_int (of_int n * x)"
  using assms by auto

lemma algebraic_int_abs_scale:
  fixes x :: complex
  assumes "algebraic_int (of_int c * x)"
  shows "algebraic_int (of_int (\<bar>c\<bar>) * x)"
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

context gs_normalized_data
begin

definition gs_c1 :: int
  where "gs_c1 = \<bar>gs_c0 alpha * gs_c0 beta * gs_c0 omega\<bar>"

lemma gelfond_schneider_data_z_nonzero:
  "zeta \<noteq> 0"
  using alpha_nonunit zeta_log_alpha by auto

lemma gelfond_schneider_data_z_transcendental:
  "\<not> algebraic zeta"
  by (rule algebraic_log_value_transcendental
    [OF alpha_alg alpha_nonzero alpha_nonunit zeta_log_alpha])

lemma gelfond_schneider_data_c1_ge1:
  shows "1 \<le> gs_c1"
proof -
  have nz: "gs_c0 (alpha) * gs_c0 (beta) * gs_c0 (omega) \<noteq> 0"
  proof
    assume "gs_c0 (alpha) * gs_c0 (beta) * gs_c0 (omega) = 0"
    then have disj: "gs_c0 (alpha) = 0 \<or> gs_c0 (beta) = 0 \<or> gs_c0 (omega) = 0"
      by auto
    have alg_a: "algebraic (alpha)"
      by (rule alpha_alg)
    have alg_b: "algebraic (beta)"
      by (rule beta_alg)
    have alg_w: "algebraic (omega)"
      by (rule omega_alg)
    moreover have "gs_c0 (alpha) \<noteq> 0"
      by (rule gs_c0_nonzero[OF alg_a])
    moreover have "gs_c0 (beta) \<noteq> 0"
      by (rule gs_c0_nonzero[OF alg_b])
    moreover have "gs_c0 (omega) \<noteq> 0"
      by (rule gs_c0_nonzero[OF alg_w])
    from disj show False
    proof
      assume "gs_c0 (alpha) = 0"
      moreover have "gs_c0 (alpha) \<noteq> 0"
        by (rule gs_c0_nonzero[OF alg_a])
      ultimately show False
        by contradiction
    next
      assume "gs_c0 (beta) = 0 \<or> gs_c0 (omega) = 0"
      then show False
      proof
        assume "gs_c0 (beta) = 0"
        moreover have "gs_c0 (beta) \<noteq> 0"
          by (rule gs_c0_nonzero[OF alg_b])
        ultimately show False
          by contradiction
      next
        assume "gs_c0 (omega) = 0"
        moreover have "gs_c0 (omega) \<noteq> 0"
          by (rule gs_c0_nonzero[OF alg_w])
        ultimately show False
          by contradiction
      qed
    qed
  qed
  have "0 < \<bar>gs_c0 (alpha) * gs_c0 (beta) * gs_c0 (omega)\<bar>"
    using nz by simp
  then show ?thesis
    unfolding gs_c1_def by linarith
qed

lemma gelfond_schneider_data_c1_nonzero:
  shows "gs_c1 \<noteq> 0"
  using gelfond_schneider_data_c1_ge1 by linarith

lemma gelfond_schneider_data_c1_a_algebraic_int:
  shows "algebraic_int (of_int (gs_c1) * alpha)"
proof -
  have alg_a: "algebraic (alpha)"
    by (rule alpha_alg)
  have "algebraic_int (of_int (gs_c0 (alpha) * gs_c0 (beta) * gs_c0 (omega)) * alpha)"
  proof -
    have "algebraic_int (of_int (gs_c0 (alpha)) * alpha)"
      by (rule gs_c0_algebraic_int[OF alg_a])
    then have h1: "algebraic_int (of_int (gs_c0 (beta)) * (of_int (gs_c0 (alpha)) * alpha))"
      by (rule algebraic_int_of_int_scale)
    from h1 have "algebraic_int (of_int (gs_c0 (omega)) *
      (of_int (gs_c0 (beta)) * (of_int (gs_c0 (alpha)) * alpha)))"
      by (rule algebraic_int_of_int_scale)
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  then show ?thesis
    unfolding gs_c1_def by (rule algebraic_int_abs_scale)
qed

lemma gelfond_schneider_data_c1_b_algebraic_int:
  shows "algebraic_int (of_int (gs_c1) * beta)"
proof -
  have alg_b: "algebraic (beta)"
    by (rule beta_alg)
  have "algebraic_int (of_int (gs_c0 (alpha) * gs_c0 (beta) * gs_c0 (omega)) * beta)"
  proof -
    have "algebraic_int (of_int (gs_c0 (beta)) * beta)"
      by (rule gs_c0_algebraic_int[OF alg_b])
    then have h1: "algebraic_int (of_int (gs_c0 (alpha)) * (of_int (gs_c0 (beta)) * beta))"
      by (rule algebraic_int_of_int_scale)
    from h1 have "algebraic_int (of_int (gs_c0 (omega)) *
      (of_int (gs_c0 (alpha)) * (of_int (gs_c0 (beta)) * beta)))"
      by (rule algebraic_int_of_int_scale)
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  then show ?thesis
    unfolding gs_c1_def by (rule algebraic_int_abs_scale)
qed

lemma gelfond_schneider_data_c1_w_algebraic_int:
  shows "algebraic_int (of_int (gs_c1) * omega)"
proof -
  have alg_w: "algebraic (omega)"
    by (rule omega_alg)
  have "algebraic_int (of_int (gs_c0 (alpha) * gs_c0 (beta) * gs_c0 (omega)) * omega)"
  proof -
    have "algebraic_int (of_int (gs_c0 (omega)) * omega)"
      by (rule gs_c0_algebraic_int[OF alg_w])
    then have h1: "algebraic_int (of_int (gs_c0 (beta)) * (of_int (gs_c0 (omega)) * omega))"
      by (rule algebraic_int_of_int_scale)
    from h1 have "algebraic_int (of_int (gs_c0 (alpha)) *
      (of_int (gs_c0 (beta)) * (of_int (gs_c0 (omega)) * omega)))"
      by (rule algebraic_int_of_int_scale)
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  then show ?thesis
    unfolding gs_c1_def by (rule algebraic_int_abs_scale)
qed

end

end
