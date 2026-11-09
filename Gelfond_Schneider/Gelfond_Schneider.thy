(*  Title:      Gelfond_Schneider/Gelfond_Schneider.thy
    Author:     OpenAI Codex

The public Gelfond-Schneider theorem and its principal corollaries.
*)

theory Gelfond_Schneider
  imports Power_Basis_Norm_Direct
begin

section \<open>Gelfond-Schneider\<close>

text \<open>
The normalized counterexample contradiction follows from the finite normal
power-basis construction, a fixed exponential denominator for its system
matrix, and the verified field-norm estimate. The public transcendence
statement follows from the normalized counterexample reduction.
\<close>

theorem gelfond_schneider:
  fixes a b w :: complex
  assumes "algebraic a"
  assumes "algebraic b"
  assumes "a \<noteq> 0"
  assumes "a \<noteq> 1"
  assumes "b \<notin> \<rat>"
  assumes "w \<in> power_values a b"
  shows "\<not> algebraic w"
proof
  assume alg_w: "algebraic w"
  obtain zeta where zeta_log: "zeta \<in> log_values a"
    and beta_zeta_log: "b * zeta \<in> log_values w"
    by (rule power_value_log_valueE[OF assms(6)])
  interpret GS: gs_normalized_data a b w zeta
    by unfold_locales (use assms alg_w zeta_log beta_zeta_log in auto)
  show False
    by (rule GS.normalized_data_contradiction)
qed

section \<open>Corollaries\<close>

corollary gelfond_schneider_principal:
  fixes a b :: complex
  assumes "algebraic a"
  assumes "algebraic b"
  assumes "a \<noteq> 0"
  assumes "a \<noteq> 1"
  assumes "b \<notin> \<rat>"
  shows "\<not> algebraic (exp (b * Ln a))"
  by (rule gelfond_schneider[of a b "exp (b * Ln a)"]) (use assms in auto)

corollary gelfond_schneider_real:
  fixes a b :: real
  assumes "algebraic a"
  assumes "algebraic b"
  assumes "0 \<le> a"
  assumes "a \<noteq> 0"
  assumes "a \<noteq> 1"
  assumes "b \<notin> \<rat>"
  shows "\<not> algebraic (a powr b)"
proof
  assume alg: "algebraic (a powr b)"
  have algc: "algebraic (of_real (a powr b) :: complex)"
    using alg by simp
  have wmem: "of_real (a powr b) \<in> power_values (of_real a) (of_real b)"
  proof -
    have eq: "of_real (a powr b) = exp (of_real b * Ln (of_real a))"
      using \<open>0 \<le> a\<close> \<open>a \<noteq> 0\<close> by (metis of_real_hom.hom_0 powr_def powr_of_real)
    have "exp (of_real b * Ln (of_real a)) \<in> power_values (of_real a) (of_real b)"
      using \<open>a \<noteq> 0\<close> by (simp add: principal_power_value_mem)
    with eq show ?thesis
      by simp
  qed
  have "\<not> algebraic (of_real (a powr b) :: complex)"
    by (rule gelfond_schneider[of "of_real a" "of_real b" "of_real (a powr b)"])
       (use assms algc wmem in auto)
  with algc show False
    by contradiction
qed

end
