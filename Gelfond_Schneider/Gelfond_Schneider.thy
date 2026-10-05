(*  Title:      Gelfond_Schneider/Gelfond_Schneider.thy
    Author:     OpenAI Codex

Standalone theorem target for the Gelfond-Schneider formalization.
*)

theory Gelfond_Schneider
  imports Gelfond_Schneider_Power_Basis_Norm_Direct
begin

section \<open>Standalone Gelfond-Schneider\<close>

text \<open>
The normalized counterexample contradiction follows from the finite normal
power-basis construction, a fixed exponential denominator for its system
matrix, and the verified field-norm estimate. The public transcendence
statement follows from the normalized counterexample reduction.
\<close>

theorem no_gelfond_schneider_data:
  assumes "is_gelfond_schneider_data d"
  shows False
  by (rule no_gelfond_schneider_data_scaled[OF assms])

lemma gelfond_schneider_of_no_data:
  fixes a b w :: complex
  assumes no_data: "\<And>d. is_gelfond_schneider_data d \<Longrightarrow> False"
  assumes "algebraic a"
  assumes "algebraic b"
  assumes "a \<noteq> 0"
  assumes "a \<noteq> 1"
  assumes "b \<notin> \<rat>"
  assumes "w \<in> power_values a b"
  shows "\<not> algebraic w"
proof
  assume alg_w: "algebraic w"
  from exists_gelfond_schneider_data_of_counterexample[OF assms(2,3) alg_w assms(4-7)]
  obtain d where "is_gelfond_schneider_data d"
    by blast
  then show False
    by (rule no_data)
qed

theorem gelfond_schneider:
  fixes a b w :: complex
  assumes "algebraic a"
  assumes "algebraic b"
  assumes "a \<noteq> 0"
  assumes "a \<noteq> 1"
  assumes "b \<notin> \<rat>"
  assumes "w \<in> power_values a b"
  shows "\<not> algebraic w"
  by (rule gelfond_schneider_of_no_data[OF no_gelfond_schneider_data]) (use assms in auto)

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
    proof -
      have "of_real (a powr b) = of_real a powr (of_real b :: complex)"
        using assms(3) by (simp add: powr_of_real)
      also have "... = exp (of_real b * Ln (of_real a))"
        using assms(4) by (simp add: powr_def)
      finally show ?thesis .
    qed
    have nz: "of_real a \<noteq> (0 :: complex)"
      using assms(4) by simp
    have "exp (of_real b * Ln (of_real a)) \<in> power_values (of_real a) (of_real b)"
      by (rule principal_power_value_mem[OF nz])
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
