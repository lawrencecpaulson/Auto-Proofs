(*  Title:      Baker/Gelfond_Schneider.thy
    Author:     OpenAI Codex

Standalone theorem target for the Gelfond-Schneider formalization.
*)

theory Gelfond_Schneider
  imports
    Gelfond_Schneider_Arithmetic
    Gelfond_Schneider_Direct
    Gelfond_Schneider_Direct_Target
    Gelfond_Schneider_Number_Field_Target
    Gelfond_Schneider_Order
    Gelfond_Schneider_Statement_Shell
    Gelfond_Schneider_Power_Basis_Norm_Direct
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

end
