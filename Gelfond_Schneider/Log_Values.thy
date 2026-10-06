(*  Title:      Gelfond_Schneider/Log_Values.thy
    Author:     OpenAI Codex

Set-valued complex logarithms and powers for branch-explicit
Gelfond-Schneider statements.
*)

theory Log_Values
  imports "HOL-Analysis.Complex_Transcendental"
begin

section \<open>Set-Valued Logarithms and Powers\<close>

definition log_values :: "complex \<Rightarrow> complex set"
  where "log_values a = {z. exp z = a}"

definition power_values :: "complex \<Rightarrow> complex \<Rightarrow> complex set"
  where "power_values a b = {w. \<exists>z\<in>log_values a. w = exp (b * z)}"

lemma mem_log_values_iff [simp]:
  "z \<in> log_values a \<longleftrightarrow> exp z = a"
  by (simp add: log_values_def)

lemma mem_power_values_iff:
  "w \<in> power_values a b \<longleftrightarrow> (\<exists>z. z \<in> log_values a \<and> w = exp (b * z))"
  by (auto simp: power_values_def)

lemma zero_in_log_values_iff [simp]:
  "0 \<in> log_values a \<longleftrightarrow> a = 1"
  by (simp add: log_values_def)

lemma Ln_in_log_values [intro]:
  assumes "a \<noteq> 0"
  shows "Ln a \<in> log_values a"
  using assms by (simp add: log_values_def)

lemma log_values_nonempty_iff [simp]:
  "log_values a \<noteq> {} \<longleftrightarrow> a \<noteq> 0"
proof
  assume "log_values a \<noteq> {}"
  then obtain z where "z \<in> log_values a"
    by blast
  then show "a \<noteq> 0"
    by auto
next
  assume "a \<noteq> 0"
  then show "log_values a \<noteq> {}"
    using Ln_in_log_values by blast
qed

lemma power_values_nonempty_iff [simp]:
  "power_values a b \<noteq> {} \<longleftrightarrow> a \<noteq> 0"
proof
  assume "power_values a b \<noteq> {}"
  then obtain w where "w \<in> power_values a b"
    by blast
  then obtain z where "z \<in> log_values a"
    by (auto simp: power_values_def)
  then show "a \<noteq> 0"
    by auto
next
  assume "a \<noteq> 0"
  then have "exp (b * Ln a) \<in> power_values a b"
    by (auto simp: power_values_def)
  then show "power_values a b \<noteq> {}"
    by blast
qed

lemma principal_power_value_mem [intro]:
  assumes "a \<noteq> 0"
  shows "exp (b * Ln a) \<in> power_values a b"
  using assms by (auto simp: power_values_def)

lemma power_values_nonzero:
  assumes "w \<in> power_values a b"
  shows "w \<noteq> 0"
  using assms by (auto simp: power_values_def)

end
