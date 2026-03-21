theory Stopped_Value_Integration
  imports "Doob_Convergence.Stopping_Time"
begin

text \<open>Integrability of stopped values and stopped processes, and the telescoping identity
  for differences of stopped values. These results bridge the gap between the existing
  AFP theories (Martingales, Doob\_Convergence) and the optional stopping theorem.\<close>

context nat_sigma_finite_filtered_measure
begin

subsection \<open>Stopped value as a sum of indicators\<close>

text \<open>A stopped value with a bounded stopping time can be written as a finite sum of indicators.\<close>

lemma stopped_value_eq_sum:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> 'b :: real_vector"
  assumes \<tau>_st: "stopping_time \<tau>" and \<tau>_bnd: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<tau> \<omega> \<le> N"
  assumes \<omega>_in: "\<omega> \<in> space M"
  shows "stopped_value X \<tau> \<omega> = (\<Sum>i\<le>N. indicator {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> *\<^sub>R X i \<omega>)"
proof -
  from \<tau>_bnd[OF \<omega>_in] have \<tau>_le: "\<tau> \<omega> \<le> N" .
  then have \<tau>_mem: "\<tau> \<omega> \<in> {..N}" by simp
  from \<omega>_in have ind_\<tau>: "indicator {\<omega> \<in> space M. \<tau> \<omega> = \<tau> \<omega>} \<omega> = (1::real)"
    by (simp add: indicator_def)
  have ind_ne: "\<And>i. i \<noteq> \<tau> \<omega> \<Longrightarrow> indicator {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> = (0::real)"
    by (simp add: indicator_def)
  have sum_split: "(\<Sum>i\<le>N. indicator {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> *\<^sub>R X i \<omega>) =
    indicator {\<omega> \<in> space M. \<tau> \<omega> = \<tau> \<omega>} \<omega> *\<^sub>R X (\<tau> \<omega>) \<omega> +
    (\<Sum>i \<in> {..N} - {\<tau> \<omega>}. indicator {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> *\<^sub>R X i \<omega>)"
    using \<omega>_in \<tau>_le
    by (subst sum.remove [where x = "\<tau> \<omega>"]) simp_all
  have sum_rest: "(\<Sum>i \<in> {..N} - {\<tau> \<omega>}. indicator {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> *\<^sub>R X i \<omega>) = 0"
    by simp
  have "stopped_value X \<tau> \<omega> = X (\<tau> \<omega>) \<omega>"
    by (simp add: stopped_value_def)
  also have "\<dots> = 1 *\<^sub>R X (\<tau> \<omega>) \<omega>" by (metis (full_types) scale_one)
  also have "\<dots> = indicator {\<omega> \<in> space M. \<tau> \<omega> = \<tau> \<omega>} \<omega> *\<^sub>R X (\<tau> \<omega>) \<omega>"
    using ind_\<tau> by simp
  also have "\<dots> = indicator {\<omega> \<in> space M. \<tau> \<omega> = \<tau> \<omega>} \<omega> *\<^sub>R X (\<tau> \<omega>) \<omega> + 0"
    by simp
  also have "\<dots> = indicator {\<omega> \<in> space M. \<tau> \<omega> = \<tau> \<omega>} \<omega> *\<^sub>R X (\<tau> \<omega>) \<omega> +
    (\<Sum>i \<in> {..N} - {\<tau> \<omega>}. indicator {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> *\<^sub>R X i \<omega>)"
    using sum_rest by simp
  also have "\<dots> = (\<Sum>i\<le>N. indicator {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> *\<^sub>R X i \<omega>)"
    using sum_split by simp
  finally show ?thesis .
qed

subsection \<open>Telescoping identity for stopped values\<close>

text \<open>The difference of stopped values can be expressed as a sum of indicator-weighted increments.
  This corresponds to @{text stoppedValue_sub_eq_sum'} in Mathlib.\<close>

lemma stopped_value_sub_eq_sum:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "stopping_time \<tau>" "stopping_time \<pi>" "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<tau> \<omega> \<le> \<pi> \<omega>"
    and "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<pi> \<omega> \<le> N"
  shows "(\<lambda>\<omega>. stopped_value X \<pi> \<omega> - stopped_value X \<tau> \<omega>) =
    (\<lambda>\<omega>. \<Sum>i\<le>N. indicator {\<omega> \<in> space M. \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega>} \<omega> * (X (Suc i) \<omega> - X i \<omega>))"
  sorry

subsection \<open>Integrability of stopped values\<close>

text \<open>If each @{term "X i"} is integrable and the stopping time is bounded, then the stopped value
  is integrable. This corresponds to @{text integrable_stoppedValue} in Mathlib.\<close>

lemma integrable_stopped_value:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "stopping_time \<tau>" "\<And>i. integrable M (X i)" "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<tau> \<omega> \<le> N"
  shows "integrable M (stopped_value X \<tau>)"
  sorry

subsection \<open>Stopped process\<close>

text \<open>The stopped process @{text "X\<^sup>\<tau>"} is defined as @{text "X (min i \<tau>)"}.\<close>

definition stopped_process :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b" where
  "stopped_process X \<tau> i \<omega> = X (min i (\<tau> \<omega>)) \<omega>"

lemma stopped_process_eq_stopped_value:
  "stopped_process X \<tau> i = stopped_value X (\<lambda>\<omega>. min i (\<tau> \<omega>))"
  unfolding stopped_process_def stopped_value_def by simp

lemma integrable_stopped_process:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "stopping_time \<tau>" "\<And>i. integrable M (X i)"
  shows "integrable M (stopped_process X \<tau> n)"
  sorry

end

end
