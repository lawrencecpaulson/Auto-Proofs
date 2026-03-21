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
  assumes \<tau>_st: "stopping_time \<tau>" and \<pi>_st: "stopping_time \<pi>"
    and le: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<tau> \<omega> \<le> \<pi> \<omega>"
    and bnd: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<pi> \<omega> \<le> N"
    and \<omega>_in: "\<omega> \<in> space M"
  shows "stopped_value X \<pi> \<omega> - stopped_value X \<tau> \<omega> =
    (\<Sum>i\<le>N. indicator {\<omega> \<in> space M. \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega>} \<omega> * (X (Suc i) \<omega> - X i \<omega>))"
proof -
  have \<tau>_le_\<pi>: "\<tau> \<omega> \<le> \<pi> \<omega>" using le[OF \<omega>_in] .
  have \<pi>_le: "\<pi> \<omega> \<le> N" using bnd[OF \<omega>_in] .
  have "(\<Sum>i\<le>N. indicator {\<omega> \<in> space M. \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega>} \<omega> * (X (Suc i) \<omega> - X i \<omega>)) =
    (\<Sum>i\<in>{..N}. if \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega> then X (Suc i) \<omega> - X i \<omega> else 0)"
    using \<omega>_in by (intro sum.cong) (auto simp: indicator_def)
  also have "\<dots> = (\<Sum>i\<in>{\<tau> \<omega>..<\<pi> \<omega>}. X (Suc i) \<omega> - X i \<omega>)"
  proof (rule sum.mono_neutral_cong_right)
    show "finite {..N}" by simp
    show "{\<tau> \<omega>..<\<pi> \<omega>} \<subseteq> {..N}" using \<pi>_le by auto
    show "\<forall>i\<in>{..N} - {\<tau> \<omega>..<\<pi> \<omega>}. (if \<tau> \<omega> \<le> i \<and> i < \<pi> \<omega> then X (Suc i) \<omega> - X i \<omega> else 0) = 0"
      by auto
    show "\<And>x. x \<in> {\<tau> \<omega>..<\<pi> \<omega>} \<Longrightarrow> (if \<tau> \<omega> \<le> x \<and> x < \<pi> \<omega> then X (Suc x) \<omega> - X x \<omega> else 0) = X (Suc x) \<omega> - X x \<omega>"
      by auto
  qed
  also have "\<dots> = X (\<pi> \<omega>) \<omega> - X (\<tau> \<omega>) \<omega>"
    using sum_Suc_diff'[OF \<tau>_le_\<pi>, of "\<lambda>i. X i \<omega>"] by simp
  finally show ?thesis by (simp add: stopped_value_def)
qed

text \<open>If each @{term "X i"} is integrable and the stopping time is bounded, then the stopped value
  is integrable. This corresponds to @{text integrable_stoppedValue} in Mathlib.\<close>

lemma integrable_stopped_value:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes \<tau>_st: "stopping_time \<tau>" and int_X: "\<And>i. integrable M (X i)"
    and \<tau>_bnd: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<tau> \<omega> \<le> N"
  shows "integrable M (stopped_value X \<tau>)"
proof -
  \<comment> \<open>Each indicator set is measurable\<close>
  have meas_eq: "\<And>i. {\<omega> \<in> space M. \<tau> \<omega> = i} \<in> sets M"
  proof -
    fix i :: nat
    have "Measurable.pred (F i) (\<lambda>\<omega>. \<tau> \<omega> = i)"
      by (rule stopping_time_measurable_eq[OF \<tau>_st]) simp_all
    then have "{\<omega> \<in> space (F i). \<tau> \<omega> = i} \<in> sets (F i)"
      by (rule Measurable.predE)
    then have "{\<omega> \<in> space M. \<tau> \<omega> = i} \<in> sets (F i)"
      using space_F[of i] by simp
    then show "{\<omega> \<in> space M. \<tau> \<omega> = i} \<in> sets M"
      using sets_F_subset[of i] by blast
  qed
  \<comment> \<open>Each summand is integrable via integrable_bound\<close>
  have int_summand: "\<And>i. integrable M (\<lambda>\<omega>. indicat_real {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> * X i \<omega>)"
  proof -
    fix i
    have meas: "(\<lambda>\<omega>. indicat_real {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> * X i \<omega>) \<in> borel_measurable M"
      by (intro borel_measurable_times borel_measurable_indicator meas_eq
              borel_measurable_integrable[OF int_X])
    show "integrable M (\<lambda>\<omega>. indicat_real {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> * X i \<omega>)"
      by (rule Bochner_Integration.integrable_bound[OF int_X[of i] meas], rule AE_I2)
         (auto simp: indicator_def)
  qed
  \<comment> \<open>The sum is integrable\<close>
  have int_sum: "integrable M (\<lambda>\<omega>. \<Sum>i\<le>N. indicat_real {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> * X i \<omega>)"
    by (intro Bochner_Integration.integrable_sum) (auto intro: int_summand)
  \<comment> \<open>The stopped value agrees with the sum AE\<close>
  have eq: "AE \<omega> in M. (\<Sum>i\<le>N. indicat_real {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> * X i \<omega>) =
    stopped_value X \<tau> \<omega>"
    by (intro AE_I2) (simp add: stopped_value_eq_sum[OF \<tau>_st \<tau>_bnd])
  have eq_space: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow>
    stopped_value X \<tau> \<omega> = (\<Sum>i\<le>N. indicat_real {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> * X i \<omega>)"
    by (simp add: stopped_value_eq_sum[OF \<tau>_st \<tau>_bnd])
  \<comment> \<open>Measurability via cong with the sum\<close>
  have meas_sum: "(\<lambda>\<omega>. \<Sum>i\<le>N. indicat_real {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> * X i \<omega>) \<in> borel_measurable M"
    using int_sum by (rule borel_measurable_integrable)
  have meas_sv: "stopped_value X \<tau> \<in> borel_measurable M"
    using measurable_cong[of M "stopped_value X \<tau>"
      "\<lambda>\<omega>. \<Sum>i\<le>N. indicat_real {\<omega> \<in> space M. \<tau> \<omega> = i} \<omega> * X i \<omega>" borel]
      eq_space meas_sum by auto
  \<comment> \<open>Transfer integrability via AE equality\<close>
  show ?thesis
    by (rule Bochner_Integration.integrable_cong_AE_imp[OF int_sum meas_sv eq])
qed

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
proof -
  have st: "stopping_time (\<lambda>\<omega>. min n (\<tau> \<omega>))"
    by (intro stopping_time_min stopping_time_const assms) simp
  have bnd: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> min n (\<tau> \<omega>) \<le> n" by simp
  show ?thesis
    unfolding stopped_process_eq_stopped_value
    by (rule integrable_stopped_value[OF st assms(2) bnd])
qed

end

end
