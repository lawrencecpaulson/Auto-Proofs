theory Optional_Stopping
  imports
    Piecewise_Stopping_Time
    "Martingales.Martingale"
begin

text \<open>The optional stopping theorem (fair game theorem): an adapted integrable process is a
  submartingale if and only if for all bounded stopping times @{term \<tau>} and @{term \<pi>} with
  @{term "\<tau> \<le> \<pi>"}, the expected stopped value at @{term \<tau>} is at most that at @{term \<pi>}.

  We also prove that the stopped process of a submartingale is a submartingale, and
  Doob's maximal inequality.\<close>

section \<open>Forward direction\<close>

text \<open>If @{term X} is a submartingale and @{term "\<tau> \<le> \<pi>"} are bounded stopping times,
  then @{term "\<integral>\<omega>. stopped_value X \<tau> \<omega> \<partial>M \<le> \<integral>\<omega>. stopped_value X \<pi> \<omega> \<partial>M"}.
  This corresponds to @{text Submartingale.expected_stoppedValue_mono} in Mathlib.\<close>

theorem (in submartingale_linorder) expected_stopped_value_mono:
  fixes \<tau> \<pi> :: "'a \<Rightarrow> nat"
  assumes "stopping_time \<tau>" "stopping_time \<pi>"
    and "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<tau> \<omega> \<le> \<pi> \<omega>"
    and "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<pi> \<omega> \<le> N"
  shows "(\<integral>\<omega>. stopped_value X \<tau> \<omega> \<partial>M) \<le> (\<integral>\<omega>. stopped_value X \<pi> \<omega> \<partial>M)"
  sorry

section \<open>Converse direction\<close>

text \<open>If an adapted integrable process satisfies the monotonicity of expected stopped values
  for all bounded stopping times, then it is a submartingale.
  This corresponds to @{text submartingale_of_expected_stoppedValue_mono} in Mathlib.\<close>

theorem (in nat_sigma_finite_filtered_measure) submartingale_of_expected_stopped_value_mono:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes adapted: "adapted_process M F 0 X"
    and integrable: "\<And>i. integrable M (X i)"
    and mono: "\<And>\<tau> \<pi>. stopping_time \<tau> \<Longrightarrow> stopping_time \<pi> \<Longrightarrow>
      (\<forall>\<omega>\<in>space M. \<tau> \<omega> \<le> \<pi> \<omega>) \<Longrightarrow> (\<exists>N. \<forall>\<omega>\<in>space M. \<pi> \<omega> \<le> N) \<Longrightarrow>
      (\<integral>\<omega>. stopped_value X \<tau> \<omega> \<partial>M) \<le> (\<integral>\<omega>. stopped_value X \<pi> \<omega> \<partial>M)"
  shows "submartingale M F 0 X"
  sorry

section \<open>The optional stopping theorem (iff)\<close>

text \<open>The full characterization: an adapted integrable process is a submartingale iff
  expected stopped values are monotone for all bounded stopping times.
  This corresponds to @{text submartingale_iff_expected_stoppedValue_mono} in Mathlib.\<close>

theorem (in nat_sigma_finite_filtered_measure) submartingale_iff_expected_stopped_value_mono:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "adapted_process M F 0 X" "\<And>i. integrable M (X i)"
  shows "submartingale M F 0 X \<longleftrightarrow>
    (\<forall>\<tau> \<pi>. stopping_time \<tau> \<longrightarrow> stopping_time \<pi> \<longrightarrow>
      (\<forall>\<omega>\<in>space M. \<tau> \<omega> \<le> \<pi> \<omega>) \<longrightarrow> (\<exists>N. \<forall>\<omega>\<in>space M. \<pi> \<omega> \<le> N) \<longrightarrow>
      (\<integral>\<omega>. stopped_value X \<tau> \<omega> \<partial>M) \<le> (\<integral>\<omega>. stopped_value X \<pi> \<omega> \<partial>M))"
  sorry

section \<open>Stopped process of a submartingale\<close>

text \<open>The stopped process of a submartingale with respect to a stopping time is a submartingale.
  This corresponds to @{text Submartingale.stoppedProcess} in Mathlib.\<close>

theorem (in submartingale_linorder) stopped_process_submartingale:
  assumes "stopping_time \<tau>"
  shows "submartingale M F t\<^sub>0 (stopped_process X \<tau>)"
  sorry

section \<open>Doob's maximal inequality\<close>

text \<open>Given a non-negative submartingale @{term X}, for all @{term "\<epsilon> > 0"},
  @{term "\<epsilon> * emeasure M {\<omega> \<in> space M. \<epsilon> \<le> Max_{k \<le> n} X k \<omega>} \<le> \<integral>\<^sup>+ \<omega> \<in> {..}. X n \<omega> \<partial>M"}.
  This corresponds to @{text maximal_ineq} in Mathlib.\<close>

theorem (in submartingale_linorder) maximal_ineq:
  assumes "\<And>i \<omega>. t\<^sub>0 \<le> i \<Longrightarrow> \<omega> \<in> space M \<Longrightarrow> 0 \<le> X i \<omega>"
    and "\<epsilon> > (0 :: real)"
  shows "ennreal \<epsilon> * emeasure M {\<omega> \<in> space M. \<epsilon> \<le> Max (X ` {t\<^sub>0..n}) \<omega>}
    \<le> ennreal (set_lebesgue_integral M {\<omega> \<in> space M. \<epsilon> \<le> Max (X ` {t\<^sub>0..n}) \<omega>} (X n))"
  sorry

end
