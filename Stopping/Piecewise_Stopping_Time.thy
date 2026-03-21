theory Piecewise_Stopping_Time
  imports Stopped_Value_Integration
begin

text \<open>Piecewise constant stopping times and their interaction with stopped values and integration.
  These are needed for the converse direction of the optional stopping theorem.\<close>

context nat_sigma_finite_filtered_measure
begin

subsection \<open>Piecewise constant stopping times\<close>

text \<open>Given @{term "i \<le> j"} and an @{term "F i"}-measurable set @{term S}, the function that
  returns @{term i} on @{term S} and @{term j} on its complement is a stopping time.
  This corresponds to @{text isStoppingTime_piecewise_const} in Mathlib.\<close>

lemma stopping_time_piecewise_const:
  assumes "i \<le> j" "S \<in> sets (F i)"
  shows "stopping_time (\<lambda>\<omega>. if \<omega> \<in> S then i else j)"
  sorry

subsection \<open>Stopped value of piecewise constant stopping times\<close>

text \<open>The stopped value at a piecewise constant stopping time decomposes into a piecewise function.
  This corresponds to @{text stoppedValue_piecewise_const} in Mathlib.\<close>

lemma stopped_value_piecewise_const:
  assumes "S \<subseteq> space M"
  shows "stopped_value X (\<lambda>\<omega>. if \<omega> \<in> S then i else j) = (\<lambda>\<omega>. if \<omega> \<in> S then X i \<omega> else X j \<omega>)"
  unfolding stopped_value_def by simp

subsection \<open>Integration over piecewise functions\<close>

text \<open>The integral of a piecewise function splits into integrals over the two pieces.
  This corresponds to @{text integral_piecewise} in Mathlib.\<close>

lemma integral_piecewise:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "S \<in> sets M" "integrable M f" "integrable M g"
  shows "(\<integral>\<omega>. (if \<omega> \<in> S then f \<omega> else g \<omega>) \<partial>M) =
    set_lebesgue_integral M S f + set_lebesgue_integral M (space M - S) g"
  sorry

end

end
