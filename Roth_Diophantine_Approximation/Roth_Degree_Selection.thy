theory Roth_Degree_Selection
  imports Roth_Approximation_Height
begin

lemma roth_ratio_gap_from_growth:
  fixes h :: "nat \<Rightarrow> real"
  assumes Tpos: "0 < T" and hpos: "0 < h v" "0 < h (Suc v)"
    and sig: "0 < sigma"
    and growth: "2 * h v \<le> sigma * h (Suc v)"
    and large: "2 * h v \<le> sigma * T"
  shows "T / h (Suc v) + 1 \<le> sigma * (T / h v)"
proof -
  have first: "T / h (Suc v) \<le> (sigma / 2) * (T / h v)"
    using Tpos hpos sig growth by (simp add: field_simps)
  have second: "1 \<le> (sigma / 2) * (T / h v)"
    using hpos sig large by (simp add: field_simps)
  have "T / h (Suc v) + 1 \<le> (sigma / 2) * (T / h v) +
      (sigma / 2) * (T / h v)"
    using first second by linarith
  also have "... = sigma * (T / h v)" by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma roth_rounded_degrees_ratios:
  fixes h :: "nat \<Rightarrow> real"
  assumes Tpos: "0 < T" and sig: "0 < sigma"
    and hpos: "\<And>v. v < m \<Longrightarrow> 0 < h v"
    and growth: "\<And>v. Suc v < m \<Longrightarrow>
      2 * h v \<le> sigma * h (Suc v)"
    and large: "\<And>v. v < m \<Longrightarrow> 2 * h v \<le> sigma * T"
  shows "\<And>v. Suc v < m \<Longrightarrow>
    real (roth_rounded_degrees T h (Suc v)) \<le>
      sigma * real (roth_rounded_degrees T h v)"
proof -
  fix v
  assume vm: "Suc v < m"
  have hv: "0 < h v" using hpos vm by simp
  have hn: "0 < h (Suc v)" by (rule hpos[OF vm])
  have gap: "T / h (Suc v) + 1 \<le> sigma * (T / h v)"
    by (rule roth_ratio_gap_from_growth[OF Tpos hv hn sig
      growth[OF vm] large[of v]]) (use vm in simp)
  show "real (roth_rounded_degrees T h (Suc v)) \<le>
      sigma * real (roth_rounded_degrees T h v)"
    by (rule roth_rounded_degrees_ratio[OF Tpos hv hn _ gap])
      (use sig in simp)
qed


lemma roth_choose_large_T:
  fixes h :: "nat \<Rightarrow> real"
  assumes sig: "0 < sigma"
  shows "\<exists>T::real. 0 < T \<and> (\<forall>v<m. 2 * h v \<le> sigma * T)"
proof -
  let ?M = "Max (insert 0 (h ` {..<m}))"
  have Mnonneg: "0 \<le> ?M" by (rule Max_ge) simp_all
  have hle: "h v \<le> ?M" if vm: "v < m" for v
    by (rule Max_ge) (use vm in auto)
  let ?T = "2 * ?M / sigma + 1"
  have Tnonneg: "0 \<le> 2 * ?M / sigma"
    using Mnonneg sig by (intro divide_nonneg_pos) auto
  have Tpos: "0 < ?T" using Tnonneg by linarith
  have eq: "sigma * ?T = 2 * ?M + sigma"
    using sig by (simp add: distrib_left)
  have bound: "2 * h v \<le> sigma * ?T" if vm: "v < m" for v
    using hle[OF vm] sig eq by linarith
  show ?thesis using Tpos bound by blast
qed

theorem roth_choose_degrees:
  fixes h :: "nat \<Rightarrow> real"
  assumes sig: "0 < sigma"
    and hpos: "\<And>v. v < m \<Longrightarrow> 0 < h v"
    and growth: "\<And>v. Suc v < m \<Longrightarrow>
      2 * h v \<le> sigma * h (Suc v)"
  shows "\<exists>T r. 0 < (T::real) \<and>
    (\<forall>v<m. 0 < r v \<and> T \<le> real (r v) * h v \<and>
      real (r v) * h v \<le> T + h v) \<and>
    (\<forall>v. Suc v < m \<longrightarrow> real (r (Suc v)) \<le> sigma * real (r v))"
proof -
  obtain T :: real where Tpos: "0 < T" and large:
      "\<And>v. v < m \<Longrightarrow> 2 * h v \<le> sigma * T"
    using roth_choose_large_T[where h=h and m=m, OF sig] by blast
  let ?r = "roth_rounded_degrees T h"
  have bounds: "\<forall>v<m. 0 < ?r v \<and> T \<le> real (?r v) * h v \<and>
      real (?r v) * h v \<le> T + h v"
    using roth_rounded_degrees_bounds Tpos hpos by blast
  have ratios: "\<forall>v. Suc v < m \<longrightarrow>
      real (?r (Suc v)) \<le> sigma * real (?r v)"
    using roth_rounded_degrees_ratios[where T=T and sigma=sigma and h=h and m=m]
      Tpos sig hpos growth large by blast
  show ?thesis using Tpos bounds ratios by blast
qed

end
