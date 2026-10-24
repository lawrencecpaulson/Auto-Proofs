theory Roth_Selected_Contradiction
  imports Roth_Parameter_Costs Roth_Conditional_Contradiction
begin

lemma roth_choose_T_threshold:
  fixes xi sigma :: real and m :: nat
  assumes mpos: "0 < m" and xi: "0 < xi" and sig: "0 < sigma"
  shows "\<exists>A::real. 0 < A \<and> (\<forall>T>A.
    ln 2 < real m*T*xi/2 \<and> ln 2 \<le> sigma*T/2)"
proof -
  have a: "0 < real m*xi/2" using mpos xi by simp
  have c: "0 < sigma/2" using sig by simp
  obtain A :: real where A: "0 < A" and bounds:
    "\<forall>T>A. ln 2 < (real m*xi/2)*T \<and> ln 2 \<le> (sigma/2)*T"
    using roth_choose_linear_budgets[OF a c] by blast
  show ?thesis using A bounds by (intro exI[of _ A]) (simp add: algebra_simps)
qed

theorem roth_selected_contradiction:
  fixes f :: "int poly" and alpha :: real and beta :: "nat \<Rightarrow> rat"
    and eta :: real and m :: nat
  defines "C \<equiv> ln (4 * real_of_int (roth_power_base f))"
    and "D \<equiv> ln (16 * max 1 (abs alpha))"
    and "sigma \<equiv> eta^(2^(m-1))"
  assumes monic: "Polynomial.lead_coeff f = 1"
    and d: "d = Polynomial.degree f" and dpos: "0 < d"
    and root: "poly (map_poly of_int f) alpha = 0"
    and mpos: "0 < m"
    and epos: "0 < eps" and elt: "eps < 1"
    and agap: "2 * real d < real m * eps\<^sup>2"
    and etapos: "0 < eta" and etahalf: "eta \<le> 1/2"
    and eta_small: "2 * eta < eps"
    and kpos: "0 < kappa" and xipos: "0 < xi" and Bpos: "0 < B"
    and eq: "kappa * ((1-eps)/2 - eps) = 1 + 2*xi"
    and budget_gap: "(1+xi)*(C+D)/B \<le> xi/2"
    and budget_height: "real m*(1+xi)*(C+4)/B \<le> sigma/2"
    and Tpos: "0 < T"
    and Tgap: "ln 2 < real m*T*xi/2"
    and Theight: "ln 2 \<le> sigma*T/2"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and rat: "\<And>v. Suc v < m \<Longrightarrow> real (r (Suc v)) \<le> sigma * real (r v)"
    and hlow: "\<And>v. v < m \<Longrightarrow> B \<le> roth_rat_log_height (beta v)"
    and wlow: "\<And>v. v < m \<Longrightarrow> T \<le> real (r v) * roth_rat_log_height (beta v)"
    and whigh: "\<And>v. v < m \<Longrightarrow> real (r v) * roth_rat_log_height (beta v) \<le> (1+xi)*T"
    and near: "\<And>v. abs (of_rat (beta v) - alpha) \<le>
      exp (-kappa * roth_rat_log_height (beta v))"
    and sumb: "real (\<Sum>v<m. r v) \<le> real m * ((1+xi)*T/B)"
  shows False
proof -
  have bpos: "1 \<le> roth_power_base f" by (rule roth_power_base_ge_one)
  have Cnonneg: "0 \<le> C" unfolding C_def using bpos by simp
  have Dnonneg: "0 \<le> D" unfolding D_def by simp
  have sigma_pos: "0 < sigma" unfolding sigma_def using etapos by simp
  have zero_m: "0 < m" by (rule mpos)
  have hlow0: "B \<le> roth_rat_log_height (beta 0)" by (rule hlow[OF zero_m])
  have whigh0: "real (r 0) * roth_rat_log_height (beta 0) \<le> (1+xi)*T"
    by (rule whigh[OF zero_m])
  have rbound: "real (r 0) \<le> (1+xi)*T/B"
    by (rule roth_degree_from_weighted[OF Bpos hlow0 whigh0])
  have gap: "ln 2 + real (\<Sum>v<m. r v) * (C+D) + real m * (1+xi)*T <
    kappa*T*(real m*(1-eps)/2 - eps*real m)"
    by (rule roth_numeric_gap[OF mpos Tpos _ sumb budget_gap Tgap eq])
      (use Cnonneg Dnonneg in simp)
  have hbudget: "real m*((1+xi)*T/B)*(C+4) \<le> sigma*T/2"
    by (rule roth_height_budget[OF Tpos budget_height])
  have hcost: "ln 2 + real (\<Sum>v<m. r v)*C + 4*real m*real (r 0) \<le> sigma*T"
    by (rule roth_numeric_height[OF Cnonneg sumb rbound hbudget Theight])
  have hbound: "ln (real (nat (2 * (4 * roth_power_base f) ^ (\<Sum>w<m. r w)))) +
    4*real m*real (r 0) \<le> eta^(2^(m-1))*real (r v)*roth_rat_log_height (beta v)"
    if vm: "v < m" for v
  proof -
    have hw: "sigma*T \<le> sigma*(real (r v)*roth_rat_log_height (beta v))"
      by (rule mult_left_mono[OF wlow[OF vm]]) (use sigma_pos in simp)
    have eqlog: "ln (real (nat (2 * (4 * roth_power_base f) ^ (\<Sum>w<m. r w)))) =
      ln 2 + real (\<Sum>w<m. r w)*C"
      using roth_auxiliary_bound_log[OF bpos, of "\<Sum>w<m. r w"]
      by (simp add: C_def)
    show ?thesis using hcost hw eqlog by (simp add: sigma_def)
  qed
  show False
    by (rule roth_conditional_contradiction[where f=f and alpha=alpha and beta=beta
        and d=d and m=m and r=r and eps=eps and eta=eta and
        L=T and U="(1+xi)*T" and kappa=kappa])
      (use monic d dpos root mpos rpos epos elt agap etapos etahalf
        eta_small rat hbound wlow whigh kpos Tpos near gap
        in \<open>auto simp: sigma_def C_def D_def\<close>)
qed

end
