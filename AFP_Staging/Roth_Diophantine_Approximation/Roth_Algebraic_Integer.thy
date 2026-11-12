theory Roth_Algebraic_Integer
  imports
    Roth_Parameter_Costs
    Auxiliary_Index_Transfer
    Integral_Reduction
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

lemma roth_monic_root_degree_pos:
  fixes f :: "int poly" and alpha :: real
  assumes monic: "Polynomial.lead_coeff f = 1"
    and root: "poly (map_poly of_int f) alpha = 0"
  shows "0 < Polynomial.degree f"
proof (rule Nat.gr0I)
  assume "Polynomial.degree f = 0"
  then obtain c :: int where f: "f = [:c:]" by (elim degree_eq_zeroE)
  have "c = 1" using monic f by simp
  then show False using root f by simp
qed

theorem roth_monic_finite:
  fixes f :: "int poly" and alpha delta :: real
  assumes monic: "Polynomial.lead_coeff f = 1"
    and root: "poly (map_poly of_int f) alpha = 0"
    and delta: "0 < delta"
  shows "finite (roth_good_pairs alpha (2+delta))"
proof (rule ccontr)
  assume notfin: "\<not> finite (roth_good_pairs alpha (2+delta))"
  have inf: "infinite (roth_good_pairs alpha (2+delta))" using notfin by simp
  let ?d = "Polynomial.degree f"
  have dpos: "0 < ?d" by (rule roth_monic_root_degree_pos[OF monic root])
  let ?kappa = "2+delta/2"
  have kap: "2 < ?kappa" "0 < ?kappa" "?kappa < 2+delta"
    using delta by auto
  define eps where "eps = (?kappa - 2)/(6*?kappa)"
  define xi where "xi = (?kappa - 2)/8"
  have epos: "0 < eps" and elt: "eps < 1" and xipos: "0 < xi"
    and eq: "?kappa * ((1-eps)/2 - eps) = 1+2*xi"
    using roth_epsilon_choice[OF kap(1)]
    by (auto simp: eps_def xi_def)
  obtain m :: nat where mpos: "0 < m" and agap:
    "2*real ?d < real m*eps\<^sup>2"
    using roth_choose_m[OF epos, of ?d] by blast
  let ?eta = "eps/4"
  let ?sigma = "?eta^(2^(m-1))"
  have etapos: "0 < ?eta" and etahalf: "?eta \<le> 1/2"
    and eta_small: "2*?eta < eps" using epos elt by auto
  have sigpos: "0 < ?sigma" using etapos by simp
  let ?C = "ln (4*real_of_int (roth_power_base f))"
  let ?D = "ln (16*max 1 (abs alpha))"
  have bpos: "1 \<le> roth_power_base f" by (rule roth_power_base_ge_one)
  have Cnonneg: "0 \<le> ?C" using bpos by simp
  have Dnonneg: "0 \<le> ?D" by simp
  obtain B :: real where Bpos: "0 < B" and Bgap:
      "(1+xi)*(?C+?D)/B \<le> xi/2" and Bheight:
      "real m*(1+xi)*(?C+4)/B \<le> ?sigma/2"
    using roth_choose_parameter_budget[OF xipos sigpos Cnonneg Dnonneg, of m]
    by blast
  obtain A :: real where Apos: "0 < A" and Abounds:
      "\<forall>T>A. ln 2 < real m*T*xi/2 \<and> ln 2 \<le> ?sigma*T/2"
    using roth_choose_T_threshold[OF mpos xipos sigpos] by blast
  obtain beta :: "nat \<Rightarrow> rat" and T :: real and r :: "nat \<Rightarrow> nat"
    where TA: "A < T" and Tpos: "0 < T" and selected:
      "roth_selected_parameters alpha ?kappa m B xi ?sigma T beta r"
    using roth_select_parameters[where alpha=alpha and kappa="2+delta"
      and kappa'="?kappa" and m=m and sigma="?sigma" and xi=xi and B=B and A=A,
      OF inf kap(2) kap(3) sigpos xipos Bpos] by blast
  have rbounds:
      "\<forall>v<m. 0 < r v \<and> B \<le> roth_rat_log_height (beta v) \<and>
      roth_rat_log_height (beta v) \<le> xi*T \<and>
      T \<le> real (r v)*roth_rat_log_height (beta v) \<and>
      real (r v)*roth_rat_log_height (beta v) \<le> (1+xi)*T \<and>
      abs (of_rat (beta v) - alpha) \<le>
        exp (-?kappa*roth_rat_log_height (beta v))"
    and ratios: "\<forall>v. Suc v < m \<longrightarrow>
      real (r (Suc v)) \<le> ?sigma*real (r v)"
    and sumb: "real (\<Sum>v<m. r v) \<le> real m*((1+xi)*T/B)"
    using selected unfolding roth_selected_parameters_def by blast+
  have Tgap: "ln 2 < real m*T*xi/2" and Theight: "ln 2 \<le> ?sigma*T/2"
    using Abounds TA by blast+
  let ?beta = "\<lambda>v. if v < m then beta v else beta 0"
  have near_all: "\<And>v. abs (of_rat (?beta v) - alpha) \<le>
      exp (-?kappa*roth_rat_log_height (?beta v))"
    using rbounds mpos by auto
  show False
    by (rule roth_selected_contradiction[where f=f and alpha=alpha and
      beta="?beta" and d="?d" and m=m and r=r and eps=eps and eta="?eta" and
      kappa="?kappa" and xi=xi and B=B and T=T])
      (use monic root dpos mpos epos elt agap etapos etahalf eta_small
        kap xipos Bpos eq Bgap Bheight Tpos Tgap Theight rbounds ratios sumb near_all
        in auto)
qed

theorem roth_algebraic_integer_finite:
  fixes alpha delta :: real
  assumes alg: "algebraic_int alpha" and delta: "0 < delta"
  shows "finite (roth_good_pairs alpha (2+delta))"
proof -
  obtain f :: "int poly" where root: "poly (map_poly of_int f) alpha = 0"
    and monic: "Polynomial.lead_coeff f = 1"
    using alg by (auto simp: algebraic_int_altdef_ipoly)
  show ?thesis by (rule roth_monic_finite[OF monic root delta])
qed

theorem roth_real_algebraic_finite:
  fixes alpha delta :: real
  assumes alg: "algebraic alpha" and irr: "alpha \<notin> \<rat>"
    and delta: "0 < delta"
  shows "finite (roth_good_pairs alpha (2+delta))"
proof -
  have integral: "\<And>beta delta :: real. algebraic_int beta \<Longrightarrow>
      beta \<notin> \<rat> \<Longrightarrow> 0 < delta \<Longrightarrow>
      finite (roth_good_pairs beta (2+delta))"
    using roth_algebraic_integer_finite by blast
  show ?thesis by (rule roth_reduction_to_integral[OF integral alg irr delta])
qed

end
