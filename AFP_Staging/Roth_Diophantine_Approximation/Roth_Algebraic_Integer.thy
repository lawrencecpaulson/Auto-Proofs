theory Roth_Algebraic_Integer
  imports
    Roth_Parameter_Costs
    Auxiliary_Index_Transfer
    Integral_Reduction
begin

section \<open>The headline results for the Thue–Siegel–Roth theorem\<close>

theorem roth_monic_finite:
  fixes f :: "int poly" and \<alpha> \<delta> :: real
  assumes monic: "Polynomial.lead_coeff f = 1"
    and root: "poly (map_poly of_int f) \<alpha> = 0"
    and \<delta>: "0 < \<delta>"
  shows "finite (roth_good_pairs \<alpha> (2+\<delta>))"
proof (rule ccontr)
  assume notfin: "\<not> finite (roth_good_pairs \<alpha> (2+\<delta>))"
  have inf: "infinite (roth_good_pairs \<alpha> (2+\<delta>))"
    using notfin by simp
  let ?d = "Polynomial.degree f"
  have dpos: "0 < ?d"
    using monic root monic_degree_0 by fastforce

  text \<open>Choose the exponent and the auxiliary polynomial parameters.\<close>
  define \<kappa> where "\<kappa> = 2+\<delta>/2"
  have kap: "2 < \<kappa>" "0 < \<kappa>" "\<kappa> < 2+\<delta>"
    using \<delta> by (auto simp: \<kappa>_def)
  define \<epsilon> where "\<epsilon> = (\<kappa> - 2)/(6*\<kappa>)"
  define \<xi> where "\<xi> = (\<kappa> - 2)/8"
  have epos: "0 < \<epsilon>" and elt: "\<epsilon> < 1" and xipos: "0 < \<xi>"
    and eq: "\<kappa> * ((1-\<epsilon>)/2 - \<epsilon>) = 1+2*\<xi>"
    using roth_epsilon_choice[OF kap(1)]
    by (auto simp: \<epsilon>_def \<xi>_def)
  obtain m :: nat where mpos: "0 < m" and agap:
    "2*real ?d < real m*\<epsilon>\<^sup>2"
    using roth_choose_m[OF epos, of ?d] by blast
  define \<eta> where "\<eta> = \<epsilon>/4"
  define \<sigma> where "\<sigma> = \<eta>^(2^(m-1))"
  have etapos: "0 < \<eta>" and etahalf: "\<eta> \<le> 1/2"
    and eta_small: "2*\<eta> < \<epsilon>"
    using epos elt by (auto simp: \<eta>_def)
  have sigpos: "0 < \<sigma>" using etapos by (simp add: \<sigma>_def)
  let ?C = "ln (4*real_of_int (roth_power_base f))"
  let ?D = "ln (16*max 1 (abs \<alpha>))"
  have bpos: "1 \<le> roth_power_base f" by (rule roth_power_base_ge_one)
  have Cnonneg: "0 \<le> ?C" using bpos by simp
  have Dnonneg: "0 \<le> ?D" by simp
  obtain B :: real where Bpos: "0 < B" and Bgap:
      "(1+\<xi>)*(?C+?D)/B \<le> \<xi>/2" and Bheight:
      "real m*(1+\<xi>)*(?C+4)/B \<le> \<sigma>/2"
    using roth_choose_parameter_budget[OF xipos sigpos Cnonneg Dnonneg, of m]
    by blast
  have apos: "0 < real m*\<xi>/2" using mpos xipos by simp
  have cpos: "0 < \<sigma>/2" using sigpos by simp
  obtain A :: real where Apos: "0 < A" and Abounds:
    "\<forall>T>A. ln 2 < (real m*\<xi>/2)*T \<and> ln 2 \<le> (\<sigma>/2)*T"
    using roth_choose_linear_budgets[OF apos cpos] by blast

  text \<open>Select rational approximants with balanced heights and degrees.\<close>
  obtain \<beta> :: "nat \<Rightarrow> rat" and T :: real and r :: "nat \<Rightarrow> nat"
    where TA: "A < T" and Tpos: "0 < T" and selected:
      "roth_selected_parameters \<alpha> \<kappa> m B \<xi> \<sigma> T \<beta> r"
    using roth_select_parameters[where \<alpha>=\<alpha> and kappa="2+\<delta>"
      and kappa'="\<kappa>" and m=m and sigma="\<sigma>" and xi="\<xi>" and B=B and A=A,
      OF inf kap(2) kap(3) sigpos xipos Bpos] by blast
  have rbounds:
      "\<forall>v<m. 0 < r v \<and> B \<le> roth_rat_log_height (\<beta> v) \<and>
      roth_rat_log_height (\<beta> v) \<le> \<xi>*T \<and>
      T \<le> real (r v)*roth_rat_log_height (\<beta> v) \<and>
      real (r v)*roth_rat_log_height (\<beta> v) \<le> (1+\<xi>)*T \<and>
      abs (of_rat (\<beta> v) - \<alpha>) \<le>
        exp (-\<kappa>*roth_rat_log_height (\<beta> v))"
    and ratios: "\<forall>v. Suc v < m \<longrightarrow>
      real (r (Suc v)) \<le> \<sigma>*real (r v)"
    and sumb: "real (\<Sum>v<m. r v) \<le> real m*((1+\<xi>)*T/B)"
    using selected unfolding roth_selected_parameters_def by blast+
  have Tgap: "ln 2 < real m*T*\<xi>/2"
    and Theight: "ln 2 \<le> \<sigma>*T/2"
    using Abounds TA by (auto simp: algebra_simps)
  let ?\<beta> = "\<lambda>v. if v < m then \<beta> v else \<beta> 0"
  have near_all: "\<And>v. abs (of_rat (?\<beta> v) - \<alpha>) \<le>
      exp (-\<kappa>*roth_rat_log_height (?\<beta> v))"
    using rbounds mpos by auto
  have rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v" using rbounds by blast
  have ratio: "\<And>v. Suc v < m \<Longrightarrow>
      real (r (Suc v)) \<le> \<eta>^(2^(m-1))*real (r v)"
    using ratios by (simp add: \<sigma>_def)
  have hlow: "\<And>v. v < m \<Longrightarrow> B \<le> roth_rat_log_height (?\<beta> v)"
    using rbounds by auto
  have wlow: "\<And>v. v < m \<Longrightarrow>
      T \<le> real (r v)*roth_rat_log_height (?\<beta> v)"
    using rbounds by auto
  have whigh: "\<And>v. v < m \<Longrightarrow>
      real (r v)*roth_rat_log_height (?\<beta> v) \<le> (1+\<xi>)*T"
    using rbounds by auto

  text \<open>Pay the logarithmic costs needed for index transfer and Roth's lemma.\<close>
  have hlow0: "B \<le> roth_rat_log_height (?\<beta> 0)" by (rule hlow[OF mpos])
  have whigh0: "real (r 0) * roth_rat_log_height (?\<beta> 0) \<le> (1+\<xi>)*T"
    by (rule whigh[OF mpos])
  have rbound: "real (r 0) \<le> (1+\<xi>)*T/B"
    by (rule roth_degree_from_weighted[OF Bpos hlow0 whigh0])
  have gap: "ln 2 + real (\<Sum>v<m. r v) * (?C+?D) + real m * (1+\<xi>)*T <
    \<kappa>*T*(real m*(1-\<epsilon>)/2 - \<epsilon>*real m)"
    by (rule roth_numeric_gap[OF mpos Tpos _ sumb Bgap Tgap eq])
      (use Cnonneg Dnonneg in simp)
  have hbudget: "real m*((1+\<xi>)*T/B)*(?C+4) \<le> \<sigma>*T/2"
    by (rule roth_height_budget[OF Tpos Bheight])
  have hcost: "ln 2 + real (\<Sum>v<m. r v)*?C + 4*real m*real (r 0) \<le> \<sigma>*T"
    by (rule roth_numeric_height[OF Cnonneg sumb rbound hbudget Theight])
  have hbound: "ln (real (nat (2 * (4 * roth_power_base f) ^ (\<Sum>w<m. r w)))) +
    4*real m*real (r 0) \<le> \<eta>^(2^(m-1))*real (r v)*roth_rat_log_height (?\<beta> v)"
    if vm: "v < m" for v
  proof -
    have hw: "\<sigma>*T \<le> \<sigma>*(real (r v)*roth_rat_log_height (?\<beta> v))"
      by (rule mult_left_mono[OF wlow[OF vm]]) (use sigpos in simp)
    have eqlog: "ln (real (nat (2 * (4 * roth_power_base f) ^ (\<Sum>w<m. r w)))) =
      ln 2 + real (\<Sum>w<m. r w)*?C"
      using roth_auxiliary_bound_log[OF bpos, of "\<Sum>w<m. r w"] by simp
    show ?thesis using hcost hw eqlog by (simp add: \<sigma>_def)
  qed

  text \<open>The auxiliary polynomial has a large index at the algebraic point.\<close>
  let ?H = "nat (2 * (4 * roth_power_base f) ^ (\<Sum>v<m. r v))"
  obtain P :: "int mpoly" where pn: "P \<noteq> 0"
    and pb: "roth_poly_in_box m r P"
    and pi: "ereal (real m * (1-\<epsilon>) / 2) \<le>
      roth_index m r (\<lambda>_. \<alpha>) (replace_coeff (of_int::int \<Rightarrow> real) P)"
    and ph: "roth_int_coeff_sup P \<le> ?H"
    using roth_auxiliary_polynomial_monic_sup
      [where f=f and a=\<alpha> and d="?d" and m=m and r=r and eps=\<epsilon>,
       OF monic refl dpos root mpos rpos epos elt agap] by blast
  have hlog: "ln (real (roth_int_coeff_sup P)) \<le> ln (real ?H)"
    by (rule roth_int_coeff_sup_log_mono[OF ph])
  have hh: "ln (real (roth_int_coeff_sup P)) +
      4*real m*real (r 0) \<le>
      \<eta>^(2^(m-1))*real (r v)*roth_rat_log_height (?\<beta> v)"
    if "v<m" for v
    using hlog hbound[OF that] by linarith
  have ib: "roth_index m r ?\<beta> (replace_coeff (of_int::int \<Rightarrow> rat) P) \<le>
      ereal (2*real m*\<eta>)"
    by (rule roth_lemma_integer[OF mpos pn pb rpos etapos etahalf ratio hh])

  text \<open>Index transfer gives the opposing bound at the rational points.\<close>
  have sum_le: "(\<Sum>v<m. real (r v) * roth_rat_log_height (?\<beta> v)) \<le>
      real m * ((1+\<xi>)*T)"
    by (rule roth_weighted_height_sum_le[OF whigh])
  have gap': "ln 2 + real (\<Sum>v<m. r v) *
        (ln (4 * real_of_int (roth_power_base f)) +
          ln (16 * max 1 (abs \<alpha>))) +
      (\<Sum>v<m. real (r v) * roth_rat_log_height (?\<beta> v)) <
      \<kappa> * T * (real m * (1-\<epsilon>) / 2 - \<epsilon> * real m)"
    using sum_le gap by linarith
  have kpos: "0 \<le> \<kappa>" using kap by simp
  have Lpos: "0 \<le> T" using Tpos by simp
  have ia: "ereal (\<epsilon> * real m) \<le>
      roth_index m r ?\<beta> (replace_coeff (of_int::int \<Rightarrow> rat) P)"
    by (rule roth_index_transfer_aux_height[OF pb bpos ph rpos
      wlow kpos Lpos pi near_all gap'])
  have upper: "\<epsilon> * real m \<le> 2 * real m * \<eta>"
    using order_trans[OF ia ib] by simp
  have mreal: "0 < real m" using mpos by simp
  have lower: "2 * \<eta> * real m < \<epsilon> * real m"
    by (rule mult_strict_right_mono[OF eta_small mreal])
  show False using upper lower by (simp add: mult_ac)
qed

theorem roth_algebraic_integer_finite:
  fixes \<alpha> \<delta> :: real
  assumes alg: "algebraic_int \<alpha>" and \<delta>: "0 < \<delta>"
  shows "finite (roth_good_pairs \<alpha> (2+\<delta>))"
  using algebraic_int_altdef_ipoly assms(1,2) roth_monic_finite by blast

theorem roth_real_algebraic_finite:
  fixes \<alpha> \<delta> :: real
  assumes alg: "algebraic \<alpha>" and irr: "\<alpha> \<notin> \<rat>"
    and \<delta>: "0 < \<delta>"
  shows "finite (roth_good_pairs \<alpha> (2+\<delta>))"
  using assms roth_algebraic_integer_finite roth_reduction_to_integral
  by presburger

end
