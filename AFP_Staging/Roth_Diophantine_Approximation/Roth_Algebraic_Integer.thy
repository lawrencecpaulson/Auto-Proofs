theory Roth_Algebraic_Integer
  imports
    Roth_Parameter_Costs
    Auxiliary_Index_Transfer
    Roth_Approximation
    "Hermite_Lindemann.More_Algebraic_Numbers_HLW"
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
  define \<kappa> where "\<kappa> \<equiv> 2+\<delta>/2"
  have kap: "2 < \<kappa>" "0 < \<kappa>" "\<kappa> < 2+\<delta>"
    using \<delta> by (auto simp: \<kappa>_def)
  define \<epsilon> where "\<epsilon> \<equiv> (\<kappa> - 2)/(6*\<kappa>)"
  define \<xi> where "\<xi> \<equiv> (\<kappa> - 2)/8"
  have epos: "0 < \<epsilon>" and elt: "\<epsilon> < 1" and xipos: "0 < \<xi>"
    and eq: "\<kappa> * ((1-\<epsilon>)/2 - \<epsilon>) = 1+2*\<xi>"
    using roth_epsilon_choice[OF kap(1)] by (auto simp: \<epsilon>_def \<xi>_def)
  obtain m :: nat where mpos: "0 < m" and agap: "2*real ?d < real m*\<epsilon>\<^sup>2"
    using roth_choose_m[OF epos, of ?d] by blast
  define \<eta> where "\<eta> \<equiv> \<epsilon>/4"
  define \<sigma> where "\<sigma> \<equiv> \<eta>^(2^(m-1))"
  have etapos: "0 < \<eta>" and etahalf: "\<eta> \<le> 1/2" and eta_small: "2*\<eta> < \<epsilon>"
    using epos elt by (auto simp: \<eta>_def)
  have sigpos: "0 < \<sigma>" using etapos by (simp add: \<sigma>_def)
  let ?C = "ln (4*real_of_int (roth_power_base f))"
  let ?D = "ln (16*max 1 (abs \<alpha>))"
  have bpos: "1 \<le> roth_power_base f" by (rule roth_power_base_ge_one)
  have Cnonneg: "0 \<le> ?C" using bpos by simp
  have Dnonneg: "0 \<le> ?D" by simp
  obtain B :: real where Bpos: "0 < B" and Bgap: "(1+\<xi>)*(?C+?D)/B \<le> \<xi>/2" 
      and Bheight: "real m*(1+\<xi>)*(?C+4)/B \<le> \<sigma>/2"
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
    using Bpos kap notfin sigpos xipos by (metis roth_select_parameters)
  have rbounds:
      "\<forall>v<m. 0 < r v \<and> B \<le> roth_rat_log_height (\<beta> v) \<and>
      roth_rat_log_height (\<beta> v) \<le> \<xi>*T \<and>
      T \<le> real (r v)*roth_rat_log_height (\<beta> v) \<and>
      real (r v)*roth_rat_log_height (\<beta> v) \<le> (1+\<xi>)*T \<and>
      \<bar>of_rat (\<beta> v) - \<alpha>\<bar> \<le> exp (-\<kappa>*roth_rat_log_height (\<beta> v))"
    and ratios: "\<forall>v. Suc v < m \<longrightarrow> real (r (Suc v)) \<le> \<sigma>*real (r v)"
    and sumb: "real (\<Sum>v<m. r v) \<le> real m*((1+\<xi>)*T/B)"
    using selected unfolding roth_selected_parameters_def by blast+
  have Tgap: "ln 2 < real m*T*\<xi>/2" and Theight: "ln 2 \<le> \<sigma>*T/2"
    using Abounds TA by (auto simp: algebra_simps)
  let ?\<beta> = "\<lambda>v. if v < m then \<beta> v else \<beta> 0"
  have near_all: "\<And>v. \<bar>of_rat (?\<beta> v) - \<alpha>\<bar> \<le> exp (-\<kappa>*roth_rat_log_height (?\<beta> v))"
    using rbounds mpos by auto
  have rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v" using rbounds by blast
  have ratio: "\<And>v. Suc v < m \<Longrightarrow> r (Suc v) \<le> \<eta>^(2^(m-1)) * r v"
    using ratios by (simp add: \<sigma>_def)
  have hlow: "\<And>v. v < m \<Longrightarrow> B \<le> roth_rat_log_height (?\<beta> v)"
    using rbounds by auto
  have wlow: "\<And>v. v < m \<Longrightarrow> T \<le> real (r v)*roth_rat_log_height (?\<beta> v)"
    using rbounds by auto
  have whigh: "\<And>v. v < m \<Longrightarrow> r v * roth_rat_log_height (?\<beta> v) \<le> (1+\<xi>)*T"
    using rbounds by auto

  text \<open>Pay the logarithmic costs needed for index transfer and Roth's lemma.\<close>
  have hlow0: "B \<le> roth_rat_log_height (?\<beta> 0)" by (rule hlow[OF mpos])
  have whigh0: "r 0 * roth_rat_log_height (?\<beta> 0) \<le> (1+\<xi>)*T"
    by (rule whigh[OF mpos])
  have rbound: "r 0 \<le> (1+\<xi>)*T/B"
    by (rule roth_degree_from_weighted[OF Bpos hlow0 whigh0])
  have gap: "ln 2 + real (\<Sum>v<m. r v) * (?C+?D) + m * (1+\<xi>)*T <
             \<kappa> * T * (m * (1-\<epsilon>)/2 - \<epsilon> * m)"
    by (rule roth_numeric_gap[OF mpos Tpos _ sumb Bgap Tgap eq])
      (use Cnonneg Dnonneg in simp)
  have hbudget: "real m*((1+\<xi>)*T/B)*(?C+4) \<le> \<sigma>*T/2"
    by (rule roth_height_budget[OF Tpos Bheight])
  have hcost: "ln 2 + real (\<Sum>v<m. r v)*?C + 4*real m*real (r 0) \<le> \<sigma>*T"
    by (rule roth_numeric_height[OF Cnonneg sumb rbound hbudget Theight])
  let ?coeff_bound_int = "(2::int) * (4 * roth_power_base f) ^ (\<Sum>v<m. r v)"
  let ?coeff_bound_nat = "nat ?coeff_bound_int"
  have hbound: "ln (real ?coeff_bound_nat) +
    4*real m*real (r 0) \<le> \<eta>^(2^(m-1))*real (r v)*roth_rat_log_height (?\<beta> v)"
    if vm: "v < m" for v
  proof -
    have hw: "\<sigma>*T \<le> \<sigma>*(real (r v)*roth_rat_log_height (?\<beta> v))"
      by (rule mult_left_mono[OF wlow[OF vm]]) (use sigpos in simp)
    have eqlog: "ln (real ?coeff_bound_nat) =
      ln 2 + real (\<Sum>w<m. r w) * ?C"
      using roth_auxiliary_bound_log[OF bpos, of "\<Sum>w<m. r w"] by simp
    show ?thesis using hcost hw eqlog by (simp add: \<sigma>_def)
  qed

  text \<open>The auxiliary polynomial has a large index at the algebraic point.\<close>
  let ?aux_witness = "\<lambda>P :: int mpoly.
      P \<noteq> 0 \<and> roth_poly_in_box m r P \<and>
      ereal (real m * (1-\<epsilon>) / 2) \<le>
        roth_index m r (\<lambda>_. \<alpha>) (replace_coeff (of_int::int \<Rightarrow> real) P) \<and>
      (\<forall>K. abs (MPoly_Type.coeff P K) \<le> ?coeff_bound_int)"
  have aux_exists: "\<exists>P :: int mpoly. ?aux_witness P"
    by (rule roth_auxiliary_polynomial_monic_exp
      [where f=f and a=\<alpha> and d="?d" and m=m and r=r and eps=\<epsilon>,
       OF monic refl dpos root mpos rpos epos elt agap]) simp
  obtain P :: "int mpoly" where P: "?aux_witness P"
    using aux_exists by (erule exE)
  have pn: "P \<noteq> 0" and pb: "roth_poly_in_box m r P"
    and pi: "ereal (real m * (1-\<epsilon>) / 2) \<le>
      roth_index m r (\<lambda>_. \<alpha>) (replace_coeff (of_int::int \<Rightarrow> real) P)"
    and pc: "\<forall>K. abs (MPoly_Type.coeff P K) \<le> ?coeff_bound_int"
    using P by blast+
  have base: "1 \<le> 4 * roth_power_base f"
    using bpos by simp
  have pow: "1 \<le> (4 * roth_power_base f) ^ (\<Sum>v<m. r v)"
    by (rule one_le_power[OF base])
  have Hpos: "1 \<le> ?coeff_bound_int" using pow by simp
  have ph: "roth_int_coeff_sup P \<le> ?coeff_bound_nat"
    by (rule roth_int_coeff_sup_le) (use Hpos pc in \<open>auto intro: nat_mono\<close>)
  have hlog: "ln (real (roth_int_coeff_sup P)) \<le> ln (real ?coeff_bound_nat)"
    by (rule roth_int_coeff_sup_log_mono[OF ph])
  have hh: "ln (roth_int_coeff_sup P) + 4 * real m * real (r 0) \<le>
      \<eta>^(2^(m-1)) *r v * roth_rat_log_height (?\<beta> v)"
    if "v<m" for v
    using hlog hbound[OF that] by linarith

  text \<open>Index transfer gives the opposing bound at the rational points.\<close>
  let ?height_sum = "(\<Sum>v<m. real (r v) * roth_rat_log_height (?\<beta> v))"
  have sum_le: "?height_sum \<le> m * ((1+\<xi>)*T)"
    by (rule roth_weighted_height_sum_le[OF whigh])
  let ?index_gap = "real m * (1-\<epsilon>) / 2 - \<epsilon> * m"
  have gap': "ln 2 + real (\<Sum>v<m. r v) * (ln (4 * real_of_int (roth_power_base f)) +
          ln (16 * max 1 (abs \<alpha>))) + ?height_sum <
      \<kappa> * T * ?index_gap"
    using sum_le gap by linarith
  have kpos: "0 \<le> \<kappa>" using kap by simp
  have Lpos: "0 \<le> T" using Tpos by simp
  have height_log: "ln (real (roth_int_coeff_sup P)) \<le>
      ln 2 + real (\<Sum>v<m. r v) * ?C"
    by (rule roth_auxiliary_height_log[OF bpos ph])
  have cost_gap: "ln (real (roth_int_coeff_sup P)) +
      real (\<Sum>v<m. r v) * ?D + ?height_sum <
      \<kappa> * T * ?index_gap"
    using height_log gap' by (simp add: algebra_simps)
  let ?transfer_cost = "real (card (roth_exponent_box m r)) ^ 2 *
      real (4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs \<alpha>) ^ r v)"
  have transfer_gap: "ln ?transfer_cost + ?height_sum <
      \<kappa> * T * ?index_gap"
    using roth_box_log_cost[of m r P \<alpha>] cost_gap by linarith
  have "ereal (\<epsilon> * real m) \<le> roth_index m r ?\<beta> (replace_coeff of_int P)"
    by (rule roth_index_transfer_log_gap[OF pb rpos wlow kpos Lpos pi near_all transfer_gap])
  also have "\<dots> \<le> ereal (2*real m*\<eta>)"
    by (rule roth_lemma_integer[OF mpos pn pb rpos etapos etahalf ratio hh])
  finally have "\<epsilon> * m \<le> 2 * m * \<eta>" "2 * \<eta> * m < \<epsilon> * m"
    by (simp_all add: eta_small mpos)
  then show False by (simp add: mult_ac)
qed

theorem roth_algebraic_integer_finite:
  fixes \<alpha> \<delta> :: real
  assumes alg: "algebraic_int \<alpha>" and \<delta>: "0 < \<delta>"
  shows "finite (roth_good_pairs \<alpha> (2+\<delta>))"
  using algebraic_int_altdef_ipoly assms(1,2) roth_monic_finite by blast

subsection \<open>Reduction to algebraic integers\<close>

lemma roth_algebraic_integral_scale:
  fixes \<alpha> :: real
  assumes "algebraic \<alpha>"
  obtains c :: int where "c > 0" "algebraic_int (of_int c * \<alpha>)"
proof -
  obtain p :: "int poly" where root: "ipoly p \<alpha> = 0" and p0: "p \<noteq> 0"
    using assms by (auto simp: algebraic_altdef_ipoly)
  let ?c = "\<bar>Polynomial.lead_coeff p\<bar>"
  have "algebraic_int (of_int ?c * \<alpha>)"
    by (rule algebraic_imp_algebraic_int'[OF root p0]) simp
  then show thesis
    using leading_coeff_0_iff p0 that zero_less_abs_iff by blast
qed

lemma roth_irrational_scaled:
  fixes c :: int and \<alpha> :: real
  assumes "c > 0" "\<alpha> \<notin> \<rat>"
  shows "of_int c * \<alpha> \<notin> \<rat>"
proof
  assume scaled: "of_int c * \<alpha> \<in> \<rat>"
  then have "(of_int c * \<alpha>) / of_int c \<in> \<rat>"
    using Rats_divide Rats_of_int by blast
  then show False
    using assms by simp
qed

theorem roth_reduction_to_integral:
  assumes integral:
    "\<And>\<beta> \<delta>::real. algebraic_int \<beta> \<Longrightarrow> \<beta> \<notin> \<rat> \<Longrightarrow>
      \<delta> > 0 \<Longrightarrow> finite (roth_good_pairs \<beta> (2 + \<delta>))"
  and alg: "algebraic \<alpha>" and irr: "\<alpha> \<notin> \<rat>"
    and \<epsilon>: "\<epsilon> > 0"
  shows "finite (roth_good_pairs \<alpha> (2 + \<epsilon>))"
proof -
  obtain c :: int where c: "c > 0" and ci: "algebraic_int (of_int c * \<alpha>)"
    using roth_algebraic_integral_scale[OF alg] by blast
  have irr': "of_int c * \<alpha> \<notin> \<rat>"
    using roth_irrational_scaled[OF c irr] .
  have \<delta>: "\<epsilon> / 2 > 0"
    using \<epsilon> by simp
  have fin: "finite (roth_good_pairs (of_int c * \<alpha>) (2 + \<epsilon> / 2))"
    by (rule integral[OF ci irr' \<delta>])
  show ?thesis
    by (rule finite_roth_good_pairs_of_scaled[OF c _ \<delta> fin]) (use \<epsilon> in simp)
qed

text \<open>Finally!\<close>
theorem roth_real_algebraic_finite:
  fixes \<alpha> \<delta> :: real
  assumes alg: "algebraic \<alpha>" and irr: "\<alpha> \<notin> \<rat>"
    and \<delta>: "0 < \<delta>"
  shows "finite (roth_good_pairs \<alpha> (2+\<delta>))"
  using assms roth_algebraic_integer_finite roth_reduction_to_integral
  by presburger

end
