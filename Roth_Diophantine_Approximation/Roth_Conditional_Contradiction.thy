theory Roth_Conditional_Contradiction
  imports Roth_Auxiliary_Index_Transfer
begin

theorem roth_conditional_contradiction:
  fixes f :: "int poly" and alpha :: real and beta :: "nat \<Rightarrow> rat"
  assumes monic: "Polynomial.lead_coeff f = 1"
    and d: "d = Polynomial.degree f"
    and dpos: "0 < d"
    and root: "poly (map_poly of_int f) alpha = 0"
    and mpos: "0 < m"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and epos: "0 < eps" and elt: "eps < 1"
    and agap: "2 * real d < real m * eps\<^sup>2"
    and etapos: "0 < eta" and etahalf: "eta \<le> 1/2"
    and eta_small: "2 * eta < eps"
    and ratio: "\<And>v. Suc v < m \<Longrightarrow>
      real (r (Suc v)) \<le> eta^(2^(m-1))*real (r v)"
    and height: "\<And>v. v < m \<Longrightarrow>
      ln (real (nat (2 * (4 * roth_power_base f) ^
        (\<Sum>w<m. r w)))) + 4*real m*real (r 0) \<le>
      eta^(2^(m-1))*real (r v)*roth_rat_log_height (beta v)"
    and balance_lo: "\<And>v. v < m \<Longrightarrow>
      L \<le> real (r v) * roth_rat_log_height (beta v)"
    and balance_hi: "\<And>v. v < m \<Longrightarrow>
      real (r v) * roth_rat_log_height (beta v) \<le> U"
    and kpos: "0 \<le> kappa" and Lpos: "0 \<le> L"
    and near: "\<And>v. abs (of_rat (beta v) - alpha) \<le>
      exp (-kappa * roth_rat_log_height (beta v))"
    and gap: "ln 2 + real (\<Sum>v<m. r v) *
        (ln (4 * real_of_int (roth_power_base f)) +
          ln (16 * max 1 (abs alpha))) + real m * U <
      kappa * L * (real m * (1-eps) / 2 - eps * real m)"
  shows False
proof -
  let ?B = "nat (2 * (4 * roth_power_base f) ^ (\<Sum>v<m. r v))"
  obtain P :: "int mpoly" where pn: "P \<noteq> 0"
    and pb: "roth_poly_in_box m r P"
    and pi: "ereal (real m * (1-eps) / 2) \<le>
      roth_index m r (\<lambda>_. alpha) (replace_coeff (of_int::int \<Rightarrow> real) P)"
    and ph: "roth_int_coeff_sup P \<le> ?B"
    using roth_auxiliary_polynomial_monic_sup
      [where f=f and a=alpha and d=d and m=m and r=r and eps=eps,
       OF monic d dpos root mpos rpos epos elt agap] by blast
  have hlog: "ln (real (roth_int_coeff_sup P)) \<le> ln (real ?B)"
    by (rule roth_int_coeff_sup_log_mono[OF ph])
  have hh: "ln (real (roth_int_coeff_sup P)) +
      4*real m*real (r 0) \<le>
      eta^(2^(m-1))*real (r v)*roth_rat_log_height (beta v)"
    if "v<m" for v
    using hlog height[OF that] by linarith
  have ib: "roth_index m r beta (replace_coeff (of_int::int \<Rightarrow> rat) P) \<le>
      ereal (2*real m*eta)"
    by (rule roth_lemma_integer[OF mpos pn pb rpos etapos etahalf
      ratio hh])
  have sum_le: "(\<Sum>v<m. real (r v) * roth_rat_log_height (beta v)) \<le>
      real m * U"
    by (rule roth_weighted_height_sum_le[OF balance_hi])
  have gap': "ln 2 + real (\<Sum>v<m. r v) *
        (ln (4 * real_of_int (roth_power_base f)) +
          ln (16 * max 1 (abs alpha))) +
      (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v)) <
      kappa * L * (real m * (1-eps) / 2 - eps * real m)"
    using sum_le gap by linarith
  have bpos: "1 \<le> roth_power_base f"
    by (rule roth_power_base_ge_one)
  have ia: "ereal (eps * real m) \<le>
      roth_index m r beta (replace_coeff (of_int::int \<Rightarrow> rat) P)"
    by (rule roth_index_transfer_aux_height[OF pb bpos ph rpos
      balance_lo kpos Lpos pi near gap'])
  have upper: "eps * real m \<le> 2 * real m * eta"
    using order_trans[OF ia ib] by simp
  have mreal: "0 < real m" using mpos by simp
  have lower: "2 * eta * real m < eps * real m"
    by (rule mult_strict_right_mono[OF eta_small mreal])
  show False using upper lower by (simp add: mult_ac)
qed

end
