theory Roth_Auxiliary_Index_Transfer
  imports Roth_Index_Transfer
begin

lemma roth_box_log_cost:
  fixes P :: "int mpoly" and alpha :: real
  shows "ln (real (card (roth_exponent_box m r)) ^ 2 *
      real (4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs alpha) ^ r v)) \<le>
    ln (real (roth_int_coeff_sup P)) +
      real (\<Sum>v<m. r v) * ln (16 * max 1 (abs alpha))"
proof -
  let ?S = "(\<Sum>v<m. r v)"
  let ?A = "max 1 (abs alpha)"
  let ?V = "real (roth_int_coeff_sup P)"
  let ?C = "real (card (roth_exponent_box m r)) ^ 2 *
      real (4 ^ ?S * roth_int_coeff_sup P) *
      (\<Prod>v<m. ?A ^ r v)"
  let ?D = "?V * (16 * ?A) ^ ?S"
  have Vpos: "0 < ?V" using roth_int_coeff_sup_ge_one[of P] by simp
  have Apos: "0 < ?A" by simp
  have cardpos: "0 < real (card (roth_exponent_box m r))"
    using roth_box_card_pos[of m r] by simp
  have prodpos: "0 < (\<Prod>v<m. ?A ^ r v)"
    by (intro prod_pos) (use Apos in auto)
  have Cpos: "0 < ?C" using cardpos Vpos prodpos
    by (simp add: power2_eq_square)
  have Dpos: "0 < ?D" using Vpos Apos by simp
  have card: "real (card (roth_exponent_box m r) ^ 2 * 4 ^ ?S) \<le>
      real (16 ^ ?S)"
    using roth_box_card_pow16[of m r] by (metis of_nat_le_iff)
  have Cform: "?C =
      real (card (roth_exponent_box m r) ^ 2 * 4 ^ ?S) *
        ?V * ?A ^ ?S"
    by (simp add: of_nat_mult of_nat_power power_sum mult.assoc)
  have Dform: "?D = real (16 ^ ?S) * ?V * ?A ^ ?S"
    by (simp add: of_nat_power power_mult_distrib mult_ac)
  have scalepos: "0 \<le> ?V * ?A ^ ?S" using Vpos Apos by simp
  have scale: "real (card (roth_exponent_box m r) ^ 2 * 4 ^ ?S) *
      ?V * ?A ^ ?S \<le> real (16 ^ ?S) * ?V * ?A ^ ?S"
    using card scalepos by (intro mult_right_mono) auto
  have cd: "?C \<le> ?D"
    using scale Cform Dform by metis
  have logs: "ln ?C \<le> ln ?D"
    by (rule ln_mono[OF cd Cpos])
  have logD: "ln ?D = ln ?V + real ?S * ln (16 * ?A)"
    using Vpos Apos by (simp add: ln_mult ln_realpow algebra_simps)
  show ?thesis using logs logD by simp
qed

theorem roth_index_transfer_constant:
  fixes P :: "int mpoly" and beta :: "nat \<Rightarrow> rat"
    and alpha :: real and h :: "nat \<Rightarrow> real"
  assumes box: "roth_poly_in_box m r P"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa" and Lpos: "0 \<le> L"
    and index: "ereal t0 \<le> roth_index m r (\<lambda>_. alpha)
      (replace_coeff (of_int::int \<Rightarrow> real) P)"
    and near: "\<And>v. abs (of_rat (beta v) - alpha) \<le> exp (-kappa * h v)"
    and gap: "ln (real (roth_int_coeff_sup P)) +
      real (\<Sum>v<m. r v) * ln (16 * max 1 (abs alpha)) +
      (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v)) <
      kappa * L * (t0 - t1)"
  shows "ereal t1 \<le> roth_index m r beta
    (replace_coeff (of_int::int \<Rightarrow> rat) P)"
proof -
  have cost: "ln (real (card (roth_exponent_box m r)) ^ 2 *
      real (4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs alpha) ^ r v)) \<le>
    ln (real (roth_int_coeff_sup P)) +
      real (\<Sum>v<m. r v) * ln (16 * max 1 (abs alpha))"
    by (rule roth_box_log_cost)
  have loggap: "ln (real (card (roth_exponent_box m r)) ^ 2 *
      real (4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs alpha) ^ r v)) +
      (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v)) <
      kappa * L * (t0 - t1)"
    using cost gap by linarith
  show ?thesis
    by (rule roth_index_transfer_log_gap[OF box rpos balance
      kpos Lpos index near loggap])
qed

lemma roth_auxiliary_height_log:
  fixes P :: "int mpoly" and b :: int
  assumes bpos: "1 \<le> b"
    and ph: "roth_int_coeff_sup P \<le>
      nat (2 * (4 * b) ^ S)"
  shows "ln (real (roth_int_coeff_sup P)) \<le>
    ln 2 + real S * ln (4 * real_of_int b)"
proof -
  let ?B = "2 * (4 * b) ^ S"
  have Bpos: "0 \<le> ?B" using bpos by simp
  have eq: "real (nat ?B) = 2 * (4 * real_of_int b) ^ S"
    using Bpos by simp
  have h: "ln (real (roth_int_coeff_sup P)) \<le> ln (real (nat ?B))"
    by (rule roth_int_coeff_sup_log_mono[OF ph])
  show ?thesis using h bpos
    by (simp add: eq ln_mult ln_realpow algebra_simps)
qed

theorem roth_index_transfer_aux_height:
  fixes P :: "int mpoly" and beta :: "nat \<Rightarrow> rat"
    and alpha :: real and h :: "nat \<Rightarrow> real"
    and b :: int
  assumes box: "roth_poly_in_box m r P"
    and bpos: "1 \<le> b"
    and ph: "roth_int_coeff_sup P \<le>
      nat (2 * (4 * b) ^ (\<Sum>v<m. r v))"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa" and Lpos: "0 \<le> L"
    and index: "ereal t0 \<le> roth_index m r (\<lambda>_. alpha)
      (replace_coeff (of_int::int \<Rightarrow> real) P)"
    and near: "\<And>v. abs (of_rat (beta v) - alpha) \<le> exp (-kappa * h v)"
    and gap: "ln 2 + real (\<Sum>v<m. r v) *
        (ln (4 * real_of_int b) + ln (16 * max 1 (abs alpha))) +
      (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v)) <
      kappa * L * (t0 - t1)"
  shows "ereal t1 \<le> roth_index m r beta
    (replace_coeff (of_int::int \<Rightarrow> rat) P)"
proof -
  have hlog: "ln (real (roth_int_coeff_sup P)) \<le>
      ln 2 + real (\<Sum>v<m. r v) * ln (4 * real_of_int b)"
    by (rule roth_auxiliary_height_log[OF bpos ph])
  have loggap: "ln (real (roth_int_coeff_sup P)) +
      real (\<Sum>v<m. r v) * ln (16 * max 1 (abs alpha)) +
      (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v)) <
      kappa * L * (t0 - t1)"
    using hlog gap by (simp add: algebra_simps)
  show ?thesis
    by (rule roth_index_transfer_constant[OF box rpos balance
      kpos Lpos index near loggap])
qed

theorem roth_auxiliary_index_transfer:
  fixes f :: "int poly" and alpha :: real
    and beta :: "nat \<Rightarrow> rat" and h :: "nat \<Rightarrow> real"
  assumes monic: "Polynomial.lead_coeff f = 1"
    and d: "d = Polynomial.degree f"
    and dpos: "0 < d"
    and root: "poly (map_poly of_int f) alpha = 0"
    and mpos: "0 < m"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and epos: "0 < eps" and elt: "eps < 1"
    and agap: "2 * real d < real m * eps\<^sup>2"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa" and Lpos: "0 \<le> L"
    and near: "\<And>v. abs (of_rat (beta v) - alpha) \<le> exp (-kappa * h v)"
    and gap: "ln 2 + real (\<Sum>v<m. r v) *
        (ln (4 * real_of_int (roth_power_base f)) +
          ln (16 * max 1 (abs alpha))) +
      (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v)) <
      kappa * L * (real m * (1-eps) / 2 - eps * real m)"
  shows "\<exists>P :: int mpoly.
    P \<noteq> 0 \<and> roth_poly_in_box m r P \<and>
    ereal (real m * (1-eps) / 2) \<le>
      roth_index m r (\<lambda>_. alpha) (replace_coeff of_int P) \<and>
    ereal (eps * real m) \<le>
      roth_index m r beta (replace_coeff of_int P)"
proof -
  obtain P :: "int mpoly" where pn: "P \<noteq> 0"
    and pb: "roth_poly_in_box m r P"
    and pi: "ereal (real m * (1-eps) / 2) \<le>
      roth_index m r (\<lambda>_. alpha) (replace_coeff (of_int::int \<Rightarrow> real) P)"
    and ph: "roth_int_coeff_sup P \<le>
      nat (2 * (4 * roth_power_base f) ^ (\<Sum>v<m. r v))"
    using roth_auxiliary_polynomial_monic_sup
      [where f=f and a=alpha and d=d and m=m and r=r and eps=eps,
       OF monic d dpos root mpos rpos epos elt agap] by blast
  have bpos: "1 \<le> roth_power_base f"
    by (rule roth_power_base_ge_one)
  have ib: "ereal (eps * real m) \<le>
      roth_index m r beta (replace_coeff (of_int::int \<Rightarrow> rat) P)"
    by (rule roth_index_transfer_aux_height[OF pb bpos ph rpos balance
      kpos Lpos pi near gap])
  show ?thesis using pn pb pi ib by blast
qed


lemma roth_weighted_height_sum_le:
  fixes h :: "nat \<Rightarrow> real"
  assumes upper: "\<And>v. v < m \<Longrightarrow> real (r v) * h v \<le> U"
  shows "(\<Sum>v<m. real (r v) * h v) \<le> real m * U"
proof -
  have "(\<Sum>v<m. real (r v) * h v) \<le> (\<Sum>v<m. U)"
    by (intro sum_mono) (use upper in auto)
  then show ?thesis by simp
qed


theorem roth_auxiliary_index_transfer_balanced:
  fixes f :: "int poly" and alpha :: real and beta :: "nat \<Rightarrow> rat"
  assumes monic: "Polynomial.lead_coeff f = 1"
    and d: "d = Polynomial.degree f"
    and dpos: "0 < d"
    and root: "poly (map_poly of_int f) alpha = 0"
    and mpos: "0 < m"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and epos: "0 < eps" and elt: "eps < 1"
    and agap: "2 * real d < real m * eps\<^sup>2"
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
  shows "\<exists>P :: int mpoly.
    P \<noteq> 0 \<and> roth_poly_in_box m r P \<and>
    ereal (real m * (1-eps) / 2) \<le>
      roth_index m r (\<lambda>_. alpha) (replace_coeff of_int P) \<and>
    ereal (eps * real m) \<le>
      roth_index m r beta (replace_coeff of_int P)"
proof -
  have sum_le: "(\<Sum>v<m. real (r v) * roth_rat_log_height (beta v)) \<le>
      real m * U"
    by (rule roth_weighted_height_sum_le[OF balance_hi])
  have gap': "ln 2 + real (\<Sum>v<m. r v) *
        (ln (4 * real_of_int (roth_power_base f)) +
          ln (16 * max 1 (abs alpha))) +
      (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v)) <
      kappa * L * (real m * (1-eps) / 2 - eps * real m)"
    using sum_le gap by linarith
  show ?thesis
    by (rule roth_auxiliary_index_transfer[OF monic d dpos root mpos
      rpos epos elt agap balance_lo kpos Lpos near gap'])
qed

end
