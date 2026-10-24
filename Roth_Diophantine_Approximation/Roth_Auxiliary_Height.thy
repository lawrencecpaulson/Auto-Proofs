theory Roth_Auxiliary_Height
  imports Roth_Lemma_Int Roth_Auxiliary_Polynomial
begin

section \<open>The auxiliary polynomial with projective height control\<close>

lemma roth_int_coeff_sup_from_pointwise:
  fixes P :: "int mpoly" and B :: int
  assumes B: "1 \<le> B"
    and coeff: "\<And>K. abs (MPoly_Type.coeff P K) \<le> B"
  shows "roth_int_coeff_sup P \<le> nat B"
proof (rule roth_int_coeff_sup_le)
  show "1 \<le> nat B" using B by simp
  fix I
  show "nat (abs (MPoly_Type.coeff P I)) \<le> nat B"
    by (rule nat_mono[OF coeff])
qed

corollary roth_auxiliary_polynomial_monic_sup:
  fixes f :: "int poly" and a :: real
  assumes monic: "Polynomial.lead_coeff f = 1"
    and d: "d = Polynomial.degree f"
    and dpos: "0 < d"
    and root: "poly (map_poly of_int f) a = 0"
    and mpos: "0 < m"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and epos: "0 < eps"
    and elt: "eps < 1"
    and gap: "2 * real d < real m * eps\<^sup>2"
  shows "\<exists>P :: int mpoly.
    P \<noteq> 0 \<and> roth_poly_in_box m r P \<and>
    ereal (real m * (1-eps) / 2) \<le>
      roth_index m r (\<lambda>_. a) (replace_coeff of_int P) \<and>
    roth_int_coeff_sup P \<le>
      nat (2 * (4 * roth_power_base f) ^ (\<Sum>v<m. r v))"
proof -
  let ?B = "2 * (4 * roth_power_base f) ^ (\<Sum>v<m. r v)"
  obtain P :: "int mpoly" where pn: "P \<noteq> 0"
    and pb: "roth_poly_in_box m r P"
    and pi: "ereal (real m * (1-eps) / 2) \<le>
      roth_index m r (\<lambda>_. a) (replace_coeff of_int P)"
    and pc: "\<forall>K. abs (MPoly_Type.coeff P K) \<le> ?B"
    using roth_auxiliary_polynomial_monic_exp
      [where f=f and a=a and d=d and m=m and r=r and eps=eps,
       OF monic d dpos root mpos rpos epos elt gap] by blast
  have base: "1 \<le> 4 * roth_power_base f"
    using roth_power_base_ge_one[of f] by simp
  have pow: "1 \<le> (4 * roth_power_base f) ^ (\<Sum>v<m. r v)"
    by (rule one_le_power[OF base])
  have Bb: "1 \<le> ?B" using pow by simp
  have hs: "roth_int_coeff_sup P \<le> nat ?B"
    by (rule roth_int_coeff_sup_from_pointwise[OF Bb])
      (use pc in auto)
  show ?thesis using pn pb pi hs by blast
qed


section \<open>Roth bound for an auxiliary polynomial\<close>

lemma roth_int_coeff_sup_log_mono:
  fixes P :: "int mpoly" and B :: nat
  assumes h: "roth_int_coeff_sup P \<le> B"
  shows "ln (real (roth_int_coeff_sup P)) \<le> ln (real B)"
proof (rule ln_mono)
  show "real (roth_int_coeff_sup P) \<le> real B"
    using h by simp
  show "0 < real (roth_int_coeff_sup P)"
    using roth_int_coeff_sup_ge_one[of P] by simp
qed

theorem roth_auxiliary_polynomial_roth_bridge:
  fixes f :: "int poly" and alpha :: real
    and beta :: "nat \<Rightarrow> rat"
  assumes monic: "Polynomial.lead_coeff f = 1"
    and d: "d = Polynomial.degree f"
    and dpos: "0 < d"
    and root: "poly (map_poly of_int f) alpha = 0"
    and mpos: "0 < m"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and epos: "0 < eps" and elt: "eps < 1"
    and gap: "2 * real d < real m * eps\<^sup>2"
    and etapos: "0 < eta" and etahalf: "eta \<le> 1/2"
    and ratio: "\<And>v. Suc v < m \<Longrightarrow>
      real (r (Suc v)) \<le> eta^(2^(m-1))*real (r v)"
    and height: "\<And>v. v < m \<Longrightarrow>
      ln (real (nat (2 * (4 * roth_power_base f) ^
        (\<Sum>w<m. r w)))) + 4*real m*real (r 0) \<le>
      eta^(2^(m-1))*real (r v)*roth_rat_log_height (beta v)"
  shows "\<exists>P :: int mpoly.
    P \<noteq> 0 \<and> roth_poly_in_box m r P \<and>
    ereal (real m * (1-eps) / 2) \<le>
      roth_index m r (\<lambda>_. alpha) (replace_coeff of_int P) \<and>
    roth_index m r beta (replace_coeff of_int P) \<le>
      ereal (2*real m*eta)"
proof -
  let ?B = "nat (2 * (4 * roth_power_base f) ^
    (\<Sum>w<m. r w))"
  obtain P :: "int mpoly" where pn: "P \<noteq> 0"
    and pb: "roth_poly_in_box m r P"
    and pi: "ereal (real m * (1-eps) / 2) \<le>
      roth_index m r (\<lambda>_. alpha) (replace_coeff of_int P)"
    and ph: "roth_int_coeff_sup P \<le> ?B"
    using roth_auxiliary_polynomial_monic_sup
      [where f=f and a=alpha and d=d and m=m and r=r and eps=eps,
        OF monic d dpos root mpos rpos epos elt gap] by blast
  have ln_bound: "ln (real (roth_int_coeff_sup P)) \<le> ln (real ?B)"
    by (rule roth_int_coeff_sup_log_mono[OF ph])
  have hh: "ln (real (roth_int_coeff_sup P)) +
      4*real m*real (r 0) \<le>
      eta^(2^(m-1))*real (r v)*roth_rat_log_height (beta v)"
    if "v<m" for v
    using ln_bound height[OF that] by linarith
  have ib: "roth_index m r beta (replace_coeff of_int P) \<le>
      ereal (2*real m*eta)"
    by (rule roth_lemma_integer[OF mpos pn pb rpos etapos etahalf
      ratio hh])
  show ?thesis using pn pb pi ib by blast
qed

end
