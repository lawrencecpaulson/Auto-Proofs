theory Roth_Lemma
  imports Roth_Lemma_Structure
begin

section \<open>Roth's lemma for rational points\<close>

lemma roth_lemma_base:
  fixes P :: "rat mpoly" and eta :: real
  assumes pn: "P \<noteq> 0"
    and box: "roth_poly_in_box 1 r P"
    and rp: "0 < r 0" and ep: "0 < eta"
    and h: "roth_proj_log_height P + 4 * real (r 0) \<le>
      eta * real (r 0) * roth_rat_log_height (a 0)"
  shows "roth_index 1 r a P \<le> ereal (2 * eta)"
proof -
  have pv: "vars P \<subseteq> {0}"
    using roth_box_vars[OF box] by auto
  have box0: "roth_poly_in_box (Suc 0) r P"
    using box by simp
  have deg: "degree (mpoly_to_poly 0 P) \<le> r 0"
    by (rule roth_univariate_degree_of_box_at[OF box0])
  have hh: "roth_proj_log_height P + real (r 0) \<le>
      eta * real (r 0) * roth_rat_log_height (a 0)"
    using h by linarith
  have ib: "roth_index 1 r a P \<le> ereal eta"
    by (rule roth_univariate_index_bound_at[where v=0])
      (use pn pv rp deg ep hh in auto)
  have e2: "eta \<le> 2*eta" using ep by linarith
  show ?thesis by (rule order_trans[OF ib]) (use e2 in simp)
qed

theorem roth_lemma_aux:
  fixes P :: "rat mpoly" and eta :: real
  assumes pn: "P \<noteq> 0"
    and box: "roth_poly_in_box (Suc n) r P"
    and rp: "\<And>v. v < Suc n \<Longrightarrow> 0 < r v"
    and ep: "0 < eta" and eb: "eta \<le> 1/2"
    and ratio: "\<And>v. Suc v < Suc n \<Longrightarrow>
      real (r (Suc v)) \<le> eta^(2^n) * real (r v)"
    and height: "\<And>v. v < Suc n \<Longrightarrow>
      roth_proj_log_height P + 4*real (Suc n)*real (r 0) \<le>
        eta^(2^n) * real (r v) * roth_rat_log_height (a v)"
  shows "roth_index (Suc n) r a P \<le>
    ereal (2*real (Suc n)*eta)"
  using assms
proof (induction n arbitrary: P r a eta)
  case 0
  note hyp = this
  have "roth_index 1 r a P \<le> ereal (2*eta)"
    by (rule roth_lemma_base) (use hyp in auto)
  then show ?case by simp
next
  case (Suc n)
  let ?sigma = "eta^(2^(Suc n))"
  let ?m = "Suc (Suc n)"
  note pn = Suc.prems(1)
  note box = Suc.prems(2)
  note rp = Suc.prems(3)
  note ep = Suc.prems(4)
  note eb = Suc.prems(5)
  note ratio = Suc.prems(6)
  note height = Suc.prems(7)
  have sigma_pos: "0 < ?sigma" using ep by simp
  have sigma_sq: "?sigma \<le> eta^2"
    by (rule roth_sigma_le_eta_sq) (use ep eb in auto)
  have eta_one: "eta \<le> 1" using eb by linarith
  have sigma_eta: "?sigma \<le> eta"
    by (rule roth_sigma_le_eta) (use ep eta_one in auto)
  have sigma_half: "?sigma \<le> 1/2"
    using sigma_eta eb by linarith
  have half: "2*r (Suc v) \<le> r v" if "Suc v < ?m" for v
    by (rule roth_ratio_halving[where sigma="?sigma" and m="?m"])
      (use ratio sigma_half that in auto)
  obtain k U L where kp: "0 < k"
    and kn: "k \<le> Suc (r (Suc n))"
    and ub: "roth_poly_in_box (Suc n) (\<lambda>v. k*r v) U"
    and lb: "roth_poly_in_box ?m (\<lambda>v. k*r v) L"
    and uv: "vars U \<subseteq> {..<Suc n}"
    and lv: "vars L \<subseteq> {Suc n}"
    and un: "U \<noteq> 0" and ln: "L \<noteq> 0"
    and hb: "roth_proj_log_height (U*L) \<le>
      real k * (roth_proj_log_height P + 4 * real (r 0))"
    and ib: "ereal (real k *
      (real_of_ereal (roth_index ?m r a P))^2 /
        (2 * real ?m)) \<le>
      roth_index ?m r a (U*L) +
        ereal (real k * (real (r (Suc n)) / real (r n)))"
    using roth_lemma_structure[OF box pn half rp] by blast
  have disj: "vars U \<inter> vars L = {}" using uv lv by auto
  have fh: "roth_proj_log_height U \<le>
      real k * (roth_proj_log_height P + 4*real (r 0))"
    using roth_factor_height_bounds[OF un ln disj] hb by linarith
  have lh: "roth_proj_log_height L \<le>
      real k * (roth_proj_log_height P + 4*real (r 0))"
    using roth_factor_height_bounds[OF un ln disj] hb by linarith
  have eta2_pos: "0 < eta^2" using ep by simp
  have eta2_le_eta: "eta^2 \<le> eta"
  proof -
    have "eta^2 \<le> eta^1"
      by (rule power_decreasing) (use ep eta_one in auto)
    then show ?thesis by simp
  qed
  have eta2_half: "eta^2 \<le> 1/2"
    using eta2_le_eta eb by linarith
  have left_ratio: "real (k*r (Suc v)) \<le>
    (eta^2)^(2^n) * real (k*r v)" if "Suc v < Suc n" for v
  proof -
    have cv: "Suc v < ?m" using that by simp
    have "real (k*r (Suc v)) \<le> ?sigma * real (k*r v)"
      by (rule roth_ratio_scale[OF ratio[OF cv]])
    then show ?thesis by (simp add: roth_sigma_recursion)
  qed
  have left_height:
    "roth_proj_log_height U +
      4*real (Suc n)*real (k*r 0) \<le>
      (eta^2)^(2^n) * real (k*r v) *
        roth_rat_log_height (a v)" if "v<Suc n" for v
  proof -
    have hv: "roth_proj_log_height P +
      4*real ?m*real (r 0) \<le>
      ?sigma * real (r v) * roth_rat_log_height (a v)"
      by (rule height) (use that in simp)
    have tr: "roth_proj_log_height U +
      4*real (Suc n)*real k*real (r 0) \<le>
      ?sigma*(real k*real (r v))*roth_rat_log_height (a v)"
      by (rule roth_height_transfer_sigma[OF fh hv])
    show ?thesis using tr by (simp add: roth_sigma_recursion algebra_simps)
  qed
  have left_rp: "0 < k*r v" if "v<Suc n" for v
    using kp rp[of v] that by simp
  have UI: "roth_index (Suc n) (\<lambda>v. k*r v) a U \<le>
      ereal (2*real (Suc n)*(eta^2))"
    by (rule Suc.IH[OF un ub left_rp eta2_pos eta2_half
      left_ratio left_height])
  have UIs: "roth_index (Suc n) r a U \<le>
      ereal (real k*(2*real (Suc n)*(eta^2)))"
    by (rule roth_index_scale_bound[OF kp un UI])
  have UI_big: "roth_index ?m r a U \<le>
      ereal (2*real k*real (Suc n)*(eta^2))"
    using UIs roth_index_extend_dimension[OF uv, where r=r and a=a]
    by (simp add: algebra_simps)
  have rlast: "r (Suc n) \<le> r 0"
    by (rule roth_rates_le_first[where m="?m"])
      (use half in auto)
  have D_bound: "real (r (Suc n)) \<le>
      4*real (Suc n)*real (r 0)"
  proof -
    have d1: "(1::real) \<le> 4*real (Suc n)" by simp
    have d2: "1*real (r 0) \<le>
      (4*real (Suc n))*real (r 0)"
      by (rule mult_right_mono[OF d1]) simp
    show ?thesis using rlast d2 by linarith
  qed
  have hvlast: "roth_proj_log_height P +
      4*real ?m*real (r 0) \<le>
      ?sigma * real (r (Suc n)) *
        roth_rat_log_height (a (Suc n))"
    by (rule height) simp
  have last_height: "roth_proj_log_height L +
      real (k*r (Suc n)) \<le>
      ?sigma * real (k*r (Suc n)) *
        roth_rat_log_height (a (Suc n))"
  proof -
    have tr: "roth_proj_log_height L +
      real k*real (r (Suc n)) \<le>
      ?sigma*(real k*real (r (Suc n)))*
        roth_rat_log_height (a (Suc n))"
      by (rule roth_height_transfer_last[OF _ D_bound lh hvlast]) simp
    show ?thesis using tr by simp
  qed
  have last_deg: "degree (mpoly_to_poly (Suc n) L) \<le>
      k*r (Suc n)"
    using roth_univariate_degree_of_box_at[OF lb] by simp
  have last_rp: "0 < r (Suc n)" by (rule rp) simp
  have LI: "roth_index ?m r a L \<le> ereal (real k*?sigma)"
  proof -
    have ib: "roth_index ?m r a L \<le>
      ereal (?sigma*real (k*r (Suc n))/real (r (Suc n)))"
      by (rule roth_univariate_index_bound_degree_at
          [where v="Suc n" and D="k*r (Suc n)" and eta="?sigma"])
        (use ln lv last_rp last_deg sigma_pos last_height kp in auto)
    show ?thesis using ib last_rp by (simp add: algebra_simps)
  qed
  obtain t where t0: "0 \<le> t"
    and teq: "roth_index ?m r a P = ereal t"
    using roth_index_real_nonzero[OF pn, where m="Suc (Suc n)" and r=r and a=a]
    by blast
  obtain u where u0: "0 \<le> u"
    and ueq: "roth_index ?m r a U = ereal u"
    using roth_index_real_nonzero[OF un, where m="Suc (Suc n)" and r=r and a=a]
    by blast
  obtain l where l0: "0 \<le> l"
    and leq: "roth_index ?m r a L = ereal l"
    using roth_index_real_nonzero[OF ln, where m="Suc (Suc n)" and r=r and a=a]
    by blast
  have ubi: "u \<le> 2*real k*real (Suc n)*eta^2"
    using UI_big ueq by (simp add: algebra_simps)
  have lbi: "l \<le> real k*?sigma"
    using LI leq by simp
  have peq: "roth_index ?m r a (U*L) = ereal (u+l)"
    using roth_disjoint_index_mult[OF disj, where m="Suc (Suc n)" and r=r and a=a] ueq leq
    by simp
  have qi: "real k*t^2/(2*real ?m) \<le>
      u+l+real k*(real (r (Suc n))/real (r n))"
    using ib by (simp add: teq peq)
  have rpn: "0 < r n" by (rule rp) simp
  have rn: "real (r (Suc n)) \<le> ?sigma*real (r n)"
    by (rule ratio) simp
  have rho: "real (r (Suc n))/real (r n) \<le> ?sigma"
    by (rule roth_ratio_divide[OF rpn rn])
  have tb: "t \<le> 2*real ?m*eta"
    by (rule roth_final_index_arith
      [where m="?m" and sigma="?sigma" and
        rho="real (r (Suc n))/real (r n)"])
      (use kp ep ubi lbi rho sigma_sq qi in auto)
  show ?case using tb teq by simp
qed

theorem roth_lemma:
  fixes P :: "rat mpoly" and eta :: real
  assumes mp: "0 < m" and pn: "P \<noteq> 0"
    and box: "roth_poly_in_box m r P"
    and rp: "\<And>v. v<m \<Longrightarrow> 0<r v"
    and ep: "0<eta" and eb: "eta\<le>1/2"
    and ratio: "\<And>v. Suc v<m \<Longrightarrow>
      real (r (Suc v)) \<le> eta^(2^(m-1))*real (r v)"
    and height: "\<And>v. v<m \<Longrightarrow>
      roth_proj_log_height P + 4*real m*real (r 0) \<le>
        eta^(2^(m-1))*real (r v)*roth_rat_log_height (a v)"
  shows "roth_index m r a P \<le> ereal (2*real m*eta)"
proof -
  obtain n where meq: "m=Suc n" using mp by (cases m) auto
  have h: "roth_index (Suc n) r a P \<le>
      ereal (2*real (Suc n)*eta)"
    by (rule roth_lemma_aux[OF pn])
      (use meq box rp ep eb ratio height in auto)
  show ?thesis using h meq by simp
qed

end
