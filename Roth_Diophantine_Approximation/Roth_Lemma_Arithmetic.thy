theory Roth_Lemma_Arithmetic
  imports Roth_Index_Scale
begin

lemma roth_sigma_recursion:
  "((eta::real)^2)^(2^n) = eta^(2^(Suc n))"
  by (simp add: power_mult power_Suc mult.commute)

lemma roth_sigma_le_eta:
  fixes eta :: real
  assumes e0: "0 \<le> eta" and e1: "eta \<le> 1"
  shows "eta^(2^n) \<le> eta"
proof -
  have "eta^(2^n) \<le> eta^1"
    by (rule power_decreasing) (use e0 e1 in auto)
  then show ?thesis by simp
qed

lemma roth_sigma_le_eta_sq:
  fixes eta :: real
  assumes e0: "0 \<le> eta" and e1: "eta \<le> 1"
  shows "eta^(2^(Suc n)) \<le> eta^2"
  by (rule power_decreasing)
    (use e0 e1 in auto)

lemma roth_ratio_halving:
  fixes r :: "nat \<Rightarrow> nat" and sigma :: real
  assumes ratio: "\<And>v. Suc v<m \<Longrightarrow>
      real (r (Suc v)) \<le> sigma * real (r v)"
    and sb: "sigma \<le> 1/2"
    and vm: "Suc v<m"
  shows "2 * r (Suc v) \<le> r v"
proof -
  have "real (r (Suc v)) \<le> sigma * real (r v)"
    by (rule ratio[OF vm])
  also have "... \<le> (1/2) * real (r v)"
    by (rule mult_right_mono[OF sb]) simp
  finally show ?thesis by linarith
qed

lemma roth_ratio_divide:
  fixes r :: "nat \<Rightarrow> nat" and sigma :: real
  assumes rp: "0 < r n"
    and ratio: "real (r (Suc n)) \<le> sigma * real (r n)"
  shows "real (r (Suc n)) / real (r n) \<le> sigma"
  using rp ratio by (simp add: pos_divide_le_eq)

lemma roth_cancel_fact:
  assumes q: "real k * t^2 / (2 * real m) \<le>
    2 * real k * real m * eta^2"
    and kp: "0<k"
  shows "t^2 / (2 * real m) \<le> 2 * real m * eta^2"
proof -
  have e1: "real k * t^2 / (2 * real m) =
    real k * (t^2 / (2 * real m))"
    by (simp add: times_divide_eq_left mult.commute)
  have e2: "2 * real k * real m * eta^2 =
    real k * (2 * real m * eta^2)"
    by (simp add: algebra_simps)
  have fac: "real k * (t^2 / (2 * real m)) \<le>
    real k * (2 * real m * eta^2)"
    using q e1 e2 by metis
  have kpos: "(0::real) < real k" using kp by simp
  show ?thesis by (rule mult_left_le_imp_le[OF fac kpos])
qed

lemma roth_sq_fact:
  assumes mp: "0 < m"
    and q: "t^2 / (2 * real m) \<le> 2 * real m * eta^2"
  shows "t^2 \<le> (2 * real m * eta)^2"
  using mp q by (simp add: pos_divide_le_eq
      power2_eq_square algebra_simps)

lemma roth_final_index_arith:
  fixes t u l rho sigma eta :: real
  assumes kp: "0 < k" and mp: "0 < m" and ep: "0 \<le> eta"
    and ub: "u \<le> 2 * real k * real (m-1) * eta^2"
    and lb: "l \<le> real k * sigma"
    and rb: "rho \<le> sigma" and sb: "sigma \<le> eta^2"
    and qb: "real k * t^2 / (2 * real m) \<le> u+l+real k*rho"
  shows "t \<le> 2 * real m * eta"
proof -
  have k0: "(0::real) \<le> real k" by simp
  have kl: "real k * sigma \<le> real k * eta^2"
    by (rule mult_left_mono[OF sb k0])
  have kr: "real k * rho \<le> real k * sigma"
    by (rule mult_left_mono[OF rb k0])
  have ar: "2 * real k * real (m-1) * eta^2 +
      2 * real k * eta^2 = 2 * real k * real m * eta^2"
    using mp by (simp add: of_nat_diff algebra_simps)
  have bv: "u+l+real k*rho \<le> 2 * real k * real m * eta^2"
    using ub lb kr kl ar by linarith
  have q: "real k * t^2 / (2 * real m) \<le>
      2 * real k * real m * eta^2"
    using qb bv by linarith
  have q': "t^2 / (2 * real m) \<le> 2 * real m * eta^2"
    by (rule roth_cancel_fact[OF q kp])
  have sq: "t^2 \<le> (2 * real m * eta)^2"
    by (rule roth_sq_fact[OF mp q'])
  show ?thesis by (rule power2_le_imp_le[OF sq])
    (use ep in auto)
qed

lemma roth_ratio_scale:
  fixes r :: "nat \<Rightarrow> nat" and sigma :: real
  assumes ratio: "real (r (Suc v)) \<le> sigma * real (r v)"
  shows "real (k * r (Suc v)) \<le> sigma * real (k * r v)"
proof -
  have "real k * real (r (Suc v)) \<le>
    real k * (sigma * real (r v))"
    by (rule mult_left_mono[OF ratio]) simp
  then show ?thesis by (simp add: mult.commute mult.left_commute)
qed

lemma roth_height_transfer_sigma:
  fixes hF hP sigma H r0 rv :: real
  assumes fb: "hF \<le> real k * (hP + 4*r0)"
    and hb: "hP + 4*real (Suc n)*r0 \<le> sigma*rv*H"
  shows "hF + 4*real n*real k*r0 \<le> sigma*(real k*rv)*H"
proof -
  have f: "hF + 4*real n*real k*r0 \<le>
    real k * (hP + 4*real (Suc n)*r0)"
    using fb by (simp add: algebra_simps)
  have g: "real k * (hP + 4*real (Suc n)*r0) \<le>
    real k * (sigma*rv*H)"
    by (rule mult_left_mono[OF hb]) simp
  show ?thesis using f g by (simp add: algebra_simps)
qed

lemma roth_height_transfer_last:
  fixes hF hP sigma H r0 rv D :: real
  assumes d0: "0 \<le> D" and d: "D \<le> 4*real n*r0"
    and fb: "hF \<le> real k * (hP + 4*r0)"
    and hb: "hP + 4*real (Suc n)*r0 \<le> sigma*rv*H"
  shows "hF + real k*D \<le> sigma*(real k*rv)*H"
proof -
  have k0: "(0::real) \<le> real k" by simp
  have f: "hF + real k*D \<le>
    real k * (hP + 4*r0 + D)"
    using fb by (simp add: algebra_simps)
  have h: "hP + 4*r0 + D \<le>
    hP + 4*real (Suc n)*r0"
    using d by (simp add: algebra_simps)
  have g: "real k*(hP + 4*r0 + D) \<le>
    real k*(hP + 4*real (Suc n)*r0)"
    by (rule mult_left_mono[OF h k0])
  have z: "real k*(hP + 4*real (Suc n)*r0) \<le>
    real k*(sigma*rv*H)"
    by (rule mult_left_mono[OF hb k0])
  show ?thesis using f g z by (simp add: algebra_simps)
qed

lemma roth_rates_le_first:
  fixes r :: "nat \<Rightarrow> nat"
  assumes half: "\<And>v. Suc v < m \<Longrightarrow> 2*r (Suc v) \<le> r v"
    and vm: "v<m"
  shows "r v \<le> r 0"
  using vm
proof (induction v)
  case 0
  then show ?case by simp
next
  case (Suc v)
  have vp: "v<m" using Suc.prems by simp
  have le: "r (Suc v) \<le> r v" using half[OF Suc.prems] by simp
  show ?case using le Suc.IH[OF vp] by linarith
qed

end
