theory Roth_Determinant_Bounds
  imports Roth_Determinant_Coeff Roth_Index_Count
begin

theorem roth_hasse_det_projective_bound:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and nz: "P \<noteq> 0"
  shows "roth_proj_height
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) \<le>
    fact k * (4^(\<Sum>v<m. r v) * roth_proj_height P)^k"
  by (rule roth_hasse_det_projective_bound_card
    [OF box nz roth_exponent_box_card_exp_bound])


section \<open>Logarithmic determinant height\<close>

lemma roth_log_det_arith:
  fixes A B :: nat
  assumes ap: "0<A" and bp: "0<B"
    and hb: "A \<le> fact k * (4^R * B)^k"
  shows "ln (real A) \<le>
    ln (real (fact k)) + real k * (real R * ln 4 + ln (real B))"
proof -
  have le: "(real A) \<le> real (fact k * (4^R * B)^k)"
    by (rule of_nat_mono[OF hb])
  have h: "ln (real A) \<le> ln (real (fact k * (4^R * B)^k))"
    by (rule ln_mono) (use ap le in auto)
  have e: "ln (real (fact k * (4^R * B)^k)) =
    ln (real (fact k)) + real k * (real R * ln 4 + ln (real B))"
    using bp by (simp add: ln_mult ln_realpow algebra_simps)
  show ?thesis using h e by simp
qed

theorem roth_hasse_det_log_bound_card:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and nz: "P \<noteq> 0"
    and cb: "card (roth_exponent_box m r) \<le> 2^(\<Sum>v<m. r v)"
  shows "roth_proj_log_height
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) \<le>
    ln (real (fact k)) + real k *
      (real (\<Sum>v<m. r v) * ln 4 + roth_proj_log_height P)"
proof -
  let ?V = "det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))"
  have vp: "0 < roth_proj_height ?V"
    using roth_proj_height_ge_one[of ?V] by linarith
  have pp: "0 < roth_proj_height P"
    using roth_proj_height_ge_one[of P] by linarith
  have hb: "roth_proj_height ?V \<le>
    fact k * (4^(\<Sum>v<m. r v) * roth_proj_height P)^k"
    by (rule roth_hasse_det_projective_bound_card[OF box nz cb])
  show ?thesis unfolding roth_proj_log_height_def
    by (rule roth_log_det_arith[OF vp pp hb])
qed

lemma roth_halving_sum:
  fixes r :: "nat \<Rightarrow> nat"
  assumes half: "\<And>v. Suc v < m \<Longrightarrow> 2 * r (Suc v) \<le> r v"
  shows "(\<Sum>v<m. r v) \<le> 2 * r 0"
  using half
proof (induction m arbitrary: r)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have tailhalf: "2 * (r \<circ> Suc) (Suc v) \<le> (r \<circ> Suc) v"
    if "Suc v < m" for v
    using Suc.prems[of "Suc v"] that by simp
  have tail: "(\<Sum>v<m. r (Suc v)) \<le> 2 * r (Suc 0)"
    using Suc.IH[of "r \<circ> Suc"] tailhalf by simp
  show ?case
  proof (cases "m=0")
    case True
    then show ?thesis by simp
  next
    case False
    have h: "2 * r (Suc 0) \<le> r 0"
      using Suc.prems[of 0] False by simp
    show ?thesis using tail h
      by (simp only: sum.lessThan_Suc_shift) 
  qed
qed

lemma roth_halving_first:
  fixes r :: "nat \<Rightarrow> nat"
  assumes half: "\<And>v. Suc v < m \<Longrightarrow> 2 * r (Suc v) \<le> r v"
    and vm: "v<m"
  shows "r v \<le> r 0"
  using vm
proof (induction v)
  case 0
  then show ?case by simp
next
  case (Suc v)
  have rv: "r v \<le> r 0" using Suc.IH Suc.prems by arith
  have h: "2 * r (Suc v) \<le> r v"
    by (rule half[OF Suc.prems])
  show ?case using rv h by arith
qed

lemma roth_fact_bound:
  assumes kn: "k \<le> Suc n" and sn: "Suc n \<le> (2::nat)^n"
  shows "fact k \<le> (2::nat)^(k*n)"
proof -
  have f: "fact k \<le> k^k"
    using fact_le_power[of k, where ?'a=nat] by simp
  have "k^k \<le> (2^n)^k"
    by (rule power_mono) (use kn sn in auto)
  also have "(2^n)^k = (2::nat)^(k*n)"
    by (simp add: power_mult[symmetric] mult.commute)
  finally show ?thesis using f by arith
qed

lemma roth_fact_log_bound:
  assumes h: "fact k \<le> (2::nat)^(k*n)"
  shows "ln (real (fact k)) \<le> real k * real n * ln 2"
proof -
  have hreal: "real (fact k) \<le> real ((2::nat)^(k*n))"
    by (rule of_nat_mono[OF h])
  have b: "ln (real (fact k)) \<le> ln (real ((2::nat)^(k*n)))"
    by (rule ln_mono) (use hreal in auto)
  show ?thesis using b
    by (simp add: ln_realpow algebra_simps)
qed

lemma roth_ln2_bound: "5 * ln (2::real) < 4"
proof -
  have h: "(1 + (4/5::real) / 3)^3 \<le> exp (4/5)"
    using exp_ge_one_plus_x_over_n_power_n[of 3 "(4/5::real)"] by simp
  have e: "2 < exp (4/5::real)"
    using h by (simp add: power3_eq_cube; linarith)
  have loge: "ln (2::real) < ln (exp (4/5))"
    by (rule ln_less_cancel_iff[THEN iffD2]) (use e in auto)
  have "ln (2::real) < 4/5"
    using loge by simp
  then show ?thesis by linarith
qed

lemma roth_log_det_sharp_arith:
  fixes A B :: nat
  assumes log_le: "ln (real A) \<le>
      ln (real (fact k)) + real k * (real R * ln 4 + ln (real B))"
    and R_le: "R \<le> 2 * r0"
    and fact_le: "fact k \<le> (2::nat)^(k*r0)"
  shows "ln (real A) \<le> real k * (ln (real B) + 4 * real r0)"
proof -
  have factlog: "ln (real (fact k)) \<le> real k * real r0 * ln 2"
    by (rule roth_fact_log_bound[OF fact_le])
  have ln4: "ln (4::real) = 2 * ln 2"
  proof -
    have "ln (4::real) = ln ((2::real)^2)" by simp
    also have "... = 2 * ln 2" by (simp only: ln_realpow)
    finally show ?thesis .
  qed
  have rlog: "real R * ln 4 \<le> 4 * real r0 * ln 2"
  proof -
    have "real R * ln 4 \<le> (2 * real r0) * ln 4"
      by (rule mult_right_mono) (use R_le in auto)
    also have "... = 4 * real r0 * ln 2"
      by (simp add: ln4 algebra_simps)
    finally show ?thesis .
  qed
  have five: "real r0 * (5 * ln 2) \<le> real r0 * 4"
    by (rule mult_left_mono) (use roth_ln2_bound in auto)
  have inner: "real r0 * ln 2 + real R * ln 4 \<le> 4 * real r0"
    using rlog five by (simp add: algebra_simps; linarith)
  have "ln (real A) \<le>
      ln (real (fact k)) + real k * (real R * ln 4 + ln (real B))"
    by (rule log_le)
  also have "... \<le> real k * real r0 * ln 2 +
      real k * (real R * ln 4 + ln (real B))"
    using factlog by simp
  also have "... = real k * (ln (real B) +
      (real r0 * ln 2 + real R * ln 4))"
    by (simp add: algebra_simps)
  also have "... \<le> real k * (ln (real B) + 4 * real r0)"
    by (intro mult_left_mono add_left_mono inner) simp
  finally show ?thesis .
qed

theorem roth_hasse_det_log_bound_sharp_card:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and nz: "P \<noteq> 0"
    and cb: "card (roth_exponent_box m r) \<le> 2^(\<Sum>v<m. r v)"
    and half: "\<And>v. Suc v < m \<Longrightarrow> 2 * r (Suc v) \<le> r v"
    and mp: "0<m"
    and kn: "k \<le> Suc (r (m-1))"
  shows "roth_proj_log_height
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) \<le>
    real k * (roth_proj_log_height P + 4 * real (r 0))"
proof -
  have last: "r (m-1) \<le> r 0"
    by (rule roth_halving_first[where r=r and m=m and v="m-1"])
      (use half mp in auto)
  have fb: "fact k \<le> (2::nat)^(k*r 0)"
    by (rule roth_fact_bound)
      (use kn last roth_suc_le_pow2 in auto)
  have logbd: "roth_proj_log_height
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) \<le>
    ln (real (fact k)) + real k *
      (real (\<Sum>v<m. r v) * ln 4 + roth_proj_log_height P)"
    by (rule roth_hasse_det_log_bound_card[OF box nz cb])
  have sumle: "(\<Sum>v<m. r v) \<le> 2 * r 0"
    by (rule roth_halving_sum[where r=r and m=m]) (rule half)
  show ?thesis unfolding roth_proj_log_height_def
    by (rule roth_log_det_sharp_arith
      [OF logbd[unfolded roth_proj_log_height_def] sumle fb])
qed

theorem roth_hasse_det_log_bound:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P" and nz: "P \<noteq> 0"
  shows "roth_proj_log_height
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) \<le>
    ln (real (fact k)) + real k *
      (real (\<Sum>v<m. r v) * ln 4 + roth_proj_log_height P)"
  by (rule roth_hasse_det_log_bound_card
    [OF box nz roth_exponent_box_card_exp_bound])

theorem roth_hasse_det_log_bound_sharp:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and nz: "P \<noteq> 0"
    and half: "\<And>v. Suc v < m \<Longrightarrow> 2 * r (Suc v) \<le> r v"
    and mp: "0<m"
    and kn: "k \<le> Suc (r (m-1))"
  shows "roth_proj_log_height
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) \<le>
    real k * (roth_proj_log_height P + 4 * real (r 0))"
  by (rule roth_hasse_det_log_bound_sharp_card
    [OF box nz roth_exponent_box_card_exp_bound half mp kn])

end
