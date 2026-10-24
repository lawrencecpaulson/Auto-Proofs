theory Roth_Lemma_Structure
  imports Roth_Lemma_Arithmetic
begin

section \<open>Determinant factors with their quantitative bounds\<close>

lemma roth_index_real_nonzero:
  fixes P :: "rat mpoly"
  assumes pn: "P \<noteq> 0"
  shows "\<exists>t\<ge>0. roth_index m r a P = ereal t"
proof -
  obtain I where ie: "roth_index m r a P =
      ereal (roth_weight m r I)"
    using roth_index_attained[OF pn, where m=m and r=r and a=a]
    by blast
  show ?thesis using ie roth_weight_nonneg by blast
qed

lemma roth_factor_height_bounds:
  fixes U L :: "rat mpoly"
  assumes un: "U \<noteq> 0" and ln: "L \<noteq> 0"
    and disj: "vars U \<inter> vars L = {}"
  shows "roth_proj_log_height U \<le> roth_proj_log_height (U*L) \<and>
    roth_proj_log_height L \<le> roth_proj_log_height (U*L)"
proof -
  have hu: "roth_proj_log_height U \<le> roth_proj_log_height (U*L)"
    by (rule roth_proj_log_height_disjoint_factor_le[OF un ln disj])
  have dl: "vars L \<inter> vars U = {}" using disj by auto
  have hl: "roth_proj_log_height L \<le> roth_proj_log_height (U*L)"
    using roth_proj_log_height_disjoint_factor_le[OF ln un dl]
    by (simp add: mult.commute)
  show ?thesis using hu hl by simp
qed

theorem roth_lemma_structure:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box (Suc (Suc n)) r P"
    and nz: "P \<noteq> 0"
    and half: "\<And>v. Suc v < Suc (Suc n) \<Longrightarrow>
      2 * r (Suc v) \<le> r v"
    and rp: "\<And>v. v < Suc (Suc n) \<Longrightarrow> 0 < r v"
  shows "\<exists>k U L.
    0 < k \<and> k \<le> Suc (r (Suc n)) \<and>
    roth_poly_in_box (Suc n) (\<lambda>v. k*r v) U \<and>
    roth_poly_in_box (Suc (Suc n)) (\<lambda>v. k*r v) L \<and>
    vars U \<subseteq> {..<Suc n} \<and>
    vars L \<subseteq> {Suc n} \<and>
    U \<noteq> 0 \<and> L \<noteq> 0 \<and>
    roth_proj_log_height (U*L) \<le>
      real k * (roth_proj_log_height P + 4 * real (r 0)) \<and>
    ereal (real k *
      (real_of_ereal (roth_index (Suc (Suc n)) r a P))^2 /
        (2 * real (Suc (Suc n)))) \<le>
      roth_index (Suc (Suc n)) r a (U*L) +
        ereal (real k *
          (real (r (Suc n)) / real (r n)))"
proof -
  obtain k mu U L where kp: "0 < k"
    and kn: "k \<le> Suc (r (Suc n))"
    and row: "\<forall>i<k. Poly_Mapping.keys (mu i) \<subseteq> {..<Suc n} \<and>
      roth_total_order (Suc n) (mu i) \<le> i"
    and ub: "roth_poly_in_box (Suc n) (\<lambda>v. k*r v) U"
    and lb: "roth_poly_in_box (Suc (Suc n)) (\<lambda>v. k*r v) L"
    and uv: "vars U \<subseteq> {..<Suc n}"
    and lv: "vars L \<subseteq> {Suc n}"
    and un: "U \<noteq> 0" and ln: "L \<noteq> 0"
    and fac: "det (mat k k (\<lambda>(i,j).
      roth_hasse (mu i + Poly_Mapping.single (Suc n) j) P)) = U * L"
    using roth_box_tensor_det_factors_bounded[OF box nz] by blast
  have hb: "roth_proj_log_height (U*L) \<le>
    real k * (roth_proj_log_height P + 4 * real (r 0))"
    unfolding fac[symmetric]
    by (rule roth_hasse_det_log_bound_sharp[OF box nz half])
      (use kn in auto)
  have ib: "ereal (real k *
      (real_of_ereal (roth_index (Suc (Suc n)) r a P))^2 /
        (2 * real (Suc (Suc n)))) \<le>
      roth_index (Suc (Suc n)) r a (U*L) +
        ereal (real k *
          (real (r (Suc n)) / real (r n)))"
    unfolding fac[symmetric]
    by (rule roth_tensor_det_index_quadratic_box)
      (use box nz half rp kn row in auto)
  show ?thesis using kp kn ub lb uv lv un ln hb ib
    by (intro exI[where x=k] exI[where x=U]
      exI[where x=L]) auto
qed

end
