theory Roth_Det_Factor_Bounds
  imports Roth_Det_Factorization
begin

lemma roth_vars_uminus_rat:
  "vars (-(P::rat mpoly)) = vars P"
  by (simp add: vars_def uminus_mpoly.rep_eq)

lemma roth_vars_sign_mult:
  "vars (signof q * (P::rat mpoly)) = vars P"
  by (simp add: sign_def roth_vars_uminus_rat)

lemma roth_det_vars_subset:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat mpoly"
  assumes ab: "\<And>i j. i<k \<Longrightarrow> j<k \<Longrightarrow> vars (A i j) \<subseteq> S"
  shows "vars (det (mat k k (\<lambda>(i,j). A i j))) \<subseteq> S"
proof -
  let ?Q = "{q. q permutes {..<k}}"
  have tvar: "vars (signof q * (\<Prod>i<k. A i (q i))) \<subseteq> S"
    if q: "q\<in>?Q" for q
  proof -
    have v: "vars (\<Prod>i<k. A i (q i)) \<subseteq>
      (\<Union>i<k. vars (A i (q i)))"
      by (rule roth_vars_prod_subset) simp
    have qp: "q permutes {..<k}" using q by simp
    have uv: "(\<Union>i<k. vars (A i (q i))) \<subseteq> S"
      using ab roth_permutes_bounded[OF qp] by blast
    show ?thesis using v uv by (simp add: roth_vars_sign_mult)
  qed
  have v: "vars (\<Sum>q\<in>?Q. signof q * (\<Prod>i<k. A i (q i)))
    \<subseteq> (\<Union>q\<in>?Q. vars (signof q * (\<Prod>i<k. A i (q i))))"
    by (rule vars_setsum) (simp add: finite_permutations)
  have u: "(\<Union>q\<in>?Q. vars (signof q * (\<Prod>i<k. A i (q i))))
    \<subseteq> S" using tvar by auto
  show ?thesis using v u
    by (simp add: roth_det_mat_expansion)
qed


lemma roth_det_left_vars:
  fixes phi :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>l<k. roth_poly_in_box n r (phi l)"
  shows "vars (det (mat k k (\<lambda>(i,l).
      roth_hasse (mu i) (phi l)))) \<subseteq> {..<n}"
proof (rule roth_det_vars_subset)
  fix i l
  assume "i<k" and lk: "l<k"
  have "vars (roth_hasse (mu i) (phi l)) \<subseteq> vars (phi l)"
    by (rule roth_hasse_vars_subset)
  also have "... \<subseteq> {..<n}"
    by (rule roth_box_vars) (use box lk in auto)
  finally show "vars (roth_hasse (mu i) (phi l)) \<subseteq> {..<n}" .
qed

lemma roth_det_right_vars:
  fixes psi :: "nat \<Rightarrow> rat mpoly"
  assumes qv: "\<And>l. l<k \<Longrightarrow> vars (psi l) \<subseteq> {n}"
  shows "vars (det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (psi l)))) \<subseteq> {n}"
proof (rule roth_det_vars_subset)
  fix l j
  assume lk: "l<k" and "j<k"
  have "vars (roth_hasse (Poly_Mapping.single n j) (psi l))
      \<subseteq> vars (psi l)"
    by (rule roth_hasse_vars_subset)
  also have "... \<subseteq> {n}" by (rule qv[OF lk])
  finally show "vars (roth_hasse
    (Poly_Mapping.single n j) (psi l)) \<subseteq> {n}" .
qed

lemma roth_det_left_box:
  fixes phi :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>l<k. roth_poly_in_box n r (phi l)"
  shows "roth_poly_in_box n (\<lambda>v. k*r v)
    (det (mat k k (\<lambda>(i,l). roth_hasse (mu i) (phi l))))"
  by (rule roth_box_det)
    (use box in \<open>auto intro: roth_hasse_box_monotone\<close>)

lemma roth_det_right_box:
  fixes psi :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>l<k. roth_poly_in_box (Suc n) r (psi l)"
  shows "roth_poly_in_box (Suc n) (\<lambda>v. k*r v)
    (det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (psi l))))"
  by (rule roth_box_det)
    (use box in \<open>auto intro: roth_hasse_box_monotone\<close>)


theorem roth_box_tensor_det_factors_bounded:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box (Suc n) r P"
    and nz: "P \<noteq> 0"
  shows "\<exists>k mu U L.
    0 < k \<and> k \<le> Suc (r n) \<and>
    (\<forall>i<k. Poly_Mapping.keys (mu i) \<subseteq> {..<n} \<and>
      roth_total_order n (mu i) \<le> i) \<and>
    roth_poly_in_box n (\<lambda>v. k*r v) U \<and>
    roth_poly_in_box (Suc n) (\<lambda>v. k*r v) L \<and>
    vars U \<subseteq> {..<n} \<and> vars L \<subseteq> {n} \<and>
    U \<noteq> 0 \<and> L \<noteq> 0 \<and>
    det (mat k k (\<lambda>(i,j).
      roth_hasse (mu i + Poly_Mapping.single n j) P)) = U * L"
proof -
  obtain k mu phi psi U L where kp: "0 < k"
    and kn: "k \<le> Suc (r n)"
    and fb: "\<forall>l<k. roth_poly_in_box n r (phi l) \<and>
      roth_poly_in_box (Suc n) r (psi l) \<and>
      vars (psi l) \<subseteq> {n}"
    and peq: "P = (\<Sum>l<k. phi l * psi l)"
    and row: "\<forall>i<k. Poly_Mapping.keys (mu i) \<subseteq> {..<n} \<and>
      roth_total_order n (mu i) \<le> i"
    and ue: "U = det (mat k k (\<lambda>(i,l).
      roth_hasse (mu i) (phi l)))"
    and le: "L = det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (psi l)))"
    and un: "U \<noteq> 0" and ln: "L \<noteq> 0"
    and fac: "det (mat k k (\<lambda>(i,j).
      roth_hasse (mu i + Poly_Mapping.single n j) P)) = U * L"
    using roth_box_tensor_det_factors[OF box nz] by blast
  have phib: "\<forall>l<k. roth_poly_in_box n r (phi l)"
    using fb by blast
  have psib: "\<forall>l<k. roth_poly_in_box (Suc n) r (psi l)"
    using fb by blast
  have psiv: "\<And>l. l<k \<Longrightarrow> vars (psi l) \<subseteq> {n}"
    using fb by blast
  have ub: "roth_poly_in_box n (\<lambda>v. k*r v) U"
    unfolding ue by (rule roth_det_left_box[OF phib])
  have lb: "roth_poly_in_box (Suc n) (\<lambda>v. k*r v) L"
    unfolding le by (rule roth_det_right_box[OF psib])
  have uv: "vars U \<subseteq> {..<n}"
    unfolding ue by (rule roth_det_left_vars[OF phib])
  have lv: "vars L \<subseteq> {n}"
    unfolding le by (rule roth_det_right_vars[OF psiv])
  show ?thesis using kp kn row ub lb uv lv un ln fac by blast
qed

end
