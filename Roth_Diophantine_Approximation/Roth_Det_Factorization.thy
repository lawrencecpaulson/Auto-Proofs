theory Roth_Det_Factorization
  imports Roth_Det_Bridge
begin

section \<open>Nonzero factors of the tensor determinant\<close>

theorem roth_tensor_det_factors:
  fixes phi psi :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>l<k. roth_poly_in_box n r (phi l)"
    and li: "roth_mpoly_indep k phi"
    and qv: "\<And>l. l<k \<Longrightarrow> vars (psi l) \<subseteq> {n}"
    and ri: "roth_poly_indep k (\<lambda>l. mpoly_to_poly n (psi l))"
  shows "\<exists>mu U L.
    (\<forall>i<k. Poly_Mapping.keys (mu i) \<subseteq> {..<n} \<and>
      roth_total_order n (mu i) \<le> i) \<and>
    U = det (mat k k (\<lambda>(i,l). roth_hasse (mu i) (phi l))) \<and>
    L = det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (psi l))) \<and>
    U \<noteq> 0 \<and> L \<noteq> 0 \<and>
    det (mat k k (\<lambda>(i,j).
      roth_hasse (mu i + Poly_Mapping.single n j)
        (\<Sum>l<k. phi l * psi l))) = U * L"
proof -
  obtain mu where row: "\<forall>i<k.
      Poly_Mapping.keys (mu i) \<subseteq> {..<n} \<and>
      roth_total_order n (mu i) \<le> i"
    and un: "det (mat k k (\<lambda>(i,l).
      roth_hasse (mu i) (phi l))) \<noteq> 0"
    using roth_generalized_wronskian[OF box li] by blast
  have ln: "det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (psi l))) \<noteq> 0"
    by (rule roth_right_det_nonzero[OF qv ri])
  have pv: "\<And>l. l<k \<Longrightarrow> vars (phi l) \<subseteq> {..<n}"
    by (rule roth_tensor_box_vars[OF box])
  have fac: "det (mat k k (\<lambda>(i,j).
      roth_hasse (mu i + Poly_Mapping.single n j)
        (\<Sum>l<k. phi l * psi l))) =
    det (mat k k (\<lambda>(i,l). roth_hasse (mu i) (phi l))) *
    det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (psi l)))"
    by (rule roth_tensor_det_factorization)
      (use row pv qv in auto)
  show ?thesis using row un ln fac by blast
qed


theorem roth_box_tensor_det_factors:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box (Suc n) r P"
    and nz: "P \<noteq> 0"
  shows "\<exists>k mu phi psi U L.
    0 < k \<and> k \<le> Suc (r n) \<and>
    (\<forall>l<k. roth_poly_in_box n r (phi l) \<and>
      roth_poly_in_box (Suc n) r (psi l) \<and>
      vars (psi l) \<subseteq> {n}) \<and>
    P = (\<Sum>l<k. phi l * psi l) \<and>
    (\<forall>i<k. Poly_Mapping.keys (mu i) \<subseteq> {..<n} \<and>
      roth_total_order n (mu i) \<le> i) \<and>
    U = det (mat k k (\<lambda>(i,l). roth_hasse (mu i) (phi l))) \<and>
    L = det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (psi l))) \<and>
    U \<noteq> 0 \<and> L \<noteq> 0 \<and>
    det (mat k k (\<lambda>(i,j).
      roth_hasse (mu i + Poly_Mapping.single n j) P)) = U * L"
proof -
  obtain B where sub: "B \<subseteq> roth_last_coeff P n ` {..r n}"
    and ne: "B \<noteq> {}" and bd: "card B \<le> Suc (r n)"
    and ind: "roth_vs.independent B"
    and boxB: "\<forall>b\<in>B. roth_poly_in_box n r b"
    and spl: "P = (\<Sum>b\<in>B.
      b * roth_right_factor P n (r n) B b)"
    using roth_tensor_basis_exists[OF box nz] by blast
  have fin: "finite B" using sub
    by (meson finite_subset finite_imageI finite_atMost)
  let ?k = "card B"
  let ?phi = "from_nat_into B"
  let ?psi = "\<lambda>l. roth_right_factor P n (r n) B (?phi l)"
  have bij: "bij_betw ?phi {..<?k} B"
    by (rule Countable_Set.bij_betw_from_nat_into_finite[OF fin])
  have boxphi: "\<forall>l<?k. roth_poly_in_box n r (?phi l)"
    using bij boxB by (auto simp: bij_betw_def)
  have li: "roth_mpoly_indep ?k ?phi"
    by (rule roth_indexed_set_indep[OF bij ind])
  have qv: "\<And>l. l<?k \<Longrightarrow> vars (?psi l) \<subseteq> {n}"
    by (rule roth_right_factor_vars)
  have ri: "roth_poly_indep ?k
    (\<lambda>l. mpoly_to_poly n (?psi l))"
    by (rule roth_indexed_right_indep[OF bij sub ind fin])
  have peq: "P = (\<Sum>l<?k. ?phi l * ?psi l)"
    by (rule roth_indexed_tensor_split[OF bij spl])
  obtain mu U L where row: "\<forall>i<?k.
      Poly_Mapping.keys (mu i) \<subseteq> {..<n} \<and>
      roth_total_order n (mu i) \<le> i"
    and ue: "U = det (mat ?k ?k (\<lambda>(i,l).
      roth_hasse (mu i) (?phi l)))"
    and le: "L = det (mat ?k ?k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (?psi l)))"
    and un: "U \<noteq> 0" and ln: "L \<noteq> 0"
    and fac: "det (mat ?k ?k (\<lambda>(i,j).
      roth_hasse (mu i + Poly_Mapping.single n j)
        (\<Sum>l<?k. ?phi l * ?psi l))) = U * L"
    using roth_tensor_det_factors[OF boxphi li qv ri] by blast
  have kp: "0<?k" using ne fin by (simp add: card_gt_0_iff)
  have boxpsi: "\<forall>l<?k. roth_poly_in_box (Suc n) r (?psi l)"
    by (simp add: roth_right_factor_box)
  show ?thesis using kp bd boxphi boxpsi qv peq row ue le un ln fac
    by (intro exI[where x="?k"] exI[where x=mu]
      exI[where x="?phi"] exI[where x="?psi"]
      exI[where x=U] exI[where x=L]) auto
qed

end
