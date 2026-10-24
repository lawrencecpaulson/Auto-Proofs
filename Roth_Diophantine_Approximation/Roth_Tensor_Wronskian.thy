theory Roth_Tensor_Wronskian
  imports Roth_Tensor_Matrix
begin

section \<open>The final-variable Wronskian\<close>

lemma roth_univariate_hasse_at:
  fixes p :: "rat poly"
  shows "mpoly_to_poly v
    (roth_hasse (Poly_Mapping.single v k) (poly_to_mpoly v p)) =
    roth_hderiv k p"
  by (rule poly_eqI)
    (simp add: roth_univariate_hasse_coeff)

lemma roth_hasse_to_hderiv_at:
  fixes \<psi> :: "rat mpoly"
  assumes qv: "vars \<psi> \<subseteq> {v}"
  shows "mpoly_to_poly v
    (roth_hasse (Poly_Mapping.single v k) \<psi>) =
    roth_hderiv k (mpoly_to_poly v \<psi>)"
  using roth_univariate_hasse_at
    [of v k "mpoly_to_poly v \<psi>"]
    mpoly_to_poly_inverse[OF qv] by simp

lemma roth_right_entry_eval:
  fixes \<psi> :: "rat mpoly"
  assumes qv: "vars \<psi> \<subseteq> {n}"
  shows "insertion (\<lambda>_. t)
    (roth_hasse (Poly_Mapping.single n j) \<psi>) =
    poly (roth_hderiv j (mpoly_to_poly n \<psi>)) t"
proof -
  have hv: "vars (roth_hasse
      (Poly_Mapping.single n j) \<psi>) \<subseteq> {n}"
    using roth_hasse_vars_subset qv by auto
  have eq: "poly (mpoly_to_poly n
      (roth_hasse (Poly_Mapping.single n j) \<psi>)) t =
    insertion (\<lambda>_. t)
      (roth_hasse (Poly_Mapping.single n j) \<psi>)"
    by (rule poly_eq_insertion[OF hv])
  show ?thesis
    using eq roth_hasse_to_hderiv_at[OF qv] by simp
qed

lemma roth_right_eval_matrix:
  fixes \<psi> :: "nat \<Rightarrow> rat mpoly"
  assumes qv: "\<And>l. l<k \<Longrightarrow> vars (\<psi> l) \<subseteq> {n}"
  shows "mat k k (\<lambda>(l,j).
      insertion (\<lambda>_. t)
        (roth_hasse (Poly_Mapping.single n j) (\<psi> l))) =
    transpose_mat (mat k k (\<lambda>(j,l).
      poly (roth_hderiv j (mpoly_to_poly n (\<psi> l))) t))"
  by (auto simp: mat_eq_iff roth_right_entry_eval qv)

lemma roth_right_det_eval:
  fixes \<psi> :: "nat \<Rightarrow> rat mpoly"
  assumes qv: "\<And>l. l<k \<Longrightarrow> vars (\<psi> l) \<subseteq> {n}"
  shows "insertion (\<lambda>_. t)
    (det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (\<psi> l)))) =
    poly (roth_hwronskian k
      (\<lambda>l. mpoly_to_poly n (\<psi> l))) t"
  by (simp add: roth_insertion_det
    roth_right_eval_matrix[OF qv] det_transpose[where n=k]
    roth_poly_det roth_hwronskian_def)

theorem roth_right_det_nonzero:
  fixes \<psi> :: "nat \<Rightarrow> rat mpoly"
  assumes qv: "\<And>l. l<k \<Longrightarrow> vars (\<psi> l) \<subseteq> {n}"
    and ind: "roth_poly_indep k
      (\<lambda>l. mpoly_to_poly n (\<psi> l))"
  shows "det (mat k k (\<lambda>(l,j).
    roth_hasse (Poly_Mapping.single n j) (\<psi> l))) \<noteq> 0"
proof -
  have wr: "roth_hwronskian k
    (\<lambda>l. mpoly_to_poly n (\<psi> l)) \<noteq> 0"
    by (rule roth_wr_independent[OF ind])
  obtain t :: rat where nz: "poly (roth_hwronskian k
      (\<lambda>l. mpoly_to_poly n (\<psi> l))) t \<noteq> 0"
    using roth_poly_nonzero_eval[OF wr] by blast
  have ev: "insertion (\<lambda>_. t)
    (det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (\<psi> l)))) =
    poly (roth_hwronskian k
      (\<lambda>l. mpoly_to_poly n (\<psi> l))) t"
    by (rule roth_right_det_eval[OF qv])
  show ?thesis using nz ev by auto
qed

lemma roth_box_vars:
  fixes P :: "rat mpoly"
  assumes "roth_poly_in_box n r P"
  shows "vars P \<subseteq> {..<n}"
  using assms
  by (auto simp: roth_poly_in_box_def vars_def
    dest: roth_exponent_boxD(1))

lemma roth_tensor_box_vars:
  fixes \<phi> :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>l<k. roth_poly_in_box n r (\<phi> l)"
    and lk: "l<k"
  shows "vars (\<phi> l) \<subseteq> {..<n}"
proof -
  have "roth_poly_in_box n r (\<phi> l)"
    using box lk by simp
  then show ?thesis by (rule roth_box_vars)
qed

theorem roth_tensor_det_nonzero:
  fixes \<phi> \<psi> :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>l<k. roth_poly_in_box n r (\<phi> l)"
    and li: "roth_mpoly_indep k \<phi>"
    and qv: "\<And>l. l<k \<Longrightarrow> vars (\<psi> l) \<subseteq> {n}"
    and ri: "roth_poly_indep k
      (\<lambda>l. mpoly_to_poly n (\<psi> l))"
  shows "\<exists>\<mu>.
    (\<forall>i<k. Poly_Mapping.keys (\<mu> i) \<subseteq> {..<n} \<and>
      roth_total_order n (\<mu> i) \<le> i) \<and>
    det (mat k k (\<lambda>(i,j).
      roth_hasse (\<mu> i + Poly_Mapping.single n j)
        (\<Sum>l<k. \<phi> l * \<psi> l))) \<noteq> 0"
proof -
  obtain \<mu> where mb: "\<forall>i<k.
      Poly_Mapping.keys (\<mu> i) \<subseteq> {..<n} \<and>
      roth_total_order n (\<mu> i) \<le> i"
    and lnz: "det (mat k k (\<lambda>(i,l).
      roth_hasse (\<mu> i) (\<phi> l))) \<noteq> 0"
    using roth_generalized_wronskian[OF box li] by auto
  have mn: "\<And>i. i<k \<Longrightarrow>
    Poly_Mapping.keys (\<mu> i) \<subseteq> {..<n}"
    using mb by auto
  have rnz: "det (mat k k (\<lambda>(l,j).
    roth_hasse (Poly_Mapping.single n j) (\<psi> l))) \<noteq> 0"
    by (rule roth_right_det_nonzero[OF qv ri])
  have fac: "det (mat k k (\<lambda>(i,j).
      roth_hasse (\<mu> i + Poly_Mapping.single n j)
        (\<Sum>l<k. \<phi> l * \<psi> l))) =
    det (mat k k (\<lambda>(i,l).
      roth_hasse (\<mu> i) (\<phi> l))) *
    det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (\<psi> l)))"
    by (rule roth_tensor_det_factorization
      [OF mn roth_tensor_box_vars[OF box] qv])
  have nz: "det (mat k k (\<lambda>(i,j).
      roth_hasse (\<mu> i + Poly_Mapping.single n j)
        (\<Sum>l<k. \<phi> l * \<psi> l))) \<noteq> 0"
    using fac lnz rnz by simp
  show ?thesis using mb nz by auto
qed

end
