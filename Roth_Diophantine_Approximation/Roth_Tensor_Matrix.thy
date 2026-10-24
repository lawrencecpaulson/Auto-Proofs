theory Roth_Tensor_Matrix
  imports Roth_Tensor_Determinant
begin

section \<open>Tensor determinant factorization\<close>

lemma roth_hasse_tensor_entry:
  fixes \<mu> :: "(nat,nat) poly_mapping"
    and \<phi> \<psi> :: "nat \<Rightarrow> rat mpoly"
  assumes mi: "Poly_Mapping.keys \<mu> \<subseteq> {..<n}"
    and pv: "\<And>l. l<k \<Longrightarrow> vars (\<phi> l) \<subseteq> {..<n}"
    and qv: "\<And>l. l<k \<Longrightarrow> vars (\<psi> l) \<subseteq> {n}"
  shows "roth_hasse (\<mu> + Poly_Mapping.single n j)
    (\<Sum>l<k. \<phi> l * \<psi> l) =
    (\<Sum>l<k. roth_hasse \<mu> (\<phi> l) *
      roth_hasse (Poly_Mapping.single n j) (\<psi> l))"
  by (simp add: roth_hasse_sum
    roth_hasse_disjoint_product[OF mi] pv qv)

lemma roth_tensor_matrix_product:
  fixes \<mu> :: "nat \<Rightarrow> (nat,nat) poly_mapping"
    and \<phi> \<psi> :: "nat \<Rightarrow> rat mpoly"
  assumes mi: "\<And>i. i<k \<Longrightarrow>
      Poly_Mapping.keys (\<mu> i) \<subseteq> {..<n}"
    and pv: "\<And>l. l<k \<Longrightarrow> vars (\<phi> l) \<subseteq> {..<n}"
    and qv: "\<And>l. l<k \<Longrightarrow> vars (\<psi> l) \<subseteq> {n}"
  shows "mat k k (\<lambda>(i,j).
      roth_hasse (\<mu> i + Poly_Mapping.single n j)
        (\<Sum>l<k. \<phi> l * \<psi> l)) =
    mat k k (\<lambda>(i,l). roth_hasse (\<mu> i) (\<phi> l)) *
    mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (\<psi> l))"
  by (auto simp: mat_eq_iff scalar_prod_def atLeast0LessThan
    roth_hasse_tensor_entry[OF _ pv qv] mi)

lemma roth_det_mat_mult:
  fixes A B :: "nat \<times> nat \<Rightarrow> rat mpoly"
  shows "det (mat k k A * mat k k B) =
    det (mat k k A) * det (mat k k B)"
  by (rule det_mult[where n=k]) simp_all

lemma roth_det_mat_product:
  fixes C :: "rat mpoly mat"
    and A B :: "nat \<times> nat \<Rightarrow> rat mpoly"
  assumes eq: "C = mat k k A * mat k k B"
  shows "det C = det (mat k k A) * det (mat k k B)"
  using arg_cong[OF eq, of det] roth_det_mat_mult[of k A B]
  by simp

theorem roth_tensor_det_factorization:
  fixes \<mu> :: "nat \<Rightarrow> (nat,nat) poly_mapping"
    and \<phi> \<psi> :: "nat \<Rightarrow> rat mpoly"
  assumes mi: "\<And>i. i<k \<Longrightarrow>
      Poly_Mapping.keys (\<mu> i) \<subseteq> {..<n}"
    and pv: "\<And>l. l<k \<Longrightarrow> vars (\<phi> l) \<subseteq> {..<n}"
    and qv: "\<And>l. l<k \<Longrightarrow> vars (\<psi> l) \<subseteq> {n}"
  shows "det (mat k k (\<lambda>(i,j).
      roth_hasse (\<mu> i + Poly_Mapping.single n j)
        (\<Sum>l<k. \<phi> l * \<psi> l))) =
    det (mat k k (\<lambda>(i,l).
      roth_hasse (\<mu> i) (\<phi> l))) *
    det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (\<psi> l)))"
  by (rule roth_det_mat_product)
    (rule roth_tensor_matrix_product[OF mi pv qv])

end
