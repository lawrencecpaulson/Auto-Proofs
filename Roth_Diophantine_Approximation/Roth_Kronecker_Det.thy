theory Roth_Kronecker_Det
  imports Roth_Kronecker_Evaluation
begin

section \<open>Reflection of nonzero determinants\<close>

lemma roth_poly_det:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat poly"
  shows "poly (det (mat k k (\<lambda>(i,j). A i j))) t =
    det (mat k k (\<lambda>(i,j). poly (A i j) t))"
  by (simp add: roth_det_mat_expansion poly_sum poly_prod sign_def)

lemma roth_poly_nonzero_eval:
  fixes Q :: "rat poly"
  assumes "Q\<noteq>0"
  shows "\<exists>t::rat. poly Q t \<noteq> 0"
proof (rule ccontr)
  assume "\<not> (\<exists>t::rat. poly Q t \<noteq> 0)"
  then have "{t::rat. poly Q t = 0} = UNIV" by auto
  moreover have "finite {t::rat. poly Q t = 0}"
    by (rule poly_roots_finite[OF assms])
  ultimately show False by (simp add: infinite_UNIV_char_0)
qed

lemma roth_ksubst_eval_mat:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat mpoly"
  assumes "\<forall>i<k. \<forall>j<k. roth_poly_in_box m r (A i j)"
  shows "mat k k (\<lambda>(i,j). poly (roth_ksubst m B (A i j)) t) =
    mat k k (\<lambda>(i,j).
      insertion (\<lambda>v. t^(B^v)) (A i j))"
  using assms
  by (auto simp: mat_eq_iff dest: roth_ksubst_eval_insertion)

lemma roth_det_ksubst_reflect_nonzero:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>i<k. \<forall>j<k.
    roth_poly_in_box m r (A i j)"
    and nz: "det (mat k k (\<lambda>(i,j).
      roth_ksubst m B (A i j))) \<noteq> 0"
  shows "det (mat k k (\<lambda>(i,j). A i j)) \<noteq> 0"
proof -
  obtain t :: rat where h:
    "poly (det (mat k k (\<lambda>(i,j).
      roth_ksubst m B (A i j)))) t \<noteq> 0"
    using roth_poly_nonzero_eval[OF nz] by blast
  have eq: "mat k k (\<lambda>(i,j).
      poly (roth_ksubst m B (A i j)) t) =
    mat k k (\<lambda>(i,j).
      insertion (\<lambda>v. t^(B^v)) (A i j))"
    by (rule roth_ksubst_eval_mat[OF box])
  have d: "poly (det (mat k k (\<lambda>(i,j).
      roth_ksubst m B (A i j)))) t =
    insertion (\<lambda>v. t^(B^v))
      (det (mat k k (\<lambda>(i,j). A i j)))"
    by (simp add: roth_poly_det eq roth_insertion_det)
  show ?thesis using h d by auto
qed

end
