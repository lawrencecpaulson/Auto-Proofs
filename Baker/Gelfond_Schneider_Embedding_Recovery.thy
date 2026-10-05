(*  Title:      Baker/Gelfond_Schneider_Embedding_Recovery.thy
    Author:     OpenAI Codex

Abstract recovery of basis coordinates from a finite family of complex
embeddings.  This isolates the linear-algebra output of Lean's
`NumberField/EquivReindex` package in the form expected by the existing
finite-embedding house / Siegel / contradiction layers.
*)

theory Gelfond_Schneider_Embedding_Recovery
  imports Gelfond_Schneider_Embedding_House
begin

locale finite_embedding_recovery = finite_embedding_house E
  for E :: "'e set" +
  fixes D :: nat
  fixes basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes repr_coeff :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  assumes biorthogonal:
    "\<lbrakk>k < D; j < D\<rbrakk> \<Longrightarrow>
      (\<Sum>e\<in>E. repr_coeff k e * basis j e) = (if j = k then 1 else 0)"
begin

lemma recover_complex_coordinate:
  assumes klt: "k < D"
  shows "(\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<D. c j * basis j e)) = c k"
proof -
  have "(\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<D. c j * basis j e)) =
      (\<Sum>e\<in>E. \<Sum>j<D. c j * (repr_coeff k e * basis j e))"
    by (simp add: algebra_simps sum_distrib_left)
  also have "\<dots> = (\<Sum>j<D. \<Sum>e\<in>E. c j * (repr_coeff k e * basis j e))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>j<D. c j * (\<Sum>e\<in>E. repr_coeff k e * basis j e))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>j<D. c j * (if j = k then 1 else 0))"
    using biorthogonal[OF klt] by simp
  also have "\<dots> = (\<Sum>j<D. if j = k then c j else 0)"
    by (simp add:  if_distrib [of "(*)_"] cong: if_cong)
  also have "\<dots> = c k"
    using klt by simp
  finally show ?thesis .
qed

corollary recover_int_coordinate:
  assumes klt: "k < D"
  shows "(of_int (c k) :: complex) =
      (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<D. of_int (c j) * basis j e))"
  using assms recover_complex_coordinate by presburger

lemma recovered_coordinate_ehouse_le:
  assumes repr_bnd: "ehouse (repr_coeff k) \<le> R"
  assumes y_bnd: "ehouse y \<le> A"
  assumes R_nonneg: "0 \<le> R"
  assumes A_nonneg: "0 \<le> A"
  shows "cmod (\<Sum>e\<in>E. repr_coeff k e * y e) \<le> of_nat (card E) * R * A"
  by (rule cmod_sum_mul_ehouse_le[OF repr_bnd y_bnd R_nonneg A_nonneg])

lemma coordinate_ehouse_le:
  assumes klt: "k < D"
  assumes repr_bnd: "ehouse (repr_coeff k) \<le> R"
  assumes R_nonneg: "0 \<le> R"
  shows "cmod (c k) \<le> of_nat (card E) * R * ehouse (\<lambda>e. \<Sum>j<D. c j * basis j e)"
proof -
  have ck:
    "c k = (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<D. c j * basis j e))"
    using recover_complex_coordinate[OF klt, of c] by simp
  have "cmod (c k) =
      cmod (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<D. c j * basis j e))"
    using ck by simp
  also have "\<dots> \<le> of_nat (card E) * R * ehouse (\<lambda>e. \<Sum>j<D. c j * basis j e)"
    by (rule recovered_coordinate_ehouse_le
          [where y = "\<lambda>e. \<Sum>j<D. c j * basis j e"
             and A = "ehouse (\<lambda>e. \<Sum>j<D. c j * basis j e)"])
       (use repr_bnd R_nonneg ehouse_nonneg in simp_all)
  finally show ?thesis .
qed

lemma abs_int_basis_coeff_ehouse_le_biorthogonal:
  assumes klt: "k < D"
  assumes repr_bnd: "ehouse (repr_coeff k) \<le> R"
  assumes R_nonneg: "0 \<le> R"
  assumes comb_bnd: "ehouse (\<lambda>e. \<Sum>j<D. of_int (c j) * basis j e) \<le> A"
  assumes A_nonneg: "0 \<le> A"
  shows "abs (c k) \<le> ceiling (of_nat (card E) * R * A)"
proof -
  have recover:
    "(of_int (c k) :: complex) =
      (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<D. of_int (c j) * basis j e))"
    by (rule recover_int_coordinate[OF klt])
  show ?thesis
    by (rule abs_int_of_ehouse_recovery_le[OF recover repr_bnd comb_bnd R_nonneg A_nonneg])
qed

end

locale finite_embedding_indexed_recovery = finite_embedding_house E
  for E :: "'e set" +
  fixes D :: nat
  fixes emb :: "nat \<Rightarrow> 'e"
  fixes basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes repr_coeff :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  assumes ebij: "bij_betw emb {0..<D} E"
  assumes indexed_biorthogonal:
    "\<lbrakk>k < D; j < D\<rbrakk> \<Longrightarrow>
      (\<Sum>i<D. repr_coeff k (emb i) * basis j (emb i)) = (if j = k then 1 else 0)"
begin

definition basis_matrix_entry :: "nat \<Rightarrow> nat \<Rightarrow> complex"
  where "basis_matrix_entry i j = basis j (emb i)"

definition inverse_basis_matrix_entry :: "nat \<Rightarrow> nat \<Rightarrow> complex"
  where "inverse_basis_matrix_entry k i = repr_coeff k (emb i)"

lemma emb_in_E:
  assumes "i < D"
  shows "emb i \<in> E"
  using ebij assms by (auto simp: bij_betw_def)

lemma card_E: "card E = D"
  using bij_betw_same_card ebij by fastforce

lemma ehouse_le_of_indexed_bound:
  assumes B_nonneg: "0 \<le> B"
  assumes bound: "\<And>i. i < D \<Longrightarrow> cmod (f (emb i)) \<le> B"
  shows "ehouse f \<le> B"
proof (rule ehouse_leI[OF B_nonneg])
  fix e
  assume eE: "e \<in> E"
  have "e \<in> emb ` {0..<D}"
    using bij_betw_imp_surj_on[OF ebij] eE by blast
  then obtain i where i: "i < D" "emb i = e"
    by auto
  show "cmod (f e) \<le> B"
    using bound[OF i(1)] by (simp add: i(2))
qed

lemma biorthogonal:
  assumes klt: "k < D"
  assumes jlt: "j < D"
  shows "(\<Sum>e\<in>E. repr_coeff k e * basis j e) = (if j = k then 1 else 0)"
proof -
  have "(\<Sum>i\<in>{0..<D}. repr_coeff k (emb i) * basis j (emb i)) =
      (\<Sum>e\<in>E. repr_coeff k e * basis j e)"
    by (rule sum.reindex_bij_betw[OF ebij])
  then show ?thesis
    using indexed_biorthogonal[OF klt jlt] by (simp add: lessThan_atLeast0)
qed

lemma indexed_biorthogonal_matrix:
  assumes klt: "k < D"
  assumes jlt: "j < D"
  shows "(\<Sum>i<D. inverse_basis_matrix_entry k i * basis_matrix_entry i j) =
      (if j = k then 1 else 0)"
  using indexed_biorthogonal[OF klt jlt]
  by (simp add: basis_matrix_entry_def inverse_basis_matrix_entry_def)

sublocale REC: finite_embedding_recovery E D basis repr_coeff
proof
  fix k j
  assume "k < D" "j < D"
  then show "(\<Sum>e\<in>E. repr_coeff k e * basis j e) = (if j = k then 1 else 0)"
    by (rule biorthogonal)
qed

lemmas recover_complex_coordinate = REC.recover_complex_coordinate
lemmas recover_int_coordinate = REC.recover_int_coordinate
lemmas recovered_coordinate_ehouse_le = REC.recovered_coordinate_ehouse_le
lemmas coordinate_ehouse_le = REC.coordinate_ehouse_le
lemmas abs_int_basis_coeff_ehouse_le_biorthogonal = REC.abs_int_basis_coeff_ehouse_le_biorthogonal

lemma basis_ehouse_le_of_matrix_bound:
  assumes B_nonneg: "0 \<le> B"
  assumes bound: "\<And>i. i < D \<Longrightarrow> cmod (basis_matrix_entry i j) \<le> B"
  shows "ehouse (basis j) \<le> B"
proof (rule ehouse_le_of_indexed_bound[OF B_nonneg])
  fix i
  assume "i < D"
  then show "cmod (basis j (emb i)) \<le> B"
    using bound by (simp add: basis_matrix_entry_def)
qed

lemma repr_coeff_ehouse_le_of_inverse_matrix_bound:
  assumes R_nonneg: "0 \<le> R"
  assumes bound: "\<And>i. i < D \<Longrightarrow> cmod (inverse_basis_matrix_entry k i) \<le> R"
  shows "ehouse (repr_coeff k) \<le> R"
proof (rule ehouse_le_of_indexed_bound[OF R_nonneg])
  fix i
  assume "i < D"
  then show "cmod (repr_coeff k (emb i)) \<le> R"
    using bound by (simp add: inverse_basis_matrix_entry_def)
qed

lemma coordinate_ehouse_le_of_inverse_matrix_bound:
  assumes klt: "k < D"
  assumes R_nonneg: "0 \<le> R"
  assumes bound: "\<And>i. i < D \<Longrightarrow> cmod (inverse_basis_matrix_entry k i) \<le> R"
  shows "cmod (c k) \<le> of_nat D * R * ehouse (\<lambda>e. \<Sum>j<D. c j * basis j e)"
proof -
  have repr_bnd: "ehouse (repr_coeff k) \<le> R"
    by (rule repr_coeff_ehouse_le_of_inverse_matrix_bound[OF R_nonneg bound])
  have "cmod (c k) \<le> of_nat (card E) * R * ehouse (\<lambda>e. \<Sum>j<D. c j * basis j e)"
    by (rule coordinate_ehouse_le[OF klt repr_bnd R_nonneg])
  then show ?thesis
    by (simp add: card_E)
qed

lemma abs_int_basis_coeff_ehouse_le_of_inverse_matrix_bound:
  assumes klt: "k < D"
  assumes R_nonneg: "0 \<le> R"
  assumes bound: "\<And>i. i < D \<Longrightarrow> cmod (inverse_basis_matrix_entry k i) \<le> R"
  assumes comb_bnd: "ehouse (\<lambda>e. \<Sum>j<D. of_int (c j) * basis j e) \<le> A"
  assumes A_nonneg: "0 \<le> A"
  shows "abs (c k) \<le> ceiling (of_nat D * R * A)"
proof -
  have repr_bnd: "ehouse (repr_coeff k) \<le> R"
    by (rule repr_coeff_ehouse_le_of_inverse_matrix_bound[OF R_nonneg bound])
  have "abs (c k) \<le> ceiling (of_nat (card E) * R * A)"
    by (rule abs_int_basis_coeff_ehouse_le_biorthogonal[OF klt repr_bnd R_nonneg comb_bnd A_nonneg])
  then show ?thesis
    by (simp add: card_E)
qed

end

end
