(*  Title:      Finite_Embedding_Bounds/Gaussian_Integer_Example.thy
    Author:     OpenAI Codex

A two-point embedding family with the basis 1, i and its conjugate images.
*)

theory Gaussian_Integer_Example
  imports Embedding_Kernel_Bounds
begin

section \<open>A two-point embedding family\<close>

text \<open>The two indices model the identity and conjugate images of a Gaussian
integer. This small example supplies concrete data for the indexed recovery
locale, without requiring a general theory of number fields.\<close>

definition gaussian_emb :: "nat \<Rightarrow> bool"
  where "gaussian_emb i \<equiv> i = 0"

definition gaussian_basis :: "nat \<Rightarrow> bool \<Rightarrow> complex"
  where "gaussian_basis j e \<equiv> if j = 0 then 1 else if e then \<i> else -\<i>"

definition gaussian_dual :: "nat \<Rightarrow> bool \<Rightarrow> complex"
  where "gaussian_dual k e \<equiv> if k = 0 then 1 / 2 else if e then -\<i> / 2 else \<i> / 2"

lemma gaussian_sum_two [simp]:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>j<2. f j) = f 0 + f 1"
proof -
  have "({..<2} :: nat set) = {0,1}" by auto
  then show ?thesis by simp
qed

lemma gaussian_emb_bij: "bij_betw gaussian_emb {0..<2} (UNIV :: bool set)"
proof -
  have "{0..<2::nat} = {0,1}" by auto
  then show ?thesis
    unfolding bij_betw_def inj_on_def gaussian_emb_def by auto
qed

lemma gaussian_biorthogonal:
  assumes "k < 2" "j < 2"
  shows "(\<Sum>i<2. gaussian_dual k (gaussian_emb i) *
    gaussian_basis j (gaussian_emb i)) = (if j = k then 1 else 0)"
proof -
  have kcases: "k = 0 \<or> k = 1" using assms by auto
  have jcases: "j = 0 \<or> j = 1" using assms by auto
  show ?thesis
    using kcases jcases
    by (elim disjE; simp add: gaussian_dual_def gaussian_basis_def gaussian_emb_def algebra_simps)
qed

interpretation GI: finite_embedding_indexed_recovery
  "UNIV :: bool set" 2 gaussian_emb gaussian_basis gaussian_dual
proof unfold_locales
  show "finite (UNIV :: bool set)" by simp
  show "bij_betw gaussian_emb {0..<2} (UNIV :: bool set)"
    by (rule gaussian_emb_bij)
  show "\<And>k j. k < 2 \<Longrightarrow> j < 2 \<Longrightarrow>
    (\<Sum>i<2. gaussian_dual k (gaussian_emb i) * gaussian_basis j (gaussian_emb i)) =
      (if j = k then 1 else 0)"
    by (rule gaussian_biorthogonal)
qed

lemma gaussian_recover_coordinate:
  assumes "k < 2"
  shows "(\<Sum>e::bool\<in>UNIV. gaussian_dual k e *
    (\<Sum>j<2. c j * gaussian_basis j e)) = c k"
  using GI.recover_complex_coordinate[OF assms] .

lemma gaussian_basis_int_independent:
  assumes "(\<Sum>j<2. of_int (c j) * gaussian_basis j True) = 0"
  shows "\<forall>j<2. c j = 0"
proof -
  have h: "(of_int (c 0) :: complex) + of_int (c 1) * \<i> = 0"
    using assms by (simp add: gaussian_basis_def)
  have c0: "c 0 = 0"
  proof -
    have "Re ((of_int (c 0) :: complex) + of_int (c 1) * \<i>) = 0"
      using h by simp
    then show ?thesis by (simp add: mult.commute)
  qed
  have c1: "c 1 = 0"
  proof -
    have "Im ((of_int (c 0) :: complex) + of_int (c 1) * \<i>) = 0"
      using h by simp
    then show ?thesis by (simp add: mult.commute)
  qed
  show ?thesis
  proof (intro allI impI)
    fix j :: nat
    assume "j < 2"
    then have "j = 0 \<or> j = 1" by auto
    then show "c j = 0" using c0 c1 by blast
  qed
qed

end
