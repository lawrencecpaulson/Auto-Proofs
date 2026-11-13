(*  Title:      Gelfond_Schneider/Finite_Embedding_Bounds/Finite_Embedding_House.thy
    Author:     OpenAI Codex

Maximum modulus over a finite family of complex embeddings, with
coordinate recovery and basis-matrix identities.
*)

theory Finite_Embedding_House
  imports "Jordan_Normal_Form.Matrix_Kernel"
begin

locale finite_embedding_house =
  fixes E :: "'e set"
  assumes finite_E [intro]: "finite E"
begin

definition ehouse :: "('e => complex) => real"
  where "ehouse x \<equiv> Max (insert 0 (cmod ` x ` E))"

lemma ehouse_nonneg [simp]: "0 \<le> ehouse x"
proof -
  have "finite (insert 0 (cmod ` x ` E))"
    by blast
  moreover have mem: "0 \<in> insert 0 (cmod ` x ` E)"
    by simp
  ultimately show ?thesis
    unfolding ehouse_def using Max_ge by blast
qed

lemma cmod_le_ehouse:
  assumes "e \<in> E"
  shows "cmod (x e) \<le> ehouse x"
proof -
  have "finite (insert 0 (cmod ` x ` E))"
    by blast
  moreover have "cmod (x e) \<in> insert 0 (cmod ` x ` E)"
    using assms by auto
  ultimately show ?thesis
    unfolding ehouse_def by (meson Max_ge)
qed

lemma ehouse_leI:
  assumes  "0 \<le> B" "\<And>e. e \<in> E \<Longrightarrow> cmod (x e) \<le> B"
  shows "ehouse x \<le> B"
proof -
  have "finite (insert 0 (cmod ` x ` E))"
    by blast
  moreover have "\<forall>y\<in>insert 0 (cmod ` x ` E). y \<le> B"
    using assms by blast
  ultimately show ?thesis
    using ehouse_def by force
qed

lemma ehouse_add_le:
  "ehouse (\<lambda>e. x e + y e) \<le> ehouse x + ehouse y"
  by (intro ehouse_leI) (auto simp: cmod_le_ehouse norm_triangle_mono)

lemma ehouse_mul_le:
  "ehouse (\<lambda>e. x e * y e) \<le> ehouse x * ehouse y"
  by (rule ehouse_leI) (auto simp: norm_mult cmod_le_ehouse mult_mono)

lemma ehouse_pow_le:
  "ehouse (\<lambda>e. x e ^ n) \<le> ehouse x ^ n"
proof (rule ehouse_leI)
  show "0 \<le> ehouse x ^ n"
    by simp
next
  fix e
  assume e: "e \<in> E"
  have "cmod (x e ^ n) = cmod (x e) ^ n"
    by (induction n) (auto simp add: norm_mult)
  then show "cmod ((\<lambda>e. x e ^ n) e) \<le> ehouse x ^ n"
    by (simp add: cmod_le_ehouse e power_mono)
qed

lemma ehouse_sum_le:
  assumes finI: "finite I"
  shows "ehouse (\<lambda>e. \<Sum>i\<in>I. f i e) \<le> (\<Sum>i\<in>I. ehouse (f i))"
  using finI
proof (induction I rule: finite_induct)
  case empty
  show ?case
    by (rule ehouse_leI) simp_all
next
  case (insert i I)
  with ehouse_add_le show ?case
    by (force intro: order.trans)
qed


lemma ehouse_of_int [simp]:
  assumes "E \<noteq> {}"
  shows "ehouse (\<lambda>_. of_int n) = \<bar>n\<bar>"
proof (rule antisym)
  show "ehouse (\<lambda>_. of_int n) \<le> \<bar>n\<bar>"
    by (simp add: ehouse_leI)
next
  obtain e where e: "e \<in> E"
    using assms by blast
  have "\<bar>n\<bar> = cmod ((\<lambda>_. of_int n) e)"
    by simp
  also have "\<dots> \<le> ehouse (\<lambda>_. of_int n)"
    by (rule cmod_le_ehouse[OF e])
  finally show "\<bar>n\<bar> \<le> ehouse (\<lambda>_. of_int n)" .
qed

lemma ehouse_of_nat [simp]:
  assumes "E \<noteq> {}"
  shows "ehouse (\<lambda>_. of_nat n) = of_nat n"
  using ehouse_of_int[OF assms, of "int n"] by simp

lemma ehouse_of_int_mult_le: "ehouse (\<lambda>e. of_int n * x e) \<le> \<bar>n\<bar> * ehouse x"
proof -
  { fix e assume e: "e \<in> E"
    have "cmod ((\<lambda>e. of_int n * x e) e) = \<bar>n\<bar> * cmod (x e)"
      by (simp add: norm_mult)
    also have "\<dots> \<le> \<bar>n\<bar> * ehouse x"
      using cmod_le_ehouse[OF e, of x]
      by (intro mult_left_mono) simp_all
    finally have "cmod ((\<lambda>e. of_int n * x e) e) \<le> \<bar>n\<bar> * ehouse x" .
    then have "cmod (complex_of_int n * x e) \<le> \<bar>real_of_int n\<bar> * ehouse x"
      by simp }
  then show ?thesis
    by (simp add: ehouse_leI)
qed

lemma ehouse_bounded_int_linear_combination_le:
  assumes B_nonneg: "0 \<le> B"
  assumes basis_bnd: "\<And>j. j < D \<Longrightarrow> ehouse (basis j) \<le> K"
  assumes K_nonneg: "0 \<le> K"
  assumes coeff_bnd: "\<And>j. j < D \<Longrightarrow> \<bar>c j\<bar> \<le> B"
  shows "ehouse (\<lambda>e. \<Sum>j<D. of_int (c j) * basis j e) \<le> (of_int B :: real) * of_nat D * K"
proof -
  have term_bnd: "ehouse (\<lambda>e. of_int (c j) * basis j e) \<le> real_of_int B * K" if j: "j < D" for j
  proof -
    have "ehouse (\<lambda>e. of_int (c j) * basis j e) \<le> \<bar>c j\<bar> * ehouse (basis j)"
      by (simp add: ehouse_of_int_mult_le)
    also have "\<dots> \<le> (of_int B :: real) * K"
      using coeff_bnd[OF j] basis_bnd[OF j] B_nonneg K_nonneg
      by (intro mult_mono) auto
    finally show ?thesis .
  qed
  have "ehouse (\<lambda>e. \<Sum>j<D. of_int (c j) * basis j e) \<le> (\<Sum>j<D. ehouse (\<lambda>e. of_int (c j) * basis j e))"
    by (rule ehouse_sum_le) simp
  also have "\<dots> \<le> (\<Sum>j<D. (of_int B :: real) * K)"
    by (rule sum_mono) (simp add: term_bnd)
  also have "\<dots> = (of_int B :: real) * of_nat D * K"
    by simp
  finally show ?thesis .
qed

lemma ehouse_sum_mul_uniform_le:
  assumes A_nonneg: "0 \<le> A"
  assumes B_nonneg: "0 \<le> B"
  assumes x_bnd: "\<And>t. t < T \<Longrightarrow> ehouse (x t) \<le> A"
  assumes y_bnd: "\<And>t. t < T \<Longrightarrow> ehouse (y t) \<le> B"
  shows "ehouse (\<lambda>e. \<Sum>t<T. x t e * y t e) \<le> of_nat T * A * B"
proof -
  have term_bnd: "ehouse (\<lambda>e. x t e * y t e) \<le> A * B" if t: "t < T" for t
  proof -
    have "ehouse (\<lambda>e. x t e * y t e) \<le> ehouse (x t) * ehouse (y t)"
      by (rule ehouse_mul_le)
    also have "\<dots> \<le> A * B"
      by (simp add: mult_mono' that x_bnd y_bnd)
    finally show ?thesis .
  qed
  have "ehouse (\<lambda>e. \<Sum>t<T. x t e * y t e) \<le> (\<Sum>t<T. ehouse (\<lambda>e. x t e * y t e))"
    by (rule ehouse_sum_le) simp
  also have "\<dots> \<le> (\<Sum>t<T. A * B)"
    by (rule sum_mono) (simp add: term_bnd)
  also have "\<dots> = of_nat T * A * B"
    by simp
  finally show ?thesis .
qed

lemma cmod_sum_mul_ehouse_le:
  assumes "ehouse x \<le> A" "ehouse y \<le> B" "0 \<le> A" "0 \<le> B"
  shows "cmod (\<Sum>e\<in>E. x e * y e) \<le> of_nat (card E) * A * B"
proof -
  have term_bnd: "cmod (x e * y e) \<le> A * B" if e: "e \<in> E" for e
    using cmod_le_ehouse[OF e] assms
    by (smt (verit, best) mult_mono' norm_ge_zero norm_mult)
  then show ?thesis
    by (simp add: mult.assoc sum_norm_bound)
qed

lemma abs_int_of_ehouse_recovery_le:
  assumes recover: "(of_int n :: complex) = (\<Sum>e\<in>E. r e * y e)"
  assumes "ehouse r \<le> R" "ehouse y \<le> A" "0 \<le> R" "0 \<le> A"
  shows "\<bar>n\<bar> \<le> \<lceil>real (card E) * R * A\<rceil>"
proof -
  have real_bound: "cmod (of_int n :: complex) \<le> of_nat (card E) * R * A"
    unfolding recover using assms cmod_sum_mul_ehouse_le by blast
  then have "real_of_int \<bar>n\<bar> \<le> real_of_int \<lceil>real (card E) * R * A\<rceil>"
    by (metis ceiling_le_iff ceiling_mono norm_of_int of_int_abs)
  then show ?thesis
    by simp
qed

lemma abs_int_basis_coeff_ehouse_le:
  assumes klt: "k < D"
  assumes recover:
    "\<And>c k. k < D \<Longrightarrow>
      of_int (c k) =
        (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<D. of_int (c j) * basis j e))"
  assumes repr_bnd: "\<And>k. k < D \<Longrightarrow> ehouse (repr_coeff k) \<le> R"
  assumes R_nonneg: "0 \<le> R"
  assumes comb_bnd: "ehouse (\<lambda>e. \<Sum>j<D. of_int (c j) * basis j e) \<le> A"
  assumes A_nonneg: "0 \<le> A"
  shows "\<bar>c k\<bar> \<le> \<lceil>real (card E) * R * A\<rceil>"
  using assms abs_int_of_ehouse_recovery_le by presburger

lemma abs_int_structure_constant_ehouse_le:
  assumes recover:
    "\<And>c k. k < D \<Longrightarrow>
      (of_int (c k) :: complex) =
        (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<D. of_int (c j) * basis j e))"
  assumes repr_bnd: "\<And>k. k < D \<Longrightarrow> ehouse (repr_coeff k) \<le> R"
  assumes A_bnd: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> ehouse (\<lambda>e. a u t e) \<le> A"
  assumes basis_bnd: "\<And>j. j < D \<Longrightarrow> ehouse (basis j) \<le> K"
  assumes R_nonneg: "0 \<le> R"
  assumes A_nonneg: "0 \<le> A"
  assumes K_nonneg: "0 \<le> K"
  assumes mult_repr:
    "\<And>u t j e. u < p \<Longrightarrow> t < q \<Longrightarrow> j < D \<Longrightarrow> e \<in> E \<Longrightarrow>
      a u t e * basis j e = (\<Sum>k<D. of_int (C u t k j) * basis k e)"
  assumes up: "u < p"
  assumes tq: "t < q"
  assumes "k < D"
  assumes "j < D"
  shows "\<bar>C u t k j\<bar> \<le> \<lceil>real (card E) * R * A * K\<rceil>"
proof -
  have "ehouse (\<lambda>e. a u t e) * ehouse (basis j) \<le> A * K"
    using A_bnd[OF up tq] basis_bnd[OF \<open>j < D\<close>] A_nonneg K_nonneg
    by (intro mult_mono) auto
  then have y_bnd: "ehouse (\<lambda>e. a u t e * basis j e) \<le> A * K"
    using ehouse_mul_le order.trans by blast
  have "of_int (C u t k j) = (\<Sum>e\<in>E. repr_coeff k e * (a u t e * basis j e))"
    using recover[OF \<open>k < D\<close>] by (simp add: \<open>j < D\<close> mult_repr tq up)
  then have "\<bar>C u t k j\<bar> \<le> \<lceil>real (card E) * R * (A * K)\<rceil>"
    by (simp add: A_nonneg K_nonneg R_nonneg finite_embedding_house.abs_int_of_ehouse_recovery_le
        finite_embedding_house_axioms \<open>k < D\<close> repr_bnd y_bnd)
  then show ?thesis
    by (simp add: mult.assoc)
qed

end


section \<open>Recovery of embedding coordinates\<close>

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
  assumes "k < D"
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
    using biorthogonal[OF \<open>k < D\<close>] by simp
  also have "\<dots> = c k"
    using \<open>k < D\<close> by (simp add: if_distrib [of "(*)_"] cong: if_cong)
  finally show ?thesis .
qed

corollary recover_int_coordinate:
  assumes "k < D"
  shows "(of_int (c k)) = (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<D. of_int (c j) * basis j e))"
  using assms recover_complex_coordinate by presburger

lemma coordinate_ehouse_le:
  assumes "k < D" "ehouse (repr_coeff k) \<le> R" "0 \<le> R"
  shows "cmod (c k) \<le> of_nat (card E) * R * ehouse (\<lambda>e. \<Sum>j<D. c j * basis j e)"
proof -
  have "c k = (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<D. c j * basis j e))"
    using recover_complex_coordinate[OF \<open>k < D\<close>] by simp
  then show ?thesis
    by (simp add: assms finite_embedding_house.cmod_sum_mul_ehouse_le finite_embedding_house_axioms)
qed 

lemma abs_int_basis_coeff_ehouse_le_biorthogonal:
  assumes"k < D" "ehouse (repr_coeff k) \<le> R"
  assumes "ehouse (\<lambda>e. \<Sum>j<D. of_int (c j) * basis j e) \<le> A"
  assumes "0 \<le> R" "0 \<le> A"
  shows "\<bar>c k\<bar> \<le> \<lceil>real (card E) * R * A\<rceil>"
  using recover_int_coordinate assms abs_int_of_ehouse_recovery_le 
  by presburger

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
  where "basis_matrix_entry i j \<equiv> basis j (emb i)"

definition inverse_basis_matrix_entry :: "nat \<Rightarrow> nat \<Rightarrow> complex"
  where "inverse_basis_matrix_entry k i \<equiv> repr_coeff k (emb i)"

lemma emb_in_E:
  assumes "i < D"
  shows "emb i \<in> E"
  using ebij assms by (auto simp: bij_betw_def)

lemma card_E: "card E = D"
  using bij_betw_same_card ebij by fastforce

lemma ehouse_le_of_indexed_bound:
  assumes B_nonneg: "0 \<le> B" and "\<And>i. i < D \<Longrightarrow> cmod (f (emb i)) \<le> B"
  shows "ehouse f \<le> B"
proof (rule ehouse_leI[OF B_nonneg])
  show "\<And>e. e \<in> E \<Longrightarrow> cmod (f e) \<le> B"
    using assms bij_betw_imp_surj_on[OF ebij] by force
qed

lemma biorthogonal:
  assumes "k < D" "j < D"
  shows "(\<Sum>e\<in>E. repr_coeff k e * basis j e) = (if j = k then 1 else 0)"
proof -
  have "(\<Sum>i\<in>{0..<D}. repr_coeff k (emb i) * basis j (emb i)) = (\<Sum>e\<in>E. repr_coeff k e * basis j e)"
    by (rule sum.reindex_bij_betw[OF ebij])
  then show ?thesis
    using indexed_biorthogonal[OF assms] by (simp add: lessThan_atLeast0)
qed

lemma indexed_biorthogonal_matrix:
  assumes "k < D" "j < D"
  shows "(\<Sum>i<D. inverse_basis_matrix_entry k i * basis_matrix_entry i j) = (if j = k then 1 else 0)"
  using indexed_biorthogonal assms
  by (simp add: basis_matrix_entry_def inverse_basis_matrix_entry_def)

sublocale REC: finite_embedding_recovery E D basis repr_coeff
  by unfold_locales (auto simp: biorthogonal)

lemmas recover_complex_coordinate = REC.recover_complex_coordinate
lemmas recover_int_coordinate = REC.recover_int_coordinate
lemmas coordinate_ehouse_le = REC.coordinate_ehouse_le
lemmas abs_int_basis_coeff_ehouse_le_biorthogonal = REC.abs_int_basis_coeff_ehouse_le_biorthogonal

lemma basis_ehouse_le_of_matrix_bound:
  assumes "0 \<le> B" "\<And>i. i < D \<Longrightarrow> cmod (basis_matrix_entry i j) \<le> B"
  shows "ehouse (basis j) \<le> B"
    using assms by (intro ehouse_le_of_indexed_bound) (auto simp add: basis_matrix_entry_def)

lemma repr_coeff_ehouse_le_of_inverse_matrix_bound:
  assumes "0 \<le> R" "\<And>i. i < D \<Longrightarrow> cmod (inverse_basis_matrix_entry k i) \<le> R"
  shows "ehouse (repr_coeff k) \<le> R"
    using assms by (intro ehouse_le_of_indexed_bound) (auto simp: inverse_basis_matrix_entry_def)

lemma coordinate_ehouse_le_of_inverse_matrix_bound:
  assumes "k < D" "0 \<le> R"
  assumes "\<And>i. i < D \<Longrightarrow> cmod (inverse_basis_matrix_entry k i) \<le> R"
  shows "cmod (c k) \<le> of_nat D * R * ehouse (\<lambda>e. \<Sum>j<D. c j * basis j e)"
proof -
  have "cmod (c k) \<le> of_nat (card E) * R * ehouse (\<lambda>e. \<Sum>j<D. c j * basis j e)"
    using repr_coeff_ehouse_le_of_inverse_matrix_bound
    using assms coordinate_ehouse_le \<open>k < D\<close> by blast
  then show ?thesis
    by (simp add: card_E)
qed

lemma abs_int_basis_coeff_ehouse_le_of_inverse_matrix_bound:
  assumes "k < D"
  assumes "\<And>i. i < D \<Longrightarrow> cmod (inverse_basis_matrix_entry k i) \<le> R"
  assumes "ehouse (\<lambda>e. \<Sum>j<D. of_int (c j) * basis j e) \<le> A"
  assumes "0 \<le> R" "0 \<le> A"
  shows "\<bar>c k\<bar> \<le> \<lceil>real D * R * A\<rceil>"
proof -
  have "ehouse (repr_coeff k) \<le> R"
    using assms repr_coeff_ehouse_le_of_inverse_matrix_bound by simp
  then show ?thesis
    using assms card_E REC.abs_int_basis_coeff_ehouse_le_biorthogonal by blast
qed

end

section \<open>Basis matrices of indexed embedding families\<close>

context finite_embedding_indexed_recovery
begin

definition basis_matrix :: "complex mat"
  where "basis_matrix \<equiv> mat D D (\<lambda>(i,j). basis_matrix_entry i j)"

definition inverse_basis_matrix :: "complex mat"
  where "inverse_basis_matrix \<equiv> mat D D (\<lambda>(k,i). inverse_basis_matrix_entry k i)"

definition coeff_vec :: "(nat \<Rightarrow> complex) \<Rightarrow> complex vec"
  where "coeff_vec c \<equiv> vec D c"

definition embedding_vec :: "('e \<Rightarrow> complex) \<Rightarrow> complex vec"
  where "embedding_vec y \<equiv> vec D (\<lambda>i. y (emb i))"

lemma basis_matrix_carrier [simp]: "basis_matrix \<in> carrier_mat D D"
  unfolding basis_matrix_def by simp

lemma inverse_basis_matrix_carrier [simp]: "inverse_basis_matrix \<in> carrier_mat D D"
  unfolding inverse_basis_matrix_def by simp

lemma basis_matrix_dim [simp]: "dim_row basis_matrix = D" "dim_col basis_matrix = D"
  unfolding basis_matrix_def by simp_all

lemma inverse_basis_matrix_dim [simp]: "dim_row inverse_basis_matrix = D" "dim_col inverse_basis_matrix = D"
  unfolding inverse_basis_matrix_def by simp_all

lemma coeff_vec_dim [simp]: "dim_vec (coeff_vec c) = D"
  unfolding coeff_vec_def by simp

lemma embedding_vec_dim [simp]: "dim_vec (embedding_vec y) = D"
  unfolding embedding_vec_def by simp

lemma coeff_vec_carrier [simp]: "coeff_vec c \<in> carrier_vec D"
  unfolding coeff_vec_def by simp

lemma embedding_vec_carrier [simp]: "embedding_vec y \<in> carrier_vec D"
  unfolding embedding_vec_def by simp

lemma basis_matrix_index [simp]:
  assumes "i < D" "j < D"
  shows "basis_matrix $$ (i,j) = basis_matrix_entry i j"
  using assms unfolding basis_matrix_def by simp

lemma inverse_basis_matrix_index [simp]:
  assumes "k < D" "i < D"
  shows "inverse_basis_matrix $$ (k,i) = inverse_basis_matrix_entry k i"
  using assms unfolding inverse_basis_matrix_def by simp

lemma coeff_vec_index [simp]:
  assumes "i < D"
  shows "coeff_vec c $ i = c i"
  using assms unfolding coeff_vec_def by simp

lemma embedding_vec_index [simp]:
  assumes "i < D"
  shows "embedding_vec y $ i = y (emb i)"
  using assms unfolding embedding_vec_def by simp

lemma inverse_basis_matrix_left_inverse: "inverse_basis_matrix * basis_matrix = 1\<^sub>m D"
proof (rule eq_matI)
  fix k j
  assume lt: "k < dim_row (1\<^sub>m D)" "j < dim_col (1\<^sub>m D)"
  then have "(inverse_basis_matrix * basis_matrix) $$ (k,j) = (\<Sum>i<D. inverse_basis_matrix_entry k i * basis_matrix_entry i j)"
    by (simp add: inverse_basis_matrix_def basis_matrix_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (1\<^sub>m D) $$ (k,j)"
    using lt indexed_biorthogonal_matrix by simp
  finally show "(inverse_basis_matrix * basis_matrix) $$ (k,j) = (1\<^sub>m D) $$ (k,j)" .
qed auto

lemma basis_matrix_right_inverse: "basis_matrix * inverse_basis_matrix = 1\<^sub>m D"
  by (simp add: inverse_basis_matrix_left_inverse mat_mult_left_right_inverse)

lemma inverse_basis_matrix_inverts [simp]:
  "inverts_mat inverse_basis_matrix basis_matrix"
  using inverse_basis_matrix_left_inverse by (simp add: inverts_mat_def)

lemma basis_matrix_inverts [simp]:
  "inverts_mat basis_matrix inverse_basis_matrix"
  using basis_matrix_right_inverse by (simp add: inverts_mat_def)

lemma det_basis_matrix_nonzero: "det basis_matrix \<noteq> 0"
proof
  assume "det basis_matrix = 0"
  with det_mult[OF inverse_basis_matrix_carrier basis_matrix_carrier] show False
    by (simp add: inverse_basis_matrix_left_inverse)
qed

lemma det_inverse_basis_matrix_nonzero: "det inverse_basis_matrix \<noteq> 0"
proof
  assume "det inverse_basis_matrix = 0"
  with det_mult[OF inverse_basis_matrix_carrier basis_matrix_carrier] show False
    by (simp add: inverse_basis_matrix_left_inverse)
qed

text \<open>
  Our @{term basis_matrix} stores embeddings as rows and basis vectors as
  columns, so the transpose present in Lean's matrix formula disappears here.
\<close>

lemma basis_matrix_mul_coeff_vec:
  "basis_matrix *\<^sub>v coeff_vec c = embedding_vec (\<lambda>e. \<Sum>j<D. c j * basis j e)"
proof (rule eq_vecI)
  fix i
  assume i: "i < dim_vec (embedding_vec (\<lambda>e. \<Sum>j<D. c j * basis j e))"
  then have "(basis_matrix *\<^sub>v coeff_vec c) $ i = (\<Sum>j<D. row basis_matrix i $ j * coeff_vec c $ j)"
    by (simp add: atLeast0LessThan scalar_prod_def)
  also have "\<dots> = (\<Sum>j<D. c j * basis j (emb i))"
    using i by (intro sum.cong[OF refl]) (simp add: basis_matrix_entry_def)
  also have "\<dots> = embedding_vec (\<lambda>e. \<Sum>j<D. c j * basis j e) $ i"
    using i unfolding embedding_vec_def by simp
  finally show "(basis_matrix *\<^sub>v coeff_vec c) $ i = embedding_vec (\<lambda>e. \<Sum>j<D. c j * basis j e) $ i" .
qed auto

lemma inverse_basis_matrix_mul_embedding_vec_eq_coeff_vec:
  "inverse_basis_matrix *\<^sub>v embedding_vec (\<lambda>e. \<Sum>j<D. c j * basis j e) = coeff_vec c"
proof -
  have "inverse_basis_matrix *\<^sub>v embedding_vec (\<lambda>e. \<Sum>j<D. c j * basis j e) =
      inverse_basis_matrix *\<^sub>v (basis_matrix *\<^sub>v coeff_vec c)"
    by (simp add: basis_matrix_mul_coeff_vec[symmetric])
  also have "\<dots> = (inverse_basis_matrix * basis_matrix) *\<^sub>v coeff_vec c"
    using assoc_mult_mat_vec[OF inverse_basis_matrix_carrier basis_matrix_carrier coeff_vec_carrier] 
    by simp
  also have "\<dots> = coeff_vec c"
    by (simp add: inverse_basis_matrix_left_inverse)
  finally show ?thesis .
qed

corollary inverse_basis_matrix_mul_embedding_vec_eq_coeff:
  assumes "k < D"
  shows "(inverse_basis_matrix *\<^sub>v embedding_vec (\<lambda>e. \<Sum>j<D. c j * basis j e)) $ k = c k"
  using assms inverse_basis_matrix_mul_embedding_vec_eq_coeff_vec[of c]
  by simp

end

end
