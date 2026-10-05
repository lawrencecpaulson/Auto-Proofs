(*  Title:      Finite_Embedding_Bounds/Finite_Embedding_House.thy
    Author:     OpenAI Codex

Maximum modulus over a finite family of complex embeddings, with
coordinate recovery and basis-matrix identities.
*)

theory Finite_Embedding_House
  imports
    Complex_Main
    "Jordan_Normal_Form.Matrix_Kernel"
begin

locale finite_embedding_house =
  fixes E :: "'e set"
  assumes finite_E [intro]: "finite E"
begin

definition ehouse :: "('e => complex) => real"
  where "ehouse x = Max (insert 0 (cmod ` x ` E))"

lemma ehouse_nonneg [simp]: "0 <= ehouse x"
proof -
  have fin_im: "finite (cmod ` x ` E)"
  proof -
    have "finite (x ` E)"
      using finite_E by (rule finite_imageI)
    then show ?thesis
      by (rule finite_imageI)
  qed
  have fin: "finite (insert 0 (cmod ` x ` E))"
    using fin_im by simp
  have mem: "0 \<in> insert 0 (cmod ` x ` E)"
    by simp
  show ?thesis
    unfolding ehouse_def by (rule Max_ge[OF fin mem])
qed

lemma cmod_le_ehouse:
  assumes "e \<in> E"
  shows "cmod (x e) <= ehouse x"
proof -
  have fin_im: "finite (cmod ` x ` E)"
  proof -
    have "finite (x ` E)"
      using finite_E by (rule finite_imageI)
    then show ?thesis
      by (rule finite_imageI)
  qed
  have fin: "finite (insert 0 (cmod ` x ` E))"
    using fin_im by simp
  have mem: "cmod (x e) \<in> insert 0 (cmod ` x ` E)"
    using assms by auto
  show ?thesis
    unfolding ehouse_def by (rule Max_ge[OF fin mem])
qed

lemma ehouse_leI:
  assumes B_nonneg: "0 <= B"
  assumes bound: "\<And>e. e \<in> E \<Longrightarrow> cmod (x e) <= B"
  shows "ehouse x <= B"
proof -
  have fin_im: "finite (cmod ` x ` E)"
  proof -
    have "finite (x ` E)"
      using finite_E by (rule finite_imageI)
    then show ?thesis
      by (rule finite_imageI)
  qed
  have fin: "finite (insert 0 (cmod ` x ` E))"
    using fin_im by simp
  have ne: "insert 0 (cmod ` x ` E) \<noteq> {}"
    by simp
  have ub: "\<forall>y\<in>insert 0 (cmod ` x ` E). y <= B"
  proof
    fix y
    assume y: "y \<in> insert 0 (cmod ` x ` E)"
    then consider "y = 0" | e where "e \<in> E" "y = cmod (x e)"
      by auto
    then show "y <= B"
    proof cases
      case 1
      with B_nonneg show ?thesis by simp
    next
      case 2
      with bound show ?thesis by simp
    qed
  qed
  show ?thesis
    unfolding ehouse_def by (rule Max.boundedI[OF fin ne]) (use ub in auto)
qed

lemma ehouse_add_le:
  "ehouse (\<lambda>e. x e + y e) <= ehouse x + ehouse y"
proof (rule ehouse_leI)
  show "0 <= ehouse x + ehouse y"
    by simp
next
  fix e
  assume e: "e \<in> E"
  have "cmod (x e + y e) <= cmod (x e) + cmod (y e)"
    by (rule norm_triangle_ineq)
  also have "... <= ehouse x + ehouse y"
    using cmod_le_ehouse[OF e, of x] cmod_le_ehouse[OF e, of y] by linarith
  finally show "cmod ((\<lambda>e. x e + y e) e) <= ehouse x + ehouse y"
    by simp
qed

lemma ehouse_mul_le:
  "ehouse (\<lambda>e. x e * y e) <= ehouse x * ehouse y"
proof (rule ehouse_leI)
  show "0 <= ehouse x * ehouse y"
    by simp
next
  fix e
  assume e: "e \<in> E"
  have "cmod (x e * y e) = cmod (x e) * cmod (y e)"
    by (simp add: norm_mult)
  also have "... <= ehouse x * ehouse y"
    using cmod_le_ehouse[OF e, of x] cmod_le_ehouse[OF e, of y]
    by (intro mult_mono) auto
  finally show "cmod ((\<lambda>e. x e * y e) e) <= ehouse x * ehouse y"
    by simp
qed

lemma ehouse_pow_le:
  "ehouse (\<lambda>e. x e ^ n) <= ehouse x ^ n"
proof (rule ehouse_leI)
  show "0 <= ehouse x ^ n"
    by simp
next
  fix e
  assume e: "e \<in> E"
  have "cmod (x e ^ n) = cmod (x e) ^ n"
  proof (induction n)
    case 0
    show ?case by simp
  next
    case (Suc n)
    then show ?case
      by (simp add: norm_mult)
  qed
  also have "... <= ehouse x ^ n"
    using cmod_le_ehouse[OF e, of x] by (rule power_mono) auto
  finally show "cmod ((\<lambda>e. x e ^ n) e) <= ehouse x ^ n"
    by simp
qed

lemma ehouse_sum_le:
  assumes finI: "finite I"
  shows "ehouse (\<lambda>e. \<Sum>i\<in>I. f i e) <= (\<Sum>i\<in>I. ehouse (f i))"
  using finI
proof (induction I rule: finite_induct)
  case empty
  show ?case
    by (rule ehouse_leI) simp_all
next
  case (insert i I)
  have "ehouse (\<lambda>e. \<Sum>j\<in>insert i I. f j e) = ehouse (\<lambda>e. f i e + (\<Sum>j\<in>I. f j e))"
    using insert.hyps by simp
  also have "... <= ehouse (f i) + ehouse (\<lambda>e. \<Sum>j\<in>I. f j e)"
    by (rule ehouse_add_le)
  also have "... <= ehouse (f i) + (\<Sum>j\<in>I. ehouse (f j))"
    using insert.IH by linarith
  also have "... = (\<Sum>j\<in>insert i I. ehouse (f j))"
    using insert.hyps by simp
  finally show ?case .
qed


lemma ehouse_of_int [simp]:
  assumes "E \<noteq> {}"
  shows "ehouse (\<lambda>_. of_int n) = abs n"
proof (rule antisym)
  show "ehouse (\<lambda>_. of_int n) <= abs n"
    by (simp add: ehouse_leI)
next
  obtain e where e: "e \<in> E"
    using assms by blast
  have "abs n = cmod ((\<lambda>_. of_int n) e)"
    by simp
  also have "... <= ehouse (\<lambda>_. of_int n)"
    by (rule cmod_le_ehouse[OF e])
  finally show "abs n <= ehouse (\<lambda>_. of_int n)" .
qed

lemma ehouse_of_nat [simp]:
  assumes "E \<noteq> {}"
  shows "ehouse (\<lambda>_. of_nat n) = of_nat n"
  using ehouse_of_int[OF assms, of "int n"] by simp

lemma ehouse_of_int_mult_le:
  "ehouse (\<lambda>e. of_int n * x e) \<le> abs n * ehouse x"
  apply (rule ehouse_leI)
   apply (simp add: mult_nonneg_nonneg)
  subgoal for e
  proof -
    assume e: "e \<in> E"
    have "cmod ((\<lambda>e. of_int n * x e) e) = abs n * cmod (x e)"
      by (simp add: norm_mult)
    also have "\<dots> \<le> abs n * ehouse x"
      using cmod_le_ehouse[OF e, of x]
      by (intro mult_left_mono) simp_all
    finally have "cmod ((\<lambda>e. of_int n * x e) e) \<le> abs n * ehouse x" .
    then show ?thesis
      by simp
  qed
  done

lemma ehouse_bounded_int_linear_combination_le:
  fixes basis :: "nat => 'e => complex"
  assumes B_nonneg: "0 <= B"
  assumes basis_bnd: "\<And>j. j < D \<Longrightarrow> ehouse (basis j) <= K"
  assumes K_nonneg: "0 <= K"
  assumes coeff_bnd: "\<And>j. j < D \<Longrightarrow> abs (c j) <= B"
  shows "ehouse (\<lambda>e. \<Sum>j<D. of_int (c j) * basis j e) <= (of_int B :: real) * of_nat D * K"
proof -
  have term_bnd: "ehouse (\<lambda>e. of_int (c j) * basis j e) <= (of_int B :: real) * K" if j: "j < D" for j
  proof -
    have "ehouse (\<lambda>e. of_int (c j) * basis j e) <= abs (c j) * ehouse (basis j)"
    proof (rule ehouse_leI)
      show "0 \<le> (abs (c j) :: real) * ehouse (basis j)"
        by (intro mult_nonneg_nonneg) simp_all
    next
      fix e
      assume e: "e \<in> E"
      have "cmod ((\<lambda>e. of_int (c j) * basis j e) e) = abs (c j) * cmod (basis j e)"
        by (simp add: norm_mult)
      also have "\<dots> \<le> abs (c j) * ehouse (basis j)"
        using cmod_le_ehouse[OF e, of "basis j"]
        by (intro mult_left_mono) simp_all
      finally show "cmod ((\<lambda>e. of_int (c j) * basis j e) e) \<le> abs (c j) * ehouse (basis j)"
        by simp
    qed
    also have "... <= (of_int B :: real) * K"
      using coeff_bnd[OF j] basis_bnd[OF j] B_nonneg K_nonneg
      by (intro mult_mono) auto
    finally show ?thesis .
  qed
  have "ehouse (\<lambda>e. \<Sum>j<D. of_int (c j) * basis j e) \<le> (\<Sum>j<D. ehouse (\<lambda>e. of_int (c j) * basis j e))"
    by (rule ehouse_sum_le) simp
  also have "... <= (\<Sum>j<D. (of_int B :: real) * K)"
    by (rule sum_mono) (simp add: term_bnd)
  also have "... = (of_int B :: real) * of_nat D * K"
    by simp
  finally show ?thesis .
qed

lemma ehouse_sum_mul_uniform_le:
  assumes A_nonneg: "0 <= A"
  assumes B_nonneg: "0 <= B"
  assumes x_bnd: "\<And>t. t < T \<Longrightarrow> ehouse (x t) <= A"
  assumes y_bnd: "\<And>t. t < T \<Longrightarrow> ehouse (y t) <= B"
  shows "ehouse (\<lambda>e. \<Sum>t<T. x t e * y t e) <= of_nat T * A * B"
proof -
  have term_bnd: "ehouse (\<lambda>e. x t e * y t e) <= A * B" if t: "t < T" for t
  proof -
    have "ehouse (\<lambda>e. x t e * y t e) <= ehouse (x t) * ehouse (y t)"
      by (rule ehouse_mul_le)
    also have "... <= A * B"
      using x_bnd[OF t] y_bnd[OF t] A_nonneg B_nonneg by (intro mult_mono) auto
    finally show ?thesis .
  qed
  have "ehouse (\<lambda>e. \<Sum>t<T. x t e * y t e) \<le> (\<Sum>t<T. ehouse (\<lambda>e. x t e * y t e))"
    by (rule ehouse_sum_le) simp
  also have "... <= (\<Sum>t<T. A * B)"
    by (rule sum_mono) (simp add: term_bnd)
  also have "... = of_nat T * A * B"
    by simp
  finally show ?thesis .
qed

lemma cmod_sum_mul_ehouse_le:
  assumes x_bnd: "ehouse x <= A"
  assumes y_bnd: "ehouse y <= B"
  assumes A_nonneg: "0 <= A"
  assumes B_nonneg: "0 <= B"
  shows "cmod (\<Sum>e\<in>E. x e * y e) <= of_nat (card E) * A * B"
proof -
  have term_bnd: "cmod (x e * y e) <= A * B" if e: "e \<in> E" for e
  proof -
    have "cmod (x e * y e) = cmod (x e) * cmod (y e)"
      by (simp add: norm_mult)
    also have "... <= A * B"
      using cmod_le_ehouse[OF e, of x] cmod_le_ehouse[OF e, of y]
        x_bnd y_bnd A_nonneg B_nonneg
      by (intro mult_mono) auto
    finally show ?thesis .
  qed
  have "cmod (\<Sum>e\<in>E. x e * y e) <= (\<Sum>e\<in>E. cmod (x e * y e))"
    by (rule norm_sum)
  also have "... <= (\<Sum>e\<in>E. A * B)"
    by (rule sum_mono) (simp add: term_bnd)
  also have "... = of_nat (card E) * A * B"
    by simp
  finally show ?thesis .
qed

lemma abs_int_of_ehouse_recovery_le:
  assumes recover: "(of_int n :: complex) = (\<Sum>e\<in>E. r e * y e)"
  assumes r_bnd: "ehouse r <= R"
  assumes y_bnd: "ehouse y <= A"
  assumes R_nonneg: "0 <= R"
  assumes A_nonneg: "0 <= A"
  shows "abs n <= ceiling (of_nat (card E) * R * A)"
proof -
  have real_bound: "cmod (of_int n :: complex) <= of_nat (card E) * R * A"
    unfolding recover
    by (rule cmod_sum_mul_ehouse_le[OF r_bnd y_bnd R_nonneg A_nonneg])
  have "(of_int (abs n) :: real) <= of_nat (card E) * R * A"
    using real_bound by simp
  also have "... <= of_int (ceiling (of_nat (card E) * R * A))"
    by (rule le_of_int_ceiling)
  finally have "(of_int (abs n) :: real) <= of_int (ceiling (of_nat (card E) * R * A))" .
  then show ?thesis
    by simp
qed

lemma abs_int_basis_coeff_ehouse_le:
  fixes basis :: "nat => 'e => complex"
  fixes repr_coeff :: "nat => 'e => complex"
  assumes klt: "k < D"
  assumes recover:
    "\<And>c k. k < D \<Longrightarrow>
      (of_int (c k) :: complex) =
        (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<D. of_int (c j) * basis j e))"
  assumes repr_bnd: "\<And>k. k < D \<Longrightarrow> ehouse (repr_coeff k) <= R"
  assumes R_nonneg: "0 <= R"
  assumes comb_bnd: "ehouse (\<lambda>e. \<Sum>j<D. of_int (c j) * basis j e) <= A"
  assumes A_nonneg: "0 <= A"
  shows "abs (c k) <= ceiling (of_nat (card E) * R * A)"
  by (rule abs_int_of_ehouse_recovery_le[OF recover[OF klt] repr_bnd[OF klt] comb_bnd R_nonneg A_nonneg])

lemma abs_int_structure_constant_ehouse_le:
  fixes basis :: "nat => 'e => complex"
  fixes repr_coeff :: "nat => 'e => complex"
  fixes a :: "nat => nat => 'e => complex"
  fixes C :: "nat => nat => nat => nat => int"
  assumes recover:
    "\<And>c k. k < D \<Longrightarrow>
      (of_int (c k) :: complex) =
        (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<D. of_int (c j) * basis j e))"
  assumes repr_bnd: "\<And>k. k < D \<Longrightarrow> ehouse (repr_coeff k) <= R"
  assumes A_bnd: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> ehouse (\<lambda>e. a u t e) <= A"
  assumes basis_bnd: "\<And>j. j < D \<Longrightarrow> ehouse (basis j) <= K"
  assumes R_nonneg: "0 <= R"
  assumes A_nonneg: "0 <= A"
  assumes K_nonneg: "0 <= K"
  assumes mult_repr:
    "\<And>u t j e. u < p \<Longrightarrow> t < q \<Longrightarrow> j < D \<Longrightarrow> e \<in> E \<Longrightarrow>
      a u t e * basis j e = (\<Sum>k<D. of_int (C u t k j) * basis k e)"
  assumes up: "u < p"
  assumes tq: "t < q"
  assumes klt: "k < D"
  assumes jlt: "j < D"
  shows "abs (C u t k j) <= ceiling (of_nat (card E) * R * A * K)"
proof -
  have y_bnd: "ehouse (\<lambda>e. a u t e * basis j e) <= A * K"
  proof -
    have "ehouse (\<lambda>e. a u t e * basis j e) <= ehouse (\<lambda>e. a u t e) * ehouse (basis j)"
      by (rule ehouse_mul_le)
    also have "... <= A * K"
      using A_bnd[OF up tq] basis_bnd[OF jlt] A_nonneg K_nonneg
      by (intro mult_mono) auto
    finally show ?thesis .
  qed
  have recoverC:
      "(of_int (C u t k j) :: complex) =
        (\<Sum>e\<in>E. repr_coeff k e * (a u t e * basis j e))"
  proof -
    have "(of_int (C u t k j) :: complex) =
        (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>l<D. of_int (C u t l j) * basis l e))"
      by (rule recover[OF klt, of "\<lambda>l. C u t l j"])
    also have "... = (\<Sum>e\<in>E. repr_coeff k e * (a u t e * basis j e))"
    proof (rule sum.cong[OF refl])
      fix e
      assume e: "e \<in> E"
      have "(\<Sum>l<D. of_int (C u t l j) * basis l e) = a u t e * basis j e"
        using mult_repr[OF up tq jlt e] by simp
      then show "repr_coeff k e * (\<Sum>l<D. of_int (C u t l j) * basis l e) =
          repr_coeff k e * (a u t e * basis j e)"
        by simp
    qed
    finally show ?thesis .
  qed
  have "abs (C u t k j) <= ceiling (of_nat (card E) * R * (A * K))"
    by (rule abs_int_of_ehouse_recovery_le[OF recoverC repr_bnd[OF klt] y_bnd R_nonneg])
       (use A_nonneg K_nonneg in auto)
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

section \<open>Basis matrices of indexed embedding families\<close>

context finite_embedding_indexed_recovery
begin

definition basis_matrix :: "complex mat"
  where "basis_matrix = mat D D (\<lambda>(i,j). basis_matrix_entry i j)"

definition inverse_basis_matrix :: "complex mat"
  where "inverse_basis_matrix = mat D D (\<lambda>(k,i). inverse_basis_matrix_entry k i)"

definition coeff_vec :: "(nat \<Rightarrow> complex) \<Rightarrow> complex vec"
  where "coeff_vec c = vec D c"

definition embedding_vec :: "('e \<Rightarrow> complex) \<Rightarrow> complex vec"
  where "embedding_vec y = vec D (\<lambda>i. y (emb i))"

lemma basis_matrix_carrier [simp]: "basis_matrix \<in> carrier_mat D D"
  unfolding basis_matrix_def by simp

lemma inverse_basis_matrix_carrier [simp]: "inverse_basis_matrix \<in> carrier_mat D D"
  unfolding inverse_basis_matrix_def by simp

lemma basis_matrix_dim [simp]:
  "dim_row basis_matrix = D"
  "dim_col basis_matrix = D"
  unfolding basis_matrix_def by simp_all

lemma inverse_basis_matrix_dim [simp]:
  "dim_row inverse_basis_matrix = D"
  "dim_col inverse_basis_matrix = D"
  unfolding inverse_basis_matrix_def by simp_all

lemma coeff_vec_dim [simp]:
  "dim_vec (coeff_vec c) = D"
  unfolding coeff_vec_def by simp

lemma embedding_vec_dim [simp]:
  "dim_vec (embedding_vec y) = D"
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

lemma inverse_basis_matrix_left_inverse:
  "inverse_basis_matrix * basis_matrix = 1\<^sub>m D"
proof (rule eq_matI)
  fix k j
  assume klt: "k < dim_row (1\<^sub>m D)"
  assume jlt: "j < dim_col (1\<^sub>m D)"
  then have kD: "k < D" and jD: "j < D"
    using klt by simp_all
  have "(inverse_basis_matrix * basis_matrix) $$ (k,j) =
      row inverse_basis_matrix k \<bullet> col basis_matrix j"
    using kD jD by simp
  also have "... = (\<Sum>i<D. inverse_basis_matrix_entry k i * basis_matrix_entry i j)"
  proof -
    have "row inverse_basis_matrix k \<bullet> col basis_matrix j =
        (\<Sum>i<D. row inverse_basis_matrix k $ i * col basis_matrix j $ i)"
      using kD jD
      unfolding inverse_basis_matrix_def basis_matrix_def scalar_prod_def
      by (simp add: Set_Interval.atLeast0LessThan)


    also have "... = (\<Sum>i<D. inverse_basis_matrix_entry k i * basis_matrix_entry i j)"
      using kD jD by (intro sum.cong[OF refl]) simp
    finally show ?thesis .
  qed
  also have "... = (if j = k then 1 else 0)"
    by (rule indexed_biorthogonal_matrix[OF kD jD])
  also have "... = (1\<^sub>m D) $$ (k,j)"
    using kD jD by simp
  finally show "(inverse_basis_matrix * basis_matrix) $$ (k,j) = (1\<^sub>m D) $$ (k,j)" .
next
  show "dim_row (inverse_basis_matrix * basis_matrix) = dim_row (1\<^sub>m D)"
    by simp
  show "dim_col (inverse_basis_matrix * basis_matrix) = dim_col (1\<^sub>m D)"
    by simp
qed

lemma basis_matrix_right_inverse:
  "basis_matrix * inverse_basis_matrix = 1\<^sub>m D"
  by (rule mat_mult_left_right_inverse[OF inverse_basis_matrix_carrier basis_matrix_carrier
        inverse_basis_matrix_left_inverse])

lemma inverse_basis_matrix_inverts [simp]:
  "inverts_mat inverse_basis_matrix basis_matrix"
proof -
  have "inverse_basis_matrix * basis_matrix = 1\<^sub>m (dim_row inverse_basis_matrix)"
    using inverse_basis_matrix_left_inverse by simp
  then show ?thesis
    unfolding inverts_mat_def .
qed

lemma basis_matrix_inverts [simp]:
  "inverts_mat basis_matrix inverse_basis_matrix"
proof -
  have "basis_matrix * inverse_basis_matrix = 1\<^sub>m (dim_row basis_matrix)"
    using basis_matrix_right_inverse by simp
  then show ?thesis
    unfolding inverts_mat_def .
qed

lemma det_basis_matrix_nonzero:
  "det basis_matrix \<noteq> 0"
proof
  assume det0: "det basis_matrix = 0"
  have "det (inverse_basis_matrix * basis_matrix) = det inverse_basis_matrix * det basis_matrix"
    by (rule det_mult[OF inverse_basis_matrix_carrier basis_matrix_carrier])
  then show False
    using det0 by (simp add: inverse_basis_matrix_left_inverse)
qed

lemma det_inverse_basis_matrix_nonzero:
  "det inverse_basis_matrix \<noteq> 0"
proof
  assume det0: "det inverse_basis_matrix = 0"
  have "det (inverse_basis_matrix * basis_matrix) = det inverse_basis_matrix * det basis_matrix"
    by (rule det_mult[OF inverse_basis_matrix_carrier basis_matrix_carrier])
  then show False
    using det0 by (simp add: inverse_basis_matrix_left_inverse)
qed

text \<open>
  Our @{term basis_matrix} stores embeddings as rows and basis vectors as
  columns, so the transpose present in Lean's matrix formula disappears here.
\<close>

lemma basis_matrix_mul_coeff_vec:
  "basis_matrix *\<^sub>v coeff_vec c = embedding_vec (\<lambda>e. \<Sum>j<D. c j * basis j e)"
proof (rule eq_vecI)
  fix i
  assume ilt: "i < dim_vec (embedding_vec (\<lambda>e. \<Sum>j<D. c j * basis j e))"
  then have iD: "i < D"
    unfolding embedding_vec_def by simp
  have "(basis_matrix *\<^sub>v coeff_vec c) $ i = row basis_matrix i \<bullet> coeff_vec c"
    using iD by simp
  also have "... = (\<Sum>j<D. row basis_matrix i $ j * coeff_vec c $ j)"
    using iD by (simp add: Set_Interval.atLeast0LessThan scalar_prod_def)


  also have "... = (\<Sum>j<D. basis_matrix $$ (i,j) * coeff_vec c $ j)"
    using iD by (intro sum.cong[OF refl]) simp
  also have "... = (\<Sum>j<D. c j * basis j (emb i))"
    using iD
    unfolding basis_matrix_def coeff_vec_def basis_matrix_entry_def
    by (intro sum.cong[OF refl]) (simp add: mult.commute)
  also have "... = embedding_vec (\<lambda>e. \<Sum>j<D. c j * basis j e) $ i"
    using iD unfolding embedding_vec_def by simp
  finally show "(basis_matrix *\<^sub>v coeff_vec c) $ i =
      embedding_vec (\<lambda>e. \<Sum>j<D. c j * basis j e) $ i" .
next
  show "dim_vec (basis_matrix *\<^sub>v coeff_vec c) =
      dim_vec (embedding_vec (\<lambda>e. \<Sum>j<D. c j * basis j e))"
    by simp
qed

lemma inverse_basis_matrix_mul_embedding_vec_eq_coeff_vec:
  "inverse_basis_matrix *\<^sub>v embedding_vec (\<lambda>e. \<Sum>j<D. c j * basis j e) = coeff_vec c"
proof -
  have assoc:
    "(inverse_basis_matrix * basis_matrix) *\<^sub>v coeff_vec c =
      inverse_basis_matrix *\<^sub>v (basis_matrix *\<^sub>v coeff_vec c)"
    by (rule assoc_mult_mat_vec[OF inverse_basis_matrix_carrier basis_matrix_carrier coeff_vec_carrier])
  have "inverse_basis_matrix *\<^sub>v embedding_vec (\<lambda>e. \<Sum>j<D. c j * basis j e) =
      inverse_basis_matrix *\<^sub>v (basis_matrix *\<^sub>v coeff_vec c)"
    by (simp add: basis_matrix_mul_coeff_vec[symmetric])
  also have "... = (inverse_basis_matrix * basis_matrix) *\<^sub>v coeff_vec c"
    using assoc by simp
  also have "... = coeff_vec c"
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
