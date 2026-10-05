(*  Title:      Baker/Gelfond_Schneider_Embedding_House.thy
    Author:     OpenAI Codex

A finite-embedding house calculus for the specialized Gelfond-Schneider
number-field port. This isolates the algebraic inequalities that Lean proves
for `NumberField.house`, but in a form that only depends on a finite family of
simultaneous complex embeddings.
*)

theory Gelfond_Schneider_Embedding_House
  imports Gelfond_Schneider_Preliminaries
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

end
