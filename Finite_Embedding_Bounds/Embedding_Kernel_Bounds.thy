(*  Title:      Finite_Embedding_Bounds/Embedding_Kernel_Bounds.thy
    Author:     OpenAI Codex

Uniform finite-embedding house bounds for bounded algebraic kernels.
*)

theory Embedding_Kernel_Bounds
  imports
    Structure_Constant_Kernels
    Finite_Embedding_House
begin

context finite_embedding_house
begin

theorem exists_nonzero_bounded_kernel_vec_of_structure_constants_ehouse:
  fixes A :: "complex mat"
  fixes basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes A: "A \<in> carrier_mat p q"
  assumes dpos: "d > 0"
  assumes hpq: "p < q"
  assumes e0: "e0 \<in> E"
  assumes mult_repr:
    "\<And>u t j. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow>
      A $$ (u,t) * basis j e0 = (\<Sum>k<d. of_int (C u t k j) * basis k e0)"
  assumes C_bnd:
    "\<And>u t k j. u < p \<Longrightarrow> t < q \<Longrightarrow> k < d \<Longrightarrow> j < d \<Longrightarrow>
      abs (C u t k j) \<le> Bnd"
  assumes basis_indep:
    "\<And>c. (\<Sum>j<d. of_int (c j) * basis j e0) = 0 \<Longrightarrow> (\<forall>j<d. c j = 0)"
  assumes basis_bnd: "\<And>j. j < d \<Longrightarrow> ehouse (basis j) \<le> K"
  assumes K_nonneg: "0 \<le> K"
  obtains eta :: "complex vec" and x :: "int vec" where
      "eta \<in> carrier_vec q"
    and "eta \<noteq> 0\<^sub>v q"
    and "x \<in> carrier_vec (q * d)"
    and "x \<noteq> 0\<^sub>v (q * d)"
    and "A *\<^sub>v eta = 0\<^sub>v p"
    and "\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e0)"
    and "x \<in> Bounded_vec (int (q * d + 1) * det_bound_hadamard (q * d) (max 1 Bnd))"
    and "\<forall>t<q.
      ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) \<le>
        (of_int (int (q * d + 1) * det_bound_hadamard (q * d) (max 1 Bnd)) :: real) *
          of_nat d * K"
    and "\<forall>t<q.
      cmod (eta $ t) \<le>
        (of_int (int (q * d + 1) * det_bound_hadamard (q * d) (max 1 Bnd)) :: real) *
          of_nat d * K"
proof -
  let ?X = "int (q * d + 1) * det_bound_hadamard (q * d) (max 1 Bnd)"
  obtain eta :: "complex vec" and x :: "int vec" where
      eta_carrier: "eta \<in> carrier_vec q"
    and eta_nz: "eta \<noteq> 0\<^sub>v q"
    and x_carrier: "x \<in> carrier_vec (q * d)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * d)"
    and ker: "A *\<^sub>v eta = 0\<^sub>v p"
    and repr: "\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e0)"
    and x_bnd: "x \<in> Bounded_vec ?X"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants
          [OF A dpos hpq mult_repr C_bnd basis_indep])

  have X_nonneg: "0 \<le> ?X"
  proof (rule ccontr)
    assume "\<not> 0 \<le> ?X"
    then have X_neg: "?X < 0"
      by simp
    have x_zero: "x = 0\<^sub>v (q * d)"
    proof (rule eq_vecI)
      show "dim_vec x = dim_vec (0\<^sub>v (q * d))"
        using x_carrier by simp
    next
      fix i
      assume i: "i < dim_vec (0\<^sub>v (q * d))"
      then have ilt: "i < q * d"
        by simp
      have le: "abs (x $ i) \<le> ?X"
        using x_bnd x_carrier ilt unfolding Bounded_vec_def by fastforce
      from le X_neg have "abs (x $ i) < 0"
        by linarith
      then show "x $ i = (0\<^sub>v (q * d)) $ i"
        by simp
    qed
    with x_nz show False
      by contradiction
  qed

  have ehouse_bnd':
      "ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) \<le>
        (of_int ?X :: real) * of_nat d * K" if tlt: "t < q" for t
  proof (rule ehouse_bounded_int_linear_combination_le)
    show "0 \<le> ?X"
      by (rule X_nonneg)
  next
    show "ehouse (basis j) \<le> K" if "j < d" for j
      by (rule basis_bnd[OF that])
  next
    show "0 \<le> K"
      by (rule K_nonneg)
  next
    show "abs ((\<lambda>j. x $ sg_pair_idx d t j) j) \<le> ?X" if jlt: "j < d" for j
    proof -
      have idx_lt: "sg_pair_idx d t j < q * d"
        by (rule sg_pair_idx_lt[OF dpos tlt jlt])
      have "abs (x $ sg_pair_idx d t j) \<le> ?X"
        using x_bnd x_carrier idx_lt unfolding Bounded_vec_def by simp
      then show ?thesis
        by simp
    qed
  qed

  have cmod_bnd':
      "cmod (eta $ t) \<le> (of_int ?X :: real) * of_nat d * K" if tlt: "t < q" for t
  proof -
    have eta_eq:
      "eta $ t = (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) e0"
      using repr tlt by simp
    have "cmod ((\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) e0) \<le>
        ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e)"
      by (rule cmod_le_ehouse[OF e0])
    also have "\<dots> \<le> (of_int ?X :: real) * of_nat d * K"
      by (rule ehouse_bnd'[OF tlt])
    finally show ?thesis
      using eta_eq by simp
  qed

  show thesis
    by (rule that[OF eta_carrier eta_nz x_carrier x_nz ker repr x_bnd])
       (use ehouse_bnd' cmod_bnd' in auto)
qed

theorem exists_nonzero_bounded_kernel_vec_of_structure_constants_ehouse_linear:
  fixes A :: "complex mat"
  fixes basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes A: "A \<in> carrier_mat p q"
  assumes ppos: "p > 0"
  assumes dpos: "d > 0"
  assumes hpq: "2 * p \<le> q"
  assumes e0: "e0 \<in> E"
  assumes mult_repr:
    "\<And>u t j. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow>
      A $$ (u,t) * basis j e0 = (\<Sum>k<d. of_int (C u t k j) * basis k e0)"
  assumes C_bnd:
    "\<And>u t k j. u < p \<Longrightarrow> t < q \<Longrightarrow> k < d \<Longrightarrow> j < d \<Longrightarrow>
      abs (C u t k j) \<le> Bnd"
  assumes basis_indep:
    "\<And>c. (\<Sum>j<d. of_int (c j) * basis j e0) = 0 \<Longrightarrow> (\<forall>j<d. c j = 0)"
  assumes basis_bnd: "\<And>j. j < d \<Longrightarrow> ehouse (basis j) \<le> K"
  assumes K_nonneg: "0 \<le> K"
  obtains eta :: "complex vec" and x :: "int vec" where
      "eta \<in> carrier_vec q"
    and "eta \<noteq> 0\<^sub>v q"
    and "x \<in> carrier_vec (q * d)"
    and "x \<noteq> 0\<^sub>v (q * d)"
    and "A *\<^sub>v eta = 0\<^sub>v p"
    and "\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e0)"
    and "x \<in> Bounded_vec (2 * int (q * d) * max 1 Bnd)"
    and "\<forall>t<q.
      ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) \<le>
        (of_int (2 * int (q * d) * max 1 Bnd) :: real) * of_nat d * K"
    and "\<forall>t<q.
      cmod (eta $ t) \<le>
        (of_int (2 * int (q * d) * max 1 Bnd) :: real) * of_nat d * K"
proof -
  let ?X = "2 * int (q * d) * max 1 Bnd"
  obtain eta :: "complex vec" and x :: "int vec" where
      eta_carrier: "eta \<in> carrier_vec q"
    and eta_nz: "eta \<noteq> 0\<^sub>v q"
    and x_carrier: "x \<in> carrier_vec (q * d)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * d)"
    and ker: "A *\<^sub>v eta = 0\<^sub>v p"
    and repr: "\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e0)"
    and x_bnd: "x \<in> Bounded_vec ?X"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants_linear
          [OF A ppos dpos hpq mult_repr C_bnd basis_indep])

  have ehouse_bnd':
      "ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) \<le>
        (of_int ?X :: real) * of_nat d * K" if tlt: "t < q" for t
  proof (rule ehouse_bounded_int_linear_combination_le)
    show "0 \<le> ?X"
      by simp
  next
    show "ehouse (basis j) \<le> K" if "j < d" for j
      by (rule basis_bnd[OF that])
  next
    show "0 \<le> K"
      by (rule K_nonneg)
  next
    show "abs ((\<lambda>j. x $ sg_pair_idx d t j) j) \<le> ?X" if jlt: "j < d" for j
    proof -
      have idx_lt: "sg_pair_idx d t j < q * d"
        by (rule sg_pair_idx_lt[OF dpos tlt jlt])
      have "abs (x $ sg_pair_idx d t j) \<le> ?X"
        using x_bnd x_carrier idx_lt unfolding Bounded_vec_def by simp
      then show ?thesis
        by simp
    qed
  qed

  have cmod_bnd':
      "cmod (eta $ t) \<le> (of_int ?X :: real) * of_nat d * K" if tlt: "t < q" for t
  proof -
    have eta_eq:
      "eta $ t = (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) e0"
      using repr tlt by simp
    have "cmod ((\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) e0) \<le>
        ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e)"
      by (rule cmod_le_ehouse[OF e0])
    also have "\<dots> \<le> (of_int ?X :: real) * of_nat d * K"
      by (rule ehouse_bnd'[OF tlt])
    finally show ?thesis
      using eta_eq by simp
  qed

  show thesis
    by (rule that[OF eta_carrier eta_nz x_carrier x_nz ker repr x_bnd])
       (use ehouse_bnd' cmod_bnd' in auto)
qed

theorem exists_nonzero_bounded_kernel_vec_of_ehouse_entries:
  fixes A :: "complex mat"
  fixes basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes repr_coeff :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes Aemb :: "nat \<Rightarrow> nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes A: "A \<in> carrier_mat p q"
  assumes dpos: "d > 0"
  assumes hpq: "p < q"
  assumes e0: "e0 \<in> E"
  assumes entry0: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> A $$ (u,t) = Aemb u t e0"
  assumes mult_repr:
    "\<And>u t j e. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow> e \<in> E \<Longrightarrow>
      Aemb u t e * basis j e = (\<Sum>k<d. of_int (C u t k j) * basis k e)"
  assumes recover:
    "\<And>c k. k < d \<Longrightarrow>
      (of_int (c k) :: complex) =
        (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<d. of_int (c j) * basis j e))"
  assumes repr_bnd: "\<And>k. k < d \<Longrightarrow> ehouse (repr_coeff k) \<le> R"
  assumes entry_bnd: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> ehouse (Aemb u t) \<le> H"
  assumes basis_indep:
    "\<And>c. (\<Sum>j<d. of_int (c j) * basis j e0) = 0 \<Longrightarrow> (\<forall>j<d. c j = 0)"
  assumes basis_bnd: "\<And>j. j < d \<Longrightarrow> ehouse (basis j) \<le> K"
  assumes R_nonneg: "0 \<le> R"
  assumes H_nonneg: "0 \<le> H"
  assumes K_nonneg: "0 \<le> K"
  obtains eta :: "complex vec" and x :: "int vec" where
      "eta \<in> carrier_vec q"
    and "eta \<noteq> 0\<^sub>v q"
    and "x \<in> carrier_vec (q * d)"
    and "x \<noteq> 0\<^sub>v (q * d)"
    and "A *\<^sub>v eta = 0\<^sub>v p"
    and "\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e0)"
    and "x \<in> Bounded_vec
      (int (q * d + 1) *
        det_bound_hadamard (q * d)
          (max 1 (ceiling (of_nat (card E) * R * H * K))))"
    and "\<forall>t<q.
      ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) \<le>
        (of_int
          (int (q * d + 1) *
            det_bound_hadamard (q * d)
              (max 1 (ceiling (of_nat (card E) * R * H * K)))) :: real) *
          of_nat d * K"
    and "\<forall>t<q.
      cmod (eta $ t) \<le>
        (of_int
          (int (q * d + 1) *
            det_bound_hadamard (q * d)
              (max 1 (ceiling (of_nat (card E) * R * H * K)))) :: real) *
          of_nat d * K"
proof -
  have mult_repr0:
    "A $$ (u,t) * basis j e0 = (\<Sum>k<d. of_int (C u t k j) * basis k e0)"
    if up: "u < p" and tq: "t < q" and jlt: "j < d" for u t j
  proof -
    have "A $$ (u,t) * basis j e0 = Aemb u t e0 * basis j e0"
      by (simp add: entry0[OF up tq])
    also have "... = (\<Sum>k<d. of_int (C u t k j) * basis k e0)"
      by (rule mult_repr[OF up tq jlt e0])
    finally show ?thesis .
  qed
  have C_bnd:
    "abs (C u t k j) \<le> ceiling (of_nat (card E) * R * H * K)"
    if up: "u < p" and tq: "t < q" and klt: "k < d" and jlt: "j < d"
    for u t k j
    by (rule abs_int_structure_constant_ehouse_le[OF recover repr_bnd entry_bnd basis_bnd
          R_nonneg H_nonneg K_nonneg mult_repr up tq klt jlt])
  obtain eta :: "complex vec" and x :: "int vec" where
      eta_carrier: "eta \<in> carrier_vec q"
    and eta_nz: "eta \<noteq> 0\<^sub>v q"
    and x_carrier: "x \<in> carrier_vec (q * d)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * d)"
    and ker: "A *\<^sub>v eta = 0\<^sub>v p"
    and repr: "\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e0)"
    and x_bnd: "x \<in> Bounded_vec
      (int (q * d + 1) *
        det_bound_hadamard (q * d)
          (max 1 (ceiling (of_nat (card E) * R * H * K))))"
    and ehouse_bnd:
      "\<forall>t<q.
        ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) \<le>
          (of_int
            (int (q * d + 1) *
              det_bound_hadamard (q * d)
                (max 1 (ceiling (of_nat (card E) * R * H * K)))) :: real) *
            of_nat d * K"
    and cmod_bnd:
      "\<forall>t<q.
        cmod (eta $ t) \<le>
          (of_int
            (int (q * d + 1) *
              det_bound_hadamard (q * d)
                (max 1 (ceiling (of_nat (card E) * R * H * K)))) :: real) *
            of_nat d * K"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants_ehouse[OF A dpos hpq e0
          mult_repr0 C_bnd basis_indep basis_bnd K_nonneg])
  show thesis
    by (rule that[OF eta_carrier eta_nz x_carrier x_nz ker repr x_bnd ehouse_bnd cmod_bnd])
qed

theorem exists_nonzero_bounded_kernel_vec_of_ehouse_entries_linear:
  fixes A :: "complex mat"
  fixes basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes repr_coeff :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes Aemb :: "nat \<Rightarrow> nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes A: "A \<in> carrier_mat p q"
  assumes ppos: "p > 0"
  assumes dpos: "d > 0"
  assumes hpq: "2 * p \<le> q"
  assumes e0: "e0 \<in> E"
  assumes entry0: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> A $$ (u,t) = Aemb u t e0"
  assumes mult_repr:
    "\<And>u t j e. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow> e \<in> E \<Longrightarrow>
      Aemb u t e * basis j e = (\<Sum>k<d. of_int (C u t k j) * basis k e)"
  assumes recover:
    "\<And>c k. k < d \<Longrightarrow>
      (of_int (c k) :: complex) =
        (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<d. of_int (c j) * basis j e))"
  assumes repr_bnd: "\<And>k. k < d \<Longrightarrow> ehouse (repr_coeff k) \<le> R"
  assumes entry_bnd: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> ehouse (Aemb u t) \<le> H"
  assumes basis_indep:
    "\<And>c. (\<Sum>j<d. of_int (c j) * basis j e0) = 0 \<Longrightarrow> (\<forall>j<d. c j = 0)"
  assumes basis_bnd: "\<And>j. j < d \<Longrightarrow> ehouse (basis j) \<le> K"
  assumes R_nonneg: "0 \<le> R"
  assumes H_nonneg: "0 \<le> H"
  assumes K_nonneg: "0 \<le> K"
  obtains eta :: "complex vec" and x :: "int vec" where
      "eta \<in> carrier_vec q"
    and "eta \<noteq> 0\<^sub>v q"
    and "x \<in> carrier_vec (q * d)"
    and "x \<noteq> 0\<^sub>v (q * d)"
    and "A *\<^sub>v eta = 0\<^sub>v p"
    and "\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e0)"
    and "x \<in> Bounded_vec
      (2 * int (q * d) * max 1 (ceiling (of_nat (card E) * R * H * K)))"
    and "\<forall>t<q.
      ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) \<le>
        (of_int
          (2 * int (q * d) * max 1 (ceiling (of_nat (card E) * R * H * K))) :: real) *
          of_nat d * K"
    and "\<forall>t<q.
      cmod (eta $ t) \<le>
        (of_int
          (2 * int (q * d) * max 1 (ceiling (of_nat (card E) * R * H * K))) :: real) *
          of_nat d * K"
proof -
  have mult_repr0:
    "A $$ (u,t) * basis j e0 = (\<Sum>k<d. of_int (C u t k j) * basis k e0)"
    if up: "u < p" and tq: "t < q" and jlt: "j < d" for u t j
  proof -
    have "A $$ (u,t) * basis j e0 = Aemb u t e0 * basis j e0"
      by (simp add: entry0[OF up tq])
    also have "... = (\<Sum>k<d. of_int (C u t k j) * basis k e0)"
      by (rule mult_repr[OF up tq jlt e0])
    finally show ?thesis .
  qed
  have C_bnd:
    "abs (C u t k j) \<le> ceiling (of_nat (card E) * R * H * K)"
    if up: "u < p" and tq: "t < q" and klt: "k < d" and jlt: "j < d"
    for u t k j
    by (rule abs_int_structure_constant_ehouse_le[OF recover repr_bnd entry_bnd basis_bnd
          R_nonneg H_nonneg K_nonneg mult_repr up tq klt jlt])
  obtain eta :: "complex vec" and x :: "int vec" where
      eta_carrier: "eta \<in> carrier_vec q"
    and eta_nz: "eta \<noteq> 0\<^sub>v q"
    and x_carrier: "x \<in> carrier_vec (q * d)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * d)"
    and ker: "A *\<^sub>v eta = 0\<^sub>v p"
    and repr: "\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e0)"
    and x_bnd: "x \<in> Bounded_vec
      (2 * int (q * d) * max 1 (ceiling (of_nat (card E) * R * H * K)))"
    and ehouse_bnd:
      "\<forall>t<q.
        ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) \<le>
          (of_int
            (2 * int (q * d) * max 1 (ceiling (of_nat (card E) * R * H * K))) :: real) *
            of_nat d * K"
    and cmod_bnd:
      "\<forall>t<q.
        cmod (eta $ t) \<le>
          (of_int
            (2 * int (q * d) * max 1 (ceiling (of_nat (card E) * R * H * K))) :: real) *
            of_nat d * K"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants_ehouse_linear[OF A ppos dpos hpq e0
          mult_repr0 C_bnd basis_indep basis_bnd K_nonneg])
  show thesis
    by (rule that[OF eta_carrier eta_nz x_carrier x_nz ker repr x_bnd ehouse_bnd cmod_bnd])
qed

end

end
