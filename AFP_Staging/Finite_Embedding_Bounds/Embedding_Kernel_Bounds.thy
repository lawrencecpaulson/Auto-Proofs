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

lemma bounded_basis_kernel_ehouse_bounds:
  fixes A :: "complex mat"
  fixes basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  assumes W: "bounded_basis_kernel A p q d (\<lambda>j. basis j e0) B eta x"
  assumes e0: "e0 \<in> E"
  assumes dpos: "d > 0"
  assumes basis_bnd: "\<And>j. j < d \<Longrightarrow> ehouse (basis j) \<le> K"
  assumes K_nonneg: "0 \<le> K"
  shows "\<forall>t<q. ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e)
      \<le> (of_int B :: real) * real d * K"
    and "\<forall>t<q. cmod (eta $ t) \<le> (of_int B :: real) * real d * K"
proof -
  note x_carrier = bounded_basis_kernel.x_carrier[OF W]
    and x_nz = bounded_basis_kernel.x_nonzero[OF W]
    and x_bnd = bounded_basis_kernel.x_bounded[OF W]
    and repr = bounded_basis_kernel.coordinates[OF W]
  have B_nonneg: "0 \<le> B"
  proof -
    obtain i where i: "i < q * d" "x $ i \<noteq> 0"
      using x_carrier x_nz by force
    have "\<bar>x $ i\<bar> \<le> B"
      using x_carrier x_bnd i(1) unfolding Bounded_vec_def by simp
    then show ?thesis by simp
  qed
  have eh_bound:
      "ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e)
        \<le> of_int B * real d * K" if tlt: "t < q" for t
  proof (rule ehouse_bounded_int_linear_combination_le[OF B_nonneg basis_bnd K_nonneg])
    fix j
    assume jlt: "j < d"
    have idx_lt: "sg_pair_idx d t j < q * d"
      by (rule sg_pair_idx_lt[OF dpos tlt jlt])
    show "\<bar>x $ sg_pair_idx d t j\<bar> \<le> B"
      using x_carrier x_bnd idx_lt unfolding Bounded_vec_def by simp
  qed
  show "\<forall>t<q. ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e)
      \<le> (of_int B :: real) * real d * K"
    using eh_bound by blast
  show "\<forall>t<q. cmod (eta $ t) \<le> (of_int B :: real) * real d * K"
    using cmod_le_ehouse dual_order.trans e0 eh_bound repr by fastforce
qed

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
      \<bar>C u t k j\<bar> \<le> Bnd"
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
        (of_int (int (q * d + 1) * det_bound_hadamard (q * d) (max 1 Bnd)) :: real) * of_nat d * K"
    and "\<forall>t<q.
      cmod (eta $ t) \<le>
        (of_int (int (q * d + 1) * det_bound_hadamard (q * d) (max 1 Bnd)) :: real) * of_nat d * K"
proof -
  let ?X = "int (q * d + 1) * det_bound_hadamard (q * d) (max 1 Bnd)"
  obtain eta :: "complex vec" and x :: "int vec" where
      W: "bounded_basis_kernel A p q d (\<lambda>j. basis j e0) ?X eta x"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants
          [OF A dpos hpq mult_repr C_bnd basis_indep])
  note eta_carrier = bounded_basis_kernel.v_carrier[OF W]
    and eta_nz = bounded_basis_kernel.v_nonzero[OF W]
    and x_carrier = bounded_basis_kernel.x_carrier[OF W]
    and x_nz = bounded_basis_kernel.x_nonzero[OF W]
    and ker = bounded_basis_kernel.kernel[OF W]
    and repr = bounded_basis_kernel.coordinates[OF W]
    and x_bnd = bounded_basis_kernel.x_bounded[OF W]
  note house = bounded_basis_kernel_ehouse_bounds[OF W e0 dpos basis_bnd K_nonneg]
  show thesis
    by (rule that[OF eta_carrier eta_nz x_carrier x_nz ker repr x_bnd])
      (use house in auto)
qed

theorem exists_nonzero_bounded_kernel_vec_of_structure_constants_ehouse_exponent:
  fixes A :: "complex mat"
  fixes basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes A: "A \<in> carrier_mat p q"
  assumes ppos: "p > 0"
  assumes dpos: "d > 0"
  assumes hpq: "p < q"
  assumes e0: "e0 \<in> E"
  assumes mult_repr:
    "\<And>u t j. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow>
      A $$ (u,t) * basis j e0 = (\<Sum>k<d. of_int (C u t k j) * basis k e0)"
  assumes C_bnd:
    "\<And>u t k j. u < p \<Longrightarrow> t < q \<Longrightarrow> k < d \<Longrightarrow> j < d \<Longrightarrow>
      \<bar>C u t k j\<bar> \<le> Bnd"
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
    and "\<forall>j<q * d. (of_int (\<bar>x $ j\<bar>) :: real) \<le>
      (real (q * d) * (of_int (max 1 Bnd) :: real)) powr
        (real (p * d) / real (q * d - p * d))"
    and "\<forall>t<q.
      ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) \<le>
        (real (q * d) * (of_int (max 1 Bnd) :: real)) powr
          (real (p * d) / real (q * d - p * d)) * real d * K"
    and "\<forall>t<q. cmod (eta $ t) \<le>
        (real (q * d) * (of_int (max 1 Bnd) :: real)) powr
          (real (p * d) / real (q * d - p * d)) * real d * K"
proof -
  let ?R = "(real (q * d) * (of_int (max 1 Bnd) :: real)) powr
    (real (p * d) / real (q * d - p * d))"
  obtain eta :: "complex vec" and x :: "int vec" where w:
      "eta \<in> carrier_vec q" "eta \<noteq> 0\<^sub>v q"
      "x \<in> carrier_vec (q * d)" "x \<noteq> 0\<^sub>v (q * d)"
      "A *\<^sub>v eta = 0\<^sub>v p"
      "\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e0)"
      "\<forall>j<q * d. (of_int (\<bar>x $ j\<bar>) :: real) \<le> ?R"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants_exponent
          [OF A ppos dpos hpq mult_repr C_bnd basis_indep])
  have R_nonneg: "0 \<le> ?R" by simp
  have coeff_bnd: "(of_int (\<bar>x $ sg_pair_idx d t j\<bar>) :: real) \<le> ?R"
    if "t < q" "j < d" for t j
    using w(7) sg_pair_idx_lt[OF dpos that] by blast
  have eh_bound:
      "ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) \<le>
        ?R * real d * K" if "t < q" for t
  proof (rule ehouse_bounded_int_linear_combination_le_real[OF R_nonneg basis_bnd K_nonneg])
    fix j
    assume "j < d"
    show "(of_int (\<bar>x $ sg_pair_idx d t j\<bar>) :: real) \<le> ?R"
      by (rule coeff_bnd[OF that \<open>j < d\<close>])
  qed
  have cmod_bound: "cmod (eta $ t) \<le> ?R * real d * K" if "t < q" for t
  proof -
    have eta_t: "eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e0)"
      using w(6) that by blast
    have "cmod (eta $ t) \<le>
        ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e)"
      unfolding eta_t by (rule cmod_le_ehouse[OF e0])
    also have "\<dots> \<le> ?R * real d * K" by (rule eh_bound[OF that])
    finally show ?thesis .
  qed
  show thesis
    by (rule that[OF w(1-7)]) (use eh_bound cmod_bound in auto)
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
      \<bar>C u t k j\<bar> \<le> Bnd"
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
      W: "bounded_basis_kernel A p q d (\<lambda>j. basis j e0) ?X eta x"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants_linear
          [OF A ppos dpos hpq mult_repr C_bnd basis_indep])
  note eta_carrier = bounded_basis_kernel.v_carrier[OF W]
    and eta_nz = bounded_basis_kernel.v_nonzero[OF W]
    and x_carrier = bounded_basis_kernel.x_carrier[OF W]
    and x_nz = bounded_basis_kernel.x_nonzero[OF W]
    and ker = bounded_basis_kernel.kernel[OF W]
    and repr = bounded_basis_kernel.coordinates[OF W]
    and x_bnd = bounded_basis_kernel.x_bounded[OF W]
  note house = bounded_basis_kernel_ehouse_bounds[OF W e0 dpos basis_bnd K_nonneg]
  show thesis
    by (rule that[OF eta_carrier eta_nz x_carrier x_nz ker repr x_bnd])
      (use house in auto)
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
    "\<And>c k. k < d \<Longrightarrow> of_int (c k) = (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<d. of_int (c j) * basis j e))"
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
          (max 1 (\<lceil>of_nat (card E) * R * H * K\<rceil>)))"
    and "\<forall>t<q.
      ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) \<le>
        (of_int
          (int (q * d + 1) * det_bound_hadamard (q * d) (max 1 (\<lceil>of_nat (card E) * R * H * K\<rceil>))) :: real) *
          of_nat d * K"
    and "\<forall>t<q.
      cmod (eta $ t) \<le>
        (of_int
          (int (q * d + 1) * det_bound_hadamard (q * d) (max 1 (\<lceil>of_nat (card E) * R * H * K\<rceil>))) :: real) *
          of_nat d * K"
proof -
  have mult_repr0:
    "A $$ (u,t) * basis j e0 = (\<Sum>k<d. of_int (C u t k j) * basis k e0)"
    if up: "u < p" and tq: "t < q" and jlt: "j < d" for u t j
    using e0 entry0 jlt mult_repr tq up by presburger
  have C_bnd: "\<bar>C u t k j\<bar> \<le> \<lceil>real (card E) * R * H * K\<rceil>"
    if up: "u < p" and tq: "t < q" and klt: "k < d" and jlt: "j < d"
    for u t k j
    by (rule abs_int_structure_constant_ehouse_le[OF recover repr_bnd entry_bnd basis_bnd
          R_nonneg H_nonneg K_nonneg mult_repr up tq klt jlt])
  show ?thesis
    using exists_nonzero_bounded_kernel_vec_of_structure_constants_ehouse[OF A dpos hpq e0
          mult_repr0 C_bnd basis_indep basis_bnd K_nonneg]
    using that by blast
qed

theorem exists_nonzero_bounded_kernel_vec_of_ehouse_entries_exponent:
  fixes A :: "complex mat"
  fixes basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes repr_coeff :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes Aemb :: "nat \<Rightarrow> nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes A: "A \<in> carrier_mat p q"
  assumes ppos: "p > 0"
  assumes dpos: "d > 0"
  assumes hpq: "p < q"
  assumes e0: "e0 \<in> E"
  assumes entry0: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> A $$ (u,t) = Aemb u t e0"
  assumes mult_repr:
    "\<And>u t j e. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow> e \<in> E \<Longrightarrow>
      Aemb u t e * basis j e = (\<Sum>k<d. of_int (C u t k j) * basis k e)"
  assumes recover:
    "\<And>c k. k < d \<Longrightarrow> of_int (c k) = (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<d. of_int (c j) * basis j e))"
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
    and "\<forall>j<q * d. (of_int (\<bar>x $ j\<bar>) :: real) \<le>
      (real (q * d) * (of_int (max 1 (\<lceil>real (card E) * R * H * K\<rceil>)) :: real)) powr
        (real (p * d) / real (q * d - p * d))"
    and "\<forall>t<q.
      ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) \<le>
        (real (q * d) * (of_int (max 1 (\<lceil>real (card E) * R * H * K\<rceil>)) :: real)) powr
          (real (p * d) / real (q * d - p * d)) * real d * K"
    and "\<forall>t<q. cmod (eta $ t) \<le>
        (real (q * d) * (of_int (max 1 (\<lceil>real (card E) * R * H * K\<rceil>)) :: real)) powr
          (real (p * d) / real (q * d - p * d)) * real d * K"
proof -
  have mult_repr0:
    "A $$ (u,t) * basis j e0 = (\<Sum>k<d. of_int (C u t k j) * basis k e0)"
    if up: "u < p" and tq: "t < q" and jlt: "j < d" for u t j
    using e0 entry0 jlt mult_repr tq up by presburger
  have C_bnd: "\<bar>C u t k j\<bar> \<le> \<lceil>real (card E) * R * H * K\<rceil>"
    if up: "u < p" and tq: "t < q" and klt: "k < d" and jlt: "j < d"
    for u t k j
    by (rule abs_int_structure_constant_ehouse_le[OF recover repr_bnd entry_bnd basis_bnd
          R_nonneg H_nonneg K_nonneg mult_repr up tq klt jlt])
  show ?thesis
    using exists_nonzero_bounded_kernel_vec_of_structure_constants_ehouse_exponent
      [OF A ppos dpos hpq e0 mult_repr0 C_bnd basis_indep basis_bnd K_nonneg]
    using that by blast
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
    "\<And>c k. k < d \<Longrightarrow> of_int (c k) = (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<d. of_int (c j) * basis j e))"
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
      (2 * int (q * d) * max 1 (\<lceil>of_nat (card E) * R * H * K\<rceil>))"
    and "\<forall>t<q.
      ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) \<le>
        (of_int (2 * int (q * d) * max 1 (\<lceil>of_nat (card E) * R * H * K\<rceil>)) :: real) *
          of_nat d * K"
    and "\<forall>t<q.
      cmod (eta $ t) \<le>
        (of_int (2 * int (q * d) * max 1 (\<lceil>of_nat (card E) * R * H * K\<rceil>)) :: real) *
          of_nat d * K"
proof -
  have mult_repr0:
    "A $$ (u,t) * basis j e0 = (\<Sum>k<d. of_int (C u t k j) * basis k e0)"
    if up: "u < p" and tq: "t < q" and jlt: "j < d" for u t j
    using e0 entry0 jlt mult_repr tq up by presburger
  have C_bnd: "\<bar>C u t k j\<bar> \<le> \<lceil>real (card E) * R * H * K\<rceil>"
    if up: "u < p" and tq: "t < q" and klt: "k < d" and jlt: "j < d"
    for u t k j
    by (rule abs_int_structure_constant_ehouse_le[OF recover repr_bnd entry_bnd basis_bnd
          R_nonneg H_nonneg K_nonneg mult_repr up tq klt jlt])
  show ?thesis
    using that exists_nonzero_bounded_kernel_vec_of_structure_constants_ehouse_linear[OF A ppos dpos hpq e0
          mult_repr0 C_bnd basis_indep basis_bnd K_nonneg] by blast
qed

end

end
