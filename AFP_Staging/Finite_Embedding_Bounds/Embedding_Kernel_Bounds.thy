(*  Title:      Finite_Embedding_Bounds/Embedding_Kernel_Bounds.thy
    Author:     OpenAI Codex
*)

section \<open>Uniform finite-embedding house bounds for bounded algebraic kernels.\<close>

theory Embedding_Kernel_Bounds
  imports
    Structure_Constant_Kernels
    Finite_Embedding_House
begin

definition ehouse_hadamard_kernel_bound :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "ehouse_hadamard_kernel_bound q d B =
    int (q * d + 1) * det_bound_hadamard (q * d) (max 1 B)"

definition ehouse_exponent_kernel_bound :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> real" where
  "ehouse_exponent_kernel_bound p q d B =
    (real (q * d) * of_int (max 1 B)) powr
      (real (p * d) / real (q * d - p * d))"

definition ehouse_linear_kernel_bound :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "ehouse_linear_kernel_bound q d B = 2 * int (q * d) * max 1 B"

context finite_embedding_house
begin

definition ehouse_structure_constant_bound :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> int" where
  "ehouse_structure_constant_bound R H K = \<lceil>real (card E) * R * H * K\<rceil>"

definition ehouse_kernel_witness where
  "ehouse_kernel_witness A p q d basis e0 K M eta x \<longleftrightarrow>
    eta \<in> carrier_vec q \<and> eta \<noteq> 0\<^sub>v q \<and>
    x \<in> carrier_vec (q * d) \<and> x \<noteq> 0\<^sub>v (q * d) \<and>
    A *\<^sub>v eta = 0\<^sub>v p \<and>
    (\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e0)) \<and>
    (\<forall>j<q * d. (of_int (\<bar>x $ j\<bar>) :: real) \<le> M) \<and>
    (\<forall>t<q. ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e)
      \<le> M * real d * K) \<and>
    (\<forall>t<q. cmod (eta $ t) \<le> M * real d * K)"


lemma ehouse_kernel_witness_bounded_basis_kernel:
  fixes A :: "complex mat"
  fixes basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  assumes W: "ehouse_kernel_witness A p q d basis e0 K (of_int B) eta x"
  shows "bounded_basis_kernel A p q d (\<lambda>j. basis j e0) B eta x"
proof -
  have x_carrier: "x \<in> carrier_vec (q * d)"
    using W unfolding ehouse_kernel_witness_def by blast
  have x_bounded: "x \<in> Bounded_vec B"
    using W x_carrier
    unfolding ehouse_kernel_witness_def Bounded_vec_def by auto
  show ?thesis
    using W x_bounded
    unfolding ehouse_kernel_witness_def
    by unfold_locales auto
qed

lemma bounded_basis_kernel_ehouse_bounds:
  fixes A :: "complex mat"
  fixes basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  assumes W: "bounded_basis_kernel A p q d (\<lambda>j. basis j e0) B eta x"
  assumes e0: "e0 \<in> E"
  assumes dpos: "d > 0"
  assumes basis_bnd: "\<And>j. j < d \<Longrightarrow> ehouse (basis j) \<le> K"
  shows "\<forall>t<q. ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e)
      \<le> (of_int B :: real) * real d * K"
    and "\<forall>t<q. cmod (eta $ t) \<le> (of_int B :: real) * real d * K"
proof -
  note x_carrier = bounded_basis_kernel.x_carrier[OF W]
    and x_bnd = bounded_basis_kernel.x_bounded[OF W]
    and repr = bounded_basis_kernel.coordinates[OF W]
  have eh_bound:
      "ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e)
        \<le> of_int B * real d * K" if tlt: "t < q" for t
  proof (rule ehouse_bounded_int_linear_combination_le[OF basis_bnd])
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

lemma bounded_basis_kernel_ehouse_witness:
  fixes A :: "complex mat"
  fixes basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  assumes W: "bounded_basis_kernel A p q d (\<lambda>j. basis j e0) B eta x"
  assumes e0: "e0 \<in> E"
  assumes dpos: "d > 0"
  assumes basis_bnd: "\<And>j. j < d \<Longrightarrow> ehouse (basis j) \<le> K"
  shows "ehouse_kernel_witness A p q d basis e0 K (of_int B) eta x"
proof -
  note carrier = bounded_basis_kernel.v_carrier[OF W]
    bounded_basis_kernel.x_carrier[OF W]
  note nonzero = bounded_basis_kernel.v_nonzero[OF W]
    bounded_basis_kernel.x_nonzero[OF W]
  note kernel = bounded_basis_kernel.kernel[OF W]
    and coordinates = bounded_basis_kernel.coordinates[OF W]
  have coeff: "\<forall>j<q * d. (of_int (\<bar>x $ j\<bar>) :: real) \<le> of_int B"
    using bounded_basis_kernel.x_bounded[OF W] bounded_basis_kernel.x_carrier[OF W]
    unfolding Bounded_vec_def by auto
  note house = bounded_basis_kernel_ehouse_bounds[OF W e0 dpos basis_bnd]
  show ?thesis
    unfolding ehouse_kernel_witness_def
    using carrier nonzero kernel coordinates coeff house by blast
qed

end

text \<open>The structure locale fixes the matrix, integral multiplication table,
independent basis, and uniform house bound. The rank hypotheses remain local to
the individual estimates.\<close>

locale finite_embedding_structure_kernel = finite_embedding_house E
  for E :: "'e set" +
  fixes A :: "complex mat"
    and p q d :: nat
    and e0 :: 'e
    and basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
    and C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
    and Bnd :: int
    and K :: real
  assumes A: "A \<in> carrier_mat p q"
    and dpos: "d > 0"
    and e0: "e0 \<in> E"
    and mult_repr:
      "\<And>u t j. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow>
        A $$ (u,t) * basis j e0 = (\<Sum>k<d. of_int (C u t k j) * basis k e0)"
    and C_bnd:
      "\<And>u t k j. u < p \<Longrightarrow> t < q \<Longrightarrow> k < d \<Longrightarrow> j < d \<Longrightarrow>
        \<bar>C u t k j\<bar> \<le> Bnd"
    and basis_indep:
      "\<And>c. (\<Sum>j<d. of_int (c j) * basis j e0) = 0 \<Longrightarrow> (\<forall>j<d. c j = 0)"
    and basis_bnd: "\<And>j. j < d \<Longrightarrow> ehouse (basis j) \<le> K"
begin

text \<open>The determinant bound applies whenever the matrix has more columns than rows.\<close>

theorem exists_nonzero_bounded_kernel_vec_of_structure_constants_ehouse:
  assumes hpq: "p < q"
  obtains eta :: "complex vec" and x :: "int vec" where
    "ehouse_kernel_witness A p q d basis e0 K (of_int (ehouse_hadamard_kernel_bound q d Bnd)) eta x"
proof -
  let ?X = "ehouse_hadamard_kernel_bound q d Bnd"
  obtain eta :: "complex vec" and x :: "int vec" where
    W: "bounded_basis_kernel A p q d (\<lambda>j. basis j e0) ?X eta x"
    using exists_nonzero_bounded_kernel_vec_of_structure_constants
      [OF A dpos hpq mult_repr C_bnd basis_indep]
    unfolding ehouse_hadamard_kernel_bound_def by blast
  have result: "ehouse_kernel_witness A p q d basis e0 K (of_int (ehouse_hadamard_kernel_bound q d Bnd)) eta x"
    by (rule bounded_basis_kernel_ehouse_witness[OF W e0 dpos basis_bnd])
  show thesis by (rule that[OF result])
qed

text \<open>The Siegel exponent estimate applies when the row dimension is positive.\<close>

theorem exists_nonzero_bounded_kernel_vec_of_structure_constants_ehouse_exponent:
  assumes ppos: "p > 0" and hpq: "p < q"
  obtains eta :: "complex vec" and x :: "int vec" where
    "ehouse_kernel_witness A p q d basis e0 K (ehouse_exponent_kernel_bound p q d Bnd) eta x"
proof -
  let ?R = "ehouse_exponent_kernel_bound p q d Bnd"
  obtain eta :: "complex vec" and x :: "int vec" where w:
      "eta \<in> carrier_vec q" "eta \<noteq> 0\<^sub>v q"
      "x \<in> carrier_vec (q * d)" "x \<noteq> 0\<^sub>v (q * d)"
      "A *\<^sub>v eta = 0\<^sub>v p"
      "\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e0)"
      "\<forall>j<q * d. (of_int (\<bar>x $ j\<bar>) :: real) \<le> ?R"
    using exists_nonzero_bounded_kernel_vec_of_structure_constants_exponent
      [OF A ppos dpos hpq mult_repr C_bnd basis_indep]
    unfolding ehouse_exponent_kernel_bound_def by blast
  have coeff_bnd: "(of_int (\<bar>x $ sg_pair_idx d t j\<bar>) :: real) \<le> ?R"
    if "t < q" "j < d" for t j
    using w(7) sg_pair_idx_lt[OF dpos that] by blast
  have eh_bound:
      "ehouse (\<lambda>e. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j e) \<le>
        ?R * real d * K" if "t < q" for t
  proof (rule ehouse_bounded_int_linear_combination_le_real[OF basis_bnd])
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
  have result: "ehouse_kernel_witness A p q d basis e0 K ?R eta x"
    unfolding ehouse_kernel_witness_def
    using w eh_bound cmod_bound by blast
  show thesis by (rule that[OF result])
qed

text \<open>With at least twice as many columns as rows, the integer bound is linear.\<close>

theorem exists_nonzero_bounded_kernel_vec_of_structure_constants_ehouse_linear:
  assumes ppos: "p > 0" and hpq: "2 * p \<le> q"
  obtains eta :: "complex vec" and x :: "int vec" where
    "ehouse_kernel_witness A p q d basis e0 K (of_int (ehouse_linear_kernel_bound q d Bnd)) eta x"
proof -
  let ?X = "ehouse_linear_kernel_bound q d Bnd"
  obtain eta :: "complex vec" and x :: "int vec" where
    W: "bounded_basis_kernel A p q d (\<lambda>j. basis j e0) ?X eta x"
    using exists_nonzero_bounded_kernel_vec_of_structure_constants_linear
      [OF A ppos dpos hpq mult_repr C_bnd basis_indep]
    unfolding ehouse_linear_kernel_bound_def by blast
  have result: "ehouse_kernel_witness A p q d basis e0 K (of_int (ehouse_linear_kernel_bound q d Bnd)) eta x"
    by (rule bounded_basis_kernel_ehouse_witness[OF W e0 dpos basis_bnd])
  show thesis by (rule that[OF result])
qed

end

text \<open>The entry locale records one finite embedding model and its coordinate
recovery bounds. Only the rank hypothesis varies between the three estimates.\<close>

locale finite_embedding_entry_kernel = finite_embedding_house E
  for E :: "'e set" +
  fixes A :: "complex mat"
    and p q d :: nat
    and e0 :: 'e
    and basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
    and repr_coeff :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
    and Aemb :: "nat \<Rightarrow> nat \<Rightarrow> 'e \<Rightarrow> complex"
    and C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
    and R H K :: real
  assumes A: "A \<in> carrier_mat p q"
    and dpos: "d > 0"
    and e0: "e0 \<in> E"
    and entry0: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> A $$ (u,t) = Aemb u t e0"
    and mult_repr:
      "\<And>u t j e. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow> e \<in> E \<Longrightarrow>
        Aemb u t e * basis j e = (\<Sum>k<d. of_int (C u t k j) * basis k e)"
    and recover:
      "\<And>c k. k < d \<Longrightarrow> of_int (c k) = (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<d. of_int (c j) * basis j e))"
    and repr_bnd: "\<And>k. k < d \<Longrightarrow> ehouse (repr_coeff k) \<le> R"
    and entry_bnd: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> ehouse (Aemb u t) \<le> H"
    and basis_indep:
      "\<And>c. (\<Sum>j<d. of_int (c j) * basis j e0) = 0 \<Longrightarrow> (\<forall>j<d. c j = 0)"
    and basis_bnd: "\<And>j. j < d \<Longrightarrow> ehouse (basis j) \<le> K"
begin

lemma ehouse_entries_structure_constants:
  shows "\<And>u t j. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow>
    A $$ (u,t) * basis j e0 = (\<Sum>k<d. of_int (C u t k j) * basis k e0)"
    and "\<And>u t k j. u < p \<Longrightarrow> t < q \<Longrightarrow> k < d \<Longrightarrow> j < d \<Longrightarrow>
      \<bar>C u t k j\<bar> \<le> ehouse_structure_constant_bound R H K"
proof -
  show "A $$ (u,t) * basis j e0 = (\<Sum>k<d. of_int (C u t k j) * basis k e0)"
    if "u < p" "t < q" "j < d" for u t j
    using e0 entry0 mult_repr that by presburger
  show "\<bar>C u t k j\<bar> \<le> ehouse_structure_constant_bound R H K"
    if "u < p" "t < q" "k < d" "j < d" for u t k j
    unfolding ehouse_structure_constant_bound_def
    by (rule abs_int_structure_constant_ehouse_le[OF recover repr_bnd entry_bnd basis_bnd
          mult_repr that])
qed

sublocale sc: finite_embedding_structure_kernel
  E A p q d e0 basis C "ehouse_structure_constant_bound R H K" K
  using A dpos e0 basis_indep basis_bnd ehouse_entries_structure_constants
  by unfold_locales blast

text \<open>The sublocale specializes all three bounds to the structure-constant
estimate obtained from recovery and entry houses. These aliases retain
entry-facing names for the determinant, exponent, and linear results.\<close>

lemmas exists_nonzero_bounded_kernel_vec_of_ehouse_entries =
  sc.exists_nonzero_bounded_kernel_vec_of_structure_constants_ehouse

lemmas exists_nonzero_bounded_kernel_vec_of_ehouse_entries_exponent =
  sc.exists_nonzero_bounded_kernel_vec_of_structure_constants_ehouse_exponent

lemmas exists_nonzero_bounded_kernel_vec_of_ehouse_entries_linear =
  sc.exists_nonzero_bounded_kernel_vec_of_structure_constants_ehouse_linear

end

end
