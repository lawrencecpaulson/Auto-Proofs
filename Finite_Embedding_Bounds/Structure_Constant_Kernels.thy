(*  Title:      Finite_Embedding_Bounds/Structure_Constant_Kernels.thy
    Author:     OpenAI Codex

Bounded complex-matrix kernels via integral structure constants.
*)

theory Structure_Constant_Kernels
  imports
    Complex_Main
    "Bounded_Integer_Kernels.Integer_Kernel_Bounds"
begin

declare [[apply_timeout = 10]]

section \<open>Structure-constant lifting of integer kernels\<close>

definition sg_pair_idx :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "sg_pair_idx d i j = i * d + j"

lemma sg_div_lt_of_lt_mult:
  fixes u m n :: nat
  assumes npos: "n > 0"
  assumes ult: "u < m * n"
  shows "u div n < m"
proof (rule ccontr)
  assume "\<not> u div n < m"
  then have m_le: "m \<le> u div n"
    by simp
  have mn_le: "m * n \<le> (u div n) * n"
    using m_le by simp
  also have "\<dots> \<le> u"
    using npos by (simp add: div_mult_mod_eq mult.commute)
  finally show False
    using ult by simp
qed

lemma sg_pair_idx_lt:
  assumes dpos: "d > 0"
  assumes i: "i < q"
  assumes j: "j < d"
  shows "sg_pair_idx d i j < q * d"
proof -
  have h1: "sg_pair_idx d i j < Suc i * d"
    unfolding sg_pair_idx_def using j by simp
  have "Suc i \<le> q"
    using i by simp
  then have h2: "Suc i * d \<le> q * d"
  proof (rule mult_right_mono)
    show "0 \<le> d"
      using dpos by simp
  qed
  from h1 h2 show ?thesis
    by (rule less_le_trans)
qed

lemma sum_upto_sg_pair_idx:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> 'a::{comm_monoid_add}"
  assumes dpos: "d > 0"
  shows "(\<Sum>n<q * d. f (n div d) (n mod d)) = (\<Sum>t<q. \<Sum>j<d. f t j)"
proof -
  let ?S = "({..<q} :: nat set) \<times> ({..<d} :: nat set)"
  let ?T = "{..<q * d}"
  let ?h = "case_prod (sg_pair_idx d)"
  have bij: "bij_betw ?h ?S ?T"
  proof (rule bij_betw_byWitness[where f' = "\<lambda>n::nat. (n div d, n mod d)"])
    show "\<forall>a\<in>?S. (\<lambda>n::nat. (n div d, n mod d)) (?h a) = a"
      using dpos by (auto simp: sg_pair_idx_def)
  next
    show "\<forall>n\<in>?T. ?h ((\<lambda>n::nat. (n div d, n mod d)) n) = n"
      using dpos by (auto simp: sg_pair_idx_def)
  next
    show "?h ` ?S \<subseteq> ?T"
      using dpos by (auto intro: sg_pair_idx_lt)
  next
    show "(\<lambda>n::nat. (n div d, n mod d)) ` ?T \<subseteq> ?S"
      using dpos by (auto intro: sg_div_lt_of_lt_mult)
  qed
  have "(\<Sum>t<q. \<Sum>j<d. f t j) = (\<Sum>ij\<in>?S. case_prod f ij)"
    by (simp add: sum.cartesian_product)
  also have "\<dots> = (\<Sum>ij\<in>?S. case_prod f (?h ij div d, ?h ij mod d))"
  proof (rule sum.cong[OF refl])
    fix a
    assume a: "a \<in> ?S"
    then obtain t j where a_def: "a = (t, j)" and j: "j < d"
      by auto
    show "case_prod f a = case_prod f (?h a div d, ?h a mod d)"
      unfolding a_def using dpos j by (simp add: sg_pair_idx_def)
  qed
  also have "\<dots> = (\<Sum>n\<in>?T. case_prod f (n div d, n mod d))"
    using bij by (rule sum.reindex_bij_betw)
  also have "\<dots> = (\<Sum>n<q * d. f (n div d) (n mod d))"

    by simp
  finally show ?thesis by simp
qed

theorem exists_nonzero_bounded_kernel_vec_of_structure_constants:
  fixes A :: "complex mat"
  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes A: "A \<in> carrier_mat p q"
  assumes dpos: "d > 0"
  assumes hpq: "p < q"
  assumes mult_repr:
    "\<And>u t j. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow>
      A $$ (u,t) * basis j = (\<Sum>k<d. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < p \<Longrightarrow> t < q \<Longrightarrow> k < d \<Longrightarrow> j < d \<Longrightarrow> abs (C u t k j) \<le> Bnd"
  assumes basis_indep:
    "\<And>c. (\<Sum>j<d. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<d. c j = 0)"
  obtains eta :: "complex vec" and x :: "int vec" where
      "eta \<in> carrier_vec q"
    and "eta \<noteq> 0\<^sub>v q"
    and "x \<in> carrier_vec (q * d)"
    and "x \<noteq> 0\<^sub>v (q * d)"
    and "A *\<^sub>v eta = 0\<^sub>v p"
    and "\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)"
    and "x \<in> Bounded_vec (int (q * d + 1) * det_bound_hadamard (q * d) (max 1 Bnd))"
proof -
  define M :: "int mat" where
    "M = mat (p * d) (q * d)
      (\<lambda>(uk,tj). C (uk div d) (tj div d) (uk mod d) (tj mod d))"
  have M: "M \<in> carrier_mat (p * d) (q * d)"
    unfolding M_def by simp
  have M_bnd: "M \<in> Bounded_mat Bnd"
    unfolding Bounded_mat_def M_def
    by (auto intro!: C_bnd sg_div_lt_of_lt_mult simp: dpos)
  have pdqd: "p * d < q * d"
    using hpq dpos by simp
  obtain x :: "int vec" where
      x_carrier: "x \<in> carrier_vec (q * d)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * d)"
    and Mx0: "M *\<^sub>v x = 0\<^sub>v (p * d)"
    and x_bnd: "x \<in> Bounded_vec (int (q * d + 1) * det_bound_hadamard (q * d) (max 1 Bnd))"
    using exists_ne_zero_int_vec_bounded_kernel[OF M pdqd M_bnd] by blast
  define eta :: "complex vec" where
    "eta = vec q (\<lambda>t. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)"
  have eta_carrier: "eta \<in> carrier_vec q"
    unfolding eta_def by simp
  have eta_coord: "eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)" if "t < q" for t
    using that x_carrier unfolding eta_def by simp
  have eta_nz: "eta \<noteq> 0\<^sub>v q"
  proof
    assume eta0: "eta = 0\<^sub>v q"
    have block_zero: "x $ sg_pair_idx d t j = 0" if t: "t < q" and j: "j < d" for t j
    proof -
      have "eta $ t = 0"
        using eta0 t eta_carrier by simp
      then have "(\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j) = 0"
        using eta_coord[OF t] by simp
      from basis_indep[OF this] j show ?thesis
        by blast
    qed
    obtain n where n: "n < q * d" "x $ n \<noteq> 0"
      using x_carrier x_nz by force
    have tlt: "n div d < q"
      by (rule sg_div_lt_of_lt_mult[OF dpos n(1)])
    have jlt: "n mod d < d"
      using dpos by simp
    have n_eq: "n = sg_pair_idx d (n div d) (n mod d)"
      unfolding sg_pair_idx_def using dpos by simp
    have "x $ sg_pair_idx d (n div d) (n mod d) = 0"
      by (rule block_zero[OF tlt jlt])
    then have "x $ n = 0"
      using n_eq by simp
    with n show False
      by simp
  qed
  have Aeta_component: "(A *\<^sub>v eta) $ u = 0" if up: "u < p" for u
  proof -
    have rowlt: "u < dim_row A"
      using A up by simp
    have row_zero: "(\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j)) = 0" if k: "k < d" for k
    proof -
      have uklt: "sg_pair_idx d u k < p * d"
        by (rule sg_pair_idx_lt[OF dpos up k])
      have ukrow: "sg_pair_idx d u k < dim_row M"
        using uklt M by simp
      have comp0: "(M *\<^sub>v x) $ sg_pair_idx d u k = 0"
        using Mx0 uklt by simp
      have comp1: "(M *\<^sub>v x) $ sg_pair_idx d u k = row M (sg_pair_idx d u k) \<bullet> x"
        by (rule index_mult_mat_vec[OF ukrow])
      have comp2: "row M (sg_pair_idx d u k) \<bullet> x =
          (\<Sum>n<q * d. M $$ (sg_pair_idx d u k, n) * x $ n)"
      proof -
        have "row M (sg_pair_idx d u k) \<bullet> x =
            (\<Sum>i = 0..<q * d. row M (sg_pair_idx d u k) $ i * x $ i)"
          using x_carrier by (simp add: scalar_prod_def)
        also have "\<dots> = (\<Sum>n<q * d. M $$ (sg_pair_idx d u k, n) * x $ n)"
          using uklt M x_carrier by (simp add: atLeast0LessThan)
        finally show ?thesis .
      qed
      have comp3: "(\<Sum>n<q * d. M $$ (sg_pair_idx d u k, n) * x $ n) =
          (\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ n)"
      proof (rule sum.cong[OF refl])
        fix n
        assume n_mem: "n \<in> {..<q * d}"
        have nlt: "n < q * d"
          using n_mem by simp
        have idx_div: "sg_pair_idx d u k div d = u"
          using dpos k by (simp add: sg_pair_idx_def)
        have idx_mod: "sg_pair_idx d u k mod d = k"
          using dpos k by (simp add: sg_pair_idx_def)
        have entry_eq: "M $$ (sg_pair_idx d u k, n) = C u (n div d) k (n mod d)"
          unfolding M_def using uklt nlt idx_div idx_mod by simp
        show "M $$ (sg_pair_idx d u k, n) * x $ n = C u (n div d) k (n mod d) * x $ n"
          using entry_eq by simp
      qed
      have comp4a: "(\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ n) =
          (\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ sg_pair_idx d (n div d) (n mod d))"
      proof (rule sum.cong[OF refl])
        fix n
        assume n_mem: "n \<in> {..<q * d}"
        have nlt: "n < q * d"
          using n_mem by simp
        have "n = sg_pair_idx d (n div d) (n mod d)"
          unfolding sg_pair_idx_def using dpos by simp
        then show "C u (n div d) k (n mod d) * x $ n = C u (n div d) k (n mod d) * x $ sg_pair_idx d (n div d) (n mod d)"
          by simp
      qed
      have comp4b: "(\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ sg_pair_idx d (n div d) (n mod d)) =
          (\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j))"
        by (rule sum_upto_sg_pair_idx[OF dpos])
      have "0 = (\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j))"
        using comp0 comp1 comp2 comp3 comp4a comp4b by simp
      then show ?thesis by simp
    qed
    have row_zero_complex:
      "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) = 0" if k: "k < d" for k
    proof -
      have "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) =
          of_int (\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j))"
        by simp
      also have "\<dots> = 0"
        using row_zero[OF k] by simp
      finally show ?thesis .
    qed
    have h1: "(A *\<^sub>v eta) $ u = (\<Sum>t<q. A $$ (u,t) * eta $ t)"
    proof -
      have "(A *\<^sub>v eta) $ u = row A u \<bullet> eta"
        by (rule index_mult_mat_vec[OF rowlt])
      also have "\<dots> = (\<Sum>i = 0..<dim_vec eta. row A u $ i * eta $ i)"
        by (simp add: scalar_prod_def)
      also have "\<dots> = (\<Sum>t<q. A $$ (u,t) * eta $ t)"
        using A eta_carrier up by (simp add: atLeast0LessThan)
      finally show ?thesis .
    qed
    have h2: "(\<Sum>t<q. A $$ (u,t) * eta $ t) =
        (\<Sum>t<q. A $$ (u,t) * (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j))"
      by (rule sum.cong[OF refl]) (simp add: eta_coord)
    have h3: "(\<Sum>t<q. A $$ (u,t) * (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)) =
        (\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j))"
      by (simp add: sum_distrib_left algebra_simps)
    have h4: "(\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j)) =
        (\<Sum>t<q. \<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
    proof (rule sum.cong[OF refl])
      fix t
      assume t_mem: "t \<in> {..<q}"
      have t: "t < q"
        using t_mem by simp
      show "(\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j)) =
          (\<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
      proof (rule sum.cong[OF refl])
        fix j
        assume j_mem: "j \<in> {..<d}"
        have j: "j < d"
          using j_mem by simp
        have "A $$ (u,t) * basis j = (\<Sum>k<d. of_int (C u t k j) * basis k)"
          by (rule mult_repr[OF up t j])
        then show "of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j) =
            (\<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
          by (simp add: sum_distrib_left algebra_simps)
      qed
    qed
    have h5a: "(\<Sum>t<q. \<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
        (\<Sum>t<q. \<Sum>k<d. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
    proof (rule sum.cong[OF refl])
      fix t
      assume "t \<in> {..<q}"
      show "(\<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
          (\<Sum>k<d. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
        by (rule sum.swap)
    qed
    have h5b: "(\<Sum>t<q. \<Sum>k<d. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
        (\<Sum>k<d. \<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
      by (rule sum.swap)
    have h5c: "(\<Sum>k<d. \<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
        (\<Sum>k<d. (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k)"
    proof (rule sum.cong[OF refl])
      fix k
      assume "k \<in> {..<d}"
      have h5c1: "(\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
          (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k)"
      proof (rule sum.cong[OF refl])
        fix t
        assume "t \<in> {..<q}"
        show "(\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
            (\<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k)"
        proof (rule sum.cong[OF refl])
          fix j
          assume "j \<in> {..<d}"
          have "of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k) =
              (of_int (x $ sg_pair_idx d t j) * of_int (C u t k j)) * basis k"
            by (simp add: mult.assoc)
          also have "... = of_int ((x $ sg_pair_idx d t j) * C u t k j) * basis k"
            by (simp only: of_int_mult[symmetric])
          also have "... = of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k"
            by simp
          finally show "of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k) =
              of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k" .
        qed
      qed
      have h5c2: "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k) =
          (\<Sum>t<q. (\<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k)"
        by (simp add: sum_distrib_right)
      have h5c3: "(\<Sum>t<q. (\<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k) =
          (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k"
        by (simp add: sum_distrib_right)
      from h5c1 h5c2 h5c3 show "(\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
          (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k"
        by simp
    qed
    have h6: "(\<Sum>k<d. (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k) = 0"
    proof -
      have "(\<Sum>k<d. (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k) =
          (\<Sum>k<d. 0 * basis k)"
      proof (rule sum.cong[OF refl])
        fix k
        assume k_mem: "k \<in> {..<d}"
        have k: "k < d"
          using k_mem by simp
        have coeff0: "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) = 0"
          using row_zero_complex[OF k] .
        show "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k = 0 * basis k"
          by (subst coeff0) simp
      qed
      then show ?thesis by simp
    qed
    have "(A *\<^sub>v eta) $ u = 0"
      using h1 h2 h3 h4 h5a h5b h5c h6 by simp
    then show ?thesis .
  qed
  have Aeta0: "A *\<^sub>v eta = 0\<^sub>v p"
  proof (rule eq_vecI)
    show "dim_vec (A *\<^sub>v eta) = dim_vec (0\<^sub>v p)"
      using A eta_carrier by simp
  next
    fix u
    assume u: "u < dim_vec (0\<^sub>v p)"
    then have up: "u < p"
      by simp
    show "(A *\<^sub>v eta) $ u = (0\<^sub>v p) $ u"
      using Aeta_component[OF up] u by simp
  qed
  show thesis
    by (rule that[OF eta_carrier eta_nz x_carrier x_nz Aeta0])
       (use eta_coord x_bnd in auto)
qed

theorem exists_nonzero_bounded_kernel_vec_of_structure_constants_linear:
  fixes A :: "complex mat"
  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes A: "A \<in> carrier_mat p q"
  assumes ppos: "p > 0"
  assumes dpos: "d > 0"
  assumes hpq: "2 * p \<le> q"
  assumes mult_repr:
    "\<And>u t j. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow>
      A $$ (u,t) * basis j = (\<Sum>k<d. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < p \<Longrightarrow> t < q \<Longrightarrow> k < d \<Longrightarrow> j < d \<Longrightarrow> abs (C u t k j) \<le> Bnd"
  assumes basis_indep:
    "\<And>c. (\<Sum>j<d. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<d. c j = 0)"
  obtains eta :: "complex vec" and x :: "int vec" where
      "eta \<in> carrier_vec q"
    and "eta \<noteq> 0\<^sub>v q"
    and "x \<in> carrier_vec (q * d)"
    and "x \<noteq> 0\<^sub>v (q * d)"
    and "A *\<^sub>v eta = 0\<^sub>v p"
    and "\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)"
    and "x \<in> Bounded_vec (2 * int (q * d) * max 1 Bnd)"
proof -
  define M :: "int mat" where
    "M = mat (p * d) (q * d)
      (\<lambda>(uk,tj). C (uk div d) (tj div d) (uk mod d) (tj mod d))"
  have M: "M \<in> carrier_mat (p * d) (q * d)"
    unfolding M_def by simp
  have M_bnd: "M \<in> Bounded_mat Bnd"
    unfolding Bounded_mat_def M_def
    by (auto intro!: C_bnd sg_div_lt_of_lt_mult simp: dpos)
  have pd_pos: "p * d > 0"
    using ppos dpos by simp
  have pdqd: "2 * (p * d) \<le> q * d"
    using hpq dpos by simp
  obtain x :: "int vec" where
      x_carrier: "x \<in> carrier_vec (q * d)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * d)"
    and Mx0: "M *\<^sub>v x = 0\<^sub>v (p * d)"
    and x_bnd: "x \<in> Bounded_vec (2 * int (q * d) * max 1 Bnd)"
    using exists_ne_zero_int_vec_bounded_kernel_linear[OF M pd_pos pdqd M_bnd] by blast
  define eta :: "complex vec" where
    "eta = vec q (\<lambda>t. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)"
  have eta_carrier: "eta \<in> carrier_vec q"
    unfolding eta_def by simp
  have eta_coord: "eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)" if "t < q" for t
    using that x_carrier unfolding eta_def by simp
  have eta_nz: "eta \<noteq> 0\<^sub>v q"
  proof
    assume eta0: "eta = 0\<^sub>v q"
    have block_zero: "x $ sg_pair_idx d t j = 0" if t: "t < q" and j: "j < d" for t j
    proof -
      have "eta $ t = 0"
        using eta0 t eta_carrier by simp
      then have "(\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j) = 0"
        using eta_coord[OF t] by simp
      from basis_indep[OF this] j show ?thesis
        by blast
    qed
    obtain n where n: "n < q * d" "x $ n \<noteq> 0"
      using x_carrier x_nz by force
    have tlt: "n div d < q"
      by (rule sg_div_lt_of_lt_mult[OF dpos n(1)])
    have jlt: "n mod d < d"
      using dpos by simp
    have n_eq: "n = sg_pair_idx d (n div d) (n mod d)"
      unfolding sg_pair_idx_def using dpos by simp
    have "x $ sg_pair_idx d (n div d) (n mod d) = 0"
      by (rule block_zero[OF tlt jlt])
    then have "x $ n = 0"
      using n_eq by simp
    with n show False
      by simp
  qed
  have Aeta_component: "(A *\<^sub>v eta) $ u = 0" if up: "u < p" for u
  proof -
    have rowlt: "u < dim_row A"
      using A up by simp
    have row_zero: "(\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j)) = 0" if k: "k < d" for k
    proof -
      have uklt: "sg_pair_idx d u k < p * d"
        by (rule sg_pair_idx_lt[OF dpos up k])
      have ukrow: "sg_pair_idx d u k < dim_row M"
        using uklt M by simp
      have comp0: "(M *\<^sub>v x) $ sg_pair_idx d u k = 0"
        using Mx0 uklt by simp
      have comp1: "(M *\<^sub>v x) $ sg_pair_idx d u k = row M (sg_pair_idx d u k) \<bullet> x"
        by (rule index_mult_mat_vec[OF ukrow])
      have comp2: "row M (sg_pair_idx d u k) \<bullet> x =
          (\<Sum>n<q * d. M $$ (sg_pair_idx d u k, n) * x $ n)"
      proof -
        have "row M (sg_pair_idx d u k) \<bullet> x =
            (\<Sum>i = 0..<q * d. row M (sg_pair_idx d u k) $ i * x $ i)"
          using x_carrier by (simp add: scalar_prod_def)
        also have "\<dots> = (\<Sum>n<q * d. M $$ (sg_pair_idx d u k, n) * x $ n)"
          using uklt M x_carrier by (simp add: atLeast0LessThan)
        finally show ?thesis .
      qed
      have comp3: "(\<Sum>n<q * d. M $$ (sg_pair_idx d u k, n) * x $ n) =
          (\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ n)"
      proof (rule sum.cong[OF refl])
        fix n
        assume n_mem: "n \<in> {..<q * d}"
        have nlt: "n < q * d"
          using n_mem by simp
        have idx_div: "sg_pair_idx d u k div d = u"
          using dpos k by (simp add: sg_pair_idx_def)
        have idx_mod: "sg_pair_idx d u k mod d = k"
          using dpos k by (simp add: sg_pair_idx_def)
        have entry_eq: "M $$ (sg_pair_idx d u k, n) = C u (n div d) k (n mod d)"
          unfolding M_def using uklt nlt idx_div idx_mod by simp
        show "M $$ (sg_pair_idx d u k, n) * x $ n = C u (n div d) k (n mod d) * x $ n"
          using entry_eq by simp
      qed
      have comp4a: "(\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ n) =
          (\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ sg_pair_idx d (n div d) (n mod d))"
      proof (rule sum.cong[OF refl])
        fix n
        assume n_mem: "n \<in> {..<q * d}"
        have nlt: "n < q * d"
          using n_mem by simp
        have "n = sg_pair_idx d (n div d) (n mod d)"
          unfolding sg_pair_idx_def using dpos by simp
        then show "C u (n div d) k (n mod d) * x $ n = C u (n div d) k (n mod d) * x $ sg_pair_idx d (n div d) (n mod d)"
          by simp
      qed
      have comp4b: "(\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ sg_pair_idx d (n div d) (n mod d)) =
          (\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j))"
        by (rule sum_upto_sg_pair_idx[OF dpos])
      have "0 = (\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j))"
        using comp0 comp1 comp2 comp3 comp4a comp4b by simp
      then show ?thesis by simp
    qed
    have row_zero_complex:
      "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) = 0" if k: "k < d" for k
    proof -
      have "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) =
          of_int (\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j))"
        by simp
      also have "\<dots> = 0"
        using row_zero[OF k] by simp
      finally show ?thesis .
    qed
    have h1: "(A *\<^sub>v eta) $ u = (\<Sum>t<q. A $$ (u,t) * eta $ t)"
    proof -
      have "(A *\<^sub>v eta) $ u = row A u \<bullet> eta"
        by (rule index_mult_mat_vec[OF rowlt])
      also have "\<dots> = (\<Sum>i = 0..<dim_vec eta. row A u $ i * eta $ i)"
        by (simp add: scalar_prod_def)
      also have "\<dots> = (\<Sum>t<q. A $$ (u,t) * eta $ t)"
        using A eta_carrier up by (simp add: atLeast0LessThan)
      finally show ?thesis .
    qed
    have h2: "(\<Sum>t<q. A $$ (u,t) * eta $ t) =
        (\<Sum>t<q. A $$ (u,t) * (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j))"
      by (rule sum.cong[OF refl]) (simp add: eta_coord)
    have h3: "(\<Sum>t<q. A $$ (u,t) * (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)) =
        (\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j))"
      by (simp add: sum_distrib_left algebra_simps)
    have h4: "(\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j)) =
        (\<Sum>t<q. \<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
    proof (rule sum.cong[OF refl])
      fix t
      assume t_mem: "t \<in> {..<q}"
      have t: "t < q"
        using t_mem by simp
      show "(\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j)) =
          (\<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
      proof (rule sum.cong[OF refl])
        fix j
        assume j_mem: "j \<in> {..<d}"
        have j: "j < d"
          using j_mem by simp
        have "A $$ (u,t) * basis j = (\<Sum>k<d. of_int (C u t k j) * basis k)"
          by (rule mult_repr[OF up t j])
        then show "of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j) =
            (\<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
          by (simp add: sum_distrib_left algebra_simps)
      qed
    qed
    have h5a: "(\<Sum>t<q. \<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
        (\<Sum>t<q. \<Sum>k<d. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
    proof (rule sum.cong[OF refl])
      fix t
      assume "t \<in> {..<q}"
      show "(\<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
          (\<Sum>k<d. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
        by (rule sum.swap)
    qed
    have h5b: "(\<Sum>t<q. \<Sum>k<d. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
        (\<Sum>k<d. \<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
      by (rule sum.swap)
    have h5c: "(\<Sum>k<d. \<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
        (\<Sum>k<d. (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k)"
    proof (rule sum.cong[OF refl])
      fix k
      assume "k \<in> {..<d}"
      have h5c1: "(\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
          (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k)"
      proof (rule sum.cong[OF refl])
        fix t
        assume "t \<in> {..<q}"
        show "(\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
            (\<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k)"
        proof (rule sum.cong[OF refl])
          fix j
          assume "j \<in> {..<d}"
          have "of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k) =
              (of_int (x $ sg_pair_idx d t j) * of_int (C u t k j)) * basis k"
            by (simp add: mult.assoc)
          also have "... = of_int ((x $ sg_pair_idx d t j) * C u t k j) * basis k"
            by (simp only: of_int_mult[symmetric])
          also have "... = of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k"
            by simp
          finally show "of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k) =
              of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k" .
        qed
      qed
      have h5c2: "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k) =
          (\<Sum>t<q. (\<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k)"
        by (simp add: sum_distrib_right)
      have h5c3: "(\<Sum>t<q. (\<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k) =
          (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k"
        by (simp add: sum_distrib_right)
      from h5c1 h5c2 h5c3 show "(\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
          (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k"
        by simp
    qed
    have h6: "(\<Sum>k<d. (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k) = 0"
    proof -
      have "(\<Sum>k<d. (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k) =
          (\<Sum>k<d. 0 * basis k)"
      proof (rule sum.cong[OF refl])
        fix k
        assume k_mem: "k \<in> {..<d}"
        have k: "k < d"
          using k_mem by simp
        have coeff0: "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) = 0"
          using row_zero_complex[OF k] .
        show "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k = 0 * basis k"
          by (subst coeff0) simp
      qed
      then show ?thesis by simp
    qed
    have "(A *\<^sub>v eta) $ u = 0"
      using h1 h2 h3 h4 h5a h5b h5c h6 by simp
    then show ?thesis .
  qed
  have Aeta0: "A *\<^sub>v eta = 0\<^sub>v p"
  proof (rule eq_vecI)
    show "dim_vec (A *\<^sub>v eta) = dim_vec (0\<^sub>v p)"
      using A eta_carrier by simp
  next
    fix u
    assume u: "u < dim_vec (0\<^sub>v p)"
    then have up: "u < p"
      by simp
    show "(A *\<^sub>v eta) $ u = (0\<^sub>v p) $ u"
      using Aeta_component[OF up] u by simp
  qed
  show thesis
    by (rule that[OF eta_carrier eta_nz x_carrier x_nz Aeta0])
       (use eta_coord x_bnd in auto)
qed

end
