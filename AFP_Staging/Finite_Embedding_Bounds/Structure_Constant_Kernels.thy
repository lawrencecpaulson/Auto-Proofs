(*  Title:      Finite_Embedding_Bounds/Structure_Constant_Kernels.thy
    Author:     OpenAI Codex
.
*)

section \<open>Bounded complex-matrix kernels via integral structure constants\<close>

theory Structure_Constant_Kernels
  imports "Bounded_Integer_Kernels.Integer_Kernel_Bounds"
begin

subsection \<open>Structure-constant lifting of integer kernels\<close>

definition sg_pair_idx :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "sg_pair_idx d i j \<equiv> i * d + j"

(* The integer matrix obtained by expanding each matrix entry in the basis. *)
definition structure_constant_mat ::
  "(nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int) \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int mat"
  where "structure_constant_mat C p q d =
    mat (p * d) (q * d)
      (\<lambda>(uk,tj). C (uk div d) (tj div d) (uk mod d) (tj mod d))"

locale bounded_basis_kernel =
  fixes A :: "complex mat"
    and p q d :: nat
    and basis :: "nat \<Rightarrow> complex"
    and B :: int
    and v :: "complex vec"
    and x :: "int vec"
  assumes v_carrier: "v \<in> carrier_vec q"
    and v_nonzero: "v \<noteq> 0\<^sub>v q"
    and x_carrier: "x \<in> carrier_vec (q * d)"
    and x_nonzero: "x \<noteq> 0\<^sub>v (q * d)"
    and kernel: "A *\<^sub>v v = 0\<^sub>v p"
    and coordinates:
      "\<forall>t<q. v $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)"
    and x_bounded: "x \<in> Bounded_vec B"

lemma sg_pair_idx_lt:
  assumes "d > 0" "i < q" "j < d"
  shows "sg_pair_idx d i j < q * d"
  by (simp add: assms sg_pair_idx_def td_gal_lt)

lemma sum_upto_sg_pair_idx:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> 'a::{comm_monoid_add}"
  assumes dpos: "d > 0"
  shows "(\<Sum>n<q * d. f (n div d) (n mod d)) = (\<Sum>t<q. \<Sum>j<d. f t j)"
proof -
  let ?S = "({..<q} :: nat set) \<times> ({..<d} :: nat set)"
  let ?T = "{..<q * d}"
  let ?h = "case_prod (sg_pair_idx d)"
  have bij: "bij_betw ?h ?S ?T"
  proof (rule bij_betw_byWitness)
    show "?h ` ?S \<subseteq> ?T"
      using dpos by (auto intro: sg_pair_idx_lt)
    show "(\<lambda>n::nat. (n div d, n mod d)) ` ?T \<subseteq> ?S"
      using dpos by (auto intro: less_mult_imp_div_less)
  qed (use dpos in \<open>auto simp: sg_pair_idx_def\<close>)
  have "(\<Sum>t<q. \<Sum>j<d. f t j) = (\<Sum>ij\<in>?S. case_prod f ij)"
    by (simp add: sum.cartesian_product)
  also have "\<dots> = (\<Sum>ij\<in>?S. case_prod f (?h ij div d, ?h ij mod d))"
    using dpos by (intro sum.cong) (auto simp add: sg_pair_idx_def split: prod.splits)
  also have "\<dots> = (\<Sum>n\<in>?T. case_prod f (n div d, n mod d))"
    using bij by (rule sum.reindex_bij_betw)
  also have "\<dots> = (\<Sum>n<q * d. f (n div d) (n mod d))"
    by simp
  finally show ?thesis by simp
qed

subsection \<open>And the main results\<close>

proposition lift_structure_constant_kernel:
  fixes A :: "complex mat"
  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  fixes x :: "int vec"
  assumes A: "A \<in> carrier_mat p q"
  assumes dpos: "d > 0"
  assumes mult_repr:
    "\<And>u t j. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow>
      A $$ (u,t) * basis j = (\<Sum>k<d. of_int (C u t k j) * basis k)"
  assumes basis_indep:
    "\<And>c. (\<Sum>j<d. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<d. c j = 0)"
  assumes x_carrier: "x \<in> carrier_vec (q * d)"
  assumes x_nz: "x \<noteq> 0\<^sub>v (q * d)"
  assumes kernel: "structure_constant_mat C p q d *\<^sub>v x = 0\<^sub>v (p * d)"
  shows "\<exists>eta. eta \<in> carrier_vec q \<and> eta \<noteq> 0\<^sub>v q \<and>
    A *\<^sub>v eta = 0\<^sub>v p \<and>
    (\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j))"
proof -
  define M :: "int mat" where "M = structure_constant_mat C p q d"
  have M: "M \<in> carrier_mat (p * d) (q * d)"
    unfolding M_def structure_constant_mat_def by simp
  have Mx0: "M *\<^sub>v x = 0\<^sub>v (p * d)"
    using kernel unfolding M_def by simp
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
      using basis_indep eta0 eta_coord j t by fastforce
    obtain n where n: "n < q * d" "x $ n \<noteq> 0"
      using x_carrier x_nz by force
    have tlt: "n div d < q"
      using dpos n(1) td_gal_lt by force
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
          unfolding M_def structure_constant_mat_def using uklt nlt idx_div idx_mod by simp
        show "M $$ (sg_pair_idx d u k, n) * x $ n = C u (n div d) k (n mod d) * x $ n"
          using entry_eq by simp
      qed
      have comp4a: "(\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ n) =
          (\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ sg_pair_idx d (n div d) (n mod d))"
        unfolding sg_pair_idx_def using dpos by simp
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
    using A Aeta_component by auto
  show ?thesis
    using eta_carrier eta_nz Aeta0 eta_coord by blast
qed

context
  fixes A :: "complex mat"
    and basis :: "nat \<Rightarrow> complex"
    and C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
    and p q d :: nat
    and Bnd :: int
  assumes A: "A \<in> carrier_mat p q"
    and dpos: "d > 0"
    and mult_repr:
      "\<And>u t j. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow>
        A $$ (u,t) * basis j = (\<Sum>k<d. of_int (C u t k j) * basis k)"
    and C_bnd:
      "\<And>u t k j. u < p \<Longrightarrow> t < q \<Longrightarrow> k < d \<Longrightarrow> j < d \<Longrightarrow>
        \<bar>C u t k j\<bar> \<le> Bnd"
    and basis_indep:
      "\<And>c. (\<Sum>j<d. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<d. c j = 0)"
begin

private abbreviation M where "M \<equiv> structure_constant_mat C p q d"

lemma structure_constant_mat_carrier: "M \<in> carrier_mat (p * d) (q * d)"
  by (simp add: structure_constant_mat_def)

lemma structure_constant_mat_bounded: "M \<in> Bounded_mat Bnd"
  unfolding Bounded_mat_def structure_constant_mat_def
  by (auto intro!: C_bnd less_mult_imp_div_less simp: dpos)

lemma lift_bounded_structure_constant_kernel:
  assumes x_carrier: "x \<in> carrier_vec (q * d)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * d)"
    and kernel: "M *\<^sub>v x = 0\<^sub>v (p * d)"
    and "x \<in> Bounded_vec B"
  obtains eta where "bounded_basis_kernel A p q d basis B eta x"
proof -
  obtain eta where 
      "eta \<in> carrier_vec q" "eta \<noteq> 0\<^sub>v q"
      "A *\<^sub>v eta = 0\<^sub>v p"
      "\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)"
    using lift_structure_constant_kernel[OF A dpos mult_repr basis_indep
      x_carrier x_nz kernel] by blast
  with assms bounded_basis_kernel.intro that show thesis 
    by blast
qed

theorem exists_nonzero_bounded_kernel_vec_of_structure_constants:
  assumes hpq: "p < q"
  obtains eta :: "complex vec" and x :: "int vec" where
    "bounded_basis_kernel A p q d basis
      (int (q * d + 1) * det_bound_hadamard (q * d) (max 1 Bnd)) eta x"
proof -
  have pdqd: "p * d < q * d"
    using hpq dpos by simp
  obtain x :: "int vec" where
      x_carrier: "x \<in> carrier_vec (q * d)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * d)"
    and Mx0: "M *\<^sub>v x = 0\<^sub>v (p * d)"
    and x_bnd: "x \<in> Bounded_vec (int (q * d + 1) * det_bound_hadamard (q * d) (max 1 Bnd))"
    using exists_ne_zero_int_vec_bounded_kernel[OF structure_constant_mat_carrier pdqd structure_constant_mat_bounded] by blast
  with lift_bounded_structure_constant_kernel[OF x_carrier x_nz Mx0 x_bnd]
  show thesis
    using that by meson
qed

theorem exists_nonzero_bounded_kernel_vec_of_structure_constants_exponent:
  assumes ppos: "p > 0"
  assumes hpq: "p < q"
  obtains eta :: "complex vec" and x :: "int vec" where
    "eta \<in> carrier_vec q"
    "eta \<noteq> 0\<^sub>v q"
    "x \<in> carrier_vec (q * d)"
    "x \<noteq> 0\<^sub>v (q * d)"
    "A *\<^sub>v eta = 0\<^sub>v p"
    "\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)"
    "\<forall>j<q * d. (of_int (\<bar>x $ j\<bar>) :: real) \<le>
      (real (q * d) * (of_int (max 1 Bnd) :: real)) powr
        (real (p * d) / real (q * d - p * d))"
proof -
  have pdpos: "0 < p * d" using ppos dpos by simp
  have pdqd: "p * d < q * d" using hpq dpos by simp
  obtain x where 
      "x \<in> carrier_vec (q * d)" "x \<noteq> 0\<^sub>v (q * d)"
      "M *\<^sub>v x = 0\<^sub>v (p * d)"
      "\<forall>j<q * d. (of_int (\<bar>x $ j\<bar>) :: real) \<le>
        (real (q * d) * (of_int (max 1 Bnd) :: real)) powr
          (real (p * d) / real (q * d - p * d))"
    using exists_ne_zero_int_vec_bounded_kernel_exponent[OF structure_constant_mat_carrier pdpos pdqd structure_constant_mat_bounded]
    by blast
  with that lift_structure_constant_kernel[OF A dpos mult_repr basis_indep] show thesis
    by blast
qed

theorem exists_nonzero_bounded_kernel_vec_of_structure_constants_linear:
  assumes "p > 0"
  assumes "2 * p \<le> q"
  obtains eta :: "complex vec" and x :: "int vec" where
    "bounded_basis_kernel A p q d basis
      (2 * int (q * d) * max 1 Bnd) eta x"
proof -
  obtain x :: "int vec" where "x \<in> carrier_vec (q * d)"
    and "x \<noteq> 0\<^sub>v (q * d)"
    and "M *\<^sub>v x = 0\<^sub>v (p * d)"
    and "x \<in> Bounded_vec (2 * int (q * d) * max 1 Bnd)"
    using exists_ne_zero_int_vec_bounded_kernel_linear[OF structure_constant_mat_carrier] 
      structure_constant_mat_bounded using dpos assms by force
  with that lift_bounded_structure_constant_kernel show thesis
    by meson
qed

end

end
