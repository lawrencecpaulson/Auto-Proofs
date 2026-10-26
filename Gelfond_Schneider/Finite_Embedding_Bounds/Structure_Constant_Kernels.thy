(*  Title:      Gelfond_Schneider/Finite_Embedding_Bounds/Structure_Constant_Kernels.thy
    Author:     OpenAI Codex

Bounded complex-matrix kernels via integral structure constants.
*)

theory Structure_Constant_Kernels
  imports "Bounded_Integer_Kernels.Integer_Kernel_Bounds"
begin

section \<open>Structure-constant lifting of integer kernels\<close>

definition sg_pair_idx :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "sg_pair_idx d i j \<equiv> i * d + j"

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

text \<open>This theorem and the next have almost identical proofs\<close>
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
    "M \<equiv> mat (p * d) (q * d) (\<lambda>(uk,tj). C (uk div d) (tj div d) (uk mod d) (tj mod d))"
  have M: "M \<in> carrier_mat (p * d) (q * d)"
    unfolding M_def by simp
  have M_bnd: "M \<in> Bounded_mat Bnd"
    unfolding Bounded_mat_def M_def
    by (auto intro!: C_bnd less_mult_imp_div_less simp: dpos)
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
    have n_eq: "n = sg_pair_idx d (n div d) (n mod d)"
      unfolding sg_pair_idx_def using dpos by simp
    have "x $ sg_pair_idx d (n div d) (n mod d) = 0"
      using block_zero dpos n(1) td_gal_lt by force
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
      have "(M *\<^sub>v x) $ sg_pair_idx d u k = row M (sg_pair_idx d u k) \<bullet> x"
        by (rule index_mult_mat_vec[OF ukrow])
      also have "\<dots> = (\<Sum>n<q * d. M $$ (sg_pair_idx d u k, n) * x $ n)"
      proof -
        have "row M (sg_pair_idx d u k) \<bullet> x = (\<Sum>i = 0..<q * d. row M (sg_pair_idx d u k) $ i * x $ i)"
          using x_carrier by (simp add: scalar_prod_def)
        also have "\<dots> = (\<Sum>n<q * d. M $$ (sg_pair_idx d u k, n) * x $ n)"
          using uklt M x_carrier by (simp add: atLeast0LessThan)
        finally show ?thesis .
      qed
      also have "\<dots> = (\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ n)"
      proof (rule sum.cong[OF refl])
        fix n
        assume "n \<in> {..<q * d}"
        then show "M $$ (sg_pair_idx d u k, n) * x $ n = C u (n div d) k (n mod d) * x $ n"
          unfolding M_def using uklt dpos k by (simp add: sg_pair_idx_def)
      qed
      also have "\<dots> = (\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ sg_pair_idx d (n div d) (n mod d))"
        unfolding sg_pair_idx_def by presburger
      also have "\<dots> = (\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j))"
        by (rule sum_upto_sg_pair_idx[OF dpos])
      finally have "0 = (\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j))"
        using Mx0 uklt by simp
      then show ?thesis by simp
    qed
    have row_zero_complex: "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) = 0" if k: "k < d" for k
      using row_zero[OF k]
      by (metis (mono_tags, lifting) of_int_hom.hom_zero of_int_sum sum.cong) 
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
    also have "\<dots> = (\<Sum>t<q. A $$ (u,t) * (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j))"
      by (rule sum.cong[OF refl]) (simp add: eta_coord)
    also have "\<dots> = (\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j))"
      by (simp add: sum_distrib_left algebra_simps)
    also have "\<dots> = (\<Sum>t<q. \<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
      by (intro sum.cong) (auto simp add: mult_repr sum_distrib_left up)
    also have "\<dots> = (\<Sum>t<q. \<Sum>k<d. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
      by (force intro: sum.cong sum.swap)
    also have "\<dots> = (\<Sum>k<d. \<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>k<d. (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k)"
      by (force intro: sum.cong simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum>k<d. 0 * basis k)"
      using row_zero_complex by (intro sum.cong) auto
    finally show ?thesis by simp
  qed
  have Aeta0: "A *\<^sub>v eta = 0\<^sub>v p"
    using A Aeta_component by auto
  show thesis
    using Aeta0 eta_carrier eta_coord eta_nz that x_bnd x_carrier x_nz by blast
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
  define M :: "int mat" 
    where "M \<equiv> mat (p * d) (q * d) (\<lambda>(uk,tj). C (uk div d) (tj div d) (uk mod d) (tj mod d))"
  have M: "M \<in> carrier_mat (p * d) (q * d)"
    unfolding M_def by simp
  have M_bnd: "M \<in> Bounded_mat Bnd"
    unfolding Bounded_mat_def M_def
    by (auto intro!: C_bnd less_mult_imp_div_less simp: dpos)
  obtain x :: "int vec" where x_carrier: "x \<in> carrier_vec (q * d)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * d)"
    and Mx0: "M *\<^sub>v x = 0\<^sub>v (p * d)"
    and x_bnd: "x \<in> Bounded_vec (2 * int (q * d) * max 1 Bnd)"
    using exists_ne_zero_int_vec_bounded_kernel_linear[OF M] M_bnd hpq ppos dpos by force
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
    have n_eq: "n = sg_pair_idx d (n div d) (n mod d)"
      unfolding sg_pair_idx_def using dpos by simp
    have "x $ sg_pair_idx d (n div d) (n mod d) = 0"
      using block_zero dpos n(1) td_gal_lt by force
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
      have "(M *\<^sub>v x) $ sg_pair_idx d u k = row M (sg_pair_idx d u k) \<bullet> x"
        by (rule index_mult_mat_vec[OF ukrow])
      also have "\<dots> = (\<Sum>n<q * d. M $$ (sg_pair_idx d u k, n) * x $ n)"
      proof -
        have "row M (sg_pair_idx d u k) \<bullet> x = (\<Sum>i = 0..<q * d. row M (sg_pair_idx d u k) $ i * x $ i)"
          using x_carrier by (simp add: scalar_prod_def)
        also have "\<dots> = (\<Sum>n<q * d. M $$ (sg_pair_idx d u k, n) * x $ n)"
          using uklt M x_carrier by (simp add: atLeast0LessThan)
        finally show ?thesis .
      qed
      also have "\<dots> = (\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ n)"
      proof (rule sum.cong[OF refl])
        fix n
        assume "n \<in> {..<q * d}"
        then show "M $$ (sg_pair_idx d u k, n) * x $ n = C u (n div d) k (n mod d) * x $ n"
          unfolding M_def using uklt dpos k by (simp add: sg_pair_idx_def)
      qed
      also have "\<dots> = (\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ sg_pair_idx d (n div d) (n mod d))"
        unfolding sg_pair_idx_def by presburger
      also have "\<dots> = (\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j))"
        by (rule sum_upto_sg_pair_idx[OF dpos])
      finally have "0 = (\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j))"
        using Mx0 uklt by simp
      then show ?thesis by simp
    qed
    have row_zero_complex: "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) = 0" if k: "k < d" for k
      using row_zero[OF k]
      by (metis (mono_tags, lifting) of_int_hom.hom_zero of_int_sum sum.cong) 
    have "(A *\<^sub>v eta) $ u = (\<Sum>t<q. A $$ (u,t) * eta $ t)"
    proof -
      have "(A *\<^sub>v eta) $ u = row A u \<bullet> eta"
        by (rule index_mult_mat_vec[OF rowlt])
      also have "\<dots> = (\<Sum>i = 0..<dim_vec eta. row A u $ i * eta $ i)"
        by (simp add: scalar_prod_def)
      also have "\<dots> = (\<Sum>t<q. A $$ (u,t) * eta $ t)"
        using A eta_carrier up by (simp add: atLeast0LessThan)
      finally show ?thesis .
    qed
    also have "\<dots> = (\<Sum>t<q. A $$ (u,t) * (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j))"
      by (rule sum.cong[OF refl]) (simp add: eta_coord)
    also have "\<dots> = (\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j))"
      by (simp add: sum_distrib_left algebra_simps)
    also have "\<dots> = (\<Sum>t<q. \<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
      by (intro sum.cong) (auto simp add: mult_repr sum_distrib_left up)
    also have "\<dots> = (\<Sum>t<q. \<Sum>k<d. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
      by (force intro: sum.cong sum.swap)
    also have "\<dots> = (\<Sum>k<d. \<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>k<d. (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k)"
      by (force intro: sum.cong simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum>k<d. 0 * basis k)"
      using row_zero_complex by (intro sum.cong) auto
    finally show ?thesis by simp
  qed
  have Aeta0: "A *\<^sub>v eta = 0\<^sub>v p"
    using A Aeta_component by auto
  show thesis
    by (rule that[OF eta_carrier eta_nz x_carrier x_nz Aeta0])
       (use eta_coord x_bnd in auto)
qed

end
