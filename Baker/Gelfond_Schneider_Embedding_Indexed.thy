(*  Title:      Baker/Gelfond_Schneider_Embedding_Indexed.thy
    Author:     OpenAI Codex

Indexed wrappers around the finite-embedding Siegel / contradiction layers.
Once an embedding family has been enumerated and equipped with the
biorthogonality data coming from a basis matrix and its inverse, the abstract
`recover` hypotheses disappear.
*)

theory Gelfond_Schneider_Embedding_Indexed
  imports
    Gelfond_Schneider_Embedding_Recovery
    Gelfond_Schneider_Embedding_Contradiction
    Gelfond_Schneider_Rho_Bounds
begin

context finite_embedding_indexed_recovery
begin

theorem exists_nonzero_bounded_kernel_vec_of_ehouse_entries_linear_indexed:
  fixes A :: "complex mat"
  fixes Aemb :: "nat \<Rightarrow> nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes A: "A \<in> carrier_mat p q"
  assumes ppos: "p > 0"
  assumes Dpos: "D > 0"
  assumes hpq: "2 * p \<le> q"
  assumes e0: "e0 \<in> E"
  assumes entry0: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> A $$ (u,t) = Aemb u t e0"
  assumes mult_repr:
    "\<And>u t j e. u < p \<Longrightarrow> t < q \<Longrightarrow> j < D \<Longrightarrow> e \<in> E \<Longrightarrow>
      Aemb u t e * basis j e = (\<Sum>k<D. of_int (C u t k j) * basis k e)"
  assumes repr_bnd: "\<And>k. k < D \<Longrightarrow> ehouse (repr_coeff k) \<le> R"
  assumes entry_bnd: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> ehouse (Aemb u t) \<le> H"
  assumes basis_indep:
    "\<And>c. (\<Sum>j<D. of_int (c j) * basis j e0) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes basis_bnd: "\<And>j. j < D \<Longrightarrow> ehouse (basis j) \<le> K"
  assumes R_nonneg: "0 \<le> R"
  assumes H_nonneg: "0 \<le> H"
  assumes K_nonneg: "0 \<le> K"
  obtains eta :: "complex vec" and x :: "int vec" where
      "eta \<in> carrier_vec q"
    and "eta \<noteq> 0\<^sub>v q"
    and "x \<in> carrier_vec (q * D)"
    and "x \<noteq> 0\<^sub>v (q * D)"
    and "A *\<^sub>v eta = 0\<^sub>v p"
    and "\<forall>t<q. eta $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j e0)"
    and "x \<in> Bounded_vec
      (2 * int (q * D) * max 1 (ceiling (of_nat (card E) * R * H * K)))"
    and "\<forall>t<q.
      ehouse (\<lambda>e. \<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j e) \<le>
        (of_int
          (2 * int (q * D) * max 1 (ceiling (of_nat (card E) * R * H * K))) :: real) *
          of_nat D * K"
    and "\<forall>t<q.
      cmod (eta $ t) \<le>
        (of_int
          (2 * int (q * D) * max 1 (ceiling (of_nat (card E) * R * H * K))) :: real) *
          of_nat D * K"
proof -
  obtain eta :: "complex vec" and x :: "int vec" where
      "eta \<in> carrier_vec q"
    and "eta \<noteq> 0\<^sub>v q"
    and "x \<in> carrier_vec (q * D)"
    and "x \<noteq> 0\<^sub>v (q * D)"
    and "A *\<^sub>v eta = 0\<^sub>v p"
    and "\<forall>t<q. eta $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j e0)"
    and "x \<in> Bounded_vec
      (2 * int (q * D) * max 1 (ceiling (of_nat (card E) * R * H * K)))"
    and "\<forall>t<q.
      ehouse (\<lambda>e. \<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j e) \<le>
        (of_int
          (2 * int (q * D) * max 1 (ceiling (of_nat (card E) * R * H * K))) :: real) *
          of_nat D * K"
    and "\<forall>t<q.
      cmod (eta $ t) \<le>
        (of_int
          (2 * int (q * D) * max 1 (ceiling (of_nat (card E) * R * H * K))) :: real) *
          of_nat D * K"
    by (rule exists_nonzero_bounded_kernel_vec_of_ehouse_entries_linear[OF A ppos Dpos hpq e0 entry0 mult_repr
          recover_int_coordinate repr_bnd entry_bnd basis_indep basis_bnd R_nonneg H_nonneg K_nonneg])
  then show thesis
    using that by blast
qed

theorem exists_nonzero_bounded_kernel_vec_of_matrix_entry_bounds_linear_indexed:
  fixes A :: "complex mat"
  fixes Aemb :: "nat \<Rightarrow> nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes A: "A \<in> carrier_mat p q"
  assumes ppos: "p > 0"
  assumes Dpos: "D > 0"
  assumes hpq: "2 * p \<le> q"
  assumes e0: "e0 \<in> E"
  assumes entry0: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> A $$ (u,t) = Aemb u t e0"
  assumes mult_repr:
    "\<And>u t j e. u < p \<Longrightarrow> t < q \<Longrightarrow> j < D \<Longrightarrow> e \<in> E \<Longrightarrow>
      Aemb u t e * basis j e = (\<Sum>k<D. of_int (C u t k j) * basis k e)"
  assumes inv_bound:
    "\<And>k i. k < D \<Longrightarrow> i < D \<Longrightarrow> cmod (inverse_basis_matrix_entry k i) \<le> R"
  assumes entry_bnd: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> ehouse (Aemb u t) \<le> H"
  assumes basis_indep:
    "\<And>c. (\<Sum>j<D. of_int (c j) * basis j e0) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes basis_bound:
    "\<And>j i. j < D \<Longrightarrow> i < D \<Longrightarrow> cmod (basis_matrix_entry i j) \<le> K"
  assumes R_nonneg: "0 \<le> R"
  assumes H_nonneg: "0 \<le> H"
  assumes K_nonneg: "0 \<le> K"
  obtains eta :: "complex vec" and x :: "int vec" where
      "eta \<in> carrier_vec q"
    and "eta \<noteq> 0\<^sub>v q"
    and "x \<in> carrier_vec (q * D)"
    and "x \<noteq> 0\<^sub>v (q * D)"
    and "A *\<^sub>v eta = 0\<^sub>v p"
    and "\<forall>t<q. eta $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j e0)"
    and "x \<in> Bounded_vec
      (2 * int (q * D) * max 1 (ceiling (of_nat (card E) * R * H * K)))"
    and "\<forall>t<q.
      ehouse (\<lambda>e. \<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j e) \<le>
        (of_int
          (2 * int (q * D) * max 1 (ceiling (of_nat (card E) * R * H * K))) :: real) *
          of_nat D * K"
    and "\<forall>t<q.
      cmod (eta $ t) \<le>
        (of_int
          (2 * int (q * D) * max 1 (ceiling (of_nat (card E) * R * H * K))) :: real) *
          of_nat D * K"
proof -
  have repr_bnd: "\<And>k. k < D \<Longrightarrow> ehouse (repr_coeff k) \<le> R"
  proof -
    fix k
    assume klt: "k < D"
    show "ehouse (repr_coeff k) \<le> R"
      by (rule repr_coeff_ehouse_le_of_inverse_matrix_bound[OF R_nonneg]) (use klt inv_bound in auto)
  qed
  have basis_bnd: "\<And>j. j < D \<Longrightarrow> ehouse (basis j) \<le> K"
  proof -
    fix j
    assume jlt: "j < D"
    show "ehouse (basis j) \<le> K"
      by (rule basis_ehouse_le_of_matrix_bound[OF K_nonneg]) (use jlt basis_bound in auto)
  qed
  obtain eta :: "complex vec" and x :: "int vec" where
      "eta \<in> carrier_vec q"
    and "eta \<noteq> 0\<^sub>v q"
    and "x \<in> carrier_vec (q * D)"
    and "x \<noteq> 0\<^sub>v (q * D)"
    and "A *\<^sub>v eta = 0\<^sub>v p"
    and "\<forall>t<q. eta $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j e0)"
    and "x \<in> Bounded_vec
      (2 * int (q * D) * max 1 (ceiling (of_nat (card E) * R * H * K)))"
    and "\<forall>t<q.
      ehouse (\<lambda>e. \<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j e) \<le>
        (of_int
          (2 * int (q * D) * max 1 (ceiling (of_nat (card E) * R * H * K))) :: real) *
          of_nat D * K"
    and "\<forall>t<q.
      cmod (eta $ t) \<le>
        (of_int
          (2 * int (q * D) * max 1 (ceiling (of_nat (card E) * R * H * K))) :: real) *
          of_nat D * K"
    by (rule exists_nonzero_bounded_kernel_vec_of_ehouse_entries_linear_indexed[OF A ppos Dpos hpq e0 entry0
          mult_repr repr_bnd entry_bnd basis_indep basis_bnd R_nonneg H_nonneg K_nonneg])
  then show thesis
    using that by blast
qed

theorem no_gelfond_schneider_data_of_row_scaled_ehouse_root_bound_linear_indexed:
  fixes Aemb :: "nat \<Rightarrow> nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  assumes Dpos: "D > 0"
  assumes e0: "e0 \<in> E"
  assumes entry0:
    "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) = Aemb u t e0"
  assumes mult_repr:
    "\<And>u t j e. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow> e \<in> E \<Longrightarrow>
      Aemb u t e * basis j e = (\<Sum>k<D. of_int (C u t k j) * basis k e)"
  assumes repr_bnd: "\<And>k. k < D \<Longrightarrow> ehouse (repr_coeff k) \<le> R"
  assumes entry_bnd:
    "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> ehouse (Aemb u t) \<le> A"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j e0)"
  assumes basis_indep:
    "\<And>c. (\<Sum>j<D. of_int (c j) * basis j e0) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes basis_bnd: "\<And>j. j < D \<Longrightarrow> ehouse (basis j) \<le> K"
  assumes R_nonneg: "0 \<le> R"
  assumes A_nonneg: "0 \<le> A"
  assumes K_nonneg: "0 \<le> K"
  assumes root_upper:
    "\<And>v x r c rho z.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j e0)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 (ceiling (of_nat (card E) * R * A * K))) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      z \<in> set (complex_roots_of_int_poly (min_int_poly rho)) \<Longrightarrow>
      cmod z \<le> H"
  assumes H_nonneg: "0 \<le> H"
  assumes explicit_small:
    "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j e0)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 (ceiling (of_nat (card E) * R * A * K))) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      (of_nat (q * q) *
        ((of_int (2 * int (q * q * D) * max 1 (ceiling (of_nat (card E) * R * A * K))) :: real) *
          of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      H ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
  shows False
proof -
  show False
    by (rule no_gelfond_schneider_data_of_row_scaled_ehouse_root_bound_linear[OF d qpos npos dvd Dpos e0 entry0
          mult_repr recover_int_coordinate repr_bnd entry_bnd basis_int basis_indep basis_bnd
          R_nonneg A_nonneg K_nonneg root_upper H_nonneg explicit_small])
       simp
qed

theorem no_gelfond_schneider_data_of_row_scaled_matrix_root_bound_linear_indexed:
  fixes Aemb :: "nat \<Rightarrow> nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  assumes Dpos: "D > 0"
  assumes e0: "e0 \<in> E"
  assumes entry0:
    "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) = Aemb u t e0"
  assumes mult_repr:
    "\<And>u t j e. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow> e \<in> E \<Longrightarrow>
      Aemb u t e * basis j e = (\<Sum>k<D. of_int (C u t k j) * basis k e)"
  assumes inv_bound:
    "\<And>k i. k < D \<Longrightarrow> i < D \<Longrightarrow> cmod (inverse_basis_matrix_entry k i) \<le> R"
  assumes entry_bnd:
    "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> ehouse (Aemb u t) \<le> A"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j e0)"
  assumes basis_indep:
    "\<And>c. (\<Sum>j<D. of_int (c j) * basis j e0) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes basis_bound:
    "\<And>j i. j < D \<Longrightarrow> i < D \<Longrightarrow> cmod (basis_matrix_entry i j) \<le> K"
  assumes R_nonneg: "0 \<le> R"
  assumes A_nonneg: "0 \<le> A"
  assumes K_nonneg: "0 \<le> K"
  assumes root_upper:
    "\<And>v x r c rho z.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j e0)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 (ceiling (of_nat (card E) * R * A * K))) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      z \<in> set (complex_roots_of_int_poly (min_int_poly rho)) \<Longrightarrow>
      cmod z \<le> H"
  assumes H_nonneg: "0 \<le> H"
  assumes explicit_small:
    "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j e0)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 (ceiling (of_nat (card E) * R * A * K))) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      (of_nat (q * q) *
        ((of_int (2 * int (q * q * D) * max 1 (ceiling (of_nat (card E) * R * A * K))) :: real) *
          of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      H ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
  shows False
proof -
  have repr_bnd: "\<And>k. k < D \<Longrightarrow> ehouse (repr_coeff k) \<le> R"
  proof -
    fix k
    assume klt: "k < D"
    show "ehouse (repr_coeff k) \<le> R"
      by (rule repr_coeff_ehouse_le_of_inverse_matrix_bound[OF R_nonneg]) (use klt inv_bound in auto)
  qed
  have basis_bnd: "\<And>j. j < D \<Longrightarrow> ehouse (basis j) \<le> K"
  proof -
    fix j
    assume jlt: "j < D"
    show "ehouse (basis j) \<le> K"
      by (rule basis_ehouse_le_of_matrix_bound[OF K_nonneg]) (use jlt basis_bound in auto)
  qed
  show False
    by (rule no_gelfond_schneider_data_of_row_scaled_ehouse_root_bound_linear_indexed[OF d qpos npos dvd Dpos e0
          entry0 mult_repr repr_bnd entry_bnd basis_int basis_indep basis_bnd R_nonneg A_nonneg
          K_nonneg root_upper H_nonneg explicit_small])
qed

theorem no_gelfond_schneider_data_of_row_scaled_matrix_house_bound_linear_indexed:
  fixes Aemb :: "nat \<Rightarrow> nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  assumes Dpos: "D > 0"
  assumes e0: "e0 \<in> E"
  assumes entry0:
    "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) = Aemb u t e0"
  assumes mult_repr:
    "\<And>u t j e. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow> e \<in> E \<Longrightarrow>
      Aemb u t e * basis j e = (\<Sum>k<D. of_int (C u t k j) * basis k e)"
  assumes inv_bound:
    "\<And>k i. k < D \<Longrightarrow> i < D \<Longrightarrow> cmod (inverse_basis_matrix_entry k i) \<le> R"
  assumes entry_bnd:
    "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> ehouse (Aemb u t) \<le> A"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j e0)"
  assumes basis_indep:
    "\<And>c. (\<Sum>j<D. of_int (c j) * basis j e0) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes basis_bound:
    "\<And>j i. j < D \<Longrightarrow> i < D \<Longrightarrow> cmod (basis_matrix_entry i j) \<le> K"
  assumes R_nonneg: "0 \<le> R"
  assumes A_nonneg: "0 \<le> A"
  assumes K_nonneg: "0 \<le> K"
  assumes house_upper:
    "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j e0)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 (ceiling (of_nat (card E) * R * A * K))) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      gs_house rho \<le> H"
  assumes H_nonneg: "0 \<le> H"
  assumes explicit_small:
    "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j e0)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 (ceiling (of_nat (card E) * R * A * K))) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      (of_nat (q * q) *
        ((of_int (2 * int (q * q * D) * max 1 (ceiling (of_nat (card E) * R * A * K))) :: real) *
          of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      H ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
  shows False
proof -
  have repr_bnd: "\<And>k. k < D \<Longrightarrow> ehouse (repr_coeff k) \<le> R"
  proof -
    fix k
    assume klt: "k < D"
    show "ehouse (repr_coeff k) \<le> R"
      by (rule repr_coeff_ehouse_le_of_inverse_matrix_bound[OF R_nonneg]) (use klt inv_bound in auto)
  qed
  have basis_bnd: "\<And>j. j < D \<Longrightarrow> ehouse (basis j) \<le> K"
  proof -
    fix j
    assume jlt: "j < D"
    show "ehouse (basis j) \<le> K"
      by (rule basis_ehouse_le_of_matrix_bound[OF K_nonneg]) (use jlt basis_bound in auto)
  qed
  show False
    by (rule no_gelfond_schneider_data_of_row_scaled_ehouse_house_bound_linear[OF d qpos npos dvd Dpos e0
          entry0 mult_repr recover_int_coordinate repr_bnd entry_bnd basis_int basis_indep basis_bnd
          R_nonneg A_nonneg K_nonneg house_upper H_nonneg explicit_small])
qed


theorem no_gelfond_schneider_data_of_row_scaled_matrix_house_product_bound_linear_indexed:
  fixes Aemb :: "nat \<Rightarrow> nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  fixes c5 c14 :: real
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  assumes Dpos: "D > 0"
  assumes e0: "e0 \<in> E"
  assumes entry0:
    "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) = Aemb u t e0"
  assumes mult_repr:
    "\<And>u t j e. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow> e \<in> E \<Longrightarrow>
      Aemb u t e * basis j e = (\<Sum>k<D. of_int (C u t k j) * basis k e)"
  assumes inv_bound:
    "\<And>k i. k < D \<Longrightarrow> i < D \<Longrightarrow> cmod (inverse_basis_matrix_entry k i) \<le> R"
  assumes entry_bnd:
    "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> ehouse (Aemb u t) \<le> A"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j e0)"
  assumes basis_indep:
    "\<And>c. (\<Sum>j<D. of_int (c j) * basis j e0) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes basis_bound:
    "\<And>j i. j < D \<Longrightarrow> i < D \<Longrightarrow> cmod (basis_matrix_entry i j) \<le> K"
  assumes R_nonneg: "0 \<le> R"
  assumes A_nonneg: "0 \<le> A"
  assumes K_nonneg: "0 \<le> K"
  assumes hpos: "h > 0"
  assumes q_def: "q = gs_q_choice h (c14 * c5)"
  assumes c14_ge1: "1 \<le> c14"
  assumes c5_gt1: "1 < c5"
  assumes rho_upper:
    "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j e0)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 (ceiling (of_nat (card E) * R * A * K))) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) \<le>
        c14 powr of_nat r *
        of_nat r powr ((- of_nat r / 2 + 3 * of_nat h / 2) :: real)"
  shows False
proof -
  have repr_bnd: "\<And>k. k < D \<Longrightarrow> ehouse (repr_coeff k) \<le> R"
  proof -
    fix k
    assume klt: "k < D"
    show "ehouse (repr_coeff k) \<le> R"
      by (rule repr_coeff_ehouse_le_of_inverse_matrix_bound[OF R_nonneg]) (use klt inv_bound in auto)
  qed
  have basis_bnd: "\<And>j. j < D \<Longrightarrow> ehouse (basis j) \<le> K"
  proof -
    fix j
    assume jlt: "j < D"
    show "ehouse (basis j) \<le> K"
      by (rule basis_ehouse_le_of_matrix_bound[OF K_nonneg]) (use jlt basis_bound in auto)
  qed
  have mult_repr0:
    "\<And>u t j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * basis j e0 =
        (\<Sum>k<D. of_int (C u t k j) * basis k e0)"
  proof -
    fix u t j
    assume up: "u < gs_m h * gs_n h q"
    assume tq: "t < q * q"
    assume jlt: "j < D"
    have "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * basis j e0 =
        Aemb u t e0 * basis j e0"
      by (simp add: entry0[OF up tq])
    also have "... = (\<Sum>k<D. of_int (C u t k j) * basis k e0)"
      by (rule mult_repr[OF up tq jlt e0])
    finally show
      "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * basis j e0 =
        (\<Sum>k<D. of_int (C u t k j) * basis k e0)" .
  qed
  have C_bnd:
    "\<And>u t k j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow>
      abs (C u t k j) \<le> ceiling (of_nat (card E) * R * A * K)"
    by (rule abs_int_structure_constant_ehouse_le[OF recover_int_coordinate repr_bnd entry_bnd basis_bnd
          R_nonneg A_nonneg K_nonneg mult_repr])
  show False
    by (rule no_gelfond_schneider_data_of_row_scaled_house_product_bound_linear
          [OF d qpos npos dvd Dpos basis_int basis_indep mult_repr0 C_bnd hpos q_def c14_ge1 c5_gt1 rho_upper])
qed

end

end
