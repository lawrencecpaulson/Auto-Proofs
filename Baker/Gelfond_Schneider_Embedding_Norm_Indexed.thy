(*  Title:      Baker/Gelfond_Schneider_Embedding_Norm_Indexed.thy
    Author:     OpenAI Codex

Indexed wrapper for the generic rho-norm contradiction shell. This is the
interface that matches Lean's `use6and8`/`use5` route most directly: once a
positive quantity attached to rho satisfies the standard upper and inverse
bounds, the row-scaled contradiction follows.
*)

theory Gelfond_Schneider_Embedding_Norm_Indexed
  imports Gelfond_Schneider_Embedding_Indexed
begin

context finite_embedding_indexed_recovery
begin
theorem no_gelfond_schneider_data_of_row_scaled_matrix_norm_bound_linear_indexed:
  fixes Aemb :: "nat \<Rightarrow> nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  fixes rho_norm :: "complex \<Rightarrow> real"
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
  assumes c5_ge1: "1 \<le> c5"
  assumes rho_pos:
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
      0 < rho_norm rho"
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
      rho_norm rho \<le>
        c14 powr of_nat r *
        of_nat r powr ((- of_nat r / 2 + 3 * of_nat h / 2) :: real)"
  assumes rho_inv_lt:
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
      inverse (rho_norm rho) < c5 powr of_nat r"
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
    by (rule no_gelfond_schneider_data_of_row_scaled_norm_bounds_linear[where rho_norm = rho_norm,
          OF d qpos npos dvd Dpos basis_int basis_indep mult_repr0 C_bnd hpos q_def c14_ge1 c5_ge1
             rho_pos rho_upper rho_inv_lt])
qed

end

end
