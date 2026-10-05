(*  Title:      Gelfond_Schneider/Gelfond_Schneider_Contradiction.thy
    Author:     OpenAI Codex

Abstract contradiction packaging for the standalone Gelfond-Schneider route.
This isolates the final analytic obligation: once an upper bound below 1 is
available for the same row-scaled witness produced by the arithmetic layer,
the contradiction is immediate.
*)

theory Gelfond_Schneider_Contradiction
  imports Gelfond_Schneider_Scaled_Bounded
begin

section \<open>Contradiction from Matching Upper Bounds\<close>

theorem no_gelfond_schneider_data_of_row_scaled_upper_bound:
  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  assumes Dpos: "D > 0"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j)"
  assumes basis_indep: "\<And>c. (\<Sum>j<D. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes mult_repr:
    "\<And>u t j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * basis j =
        (\<Sum>k<D. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow>
      abs (C u t k j) \<le> Bnd"
  assumes upper:
    "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      algebraic_int rho \<Longrightarrow>
      rho \<noteq> 0 \<Longrightarrow>
      cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
  shows False
proof -
  obtain v :: "complex vec" and x :: "int vec" and r and c and rho :: complex where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
    and repr: "\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd))"
    and r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
    and deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
    and c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    and rho_def:
      "rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
    and rho_int: "algebraic_int rho"
    and rho_nz: "rho \<noteq> 0"
    and lower:
      "1 \<le> cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
    by (rule gs_exists_row_scaled_bounded_nonzero_algebraic_int_house_lower_bound
          [OF d qpos npos dvd Dpos basis_int basis_indep mult_repr C_bnd])
  have upper_lt:
      "cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
    by (rule upper[OF v_carrier v_nz v_ker vint repr x_carrier x_nz x_bnd r_eq deriv_nz c_def rho_def rho_int rho_nz])
  from lower upper_lt show False
    by linarith
qed

theorem no_gelfond_schneider_data_of_row_scaled_upper_bound_linear:
  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  assumes Dpos: "D > 0"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j)"
  assumes basis_indep: "\<And>c. (\<Sum>j<D. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes mult_repr:
    "\<And>u t j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * basis j =
        (\<Sum>k<D. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow>
      abs (C u t k j) \<le> Bnd"
  assumes upper:
    "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      algebraic_int rho \<Longrightarrow>
      rho \<noteq> 0 \<Longrightarrow>
      cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
  shows False
proof -
  obtain v :: "complex vec" and x :: "int vec" and r and c and rho :: complex where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
    and repr: "\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd)"
    and r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
    and deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
    and c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    and rho_def:
      "rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
    and rho_int: "algebraic_int rho"
    and rho_nz: "rho \<noteq> 0"
    and lower:
      "1 \<le> cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
    by (rule gs_exists_row_scaled_bounded_nonzero_algebraic_int_house_lower_bound_linear
          [OF d qpos npos dvd Dpos basis_int basis_indep mult_repr C_bnd])
  have upper_lt:
      "cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
    by (rule upper[OF v_carrier v_nz v_ker vint repr x_carrier x_nz x_bnd r_eq deriv_nz c_def rho_def rho_int rho_nz])
  from lower upper_lt show False
    by linarith
qed

theorem no_gelfond_schneider_data_of_row_scaled_explicit_cmod_upper_bound:
  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  assumes Dpos: "D > 0"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j)"
  assumes basis_indep: "\<And>c. (\<Sum>j<D. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes mult_repr:
    "\<And>u t j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * basis j =
        (\<Sum>k<D. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow>
      abs (C u t k j) \<le> Bnd"
  assumes basis_bnd: "\<And>j. j < D \<Longrightarrow> cmod (basis j) \<le> K"
  assumes K_nonneg: "0 \<le> K"
  assumes upper:
    "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      algebraic_int rho \<Longrightarrow>
      rho \<noteq> 0 \<Longrightarrow>
      (of_nat (q * q) *
        ((of_int (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) :: real) *
          of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      gs_house rho ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
  shows False
proof -
  obtain v :: "complex vec" and x :: "int vec" and r and c and rho :: complex where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
    and repr: "\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd))"
    and r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
    and deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
    and c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    and rho_def:
      "rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
    and rho_int: "algebraic_int rho"
    and rho_nz: "rho \<noteq> 0"
    and rho_cmod:
      "cmod rho \<le>
        of_nat (q * q) *
        ((of_int (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) :: real) *
          of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))"
    by (rule gs_exists_row_scaled_bounded_nonzero_algebraic_int_cmod_upper_bound
          [OF d qpos npos dvd Dpos basis_int basis_indep mult_repr C_bnd basis_bnd K_nonneg])
  have lower:
      "1 \<le> cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
    by (rule one_le_self_mul_house_pow_of_nonzero_algebraic_int[OF rho_int rho_nz])
  have upper_lt:
      "(of_nat (q * q) *
        ((of_int (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) :: real) *
          of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      gs_house rho ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
    by (rule upper[OF v_carrier v_nz v_ker vint repr x_carrier x_nz x_bnd r_eq deriv_nz c_def rho_def rho_int rho_nz])
  have upper_rho:
      "cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
  proof -
    have hpow_nonneg:
        "0 \<le> gs_house rho ^
          (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
      by simp
    have "cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) \<le>
      (of_nat (q * q) *
        ((of_int (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) :: real) *
          of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      gs_house rho ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
      using rho_cmod by (intro mult_right_mono hpow_nonneg)
    then show ?thesis
      using upper_lt by linarith
  qed
  from lower upper_rho show False
    by linarith
qed

theorem no_gelfond_schneider_data_of_row_scaled_explicit_cmod_upper_bound_linear:
  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  assumes Dpos: "D > 0"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j)"
  assumes basis_indep: "\<And>c. (\<Sum>j<D. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes mult_repr:
    "\<And>u t j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * basis j =
        (\<Sum>k<D. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow>
      abs (C u t k j) \<le> Bnd"
  assumes basis_bnd: "\<And>j. j < D \<Longrightarrow> cmod (basis j) \<le> K"
  assumes K_nonneg: "0 \<le> K"
  assumes upper:
    "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      algebraic_int rho \<Longrightarrow>
      rho \<noteq> 0 \<Longrightarrow>
      (of_nat (q * q) *
        ((of_int (2 * int (q * q * D) * max 1 Bnd) :: real) * of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      gs_house rho ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
  shows False
proof -
  obtain v :: "complex vec" and x :: "int vec" and r and c and rho :: complex where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
    and repr: "\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd)"
    and r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
    and deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
    and c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    and rho_def:
      "rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
    and rho_int: "algebraic_int rho"
    and rho_nz: "rho \<noteq> 0"
    and rho_cmod:
      "cmod rho \<le>
        of_nat (q * q) *
        ((of_int (2 * int (q * q * D) * max 1 Bnd) :: real) * of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))"
    by (rule gs_exists_row_scaled_bounded_nonzero_algebraic_int_cmod_upper_bound_linear
          [OF d qpos npos dvd Dpos basis_int basis_indep mult_repr C_bnd basis_bnd K_nonneg])
  have lower:
      "1 \<le> cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
    by (rule one_le_self_mul_house_pow_of_nonzero_algebraic_int[OF rho_int rho_nz])
  have upper_lt:
      "(of_nat (q * q) *
        ((of_int (2 * int (q * q * D) * max 1 Bnd) :: real) * of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      gs_house rho ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
    by (rule upper[OF v_carrier v_nz v_ker vint repr x_carrier x_nz x_bnd r_eq deriv_nz c_def rho_def rho_int rho_nz])
  have upper_rho:
      "cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
  proof -
    have hpow_nonneg:
        "0 \<le> gs_house rho ^
          (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
      by simp
    have "cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) \<le>
      (of_nat (q * q) *
        ((of_int (2 * int (q * q * D) * max 1 Bnd) :: real) * of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      gs_house rho ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
      using rho_cmod by (intro mult_right_mono hpow_nonneg)
    then show ?thesis
      using upper_lt by linarith
  qed
  from lower upper_rho show False
    by linarith
qed

theorem no_gelfond_schneider_data_of_row_scaled_uniform_house_bound:
  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  assumes Dpos: "D > 0"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j)"
  assumes basis_indep: "\<And>c. (\<Sum>j<D. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes mult_repr:
    "\<And>u t j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * basis j =
        (\<Sum>k<D. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow>
      abs (C u t k j) \<le> Bnd"
  assumes basis_bnd: "\<And>j. j < D \<Longrightarrow> cmod (basis j) \<le> K"
  assumes K_nonneg: "0 \<le> K"
  assumes house_upper:
    "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) \<Longrightarrow>
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
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      (of_nat (q * q) *
        ((of_int (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) :: real) *
          of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      H ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
  shows False
proof -
  have upper:
    "\<And>(v :: complex vec) (x :: int vec) r c (rho :: complex).
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      algebraic_int rho \<Longrightarrow>
      rho \<noteq> 0 \<Longrightarrow>
      (of_nat (q * q) *
        ((of_int (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) :: real) *
          of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      gs_house rho ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
  proof -
    fix v :: "complex vec" and x :: "int vec" and r and c and rho :: complex

    assume v_carrier: "v \<in> carrier_vec (q * q)"
    assume v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    assume v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    assume vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
    assume repr: "\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)"
    assume x_carrier: "x \<in> carrier_vec (q * q * D)"
    assume x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    assume x_bnd: "x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd))"
    assume r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
    assume deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
    assume c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    assume rho_def:
      "rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
    assume rho_int: "algebraic_int rho"
    assume rho_nz: "rho \<noteq> 0"
    let ?e = "card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1"
    let ?X = "int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)"
    let ?B =
      "of_nat (q * q) *
        ((of_int ?X :: real) * of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))"
    have X_nonneg: "0 \<le> ?X"
    proof (rule ccontr)
      assume "\<not> 0 \<le> ?X"
      then have X_neg: "?X < 0"
        by simp
      have x_zero: "x = 0\<^sub>v (q * q * D)"
      proof (rule eq_vecI)
        show "dim_vec x = dim_vec (0\<^sub>v (q * q * D))"
          using x_carrier by simp
      next
        fix i
        assume i: "i < dim_vec (0\<^sub>v (q * q * D))"
        then have ilt: "i < q * q * D"
          by simp
        have le: "abs (Matrix.vec_index x i) \<le> ?X"
          using x_bnd x_carrier ilt unfolding Bounded_vec_def by fastforce
        from le X_neg have "abs (Matrix.vec_index x i) < 0"
          by linarith
        then show "Matrix.vec_index x i = Matrix.vec_index (0\<^sub>v (q * q * D)) i"
          by simp
      qed
      with x_nz show False
        by contradiction
    qed
    have Xreal_nonneg: "0 \<le> (of_int ?X :: real)"
      using X_nonneg of_int_0_le_iff by blast

    have B_nonneg: "0 \<le> ?B"
      using Xreal_nonneg K_nonneg by (intro mult_nonneg_nonneg) simp_all


    have hpow_le: "gs_house rho ^ ?e \<le> H ^ ?e"
      using H_nonneg house_upper[OF v_carrier v_nz v_ker vint repr x_carrier x_nz x_bnd r_eq deriv_nz c_def rho_def]
      by (intro power_mono) simp_all

    have "?B * gs_house rho ^ ?e \<le> ?B * H ^ ?e"
      by (rule mult_left_mono[OF hpow_le B_nonneg])
    also have "... < 1"
      by (rule explicit_small[OF v_carrier v_nz v_ker vint repr x_carrier x_nz x_bnd r_eq deriv_nz c_def rho_def])
    finally show
      "(of_nat (q * q) *
        ((of_int (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) :: real) *
          of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      gs_house rho ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1" .
  qed
  show False
    by (rule no_gelfond_schneider_data_of_row_scaled_explicit_cmod_upper_bound
          [OF d qpos npos dvd Dpos basis_int basis_indep mult_repr C_bnd basis_bnd K_nonneg upper])
qed

theorem no_gelfond_schneider_data_of_row_scaled_uniform_house_bound_linear:
  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  assumes Dpos: "D > 0"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j)"
  assumes basis_indep: "\<And>c. (\<Sum>j<D. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes mult_repr:
    "\<And>u t j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * basis j =
        (\<Sum>k<D. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow>
      abs (C u t k j) \<le> Bnd"
  assumes basis_bnd: "\<And>j. j < D \<Longrightarrow> cmod (basis j) \<le> K"
  assumes K_nonneg: "0 \<le> K"
  assumes house_upper:
    "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd) \<Longrightarrow>
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
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      (of_nat (q * q) *
        ((of_int (2 * int (q * q * D) * max 1 Bnd) :: real) * of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      H ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
  shows False
proof -
  have upper:
    "\<And>(v :: complex vec) (x :: int vec) r c (rho :: complex).
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      algebraic_int rho \<Longrightarrow>
      rho \<noteq> 0 \<Longrightarrow>
      (of_nat (q * q) *
        ((of_int (2 * int (q * q * D) * max 1 Bnd) :: real) * of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      gs_house rho ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
  proof -
    fix v :: "complex vec" and x :: "int vec" and r and c and rho :: complex

    assume v_carrier: "v \<in> carrier_vec (q * q)"
    assume v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    assume v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    assume vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
    assume repr: "\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)"
    assume x_carrier: "x \<in> carrier_vec (q * q * D)"
    assume x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    assume x_bnd: "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd)"
    assume r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
    assume deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
    assume c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    assume rho_def:
      "rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
    assume rho_int: "algebraic_int rho"
    assume rho_nz: "rho \<noteq> 0"
    let ?e = "card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1"
    let ?B =
      "of_nat (q * q) *
        ((of_int (2 * int (q * q * D) * max 1 Bnd) :: real) * of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))"
    have B_nonneg: "0 \<le> ?B"
      using K_nonneg by (intro mult_nonneg_nonneg) simp_all
    have hpow_le: "gs_house rho ^ ?e \<le> H ^ ?e"
      using H_nonneg house_upper[OF v_carrier v_nz v_ker vint repr x_carrier x_nz x_bnd r_eq deriv_nz c_def rho_def]
      by (intro power_mono) simp_all
    have "?B * gs_house rho ^ ?e \<le> ?B * H ^ ?e"
      by (rule mult_left_mono[OF hpow_le B_nonneg])
    also have "... < 1"
      by (rule explicit_small[OF v_carrier v_nz v_ker vint repr x_carrier x_nz x_bnd r_eq deriv_nz c_def rho_def])
    finally show
      "(of_nat (q * q) *
        ((of_int (2 * int (q * q * D) * max 1 Bnd) :: real) * of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      gs_house rho ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1" .
  qed
  show False
    by (rule no_gelfond_schneider_data_of_row_scaled_explicit_cmod_upper_bound_linear
          [OF d qpos npos dvd Dpos basis_int basis_indep mult_repr C_bnd basis_bnd K_nonneg upper])
qed


theorem no_gelfond_schneider_data_of_row_scaled_uniform_root_bound:
  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  assumes Dpos: "D > 0"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j)"
  assumes basis_indep: "\<And>c. (\<Sum>j<D. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes mult_repr:
    "\<And>u t j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * basis j =
        (\<Sum>k<D. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow>
      abs (C u t k j) \<le> Bnd"
  assumes basis_bnd: "\<And>j. j < D \<Longrightarrow> cmod (basis j) \<le> K"
  assumes K_nonneg: "0 \<le> K"
  assumes root_upper:
    "\<And>v x r c rho z.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) \<Longrightarrow>
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
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      (of_nat (q * q) *
        ((of_int (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) :: real) *
          of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      H ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
  shows False
proof -
  have house_upper:
    "\<And>(v :: complex vec) (x :: int vec) r c (rho :: complex).
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      gs_house rho \<le> H"
  proof -
    fix v :: "complex vec" and x :: "int vec" and r and c and rho :: complex

    assume v_carrier: "v \<in> carrier_vec (q * q)"
    assume v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    assume v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    assume vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
    assume repr: "\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)"
    assume x_carrier: "x \<in> carrier_vec (q * q * D)"
    assume x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    assume x_bnd: "x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd))"
    assume r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
    assume deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
    assume c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    assume rho_def:
      "rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"

    show "gs_house rho \<le> H"
    proof (rule gs_house_le_of_roots_le[OF H_nonneg])
      fix z
      assume z: "z \<in> set (complex_roots_of_int_poly (min_int_poly rho))"
      show "cmod z \<le> H"
        by (rule root_upper[OF v_carrier v_nz v_ker vint repr x_carrier x_nz x_bnd r_eq deriv_nz c_def rho_def z])
    qed
  qed
  show False
    by (rule no_gelfond_schneider_data_of_row_scaled_uniform_house_bound
          [OF d qpos npos dvd Dpos basis_int basis_indep mult_repr C_bnd basis_bnd K_nonneg house_upper H_nonneg explicit_small])
qed

theorem no_gelfond_schneider_data_of_row_scaled_uniform_root_bound_linear:
  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  assumes Dpos: "D > 0"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j)"
  assumes basis_indep: "\<And>c. (\<Sum>j<D. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes mult_repr:
    "\<And>u t j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * basis j =
        (\<Sum>k<D. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow>
      abs (C u t k j) \<le> Bnd"
  assumes basis_bnd: "\<And>j. j < D \<Longrightarrow> cmod (basis j) \<le> K"
  assumes K_nonneg: "0 \<le> K"
  assumes root_upper:
    "\<And>v x r c rho z.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd) \<Longrightarrow>
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
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      (of_nat (q * q) *
        ((of_int (2 * int (q * q * D) * max 1 Bnd) :: real) * of_nat D * K) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      H ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
  shows False
proof -
  have house_upper:
    "\<And>(v :: complex vec) (x :: int vec) r c (rho :: complex).
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      gs_house rho \<le> H"
  proof -
    fix v :: "complex vec" and x :: "int vec" and r and c and rho :: complex

    assume v_carrier: "v \<in> carrier_vec (q * q)"
    assume v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    assume v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    assume vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
    assume repr: "\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)"
    assume x_carrier: "x \<in> carrier_vec (q * q * D)"
    assume x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    assume x_bnd: "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd)"
    assume r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
    assume deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
    assume c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    assume rho_def:
      "rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"

    show "gs_house rho \<le> H"
    proof (rule gs_house_le_of_roots_le[OF H_nonneg])
      fix z
      assume z: "z \<in> set (complex_roots_of_int_poly (min_int_poly rho))"
      show "cmod z \<le> H"
        by (rule root_upper[OF v_carrier v_nz v_ker vint repr x_carrier x_nz x_bnd r_eq deriv_nz c_def rho_def z])
    qed
  qed
  show False
    by (rule no_gelfond_schneider_data_of_row_scaled_uniform_house_bound_linear
          [OF d qpos npos dvd Dpos basis_int basis_indep mult_repr C_bnd basis_bnd K_nonneg house_upper H_nonneg explicit_small])
qed

end
