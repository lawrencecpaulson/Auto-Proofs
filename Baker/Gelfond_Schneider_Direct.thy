(*  Title:      Baker/Gelfond_Schneider_Direct.thy
    Author:     OpenAI Codex

Direct packaging of the completed matrix/order part of the standalone
Gelfond-Schneider argument. This isolates the witness data that the remaining
arithmetic lower-bound / analytic upper-bound contradiction will consume,
following the structure of the Lean `MainAlgSetup`/`MainOrder` path rather
than the temporary two-logarithm detour.
*)

theory Gelfond_Schneider_Direct
  imports
    Gelfond_Schneider_Matrix
    "Finite_Embedding_Bounds.Structure_Constant_Kernels"

begin

declare [[apply_timeout = 10]]

section \<open>Bounded kernels for the Gelfond-Schneider system\<close>

theorem gs_system_mat_exists_bounded_algebraic_int_kernel:

  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes dpos: "D > 0"
  assumes mnq: "m * n < q * q"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j)"
  assumes basis_indep: "\<And>c. (\<Sum>j<D. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes mult_repr:
    "\<And>u t j. u < m * n \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow>
      gs_system_mat d m n q $$ (u,t) * basis j = (\<Sum>k<D. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < m * n \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow> abs (C u t k j) \<le> Bnd"
  obtains v :: "complex vec" and x :: "int vec" where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_system_mat d m n q *\<^sub>v v = 0\<^sub>v (m * n)"
    and "\<forall>i<q * q. algebraic_int (v $ i)"
    and "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and "x \<in> carrier_vec (q * q * D)"
    and "x \<noteq> 0\<^sub>v (q * q * D)"
    and "x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd))"
proof -
  obtain v :: "complex vec" and x :: "int vec" where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and ker: "gs_system_mat d m n q *\<^sub>v v = 0\<^sub>v (m * n)"
    and repr: "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and x_bnd: "x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd))"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants[OF gs_system_mat_carrier dpos mnq mult_repr C_bnd basis_indep])
  have vint: "\<forall>i<q * q. algebraic_int (v $ i)"
  proof
    fix i
    show "i < q * q \<longrightarrow> algebraic_int (v $ i)"
    proof
      assume i: "i < q * q"
      have sum_int: "algebraic_int (\<Sum>j<D. of_int (x $ sg_pair_idx D i j) * basis j)"
      proof (rule algebraic_int_sum)
        fix j
        assume j: "j \<in> {..<D}"
        have "algebraic_int (of_int (x $ sg_pair_idx D i j))"
          by simp
        moreover have "algebraic_int (basis j)"
          using basis_int j by simp
        ultimately show "algebraic_int (of_int (x $ sg_pair_idx D i j) * basis j)"
          by (rule algebraic_int_times)
      qed
      show "algebraic_int (v $ i)"
        using repr i sum_int by simp
    qed
  qed
  show thesis
    by (rule that[OF v_carrier v_nz ker vint repr x_carrier x_nz x_bnd])
qed

theorem gs_system_mat_exists_bounded_algebraic_int_kernel_linear:

  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes dpos: "D > 0"
  assumes mnpos: "m * n > 0"
  assumes mnq: "2 * (m * n) \<le> q * q"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j)"
  assumes basis_indep: "\<And>c. (\<Sum>j<D. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes mult_repr:
    "\<And>u t j. u < m * n \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow>
      gs_system_mat d m n q $$ (u,t) * basis j = (\<Sum>k<D. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < m * n \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow> abs (C u t k j) \<le> Bnd"
  obtains v :: "complex vec" and x :: "int vec" where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_system_mat d m n q *\<^sub>v v = 0\<^sub>v (m * n)"
    and "\<forall>i<q * q. algebraic_int (v $ i)"
    and "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and "x \<in> carrier_vec (q * q * D)"
    and "x \<noteq> 0\<^sub>v (q * q * D)"
    and "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd)"
proof -
  obtain v :: "complex vec" and x :: "int vec" where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and ker: "gs_system_mat d m n q *\<^sub>v v = 0\<^sub>v (m * n)"
    and repr: "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd)"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants_linear[OF gs_system_mat_carrier mnpos dpos mnq mult_repr C_bnd basis_indep])
  have vint: "\<forall>i<q * q. algebraic_int (v $ i)"
  proof
    fix i
    show "i < q * q \<longrightarrow> algebraic_int (v $ i)"
    proof
      assume i: "i < q * q"
      have sum_int: "algebraic_int (\<Sum>j<D. of_int (x $ sg_pair_idx D i j) * basis j)"
      proof (rule algebraic_int_sum)
        fix j
        assume j: "j \<in> {..<D}"
        have "algebraic_int (of_int (x $ sg_pair_idx D i j))"
          by simp
        moreover have "algebraic_int (basis j)"
          using basis_int j by simp
        ultimately show "algebraic_int (of_int (x $ sg_pair_idx D i j) * basis j)"
          by (rule algebraic_int_times)
      qed
      show "algebraic_int (v $ i)"
        using repr i sum_int by simp
    qed
  qed
  show thesis
    by (rule that[OF v_carrier v_nz ker vint repr x_carrier x_nz x_bnd])
qed

section \<open>Direct Auxiliary Witness Data\<close>

theorem gs_exists_integral_auxiliary_data:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  obtains v :: "complex vec" and r where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
    and "gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t) \<ge> gs_n h q"
    and "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
    and "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
proof -
  have qsq: "q ^ 2 = 2 * gs_m h * gs_n h q"
    by (rule gs_q_sq_eq_two_mn[OF dvd])
  have mnq: "gs_m h * gs_n h q < q * q"
  proof -
    have pos: "gs_m h * gs_n h q > 0"
      using npos by simp
    have "gs_m h * gs_n h q < 2 * (gs_m h * gs_n h q)"
      using pos by linarith
    also have "\<dots> = q ^ 2"
      using qsq by simp
    also have "\<dots> = q * q"
      by (simp add: power2_eq_square)
    finally show ?thesis .
  qed
  have algA: "algebraic_mat (gs_system_mat d (gs_m h) (gs_n h q) q)"
    by (rule gs_system_mat_algebraic[OF d])
  obtain v :: "complex vec" where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and v_ker: "gs_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
    using exists_nonzero_algebraic_int_kernel_vec_rectangular[OF gs_system_mat_carrier mnq algA]
    by blast
  have coeff_nz: "\<exists>t<q * q. Matrix.vec_index v t \<noteq> 0"
    using v_carrier v_nz by force
  have min_ord: "gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t) \<ge> gs_n h q"
  proof -
    have ker: "gs_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v gs_coeff_vec q (\<lambda>t. Matrix.vec_index v t) =
        0\<^sub>v (gs_m h * gs_n h q)"
      by (simp add: gs_coeff_vec_eqI[OF v_carrier] v_ker)
    show ?thesis
      by (rule gs_min_order_ge_of_kernel_nonzero[OF d qpos gs_m_pos npos coeff_nz ker])
  qed
  define r0 where "r0 = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  have deriv_nz:
      "((deriv ^^ r0) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
    unfolding r0_def
    by (rule gs_min_order_deriv_nonzero_of_coeff_nonzero[OF d qpos coeff_nz])
  show thesis
    by (rule that[OF v_carrier v_nz v_ker vint min_ord]) (use r0_def deriv_nz in auto)
qed

theorem gs_exists_bounded_integral_auxiliary_data:

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
      gs_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * basis j =
        (\<Sum>k<D. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow> abs (C u t k j) \<le> Bnd"
  obtains v :: "complex vec" and x :: "int vec" and r where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and "\<forall>i<q * q. algebraic_int (v $ i)"
    and "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and "x \<in> carrier_vec (q * q * D)"
    and "x \<noteq> 0\<^sub>v (q * q * D)"
    and "x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd))"
    and "gs_min_order (gs_m h) d q (\<lambda>t. v $ t) \<ge> gs_n h q"
    and "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t))"
    and "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)) \<noteq> 0"
proof -
  have qsq: "q ^ 2 = 2 * gs_m h * gs_n h q"
    by (rule gs_q_sq_eq_two_mn[OF dvd])
  have mnq: "gs_m h * gs_n h q < q * q"
  proof -
    have pos: "gs_m h * gs_n h q > 0"
      using npos by simp
    have "gs_m h * gs_n h q < 2 * (gs_m h * gs_n h q)"
      using pos by linarith
    also have "\<dots> = q ^ 2"
      using qsq by simp
    also have "\<dots> = q * q"
      by (simp add: power2_eq_square)
    finally show ?thesis .
  qed
  obtain v :: "complex vec" and x :: "int vec" where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and v_ker: "gs_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>i<q * q. algebraic_int (v $ i)"
    and repr: "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd))"
    by (rule gs_system_mat_exists_bounded_algebraic_int_kernel[OF Dpos mnq basis_int basis_indep mult_repr C_bnd])
  have coeff_nz: "\<exists>t<q * q. v $ t \<noteq> 0"
    using v_carrier v_nz by force
  have min_ord: "gs_min_order (gs_m h) d q (\<lambda>t. v $ t) \<ge> gs_n h q"
  proof -
    have ker: "gs_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v gs_coeff_vec q (\<lambda>t. v $ t) =
        0\<^sub>v (gs_m h * gs_n h q)"
      by (simp add: gs_coeff_vec_eqI[OF v_carrier] v_ker)
    show ?thesis
      by (rule gs_min_order_ge_of_kernel_nonzero[OF d qpos gs_m_pos npos coeff_nz ker])
  qed
  define r0 where "r0 = nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t))"
  have deriv_nz:
      "((deriv ^^ r0) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)) \<noteq> 0"
    unfolding r0_def
    by (rule gs_min_order_deriv_nonzero_of_coeff_nonzero[OF d qpos coeff_nz])
  show thesis
    by (rule that[OF v_carrier v_nz v_ker vint repr x_carrier x_nz x_bnd min_ord])
       (use r0_def deriv_nz in auto)
qed

theorem gs_exists_bounded_integral_auxiliary_data_linear:

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
      gs_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * basis j =
        (\<Sum>k<D. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow> abs (C u t k j) \<le> Bnd"
  obtains v :: "complex vec" and x :: "int vec" and r where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and "\<forall>i<q * q. algebraic_int (v $ i)"
    and "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and "x \<in> carrier_vec (q * q * D)"
    and "x \<noteq> 0\<^sub>v (q * q * D)"
    and "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd)"
    and "gs_min_order (gs_m h) d q (\<lambda>t. v $ t) \<ge> gs_n h q"
    and "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t))"
    and "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)) \<noteq> 0"
proof -
  have qsq: "q ^ 2 = 2 * gs_m h * gs_n h q"
    by (rule gs_q_sq_eq_two_mn[OF dvd])
  have mnpos: "gs_m h * gs_n h q > 0"
    using npos by simp
  have mnq: "2 * (gs_m h * gs_n h q) \<le> q * q"
    using qsq by (simp add: power2_eq_square)
  obtain v :: "complex vec" and x :: "int vec" where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and v_ker: "gs_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>i<q * q. algebraic_int (v $ i)"
    and repr: "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd)"
    by (rule gs_system_mat_exists_bounded_algebraic_int_kernel_linear[OF Dpos mnpos mnq basis_int basis_indep mult_repr C_bnd])
  have coeff_nz: "\<exists>t<q * q. v $ t \<noteq> 0"
    using v_carrier v_nz by force
  have min_ord: "gs_min_order (gs_m h) d q (\<lambda>t. v $ t) \<ge> gs_n h q"
  proof -
    have ker: "gs_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v gs_coeff_vec q (\<lambda>t. v $ t) =
        0\<^sub>v (gs_m h * gs_n h q)"
      by (simp add: gs_coeff_vec_eqI[OF v_carrier] v_ker)
    show ?thesis
      by (rule gs_min_order_ge_of_kernel_nonzero[OF d qpos gs_m_pos npos coeff_nz ker])
  qed
  define r0 where "r0 = nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t))"
  have deriv_nz:
      "((deriv ^^ r0) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)) \<noteq> 0"
    unfolding r0_def
    by (rule gs_min_order_deriv_nonzero_of_coeff_nonzero[OF d qpos coeff_nz])
  show thesis
    by (rule that[OF v_carrier v_nz v_ker vint repr x_carrier x_nz x_bnd min_ord])
       (use r0_def deriv_nz in auto)
qed

end
