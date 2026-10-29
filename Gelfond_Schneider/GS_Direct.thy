(*  Title:      Gelfond_Schneider/GS_Direct.thy
    Author:     OpenAI Codex

Direct packaging of the completed matrix/order part of the standalone
Gelfond-Schneider argument. This isolates the witness data that the remaining
arithmetic lower-bound / analytic upper-bound contradiction will consume,
following the structure of the Lean `MainAlgSetup`/`MainOrder` path rather
than the temporary two-logarithm detour.
*)

theory GS_Direct
  imports
    GS_Matrix
    "Finite_Embedding_Bounds.Structure_Constant_Kernels"

begin

section \<open>Bounded kernels for the Gelfond-Schneider system\<close>

lemma algebraic_int_coordinates_of_integral_basis:
  fixes basis :: "nat \<Rightarrow> complex"
    and v :: "complex vec"
    and x :: "int vec"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j)"
    and repr: "\<forall>t<q. v $ t =
      (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
  shows "\<forall>t<q. algebraic_int (v $ t)"
proof (intro allI impI)
  fix t
  assume tq: "t < q"
  have sum_int: "algebraic_int
    (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
  proof (rule algebraic_int_sum)
    fix j
    assume "j \<in> {..<D}"
    then show "algebraic_int (of_int (x $ sg_pair_idx D t j) * basis j)"
      by (intro algebraic_int_times) (auto intro: basis_int)
  qed
  show "algebraic_int (v $ t)"
    using repr tq sum_int by simp
qed

locale bounded_integral_basis_kernel = bounded_basis_kernel A p q D basis B v x
  for A :: "complex mat"
  and p q D :: nat
  and basis :: "nat \<Rightarrow> complex"
  and B :: int
  and v :: "complex vec"
  and x :: "int vec" +
  assumes v_integral: "\<forall>t<q. algebraic_int (v $ t)"

definition gs_bounded_auxiliary_witness ::
  "complex mat \<Rightarrow> gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (nat \<Rightarrow> complex) \<Rightarrow> int \<Rightarrow> complex vec \<Rightarrow> int vec \<Rightarrow> nat \<Rightarrow> bool"
  where
  "gs_bounded_auxiliary_witness A d h q D basis B v x r \<longleftrightarrow>
    bounded_integral_basis_kernel A (gs_m h * gs_n h q) (q * q) D basis B v x \<and>
    gs_min_order (gs_m h) d q (\<lambda>t. v $ t) \<ge> gs_n h q \<and>
    r = nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t)) \<and>
    ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
      (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)) \<noteq> 0"

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
    "\<And>u t k j. u < m * n \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow> \<bar>C u t k j\<bar> \<le> Bnd"
  obtains v :: "complex vec" and x :: "int vec" where
    "bounded_integral_basis_kernel (gs_system_mat d m n q) (m * n) (q * q) D
      basis (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) v x"
proof -
  obtain v :: "complex vec" and x :: "int vec" where
      W: "bounded_basis_kernel (gs_system_mat d m n q) (m * n) (q * q) D basis
        (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) v x"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants[OF gs_system_mat_carrier dpos mnq mult_repr C_bnd basis_indep])
  note v_carrier = bounded_basis_kernel.v_carrier[OF W]
    and v_nz = bounded_basis_kernel.v_nonzero[OF W]
    and x_carrier = bounded_basis_kernel.x_carrier[OF W]
    and x_nz = bounded_basis_kernel.x_nonzero[OF W]
    and ker = bounded_basis_kernel.kernel[OF W]
    and repr = bounded_basis_kernel.coordinates[OF W]
    and x_bnd = bounded_basis_kernel.x_bounded[OF W]
  have vint: "\<forall>i<q * q. algebraic_int (v $ i)"
    by (rule algebraic_int_coordinates_of_integral_basis[OF basis_int repr])
  have IW: "bounded_integral_basis_kernel (gs_system_mat d m n q) (m * n)
    (q * q) D basis
    (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) v x"
    by unfold_locales
      (use v_carrier v_nz ker vint repr x_carrier x_nz x_bnd in auto)
  show thesis by (rule that[OF IW])
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
    "\<And>u t k j. u < m * n \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow> \<bar>C u t k j\<bar> \<le> Bnd"
  obtains v :: "complex vec" and x :: "int vec" where
    "bounded_integral_basis_kernel (gs_system_mat d m n q) (m * n) (q * q) D
      basis (2 * int (q * q * D) * max 1 Bnd) v x"
proof -
  obtain v :: "complex vec" and x :: "int vec" where
      W: "bounded_basis_kernel (gs_system_mat d m n q) (m * n) (q * q) D basis
        (2 * int (q * q * D) * max 1 Bnd) v x"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants_linear[OF gs_system_mat_carrier mnpos dpos mnq mult_repr C_bnd basis_indep])
  note v_carrier = bounded_basis_kernel.v_carrier[OF W]
    and v_nz = bounded_basis_kernel.v_nonzero[OF W]
    and ker = bounded_basis_kernel.kernel[OF W]
    and repr = bounded_basis_kernel.coordinates[OF W]
    and x_carrier = bounded_basis_kernel.x_carrier[OF W]
    and x_nz = bounded_basis_kernel.x_nonzero[OF W]
    and x_bnd = bounded_basis_kernel.x_bounded[OF W]
  have vint: "\<forall>i<q * q. algebraic_int (v $ i)"
    by (rule algebraic_int_coordinates_of_integral_basis[OF basis_int repr])
  have IW: "bounded_integral_basis_kernel (gs_system_mat d m n q) (m * n)
    (q * q) D basis (2 * int (q * q * D) * max 1 Bnd) v x"
    by unfold_locales
      (use v_carrier v_nz ker vint repr x_carrier x_nz x_bnd in auto)
  show thesis by (rule that[OF IW])
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
  have mnq: "gs_m h * gs_n h q < q * q"
    by (rule gs_balanced_rows_lt_columns[OF dvd npos])
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

context
  fixes d :: gelfond_schneider_data
    and q h D :: nat
    and Bnd :: int
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
    "\<And>u t k j. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow> \<bar>C u t k j\<bar> \<le> Bnd"
begin

theorem gs_exists_bounded_integral_auxiliary_data:
  obtains v :: "complex vec" and x :: "int vec" and r where
    "gs_bounded_auxiliary_witness
      (gs_system_mat d (gs_m h) (gs_n h q) q) d h q D basis
      (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) v x r"
proof -
  have mnq: "gs_m h * gs_n h q < q * q"
    by (rule gs_balanced_rows_lt_columns[OF dvd npos])
  obtain v :: "complex vec" and x :: "int vec" where
      IW: "bounded_integral_basis_kernel
        (gs_system_mat d (gs_m h) (gs_n h q) q)
        (gs_m h * gs_n h q) (q * q) D basis
        (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) v x"
    by (rule gs_system_mat_exists_bounded_algebraic_int_kernel[OF Dpos mnq basis_int basis_indep mult_repr C_bnd])
  interpret W: bounded_integral_basis_kernel
    "gs_system_mat d (gs_m h) (gs_n h q) q"
    "gs_m h * gs_n h q" "q * q" D basis
    "int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)" v x
    by (rule IW)
  note v_carrier = W.v_carrier and v_nz = W.v_nonzero
    and v_ker = W.kernel
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
  have BW: "gs_bounded_auxiliary_witness
    (gs_system_mat d (gs_m h) (gs_n h q) q) d h q D basis
    (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) v x r0"
    using IW min_ord r0_def deriv_nz
    unfolding gs_bounded_auxiliary_witness_def by blast
  show thesis by (rule that[OF BW])
qed

theorem gs_exists_bounded_integral_auxiliary_data_linear:
  obtains v :: "complex vec" and x :: "int vec" and r where
    "gs_bounded_auxiliary_witness
      (gs_system_mat d (gs_m h) (gs_n h q) q) d h q D basis
      (2 * int (q * q * D) * max 1 Bnd) v x r"
proof -
  have qsq: "q ^ 2 = 2 * gs_m h * gs_n h q"
    by (rule gs_q_sq_eq_two_mn[OF dvd])
  have mnpos: "gs_m h * gs_n h q > 0"
    using npos by simp
  have mnq: "2 * (gs_m h * gs_n h q) \<le> q * q"
    using qsq by (simp add: power2_eq_square)
  obtain v :: "complex vec" and x :: "int vec" where
      IW: "bounded_integral_basis_kernel
        (gs_system_mat d (gs_m h) (gs_n h q) q)
        (gs_m h * gs_n h q) (q * q) D basis
        (2 * int (q * q * D) * max 1 Bnd) v x"
    by (rule gs_system_mat_exists_bounded_algebraic_int_kernel_linear[OF Dpos mnpos mnq basis_int basis_indep mult_repr C_bnd])
  interpret W: bounded_integral_basis_kernel
    "gs_system_mat d (gs_m h) (gs_n h q) q"
    "gs_m h * gs_n h q" "q * q" D basis
    "2 * int (q * q * D) * max 1 Bnd" v x
    by (rule IW)
  note v_carrier = W.v_carrier and v_nz = W.v_nonzero
    and v_ker = W.kernel
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
  have BW: "gs_bounded_auxiliary_witness
    (gs_system_mat d (gs_m h) (gs_n h q) q) d h q D basis
    (2 * int (q * q * D) * max 1 Bnd) v x r0"
    using IW min_ord r0_def deriv_nz
    unfolding gs_bounded_auxiliary_witness_def by blast
  show thesis by (rule that[OF BW])
qed

end

end
