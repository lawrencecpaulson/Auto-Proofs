(*  Title:      Gelfond_Schneider/Gelfond_Schneider_Scaled_Bounded.thy
    Author:     OpenAI Codex

Bounded-kernel packaging for the row-scaled Gelfond-Schneider system matrix.
This mirrors the existing unscaled bounded-kernel route, but targets the
row-scaled coefficients that already match the arithmetic normalization.
*)

theory Gelfond_Schneider_Scaled_Bounded
  imports
    Gelfond_Schneider_Scaled_Matrix
    Gelfond_Schneider_Arithmetic
begin

section \<open>Bounded Kernel Coefficients for the Row-Scaled System\<close>

lemma cmod_repr_by_bounded_int_vec_le:
  fixes basis :: "nat \<Rightarrow> complex"
  assumes Dpos: "D > 0"
  assumes repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes tlt: "t < q * q"
  shows "cmod (Matrix.vec_index v t) \<le> ((of_int B :: real) * (\<Sum>j<D. cmod (basis j)))"
proof -
  have vt_repr: "Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)"
    using repr tlt by blast
  have term_le:
      "cmod (of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j) \<le>
        (of_int B :: real) * cmod (basis j)"
    if jlt: "j < D" for j
  proof -
    have idx_lt: "sg_pair_idx D t j < q * q * D"
      by (rule sg_pair_idx_lt[OF Dpos tlt jlt])
    have x_le: "abs (Matrix.vec_index x (sg_pair_idx D t j)) \<le> B"
      using x_bnd x_carrier idx_lt unfolding Bounded_vec_def by simp
    have x_nonneg: "0 \<le> cmod (basis j)"
      by simp
    have cast_le: "(of_int (abs (Matrix.vec_index x (sg_pair_idx D t j))) :: real) \<le> of_int B"
      using x_le by simp
    have "cmod (of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j) =
        (of_int (abs (Matrix.vec_index x (sg_pair_idx D t j))) :: real) * cmod (basis j)"
      by (simp add: norm_mult)
    also have "\<dots> \<le> (of_int B :: real) * cmod (basis j)"
      by (rule mult_right_mono[OF cast_le]) simp
    finally show ?thesis .
  qed
  have "cmod (Matrix.vec_index v t) =
      cmod (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)"
    by (simp add: vt_repr)
  also have "\<dots> \<le> (\<Sum>j<D. cmod (of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j))"
    by (rule sum_norm_le) simp
  also have "\<dots> \<le> (\<Sum>j<D. (of_int B :: real) * cmod (basis j))"
    by (rule sum_mono) (simp add: term_le)
  also have "\<dots> = (of_int B :: real) * (\<Sum>j<D. cmod (basis j))"
    by (simp add: sum_distrib_left)
  finally show ?thesis .
qed

lemma cmod_repr_by_bounded_int_vec_uniform_le:
  fixes basis :: "nat \<Rightarrow> complex"
  assumes Dpos: "D > 0"
  assumes repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes basis_bnd: "\<And>j. j < D \<Longrightarrow> cmod (basis j) \<le> K"
  assumes tlt: "t < q * q"
  shows "cmod (Matrix.vec_index v t) \<le> ((of_int B :: real) * of_nat D * K)"
proof -
  have coeff_le: "cmod (Matrix.vec_index v t) \<le> (of_int B :: real) * (\<Sum>j<D. cmod (basis j))"
    by (rule cmod_repr_by_bounded_int_vec_le[OF Dpos repr x_carrier x_bnd B_nonneg tlt])
  also have "\<dots> \<le> (of_int B :: real) * (\<Sum>j<D. K)"
  proof (intro mult_left_mono)
    show "(\<Sum>j<D. cmod (basis j)) \<le> (\<Sum>j<D. K)"
      by (rule sum_mono) (simp add: basis_bnd)
  qed (use B_nonneg in simp)
  also have "\<dots> = (of_int B :: real) * of_nat D * K"
    by simp
  finally show ?thesis .
qed

lemma gs_bounded_vec_min_order_derivative_bound:
  fixes basis :: "nat \<Rightarrow> complex"
  fixes K :: real
  assumes qge: "4 \<le> q"
  assumes bal: "q * q = 2 * m * n"
  assumes nle: "n \<le> r"
  assumes mpos: "m > 0"
  assumes rpos: "r > 0"
  assumes Dpos: "D > 0"
  assumes repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j)"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes Knonneg: "0 \<le> K"
  assumes basis_bnd: "\<And>j. j < D \<Longrightarrow> cmod (basis j) \<le> K"
  assumes nz: "gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t) \<noteq> (\<lambda>_. 0)"
  assumes req: "r = nat (gs_min_order m d q (\<lambda>t. Matrix.vec_index v t))"
  shows "cmod (((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
      (gs_min_order_node m d q (\<lambda>t. Matrix.vec_index v t))) \<le>
    fact r * (of_nat (q * q) * ((of_int B :: real) * of_nat D * K) *
      exp ((of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)) *
        (of_nat m * (1 + of_nat r / of_nat q))) /
      (of_nat m * of_nat r / of_nat q) ^ (m * r)) *
      (2 * of_nat m + 1) ^ (m * r)"
proof -
  let ?V = "(of_int B :: real) * of_nat D * K"
  let ?T = "of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)"
  have qpos: "q > 0" using qge by simp
  have dgt: "1 < (of_nat m * of_nat r / of_nat q :: real)"
    by (rule gs_circle_clearance_of_balanced_dimensions[OF qge bal nle])
  have Vnonneg: "0 \<le> ?V"
    using B_nonneg Knonneg by simp
  have Tnonneg: "0 \<le> ?T" by simp
  have coeff: "\<And>t. t < q * q \<Longrightarrow> cmod (Matrix.vec_index v t) \<le> ?V"
    by (rule cmod_repr_by_bounded_int_vec_uniform_le[OF Dpos repr x_carrier x_bnd B_nonneg basis_bnd])
  have rho: "\<And>t. t < q * q \<Longrightarrow> cmod (gs_rho_idx d q t) \<le> ?T"
    by (rule gs_rho_idx_cmod_le[OF qpos])
  show ?thesis
    by (rule gs_aux_fun_vec_min_order_derivative_bound[OF qpos mpos rpos dgt Vnonneg Tnonneg nz req coeff rho])
qed

section \<open>Elementary Upper Bounds\<close>

lemma cmod_gs_system_coeff_le_uniform:
  assumes aq: "a \<le> q"
  assumes bq: "b \<le> q"
  assumes lm: "l \<le> m"
  shows "cmod (gs_system_coeff d a b l k) \<le>
    (of_nat q * (1 + cmod (gs_b d))) ^ k *
    (max 1 (cmod (gs_a d))) ^ (m * q) *
    (max 1 (cmod (gs_w d))) ^ (m * q)"
proof -
  let ?B = "of_nat q * (1 + cmod (gs_b d))"
  let ?A = "max 1 (cmod (gs_a d))"
  let ?W = "max 1 (cmod (gs_w d))"
  let ?ea = "a * l"
  let ?eb = "b * l"
  have aff_le: "cmod (gs_affine_coeff d a b) \<le> ?B"
    by (rule cmod_gs_affine_coeff_le[OF aq bq])
  have aff_pow_le: "cmod (gs_affine_coeff d a b) ^ k \<le> ?B ^ k"
    by (rule power_mono[OF aff_le]) auto
  have ea_le: "?ea \<le> m * q"
  proof -
    have "?ea \<le> q * l"
      using aq by simp
    also have "... \<le> q * m"
      using lm by simp
    finally show ?thesis
      by (simp add: mult.commute)
  qed
  have eb_le: "?eb \<le> m * q"
  proof -
    have "?eb \<le> q * l"
      using bq by simp
    also have "... \<le> q * m"
      using lm by simp
    finally show ?thesis
      by (simp add: mult.commute)
  qed
  have a_pow_le: "cmod (gs_a d) ^ ?ea \<le> ?A ^ (m * q)"
  proof -
    have "cmod (gs_a d) ^ ?ea \<le> ?A ^ ?ea"
      by (rule power_mono) auto
    also have "... \<le> ?A ^ (m * q)"
      by (rule power_increasing) (use ea_le in auto)
    finally show ?thesis .
  qed
  have w_pow_le: "cmod (gs_w d) ^ ?eb \<le> ?W ^ (m * q)"
  proof -
    have "cmod (gs_w d) ^ ?eb \<le> ?W ^ ?eb"
      by (rule power_mono) auto
    also have "... \<le> ?W ^ (m * q)"
      by (rule power_increasing) (use eb_le in auto)
    finally show ?thesis .
  qed
  have eq_term:
      "gs_system_coeff d a b l k =
        gs_affine_coeff d a b ^ k * gs_a d ^ ?ea * gs_w d ^ ?eb"
    unfolding gs_system_coeff_def by simp
  have "cmod (gs_system_coeff d a b l k) =
      cmod (gs_affine_coeff d a b) ^ k * cmod (gs_a d) ^ ?ea * cmod (gs_w d) ^ ?eb"
    by (simp add: eq_term norm_mult norm_power mult.assoc)
  also have "... \<le> ?B ^ k * ?A ^ (m * q) * ?W ^ (m * q)"
    using aff_pow_le a_pow_le w_pow_le by (intro mult_mono) auto
  finally show ?thesis .
qed

lemma cmod_scaled_gs_system_coeff_le_uniform:
  assumes aq: "a \<le> q"
  assumes bq: "b \<le> q"
  assumes lm: "l \<le> m"
  shows "cmod ((of_int c :: complex) * gs_system_coeff d a b l k) \<le>
    of_int (abs c) *
    (of_nat q * (1 + cmod (gs_b d))) ^ k *
    (max 1 (cmod (gs_a d))) ^ (m * q) *
    (max 1 (cmod (gs_w d))) ^ (m * q)"
proof -
  have "cmod ((of_int c :: complex) * gs_system_coeff d a b l k) =
      of_int (abs c) * cmod (gs_system_coeff d a b l k)"
    by (simp add: norm_mult)
  also have "... \<le> of_int (abs c) *
      ((of_nat q * (1 + cmod (gs_b d))) ^ k *
        (max 1 (cmod (gs_a d))) ^ (m * q) *
        (max 1 (cmod (gs_w d))) ^ (m * q))"
    by (intro mult_left_mono cmod_gs_system_coeff_le_uniform[OF aq bq lm]) auto
  finally show ?thesis by argo
qed

lemma cmod_scaled_deriv_at_nat_le_uniform:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes coeff_bnd: "\<forall>t<q * q. cmod (\<xi> t) \<le> V"
  assumes V_nonneg: "0 \<le> V"
  assumes lm: "l \<le> m"
  shows "cmod ((of_int c :: complex) *
      (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l))) \<le>
    of_nat (q * q) * V *
      (of_int (abs c) *
        (of_nat q * (1 + cmod (gs_b d))) ^ k *
        (max 1 (cmod (gs_a d))) ^ (m * q) *
        (max 1 (cmod (gs_w d))) ^ (m * q))"
proof -
  let ?U =
    "of_int (abs c) *
      (of_nat q * (1 + cmod (gs_b d))) ^ k *
      (max 1 (cmod (gs_a d))) ^ (m * q) *
      (max 1 (cmod (gs_w d))) ^ (m * q)"
  have sum_eq:
      "(of_int c :: complex) *
        (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l)) =
      (\<Sum>t<q * q. (of_int c :: complex) *
        (\<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k))"
    by (simp add: gs_aux_fun_vec_deriv_at_nat[OF d] sum_distrib_left algebra_simps)
  have term_le:
      "cmod ((of_int c :: complex) *
        (\<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)) \<le> V * ?U"
    if tlt: "t < q * q" for t
  proof -
    have xi_le: "cmod (\<xi> t) \<le> V"
      using coeff_bnd tlt by blast
    have coeff_le:
        "cmod ((of_int c :: complex) *
          gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k) \<le> ?U"
      by (rule cmod_scaled_gs_system_coeff_le_uniform[OF gs_a_idx_le[OF qpos tlt] gs_b_idx_le[OF qpos] lm])
    have "cmod ((of_int c :: complex) *
        (\<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)) =
        cmod (\<xi> t) *
        cmod ((of_int c :: complex) * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)"
      by (simp add: norm_mult algebra_simps)
    also have "... \<le> V * ?U"
      by (intro mult_mono xi_le coeff_le) (use V_nonneg in auto)
    finally show ?thesis .
  qed
  have "cmod ((of_int c :: complex) *
      (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l))) =
      cmod (\<Sum>t<q * q. (of_int c :: complex) *
        (\<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k))"
    by (simp add: sum_eq)
  also have "... \<le> (\<Sum>t<q * q. cmod ((of_int c :: complex) *
      (\<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)))"
    by (rule sum_norm_le) simp
  also have "... \<le> (\<Sum>t<q * q. V * ?U)"
  proof (rule sum_mono)
    fix t
    assume "t \<in> {..<q * q}"
    then show "cmod ((of_int c :: complex) * (\<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)) \<le> V * ?U"
      by (meson lessThan_iff term_le)
  qed
  also have "... = of_nat (q * q) * V * ?U"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem gs_row_scaled_system_mat_exists_bounded_algebraic_int_kernel:
  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes dpos: "D > 0"
  assumes mnq: "m * n < q * q"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j)"
  assumes basis_indep: "\<And>c. (\<Sum>j<D. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes mult_repr:
    "\<And>u t j. u < m * n \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow>
      gs_row_scaled_system_mat d m n q $$ (u,t) * basis j =
        (\<Sum>k<D. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < m * n \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow>
      abs (C u t k j) \<le> Bnd"
  obtains v :: "complex vec" and x :: "int vec" where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_row_scaled_system_mat d m n q *\<^sub>v v = 0\<^sub>v (m * n)"
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
    and ker: "gs_row_scaled_system_mat d m n q *\<^sub>v v = 0\<^sub>v (m * n)"
    and repr: "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and x_bnd: "x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd))"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants[OF gs_row_scaled_system_mat_carrier dpos mnq mult_repr C_bnd basis_indep])
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

theorem gs_row_scaled_system_mat_exists_bounded_algebraic_int_kernel_linear:
  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes dpos: "D > 0"
  assumes mnpos: "m * n > 0"
  assumes mnq: "2 * (m * n) \<le> q * q"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j)"
  assumes basis_indep: "\<And>c. (\<Sum>j<D. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes mult_repr:
    "\<And>u t j. u < m * n \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow>
      gs_row_scaled_system_mat d m n q $$ (u,t) * basis j =
        (\<Sum>k<D. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < m * n \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow>
      abs (C u t k j) \<le> Bnd"
  obtains v :: "complex vec" and x :: "int vec" where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_row_scaled_system_mat d m n q *\<^sub>v v = 0\<^sub>v (m * n)"
    and "\<forall>i<q * q. algebraic_int (v $ i)"
    and "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and "x \<in> carrier_vec (q * q * D)"
    and "x \<noteq> 0\<^sub>v (q * q * D)"
    and "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd)"
proof -
  obtain v :: "complex vec" and x :: "int vec" where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and ker: "gs_row_scaled_system_mat d m n q *\<^sub>v v = 0\<^sub>v (m * n)"
    and repr: "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and x_bnd: "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd)"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants_linear
          [OF gs_row_scaled_system_mat_carrier mnpos dpos mnq mult_repr C_bnd basis_indep])
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

theorem gs_exists_row_scaled_bounded_integral_auxiliary_data:
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
  obtains v :: "complex vec" and x :: "int vec" and r where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
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
    and v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>i<q * q. algebraic_int (v $ i)"
    and repr: "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd))"
    by (rule gs_row_scaled_system_mat_exists_bounded_algebraic_int_kernel[OF Dpos mnq basis_int basis_indep mult_repr C_bnd])
  have coeff_nz: "\<exists>t<q * q. v $ t \<noteq> 0"
    using v_carrier v_nz by force
  have min_ord: "gs_min_order (gs_m h) d q (\<lambda>t. v $ t) \<ge> gs_n h q"
  proof -
    have ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v gs_coeff_vec q (\<lambda>t. v $ t) =
        0\<^sub>v (gs_m h * gs_n h q)"
      by (simp add: gs_coeff_vec_eqI[OF v_carrier] v_ker)
    show ?thesis
      by (rule gs_min_order_ge_of_row_scaled_kernel_nonzero[OF d qpos gs_m_pos npos coeff_nz ker])
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

theorem gs_exists_row_scaled_bounded_integral_auxiliary_data_linear:
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
  obtains v :: "complex vec" and x :: "int vec" and r where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
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
    and v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>i<q * q. algebraic_int (v $ i)"
    and repr: "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd)"
    by (rule gs_row_scaled_system_mat_exists_bounded_algebraic_int_kernel_linear
          [OF Dpos mnpos mnq basis_int basis_indep mult_repr C_bnd])
  have coeff_nz: "\<exists>t<q * q. v $ t \<noteq> 0"
    using v_carrier v_nz by force
  have min_ord: "gs_min_order (gs_m h) d q (\<lambda>t. v $ t) \<ge> gs_n h q"
  proof -
    have ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v gs_coeff_vec q (\<lambda>t. v $ t) =
        0\<^sub>v (gs_m h * gs_n h q)"
      by (simp add: gs_coeff_vec_eqI[OF v_carrier] v_ker)
    show ?thesis
      by (rule gs_min_order_ge_of_row_scaled_kernel_nonzero[OF d qpos gs_m_pos npos coeff_nz ker])
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

theorem gs_exists_row_scaled_bounded_nonzero_algebraic_int_house_lower_bound:
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
  obtains v :: "complex vec" and x :: "int vec" and r and c and rho :: complex where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and "\<forall>i<q * q. algebraic_int (v $ i)"
    and "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and "x \<in> carrier_vec (q * q * D)"
    and "x \<noteq> 0\<^sub>v (q * q * D)"
    and "x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd))"
    and "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t))"
    and "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)) \<noteq> 0"
    and "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    and "rho = (of_int c :: complex) *
          (gs_z d powi (- int r) *
            ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
              (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)))"
    and "algebraic_int rho"
    and "rho \<noteq> 0"
    and "1 \<le> cmod rho * gs_house rho ^
          (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
proof -
  obtain v :: "complex vec" and x :: "int vec" and r where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>i<q * q. algebraic_int (v $ i)"
    and repr: "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd))"
    and min_ord: "gs_min_order (gs_m h) d q (\<lambda>t. v $ t) \<ge> gs_n h q"
    and r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t))"
    and deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)) \<noteq> 0"
    by (rule gs_exists_row_scaled_bounded_integral_auxiliary_data[OF d qpos npos dvd Dpos basis_int basis_indep mult_repr C_bnd])
  have coeff_nz: "\<exists>t<q * q. v $ t \<noteq> 0"
    using v_carrier v_nz by force
  define c :: int where "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
  have c_nz: "c \<noteq> 0"
    unfolding c_def using gelfond_schneider_data_c1_nonzero[OF d] by auto
  have rho_int:
      "algebraic_int
        ((of_int c :: complex) *
          (gs_z d powi (- int r) *
            ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
              (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t))))"
  proof -
    have "algebraic_int
        (of_int (gs_c1 d ^ nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t)) *
                 gs_c1 d ^ (2 * gs_m h * q)) *
          (gs_z d powi (- int (nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t)))) *
            ((deriv ^^ nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t)))
              (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
              (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t))))"
      by (rule gs_scaled_min_deriv_algebraic_int[OF d qpos gs_m_pos vint coeff_nz])
    then show ?thesis
      unfolding c_def using r_eq by simp
  qed
  have zfac_nz: "gs_z d powi (- int r) \<noteq> 0"
    using gelfond_schneider_data_z_nonzero[OF d] by (simp add: power_int_def)
  have scaled_nz:
      "(of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t))) \<noteq> 0"
    using c_nz zfac_nz deriv_nz by auto
  define rho :: complex where "rho = (of_int c :: complex) *
      (gs_z d powi (- int r) *
        ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)))"
  have rho_lb:
      "1 \<le> cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
    unfolding rho_def by (rule one_le_self_mul_house_pow_of_nonzero_algebraic_int[OF rho_int scaled_nz])
  show thesis
    by (rule that[OF v_carrier v_nz v_ker vint repr x_carrier x_nz x_bnd r_eq deriv_nz])
       (use c_def rho_def rho_int scaled_nz rho_lb in auto)
qed

theorem gs_exists_row_scaled_bounded_nonzero_algebraic_int_house_lower_bound_linear:
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
  obtains v :: "complex vec" and x :: "int vec" and r and c and rho :: complex where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and "\<forall>i<q * q. algebraic_int (v $ i)"
    and "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and "x \<in> carrier_vec (q * q * D)"
    and "x \<noteq> 0\<^sub>v (q * q * D)"
    and "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd)"
    and "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t))"
    and "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)) \<noteq> 0"
    and "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    and "rho = (of_int c :: complex) *
          (gs_z d powi (- int r) *
            ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
              (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)))"
    and "algebraic_int rho"
    and "rho \<noteq> 0"
    and "1 \<le> cmod rho * gs_house rho ^
          (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
proof -
  obtain v :: "complex vec" and x :: "int vec" and r where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>i<q * q. algebraic_int (v $ i)"
    and repr: "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd)"
    and min_ord: "gs_min_order (gs_m h) d q (\<lambda>t. v $ t) \<ge> gs_n h q"
    and r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t))"
    and deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)) \<noteq> 0"
    by (rule gs_exists_row_scaled_bounded_integral_auxiliary_data_linear
          [OF d qpos npos dvd Dpos basis_int basis_indep mult_repr C_bnd])
  have coeff_nz: "\<exists>t<q * q. v $ t \<noteq> 0"
    using v_carrier v_nz by force
  define c :: int where "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
  have c_nz: "c \<noteq> 0"
    unfolding c_def using gelfond_schneider_data_c1_nonzero[OF d] by auto
  have rho_int:
      "algebraic_int
        ((of_int c :: complex) *
          (gs_z d powi (- int r) *
            ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
              (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t))))"
  proof -
    have "algebraic_int
        (of_int (gs_c1 d ^ nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t)) *
                 gs_c1 d ^ (2 * gs_m h * q)) *
          (gs_z d powi (- int (nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t)))) *
            ((deriv ^^ nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t)))
              (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
              (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t))))"
      by (rule gs_scaled_min_deriv_algebraic_int[OF d qpos gs_m_pos vint coeff_nz])
    then show ?thesis
      unfolding c_def using r_eq by simp
  qed
  have zfac_nz: "gs_z d powi (- int r) \<noteq> 0"
    using gelfond_schneider_data_z_nonzero[OF d] by (simp add: power_int_def)
  have scaled_nz:
      "(of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t))) \<noteq> 0"
    using c_nz zfac_nz deriv_nz by auto
  define rho :: complex where "rho = (of_int c :: complex) *
      (gs_z d powi (- int r) *
        ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)))"
  have rho_lb:
      "1 \<le> cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
    unfolding rho_def by (rule one_le_self_mul_house_pow_of_nonzero_algebraic_int[OF rho_int scaled_nz])
  show thesis
    by (rule that[OF v_carrier v_nz v_ker vint repr x_carrier x_nz x_bnd r_eq deriv_nz])
       (use c_def rho_def rho_int scaled_nz rho_lb in auto)
qed

theorem gs_exists_row_scaled_bounded_nonzero_algebraic_int_cmod_upper_bound:
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
  obtains v :: "complex vec" and x :: "int vec" and r and c and rho :: complex where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and "\<forall>i<q * q. algebraic_int (v $ i)"
    and "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and "x \<in> carrier_vec (q * q * D)"
    and "x \<noteq> 0\<^sub>v (q * q * D)"
    and "x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd))"
    and "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t))"
    and "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)) \<noteq> 0"
    and "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    and "rho = (of_int c :: complex) *
          (gs_z d powi (- int r) *
            ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
              (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)))"
    and "algebraic_int rho"
    and "rho \<noteq> 0"
    and "cmod rho \<le>
          of_nat (q * q) *
          ((of_int (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)) :: real) *
            of_nat D * K) *
          (of_int (abs c) *
            (of_nat q * (1 + cmod (gs_b d))) ^ r *
            (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
            (max 1 (cmod (gs_w d))) ^ (gs_m h * q))"
proof -
  let ?X = "int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd)"
  obtain v :: "complex vec" and x :: "int vec" and r and c and rho :: complex where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>i<q * q. algebraic_int (v $ i)"
    and repr: "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec ?X"
    and r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t))"
    and deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)) \<noteq> 0"
    and c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    and rho_def:
      "rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)))"
    and rho_int: "algebraic_int rho"
    and rho_nz: "rho \<noteq> 0"
    and rho_lb:
      "1 \<le> cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
    by (rule gs_exists_row_scaled_bounded_nonzero_algebraic_int_house_lower_bound
          [OF d qpos npos dvd Dpos basis_int basis_indep mult_repr C_bnd])
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
      have le: "abs (x $ i) \<le> ?X"
        using x_bnd x_carrier ilt unfolding Bounded_vec_def by fastforce
      from le X_neg have "abs (x $ i) < 0"
        by linarith
      then show "x $ i = (0\<^sub>v (q * q * D)) $ i"
        by simp
    qed
    with x_nz show False
      by contradiction
  qed
  let ?V = "(of_int ?X :: real) * of_nat D * K"
  have V_nonneg: "0 \<le> ?V"
    using X_nonneg K_nonneg of_int_0_le_iff by blast
  have coeff_bnd: "\<forall>t<q * q. cmod (v $ t) \<le> ?V"
  proof
    fix t
    show "t < q * q \<longrightarrow> cmod (v $ t) \<le> ?V"
    proof
      assume tlt: "t < q * q"
      show "cmod (v $ t) \<le> ?V"
        by (rule cmod_repr_by_bounded_int_vec_uniform_le[OF Dpos repr x_carrier x_bnd X_nonneg basis_bnd tlt])
    qed
  qed
  obtain l where llt: "l < gs_m h"
    and node: "gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t) = of_nat (Suc l)"
    by (rule gs_min_order_node_eq_nat[OF gs_m_pos])
  have l_le_m: "Suc l \<le> gs_m h"
    using llt by simp
  have rho_ub:
      "cmod rho \<le> of_nat (q * q) * ?V *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))"
    unfolding rho_def node
    by (rule cmod_scaled_deriv_at_nat_le_uniform[OF d qpos coeff_bnd V_nonneg l_le_m])
  show thesis
    by (rule that[OF v_carrier v_nz v_ker vint repr x_carrier x_nz x_bnd r_eq deriv_nz c_def rho_def rho_int rho_nz])
       (use rho_ub in auto)
qed

theorem gs_exists_row_scaled_bounded_nonzero_algebraic_int_cmod_upper_bound_linear:
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
  obtains v :: "complex vec" and x :: "int vec" and r and c and rho :: complex where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and "\<forall>i<q * q. algebraic_int (v $ i)"
    and "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and "x \<in> carrier_vec (q * q * D)"
    and "x \<noteq> 0\<^sub>v (q * q * D)"
    and "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd)"
    and "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t))"
    and "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)) \<noteq> 0"
    and "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    and "rho = (of_int c :: complex) *
          (gs_z d powi (- int r) *
            ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
              (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)))"
    and "algebraic_int rho"
    and "rho \<noteq> 0"
    and "cmod rho \<le>
          of_nat (q * q) *
          ((of_int (2 * int (q * q * D) * max 1 Bnd) :: real) * of_nat D * K) *
          (of_int (abs c) *
            (of_nat q * (1 + cmod (gs_b d))) ^ r *
            (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
            (max 1 (cmod (gs_w d))) ^ (gs_m h * q))"
proof -
  let ?X = "2 * int (q * q * D) * max 1 Bnd"
  obtain v :: "complex vec" and x :: "int vec" and r and c and rho :: complex where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>i<q * q. algebraic_int (v $ i)"
    and repr: "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec ?X"
    and r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t))"
    and deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)) \<noteq> 0"
    and c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    and rho_def:
      "rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)))"
    and rho_int: "algebraic_int rho"
    and rho_nz: "rho \<noteq> 0"
    and rho_lb:
      "1 \<le> cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
    by (rule gs_exists_row_scaled_bounded_nonzero_algebraic_int_house_lower_bound_linear
          [OF d qpos npos dvd Dpos basis_int basis_indep mult_repr C_bnd])
  have X_nonneg: "0 \<le> ?X"
    using K_nonneg by simp
  let ?V = "(of_int ?X :: real) * of_nat D * K"
  have V_nonneg: "0 \<le> ?V"
    using X_nonneg K_nonneg of_int_0_le_iff by blast
  have coeff_bnd: "\<forall>t<q * q. cmod (v $ t) \<le> ?V"
  proof
    fix t
    show "t < q * q \<longrightarrow> cmod (v $ t) \<le> ?V"
    proof
      assume tlt: "t < q * q"
      show "cmod (v $ t) \<le> ?V"
        by (rule cmod_repr_by_bounded_int_vec_uniform_le[OF Dpos repr x_carrier x_bnd X_nonneg basis_bnd tlt])
    qed
  qed
  obtain l where llt: "l < gs_m h"
    and node: "gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t) = of_nat (Suc l)"
    by (rule gs_min_order_node_eq_nat[OF gs_m_pos])
  have l_le_m: "Suc l \<le> gs_m h"
    using llt by simp
  have rho_ub:
      "cmod rho \<le> of_nat (q * q) * ?V *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))"
    unfolding rho_def node
    by (rule cmod_scaled_deriv_at_nat_le_uniform[OF d qpos coeff_bnd V_nonneg l_le_m])
  show thesis
    by (rule that[OF v_carrier v_nz v_ker vint repr x_carrier x_nz x_bnd r_eq deriv_nz c_def rho_def rho_int rho_nz])
       (use rho_ub in auto)
qed

end
