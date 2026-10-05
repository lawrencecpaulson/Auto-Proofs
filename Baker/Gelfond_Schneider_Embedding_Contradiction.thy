(*  Title:      Baker/Gelfond_Schneider_Embedding_Contradiction.thy
    Author:     OpenAI Codex

Concrete contradiction packaging for the finite-embedding route. This turns
uniform ehouse bounds on the row-scaled matrix entries into the structure-
constant hypotheses required by the direct Gelfond-Schneider contradiction
theorem.
*)

theory Gelfond_Schneider_Embedding_Contradiction
  imports
    Gelfond_Schneider_Embedding_Siegel
    Gelfond_Schneider_Contradiction
begin

context finite_embedding_house
begin

theorem no_gelfond_schneider_data_of_row_scaled_ehouse_root_bound_linear:
  fixes basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes repr_coeff :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
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
  assumes recover:
    "\<And>c k. k < D \<Longrightarrow>
      (of_int (c k) :: complex) =
        (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<D. of_int (c j) * basis j e))"
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
    by (rule abs_int_structure_constant_ehouse_le[OF recover repr_bnd entry_bnd basis_bnd
          R_nonneg A_nonneg K_nonneg mult_repr])
  have basis_bnd0: "\<And>j. j < D \<Longrightarrow> cmod (basis j e0) \<le> K"
  proof -
    fix j
    assume jlt: "j < D"
    have "cmod (basis j e0) \<le> ehouse (basis j)"
      by (rule cmod_le_ehouse[OF e0])
    also have "... \<le> K"
      by (rule basis_bnd[OF jlt])
    finally show "cmod (basis j e0) \<le> K" .
  qed
  show False
    by (rule no_gelfond_schneider_data_of_row_scaled_uniform_root_bound_linear
          [OF d qpos npos dvd Dpos basis_int basis_indep mult_repr0 C_bnd basis_bnd0
            K_nonneg root_upper H_nonneg explicit_small])
qed

theorem no_gelfond_schneider_data_of_row_scaled_ehouse_house_bound_linear:
  fixes basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  fixes repr_coeff :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
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
  assumes recover:
    "\<And>c k. k < D \<Longrightarrow>
      (of_int (c k) :: complex) =
        (\<Sum>e\<in>E. repr_coeff k e * (\<Sum>j<D. of_int (c j) * basis j e))"
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
    by (rule abs_int_structure_constant_ehouse_le[OF recover repr_bnd entry_bnd basis_bnd
          R_nonneg A_nonneg K_nonneg mult_repr])
  have basis_bnd0: "\<And>j. j < D \<Longrightarrow> cmod (basis j e0) \<le> K"
  proof -
    fix j
    assume jlt: "j < D"
    have "cmod (basis j e0) \<le> ehouse (basis j)"
      by (rule cmod_le_ehouse[OF e0])
    also have "... \<le> K"
      by (rule basis_bnd[OF jlt])
    finally show "cmod (basis j e0) \<le> K" .
  qed
  show False
    by (rule no_gelfond_schneider_data_of_row_scaled_uniform_house_bound_linear
          [OF d qpos npos dvd Dpos basis_int basis_indep mult_repr0 C_bnd basis_bnd0
            K_nonneg house_upper H_nonneg explicit_small])
qed

end

end
