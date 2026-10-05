(*  Title:      Baker/Gelfond_Schneider_Number_Field_Norm_Target.thy
    Author:     OpenAI Codex

Concrete number-field packaging of the generic rho-norm contradiction route.
This is the wrapper layer that matches the Lean `use6and8`/`use5` estimates.
*)

theory Gelfond_Schneider_Number_Field_Norm_Target
  imports
    Gelfond_Schneider_Direct_Target
    Gelfond_Schneider_Embedding_Norm_Indexed
begin

locale gelfond_schneider_number_field_norm_target =
  finite_embedding_indexed_recovery E D emb basis repr_coeff
  for E :: "'e set"
  and D :: nat
  and emb :: "nat \<Rightarrow> 'e"
  and basis :: "nat \<Rightarrow> 'e \<Rightarrow> complex"
  and repr_coeff :: "nat \<Rightarrow> 'e \<Rightarrow> complex" +
  fixes \<theta> :: complex
  fixes ca cb cw :: "nat \<Rightarrow> complex"
  fixes d
  fixes q h e0 Aemb C R A K
  fixes rho_norm :: "complex \<Rightarrow> real"
  fixes c5 c14
  assumes d: "is_gelfond_schneider_data d"
  assumes D_def: "D = ext_degree (\<rat> :: complex set) \<theta>"
  assumes Dpos: "D > 0"
  assumes ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
  assumes a_eq: "gs_a d = (\<Sum>i<D. ca i * \<theta> ^ i)"
  assumes cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
  assumes b_eq: "gs_b d = (\<Sum>i<D. cb i * \<theta> ^ i)"
  assumes cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
  assumes w_eq: "gs_w d = (\<Sum>i<D. cw i * \<theta> ^ i)"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
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
begin

theorem coordinate_contradiction:
  shows False
  by (rule no_gelfond_schneider_data_of_row_scaled_matrix_norm_bound_linear_indexed[where rho_norm = rho_norm,
        OF d qpos npos dvd Dpos e0 entry0 mult_repr inv_bound entry_bnd basis_int basis_indep
           basis_bound R_nonneg A_nonneg K_nonneg hpos q_def c14_ge1 c5_ge1 rho_pos rho_upper rho_inv_lt])

end

theorem no_gelfond_schneider_data_of_number_field_norm_target_existence:
  assumes d: "is_gelfond_schneider_data d"
  assumes target:
    "\<And>\<theta> D ca cb cw.
      D = ext_degree (\<rat> :: complex set) \<theta> \<Longrightarrow>
      D > 0 \<Longrightarrow>
      (\<forall>i<D. ca i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_a d = (\<Sum>i<D. ca i * \<theta> ^ i) \<Longrightarrow>
      (\<forall>i<D. cb i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_b d = (\<Sum>i<D. cb i * \<theta> ^ i) \<Longrightarrow>
      (\<forall>i<D. cw i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_w d = (\<Sum>i<D. cw i * \<theta> ^ i) \<Longrightarrow>
      (\<exists>E emb basis repr_coeff q h e0 Aemb C R A K rho_norm c5 c14.
        gelfond_schneider_number_field_norm_target E D emb basis repr_coeff \<theta> ca cb cw d q h e0 Aemb C R A K rho_norm c5 c14)"
  shows False
proof (rule no_gelfond_schneider_data_of_coordinate_contradiction[OF d])
  fix \<theta> D ca cb cw
  assume D_def: "D = ext_degree (\<rat> :: complex set) \<theta>"
  assume Dpos: "D > 0"
  assume ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
  assume a_eq: "gs_a d = (\<Sum>i<D. ca i * \<theta> ^ i)"
  assume cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
  assume b_eq: "gs_b d = (\<Sum>i<D. cb i * \<theta> ^ i)"
  assume cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
  assume w_eq: "gs_w d = (\<Sum>i<D. cw i * \<theta> ^ i)"
  from target[OF D_def Dpos ca_rat a_eq cb_rat b_eq cw_rat w_eq]
  obtain E emb basis repr_coeff q h e0 Aemb C R A K rho_norm c5 c14 where
    T: "gelfond_schneider_number_field_norm_target E D emb basis repr_coeff \<theta> ca cb cw d q h e0 Aemb C R A K rho_norm c5 c14"
    by (meson gelfond_schneider_number_field_norm_target.coordinate_contradiction)
  interpret T: gelfond_schneider_number_field_norm_target
    E D emb basis repr_coeff \<theta> ca cb cw d q h e0 Aemb C R A K rho_norm c5 c14
    by (rule T)
  show False
    by (rule T.coordinate_contradiction)
qed

theorem gelfond_schneider_of_number_field_norm_target_existence:
  fixes a b w :: complex
  assumes target:
    "\<And>d \<theta> D ca cb cw.
      is_gelfond_schneider_data d \<Longrightarrow>
      D = ext_degree (\<rat> :: complex set) \<theta> \<Longrightarrow>
      D > 0 \<Longrightarrow>
      (\<forall>i<D. ca i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_a d = (\<Sum>i<D. ca i * \<theta> ^ i) \<Longrightarrow>
      (\<forall>i<D. cb i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_b d = (\<Sum>i<D. cb i * \<theta> ^ i) \<Longrightarrow>
      (\<forall>i<D. cw i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_w d = (\<Sum>i<D. cw i * \<theta> ^ i) \<Longrightarrow>
      (\<exists>E emb basis repr_coeff q h e0 Aemb C R A K rho_norm c5 c14.
        gelfond_schneider_number_field_norm_target E D emb basis repr_coeff \<theta> ca cb cw d q h e0 Aemb C R A K rho_norm c5 c14)"
  assumes "algebraic a"
  assumes "algebraic b"
  assumes "a \<noteq> 0"
  assumes "a \<noteq> 1"
  assumes "b \<notin> \<rat>"
  assumes "w \<in> power_values a b"
  shows "\<not> algebraic w"
proof (rule gelfond_schneider_of_coordinate_contradiction)
  fix d \<theta> D ca cb cw
  assume d: "is_gelfond_schneider_data d"
  assume D_def: "D = ext_degree (\<rat> :: complex set) \<theta>"
  assume Dpos: "D > 0"
  assume ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
  assume a_eq: "gs_a d = (\<Sum>i<D. ca i * \<theta> ^ i)"
  assume cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
  assume b_eq: "gs_b d = (\<Sum>i<D. cb i * \<theta> ^ i)"
  assume cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
  assume w_eq: "gs_w d = (\<Sum>i<D. cw i * \<theta> ^ i)"
  from target[OF d D_def Dpos ca_rat a_eq cb_rat b_eq cw_rat w_eq]
  obtain E emb basis repr_coeff q h e0 Aemb C R A K rho_norm c5 c14 where
    T: "gelfond_schneider_number_field_norm_target E D emb basis repr_coeff \<theta> ca cb cw d q h e0 Aemb C R A K rho_norm c5 c14"
    by (meson gelfond_schneider_number_field_norm_target.coordinate_contradiction)
  interpret T: gelfond_schneider_number_field_norm_target
    E D emb basis repr_coeff \<theta> ca cb cw d q h e0 Aemb C R A K rho_norm c5 c14
    by (rule T)
  show False
    by (rule T.coordinate_contradiction)
qed (use assms(2-) in auto)

end
