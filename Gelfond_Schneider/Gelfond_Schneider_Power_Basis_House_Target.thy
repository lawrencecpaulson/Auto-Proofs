(*  Title:      Gelfond_Schneider/Gelfond_Schneider_Power_Basis_House_Target.thy
    Author:     OpenAI Codex

Concrete packaging of the power-basis recovery and entry-bound layers into the
indexed number-field house contradiction interface. This is the version that
expects a direct house bound on the scaled derivative witness, which is often
closer to the analytic output than a root-by-root bound.
*)

theory Gelfond_Schneider_Power_Basis_House_Target
  imports
    Gelfond_Schneider_Power_Basis_Recovery
    Gelfond_Schneider_Power_Basis
    Gelfond_Schneider_Power_Basis_Inverse_Bounds
    Gelfond_Schneider_Number_Field_Target
begin

locale gelfond_schneider_power_basis_house_target =
  finite_normal_galois_power_basis K eta D emb
  for K :: "complex set"
  and eta :: complex
  and D :: nat
  and emb :: "nat \<Rightarrow> complex \<Rightarrow> complex" +
  fixes ca cb cw :: "nat \<Rightarrow> complex"
  fixes d
  fixes q h i0
  fixes Aemb :: "nat \<Rightarrow> nat \<Rightarrow> (complex \<Rightarrow> complex) \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  fixes R A H
  assumes d: "is_gelfond_schneider_data d"
  assumes ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
  assumes a_eq: "gs_a d = (\<Sum>i<D. ca i * eta ^ i)"
  assumes cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
  assumes b_eq: "gs_b d = (\<Sum>i<D. cb i * eta ^ i)"
  assumes cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
  assumes w_eq: "gs_w d = (\<Sum>i<D. cw i * eta ^ i)"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  assumes i0lt: "i0 < D"
  assumes entry0:
    "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) = Aemb u t (emb i0)"
  assumes mult_repr:
    "\<And>u t j e. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow> e \<in> E \<Longrightarrow>
      Aemb u t e * basis j e = (\<Sum>k<D. of_int (C u t k j) * basis k e)"
  assumes R_def: "R = power_basis_inverse_bound"
  assumes entry_bnd:
    "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> ehouse (Aemb u t) \<le> A"
  assumes A_nonneg: "0 \<le> A"
  assumes house_upper:
    "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 (ceiling (of_nat (card E) * R * A * power_basis_entry_bound))) \<Longrightarrow>
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
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 (ceiling (of_nat (card E) * R * A * power_basis_entry_bound))) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      (of_nat (q * q) *
        ((of_int (2 * int (q * q * D) * max 1 (ceiling (of_nat (card E) * R * A * power_basis_entry_bound))) :: real) *
          of_nat D * power_basis_entry_bound) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      H ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
begin

sublocale TARGET: gelfond_schneider_number_field_house_target
  E D emb basis repr_coeff eta ca cb cw d q h "emb i0" Aemb C R A power_basis_entry_bound H
proof unfold_locales
  show "is_gelfond_schneider_data d"
    by (rule d)
  show "D = ext_degree (\<rat> :: complex set) eta"
    by (rule D_def)
  show "D > 0"
    by (rule Dpos)
  show "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
    by (rule ca_rat)
  show "gs_a d = (\<Sum>i<D. ca i * eta ^ i)"
    by (rule a_eq)
  show "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
    by (rule cb_rat)
  show "gs_b d = (\<Sum>i<D. cb i * eta ^ i)"
    by (rule b_eq)
  show "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
    by (rule cw_rat)
  show "gs_w d = (\<Sum>i<D. cw i * eta ^ i)"
    by (rule w_eq)
  show "q > 0"
    by (rule qpos)
  show "gs_n h q > 0"
    by (rule npos)
  show "2 * gs_m h dvd q ^ 2"
    by (rule dvd)
  show "emb i0 \<in> E"
    using i0lt unfolding E_def by auto
  show "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) = Aemb u t (emb i0)"
    by (rule entry0)
  show "\<And>u t j e. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow> e \<in> E \<Longrightarrow>
      Aemb u t e * basis j e = (\<Sum>k<D. of_int (C u t k j) * basis k e)"
    by (rule mult_repr)
  show "\<And>k i. k < D \<Longrightarrow> i < D \<Longrightarrow> cmod (REC.inverse_basis_matrix_entry k i) \<le> R"
  proof -
    fix k i
    assume klt: "k < D"
    assume ilt: "i < D"
    have "cmod (REC.inverse_basis_matrix_entry k i) \<le> power_basis_inverse_bound"
      by (rule inverse_basis_matrix_entry_le_power_basis_inverse_bound[OF ilt klt])
    then show "cmod (REC.inverse_basis_matrix_entry k i) \<le> R"
      unfolding R_def by simp
  qed
  show "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> EH.ehouse (Aemb u t) \<le> A"
    using entry_bnd by simp
  show "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j (emb i0))"
    by (rule basis_algebraic_int_at_emb[OF i0lt])
  show "\<And>c. (\<Sum>j<D. of_int (c j) * basis j (emb i0)) = 0 \<Longrightarrow> \<forall>j<D. c j = 0"
    by (rule basis_indep_at_emb[OF i0lt])
  show "\<And>j i. j < D \<Longrightarrow> i < D \<Longrightarrow> cmod (REC.basis_matrix_entry i j) \<le> power_basis_entry_bound"
  proof -
    fix j i
    assume jlt: "j < D"
    assume ilt: "i < D"
    have "cmod (basis j (emb i)) \<le> power_basis_entry_bound"
      by (rule basis_cmod_le_power_basis_entry_bound[OF ilt jlt])
    then show "cmod (REC.basis_matrix_entry i j) \<le> power_basis_entry_bound"
      by (simp add: REC.basis_matrix_entry_def)
  qed
  show "0 \<le> R"
    unfolding R_def by simp
  show "0 \<le> A"
    by (rule A_nonneg)
  show "0 \<le> power_basis_entry_bound"
    by simp
  show "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 (ceiling (of_nat (card E) * R * A * power_basis_entry_bound))) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      gs_house rho \<le> H"
    by (rule house_upper)
  show "0 \<le> H"
    by (rule H_nonneg)
  show "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec (2 * int (q * q * D) * max 1 (ceiling (of_nat (card E) * R * A * power_basis_entry_bound))) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      (of_nat (q * q) *
        ((of_int (2 * int (q * q * D) * max 1 (ceiling (of_nat (card E) * R * A * power_basis_entry_bound))) :: real) *
          of_nat D * power_basis_entry_bound) *
        (of_int (abs c) *
          (of_nat q * (1 + cmod (gs_b d))) ^ r *
          (max 1 (cmod (gs_a d))) ^ (gs_m h * q) *
          (max 1 (cmod (gs_w d))) ^ (gs_m h * q))) *
      H ^ (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1) < 1"
    by (rule explicit_small)
qed

theorem coordinate_contradiction:
  shows False
  by (rule TARGET.coordinate_contradiction)

end




theorem no_gelfond_schneider_data_of_power_basis_house_target_existence:
  assumes d: "is_gelfond_schneider_data d"
  assumes target:
    "\<And>eta D ca cb cw.
      D = ext_degree (\<rat> :: complex set) eta \<Longrightarrow>
      D > 0 \<Longrightarrow>
      (\<forall>i<D. ca i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_a d = (\<Sum>i<D. ca i * eta ^ i) \<Longrightarrow>
      (\<forall>i<D. cb i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_b d = (\<Sum>i<D. cb i * eta ^ i) \<Longrightarrow>
      (\<forall>i<D. cw i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_w d = (\<Sum>i<D. cw i * eta ^ i) \<Longrightarrow>
      (\<exists>K emb q h i0 Aemb C R A H.
        gelfond_schneider_power_basis_house_target K eta D emb ca cb cw d q h i0 Aemb C R A H)"
  shows False
proof (rule no_gelfond_schneider_data_of_coordinate_contradiction[OF d])
  fix eta D ca cb cw
  assume D_def: "D = ext_degree (\<rat> :: complex set) eta"
  assume Dpos: "D > 0"
  assume ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
  assume a_eq: "gs_a d = (\<Sum>i<D. ca i * eta ^ i)"
  assume cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
  assume b_eq: "gs_b d = (\<Sum>i<D. cb i * eta ^ i)"
  assume cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
  assume w_eq: "gs_w d = (\<Sum>i<D. cw i * eta ^ i)"
  from target[OF D_def Dpos ca_rat a_eq cb_rat b_eq cw_rat w_eq]
  obtain K emb q h i0 Aemb C R A H where
    T: "gelfond_schneider_power_basis_house_target K eta D emb ca cb cw d q h i0 Aemb C R A H"
    by (meson gelfond_schneider_power_basis_house_target.coordinate_contradiction)
  interpret T: gelfond_schneider_power_basis_house_target
    K eta D emb ca cb cw d q h i0 Aemb C R A H
    by (rule T)
  show False
    by (rule T.coordinate_contradiction)
qed

theorem gelfond_schneider_of_power_basis_house_target_existence:
  fixes a b w :: complex
  assumes target:
    "\<And>d eta D ca cb cw.
      is_gelfond_schneider_data d \<Longrightarrow>
      D = ext_degree (\<rat> :: complex set) eta \<Longrightarrow>
      D > 0 \<Longrightarrow>
      (\<forall>i<D. ca i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_a d = (\<Sum>i<D. ca i * eta ^ i) \<Longrightarrow>
      (\<forall>i<D. cb i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_b d = (\<Sum>i<D. cb i * eta ^ i) \<Longrightarrow>
      (\<forall>i<D. cw i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_w d = (\<Sum>i<D. cw i * eta ^ i) \<Longrightarrow>
      (\<exists>K emb q h i0 Aemb C R A H.
        gelfond_schneider_power_basis_house_target K eta D emb ca cb cw d q h i0 Aemb C R A H)"
  assumes "algebraic a"
  assumes "algebraic b"
  assumes "a \<noteq> 0"
  assumes "a \<noteq> 1"
  assumes "b \<notin> \<rat>"
  assumes "w \<in> power_values a b"
  shows "\<not> algebraic w"
proof (rule gelfond_schneider_of_coordinate_contradiction)
  fix d eta D ca cb cw
  assume d: "is_gelfond_schneider_data d"
  assume D_def: "D = ext_degree (\<rat> :: complex set) eta"
  assume Dpos: "D > 0"
  assume ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
  assume a_eq: "gs_a d = (\<Sum>i<D. ca i * eta ^ i)"
  assume cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
  assume b_eq: "gs_b d = (\<Sum>i<D. cb i * eta ^ i)"
  assume cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
  assume w_eq: "gs_w d = (\<Sum>i<D. cw i * eta ^ i)"
  from target[OF d D_def Dpos ca_rat a_eq cb_rat b_eq cw_rat w_eq]
  obtain K emb q h i0 Aemb C R A H where
    T: "gelfond_schneider_power_basis_house_target K eta D emb ca cb cw d q h i0 Aemb C R A H"
    by (meson gelfond_schneider_power_basis_house_target.coordinate_contradiction)
  interpret T: gelfond_schneider_power_basis_house_target
    K eta D emb ca cb cw d q h i0 Aemb C R A H
    by (rule T)
  show False
    by (rule T.coordinate_contradiction)
qed (use assms(2-) in auto)

end
