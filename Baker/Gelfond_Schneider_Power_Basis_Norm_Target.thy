(*  Title:      Baker/Gelfond_Schneider_Power_Basis_Norm_Target.thy
    Author:     OpenAI Codex

Concrete packaging of the power-basis recovery layer into the generic
rho-norm contradiction interface. This is the power-basis wrapper that matches
Lean's `use6and8`/`use5` path.
*)

theory Gelfond_Schneider_Power_Basis_Norm_Target
  imports
    Gelfond_Schneider_Power_Basis_Recovery
    Gelfond_Schneider_Power_Basis_Bounds
    Gelfond_Schneider_Power_Basis_Inverse_Bounds
    Gelfond_Schneider_Power_Basis_Field_Norm
    Gelfond_Schneider_Number_Field_Norm_Target
begin

locale gelfond_schneider_power_basis_norm_target =
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
  fixes R A
  fixes rho_norm :: "complex \<Rightarrow> real"
  fixes c5 c14
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
      0 < rho_norm rho"
  assumes rho_upper:
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
      rho_norm rho \<le>
        c14 powr of_nat r *
        of_nat r powr ((- of_nat r / 2 + 3 * of_nat h / 2) :: real)"
  assumes rho_inv_lt:
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
      inverse (rho_norm rho) < c5 powr of_nat r"
begin

sublocale TARGET: gelfond_schneider_number_field_norm_target
  E D emb basis repr_coeff eta ca cb cw d q h "emb i0" Aemb C R A power_basis_entry_bound rho_norm c5 c14
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
  show "h > 0"
    by (rule hpos)
  show "q = gs_q_choice h (c14 * c5)"
    by (rule q_def)
  show "1 \<le> c14"
    by (rule c14_ge1)
  show "1 \<le> c5"
    by (rule c5_ge1)
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
      0 < rho_norm rho"
    by (rule rho_pos)
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
      rho_norm rho \<le> c14 powr of_nat r *
        of_nat r powr ((- of_nat r / 2 + 3 * of_nat h / 2) :: real)"
    by (rule rho_upper)
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
      inverse (rho_norm rho) < c5 powr of_nat r"
    by (rule rho_inv_lt)
qed

theorem coordinate_contradiction:
  shows False
  by (rule TARGET.coordinate_contradiction)

end

locale gelfond_schneider_power_basis_field_norm_estimates =
  finite_normal_galois_power_basis K eta D emb
  for K :: "complex set"
  and eta :: complex
  and D :: nat
  and emb :: "nat \<Rightarrow> complex \<Rightarrow> complex" +
  fixes ca cb cw :: "nat \<Rightarrow> complex"
  fixes d
  fixes q h i0
  fixes A c5 c14 :: real
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
  assumes emb0: "emb i0 = identity K"
  assumes entryK:
    "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) \<in> K"
  assumes hpos: "h > 0"
  assumes q_def: "q = gs_q_choice h (c14 * c5)"
  assumes c14_ge1: "1 \<le> c14"
  assumes c5_gt1: "1 < c5"
begin

definition Aemb :: "nat \<Rightarrow> nat \<Rightarrow> (complex \<Rightarrow> complex) \<Rightarrow> complex"
  where "Aemb u t e = e (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))"

lemma identity_apply_in_K:
  assumes xK: "x \<in> K"
  shows "identity K x = x"
proof -
  have id_auto: "identity K \<in> field_auto K (\<rat> :: complex set)"
    by (rule field_auto_identity[OF K_subfield Rats_subset_K])
  from id_auto xK show ?thesis
    by (auto simp: field_auto_mem_iff)
qed

lemma row_scaled_entry0:
  assumes up: "u < gs_m h * gs_n h q"
  assumes tq: "t < q * q"
  shows "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) = Aemb u t (emb i0)"
proof -
  have xK: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) \<in> K"
    by (rule entryK[OF up tq])
  have "Aemb u t (emb i0) = emb i0 (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))"
    by (simp add: Aemb_def)
  also have "... = gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t)"
    using xK by (simp add: emb0 identity_apply_in_K)
  finally show ?thesis
    by simp
qed

lemma a_in_K: "gs_a d \<in> K"
proof -
  have "(\<Sum>i<D. ca i * eta ^ i) \<in> K"
    by (rule sum_rat_power_in_K[OF ca_rat])
  then show ?thesis
    by (simp add: a_eq)
qed

lemma b_in_K: "gs_b d \<in> K"
proof -
  have "(\<Sum>i<D. cb i * eta ^ i) \<in> K"
    by (rule sum_rat_power_in_K[OF cb_rat])
  then show ?thesis
    by (simp add: b_eq)
qed

lemma w_in_K: "gs_w d \<in> K"
proof -
  have "(\<Sum>i<D. cw i * eta ^ i) \<in> K"
    by (rule sum_rat_power_in_K[OF cw_rat])
  then show ?thesis
    by (simp add: w_eq)
qed

lemma gs_affine_coeff_in_K:
  shows "gs_affine_coeff d a b \<in> K"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have aK: "(of_nat a :: complex) \<in> K"
  proof -
    have "(of_nat a :: complex) \<in> (\<rat> :: complex set)"
      by simp
    then show ?thesis
      using Rats_subset_K by blast
  qed
  have bK: "(of_nat b :: complex) \<in> K"
  proof -
    have "(of_nat b :: complex) \<in> (\<rat> :: complex set)"
      by simp
    then show ?thesis
      using Rats_subset_K by blast
  qed
  have bgK: "of_nat b * gs_b d \<in> K"
    by (rule KS.mult_closed[OF bK b_in_K])
  show ?thesis
    unfolding gs_affine_coeff_def
    by (rule KS.add_closed[OF aK bgK])
qed

lemma gs_affine_coeff_emb_cmod_le:
  assumes ilt: "i < D"
  assumes aq: "a \<le> q"
  assumes bq: "b \<le> q"
  shows "cmod (emb i (gs_affine_coeff d a b)) \<le>
    of_nat q * (1 + cmod (emb i (gs_b d)))"
proof -
  interpret KS: Subfield K by (rule K_subfield)
  have sigma: "emb i \<in> field_auto K (\<rat> :: complex set)"
    by (rule emb_in_field_auto[OF ilt])
  have aK: "(of_nat a :: complex) \<in> K"
    using Rats_subset_K by auto
  have bK: "(of_nat b :: complex) \<in> K"
    using Rats_subset_K by auto
  have bgK: "of_nat b * gs_b d \<in> K"
    by (rule KS.mult_closed[OF bK b_in_K])
  have afix: "emb i (of_nat a :: complex) = of_nat a"
    using sigma by (simp add: field_auto_mem_iff)
  have bfix: "emb i (of_nat b :: complex) = of_nat b"
    using sigma by (simp add: field_auto_mem_iff)
  have eq: "emb i (gs_affine_coeff d a b) = of_nat a + of_nat b * emb i (gs_b d)"
    unfolding gs_affine_coeff_def
    by (simp add: field_auto_add[OF sigma aK bgK]
        field_auto_mult[OF sigma bK b_in_K] afix bfix)
  have "cmod (emb i (gs_affine_coeff d a b)) \<le>
      cmod (of_nat a :: complex) + cmod (of_nat b * emb i (gs_b d))"
    unfolding eq by (rule norm_triangle_ineq)
  also have "... = of_nat a + of_nat b * cmod (emb i (gs_b d))"
    by (simp add: norm_mult)
  also have "... \<le> of_nat q + of_nat q * cmod (emb i (gs_b d))"
    using aq bq by (intro add_mono mult_right_mono) auto
  also have "... = of_nat q * (1 + cmod (emb i (gs_b d)))"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma gs_system_coeff_emb_cmod_le:
  assumes ilt: "i < D"
  assumes aq: "a \<le> q"
  assumes bq: "b \<le> q"
  shows "cmod (emb i (gs_system_coeff d a b l k)) \<le>
    (of_nat q * (1 + cmod (emb i (gs_b d)))) ^ k *
    cmod (emb i (gs_a d)) ^ (a * l) *
    cmod (emb i (gs_w d)) ^ (b * l)"
proof -
  interpret KS: Subfield K by (rule K_subfield)
  have sigma: "emb i \<in> field_auto K (\<rat> :: complex set)"
    by (rule emb_in_field_auto[OF ilt])
  have hom: "field_hom_on K (emb i)"
    by (rule field_auto_as_hom[OF K_subfield sigma])
  have affK: "gs_affine_coeff d a b ^ k \<in> K"
    by (rule KS.power_closed[OF gs_affine_coeff_in_K])
  have aPowK: "gs_a d ^ (a * l) \<in> K"
    by (rule KS.power_closed[OF a_in_K])
  have wPowK: "gs_w d ^ (b * l) \<in> K"
    by (rule KS.power_closed[OF w_in_K])
  have leftK: "gs_affine_coeff d a b ^ k * gs_a d ^ (a * l) \<in> K"
    by (rule KS.mult_closed[OF affK aPowK])
  have eq: "emb i (gs_system_coeff d a b l k) =
      emb i (gs_affine_coeff d a b) ^ k *
      emb i (gs_a d) ^ (a * l) * emb i (gs_w d) ^ (b * l)"
    unfolding gs_system_coeff_def
    by (simp add: field_auto_mult[OF sigma leftK wPowK]
        field_auto_mult[OF sigma affK aPowK]
        field_hom_on.hom_power[OF hom gs_affine_coeff_in_K]
        field_hom_on.hom_power[OF hom a_in_K]
        field_hom_on.hom_power[OF hom w_in_K])
  have affpow: "cmod (emb i (gs_affine_coeff d a b)) ^ k \<le>
      (of_nat q * (1 + cmod (emb i (gs_b d)))) ^ k"
    by (rule power_mono[OF gs_affine_coeff_emb_cmod_le[OF ilt aq bq]]) auto
  have "cmod (emb i (gs_system_coeff d a b l k)) =
      cmod (emb i (gs_affine_coeff d a b)) ^ k *
      cmod (emb i (gs_a d)) ^ (a * l) * cmod (emb i (gs_w d)) ^ (b * l)"
    by (simp add: eq norm_mult norm_power)
  also have "... \<le> (of_nat q * (1 + cmod (emb i (gs_b d)))) ^ k *
      cmod (emb i (gs_a d)) ^ (a * l) * cmod (emb i (gs_w d)) ^ (b * l)"
    using affpow by (intro mult_right_mono) auto
  finally show ?thesis .
qed

lemma gs_system_coeff_in_K:
  shows "gs_system_coeff d a b l k \<in> K"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have affK: "gs_affine_coeff d a b ^ k \<in> K"
    by (rule KS.power_closed[OF gs_affine_coeff_in_K])
  have aPowK: "gs_a d ^ (a * l) \<in> K"
    by (rule KS.power_closed[OF a_in_K])
  have wPowK: "gs_w d ^ (b * l) \<in> K"
    by (rule KS.power_closed[OF w_in_K])
  have leftK: "gs_affine_coeff d a b ^ k * gs_a d ^ (a * l) \<in> K"
    by (rule KS.mult_closed[OF affK aPowK])
  show ?thesis
    unfolding gs_system_coeff_def
    by (rule KS.mult_closed[OF leftK wPowK])
qed

lemma gs_row_scaled_entry_emb_cmod_le:
  assumes ilt: "i < D"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes ult: "u < gs_m h * gs_n h q"
  assumes tlt: "t < q * q"
  shows "cmod (emb i (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) \<le>
    abs (gs_row_scale d (gs_m h) (gs_n h q) q u) *
    (of_nat q * (1 + cmod (emb i (gs_b d)))) ^ gs_k_idx (gs_n h q) u *
    cmod (emb i (gs_a d)) ^ (gs_a_idx q t * gs_l_idx (gs_n h q) u) *
    cmod (emb i (gs_w d)) ^ (gs_b_idx q t * gs_l_idx (gs_n h q) u)"
proof -
  let ?c = "gs_row_scale d (gs_m h) (gs_n h q) q u"
  let ?s = "gs_system_coeff_idx d (gs_n h q) q u t"
  have sigma: "emb i \<in> field_auto K (\<rat> :: complex set)"
    by (rule emb_in_field_auto[OF ilt])
  have cK: "(of_int ?c :: complex) \<in> K"
    using Rats_subset_K by auto
  have sK: "?s \<in> K"
    unfolding gs_system_coeff_idx_def by (rule gs_system_coeff_in_K)
  have cfix: "emb i (of_int ?c :: complex) = of_int ?c"
    using sigma by (simp add: field_auto_mem_iff)
  have eq: "emb i (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t)) =
      of_int ?c * emb i ?s"
    using ult tlt
    by (simp add: gs_row_scaled_system_mat_def field_auto_mult[OF sigma cK sK] cfix)
  have ale: "gs_a_idx q t \<le> q"
    by (rule gs_a_idx_le[OF qpos tlt])
  have ble: "gs_b_idx q t \<le> q"
    by (rule gs_b_idx_le[OF qpos])
  have sbnd: "cmod (emb i ?s) \<le>
      (of_nat q * (1 + cmod (emb i (gs_b d)))) ^ gs_k_idx (gs_n h q) u *
      cmod (emb i (gs_a d)) ^ (gs_a_idx q t * gs_l_idx (gs_n h q) u) *
      cmod (emb i (gs_w d)) ^ (gs_b_idx q t * gs_l_idx (gs_n h q) u)"
    unfolding gs_system_coeff_idx_def
    by (rule gs_system_coeff_emb_cmod_le[OF ilt ale ble])
  have "cmod (emb i (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) =
      abs ?c * cmod (emb i ?s)"
    by (simp add: eq norm_mult)
  also have "... \<le> abs ?c *
      ((of_nat q * (1 + cmod (emb i (gs_b d)))) ^ gs_k_idx (gs_n h q) u *
      cmod (emb i (gs_a d)) ^ (gs_a_idx q t * gs_l_idx (gs_n h q) u) *
      cmod (emb i (gs_w d)) ^ (gs_b_idx q t * gs_l_idx (gs_n h q) u))"
    by (rule mult_left_mono[OF sbnd]) simp
  finally show ?thesis by (simp add: mult.assoc)
qed

lemma gs_scaled_deriv_emb_sum_bound:
  assumes ilt: "i < D"
  assumes coeffK: "\<And>t. t < q * q \<Longrightarrow> \<xi> t \<in> K"
  shows "cmod (emb i ((of_int c :: complex) *
    (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l)))) \<le>
    of_int (abs c) *
      (\<Sum>t<q * q. cmod (emb i (\<xi> t)) *
        cmod (emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)))"
proof -
  interpret KS: Subfield K by (rule K_subfield)
  have sigma: "emb i \<in> field_auto K (\<rat> :: complex set)"
    by (rule emb_in_field_auto[OF ilt])
  have hom: "field_hom_on K (emb i)"
    by (rule field_auto_as_hom[OF K_subfield sigma])
  have cK: "(of_int c :: complex) \<in> K"
    using Rats_subset_K by auto
  have termK: "\<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k \<in> K"
    if tlt: "t < q * q" for t
    by (rule KS.mult_closed[OF coeffK[OF tlt] gs_system_coeff_in_K])
  have sumK: "(\<Sum>t<q * q. \<xi> t *
      gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k) \<in> K"
    by (rule KS.sum_closed) (use termK in auto)
  have cfix: "emb i (of_int c :: complex) = of_int c"
    using sigma by (simp add: field_auto_mem_iff)
  have eq: "emb i ((of_int c :: complex) *
      (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l))) =
      of_int c * (\<Sum>t<q * q. emb i (\<xi> t) *
        emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k))"
  proof -
    have "emb i ((of_int c :: complex) *
      (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l))) =
        of_int c * emb i (\<Sum>t<q * q. \<xi> t *
          gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)"
      by (simp add: gs_aux_fun_vec_deriv_at_nat[OF d]
          field_auto_mult[OF sigma cK sumK] cfix)
    also have "... = of_int c * (\<Sum>t<q * q. emb i (\<xi> t *
        gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k))"
    proof -
      have homsum: "emb i (\<Sum>t<q * q. \<xi> t *
        gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k) =
        (\<Sum>t<q * q. emb i (\<xi> t *
          gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k))"
        by (rule field_hom_on.hom_sum[OF hom]) (use termK in auto)
      show ?thesis by (simp only: homsum)
    qed
    also have "... = of_int c * (\<Sum>t<q * q. emb i (\<xi> t) *
        emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k))"
      by (intro arg_cong[where f="(\<lambda>x::complex. of_int c * x)"] sum.cong)
         (auto intro: field_auto_mult[OF sigma coeffK gs_system_coeff_in_K])
    finally show ?thesis .
  qed
  have "cmod (emb i ((of_int c :: complex) *
    (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l)))) =
      of_int (abs c) * cmod (\<Sum>t<q * q. emb i (\<xi> t) *
        emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k))"
    by (simp add: eq norm_mult)
  also have "... \<le> of_int (abs c) * (\<Sum>t<q * q.
      cmod (emb i (\<xi> t) *
        emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)))"
    by (intro mult_left_mono sum_norm_le) auto
  also have "... = of_int (abs c) * (\<Sum>t<q * q. cmod (emb i (\<xi> t)) *
        cmod (emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)))"
    by (simp add: norm_mult)
  finally show ?thesis .
qed

lemma represented_coordinate_emb_cmod_le:
  assumes ilt: "i < D"
  assumes repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes tlt: "t < q * q"
  shows "cmod (emb i (Matrix.vec_index v t)) \<le>
    (of_int B :: real) * of_nat D * power_basis_entry_bound"
proof -
  let ?v' = "vec (q * q) (\<lambda>t. emb i (Matrix.vec_index v t))"
  have repr': "\<forall>t<q * q. Matrix.vec_index ?v' t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i))"
  proof (intro allI impI)
    fix t
    assume tlt: "t < q * q"
    have vt: "Matrix.vec_index v t =
      (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * eta ^ j)"
      using repr tlt by (simp add: basis_eq_power_at_identity_embedding[OF emb0])
    have "emb i (Matrix.vec_index v t) =
      (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i))"
      unfolding vt by (rule emb_sum_int_power[OF ilt])
    then show "Matrix.vec_index ?v' t =
      (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i))"
      using tlt by simp
  qed
  have basis_bnd: "\<And>j. j < D \<Longrightarrow> cmod (basis j (emb i)) \<le> power_basis_entry_bound"
    by (rule basis_cmod_le_power_basis_entry_bound[OF ilt])
  have "cmod (Matrix.vec_index ?v' t) \<le>
      (of_int B :: real) * of_nat D * power_basis_entry_bound"
    by (rule cmod_repr_by_bounded_int_vec_uniform_le[OF Dpos repr' x_carrier x_bnd B_nonneg basis_bnd tlt])
  then show ?thesis using tlt by simp
qed

lemma gs_scaled_deriv_emb_uniform_bound:
  fixes V U :: real
  assumes ilt: "i < D"
  assumes coeffK: "\<And>t. t < q * q \<Longrightarrow> \<xi> t \<in> K"
  assumes Vnonneg: "0 \<le> V"
  assumes Unonneg: "0 \<le> U"
  assumes coeff_bnd: "\<And>t. t < q * q \<Longrightarrow> cmod (emb i (\<xi> t)) \<le> V"
  assumes system_bnd: "\<And>t. t < q * q \<Longrightarrow>
    cmod (emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)) \<le> U"
  shows "cmod (emb i ((of_int c :: complex) *
    (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l)))) \<le>
    of_int (abs c) * of_nat (q * q) * V * U"
proof -
  have term_bnd: "cmod (emb i (\<xi> t)) *
      cmod (emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)) \<le> V * U"
    if tlt: "t < q * q" for t
    by (intro mult_mono coeff_bnd[OF tlt] system_bnd[OF tlt]) (use Vnonneg Unonneg in auto)
  have "cmod (emb i ((of_int c :: complex) *
    (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l)))) \<le>
      of_int (abs c) * (\<Sum>t<q * q. cmod (emb i (\<xi> t)) *
        cmod (emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)))"
    by (rule gs_scaled_deriv_emb_sum_bound[OF ilt coeffK])
  also have "... \<le> of_int (abs c) * (\<Sum>t<q * q. V * U)"
    by (intro mult_left_mono sum_mono term_bnd) auto
  also have "... = of_int (abs c) * of_nat (q * q) * V * U"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma gs_system_coeff_emb_uniform_le:
  fixes H :: real
  assumes ilt: "i < D"
  assumes aq: "a \<le> q"
  assumes bq: "b \<le> q"
  assumes lm: "l \<le> m"
  assumes Hone: "1 \<le> H"
  assumes aH: "cmod (emb i (gs_a d)) \<le> H"
  assumes bH: "cmod (emb i (gs_b d)) \<le> H"
  assumes wH: "cmod (emb i (gs_w d)) \<le> H"
  shows "cmod (emb i (gs_system_coeff d a b l k)) \<le>
    (of_nat q * (1 + H)) ^ k * H ^ (m * q) * H ^ (m * q)"
proof -
  let ?B = "of_nat q * (1 + H)"
  have ale: "a * l \<le> m * q"
  proof -
    have "a * l \<le> q * l" using aq by simp
    also have "... \<le> q * m" using lm by simp
    finally show ?thesis by (simp add: mult.commute)
  qed
  have ble: "b * l \<le> m * q"
  proof -
    have "b * l \<le> q * l" using bq by simp
    also have "... \<le> q * m" using lm by simp
    finally show ?thesis by (simp add: mult.commute)
  qed
  have Bbound: "of_nat q * (1 + cmod (emb i (gs_b d))) \<le> ?B"
    using bH by (intro mult_left_mono) auto
  have first: "(of_nat q * (1 + cmod (emb i (gs_b d)))) ^ k \<le> ?B ^ k"
    by (rule power_mono[OF Bbound]) auto
  have second: "cmod (emb i (gs_a d)) ^ (a * l) \<le> H ^ (m * q)"
  proof -
    have "cmod (emb i (gs_a d)) ^ (a * l) \<le> H ^ (a * l)"
      by (rule power_mono[OF aH]) auto
    also have "... \<le> H ^ (m * q)"
      by (rule power_increasing) (use Hone ale in auto)
    finally show ?thesis .
  qed
  have third: "cmod (emb i (gs_w d)) ^ (b * l) \<le> H ^ (m * q)"
  proof -
    have "cmod (emb i (gs_w d)) ^ (b * l) \<le> H ^ (b * l)"
      by (rule power_mono[OF wH]) auto
    also have "... \<le> H ^ (m * q)"
      by (rule power_increasing) (use Hone ble in auto)
    finally show ?thesis .
  qed
  have "cmod (emb i (gs_system_coeff d a b l k)) \<le>
      (of_nat q * (1 + cmod (emb i (gs_b d)))) ^ k *
      cmod (emb i (gs_a d)) ^ (a * l) * cmod (emb i (gs_w d)) ^ (b * l)"
    by (rule gs_system_coeff_emb_cmod_le[OF ilt aq bq])
  also have "... \<le> ?B ^ k * H ^ (m * q) * H ^ (m * q)"
    using first second third Hone by (intro mult_mono) auto
  finally show ?thesis .
qed

definition gs_data_emb_bound :: real where
  "gs_data_emb_bound = max 1
    (EH.ehouse (\<lambda>e. e (gs_a d)) +
     EH.ehouse (\<lambda>e. e (gs_b d)) +
     EH.ehouse (\<lambda>e. e (gs_w d)))"

lemma gs_data_emb_bound_facts:
  assumes ilt: "i < D"
  shows "1 \<le> gs_data_emb_bound"
    and "cmod (emb i (gs_a d)) \<le> gs_data_emb_bound"
    and "cmod (emb i (gs_b d)) \<le> gs_data_emb_bound"
    and "cmod (emb i (gs_w d)) \<le> gs_data_emb_bound"
proof -
  have eE: "emb i \<in> E"
    using ilt by (auto simp: E_def)
  have a_le: "cmod (emb i (gs_a d)) \<le> EH.ehouse (\<lambda>e. e (gs_a d))"
    by (rule EH.cmod_le_ehouse[OF eE])
  have b_le: "cmod (emb i (gs_b d)) \<le> EH.ehouse (\<lambda>e. e (gs_b d))"
    by (rule EH.cmod_le_ehouse[OF eE])
  have w_le: "cmod (emb i (gs_w d)) \<le> EH.ehouse (\<lambda>e. e (gs_w d))"
    by (rule EH.cmod_le_ehouse[OF eE])
  have a0: "0 \<le> EH.ehouse (\<lambda>e. e (gs_a d))" by simp
  have b0: "0 \<le> EH.ehouse (\<lambda>e. e (gs_b d))" by simp
  have w0: "0 \<le> EH.ehouse (\<lambda>e. e (gs_w d))" by simp
  have sum_le: "EH.ehouse (\<lambda>e. e (gs_a d)) +
      EH.ehouse (\<lambda>e. e (gs_b d)) +
      EH.ehouse (\<lambda>e. e (gs_w d)) \<le> gs_data_emb_bound"
    by (simp add: gs_data_emb_bound_def)
  show "1 \<le> gs_data_emb_bound"
    by (simp add: gs_data_emb_bound_def)
  show "cmod (emb i (gs_a d)) \<le> gs_data_emb_bound"
    using a_le b0 w0 sum_le by linarith
  show "cmod (emb i (gs_b d)) \<le> gs_data_emb_bound"
    using b_le a0 w0 sum_le by linarith
  show "cmod (emb i (gs_w d)) \<le> gs_data_emb_bound"
    using w_le a0 b0 sum_le by linarith
qed

lemma gs_system_coeff_emb_data_bound:
  assumes ilt: "i < D"
  assumes aq: "a \<le> q"
  assumes bq: "b \<le> q"
  assumes lm: "l \<le> m"
  shows "cmod (emb i (gs_system_coeff d a b l k)) \<le>
    (of_nat q * (1 + gs_data_emb_bound)) ^ k *
    gs_data_emb_bound ^ (m * q) * gs_data_emb_bound ^ (m * q)"
  by (rule gs_system_coeff_emb_uniform_le[OF ilt aq bq lm
      gs_data_emb_bound_facts(1)[OF ilt] gs_data_emb_bound_facts(2)[OF ilt]
      gs_data_emb_bound_facts(3)[OF ilt] gs_data_emb_bound_facts(4)[OF ilt]])

lemma gs_row_scaled_entry_emb_data_uniform_le:
  assumes ilt: "i < D"
  assumes ult: "u < gs_m h * gs_n h q"
  assumes tlt: "t < q * q"
  shows "cmod (emb i (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) \<le>
    (of_int (abs (gs_c1 d)) :: real) ^ (gs_n h q) *
    (of_int (abs (gs_c1 d)) :: real) ^ (gs_m h * q) *
    (of_int (abs (gs_c1 d)) :: real) ^ (gs_m h * q) *
    (of_nat q * (1 + gs_data_emb_bound)) ^ (gs_n h q) *
    gs_data_emb_bound ^ (gs_m h * q) *
    gs_data_emb_bound ^ (gs_m h * q)"
proof -
  let ?m = "gs_m h"
  let ?n = "gs_n h q"
  let ?k = "gs_k_idx ?n u"
  let ?ea = "gs_a_idx q t * gs_l_idx ?n u"
  let ?eb = "gs_b_idx q t * gs_l_idx ?n u"
  let ?H = "gs_data_emb_bound"
  let ?C = "(of_int (abs (gs_c1 d)) :: real)"
  let ?B = "of_nat q * (1 + ?H)"
  let ?scale = "of_int (abs (gs_row_scale d ?m ?n q u)) :: real"
  have Hone: "1 \<le> ?H" by (rule gs_data_emb_bound_facts(1)[OF ilt])
  have aH: "cmod (emb i (gs_a d)) \<le> ?H"
    by (rule gs_data_emb_bound_facts(2)[OF ilt])
  have bH: "cmod (emb i (gs_b d)) \<le> ?H"
    by (rule gs_data_emb_bound_facts(3)[OF ilt])
  have wH: "cmod (emb i (gs_w d)) \<le> ?H"
    by (rule gs_data_emb_bound_facts(4)[OF ilt])
  have kle: "?k \<le> ?n"
    using gs_k_idx_le[OF npos, of u] by linarith
  have lle: "gs_l_idx ?n u \<le> ?m"
    by (rule gs_l_idx_le[OF npos ult])
  have ale: "gs_a_idx q t \<le> q"
    by (rule gs_a_idx_le[OF qpos tlt])
  have ble: "gs_b_idx q t \<le> q"
    by (rule gs_b_idx_le[OF qpos])
  have eale: "?ea \<le> ?m * q"
  proof -
    have "?ea \<le> q * gs_l_idx ?n u" using ale by simp
    also have "... \<le> q * ?m" using lle by simp
    finally show ?thesis by (simp add: mult.commute)
  qed
  have eble: "?eb \<le> ?m * q"
  proof -
    have "?eb \<le> q * gs_l_idx ?n u" using ble by simp
    also have "... \<le> q * ?m" using lle by simp
    finally show ?thesis by (simp add: mult.commute)
  qed
  have bone: "1 \<le> ?B"
  proof -
    have qone: "1 \<le> (of_nat q :: real)" using qpos by simp
    have "1 * 1 \<le> (of_nat q :: real) * (1 + ?H)"
      using qone Hone by (intro mult_mono) auto
    then show ?thesis by simp
  qed
  have cone: "1 \<le> ?C"
    using gelfond_schneider_data_c1_ge1[OF d] by simp
  have scale_eq: "?scale = ?C ^ ?k * ?C ^ (?m * q) * ?C ^ (?m * q)"
    unfolding gs_row_scale_def by (simp add: power_abs abs_mult algebra_simps)
  have cpower: "?C ^ ?k \<le> ?C ^ ?n"
    by (rule power_increasing) (use cone kle in auto)
  have scale_up: "?scale \<le> ?C ^ ?n * ?C ^ (?m * q) * ?C ^ (?m * q)"
  proof -
    have "?scale = ?C ^ ?k * (?C ^ (?m * q) * ?C ^ (?m * q))"
      by (simp only: scale_eq mult.assoc)
    also have "... \<le> ?C ^ ?n * (?C ^ (?m * q) * ?C ^ (?m * q))"
      by (rule mult_right_mono[OF cpower]) simp
    finally show ?thesis by (simp add: mult.assoc)
  qed
  have bpow: "(of_nat q * (1 + cmod (emb i (gs_b d)))) ^ ?k \<le> ?B ^ ?n"
  proof -
    have "of_nat q * (1 + cmod (emb i (gs_b d))) \<le> ?B"
      using bH by (intro mult_left_mono) auto
    then have "(of_nat q * (1 + cmod (emb i (gs_b d)))) ^ ?k \<le> ?B ^ ?k"
      by (rule power_mono) auto
    also have "... \<le> ?B ^ ?n"
      by (rule power_increasing) (use bone kle in auto)
    finally show ?thesis .
  qed
  have apow: "cmod (emb i (gs_a d)) ^ ?ea \<le> ?H ^ (?m * q)"
  proof -
    have "cmod (emb i (gs_a d)) ^ ?ea \<le> ?H ^ ?ea"
      by (rule power_mono[OF aH]) auto
    also have "... \<le> ?H ^ (?m * q)"
      by (rule power_increasing) (use Hone eale in auto)
    finally show ?thesis .
  qed
  have wpow: "cmod (emb i (gs_w d)) ^ ?eb \<le> ?H ^ (?m * q)"
  proof -
    have "cmod (emb i (gs_w d)) ^ ?eb \<le> ?H ^ ?eb"
      by (rule power_mono[OF wH]) auto
    also have "... \<le> ?H ^ (?m * q)"
      by (rule power_increasing) (use Hone eble in auto)
    finally show ?thesis .
  qed
  have raw: "cmod (emb i (gs_row_scaled_system_mat d ?m ?n q $$ (u,t))) \<le>
      ?scale * ((of_nat q * (1 + cmod (emb i (gs_b d)))) ^ ?k *
      cmod (emb i (gs_a d)) ^ ?ea * cmod (emb i (gs_w d)) ^ ?eb)"
    using gs_row_scaled_entry_emb_cmod_le[OF ilt qpos npos ult tlt]
    by (simp add: mult.assoc)
  have factor: "(of_nat q * (1 + cmod (emb i (gs_b d)))) ^ ?k *
      cmod (emb i (gs_a d)) ^ ?ea * cmod (emb i (gs_w d)) ^ ?eb \<le>
      ?B ^ ?n * ?H ^ (?m * q) * ?H ^ (?m * q)"
    using bpow apow wpow Hone bone by (intro mult_mono) auto
  have scale_nonneg: "0 \<le> ?scale" by simp
  have factor_nonneg: "0 \<le> ?B ^ ?n * ?H ^ (?m * q) * ?H ^ (?m * q)"
    using bone Hone by simp
  have "cmod (emb i (gs_row_scaled_system_mat d ?m ?n q $$ (u,t))) \<le>
      ?scale * (?B ^ ?n * ?H ^ (?m * q) * ?H ^ (?m * q))"
    using raw factor scale_nonneg by (meson mult_left_mono order_trans)
  also have "... \<le> (?C ^ ?n * ?C ^ (?m * q) * ?C ^ (?m * q)) *
      (?B ^ ?n * ?H ^ (?m * q) * ?H ^ (?m * q))"
    by (rule mult_right_mono[OF scale_up factor_nonneg])
  finally show ?thesis by (simp add: mult.assoc)
qed

definition gs_concrete_entry_bound :: real where
  "gs_concrete_entry_bound =
    (of_int (abs (gs_c1 d)) :: real) ^ (gs_n h q) *
    (of_int (abs (gs_c1 d)) :: real) ^ (gs_m h * q) *
    (of_int (abs (gs_c1 d)) :: real) ^ (gs_m h * q) *
    (of_nat q * (1 + gs_data_emb_bound)) ^ (gs_n h q) *
    gs_data_emb_bound ^ (gs_m h * q) *
    gs_data_emb_bound ^ (gs_m h * q)"

lemma gs_concrete_entry_bound_nonneg:
  "0 \<le> gs_concrete_entry_bound"
  using gs_data_emb_bound_facts(1)[OF i0lt]
  unfolding gs_concrete_entry_bound_def by simp

lemma gs_row_scaled_entry_concrete_house_le:
  assumes ult: "u < gs_m h * gs_n h q"
  assumes tlt: "t < q * q"
  shows "EH.ehouse (Aemb u t) \<le> gs_concrete_entry_bound"
proof (rule EH.ehouse_leI[OF gs_concrete_entry_bound_nonneg])
  fix e
  assume eE: "e \<in> E"
  then obtain i where ilt: "i < D" and eeq: "e = emb i"
    unfolding E_def by auto
  show "cmod (Aemb u t e) \<le> gs_concrete_entry_bound"
    using gs_row_scaled_entry_emb_data_uniform_le[OF ilt ult tlt]
    by (simp add: Aemb_def eeq gs_concrete_entry_bound_def)
qed

definition gs_concrete_entry_growth_constant :: real where
  "gs_concrete_entry_growth_constant =
    (of_int (abs (gs_c1 d)) :: real) *
    (of_int (abs (gs_c1 d)) :: real) ^ (2 * gs_m h * gs_m h) *
    (of_int (abs (gs_c1 d)) :: real) ^ (2 * gs_m h * gs_m h) *
    (sqrt (2 * of_nat (gs_m h)) * (1 + gs_data_emb_bound)) *
    gs_data_emb_bound ^ (2 * gs_m h * gs_m h) *
    gs_data_emb_bound ^ (2 * gs_m h * gs_m h)"

lemma gs_concrete_entry_bound_le_growth:
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  shows "gs_concrete_entry_bound \<le>
    gs_concrete_entry_growth_constant ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
proof -
  have prod_ge1: "1 \<le> c14 * c5"
  proof -
    have "(1::real) * 1 \<le> c14 * c5"
      by (intro mult_mono) (use c14_ge1 c5_gt1 in auto)
    then show ?thesis by simp
  qed
  have nle_choice: "gs_n h (gs_q_choice h (c14 * c5)) \<le> r"
    using nle by (simp add: q_def)
  have qle: "q \<le> 2 * gs_m h * r"
    using gs_q_choice_le_two_mr[OF hpos prod_ge1 nle_choice]
    by (simp add: q_def)
  have bal: "q * q = 2 * gs_m h * gs_n h q"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have qsq: "q * q \<le> 2 * gs_m h * r"
  proof -
    have "2 * gs_m h * gs_n h q \<le> 2 * gs_m h * r"
      by (rule mult_left_mono[OF nle]) simp
    then show ?thesis using bal by simp
  qed
  have mpos: "gs_m h > 0" by simp
  have Cge1: "1 \<le> (of_int (abs (gs_c1 d)) :: real)"
    using gelfond_schneider_data_c1_ge1[OF d] by simp
  have Hge1: "1 \<le> gs_data_emb_bound"
    by (rule gs_data_emb_bound_facts(1)[OF i0lt])
  show ?thesis
    using gs_entry_power_le_r_half[OF mpos rpos nle qle qsq Cge1 Hge1]
    by (simp add: gs_concrete_entry_bound_def
      gs_concrete_entry_growth_constant_def)
qed

definition gs_witness_growth_weight :: real where
  "gs_witness_growth_weight =
    of_nat (card E) * power_basis_inverse_bound * power_basis_entry_bound"

definition gs_entry_growth_envelope :: "nat \<Rightarrow> real" where
  "gs_entry_growth_envelope r = max 1
    (gs_concrete_entry_growth_constant ^ r *
      (of_nat r :: real) powr (of_nat r / 2))"

lemma gs_concrete_entry_growth_constant_ge_one:
  "1 \<le> gs_concrete_entry_growth_constant"
proof -
  let ?C = "(of_int (abs (gs_c1 d)) :: real)"
  let ?H = "gs_data_emb_bound"
  let ?m = "gs_m h"
  have Cone: "1 \<le> ?C"
    using gelfond_schneider_data_c1_ge1[OF d] by simp
  have Hone: "1 \<le> ?H"
    by (rule gs_data_emb_bound_facts(1)[OF i0lt])
  have middle: "1 \<le> sqrt (2 * of_nat ?m) * (1 + ?H)"
  proof -
    have sqone: "1 \<le> sqrt (2 * (of_nat ?m :: real))"
      by (simp add: gs_m_def)
    have "(1::real) * 1 \<le> sqrt (2 * of_nat ?m) * (1 + ?H)"
      by (intro mult_mono sqone) (use Hone in auto)
    then show ?thesis by simp
  qed
  have "(1::real) * 1 * 1 * 1 * 1 * 1 \<le>
      ?C * ?C ^ (2 * ?m * ?m) * ?C ^ (2 * ?m * ?m) *
      (sqrt (2 * of_nat ?m) * (1 + ?H)) *
      ?H ^ (2 * ?m * ?m) * ?H ^ (2 * ?m * ?m)"
    by (intro mult_mono Cone middle power_increasing Hone) (use Cone Hone in auto)
  then show ?thesis by (simp add: gs_concrete_entry_growth_constant_def)
qed

lemma gs_entry_growth_envelope_eq:
  assumes rpos: "r > 0"
  shows "gs_entry_growth_envelope r =
    gs_concrete_entry_growth_constant ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
proof -
  have rone: "1 \<le> (of_nat r :: real)" using rpos by simp
  have powrone: "1 \<le> (of_nat r :: real) powr (of_nat r / 2)"
    using powr_mono2[of "of_nat r / 2" 1 "of_nat r"] rone by simp
  have Kone: "1 \<le> gs_concrete_entry_growth_constant"
    by (rule gs_concrete_entry_growth_constant_ge_one)
  have Fone: "1 \<le> gs_concrete_entry_growth_constant ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
  proof -
    have "(1::real) * 1 \<le> gs_concrete_entry_growth_constant ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
      by (intro mult_mono powrone) (use Kone in auto)
    then show ?thesis by simp
  qed
  show ?thesis using Fone by (simp add: gs_entry_growth_envelope_def)
qed

lemma gs_witness_bound_le_growth:
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  shows "(of_int (2 * int (q * q * D) *
    max 1 (ceiling (of_nat (card E) * power_basis_inverse_bound *
      gs_concrete_entry_bound * power_basis_entry_bound))) :: real) \<le>
    (4 * of_nat (gs_m h) * of_nat D *
      (1 + gs_witness_growth_weight)) * of_nat r *
      gs_entry_growth_envelope r"
proof -
  have bal: "q * q = 2 * gs_m h * gs_n h q"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have qsq: "q * q \<le> 2 * gs_m h * r"
  proof -
    have "2 * gs_m h * gs_n h q \<le> 2 * gs_m h * r"
      by (rule mult_left_mono[OF nle]) simp
    then show ?thesis using bal by simp
  qed
  have Anonneg: "0 \<le> gs_concrete_entry_bound"
    by (rule gs_concrete_entry_bound_nonneg)
  have Wnonneg: "0 \<le> gs_witness_growth_weight"
    unfolding gs_witness_growth_weight_def
    using power_basis_inverse_bound_nonneg power_basis_entry_bound_nonneg by simp
  have Ale: "gs_concrete_entry_bound \<le> gs_entry_growth_envelope r"
    using gs_concrete_entry_bound_le_growth[OF nle rpos]
    by (simp add: gs_entry_growth_envelope_def)
  have Gone: "1 \<le> gs_entry_growth_envelope r"
    by (simp add: gs_entry_growth_envelope_def)
  have bound: "(of_int (2 * int (q * q * D) *
    max 1 (ceiling (gs_witness_growth_weight * gs_concrete_entry_bound))) :: real) \<le>
    (4 * of_nat (gs_m h) * of_nat D *
      (1 + gs_witness_growth_weight)) * of_nat r *
      gs_entry_growth_envelope r"
    by (rule gs_witness_bound_le_growth[OF qsq Anonneg Wnonneg Ale Gone])
  show ?thesis using bound
    by (simp add: gs_witness_growth_weight_def ac_simps)
qed

lemma gs_row_denominator_exponent_le_order:
  assumes nle: "gs_n h q \<le> r"
    and rpos: "r > 0"
  shows "gs_n h q + 2 * (gs_m h * q) + D \<le>
    (1 + 4 * gs_m h * gs_m h + D) * r"
proof -
  have prod_ge1: "1 \<le> c14 * c5"
  proof -
    have "(1::real) * 1 \<le> c14 * c5"
      by (intro mult_mono) (use c14_ge1 c5_gt1 in auto)
    then show ?thesis by simp
  qed
  have nle_choice: "gs_n h (gs_q_choice h (c14 * c5)) \<le> r"
    using nle by (simp add: q_def)
  have qle: "q \<le> 2 * gs_m h * r"
    using gs_q_choice_le_two_mr[OF hpos prod_ge1 nle_choice]
    by (simp add: q_def)
  have mle: "2 * (gs_m h * q) \<le> (4 * gs_m h * gs_m h) * r"
  proof -
    have "2 * gs_m h * q \<le> 2 * gs_m h * (2 * gs_m h * r)"
      by (rule mult_left_mono[OF qle]) simp
    then show ?thesis by (simp add: algebra_simps)
  qed
  have Dle: "D \<le> D * r" using rpos by simp
  have "gs_n h q + 2 * (gs_m h * q) + D \<le>
    r + (4 * gs_m h * gs_m h) * r + D * r"
    using nle mle Dle by linarith
  also have "... = (1 + 4 * gs_m h * gs_m h + D) * r"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma gs_row_denominator_power_le_order:
  assumes nle: "gs_n h q \<le> r"
    and rpos: "r > 0"
    and Tp: "T > (0::int)"
  shows "T ^ (gs_n h q + 2 * (gs_m h * q) + D) \<le>
    (T ^ (1 + 4 * gs_m h * gs_m h + D)) ^ r"
proof -
  have Tge: "1 \<le> T" using Tp by simp
  have exp: "gs_n h q + 2 * (gs_m h * q) + D \<le>
    (1 + 4 * gs_m h * gs_m h + D) * r"
    by (rule gs_row_denominator_exponent_le_order[OF nle rpos])
  have "T ^ (gs_n h q + 2 * (gs_m h * q) + D) \<le>
    T ^ ((1 + 4 * gs_m h * gs_m h + D) * r)"
    by (rule power_increasing) (use Tge exp in auto)
  then show ?thesis by (simp only: power_mult)
qed

lemma gs_witness_bound_le_growth_simple:
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  shows "(of_int (2 * int (q * q * D) *
    max 1 (ceiling (of_nat (card E) * power_basis_inverse_bound *
      gs_concrete_entry_bound * power_basis_entry_bound))) :: real) \<le>
    (4 * of_nat (gs_m h) * of_nat D *
      (1 + gs_witness_growth_weight)) * of_nat r *
      gs_concrete_entry_growth_constant ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
  using gs_witness_bound_le_growth[OF nle rpos]
  by (simp add: gs_entry_growth_envelope_eq[OF rpos] ac_simps)

lemma gs_witness_bound_le_growth_with_denominator:
  assumes nle: "gs_n h q \<le> r"
    and rpos: "r > 0"
    and Tp: "T > (0::int)"
  shows "(of_int (2 * int (q * q * D) *
    max 1 (ceiling (of_nat (card E) * power_basis_inverse_bound *
      (of_int (T ^ (gs_n h q + 2 * (gs_m h * q) + D)) *
        gs_concrete_entry_bound * power_basis_entry_bound)))) :: real) \<le>
    (4 * of_nat (gs_m h) * of_nat D *
      (1 + gs_witness_growth_weight)) * of_nat r *
      (gs_concrete_entry_growth_constant *
        of_int (T ^ (1 + 4 * gs_m h * gs_m h + D))) ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
proof -
  let ?N = "gs_n h q + 2 * (gs_m h * q) + D"
  let ?C = "1 + 4 * gs_m h * gs_m h + D"
  let ?S = "of_int (T ^ ?C) :: real"
  let ?L = "of_int (T ^ ?N) :: real"
  let ?A = "?L * gs_concrete_entry_bound"
  let ?K = "gs_concrete_entry_growth_constant"
  let ?P = "(of_nat r :: real) powr (of_nat r / 2)"
  let ?G = "(?K * ?S) ^ r * ?P"
  let ?W = "gs_witness_growth_weight"
  have bal: "q * q = 2 * gs_m h * gs_n h q"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have qsq: "q * q \<le> 2 * gs_m h * r"
  proof -
    have "2 * gs_m h * gs_n h q \<le> 2 * gs_m h * r"
      by (rule mult_left_mono[OF nle]) simp
    then show ?thesis using bal by simp
  qed
  have Lnonneg: "0 \<le> ?L" using Tp by simp
  have Anonneg: "0 \<le> ?A"
    using Lnonneg gs_concrete_entry_bound_nonneg by simp
  have Wnonneg: "0 \<le> ?W"
    unfolding gs_witness_growth_weight_def
    using power_basis_inverse_bound_nonneg power_basis_entry_bound_nonneg by simp
  have Sle_int: "T ^ ?N \<le> (T ^ ?C) ^ r"
    by (rule gs_row_denominator_power_le_order[OF nle rpos Tp])
  have Sle_cast: "(of_int (T ^ ?N) :: real) \<le> of_int ((T ^ ?C) ^ r)"
    by (simp only: of_int_le_iff Sle_int)
  have Sle: "?L \<le> ?S ^ r"
    using Sle_cast by (simp only: of_int_power)
  have Aold: "gs_concrete_entry_bound \<le> ?K ^ r * ?P"
    by (rule gs_concrete_entry_bound_le_growth[OF nle rpos])
  have Ale: "?A \<le> ?G"
  proof -
    have "?L * gs_concrete_entry_bound \<le> ?L * (?K ^ r * ?P)"
      by (rule mult_left_mono[OF Aold Lnonneg])
    also have "... \<le> ?S ^ r * (?K ^ r * ?P)"
      by (rule mult_right_mono[OF Sle])
        (use gs_concrete_entry_growth_constant_ge_one in auto)
    also have "... = ?G" by (simp add: power_mult_distrib ac_simps)
    finally show ?thesis .
  qed
  have Tone: "1 \<le> T" using Tp by simp
  have Sint: "1 \<le> T ^ ?C" by (rule one_le_power[OF Tone])
  have Sone: "1 \<le> ?S" using Sint by (simp only: of_int_le_iff)
  have Eone: "1 \<le> gs_entry_growth_envelope r"
    by (simp add: gs_entry_growth_envelope_def)
  have G_eq: "?G = ?S ^ r * gs_entry_growth_envelope r"
    by (simp add: gs_entry_growth_envelope_eq[OF rpos] power_mult_distrib ac_simps)
  have Spow: "1 \<le> ?S ^ r" using Sone by simp
  have Gone: "1 \<le> ?G"
  proof -
    have "(1::real) * 1 \<le> ?S ^ r * gs_entry_growth_envelope r"
      by (intro mult_mono Spow Eone) (use Spow in auto)
    then show ?thesis by (simp only: G_eq)
  qed
  have bound: "(of_int (2 * int (q * q * D) *
      max 1 (ceiling (?W * ?A))) :: real) \<le>
      (4 * of_nat (gs_m h) * of_nat D * (1 + ?W)) * of_nat r * ?G"
    by (rule Gelfond_Schneider_Rho_Bounds.gs_witness_bound_le_growth
      [OF qsq Anonneg Wnonneg Ale Gone])
  show ?thesis using bound
    by (simp add: gs_witness_growth_weight_def ac_simps)
qed

lemma gs_house_aux_factor_le_growth:
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  shows "(of_int (abs (gs_c1 d)) :: real) ^ r *
    (of_int (abs (gs_c1 d)) :: real) ^ (2 * gs_m h * q) *
    (of_nat q * (1 + gs_data_emb_bound)) ^ r *
    gs_data_emb_bound ^ (gs_m h * q) *
    gs_data_emb_bound ^ (gs_m h * q) \<le>
    gs_concrete_entry_growth_constant ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
proof -
  have prod_ge1: "1 \<le> c14 * c5"
  proof -
    have "(1::real) * 1 \<le> c14 * c5"
      by (intro mult_mono) (use c14_ge1 c5_gt1 in auto)
    then show ?thesis by simp
  qed
  have nle_choice: "gs_n h (gs_q_choice h (c14 * c5)) \<le> r"
    using nle by (simp add: q_def)
  have qle: "q \<le> 2 * gs_m h * r"
    using gs_q_choice_le_two_mr[OF hpos prod_ge1 nle_choice]
    by (simp add: q_def)
  have bal: "q * q = 2 * gs_m h * gs_n h q"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have qsq: "q * q \<le> 2 * gs_m h * r"
  proof -
    have "2 * gs_m h * gs_n h q \<le> 2 * gs_m h * r"
      by (rule mult_left_mono[OF nle]) simp
    then show ?thesis using bal by simp
  qed
  have Cge1: "1 \<le> (of_int (abs (gs_c1 d)) :: real)"
    using gelfond_schneider_data_c1_ge1[OF d] by simp
  have Hge1: "1 \<le> gs_data_emb_bound"
    by (rule gs_data_emb_bound_facts(1)[OF i0lt])
  note bound = gs_entry_power_le_r_half[OF gs_m_pos rpos le_refl qle qsq Cge1 Hge1]
  have split: "(of_int (abs (gs_c1 d)) :: real) ^ (2 * gs_m h * q) =
      (of_int (abs (gs_c1 d)) :: real) ^ (gs_m h * q) *
      (of_int (abs (gs_c1 d)) :: real) ^ (gs_m h * q)"
  proof -
    have "2 * gs_m h * q = gs_m h * q + gs_m h * q"
      by (simp add: algebra_simps)
    then show ?thesis by (simp only: power_add)
  qed
  show ?thesis using bound
    by (simp only: split gs_concrete_entry_growth_constant_def)
qed

lemma represented_coordinate_in_K:
  assumes repr:
    "\<forall>t<q * q. Matrix.vec_index v t =
      (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))"
  assumes tlt: "t < q * q"
  shows "Matrix.vec_index v t \<in> K"
proof -
  have "Matrix.vec_index v t =
      (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * eta ^ j)"
    using repr tlt by (simp add: basis_eq_power_at_identity_embedding[OF emb0])
  also have "... \<in> K"
    by (rule sum_rat_power_in_K) auto
  finally show ?thesis
    by simp
qed

lemma gs_scaled_deriv_emb_bounded_vec_le:
  assumes ilt: "i < D"
  assumes repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes lm: "l \<le> gs_m h"
  shows "cmod (emb i ((of_int c :: complex) *
    (gs_z d powi (- int k) *
      ((deriv ^^ k) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t))) (of_nat l)))) \<le>
    of_int (abs c) * of_nat (q * q) *
      ((of_int B :: real) * of_nat D * power_basis_entry_bound) *
      ((of_nat q * (1 + gs_data_emb_bound)) ^ k *
        gs_data_emb_bound ^ (gs_m h * q) *
        gs_data_emb_bound ^ (gs_m h * q))"
proof -
  let ?V = "(of_int B :: real) * of_nat D * power_basis_entry_bound"
  let ?U = "(of_nat q * (1 + gs_data_emb_bound)) ^ k *
    gs_data_emb_bound ^ (gs_m h * q) * gs_data_emb_bound ^ (gs_m h * q)"
  have Hone: "1 \<le> gs_data_emb_bound"
    by (rule gs_data_emb_bound_facts(1)[OF ilt])
  have Vnonneg: "0 \<le> ?V"
    using B_nonneg power_basis_entry_bound_nonneg by simp
  have Unonneg: "0 \<le> ?U"
    using Hone by simp
  have coeffK: "\<And>t. t < q * q \<Longrightarrow> Matrix.vec_index v t \<in> K"
    by (rule represented_coordinate_in_K[OF repr])
  have coeffB: "\<And>t. t < q * q \<Longrightarrow>
    cmod (emb i (Matrix.vec_index v t)) \<le> ?V"
    by (rule represented_coordinate_emb_cmod_le[OF ilt repr x_carrier x_bnd B_nonneg])
  have sysB: "\<And>t. t < q * q \<Longrightarrow>
    cmod (emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)) \<le> ?U"
  proof -
    fix t
    assume tlt: "t < q * q"
    have ale: "gs_a_idx q t \<le> q"
      by (rule gs_a_idx_le[OF qpos tlt])
    have ble: "gs_b_idx q t \<le> q"
      by (rule gs_b_idx_le[OF qpos])
    show "cmod (emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)) \<le> ?U"
      by (rule gs_system_coeff_emb_data_bound[OF ilt ale ble lm])
  qed
  show ?thesis
    by (rule gs_scaled_deriv_emb_uniform_bound[OF ilt coeffK Vnonneg Unonneg coeffB sysB])
qed

lemma scaled_deriv_at_nat_in_K:
  assumes coeffK: "\<forall>t<q * q. Matrix.vec_index v t \<in> K"
  shows "gs_z d powi (- int k) *
      ((deriv ^^ k) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t))) (of_nat l) \<in> K"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have termK:
      "Matrix.vec_index v t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k \<in> K"
    if tmem: "t \<in> {..<q * q}" for t
  proof -
    have vK: "Matrix.vec_index v t \<in> K"
      using coeffK tmem by blast
    have sysK: "gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k \<in> K"
      by (rule gs_system_coeff_in_K)
    show ?thesis
      by (rule KS.mult_closed[OF vK sysK])
  qed
  have "(\<Sum>t<q * q. Matrix.vec_index v t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k) \<in> K"
    by (rule KS.sum_closed) (use termK in auto)
  then show ?thesis
    by (simp add: gs_aux_fun_vec_deriv_at_nat[OF d])
qed

lemma rho_in_K:
  assumes repr:
    "\<forall>t<q * q. Matrix.vec_index v t =
      (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))"
  assumes rho_def:
    "rho = (of_int c :: complex) *
      (gs_z d powi (- int r) *
        ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
  shows "rho \<in> K"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have coeffK: "\<forall>t<q * q. Matrix.vec_index v t \<in> K"
  proof (intro strip)
    fix t
    assume tlt: "t < q * q"
    show "Matrix.vec_index v t \<in> K"
    proof -
      have eq:
          "Matrix.vec_index v t =
          (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * eta ^ j)"
        using repr tlt by (simp add: basis_eq_power_at_identity_embedding[OF emb0])
      have inK:
          "(\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * eta ^ j) \<in> K"
        by (rule sum_rat_power_in_K) auto
      show ?thesis
        unfolding eq by (rule inK)
    qed
  qed
  obtain l where node: "gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t) = of_nat (Suc l)"
    by (rule gs_min_order_node_eq_nat[OF gs_m_pos])
  have derivK:
      "gs_z d powi (- int r) *
        ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<in> K"
  proof -
    have "gs_z d powi (- int r) *
        ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t))) (of_nat (Suc l)) \<in> K"
      by (rule scaled_deriv_at_nat_in_K[OF coeffK])
    then show ?thesis
      by (simp add: node)
  qed
  have cK: "(of_int c :: complex) \<in> K"
    by (simp add: KS.of_int_closed)
  have "(of_int c :: complex) *
      (gs_z d powi (- int r) *
        ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<in> K"
    by (rule KS.mult_closed[OF cK derivK])
  then show ?thesis
    by (simp add: rho_def)
qed

lemma rho_order_pos:
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes v_ker:
    "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
  assumes r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  shows "0 < r"
proof -
  have coeff_nz: "\<exists>t<q * q. Matrix.vec_index v t \<noteq> 0"
    using v_carrier v_nz by force
  have ker_coeff:
    "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v gs_coeff_vec q (\<lambda>t. Matrix.vec_index v t) =
      0\<^sub>v (gs_m h * gs_n h q)"
    by (simp add: gs_coeff_vec_eqI[OF v_carrier] v_ker)
  have min_ord:
    "gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t) \<ge> gs_n h q"
    by (rule gs_min_order_ge_of_row_scaled_kernel_nonzero[OF d qpos gs_m_pos npos coeff_nz ker_coeff])
  show ?thesis
    using min_ord npos r_eq by linarith
qed

lemma rho_order_ge_n:
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes v_ker:
    "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
  assumes r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  shows "gs_n h q \<le> r"
proof -
  have coeff_nz: "\<exists>t<q * q. Matrix.vec_index v t \<noteq> 0"
    using v_carrier v_nz by force
  have ker_coeff:
    "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v
      gs_coeff_vec q (\<lambda>t. Matrix.vec_index v t) =
      0\<^sub>v (gs_m h * gs_n h q)"
    by (simp add: gs_coeff_vec_eqI[OF v_carrier] v_ker)
  have min_ord:
    "gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t) \<ge> gs_n h q"
    by (rule gs_min_order_ge_of_row_scaled_kernel_nonzero[OF d qpos gs_m_pos
      npos coeff_nz ker_coeff])
  show ?thesis using min_ord r_eq by linarith
qed

lemma rho_algebraic_int_nonzero:
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
  assumes r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  assumes deriv_nz:
    "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
      (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
  assumes c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
  assumes rho_def:
    "rho = (of_int c :: complex) *
      (gs_z d powi (- int r) *
        ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
  shows "algebraic_int rho" and "rho \<noteq> 0"
proof -
  have rho_ai: "algebraic_int rho"
    using gs_scaled_rho_algebraic_int_nonzero(1)[OF d qpos gs_m_pos v_carrier v_nz vint r_eq deriv_nz c_def rho_def] .
  show "algebraic_int rho"
    using rho_ai .
  show "rho \<noteq> 0"
  proof -
    have c_nz: "c \<noteq> 0"
      unfolding c_def using gelfond_schneider_data_c1_nonzero[OF d] by auto
    have zfac_nz: "gs_z d powi (- int r) \<noteq> 0"
      using gelfond_schneider_data_z_nonzero[OF d] by (simp add: power_int_def)
    have "rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
      by (rule rho_def)
    then show ?thesis
      using c_nz zfac_nz deriv_nz by auto
  qed
qed

lemma gs_house_rho_le_of_bounded_vec:
  assumes repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes ai: "algebraic_int rho"
  assumes xK: "rho \<in> K"
  assumes rho_def: "rho = (of_int c :: complex) *
    (gs_z d powi (- int r) *
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
  shows "gs_house rho \<le>
    of_int (abs c) * of_nat (q * q) *
      ((of_int B :: real) * of_nat D * power_basis_entry_bound) *
      ((of_nat q * (1 + gs_data_emb_bound)) ^ r *
        gs_data_emb_bound ^ (gs_m h * q) *
        gs_data_emb_bound ^ (gs_m h * q))"
proof -
  let ?H = "of_int (abs c) * of_nat (q * q) *
      ((of_int B :: real) * of_nat D * power_basis_entry_bound) *
      ((of_nat q * (1 + gs_data_emb_bound)) ^ r *
        gs_data_emb_bound ^ (gs_m h * q) *
        gs_data_emb_bound ^ (gs_m h * q))"
  have Hnonneg: "0 \<le> ?H"
    using B_nonneg power_basis_entry_bound_nonneg
      gs_data_emb_bound_facts(1)[OF i0lt] by simp
  obtain l where llt: "l < gs_m h" and node:
    "gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t) = of_nat (Suc l)"
    by (rule gs_min_order_node_eq_nat[OF gs_m_pos])
  have lle: "Suc l \<le> gs_m h" using llt by simp
  have bound: "cmod (emb j rho) \<le> ?H" if jlt: "j < D" for j
  proof -
    have "cmod (emb j rho) = cmod (emb j ((of_int c :: complex) *
      (gs_z d powi (- int r) *
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t))) (of_nat (Suc l)))))"
      by (simp add: rho_def node)
    also have "... \<le> ?H"
      by (rule gs_scaled_deriv_emb_bounded_vec_le[OF jlt repr x_carrier x_bnd B_nonneg lle])
    finally show ?thesis .
  qed
  show ?thesis
    by (rule gs_house_le_of_emb_bound[OF finite normal separable ai xK Hnonneg bound])
qed

lemma gs_house_rho_le_growth:
  assumes repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes ai: "algebraic_int rho"
  assumes xK: "rho \<in> K"
  assumes rho_def: "rho = (of_int c :: complex) *
    (gs_z d powi (- int r) *
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
  assumes c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  assumes Bbound: "(of_int B :: real) \<le>
    (4 * of_nat (gs_m h) * of_nat D *
      (1 + gs_witness_growth_weight)) * of_nat r *
      gs_concrete_entry_growth_constant ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
  shows "gs_house rho \<le>
    (2 * of_nat (gs_m h) *
      (4 * of_nat (gs_m h) * of_nat D *
        (1 + gs_witness_growth_weight)) *
      (of_nat D * power_basis_entry_bound)) *
      (gs_concrete_entry_growth_constant *
        gs_concrete_entry_growth_constant) ^ r *
      (of_nat r :: real) powr (of_nat r + 2)"
proof -
  let ?C = "(of_int (abs (gs_c1 d)) :: real)"
  let ?H = "gs_data_emb_bound"
  let ?K = "gs_concrete_entry_growth_constant"
  let ?W = "4 * of_nat (gs_m h) * of_nat D *
      (1 + gs_witness_growth_weight) :: real"
  let ?E = "of_nat D * power_basis_entry_bound :: real"
  let ?F = "?C ^ r * ?C ^ (2 * gs_m h * q) *
    (of_nat q * (1 + ?H)) ^ r *
    ?H ^ (gs_m h * q) * ?H ^ (gs_m h * q)"
  have bal: "q * q = 2 * gs_m h * gs_n h q"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have qsq: "q * q \<le> 2 * gs_m h * r"
  proof -
    have "2 * gs_m h * gs_n h q \<le> 2 * gs_m h * r"
      by (rule mult_left_mono[OF nle]) simp
    then show ?thesis using bal by simp
  qed
  have Cge: "1 \<le> ?C"
    using gelfond_schneider_data_c1_ge1[OF d] by simp
  have Hge: "1 \<le> ?H"
    by (rule gs_data_emb_bound_facts(1)[OF i0lt])
  have c_abs: "(of_int (abs c) :: real) = ?C ^ r * ?C ^ (2 * gs_m h * q)"
    using c_def by (simp add: abs_mult power_abs)
  have Fnonneg: "0 \<le> ?F" using Cge Hge by simp
  have Fbound: "?F \<le> ?K ^ r * (of_nat r :: real) powr (of_nat r / 2)"
    by (rule gs_house_aux_factor_le_growth[OF nle rpos])
  have Wnonneg: "0 \<le> ?W"
    using power_basis_inverse_bound_nonneg power_basis_entry_bound_nonneg
    by (simp add: gs_witness_growth_weight_def)
  have Enonneg: "0 \<le> ?E"
    using power_basis_entry_bound_nonneg by simp
  note house_raw = gs_house_rho_le_of_bounded_vec[OF repr x_carrier x_bnd B_nonneg ai xK rho_def]
  have house_factor: "gs_house rho \<le> (of_nat (q * q) :: real) * of_int B * ?E * ?F"
    using house_raw by (simp only: c_abs of_nat_mult ac_simps)
  have multiplied: "(of_nat (q * q) :: real) * of_int B * ?E * ?F \<le>
    (2 * of_nat (gs_m h) * ?W * ?E) * (?K * ?K) ^ r *
      (of_nat r :: real) powr (of_nat r + 2)"
    by (rule gs_house_growth_multiply[OF rpos qsq _ Fnonneg Wnonneg _ Enonneg Bbound Fbound])
      (use B_nonneg gs_concrete_entry_growth_constant_ge_one in auto)
  show ?thesis using house_factor multiplied by simp
qed

lemma gs_house_rho_le_growth_with_factor:
  assumes repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes ai: "algebraic_int rho"
  assumes xK: "rho \<in> K"
  assumes rho_def: "rho = (of_int c :: complex) *
    (gs_z d powi (- int r) *
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
  assumes c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  assumes Uone: "1 \<le> U"
  assumes Bbound: "(of_int B :: real) \<le>
    (4 * of_nat (gs_m h) * of_nat D *
      (1 + gs_witness_growth_weight)) * of_nat r *
      (gs_concrete_entry_growth_constant * U) ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
  shows "gs_house rho \<le>
    (2 * of_nat (gs_m h) *
      (4 * of_nat (gs_m h) * of_nat D *
        (1 + gs_witness_growth_weight)) *
      (of_nat D * power_basis_entry_bound)) *
      ((gs_concrete_entry_growth_constant * U) *
        (gs_concrete_entry_growth_constant * U)) ^ r *
      (of_nat r :: real) powr (of_nat r + 2)"
proof -
  let ?C = "(of_int (abs (gs_c1 d)) :: real)"
  let ?H = "gs_data_emb_bound"
  let ?K = "gs_concrete_entry_growth_constant * U"
  let ?W = "4 * of_nat (gs_m h) * of_nat D *
      (1 + gs_witness_growth_weight) :: real"
  let ?E = "of_nat D * power_basis_entry_bound :: real"
  let ?F = "?C ^ r * ?C ^ (2 * gs_m h * q) *
    (of_nat q * (1 + ?H)) ^ r *
    ?H ^ (gs_m h * q) * ?H ^ (gs_m h * q)"
  have bal: "q * q = 2 * gs_m h * gs_n h q"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have qsq: "q * q \<le> 2 * gs_m h * r"
  proof -
    have "2 * gs_m h * gs_n h q \<le> 2 * gs_m h * r"
      by (rule mult_left_mono[OF nle]) simp
    then show ?thesis using bal by simp
  qed
  have Cge: "1 \<le> ?C"
    using gelfond_schneider_data_c1_ge1[OF d] by simp
  have Hge: "1 \<le> ?H"
    by (rule gs_data_emb_bound_facts(1)[OF i0lt])
  have c_abs: "(of_int (abs c) :: real) = ?C ^ r * ?C ^ (2 * gs_m h * q)"
    using c_def by (simp add: abs_mult power_abs)
  have Fnonneg: "0 \<le> ?F" using Cge Hge by simp
  have Fbase: "?F \<le> gs_concrete_entry_growth_constant ^ r *
    (of_nat r :: real) powr (of_nat r / 2)"
    by (rule gs_house_aux_factor_le_growth[OF nle rpos])
  have Kge: "1 \<le> gs_concrete_entry_growth_constant"
    by (rule gs_concrete_entry_growth_constant_ge_one)
  have Knonneg: "0 \<le> ?K" using Kge Uone by simp
  have Fbound: "?F \<le> ?K ^ r * (of_nat r :: real) powr (of_nat r / 2)"
  proof -
    have pow: "gs_concrete_entry_growth_constant ^ r \<le> ?K ^ r"
      by (rule power_mono) (use Kge Uone in auto)
    have "gs_concrete_entry_growth_constant ^ r *
      (of_nat r :: real) powr (of_nat r / 2) \<le>
      ?K ^ r * (of_nat r :: real) powr (of_nat r / 2)"
      by (rule mult_right_mono[OF pow]) simp
    then show ?thesis using Fbase by linarith
  qed
  have Wnonneg: "0 \<le> ?W"
    using power_basis_inverse_bound_nonneg power_basis_entry_bound_nonneg
    by (simp add: gs_witness_growth_weight_def)
  have Enonneg: "0 \<le> ?E"
    using power_basis_entry_bound_nonneg by simp
  note house_raw = gs_house_rho_le_of_bounded_vec[OF repr x_carrier x_bnd B_nonneg ai xK rho_def]
  have house_factor: "gs_house rho \<le> (of_nat (q * q) :: real) * of_int B * ?E * ?F"
    using house_raw by (simp only: c_abs of_nat_mult ac_simps)
  have multiplied: "(of_nat (q * q) :: real) * of_int B * ?E * ?F \<le>
    (2 * of_nat (gs_m h) * ?W * ?E) * (?K * ?K) ^ r *
      (of_nat r :: real) powr (of_nat r + 2)"
    by (rule gs_house_growth_multiply[OF rpos qsq _ Fnonneg Wnonneg _ Enonneg Bbound Fbound])
      (use B_nonneg Knonneg in auto)
  show ?thesis using house_factor multiplied by simp
qed

definition gs_house_growth_prefactor :: real where
  "gs_house_growth_prefactor =
    2 * of_nat (gs_m h) *
      (4 * of_nat (gs_m h) * of_nat D *
        (1 + gs_witness_growth_weight)) *
      (of_nat D * power_basis_entry_bound)"

definition gs_house_growth_base :: real where
  "gs_house_growth_base =
    2 * max 1 gs_house_growth_prefactor *
      (gs_concrete_entry_growth_constant *
        gs_concrete_entry_growth_constant)"

lemma gs_house_growth_base_pos:
  "0 < gs_house_growth_base"
proof -
  have Kone: "1 \<le> gs_concrete_entry_growth_constant"
    by (rule gs_concrete_entry_growth_constant_ge_one)
  show ?thesis using Kone
    by (simp add: gs_house_growth_base_def)
qed

lemma gs_house_rho_le_growth_absorbed:
  assumes repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes ai: "algebraic_int rho"
  assumes xK: "rho \<in> K"
  assumes rho_def: "rho = (of_int c :: complex) *
    (gs_z d powi (- int r) *
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
  assumes c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  assumes Bbound: "(of_int B :: real) \<le>
    (4 * of_nat (gs_m h) * of_nat D *
      (1 + gs_witness_growth_weight)) * of_nat r *
      gs_concrete_entry_growth_constant ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
  shows "gs_house rho \<le>
    gs_house_growth_base ^ r *
      (of_nat r :: real) powr (of_nat r + 3 / 2)"
proof -
  have Kone: "1 \<le> gs_concrete_entry_growth_constant"
    by (rule gs_concrete_entry_growth_constant_ge_one)
  have Wnonneg: "0 \<le> gs_witness_growth_weight"
    unfolding gs_witness_growth_weight_def
    using power_basis_inverse_bound_nonneg power_basis_entry_bound_nonneg by simp
  have Fnonneg: "0 \<le> gs_house_growth_prefactor"
    unfolding gs_house_growth_prefactor_def
    using Wnonneg power_basis_entry_bound_nonneg by simp
  have raw: "gs_house rho \<le>
    gs_house_growth_prefactor *
      (gs_concrete_entry_growth_constant *
        gs_concrete_entry_growth_constant) ^ r *
      (of_nat r :: real) powr (of_nat r + 2)"
    using gs_house_rho_le_growth[OF repr x_carrier x_bnd B_nonneg ai xK
      rho_def c_def nle rpos Bbound]
    by (simp only: gs_house_growth_prefactor_def)
  have absorb: "gs_house_growth_prefactor *
      (gs_concrete_entry_growth_constant *
        gs_concrete_entry_growth_constant) ^ r *
      (of_nat r :: real) powr (of_nat r + 2) \<le>
      gs_house_growth_base ^ r *
        (of_nat r :: real) powr (of_nat r + 3 / 2)"
    using gs_house_growth_absorb[OF rpos Fnonneg, of gs_concrete_entry_growth_constant]
      Kone by (simp add: gs_house_growth_base_def)
  show ?thesis using raw absorb by linarith
qed

lemma gs_house_rho_le_growth_absorbed_with_factor:
  assumes repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes ai: "algebraic_int rho"
  assumes xK: "rho \<in> K"
  assumes rho_def: "rho = (of_int c :: complex) *
    (gs_z d powi (- int r) *
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
  assumes c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  assumes Uone: "1 \<le> U"
  assumes Bbound: "(of_int B :: real) \<le>
    (4 * of_nat (gs_m h) * of_nat D *
      (1 + gs_witness_growth_weight)) * of_nat r *
      (gs_concrete_entry_growth_constant * U) ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
  shows "gs_house rho \<le>
    (gs_house_growth_base * U ^ 2) ^ r *
      (of_nat r :: real) powr (of_nat r + 3 / 2)"
proof -
  have Kbase: "1 \<le> gs_concrete_entry_growth_constant"
    by (rule gs_concrete_entry_growth_constant_ge_one)
  have Kone: "1 \<le> gs_concrete_entry_growth_constant * U"
  proof -
    have "(1::real) * 1 \<le> gs_concrete_entry_growth_constant * U"
      by (intro mult_mono Kbase Uone) (use Kbase Uone in auto)
    then show ?thesis by simp
  qed
  have Wnonneg: "0 \<le> gs_witness_growth_weight"
    unfolding gs_witness_growth_weight_def
    using power_basis_inverse_bound_nonneg power_basis_entry_bound_nonneg by simp
  have Fnonneg: "0 \<le> gs_house_growth_prefactor"
    unfolding gs_house_growth_prefactor_def
    using Wnonneg power_basis_entry_bound_nonneg by simp
  have raw: "gs_house rho \<le>
    gs_house_growth_prefactor *
      ((gs_concrete_entry_growth_constant * U) *
        (gs_concrete_entry_growth_constant * U)) ^ r *
      (of_nat r :: real) powr (of_nat r + 2)"
    using gs_house_rho_le_growth_with_factor[OF repr x_carrier x_bnd B_nonneg ai xK
      rho_def c_def nle rpos Uone Bbound]
    by (simp only: gs_house_growth_prefactor_def)
  have absorb: "gs_house_growth_prefactor *
      ((gs_concrete_entry_growth_constant * U) *
        (gs_concrete_entry_growth_constant * U)) ^ r *
      (of_nat r :: real) powr (of_nat r + 2) \<le>
      (gs_house_growth_base * U ^ 2) ^ r *
        (of_nat r :: real) powr (of_nat r + 3 / 2)"
    using gs_house_growth_absorb[OF rpos Fnonneg, of "gs_concrete_entry_growth_constant * U"]
      Kone by (simp add: gs_house_growth_base_def power2_eq_square algebra_simps)
  show ?thesis using raw absorb by linarith
qed

definition gs_point_scale_base :: real where
  "gs_point_scale_base =
    (of_int (abs (gs_c1 d)) :: real) *
      (of_int (abs (gs_c1 d)) :: real) ^ (4 * gs_m h * gs_m h)"

definition gs_point_fixed_base :: real where
  "gs_point_fixed_base = gs_point_scale_base *
    inverse (cmod (gs_z d)) *
    exp (of_nat (gs_m h) * (2 * of_nat (gs_m h) + 1) *
      (1 + cmod (gs_b d)) * cmod (gs_z d)) *
    (2 * of_nat (gs_m h) + 1) ^ (gs_m h)"

lemma gs_point_fixed_base_pos:
  "0 < gs_point_fixed_base"
proof -
  have Cge: "1 \<le> (of_int (abs (gs_c1 d)) :: real)"
    using gelfond_schneider_data_c1_ge1[OF d] by simp
  have zpos: "0 < cmod (gs_z d)"
    using gelfond_schneider_data_z_nonzero[OF d] by simp
  show ?thesis using Cge zpos
    by (simp add: gs_point_fixed_base_def gs_point_scale_base_def)
qed

lemma gs_rho_fixed_factor_le_growth:
  assumes c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  shows "(of_int (abs c) :: real) * cmod (gs_z d powi (- int r)) *
    exp ((of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)) *
      (of_nat (gs_m h) * (1 + of_nat r / of_nat q))) *
    (2 * of_nat (gs_m h) + 1) ^ (gs_m h * r) \<le>
    gs_point_fixed_base ^ r"
proof -
  let ?C = "(of_int (abs (gs_c1 d)) :: real)"
  let ?m = "gs_m h"
  let ?Z = "inverse (cmod (gs_z d))"
  let ?X = "exp (of_nat ?m * (2 * of_nat ?m + 1) *
      (1 + cmod (gs_b d)) * cmod (gs_z d))"
  let ?P = "2 * of_nat ?m + 1 :: real"
  have prod_ge1: "1 \<le> c14 * c5"
  proof -
    have "(1::real) * 1 \<le> c14 * c5"
      by (intro mult_mono) (use c14_ge1 c5_gt1 in auto)
    then show ?thesis by simp
  qed
  have nle_choice: "gs_n h (gs_q_choice h (c14 * c5)) \<le> r"
    using nle by (simp add: q_def)
  have qle: "q \<le> 2 * ?m * r"
    using gs_q_choice_le_two_mr[OF hpos prod_ge1 nle_choice]
    by (simp add: q_def)
  have Cge: "1 \<le> ?C"
    using gelfond_schneider_data_c1_ge1[OF d] by simp
  have scale: "(of_int (abs c) :: real) \<le> gs_point_scale_base ^ r"
  proof -
    have eq: "(of_int (abs c) :: real) = ?C ^ r * ?C ^ (2 * ?m * q)"
      using c_def by (simp add: abs_mult power_abs)
    show ?thesis using gs_scale_factor_le_r_power[OF qle Cge]
      by (simp only: eq gs_point_scale_base_def)
  qed
  have z_eq: "cmod (gs_z d powi (- int r)) = ?Z ^ r"
    by (rule gs_negative_powi_norm[OF gelfond_schneider_data_z_nonzero[OF d]])
  have exp_le: "exp ((of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)) *
      (of_nat ?m * (1 + of_nat r / of_nat q))) \<le> ?X ^ r"
    by (rule gs_aux_exp_growth_le[OF qpos qle])
  have p_eq: "?P ^ (?m * r) = (?P ^ ?m) ^ r"
    by (simp add: power_mult)
  have nonneg: "0 \<le> (of_int (abs c) :: real)" by simp
  have all: "(of_int (abs c) :: real) * cmod (gs_z d powi (- int r)) *
    exp ((of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)) *
      (of_nat ?m * (1 + of_nat r / of_nat q))) * ?P ^ (?m * r) \<le>
    gs_point_scale_base ^ r * ?Z ^ r * ?X ^ r * (?P ^ ?m) ^ r"
    using scale exp_le z_eq p_eq
    by (intro mult_mono) (use nonneg in auto)
  show ?thesis using all
    by (simp add: gs_point_fixed_base_def power_mult_distrib ac_simps)
qed

lemma gs_rho_cmod_le_of_bounded_vec:
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v =
    0\<^sub>v (gs_m h * gs_n h q)"
  assumes repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes req: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  assumes rho_def: "rho = (of_int c :: complex) *
    (gs_z d powi (- int r) *
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
  shows "cmod rho \<le> of_int (abs c) * cmod (gs_z d powi (- int r)) *
    (fact r * (of_nat (q * q) *
      ((of_int B :: real) * of_nat D * power_basis_entry_bound) *
      exp ((of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)) *
        (of_nat (gs_m h) * (1 + of_nat r / of_nat q))) /
      (of_nat (gs_m h) * of_nat r / of_nat q) ^ (gs_m h * r)) *
      (2 * of_nat (gs_m h) + 1) ^ (gs_m h * r))"
proof -
  let ?B = "fact r * (of_nat (q * q) *
      ((of_int B :: real) * of_nat D * power_basis_entry_bound) *
      exp ((of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)) *
        (of_nat (gs_m h) * (1 + of_nat r / of_nat q))) /
      (of_nat (gs_m h) * of_nat r / of_nat q) ^ (gs_m h * r)) *
      (2 * of_nat (gs_m h) + 1) ^ (gs_m h * r)"
  have c5ge: "1 \<le> c5" using c5_gt1 by linarith
  have c15ge: "1 \<le> c14 * c5"
  proof -
    have "1 * 1 \<le> c14 * c5"
      using c14_ge1 c5ge by (intro mult_mono) simp_all
    then show ?thesis by simp
  qed
  have qge: "4 \<le> q"
    unfolding q_def by (rule gs_q_choice_ge_four[OF hpos c15ge])
  have bal: "q * q = 2 * gs_m h * gs_n h q"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have coeff_nz: "\<exists>t<q * q. Matrix.vec_index v t \<noteq> 0"
    using v_carrier v_nz by force
  have ker_coeff: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v
      gs_coeff_vec q (\<lambda>t. Matrix.vec_index v t) =
      0\<^sub>v (gs_m h * gs_n h q)"
    by (simp add: gs_coeff_vec_eqI[OF v_carrier] v_ker)
  have min_ord: "gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t) \<ge> gs_n h q"
    by (rule gs_min_order_ge_of_row_scaled_kernel_nonzero[OF d qpos gs_m_pos npos coeff_nz ker_coeff])
  have nle: "gs_n h q \<le> r"
    using min_ord req by linarith
  have rpos: "r > 0"
    by (rule rho_order_pos[OF v_carrier v_nz v_ker req])
  have nz: "gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t) \<noteq> (\<lambda>_. 0)"
    by (rule gs_aux_fun_vec_nonzero[OF d qpos coeff_nz])
  have basis_bnd: "\<And>j. j < D \<Longrightarrow>
    cmod (basis j (emb i0)) \<le> power_basis_entry_bound"
    by (rule basis_cmod_le_power_basis_entry_bound[OF i0lt])
  have deriv_bound: "cmod (((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
      (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<le> ?B"
    by (rule gs_bounded_vec_min_order_derivative_bound[OF qge bal nle gs_m_pos rpos Dpos
        repr x_carrier x_bnd B_nonneg power_basis_entry_bound_nonneg basis_bnd nz req])
  have "cmod rho = of_int (abs c) * cmod (gs_z d powi (- int r)) *
      cmod (((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
    by (simp add: rho_def norm_mult)
  also have "... \<le> of_int (abs c) * cmod (gs_z d powi (- int r)) * ?B"
    using deriv_bound by (intro mult_left_mono mult_right_mono) auto
  finally show ?thesis .
qed

definition gs_point_growth_prefactor :: real where
  "gs_point_growth_prefactor =
    2 * of_nat (gs_m h) *
      (4 * of_nat (gs_m h) * of_nat D *
        (1 + gs_witness_growth_weight)) *
      (of_nat D * power_basis_entry_bound)"

definition gs_point_growth_base :: real where
  "gs_point_growth_base =
    2 * max 1 gs_point_growth_prefactor *
      (gs_concrete_entry_growth_constant * gs_point_fixed_base)"

lemma gs_point_growth_base_pos:
  "0 < gs_point_growth_base"
  using gs_concrete_entry_growth_constant_ge_one gs_point_fixed_base_pos
  by (simp add: gs_point_growth_base_def)

lemma gs_rho_cmod_le_growth_absorbed:
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v =
    0\<^sub>v (gs_m h * gs_n h q)"
  assumes repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes req: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  assumes rho_def: "rho = (of_int c :: complex) *
    (gs_z d powi (- int r) *
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
  assumes c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  assumes Bbound: "(of_int B :: real) \<le>
    (4 * of_nat (gs_m h) * of_nat D *
      (1 + gs_witness_growth_weight)) * of_nat r *
      gs_concrete_entry_growth_constant ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
  shows "cmod rho \<le> gs_point_growth_base ^ r *
    (of_nat r :: real) powr
      (of_nat r * (3 - of_nat (gs_m h)) / 2 + 3 / 2)"
proof -
  let ?m = "gs_m h"
  let ?R = "(of_nat r :: real)"
  let ?W = "4 * of_nat ?m * of_nat D *
      (1 + gs_witness_growth_weight) :: real"
  let ?E = "of_nat D * power_basis_entry_bound :: real"
  let ?K = "gs_concrete_entry_growth_constant"
  let ?L = "gs_point_fixed_base"
  let ?radius = "(of_nat ?m * ?R / of_nat q :: real) ^ (?m * r)"
  let ?G = "(of_int (abs c) :: real) * cmod (gs_z d powi (- int r)) *
    exp ((of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)) *
      (of_nat ?m * (1 + ?R / of_nat q))) *
    (2 * of_nat ?m + 1) ^ (?m * r)"
  have bal: "q * q = 2 * ?m * gs_n h q"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have qsq: "q * q \<le> 2 * ?m * r"
  proof -
    have "2 * ?m * gs_n h q \<le> 2 * ?m * r"
      by (rule mult_left_mono[OF nle]) simp
    then show ?thesis using bal by simp
  qed
  have mge: "2 \<le> ?m" by (simp add: gs_m_def)
  have radbound: "?R powr (of_nat ?m * ?R / 2) \<le> ?radius"
    by (rule gs_balanced_radius_power_ge[OF qpos mge rpos qsq])
  have Gbound: "?G \<le> ?L ^ r"
    by (rule gs_rho_fixed_factor_le_growth[OF c_def nle rpos])
  have Gnonneg: "0 \<le> ?G" by simp
  have Wnonneg: "0 \<le> ?W"
    using power_basis_inverse_bound_nonneg power_basis_entry_bound_nonneg
    by (simp add: gs_witness_growth_weight_def)
  have Enonneg: "0 \<le> ?E"
    using power_basis_entry_bound_nonneg by simp
  have Knonneg: "0 \<le> ?K"
    using gs_concrete_entry_growth_constant_ge_one by linarith
  have Lnonneg: "0 \<le> ?L"
    using gs_point_fixed_base_pos by linarith
  have Bnonneg: "0 \<le> (of_int B :: real)" using B_nonneg by simp
  note raw = gs_rho_cmod_le_of_bounded_vec[OF v_carrier v_nz v_ker repr
    x_carrier x_bnd B_nonneg req rho_def]
  have raw_refactor: "cmod rho \<le>
      (((of_nat (q * q) :: real) * of_int B * fact r * ?G) / ?radius) * ?E"
    using raw by (simp add: ac_simps)
  have point_num: "(((of_nat (q * q) :: real) * of_int B * fact r * ?G) /
      ?radius) \<le> (2 * of_nat ?m * ?W) * (?K * ?L) ^ r *
        ?R powr (?R * (3 - of_nat ?m) / 2 + 2)"
    by (rule gs_point_growth_multiply[OF rpos qsq Bnonneg Gnonneg Wnonneg
      Knonneg Lnonneg Bbound Gbound radbound])
  have point_pref: "cmod rho \<le> gs_point_growth_prefactor *
      (?K * ?L) ^ r * ?R powr (?R * (3 - of_nat ?m) / 2 + 2)"
  proof -
    have "(((of_nat (q * q) :: real) * of_int B * fact r * ?G) /
        ?radius) * ?E \<le> ((2 * of_nat ?m * ?W) * (?K * ?L) ^ r *
          ?R powr (?R * (3 - of_nat ?m) / 2 + 2)) * ?E"
      by (rule mult_right_mono[OF point_num Enonneg])
    then show ?thesis using raw_refactor
      by (simp add: gs_point_growth_prefactor_def ac_simps)
  qed
  have Wscaled: "0 \<le> 2 * of_nat ?m * ?W"
    by (rule mult_nonneg_nonneg) (use Wnonneg in auto)
  have pref_eq: "gs_point_growth_prefactor = (2 * of_nat ?m * ?W) * ?E"
    by (simp only: gs_point_growth_prefactor_def)
  have Fnonneg: "0 \<le> gs_point_growth_prefactor"
  proof -
    have "0 \<le> (2 * of_nat ?m * ?W) * ?E"
      by (rule mult_nonneg_nonneg[OF Wscaled Enonneg])
    then show ?thesis by (simp only: pref_eq)
  qed
  have absorb: "gs_point_growth_prefactor * (?K * ?L) ^ r *
      ?R powr (?R * (3 - of_nat ?m) / 2 + 2) \<le>
      gs_point_growth_base ^ r *
        ?R powr (?R * (3 - of_nat ?m) / 2 + 3 / 2)"
    using gs_point_growth_absorb[OF rpos Fnonneg, of "?K * ?L"
      "?R * (3 - of_nat ?m) / 2"] Knonneg Lnonneg
    by (simp add: gs_point_growth_base_def)
  show ?thesis using point_pref absorb by linarith
qed

lemma gs_rho_cmod_le_growth_absorbed_with_factor:
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v =
    0\<^sub>v (gs_m h * gs_n h q)"
  assumes repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes req: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  assumes rho_def: "rho = (of_int c :: complex) *
    (gs_z d powi (- int r) *
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
  assumes c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  assumes Uone: "1 \<le> U"
  assumes Bbound: "(of_int B :: real) \<le>
    (4 * of_nat (gs_m h) * of_nat D *
      (1 + gs_witness_growth_weight)) * of_nat r *
      (gs_concrete_entry_growth_constant * U) ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
  shows "cmod rho \<le> (gs_point_growth_base * U) ^ r *
    (of_nat r :: real) powr
      (of_nat r * (3 - of_nat (gs_m h)) / 2 + 3 / 2)"
proof -
  let ?m = "gs_m h"
  let ?R = "(of_nat r :: real)"
  let ?W = "4 * of_nat ?m * of_nat D *
      (1 + gs_witness_growth_weight) :: real"
  let ?E = "of_nat D * power_basis_entry_bound :: real"
  let ?K = "gs_concrete_entry_growth_constant * U"
  let ?L = "gs_point_fixed_base"
  let ?radius = "(of_nat ?m * ?R / of_nat q :: real) ^ (?m * r)"
  let ?G = "(of_int (abs c) :: real) * cmod (gs_z d powi (- int r)) *
    exp ((of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)) *
      (of_nat ?m * (1 + ?R / of_nat q))) *
    (2 * of_nat ?m + 1) ^ (?m * r)"
  have bal: "q * q = 2 * ?m * gs_n h q"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have qsq: "q * q \<le> 2 * ?m * r"
  proof -
    have "2 * ?m * gs_n h q \<le> 2 * ?m * r"
      by (rule mult_left_mono[OF nle]) simp
    then show ?thesis using bal by simp
  qed
  have mge: "2 \<le> ?m" by (simp add: gs_m_def)
  have radbound: "?R powr (of_nat ?m * ?R / 2) \<le> ?radius"
    by (rule gs_balanced_radius_power_ge[OF qpos mge rpos qsq])
  have Gbound: "?G \<le> ?L ^ r"
    by (rule gs_rho_fixed_factor_le_growth[OF c_def nle rpos])
  have Gnonneg: "0 \<le> ?G" by simp
  have Wnonneg: "0 \<le> ?W"
    using power_basis_inverse_bound_nonneg power_basis_entry_bound_nonneg
    by (simp add: gs_witness_growth_weight_def)
  have Enonneg: "0 \<le> ?E"
    using power_basis_entry_bound_nonneg by simp
  have Knonneg: "0 \<le> ?K"
    using gs_concrete_entry_growth_constant_ge_one Uone by simp
  have Lnonneg: "0 \<le> ?L"
    using gs_point_fixed_base_pos by linarith
  have Bnonneg: "0 \<le> (of_int B :: real)" using B_nonneg by simp
  note raw = gs_rho_cmod_le_of_bounded_vec[OF v_carrier v_nz v_ker repr
    x_carrier x_bnd B_nonneg req rho_def]
  have raw_refactor: "cmod rho \<le>
      (((of_nat (q * q) :: real) * of_int B * fact r * ?G) / ?radius) * ?E"
    using raw by (simp add: ac_simps)
  have point_num: "(((of_nat (q * q) :: real) * of_int B * fact r * ?G) /
      ?radius) \<le> (2 * of_nat ?m * ?W) * (?K * ?L) ^ r *
        ?R powr (?R * (3 - of_nat ?m) / 2 + 2)"
    by (rule gs_point_growth_multiply[OF rpos qsq Bnonneg Gnonneg Wnonneg
      Knonneg Lnonneg Bbound Gbound radbound])
  have point_pref: "cmod rho \<le> gs_point_growth_prefactor *
      (?K * ?L) ^ r * ?R powr (?R * (3 - of_nat ?m) / 2 + 2)"
  proof -
    have "(((of_nat (q * q) :: real) * of_int B * fact r * ?G) /
        ?radius) * ?E \<le> ((2 * of_nat ?m * ?W) * (?K * ?L) ^ r *
          ?R powr (?R * (3 - of_nat ?m) / 2 + 2)) * ?E"
      by (rule mult_right_mono[OF point_num Enonneg])
    then show ?thesis using raw_refactor
      by (simp add: gs_point_growth_prefactor_def ac_simps)
  qed
  have Wscaled: "0 \<le> 2 * of_nat ?m * ?W"
    by (rule mult_nonneg_nonneg) (use Wnonneg in auto)
  have pref_eq: "gs_point_growth_prefactor = (2 * of_nat ?m * ?W) * ?E"
    by (simp only: gs_point_growth_prefactor_def)
  have Fnonneg: "0 \<le> gs_point_growth_prefactor"
  proof -
    have "0 \<le> (2 * of_nat ?m * ?W) * ?E"
      by (rule mult_nonneg_nonneg[OF Wscaled Enonneg])
    then show ?thesis by (simp only: pref_eq)
  qed
  have base_eq: "gs_point_growth_base * U =
      2 * max 1 gs_point_growth_prefactor * (?K * ?L)"
    by (simp add: gs_point_growth_base_def algebra_simps)
  have KLnonneg: "0 \<le> ?K * ?L" using Knonneg Lnonneg by simp
  have absorb: "gs_point_growth_prefactor * (?K * ?L) ^ r *
      ?R powr (?R * (3 - of_nat ?m) / 2 + 2) \<le>
      (gs_point_growth_base * U) ^ r *
        ?R powr (?R * (3 - of_nat ?m) / 2 + 3 / 2)"
    using gs_point_growth_absorb[OF rpos Fnonneg KLnonneg, of
      "?R * (3 - of_nat ?m) / 2"]
    by (simp only: base_eq)
  show ?thesis using point_pref absorb by linarith
qed

lemma gs_norm_upper_from_concrete_house_point:
  assumes hD: "h = D"
  assumes xK: "rho \<in> K"
  assumes ai: "algebraic_int rho"
  assumes rpos: "r > 0"
  assumes house_bound: "gs_house rho \<le>
    gs_house_growth_base ^ r *
      (of_nat r :: real) powr (of_nat r + 3 / 2)"
  assumes point_bound: "cmod rho \<le> gs_point_growth_base ^ r *
    (of_nat r :: real) powr
      (of_nat r * (3 - of_nat (gs_m h)) / 2 + 3 / 2)"
  assumes c14_big: "gs_house_growth_base ^ (D - 1) *
    gs_point_growth_base \<le> c14"
  shows "gs_abs_galois_norm rho \<le>
    c14 powr of_nat r *
      (of_nat r :: real) powr (- of_nat r / 2 + 3 * of_nat h / 2)"
proof -
  have house_pos: "0 < gs_house_growth_base"
    by (rule gs_house_growth_base_pos)
  have point_pos: "0 < gs_point_growth_base"
    by (rule gs_point_growth_base_pos)
  have emb0_rho: "emb i0 rho = rho"
    using xK by (simp add: emb0 identity_apply_in_K)
  have point_power: "gs_point_growth_base ^ r =
      gs_point_growth_base powr of_nat r"
    by (simp only: powr_realpow[OF point_pos])
  have point_exponent: "(of_nat r :: real) *
      (3 - of_nat (gs_m h)) / 2 + 3 / 2 =
      of_nat r * (3 - of_nat (2 * D + 2)) / 2 + 3 / 2"
    using hD by (simp add: gs_m_def)
  have point_le: "cmod (emb i0 rho) \<le>
      gs_point_growth_base powr of_nat r *
      (of_nat r :: real) powr
        (of_nat r * (3 - of_nat (2 * D + 2)) / 2 + 3 / 2)"
    using point_bound by (simp only: emb0_rho point_power point_exponent)
  have house_le: "gs_house rho \<le>
      gs_house_growth_base powr of_nat r *
        (of_nat r :: real) powr (of_nat r + 3 / 2)"
    using house_bound by (simp add: powr_realpow[OF house_pos])
  have norm_le: "gs_abs_galois_norm rho \<le>
      (gs_house_growth_base ^ (D - 1) * gs_point_growth_base) powr of_nat r *
        (of_nat r :: real) powr (- of_nat r / 2 + 3 * of_nat D / 2)"
    by (rule gs_abs_galois_norm_le_from_analytic_house_bounds[OF i0lt xK ai
      house_pos point_pos rpos house_le point_le])
  have base_nonneg: "0 \<le> gs_house_growth_base ^ (D - 1) * gs_point_growth_base"
    using house_pos point_pos by simp
  have base_le: "(gs_house_growth_base ^ (D - 1) * gs_point_growth_base)
      powr of_nat r \<le> c14 powr of_nat r"
    by (rule powr_mono2[OF _ base_nonneg c14_big]) simp
  have rp_nonneg: "0 \<le> (of_nat r :: real) powr
      (- of_nat r / 2 + 3 * of_nat D / 2)"
    by simp
  show ?thesis using norm_le base_le rp_nonneg hD
    by (intro order_trans[OF norm_le]) (simp add: mult_right_mono)
qed

lemma gs_norm_upper_from_concrete_house_point_with_factor:
  assumes hD: "h = D"
  assumes xK: "rho \<in> K"
  assumes ai: "algebraic_int rho"
  assumes rpos: "r > 0"
  assumes Uone: "1 \<le> U"
  assumes house_bound: "gs_house rho \<le>
    (gs_house_growth_base * U ^ 2) ^ r *
      (of_nat r :: real) powr (of_nat r + 3 / 2)"
  assumes point_bound: "cmod rho \<le> (gs_point_growth_base * U) ^ r *
    (of_nat r :: real) powr
      (of_nat r * (3 - of_nat (gs_m h)) / 2 + 3 / 2)"
  assumes c14_big: "(gs_house_growth_base * U ^ 2) ^ (D - 1) *
    (gs_point_growth_base * U) \<le> c14"
  shows "gs_abs_galois_norm rho \<le>
    c14 powr of_nat r *
      (of_nat r :: real) powr (- of_nat r / 2 + 3 * of_nat h / 2)"
proof -
  have house_pos: "0 < (gs_house_growth_base * U ^ 2)"
    using gs_house_growth_base_pos Uone by simp
  have point_pos: "0 < (gs_point_growth_base * U)"
    using gs_point_growth_base_pos Uone by simp
  have emb0_rho: "emb i0 rho = rho"
    using xK by (simp add: emb0 identity_apply_in_K)
  have point_power: "(gs_point_growth_base * U) ^ r =
      (gs_point_growth_base * U) powr of_nat r"
    by (simp only: powr_realpow[OF point_pos])
  have point_exponent: "(of_nat r :: real) *
      (3 - of_nat (gs_m h)) / 2 + 3 / 2 =
      of_nat r * (3 - of_nat (2 * D + 2)) / 2 + 3 / 2"
    using hD by (simp add: gs_m_def)
  have point_le: "cmod (emb i0 rho) \<le>
      (gs_point_growth_base * U) powr of_nat r *
      (of_nat r :: real) powr
        (of_nat r * (3 - of_nat (2 * D + 2)) / 2 + 3 / 2)"
    using point_bound by (simp only: emb0_rho point_power point_exponent)
  have house_le: "gs_house rho \<le>
      (gs_house_growth_base * U ^ 2) powr of_nat r *
        (of_nat r :: real) powr (of_nat r + 3 / 2)"
    using house_bound by (simp add: powr_realpow[OF house_pos])
  have norm_le: "gs_abs_galois_norm rho \<le>
      ((gs_house_growth_base * U ^ 2) ^ (D - 1) * (gs_point_growth_base * U)) powr of_nat r *
        (of_nat r :: real) powr (- of_nat r / 2 + 3 * of_nat D / 2)"
    by (rule gs_abs_galois_norm_le_from_analytic_house_bounds[OF i0lt xK ai
      house_pos point_pos rpos house_le point_le])
  have base_nonneg: "0 \<le> (gs_house_growth_base * U ^ 2) ^ (D - 1) * (gs_point_growth_base * U)"
    using house_pos point_pos by simp
  have base_le: "((gs_house_growth_base * U ^ 2) ^ (D - 1) * (gs_point_growth_base * U))
      powr of_nat r \<le> c14 powr of_nat r"
    by (rule powr_mono2[OF _ base_nonneg c14_big]) simp
  have rp_nonneg: "0 \<le> (of_nat r :: real) powr
      (- of_nat r / 2 + 3 * of_nat D / 2)"
    by simp
  show ?thesis using norm_le base_le rp_nonneg hD
    by (intro order_trans[OF norm_le]) (simp add: mult_right_mono)
qed

lemma gs_rho_upper_from_concrete_witness:
  assumes hD: "h = D"
  assumes A_choice: "A = gs_concrete_entry_bound"
  assumes c14_big: "gs_house_growth_base ^ (D - 1) *
    gs_point_growth_base \<le> c14"
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v =
    0\<^sub>v (gs_m h * gs_n h q)"
  assumes repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec
    (2 * int (q * q * D) *
      max 1 (ceiling (of_nat (card E) * power_basis_inverse_bound * A *
        power_basis_entry_bound)))"
  assumes req: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  assumes rho_def: "rho = (of_int c :: complex) *
    (gs_z d powi (- int r) *
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
  assumes c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  assumes ai: "algebraic_int rho"
  assumes xK: "rho \<in> K"
  shows "gs_abs_galois_norm rho \<le>
    c14 powr of_nat r *
      (of_nat r :: real) powr (- of_nat r / 2 + 3 * of_nat h / 2)"
proof -
  let ?B = "2 * int (q * q * D) *
      max 1 (ceiling (of_nat (card E) * power_basis_inverse_bound * A *
        power_basis_entry_bound))"
  have Bnonneg: "0 \<le> ?B" by simp
  have Bbound: "(of_int ?B :: real) \<le>
    (4 * of_nat (gs_m h) * of_nat D *
      (1 + gs_witness_growth_weight)) * of_nat r *
      gs_concrete_entry_growth_constant ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
    using gs_witness_bound_le_growth_simple[OF nle rpos]
    by (simp only: A_choice)
  have house: "gs_house rho \<le>
    gs_house_growth_base ^ r *
      (of_nat r :: real) powr (of_nat r + 3 / 2)"
    by (rule gs_house_rho_le_growth_absorbed[OF repr x_carrier x_bnd
      Bnonneg ai xK rho_def c_def nle rpos Bbound])
  have point: "cmod rho \<le> gs_point_growth_base ^ r *
    (of_nat r :: real) powr
      (of_nat r * (3 - of_nat (gs_m h)) / 2 + 3 / 2)"
    by (rule gs_rho_cmod_le_growth_absorbed[OF v_carrier v_nz v_ker repr
      x_carrier x_bnd Bnonneg req rho_def c_def nle rpos Bbound])
  show ?thesis
    by (rule gs_norm_upper_from_concrete_house_point[OF hD xK ai rpos
      house point c14_big])
qed

lemma gs_rho_upper_from_concrete_witness_with_denominator:
  assumes hD: "h = D"
  assumes A_choice: "A = gs_concrete_entry_bound"
  assumes Tp: "T > (0::int)"
  assumes c14_big:
    "(gs_house_growth_base *
      (of_int (T ^ (1 + 4 * gs_m h * gs_m h + D)) :: real) ^ 2) ^ (D - 1) *
      (gs_point_growth_base *
        of_int (T ^ (1 + 4 * gs_m h * gs_m h + D))) \<le> c14"
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v =
    0\<^sub>v (gs_m h * gs_n h q)"
  assumes repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec
    (2 * int (q * q * D) *
      max 1 (ceiling (of_nat (card E) * power_basis_inverse_bound *
        (of_int (T ^ (gs_n h q + 2 * (gs_m h * q) + D)) * A *
          power_basis_entry_bound))))"
  assumes req: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  assumes rho_def: "rho = (of_int c :: complex) *
    (gs_z d powi (- int r) *
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
  assumes c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  assumes ai: "algebraic_int rho"
  assumes xK: "rho \<in> K"
  shows "gs_abs_galois_norm rho \<le>
    c14 powr of_nat r *
      (of_nat r :: real) powr (- of_nat r / 2 + 3 * of_nat h / 2)"
proof -
  let ?U = "of_int (T ^ (1 + 4 * gs_m h * gs_m h + D)) :: real"
  have Tone: "1 \<le> T" using Tp by simp
  have Uone: "1 \<le> ?U"
  proof -
    have "1 \<le> T ^ (1 + 4 * gs_m h * gs_m h + D)"
      by (rule one_le_power[OF Tone])
    then show ?thesis by (simp only: of_int_le_iff)
  qed
  let ?B = "2 * int (q * q * D) *
      max 1 (ceiling (of_nat (card E) * power_basis_inverse_bound *
        (of_int (T ^ (gs_n h q + 2 * (gs_m h * q) + D)) * A *
          power_basis_entry_bound)))"
  have Bnonneg: "0 \<le> ?B" by simp
  have Bbound: "(of_int ?B :: real) \<le>
    (4 * of_nat (gs_m h) * of_nat D *
      (1 + gs_witness_growth_weight)) * of_nat r *
      (gs_concrete_entry_growth_constant * ?U) ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
    using gs_witness_bound_le_growth_with_denominator[OF nle rpos Tp]
    by (simp only: A_choice)
  have house: "gs_house rho \<le>
    (gs_house_growth_base * ?U ^ 2) ^ r *
      (of_nat r :: real) powr (of_nat r + 3 / 2)"
    by (rule gs_house_rho_le_growth_absorbed_with_factor[OF repr x_carrier x_bnd
      Bnonneg ai xK rho_def c_def nle rpos Uone Bbound])
  have point: "cmod rho \<le> (gs_point_growth_base * ?U) ^ r *
    (of_nat r :: real) powr
      (of_nat r * (3 - of_nat (gs_m h)) / 2 + 3 / 2)"
    by (rule gs_rho_cmod_le_growth_absorbed_with_factor[OF v_carrier v_nz v_ker repr
      x_carrier x_bnd Bnonneg req rho_def c_def nle rpos Uone Bbound])
  show ?thesis
    by (rule gs_norm_upper_from_concrete_house_point_with_factor[OF hD xK ai rpos
      Uone house point c14_big])
qed

lemma gs_rho_upper_verified:
  assumes hD: "h = D"
  assumes A_choice: "A = gs_concrete_entry_bound"
  assumes c14_big: "gs_house_growth_base ^ (D - 1) *
    gs_point_growth_base \<le> c14"
  shows "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec
            (2 * int (q * q * D) *
              max 1 (ceiling (of_nat (card E) * power_basis_inverse_bound * A * power_basis_entry_bound))) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      gs_abs_galois_norm rho \<le>
        c14 powr of_nat r *
        of_nat r powr ((- of_nat r / 2 + 3 * of_nat h / 2) :: real)"
proof -
  fix v :: "complex vec" and x :: "int vec" and r :: nat and c :: int and rho :: complex
  assume v_carrier: "v \<in> carrier_vec (q * q)"
  assume v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assume v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v =
    0\<^sub>v (gs_m h * gs_n h q)"
  assume vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
  assume repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))"
  assume x_carrier: "x \<in> carrier_vec (q * q * D)"
  assume x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
  assume x_bnd: "x \<in> Bounded_vec
    (2 * int (q * q * D) *
      max 1 (ceiling (of_nat (card E) * power_basis_inverse_bound * A *
        power_basis_entry_bound)))"
  assume req: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  assume deriv_nz: "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
    (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
  assume c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
  assume rho_def: "rho = (of_int c :: complex) *
    (gs_z d powi (- int r) *
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
  have nle: "gs_n h q \<le> r"
    by (rule rho_order_ge_n[OF v_carrier v_nz v_ker req])
  have rpos: "r > 0"
    by (rule rho_order_pos[OF v_carrier v_nz v_ker req])
  have ai: "algebraic_int rho"
    by (rule rho_algebraic_int_nonzero(1)[OF v_carrier v_nz vint req
      deriv_nz c_def rho_def])
  have xK: "rho \<in> K"
    by (rule rho_in_K[OF repr rho_def])
  show "gs_abs_galois_norm rho \<le>
    c14 powr of_nat r *
      (of_nat r :: real) powr (- of_nat r / 2 + 3 * of_nat h / 2)"
    by (rule gs_rho_upper_from_concrete_witness[OF hD A_choice c14_big
      v_carrier v_nz v_ker repr x_carrier x_bnd req rho_def c_def
      nle rpos ai xK])
qed

end

locale gelfond_schneider_power_basis_field_norm_target =
  gelfond_schneider_power_basis_field_norm_estimates K eta D emb ca cb cw d q h i0 A c5 c14
  for K :: "complex set"
  and eta :: complex
  and D :: nat
  and emb :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  and ca cb cw :: "nat \<Rightarrow> complex"
  and d
  and q h i0 :: nat
  and C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  and A c5 c14 :: real +
  assumes mult_repr:
    "\<And>u t j e. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow> e \<in> E \<Longrightarrow>
      e (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t)) * basis j e =
        (\<Sum>k<D. of_int (C u t k j) * basis k e)"
  assumes entry_bnd:
    "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow>
      EH.ehouse (\<lambda>e. e (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) \<le> A"
  assumes A_nonneg: "0 \<le> A"
  assumes rho_upper:
    "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec
            (2 * int (q * q * D) *
              max 1 (ceiling (of_nat (card E) * power_basis_inverse_bound * A * power_basis_entry_bound))) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      gs_abs_galois_norm rho \<le>
        c14 powr of_nat r *
        of_nat r powr ((- of_nat r / 2 + 3 * of_nat h / 2) :: real)"
begin

sublocale TARGET: gelfond_schneider_number_field_norm_target
  E D emb basis repr_coeff eta ca cb cw d q h "emb i0" Aemb C power_basis_inverse_bound A
  power_basis_entry_bound gs_abs_galois_norm c5 c14
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
    by (rule row_scaled_entry0)
  show "\<And>u t j e. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow> e \<in> E \<Longrightarrow>
      Aemb u t e * basis j e = (\<Sum>k<D. of_int (C u t k j) * basis k e)"
    unfolding Aemb_def by (rule mult_repr)
  show "\<And>k i. k < D \<Longrightarrow> i < D \<Longrightarrow> cmod (REC.inverse_basis_matrix_entry k i) \<le> power_basis_inverse_bound"
    by (rule inverse_basis_matrix_entry_le_power_basis_inverse_bound)
  show "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> EH.ehouse (Aemb u t) \<le> A"
    unfolding Aemb_def by (rule entry_bnd)
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
  show "0 \<le> power_basis_inverse_bound"
    by (rule power_basis_inverse_bound_nonneg)
  show "0 \<le> A"
    by (rule A_nonneg)
  show "0 \<le> power_basis_entry_bound"
    by (rule power_basis_entry_bound_nonneg)
  show "h > 0"
    by (rule hpos)
  show "q = gs_q_choice h (c14 * c5)"
    by (rule q_def)
  show "1 \<le> c14"
    by (rule c14_ge1)
  show "1 \<le> c5"
    using c5_gt1 by linarith
  show "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec
            (2 * int (q * q * D) *
              max 1 (ceiling (of_nat (card E) * power_basis_inverse_bound * A * power_basis_entry_bound))) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      0 < gs_abs_galois_norm rho"
    by (metis (no_types, lifting) ext gs_abs_galois_norm_pos rho_algebraic_int_nonzero(2)
        rho_in_K)
  show "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec
            (2 * int (q * q * D) *
              max 1 (ceiling (of_nat (card E) * power_basis_inverse_bound * A * power_basis_entry_bound))) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      gs_abs_galois_norm rho \<le>
        c14 powr of_nat r *
        of_nat r powr ((- of_nat r / 2 + 3 * of_nat h / 2) :: real)"
    by (rule rho_upper)
  show "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec
            (2 * int (q * q * D) *
              max 1 (ceiling (of_nat (card E) * power_basis_inverse_bound * A * power_basis_entry_bound))) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      inverse (gs_abs_galois_norm rho) < c5 powr of_nat r"
    by (metis (no_types, lifting) ext c5_gt1 inverse_gs_abs_galois_norm_lt_powr
        rho_algebraic_int_nonzero(1,2) rho_in_K rho_order_pos)
qed

theorem coordinate_contradiction:
  shows False
  by (rule TARGET.coordinate_contradiction)

end

locale gelfond_schneider_power_basis_field_norm_verified =
  gelfond_schneider_power_basis_field_norm_estimates K eta D emb ca cb cw d q h i0 A c5 c14
  for K :: "complex set"
  and eta :: complex
  and D :: nat
  and emb :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  and ca cb cw :: "nat \<Rightarrow> complex"
  and d
  and q h i0 :: nat
  and C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  and A c5 c14 :: real +
  assumes mult_repr:
    "\<And>u t j e. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow> e \<in> E \<Longrightarrow>
      e (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t)) * basis j e =
        (\<Sum>k<D. of_int (C u t k j) * basis k e)"
  assumes hD: "h = D"
  assumes A_choice: "A = gs_concrete_entry_bound"
  assumes c14_big: "gs_house_growth_base ^ (D - 1) *
    gs_point_growth_base \<le> c14"
begin

sublocale CHECKED: gelfond_schneider_power_basis_field_norm_target
  K eta D emb ca cb cw d q h i0 C A c5 c14
proof unfold_locales
  show "\<And>u t j e. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow> e \<in> E \<Longrightarrow>
      e (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t)) * basis j e =
        (\<Sum>k<D. of_int (C u t k j) * basis k e)"
    by (rule mult_repr)
  show "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow>
      EH.ehouse (\<lambda>e. e (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) \<le> A"
  proof -
    fix u t
    assume up: "u < gs_m h * gs_n h q"
    assume tq: "t < q * q"
    have bound: "EH.ehouse (Aemb u t) \<le> gs_concrete_entry_bound"
      by (rule gs_row_scaled_entry_concrete_house_le[OF up tq])
    have fun_eq: "Aemb u t =
        (\<lambda>e. e (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t)))"
      by (rule ext) (simp add: Aemb_def)
    show "EH.ehouse (\<lambda>e. e (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) \<le> A"
      using bound by (simp only: A_choice fun_eq)
  qed
  show "0 \<le> A"
    using A_choice gs_concrete_entry_bound_nonneg by simp
  show "\<And>v x r c rho.
      v \<in> carrier_vec (q * q) \<Longrightarrow>
      v \<noteq> 0\<^sub>v (q * q) \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q) \<Longrightarrow>
      (\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)) \<Longrightarrow>
      (\<forall>t<q * q. Matrix.vec_index v t = (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))) \<Longrightarrow>
      x \<in> carrier_vec (q * q * D) \<Longrightarrow>
      x \<noteq> 0\<^sub>v (q * q * D) \<Longrightarrow>
      x \<in> Bounded_vec
            (2 * int (q * q * D) *
              max 1 (ceiling (of_nat (card E) * power_basis_inverse_bound * A * power_basis_entry_bound))) \<Longrightarrow>
      r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<Longrightarrow>
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0 \<Longrightarrow>
      c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q) \<Longrightarrow>
      rho = (of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<Longrightarrow>
      gs_abs_galois_norm rho \<le>
        c14 powr of_nat r *
        of_nat r powr ((- of_nat r / 2 + 3 * of_nat h / 2) :: real)"
    by (rule gs_rho_upper_verified[OF hD A_choice c14_big])
qed

theorem coordinate_contradiction: False
  by (rule CHECKED.coordinate_contradiction)

end

lemma finite_Rats_common_denominator:
  fixes F :: "complex set"
  assumes finite: "finite F"
    and rat: "F \<subseteq> (\<rat> :: complex set)"
  shows "\<exists>L::int. L > 0 \<and> (\<forall>x\<in>F. \<exists>z::int. of_int L * x = of_int z)"
using finite rat
proof (induction F rule: finite_induct)
  case empty
  show ?case by (intro exI[of _ 1]) simp
next
  case (insert x F)
  have xr: "x \<in> (\<rat> :: complex set)" using insert.prems by auto
  obtain a b where bp: "b > 0" and xe: "x = of_int a / of_int b"
    using Rats_cases'[OF xr] by blast
  obtain L::int where Lp: "L > 0" and Le: "\<forall>y\<in>F. \<exists>z::int. of_int L * y = of_int z"
    using insert.IH insert.prems by auto
  have all: "\<forall>y\<in>insert x F. \<exists>z::int. of_int (b * L) * y = of_int z"
  proof (intro ballI)
    fix y
    assume yin: "y \<in> insert x F"
    show "\<exists>z::int. of_int (b * L) * y = of_int z"
    proof (cases "y = x")
      case True
      show ?thesis using bp xe True
        by (intro exI[of _ "L * a"]) (simp add: field_simps)
    next
      case False
      then have yf: "y \<in> F" using yin by simp
      obtain z::int where yz: "of_int L * y = of_int z" using Le yf by blast
      show ?thesis using yz
        by (intro exI[of _ "b * z"]) (simp add: algebra_simps)
    qed
  qed
  show ?case using bp Lp all by (intro exI[of _ "b * L"]) simp
qed

lemma integer_reduction_of_powers_from_monic_relation:
  fixes eta :: complex
  assumes Dpos: "D > 0"
    and red: "eta ^ D = (\<Sum>k<D. of_int (a k) * eta ^ k)"
  shows "\<exists>c::nat \<Rightarrow> int. eta ^ n = (\<Sum>k<D. of_int (c k) * eta ^ k)"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < D")
    case True
    let ?c = "\<lambda>k. if k = n then (1::int) else 0"
    have eq: "eta ^ n = (\<Sum>k<D. of_int (?c k) * eta ^ k)"
    proof -
      have "(\<Sum>k<D. of_int (?c k) * eta ^ k) =
          (\<Sum>k<D. if k = n then eta ^ k else 0)"
        by (rule sum.cong[OF refl]) simp
      also have "... = eta ^ n" using True by simp
      finally show ?thesis by simp
    qed
    show ?thesis by (rule exI[of _ ?c]) (rule eq)
  next
    case False
    then have Dn: "D \<le> n" by simp
    have exp_lt: "n - D + k < n" if kd: "k < D" for k
      using kd Dn by simp
    have each: "\<forall>k<D. \<exists>c::nat \<Rightarrow> int.
        eta ^ (n - D + k) = (\<Sum>j<D. of_int (c j) * eta ^ j)"
      using less.IH exp_lt by blast
    define c :: "nat \<Rightarrow> nat \<Rightarrow> int" where
      "c = (\<lambda>k. SOME f. eta ^ (n - D + k) =
        (\<Sum>j<D. of_int (f j) * eta ^ j))"
    have crep: "\<forall>k<D. eta ^ (n - D + k) =
      (\<Sum>j<D. of_int (c k j) * eta ^ j)"
    proof (intro allI impI)
      fix k
      assume kd: "k < D"
      have ex: "\<exists>f::nat \<Rightarrow> int. eta ^ (n - D + k) =
        (\<Sum>j<D. of_int (f j) * eta ^ j)"
        using each kd by blast
      show "eta ^ (n - D + k) =
        (\<Sum>j<D. of_int (c k j) * eta ^ j)"
        using someI_ex[OF ex] by (simp only: c_def)
    qed
    have nsplit: "n = (n - D) + D" using Dn by simp
    have "eta ^ n = eta ^ ((n - D) + D)"
      by (rule arg_cong[OF nsplit])
    also have "... = eta ^ (n - D) * eta ^ D"
      by (simp only: power_add)
    also have "... = eta ^ (n - D) * (\<Sum>k<D. of_int (a k) * eta ^ k)"
      by (simp only: red)
    also have "... = (\<Sum>k<D. of_int (a k) * eta ^ (n - D + k))"
      by (simp add: sum_distrib_left power_add algebra_simps)
    also have "... = (\<Sum>k<D. of_int (a k) *
      (\<Sum>j<D. of_int (c k j) * eta ^ j))"
      using crep by (intro sum.cong[OF refl]) auto
    also have "... = (\<Sum>k<D. \<Sum>j<D.
      of_int (a k * c k j) * eta ^ j)"
      by (simp add: sum_distrib_left algebra_simps)
    also have "... = (\<Sum>j<D. \<Sum>k<D.
      of_int (a k * c k j) * eta ^ j)"
      by (rule sum.swap)
    also have "... = (\<Sum>j<D.
      of_int (\<Sum>k<D. a k * c k j) * eta ^ j)"
      by (simp add: sum_distrib_right)
    finally have eq: "eta ^ n = (\<Sum>j<D.
      of_int (\<Sum>k<D. a k * c k j) * eta ^ j)" .
    show ?thesis by (rule exI[of _ "\<lambda>j. \<Sum>k<D. a k * c k j"])
      (rule eq)
  qed
qed

lemma scaled_integer_power_basis_coordinate_mul:
  fixes eta x y :: complex
    and c :: "nat \<Rightarrow> int"
    and C :: "nat \<Rightarrow> nat \<Rightarrow> int"
  assumes y_rep: "of_int (T ^ s) * y =
    (\<Sum>j<D. of_int (c j) * eta ^ j)"
    and x_rep: "\<And>j. j < D \<Longrightarrow> of_int T * (x * eta ^ j) =
      (\<Sum>k<D. of_int (C j k) * eta ^ k)"
  shows "of_int (T ^ (s + 1)) * (x * y) =
    (\<Sum>k<D. of_int (\<Sum>j<D. c j * C j k) * eta ^ k)"
proof -
  have "of_int (T ^ (s + 1)) * (x * y) =
      of_int T * x * (of_int (T ^ s) * y)"
    by (simp add: power_Suc algebra_simps)
  also have "... = of_int T * x * (\<Sum>j<D. of_int (c j) * eta ^ j)"
    by (simp only: y_rep)
  also have "... = (\<Sum>j<D. of_int (c j) * (of_int T * (x * eta ^ j)))"
    by (simp add: sum_distrib_left algebra_simps)
  also have "... = (\<Sum>j<D. of_int (c j) *
      (\<Sum>k<D. of_int (C j k) * eta ^ k))"
    by (intro sum.cong[OF refl]) (use x_rep in auto)
  also have "... = (\<Sum>j<D. \<Sum>k<D.
      of_int (c j * C j k) * eta ^ k)"
    by (simp add: sum_distrib_left algebra_simps)
  also have "... = (\<Sum>k<D. \<Sum>j<D.
      of_int (c j * C j k) * eta ^ k)"
    by (rule sum.swap)
  also have "... = (\<Sum>k<D.
      of_int (\<Sum>j<D. c j * C j k) * eta ^ k)"
    by (simp add: sum_distrib_right)
  finally show ?thesis .
qed

lemma scaled_integer_affine_power_basis_coordinate:
  fixes eta beta :: complex
    and C :: "nat \<Rightarrow> nat \<Rightarrow> int"
  assumes jlt: "j < D"
    and beta_rep: "of_int T * (beta * eta ^ j) =
      (\<Sum>k<D. of_int (C j k) * eta ^ k)"
  shows "of_int T * ((of_nat a + of_nat b * beta) * eta ^ j) =
    (\<Sum>k<D. of_int ((if k = j then T * int a else 0) +
      int b * C j k) * eta ^ k)"
proof -
  have delta: "(\<Sum>k<D. of_int (if k = j then T * int a else 0) * eta ^ k) =
      of_int (T * int a) * eta ^ j"
  proof -
    have "(\<Sum>k<D. of_int (if k = j then T * int a else 0) * eta ^ k) =
        (\<Sum>k<D. if k = j then of_int (T * int a) * eta ^ k else 0)"
      by (rule sum.cong[OF refl]) simp
    also have "... = of_int (T * int a) * eta ^ j"
      using jlt by simp
    finally show ?thesis .
  qed
  have "of_int T * ((of_nat a + of_nat b * beta) * eta ^ j) =
      of_int (T * int a) * eta ^ j + of_nat b * (of_int T * (beta * eta ^ j))"
    by (simp add: algebra_simps)
  also have "... = of_int (T * int a) * eta ^ j +
      of_nat b * (\<Sum>k<D. of_int (C j k) * eta ^ k)"
    by (simp only: beta_rep)
  also have "... = (\<Sum>k<D. of_int ((if k = j then T * int a else 0) +
      int b * C j k) * eta ^ k)"
  proof -
    have rhs: "(\<Sum>k<D. of_int ((if k = j then T * int a else 0) +
        int b * C j k) * eta ^ k) =
        (\<Sum>k<D. of_int (if k = j then T * int a else 0) * eta ^ k) +
        of_nat b * (\<Sum>k<D. of_int (C j k) * eta ^ k)"
      by (simp add: sum.distrib sum_distrib_left algebra_simps)
    show ?thesis using rhs delta by simp
  qed
  finally show ?thesis .
qed

lemma scaled_integer_power_basis_coordinates_prod_list:
  fixes eta :: complex
    and S :: "complex set"
    and C :: "complex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes Dpos: "D > 0"
    and reps: "\<And>x j. x \<in> S \<Longrightarrow> j < D \<Longrightarrow>
      of_int T * (x * eta ^ j) =
        (\<Sum>k<D. of_int (C x j k) * eta ^ k)"
    and xsS: "set xs \<subseteq> S"
  shows "\<exists>c::nat \<Rightarrow> int.
    of_int (T ^ length xs) * prod_list xs =
      (\<Sum>k<D. of_int (c k) * eta ^ k)"
using xsS
proof (induction xs)
  case Nil
  let ?c = "\<lambda>k. if k = 0 then (1::int) else 0"
  have eq: "of_int (T ^ length []) * prod_list [] =
      (\<Sum>k<D. of_int (?c k) * eta ^ k)"
  proof -
    have "(\<Sum>k<D. of_int (?c k) * eta ^ k) =
        (\<Sum>k<D. if k = 0 then eta ^ k else 0)"
      by (rule sum.cong[OF refl]) simp
    also have "... = 1" using Dpos by simp
    finally show ?thesis by simp
  qed
  show ?case by (rule exI[of _ ?c]) (rule eq)
next
  case (Cons x xs)
  have xS: "x \<in> S" and restS: "set xs \<subseteq> S"
    using Cons.prems by auto
  obtain c::"nat \<Rightarrow> int" where crep:
    "of_int (T ^ length xs) * prod_list xs =
      (\<Sum>j<D. of_int (c j) * eta ^ j)"
    using Cons.IH[OF restS] by blast
  let ?c = "\<lambda>k. \<Sum>j<D. c j * C x j k"
  have eq: "of_int (T ^ length (x # xs)) * prod_list (x # xs) =
      (\<Sum>k<D. of_int (?c k) * eta ^ k)"
    using scaled_integer_power_basis_coordinate_mul[OF crep reps[OF xS]]
    by simp
  show ?case by (rule exI[of _ ?c]) (rule eq)
qed

lemma scaled_integer_power_basis_coordinates_prod_list_weak:
  fixes eta :: complex
    and S :: "complex set"
  assumes Dpos: "D > 0"
    and reps: "\<And>x j. x \<in> S \<Longrightarrow> j < D \<Longrightarrow>
      \<exists>c::nat \<Rightarrow> int. of_int T * (x * eta ^ j) =
        (\<Sum>k<D. of_int (c k) * eta ^ k)"
    and xsS: "set xs \<subseteq> S"
  shows "\<exists>c::nat \<Rightarrow> int.
    of_int (T ^ length xs) * prod_list xs =
      (\<Sum>k<D. of_int (c k) * eta ^ k)"
proof -
  define C :: "complex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
    "C = (\<lambda>x j. SOME c. of_int T * (x * eta ^ j) =
      (\<Sum>k<D. of_int (c k) * eta ^ k))"
  have rep: "of_int T * (x * eta ^ j) =
      (\<Sum>k<D. of_int (C x j k) * eta ^ k)"
    if xS: "x \<in> S" and jD: "j < D" for x j
  proof -
    have ex: "\<exists>c::nat \<Rightarrow> int. of_int T * (x * eta ^ j) =
      (\<Sum>k<D. of_int (c k) * eta ^ k)"
      by (rule reps[OF xS jD])
    show ?thesis using someI_ex[OF ex] by (simp only: C_def)
  qed
  show ?thesis
    by (rule scaled_integer_power_basis_coordinates_prod_list[OF Dpos rep xsS])
qed

definition gs_system_coeff_factor_list ::
  "gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex list"
  where "gs_system_coeff_factor_list d a b l k =
    replicate k (gs_affine_coeff d a b) @
    replicate (a * l) (gs_a d) @ replicate (b * l) (gs_w d)"

lemma gs_system_coeff_factor_list_product:
  "prod_list (gs_system_coeff_factor_list d a b l k) =
    gs_system_coeff d a b l k"
  by (simp add: gs_system_coeff_factor_list_def gs_system_coeff_def)

lemma gs_system_coeff_factor_list_length:
  "length (gs_system_coeff_factor_list d a b l k) = k + a * l + b * l"
  by (simp add: gs_system_coeff_factor_list_def)

lemma gs_system_coeff_factor_list_members:
  "\<forall>x\<in>set (gs_system_coeff_factor_list d a b l k).
    x = gs_a d \<or> x = gs_w d \<or>
      (\<exists>u v::nat. x = of_nat u + of_nat v * gs_b d)"
  by (auto simp: gs_system_coeff_factor_list_def gs_affine_coeff_def)

lemma scaled_integer_power_basis_coordinate_pad_exponent:
  fixes eta y :: complex
    and c :: "nat \<Rightarrow> int"
  assumes eN: "e \<le> N"
    and rep: "of_int (T ^ e) * y =
      (\<Sum>j<D. of_int (c j) * eta ^ j)"
  shows "of_int (T ^ N) * y =
    (\<Sum>j<D. of_int (T ^ (N - e) * c j) * eta ^ j)"
proof -
  have Nsplit: "N = (N - e) + e" using eN by simp
  have "T ^ N = T ^ ((N - e) + e)"
    by (rule arg_cong[OF Nsplit])
  also have "... = T ^ (N - e) * T ^ e"
    by (simp only: power_add)
  finally have pow: "T ^ N = T ^ (N - e) * T ^ e" .
  have "of_int (T ^ N) * y = of_int (T ^ (N - e)) * (of_int (T ^ e) * y)"
    by (simp only: pow of_int_mult mult.assoc)
  also have "... = of_int (T ^ (N - e)) *
      (\<Sum>j<D. of_int (c j) * eta ^ j)"
    by (simp only: rep)
  also have "... = (\<Sum>j<D. of_int (T ^ (N - e) * c j) * eta ^ j)"
    by (simp add: sum_distrib_left algebra_simps)
  finally show ?thesis .
qed

lemma complex_smult_mat_vec:
  fixes A :: "complex mat"
  assumes A: "A \<in> carrier_mat p q"
    and v: "v \<in> carrier_vec q"
  shows "(a \<cdot>\<^sub>m A) *\<^sub>v v = a \<cdot>\<^sub>v (A *\<^sub>v v)"
proof (rule eq_vecI)
  show "dim_vec ((a \<cdot>\<^sub>m A) *\<^sub>v v) = dim_vec (a \<cdot>\<^sub>v (A *\<^sub>v v))"
    using A v by (simp add: smult_mat_def map_mat_def)
next
  fix i
  assume i: "i < dim_vec (a \<cdot>\<^sub>v (A *\<^sub>v v))"
  then have ip: "i < p" using A v by simp
  have "((a \<cdot>\<^sub>m A) *\<^sub>v v) $ i =
      (\<Sum>j<q. (a * A $$ (i,j)) * v $ j)"
    using A v ip by (simp add: index_mult_mat_vec smult_mat_def map_mat_def scalar_prod_def atLeast0LessThan)
  also have "... = a * (\<Sum>j<q. A $$ (i,j) * v $ j)"
    by (simp add: sum_distrib_left algebra_simps)
  also have "... = (a \<cdot>\<^sub>v (A *\<^sub>v v)) $ i"
    using A v ip by (simp add: index_mult_mat_vec scalar_prod_def atLeast0LessThan)
  finally show "((a \<cdot>\<^sub>m A) *\<^sub>v v) $ i =
      (a \<cdot>\<^sub>v (A *\<^sub>v v)) $ i" .
qed

theorem bounded_kernel_of_scaled_integer_structure_constants:
  fixes A :: "complex mat"
    and basis :: "nat \<Rightarrow> complex"
    and C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes A: "A \<in> carrier_mat p q"
    and ppos: "p > 0"
    and dpos: "d > 0"
    and hpq: "2 * p \<le> q"
    and Lnz: "L \<noteq> (0::int)"
    and mult_repr: "\<And>u t j. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow>
      of_int L * (A $$ (u,t) * basis j) =
        (\<Sum>k<d. of_int (C u t k j) * basis k)"
    and C_bnd: "\<And>u t k j. u < p \<Longrightarrow> t < q \<Longrightarrow>
      k < d \<Longrightarrow> j < d \<Longrightarrow> abs (C u t k j) \<le> Bnd"
    and basis_indep: "\<And>c. (\<Sum>j<d. of_int (c j) * basis j) = 0 \<Longrightarrow>
      (\<forall>j<d. c j = 0)"
  obtains v :: "complex vec" and x :: "int vec" where
    "v \<in> carrier_vec q"
    "v \<noteq> 0\<^sub>v q"
    "x \<in> carrier_vec (q * d)"
    "x \<noteq> 0\<^sub>v (q * d)"
    "A *\<^sub>v v = 0\<^sub>v p"
    "\<forall>t<q. v $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)"
    "x \<in> Bounded_vec (2 * int (q * d) * max 1 Bnd)"
proof -
  let ?T = "of_int L \<cdot>\<^sub>m A"
  have Tcar: "?T \<in> carrier_mat p q"
    using A by (simp add: smult_mat_def map_mat_def)
  have Trep: "?T $$ (u,t) * basis j =
      (\<Sum>k<d. of_int (C u t k j) * basis k)"
    if up: "u < p" and tq: "t < q" and jd: "j < d" for u t j
    using mult_repr[OF up tq jd] A up tq
    by (simp add: smult_mat_def map_mat_def algebra_simps)
  obtain v :: "complex vec" and x :: "int vec" where
      vcar: "v \<in> carrier_vec q"
    and vnz: "v \<noteq> 0\<^sub>v q"
    and xcar: "x \<in> carrier_vec (q * d)"
    and xnz: "x \<noteq> 0\<^sub>v (q * d)"
    and Tker: "?T *\<^sub>v v = 0\<^sub>v p"
    and repr: "\<forall>t<q. v $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)"
    and xbnd: "x \<in> Bounded_vec (2 * int (q * d) * max 1 Bnd)"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants_linear
      [OF Tcar ppos dpos hpq Trep C_bnd basis_indep])
  have scaled0: "of_int L \<cdot>\<^sub>v (A *\<^sub>v v) = 0\<^sub>v p"
    using Tker complex_smult_mat_vec[OF A vcar] by simp
  have Aker: "A *\<^sub>v v = 0\<^sub>v p"
  proof (rule eq_vecI)
    show "dim_vec (A *\<^sub>v v) = dim_vec (0\<^sub>v p)" using A vcar by simp
  next
    fix i
    assume ip: "i < dim_vec (0\<^sub>v p)"
    have ai: "i < dim_vec (A *\<^sub>v v)" using A ip by simp
    have comp: "(of_int L \<cdot>\<^sub>v (A *\<^sub>v v)) $ i =
        of_int L * (A *\<^sub>v v) $ i"
      using ai by (simp only: smult_vec_def index_vec)
    have zero: "(of_int L \<cdot>\<^sub>v (A *\<^sub>v v)) $ i = 0"
      using scaled0 ip by simp
    have "of_int L * (A *\<^sub>v v) $ i = 0" using comp zero by simp
    then show "(A *\<^sub>v v) $ i = (0\<^sub>v p) $ i"
      using Lnz ip by simp
  qed
  show thesis by (rule that[OF vcar vnz xcar xnz Aker repr xbnd])
qed

context finite_normal_galois_power_basis
begin

lemma rational_coordinates_of_product:
  assumes xK: "x \<in> K"
  shows "\<exists>c. (\<forall>k<D. c k \<in> (\<rat> :: complex set)) \<and>
    x * eta ^ j = (\<Sum>k<D. c k * eta ^ k)"
proof -
  interpret KS: Subfield K by (rule K_subfield)
  have xjK: "x * eta ^ j \<in> K"
    by (rule KS.mult_closed[OF xK KS.power_closed[OF eta_in_K]])
  from Subfield.power_basis_span[OF Rats_subfield algQ, of "x * eta ^ j"] xjK
  show ?thesis by (simp add: K_def D_def)
qed

lemma finite_entries_have_scaled_integer_structure_constants:
  assumes Sfin: "finite S"
    and SK: "S \<subseteq> K"
  shows "\<exists>L::int. \<exists>C::complex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int.
    L > 0 \<and> (\<forall>x\<in>S. \<forall>j<D.
      of_int L * (x * eta ^ j) = (\<Sum>k<D. of_int (C x j k) * eta ^ k))"
proof -
  define c :: "complex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
    "c = (\<lambda>x j. SOME f. (\<forall>k<D. f k \<in> (\<rat> :: complex set)) \<and>
      x * eta ^ j = (\<Sum>k<D. f k * eta ^ k))"
  have cp: "(\<forall>k<D. c x j k \<in> (\<rat> :: complex set)) \<and>
      x * eta ^ j = (\<Sum>k<D. c x j k * eta ^ k)" if xS: "x \<in> S" for x j
  proof -
    have xK: "x \<in> K" using SK xS by blast
    have ex: "\<exists>f. (\<forall>k<D. f k \<in> (\<rat> :: complex set)) \<and>
        x * eta ^ j = (\<Sum>k<D. f k * eta ^ k)"
      by (rule rational_coordinates_of_product[OF xK])
    show ?thesis using someI_ex[OF ex] by (auto simp only: c_def)
  qed
  let ?F = "(\<Union>x\<in>S. \<Union>j\<in>{..<D}. c x j ` {..<D})"
  have Ffin: "finite ?F" using Sfin by simp
  have Frat: "?F \<subseteq> (\<rat> :: complex set)"
    using cp by auto
  obtain L::int where Lp: "L > 0"
    and Le: "\<forall>z\<in>?F. \<exists>n::int. of_int L * z = of_int n"
    using finite_Rats_common_denominator[OF Ffin Frat] by blast
  define C :: "complex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
    "C = (\<lambda>x j k. SOME n. of_int L * c x j k = of_int n)"
  have LC: "of_int L * c x j k = of_int (C x j k)"
    if xS: "x \<in> S" and jD: "j < D" and kD: "k < D" for x j k
  proof -
    have mem: "c x j k \<in> ?F" using xS jD kD by auto
    have ex: "\<exists>n::int. of_int L * c x j k = of_int n" using Le mem by blast
    show ?thesis using someI_ex[OF ex] by (simp only: C_def)
  qed
  have eq: "of_int L * (x * eta ^ j) =
      (\<Sum>k<D. of_int (C x j k) * eta ^ k)"
    if xS: "x \<in> S" and jD: "j < D" for x j
  proof -
    have "of_int L * (x * eta ^ j) =
        of_int L * (\<Sum>k<D. c x j k * eta ^ k)"
      using cp[OF xS, of j] by simp
    also have "... = (\<Sum>k<D. of_int L * c x j k * eta ^ k)"
      by (simp add: sum_distrib_left algebra_simps)
    also have "... = (\<Sum>k<D. of_int (C x j k) * eta ^ k)"
      by (rule sum.cong[OF refl]) (use LC[OF xS jD] in auto)
    finally show ?thesis .
  qed
  show ?thesis by (intro exI[of _ L] exI[of _ C]) (use Lp eq in auto)
qed

lemma finite_K_generators_have_uniform_product_denominator:
  assumes Sfin: "finite S"
    and SK: "S \<subseteq> K"
  shows "\<exists>T::int. T > 0 \<and> (\<forall>xs. set xs \<subseteq> S \<longrightarrow>
    (\<exists>c::nat \<Rightarrow> int. of_int (T ^ length xs) * prod_list xs =
      (\<Sum>k<D. of_int (c k) * eta ^ k)))"
proof -
  obtain T::int and C::"complex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
    where Tp: "T > 0"
      and rep: "\<forall>x\<in>S. \<forall>j<D. of_int T * (x * eta ^ j) =
        (\<Sum>k<D. of_int (C x j k) * eta ^ k)"
    using finite_entries_have_scaled_integer_structure_constants[OF Sfin SK] by blast
  have Dp: "D > 0" by (rule Dpos)
  have product_rep: "\<exists>c::nat \<Rightarrow> int.
    of_int (T ^ length xs) * prod_list xs =
      (\<Sum>k<D. of_int (c k) * eta ^ k)"
    if xsS: "set xs \<subseteq> S" for xs
    by (rule scaled_integer_power_basis_coordinates_prod_list[OF Dp _ xsS])
      (use rep in auto)
  show ?thesis by (intro exI[of _ T]) (use Tp product_rep in auto)
qed

lemma data_generators_and_affines_uniform_product_denominator:
  assumes aK: "a \<in> K"
    and bK: "b \<in> K"
    and wK: "w \<in> K"
  shows "\<exists>T::int. T > 0 \<and>
    (\<forall>xs. (\<forall>x\<in>set xs. x = a \<or> x = w \<or> x = eta \<or>
      (\<exists>u v::nat. x = of_nat u + of_nat v * b)) \<longrightarrow>
      (\<exists>c::nat \<Rightarrow> int.
        of_int (T ^ length xs) * prod_list xs =
          (\<Sum>k<D. of_int (c k) * eta ^ k)))"
proof -
  let ?S = "{a,b,w,eta}"
  have Sfin: "finite ?S" by simp
  have SK: "?S \<subseteq> K" using aK bK wK eta_in_K by auto
  obtain T::int and C::"complex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
    where Tp: "T > 0"
      and rep: "\<forall>x\<in>?S. \<forall>j<D. of_int T * (x * eta ^ j) =
        (\<Sum>k<D. of_int (C x j k) * eta ^ k)"
    using finite_entries_have_scaled_integer_structure_constants[OF Sfin SK] by blast
  let ?A = "{x::complex. x = a \<or> x = w \<or> x = eta \<or>
    (\<exists>u v::nat. x = of_nat u + of_nat v * b)}"
  have arep: "\<exists>c::nat \<Rightarrow> int. of_int T * (x * eta ^ j) =
      (\<Sum>k<D. of_int (c k) * eta ^ k)"
    if xA: "x \<in> ?A" and jd: "j < D" for x j
  proof -
    consider (a) "x = a" | (w) "x = w" | (eta) "x = eta" |
      (aff) u v where "x = of_nat u + of_nat v * b"
      using xA by auto
    then show ?thesis
    proof cases
      case a
      show ?thesis using rep jd by (intro exI[of _ "C a j"]) (simp add: a)
    next
      case w
      show ?thesis using rep jd by (intro exI[of _ "C w j"]) (simp add: w)
    next
      case eta
      show ?thesis using rep jd by (intro exI[of _ "C eta j"]) (simp add: eta)
    next
      case (aff u v)
      have brep: "of_int T * (b * eta ^ j) =
        (\<Sum>k<D. of_int (C b j k) * eta ^ k)"
        using rep jd by auto
      have affrep: "of_int T * ((of_nat u + of_nat v * b) * eta ^ j) =
        (\<Sum>k<D. of_int ((if k = j then T * int u else 0) +
          int v * C b j k) * eta ^ k)"
        by (rule scaled_integer_affine_power_basis_coordinate
          [where eta=eta and beta=b and C="C b" and T=T and j=j and D=D
            and a=u and b=v, OF jd brep])
      show ?thesis using affrep aff
        by (intro exI[of _ "\<lambda>k. (if k = j then T * int u else 0) +
          int v * C b j k"]) simp
    qed
  qed
  have Dp: "D > 0" by (rule Dpos)
  have prod: "\<exists>c::nat \<Rightarrow> int.
      of_int (T ^ length xs) * prod_list xs =
        (\<Sum>k<D. of_int (c k) * eta ^ k)"
    if xsA: "set xs \<subseteq> ?A" for xs
    by (rule scaled_integer_power_basis_coordinates_prod_list_weak[OF Dp arep xsA])
  show ?thesis
  proof (intro exI[of _ T] conjI allI impI)
    show "T > 0" by (rule Tp)
    fix xs
    assume all: "\<forall>x\<in>set xs. x = a \<or> x = w \<or> x = eta \<or>
      (\<exists>u v::nat. x = of_nat u + of_nat v * b)"
    have xsA: "set xs \<subseteq> ?A" using all by auto
    show "\<exists>c::nat \<Rightarrow> int.
      of_int (T ^ length xs) * prod_list xs =
        (\<Sum>k<D. of_int (c k) * eta ^ k)"
      by (rule prod[OF xsA])
  qed
qed

theorem system_coefficients_have_uniform_exponential_denominator:
  assumes ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
    and a_eq: "gs_a d = (\<Sum>i<D. ca i * eta ^ i)"
    and cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
    and b_eq: "gs_b d = (\<Sum>i<D. cb i * eta ^ i)"
    and cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
    and w_eq: "gs_w d = (\<Sum>i<D. cw i * eta ^ i)"
  shows "\<exists>T::int. T > 0 \<and> (\<forall>a b l k.
    \<exists>c::nat \<Rightarrow> int.
      of_int (T ^ (k + a * l + b * l)) * gs_system_coeff d a b l k =
        (\<Sum>j<D. of_int (c j) * eta ^ j))"
proof -
  have aK: "gs_a d \<in> K"
    using sum_rat_power_in_K[OF ca_rat] by (simp only: a_eq)
  have bK: "gs_b d \<in> K"
    using sum_rat_power_in_K[OF cb_rat] by (simp only: b_eq)
  have wK: "gs_w d \<in> K"
    using sum_rat_power_in_K[OF cw_rat] by (simp only: w_eq)
  obtain T::int where Tp: "T > 0"
    and prod: "\<forall>xs. (\<forall>x\<in>set xs.
      x = gs_a d \<or> x = gs_w d \<or> x = eta \<or>
      (\<exists>u v::nat. x = of_nat u + of_nat v * gs_b d)) \<longrightarrow>
      (\<exists>c::nat \<Rightarrow> int.
        of_int (T ^ length xs) * prod_list xs =
          (\<Sum>j<D. of_int (c j) * eta ^ j))"
    using data_generators_and_affines_uniform_product_denominator
      [OF aK bK wK] by blast
  have one: "\<exists>c::nat \<Rightarrow> int.
      of_int (T ^ (k + a * l + b * l)) * gs_system_coeff d a b l k =
        (\<Sum>j<D. of_int (c j) * eta ^ j)" for a b l k
  proof -
    let ?xs = "gs_system_coeff_factor_list d a b l k"
    have mem: "\<forall>x\<in>set ?xs.
      x = gs_a d \<or> x = gs_w d \<or>
      (\<exists>u v::nat. x = of_nat u + of_nat v * gs_b d)"
      by (rule gs_system_coeff_factor_list_members)
    from prod mem have "\<exists>c::nat \<Rightarrow> int.
      of_int (T ^ length ?xs) * prod_list ?xs =
        (\<Sum>j<D. of_int (c j) * eta ^ j)"
      by blast
    then show ?thesis
      by (simp only: gs_system_coeff_factor_list_length
        gs_system_coeff_factor_list_product)
  qed
  show ?thesis by (intro exI[of _ T]) (use Tp one in auto)
qed

lemma system_coefficients_times_basis_from_product_denominator:
  fixes T :: int
  assumes prod: "\<forall>xs. (\<forall>x\<in>set xs.
    x = gs_a d \<or> x = gs_w d \<or> x = eta \<or>
    (\<exists>u v::nat. x = of_nat u + of_nat v * gs_b d)) \<longrightarrow>
    (\<exists>c::nat \<Rightarrow> int.
      of_int (T ^ length xs) * prod_list xs =
        (\<Sum>i<D. of_int (c i) * eta ^ i))"
  shows "\<forall>a b l k j. \<exists>c::nat \<Rightarrow> int.
    of_int (T ^ (k + a * l + b * l + j)) *
      (gs_system_coeff d a b l k * eta ^ j) =
      (\<Sum>i<D. of_int (c i) * eta ^ i)"
proof -
  have one: "\<exists>c::nat \<Rightarrow> int.
      of_int (T ^ (k + a * l + b * l + j)) *
        (gs_system_coeff d a b l k * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i)" for a b l k j
  proof -
    let ?xs = "gs_system_coeff_factor_list d a b l k @ replicate j eta"
    have mem: "\<forall>x\<in>set ?xs.
      x = gs_a d \<or> x = gs_w d \<or> x = eta \<or>
      (\<exists>u v::nat. x = of_nat u + of_nat v * gs_b d)"
      by (auto simp: gs_system_coeff_factor_list_def gs_affine_coeff_def)
    from prod mem have ex: "\<exists>c::nat \<Rightarrow> int.
      of_int (T ^ length ?xs) * prod_list ?xs =
        (\<Sum>i<D. of_int (c i) * eta ^ i)" by blast
    show ?thesis using ex
      by (simp add: gs_system_coeff_factor_list_length
        gs_system_coeff_factor_list_product)
  qed
  show ?thesis using one by blast
qed

theorem system_coefficients_times_basis_have_uniform_denominator:
  assumes ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
    and a_eq: "gs_a d = (\<Sum>i<D. ca i * eta ^ i)"
    and cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
    and b_eq: "gs_b d = (\<Sum>i<D. cb i * eta ^ i)"
    and cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
    and w_eq: "gs_w d = (\<Sum>i<D. cw i * eta ^ i)"
  shows "\<exists>T::int. T > 0 \<and> (\<forall>a b l k j.
    \<exists>c::nat \<Rightarrow> int.
      of_int (T ^ (k + a * l + b * l + j)) *
        (gs_system_coeff d a b l k * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i))"
proof -
  have aK: "gs_a d \<in> K"
    using sum_rat_power_in_K[OF ca_rat] by (simp only: a_eq)
  have bK: "gs_b d \<in> K"
    using sum_rat_power_in_K[OF cb_rat] by (simp only: b_eq)
  have wK: "gs_w d \<in> K"
    using sum_rat_power_in_K[OF cw_rat] by (simp only: w_eq)
  obtain T::int where Tp: "T > 0"
    and prod: "\<forall>xs. (\<forall>x\<in>set xs.
      x = gs_a d \<or> x = gs_w d \<or> x = eta \<or>
      (\<exists>u v::nat. x = of_nat u + of_nat v * gs_b d)) \<longrightarrow>
      (\<exists>c::nat \<Rightarrow> int.
        of_int (T ^ length xs) * prod_list xs =
          (\<Sum>i<D. of_int (c i) * eta ^ i))"
    using data_generators_and_affines_uniform_product_denominator
      [OF aK bK wK] by blast
  have one: "\<exists>c::nat \<Rightarrow> int.
      of_int (T ^ (k + a * l + b * l + j)) *
        (gs_system_coeff d a b l k * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i)" for a b l k j
  proof -
    let ?xs = "gs_system_coeff_factor_list d a b l k @ replicate j eta"
    have mem: "\<forall>x\<in>set ?xs.
      x = gs_a d \<or> x = gs_w d \<or> x = eta \<or>
      (\<exists>u v::nat. x = of_nat u + of_nat v * gs_b d)"
      by (auto simp: gs_system_coeff_factor_list_def gs_affine_coeff_def)
    from prod mem have ex: "\<exists>c::nat \<Rightarrow> int.
      of_int (T ^ length ?xs) * prod_list ?xs =
        (\<Sum>i<D. of_int (c i) * eta ^ i)" by blast
    show ?thesis using ex
      by (simp add: gs_system_coeff_factor_list_length
        gs_system_coeff_factor_list_product)
  qed
  show ?thesis by (intro exI[of _ T]) (use Tp one in auto)
qed

lemma gs_system_coeff_idx_basis_exponent_le:
  assumes npos: "gs_n h q > 0"
    and qpos: "q > 0"
    and ult: "u < gs_m h * gs_n h q"
    and tlt: "t < q * q"
    and jlt: "j < D"
  shows "gs_k_idx (gs_n h q) u +
    gs_a_idx q t * gs_l_idx (gs_n h q) u +
    gs_b_idx q t * gs_l_idx (gs_n h q) u + j
      \<le> gs_n h q + 2 * (gs_m h * q) + D"
proof -
  have kle: "gs_k_idx (gs_n h q) u \<le> gs_n h q"
    using gs_k_idx_le[OF npos, of u] by linarith
  have lle: "gs_l_idx (gs_n h q) u \<le> gs_m h"
    by (rule gs_l_idx_le[OF npos ult])
  have ale: "gs_a_idx q t \<le> q"
    by (rule gs_a_idx_le[OF qpos tlt])
  have ble: "gs_b_idx q t \<le> q"
    by (rule gs_b_idx_le[OF qpos])
  have ea: "gs_a_idx q t * gs_l_idx (gs_n h q) u \<le> gs_m h * q"
  proof -
    have "gs_a_idx q t * gs_l_idx (gs_n h q) u \<le> q * gs_l_idx (gs_n h q) u"
      using ale by simp
    also have "... \<le> q * gs_m h" using lle by simp
    finally show ?thesis by (simp add: mult.commute)
  qed
  have eb: "gs_b_idx q t * gs_l_idx (gs_n h q) u \<le> gs_m h * q"
  proof -
    have "gs_b_idx q t * gs_l_idx (gs_n h q) u \<le> q * gs_l_idx (gs_n h q) u"
      using ble by simp
    also have "... \<le> q * gs_m h" using lle by simp
    finally show ?thesis by (simp add: mult.commute)
  qed
  show ?thesis using kle ea eb jlt by linarith
qed

lemma row_scaled_matrix_entries_from_product_denominator:
  fixes T :: int
  assumes prod: "\<forall>xs. (\<forall>x\<in>set xs.
    x = gs_a d \<or> x = gs_w d \<or> x = eta \<or>
    (\<exists>u v::nat. x = of_nat u + of_nat v * gs_b d)) \<longrightarrow>
    (\<exists>c::nat \<Rightarrow> int.
      of_int (T ^ length xs) * prod_list xs =
        (\<Sum>i<D. of_int (c i) * eta ^ i))"
    and npos: "gs_n h q > 0"
    and qpos: "q > 0"
  shows "\<forall>u<gs_m h * gs_n h q. \<forall>t<q * q. \<forall>j<D.
    \<exists>c::nat \<Rightarrow> int.
      of_int (T ^ (gs_n h q + 2 * (gs_m h * q) + D)) *
        (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i)"
proof -
  have rep: "\<forall>a b l k j. \<exists>c::nat \<Rightarrow> int.
      of_int (T ^ (k + a * l + b * l + j)) *
        (gs_system_coeff d a b l k * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i)"
    by (rule system_coefficients_times_basis_from_product_denominator[OF prod])
  have one: "\<exists>c::nat \<Rightarrow> int.
    of_int (T ^ (gs_n h q + 2 * (gs_m h * q) + D)) *
      (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * eta ^ j) =
      (\<Sum>i<D. of_int (c i) * eta ^ i)"
    if ult: "u < gs_m h * gs_n h q" and tlt: "t < q * q" and jlt: "j < D"
    for u t j
  proof -
    let ?k = "gs_k_idx (gs_n h q) u"
    let ?a = "gs_a_idx q t"
    let ?b = "gs_b_idx q t"
    let ?l = "gs_l_idx (gs_n h q) u"
    let ?e = "?k + ?a * ?l + ?b * ?l + j"
    let ?N = "gs_n h q + 2 * (gs_m h * q) + D"
    have eN: "?e \<le> ?N"
      by (rule gs_system_coeff_idx_basis_exponent_le[OF npos qpos ult tlt jlt])
    obtain c::"nat \<Rightarrow> int" where crep:
      "of_int (T ^ ?e) * (gs_system_coeff d ?a ?b ?l ?k * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i)"
      using rep by blast
    have padded: "of_int (T ^ ?N) *
      (gs_system_coeff d ?a ?b ?l ?k * eta ^ j) =
        (\<Sum>i<D. of_int (T ^ (?N - ?e) * c i) * eta ^ i)"
      by (rule scaled_integer_power_basis_coordinate_pad_exponent[OF eN crep])
    let ?s = "gs_row_scale d (gs_m h) (gs_n h q) q u"
    have row: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) =
      of_int ?s * gs_system_coeff d ?a ?b ?l ?k"
      using ult tlt by (simp add: gs_row_scaled_system_mat_def gs_system_coeff_idx_def)
    have final: "of_int (T ^ ?N) *
      (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * eta ^ j) =
      (\<Sum>i<D. of_int (?s * (T ^ (?N - ?e) * c i)) * eta ^ i)"
    proof -
      have "of_int (T ^ ?N) *
        (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * eta ^ j) =
        of_int ?s * (of_int (T ^ ?N) *
          (gs_system_coeff d ?a ?b ?l ?k * eta ^ j))"
        by (simp add: row algebra_simps)
      also have "... = of_int ?s *
        (\<Sum>i<D. of_int (T ^ (?N - ?e) * c i) * eta ^ i)"
        by (simp only: padded)
      also have "... = (\<Sum>i<D. of_int (?s * (T ^ (?N - ?e) * c i)) * eta ^ i)"
        by (simp add: sum_distrib_left algebra_simps)
      finally show ?thesis .
    qed
    show ?thesis by (rule exI[of _ "\<lambda>i. ?s * (T ^ (?N - ?e) * c i)"]) (rule final)
  qed
  show ?thesis using one by blast
qed

theorem row_scaled_matrix_entries_have_uniform_exponential_denominator:
  assumes ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
    and a_eq: "gs_a d = (\<Sum>i<D. ca i * eta ^ i)"
    and cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
    and b_eq: "gs_b d = (\<Sum>i<D. cb i * eta ^ i)"
    and cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
    and w_eq: "gs_w d = (\<Sum>i<D. cw i * eta ^ i)"
    and npos: "gs_n h q > 0"
    and qpos: "q > 0"
  shows "\<exists>T::int. T > 0 \<and>
    (\<forall>u<gs_m h * gs_n h q. \<forall>t<q * q. \<forall>j<D.
      \<exists>c::nat \<Rightarrow> int.
        of_int (T ^ (gs_n h q + 2 * (gs_m h * q) + D)) *
          (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * eta ^ j) =
          (\<Sum>i<D. of_int (c i) * eta ^ i))"
proof -
  obtain T::int where Tp: "T > 0" and rep:
    "\<forall>a b l k j. \<exists>c::nat \<Rightarrow> int.
      of_int (T ^ (k + a * l + b * l + j)) *
        (gs_system_coeff d a b l k * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i)"
    using system_coefficients_times_basis_have_uniform_denominator
      [OF ca_rat a_eq cb_rat b_eq cw_rat w_eq] by blast
  have one: "\<exists>c::nat \<Rightarrow> int.
    of_int (T ^ (gs_n h q + 2 * (gs_m h * q) + D)) *
      (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * eta ^ j) =
      (\<Sum>i<D. of_int (c i) * eta ^ i)"
    if ult: "u < gs_m h * gs_n h q" and tlt: "t < q * q" and jlt: "j < D"
    for u t j
  proof -
    let ?k = "gs_k_idx (gs_n h q) u"
    let ?a = "gs_a_idx q t"
    let ?b = "gs_b_idx q t"
    let ?l = "gs_l_idx (gs_n h q) u"
    let ?e = "?k + ?a * ?l + ?b * ?l + j"
    let ?N = "gs_n h q + 2 * (gs_m h * q) + D"
    have eN: "?e \<le> ?N"
      by (rule gs_system_coeff_idx_basis_exponent_le[OF npos qpos ult tlt jlt])
    obtain c::"nat \<Rightarrow> int" where crep:
      "of_int (T ^ ?e) * (gs_system_coeff d ?a ?b ?l ?k * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i)"
      using rep by blast
    have padded: "of_int (T ^ ?N) *
      (gs_system_coeff d ?a ?b ?l ?k * eta ^ j) =
        (\<Sum>i<D. of_int (T ^ (?N - ?e) * c i) * eta ^ i)"
      by (rule scaled_integer_power_basis_coordinate_pad_exponent[OF eN crep])
    let ?s = "gs_row_scale d (gs_m h) (gs_n h q) q u"
    have row: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) =
      of_int ?s * gs_system_coeff d ?a ?b ?l ?k"
      using ult tlt by (simp add: gs_row_scaled_system_mat_def gs_system_coeff_idx_def)
    have final: "of_int (T ^ ?N) *
      (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * eta ^ j) =
      (\<Sum>i<D. of_int (?s * (T ^ (?N - ?e) * c i)) * eta ^ i)"
    proof -
      have "of_int (T ^ ?N) *
        (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * eta ^ j) =
        of_int ?s * (of_int (T ^ ?N) *
          (gs_system_coeff d ?a ?b ?l ?k * eta ^ j))"
        by (simp add: row algebra_simps)
      also have "... = of_int ?s *
        (\<Sum>i<D. of_int (T ^ (?N - ?e) * c i) * eta ^ i)"
        by (simp only: padded)
      also have "... = (\<Sum>i<D. of_int (?s * (T ^ (?N - ?e) * c i)) * eta ^ i)"
        by (simp add: sum_distrib_left algebra_simps)
      finally show ?thesis .
    qed
    show ?thesis by (rule exI[of _ "\<lambda>i. ?s * (T ^ (?N - ?e) * c i)"]) (rule final)
  qed
  show ?thesis by (intro exI[of _ T]) (use Tp one in auto)
qed

lemma finite_matrix_has_scaled_integer_structure_constants:
  fixes A :: "complex mat"
  assumes A: "A \<in> carrier_mat p q"
    and entryK: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> A $$ (u,t) \<in> K"
  shows "\<exists>L::int. \<exists>C::nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int.
    L > 0 \<and> (\<forall>u<p. \<forall>t<q. \<forall>j<D.
      of_int L * (A $$ (u,t) * eta ^ j) =
        (\<Sum>k<D. of_int (C u t k j) * eta ^ k))"
proof -
  let ?S = "(\<lambda>(u,t). A $$ (u,t)) ` ({..<p} \<times> {..<q})"
  have Sfin: "finite ?S" by simp
  have SK: "?S \<subseteq> K" using entryK by auto
  obtain L::int and C::"complex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
    where Lp: "L > 0"
      and rep: "\<forall>x\<in>?S. \<forall>j<D. of_int L * (x * eta ^ j) =
        (\<Sum>k<D. of_int (C x j k) * eta ^ k)"
    using finite_entries_have_scaled_integer_structure_constants[OF Sfin SK] by blast
  let ?C = "\<lambda>u t k j. C (A $$ (u,t)) j k"
  have eq: "of_int L * (A $$ (u,t) * eta ^ j) =
      (\<Sum>k<D. of_int (?C u t k j) * eta ^ k)"
    if up: "u < p" and tq: "t < q" and jd: "j < D" for u t j
    using rep up tq jd by auto
  show ?thesis by (intro exI[of _ L] exI[of _ ?C]) (use Lp eq in auto)
qed

theorem finite_K_matrix_has_bounded_algebraic_integer_kernel:
  fixes A :: "complex mat"
  assumes A: "A \<in> carrier_mat p q"
    and ppos: "p > 0"
    and hpq: "2 * p \<le> q"
    and entryK: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> A $$ (u,t) \<in> K"
  obtains B :: int and v :: "complex vec" and x :: "int vec" where
    "v \<in> carrier_vec q"
    "v \<noteq> 0\<^sub>v q"
    "A *\<^sub>v v = 0\<^sub>v p"
    "\<forall>t<q. algebraic_int (v $ t)"
    "\<forall>t<q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * eta ^ j)"
    "x \<in> carrier_vec (q * D)"
    "x \<noteq> 0\<^sub>v (q * D)"
    "x \<in> Bounded_vec (2 * int (q * D) * max 1 B)"
proof -
  obtain L::int and C::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
    where Lp: "L > 0"
      and rep: "\<forall>u<p. \<forall>t<q. \<forall>j<D.
        of_int L * (A $$ (u,t) * eta ^ j) =
        (\<Sum>k<D. of_int (C u t k j) * eta ^ k)"
    using finite_matrix_has_scaled_integer_structure_constants[OF A entryK] by blast
  let ?F = "(\<Union>u\<in>{..<p}. \<Union>t\<in>{..<q}. \<Union>k\<in>{..<D}.
    abs ` (C u t k ` {..<D}))"
  have Ffin: "finite ?F" by simp
  let ?B = "Max (insert 0 ?F)"
  have Cbnd: "abs (C u t k j) \<le> ?B"
    if up: "u < p" and tq: "t < q" and kd: "k < D" and jd: "j < D"
    for u t k j
  proof -
    have mem0: "abs (C u t k j) \<in> abs ` (C u t k ` {..<D})"
      using jd by blast
    have mem: "abs (C u t k j) \<in> insert 0 ?F"
      using mem0 up tq kd by blast
    show ?thesis by (rule Max_ge[OF _ mem]) (simp add: Ffin)
  qed
  have indep: "(\<Sum>j<D. of_int (c j) * eta ^ j) = 0 \<Longrightarrow>
    (\<forall>j<D. c j = 0)" for c::"nat \<Rightarrow> int"
  proof -
    assume zero: "(\<Sum>j<D. of_int (c j) * eta ^ j) = 0"
    have cR: "of_int (c j) \<in> (\<rat> :: complex set)"
      for j by simp
    have z: "(\<Sum>j<ext_degree (\<rat> :: complex set) eta.
      of_int (c j) * eta ^ j) = 0"
      using zero by (simp only: D_def)
    have cj0: "(\<forall>j<ext_degree (\<rat> :: complex set) eta.
      of_int (c j) = (0::complex))"
      by (rule Subfield.power_basis_indep[OF Rats_subfield algQ cR z])
    have cj: "(\<forall>j<D. of_int (c j) = (0::complex))"
      using cj0 by (simp only: D_def)
    show "\<forall>j<D. c j = 0" using cj by auto
  qed
  have Dp: "D > 0" by (rule Dpos)
  have Lnz: "L \<noteq> (0::int)" using Lp by simp
  have repp: "of_int L * (A $$ (u,t) * eta ^ j) =
      (\<Sum>k<D. of_int (C u t k j) * eta ^ k)"
    if up: "u < p" and tq: "t < q" and jd: "j < D" for u t j
    using rep up tq jd by blast
  obtain v :: "complex vec" and x :: "int vec" where
      vcar: "v \<in> carrier_vec q"
    and vnz: "v \<noteq> 0\<^sub>v q"
    and xcar: "x \<in> carrier_vec (q * D)"
    and xnz: "x \<noteq> 0\<^sub>v (q * D)"
    and ker: "A *\<^sub>v v = 0\<^sub>v p"
    and repr: "\<forall>t<q. v $ t =
      (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * eta ^ j)"
    and xbnd: "x \<in> Bounded_vec (2 * int (q * D) * max 1 ?B)"
    by (rule bounded_kernel_of_scaled_integer_structure_constants
      [OF A ppos Dp hpq Lnz repp Cbnd indep])
  have vint: "\<forall>t<q. algebraic_int (v $ t)"
  proof (intro allI impI)
    fix t
    assume tq: "t < q"
    have ai_term: "algebraic_int (of_int (x $ sg_pair_idx D t j) * eta ^ j)" for j
      by (intro algebraic_int_times algebraic_int_power eta_int) simp
    show "algebraic_int (v $ t)"
      using repr tq by (simp add: algebraic_int_sum ai_term)
  qed
  show thesis by (rule that[OF vcar vnz ker vint repr xcar xnz xbnd])
qed

lemma scaled_structure_constants_transport_to_embedding:
  assumes ilt: "i < D"
    and xK: "x \<in> K"
    and rep: "of_int L * (x * eta ^ j) =
      (\<Sum>k<D. of_int (C k) * eta ^ k)"
  shows "of_int L * (emb i x * basis j (emb i)) =
    (\<Sum>k<D. of_int (C k) * basis k (emb i))"
proof -
  interpret KS: Subfield K by (rule K_subfield)
  have sigma: "emb i \<in> field_auto K (\<rat> :: complex set)"
    by (rule emb_in_field_auto[OF ilt])
  have hom: "field_hom_on K (emb i)"
    by (rule field_auto_imp_field_hom_on[OF K_subfield sigma])
  have LK: "(of_int L :: complex) \<in> K"
    using Rats_subset_K by auto
  have Lfix: "emb i (of_int L :: complex) = of_int L"
    using sigma by (simp add: field_auto_mem_iff)
  have etaP: "eta ^ j \<in> K" by (rule KS.power_closed[OF eta_in_K])
  have xjK: "x * eta ^ j \<in> K" by (rule KS.mult_closed[OF xK etaP])
  have lhs: "emb i (of_int L * (x * eta ^ j)) =
      of_int L * (emb i x * basis j (emb i))"
    by (simp add: field_hom_on.hom_mult[OF hom LK xjK]
      field_hom_on.hom_mult[OF hom xK etaP]
      field_hom_on.hom_power[OF hom eta_in_K] Lfix basis_def)
  have rhs: "emb i (\<Sum>k<D. of_int (C k) * eta ^ k) =
      (\<Sum>k<D. of_int (C k) * basis k (emb i))"
    by (rule emb_sum_int_power[OF ilt])
  show ?thesis using arg_cong[OF rep, of "emb i"] lhs rhs by simp
qed

lemma scaled_structure_constant_abs_le:
  assumes xK: "x \<in> K"
    and Lp: "L > (0::int)"
    and rep: "of_int L * (x * eta ^ j) =
      (\<Sum>k<D. of_int (C k) * eta ^ k)"
    and house: "EH.ehouse (\<lambda>e. e x) \<le> A"
    and Anonneg: "0 \<le> A"
    and klt: "k < D"
    and jlt: "j < D"
  shows "abs (C k) \<le> ceiling (of_nat (card E) *
    power_basis_inverse_bound * (of_int L * A * power_basis_entry_bound))"
proof -
  let ?H = "(of_int L :: real) * A * power_basis_entry_bound"
  have Hnonneg: "0 \<le> ?H"
    using Lp Anonneg power_basis_entry_bound_nonneg by simp
  have comb_le: "EH.ehouse (\<lambda>e. \<Sum>k<D. of_int (C k) * basis k e) \<le> ?H"
  proof (rule EH.ehouse_leI[OF Hnonneg])
    fix e
    assume eE: "e \<in> E"
    obtain i where ilt: "i < D" and e_eq: "e = emb i"
      using eE unfolding E_def by auto
    have trans: "(\<Sum>k<D. of_int (C k) * basis k e) =
        of_int L * (e x * basis j e)"
      using scaled_structure_constants_transport_to_embedding[OF ilt xK rep]
      by (simp add: e_eq)
    have xle: "cmod (e x) \<le> A"
      using EH.cmod_le_ehouse[OF eE, of "\<lambda>e. e x"] house by linarith
    have ble: "cmod (basis j e) \<le> power_basis_entry_bound"
      using basis_cmod_le_power_basis_entry_bound[OF ilt jlt] by (simp add: e_eq)
    have "cmod (\<Sum>k<D. of_int (C k) * basis k e) =
        of_int L * cmod (e x) * cmod (basis j e)"
      using Lp by (simp add: trans norm_mult)
    also have "... \<le> ?H"
      using Lp Anonneg xle ble power_basis_entry_bound_nonneg
      by (intro mult_mono) auto
    finally show "cmod ((\<lambda>e. \<Sum>k<D. of_int (C k) * basis k e) e) \<le> ?H"
      by simp
  qed
  have rb: "EH.ehouse (repr_coeff k) \<le> power_basis_inverse_bound"
  proof (rule REC.repr_coeff_ehouse_le_of_inverse_matrix_bound)
    show "0 \<le> power_basis_inverse_bound"
      by (rule power_basis_inverse_bound_nonneg)
    show "\<And>i. i < D \<Longrightarrow>
      cmod (REC.inverse_basis_matrix_entry k i) \<le> power_basis_inverse_bound"
      by (rule inverse_basis_matrix_entry_le_power_basis_inverse_bound[OF _ klt])
  qed
  show ?thesis
    by (rule REC.abs_int_basis_coeff_ehouse_le_biorthogonal
      [OF klt rb power_basis_inverse_bound_nonneg comb_le Hnonneg])
qed

theorem finite_K_matrix_has_house_bounded_kernel_given_denominator:
  fixes M :: "complex mat"
    and L :: int
    and C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes M: "M \<in> carrier_mat p q"
    and ppos: "p > 0"
    and hpq: "2 * p \<le> q"
    and entryK: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> M $$ (u,t) \<in> K"
    and house: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow>
      EH.ehouse (\<lambda>e. e (M $$ (u,t))) \<le> H"
    and Hnonneg: "0 \<le> H"
    and Lp: "L > 0"
    and rep: "\<forall>u<p. \<forall>t<q. \<forall>j<D.
      of_int L * (M $$ (u,t) * eta ^ j) =
        (\<Sum>k<D. of_int (C u t k j) * eta ^ k)"
  obtains v :: "complex vec" and x :: "int vec" where
    "v \<in> carrier_vec q"
    "v \<noteq> 0\<^sub>v q"
    "M *\<^sub>v v = 0\<^sub>v p"
    "\<forall>t<q. algebraic_int (v $ t)"
    "\<forall>t<q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * eta ^ j)"
    "x \<in> carrier_vec (q * D)"
    "x \<noteq> 0\<^sub>v (q * D)"
    "x \<in> Bounded_vec (2 * int (q * D) * max 1
      (ceiling (of_nat (card E) * power_basis_inverse_bound *
        (of_int L * H * power_basis_entry_bound))))"
proof -
  let ?B = "ceiling (of_nat (card E) * power_basis_inverse_bound *
    (of_int L * H * power_basis_entry_bound))"
  have Cbnd: "abs (C u t k j) \<le> ?B"
    if up: "u < p" and tq: "t < q" and kd: "k < D" and jd: "j < D"
    for u t k j
    by (rule scaled_structure_constant_abs_le[OF entryK[OF up tq] Lp
      _ house[OF up tq] Hnonneg kd jd]) (use rep up tq jd in blast)
  have indep: "(\<Sum>j<D. of_int (c j) * eta ^ j) = 0 \<Longrightarrow>
    (\<forall>j<D. c j = 0)" for c::"nat \<Rightarrow> int"
  proof -
    assume zero: "(\<Sum>j<D. of_int (c j) * eta ^ j) = 0"
    have cR: "of_int (c j) \<in> (\<rat> :: complex set)" for j by simp
    have z: "(\<Sum>j<ext_degree (\<rat> :: complex set) eta.
      of_int (c j) * eta ^ j) = 0" using zero by (simp only: D_def)
    have cj: "(\<forall>j<ext_degree (\<rat> :: complex set) eta.
      of_int (c j) = (0::complex))"
      by (rule Subfield.power_basis_indep[OF Rats_subfield algQ cR z])
    show "\<forall>j<D. c j = 0" using cj by (simp add: D_def)
  qed
  have Dp: "D > 0" by (rule Dpos)
  have Lnz: "L \<noteq> (0::int)" using Lp by simp
  have repp: "of_int L * (M $$ (u,t) * eta ^ j) =
      (\<Sum>k<D. of_int (C u t k j) * eta ^ k)"
    if up: "u < p" and tq: "t < q" and jd: "j < D" for u t j
    using rep up tq jd by blast
  obtain v :: "complex vec" and x :: "int vec" where
      vcar: "v \<in> carrier_vec q"
    and vnz: "v \<noteq> 0\<^sub>v q"
    and xcar: "x \<in> carrier_vec (q * D)"
    and xnz: "x \<noteq> 0\<^sub>v (q * D)"
    and ker: "M *\<^sub>v v = 0\<^sub>v p"
    and repr: "\<forall>t<q. v $ t =
      (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * eta ^ j)"
    and xbnd: "x \<in> Bounded_vec (2 * int (q * D) * max 1 ?B)"
    by (rule bounded_kernel_of_scaled_integer_structure_constants
      [OF M ppos Dp hpq Lnz repp Cbnd indep])
  have vint: "\<forall>t<q. algebraic_int (v $ t)"
  proof (intro allI impI)
    fix t
    assume tq: "t < q"
    have ai_term: "algebraic_int (of_int (x $ sg_pair_idx D t j) * eta ^ j)" for j
      by (intro algebraic_int_times algebraic_int_power eta_int) simp
    show "algebraic_int (v $ t)"
      using repr tq by (simp add: algebraic_int_sum ai_term)
  qed
  show thesis by (rule that[OF vcar vnz ker vint repr xcar xnz xbnd])
qed

theorem finite_K_matrix_has_house_bounded_algebraic_integer_kernel:
  fixes M :: "complex mat"
  assumes M: "M \<in> carrier_mat p q"
    and ppos: "p > 0"
    and hpq: "2 * p \<le> q"
    and entryK: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> M $$ (u,t) \<in> K"
    and house: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow>
      EH.ehouse (\<lambda>e. e (M $$ (u,t))) \<le> H"
    and Hnonneg: "0 \<le> H"
  obtains L :: int and v :: "complex vec" and x :: "int vec" where
    "L > 0"
    "v \<in> carrier_vec q"
    "v \<noteq> 0\<^sub>v q"
    "M *\<^sub>v v = 0\<^sub>v p"
    "\<forall>t<q. algebraic_int (v $ t)"
    "\<forall>t<q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * eta ^ j)"
    "x \<in> carrier_vec (q * D)"
    "x \<noteq> 0\<^sub>v (q * D)"
    "x \<in> Bounded_vec (2 * int (q * D) * max 1
      (ceiling (of_nat (card E) * power_basis_inverse_bound *
        (of_int L * H * power_basis_entry_bound))))"
proof -
  obtain L::int and C::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
    where Lp: "L > 0"
      and rep: "\<forall>u<p. \<forall>t<q. \<forall>j<D.
        of_int L * (M $$ (u,t) * eta ^ j) =
        (\<Sum>k<D. of_int (C u t k j) * eta ^ k)"
    using finite_matrix_has_scaled_integer_structure_constants[OF M entryK] by blast
  show thesis
    by (rule finite_K_matrix_has_house_bounded_kernel_given_denominator
      [OF M ppos hpq entryK house Hnonneg Lp rep]) (auto intro: that[OF Lp])
qed

lemma three_power_basis_coordinate_families_common_denominator:
  assumes ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
    and cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
    and cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
  shows "\<exists>L::int. \<exists>za zb zw::nat \<Rightarrow> int.
    L > 0 \<and> (\<forall>i<D. of_int L * ca i = of_int (za i)) \<and>
      (\<forall>i<D. of_int L * cb i = of_int (zb i)) \<and>
      (\<forall>i<D. of_int L * cw i = of_int (zw i))"
proof -
  let ?F = "ca ` {..<D} \<union> cb ` {..<D} \<union> cw ` {..<D}"
  have Ffin: "finite ?F" by simp
  have Frat: "?F \<subseteq> (\<rat> :: complex set)"
    using ca_rat cb_rat cw_rat by auto
  obtain L::int where Lp: "L > 0"
    and Le: "\<forall>x\<in>?F. \<exists>z::int. of_int L * x = of_int z"
    using finite_Rats_common_denominator[OF Ffin Frat] by blast
  define za :: "nat \<Rightarrow> int" where
    "za = (\<lambda>i. SOME z. of_int L * ca i = of_int z)"
  define zb :: "nat \<Rightarrow> int" where
    "zb = (\<lambda>i. SOME z. of_int L * cb i = of_int z)"
  define zw :: "nat \<Rightarrow> int" where
    "zw = (\<lambda>i. SOME z. of_int L * cw i = of_int z)"
  have a: "of_int L * ca i = of_int (za i)" if id: "i < D" for i
  proof -
    have ex: "\<exists>z::int. of_int L * ca i = of_int z"
      using Le id by auto
    show ?thesis using someI_ex[OF ex] by (simp only: za_def)
  qed
  have b: "of_int L * cb i = of_int (zb i)" if id: "i < D" for i
  proof -
    have ex: "\<exists>z::int. of_int L * cb i = of_int z"
      using Le id by auto
    show ?thesis using someI_ex[OF ex] by (simp only: zb_def)
  qed
  have w: "of_int L * cw i = of_int (zw i)" if id: "i < D" for i
  proof -
    have ex: "\<exists>z::int. of_int L * cw i = of_int z"
      using Le id by auto
    show ?thesis using someI_ex[OF ex] by (simp only: zw_def)
  qed
  show ?thesis by (intro exI[of _ L] exI[of _ za] exI[of _ zb]
    exI[of _ zw]) (use Lp a b w in auto)
qed

lemma row_scaled_entry_in_K_from_rational_coordinates:
  assumes ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
    and a_eq: "gs_a d = (\<Sum>i<D. ca i * eta ^ i)"
    and cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
    and b_eq: "gs_b d = (\<Sum>i<D. cb i * eta ^ i)"
    and cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
    and w_eq: "gs_w d = (\<Sum>i<D. cw i * eta ^ i)"
    and up: "u < m * n"
    and tq: "t < q * q"
  shows "gs_row_scaled_system_mat d m n q $$ (u,t) \<in> K"
proof -
  interpret KS: Subfield K by (rule K_subfield)
  have aK: "gs_a d \<in> K"
    using sum_rat_power_in_K[OF ca_rat] by (simp only: a_eq)
  have bK: "gs_b d \<in> K"
    using sum_rat_power_in_K[OF cb_rat] by (simp only: b_eq)
  have wK: "gs_w d \<in> K"
    using sum_rat_power_in_K[OF cw_rat] by (simp only: w_eq)
  have natK: "(of_nat z :: complex) \<in> K" for z
    using Rats_subset_K by auto
  have affK: "gs_affine_coeff d a b \<in> K" for a b
  proof -
    have bh: "of_nat b * gs_b d \<in> K"
      by (rule KS.mult_closed[OF natK bK])
    show ?thesis unfolding gs_affine_coeff_def
      by (rule KS.add_closed[OF natK bh])
  qed
  have sysK: "gs_system_coeff d a b l k \<in> K" for a b l k
  proof -
    have afp: "gs_affine_coeff d a b ^ k \<in> K"
      by (rule KS.power_closed[OF affK])
    have ap: "gs_a d ^ (a * l) \<in> K"
      by (rule KS.power_closed[OF aK])
    have wp: "gs_w d ^ (b * l) \<in> K"
      by (rule KS.power_closed[OF wK])
    show ?thesis unfolding gs_system_coeff_def
      by (intro KS.mult_closed) (use afp ap wp in auto)
  qed
  have scaleK: "(of_int (gs_row_scale d m n q u) :: complex) \<in> K"
    using Rats_subset_K by auto
  have coeffK: "gs_system_coeff_idx d n q u t \<in> K"
    unfolding gs_system_coeff_idx_def by (rule sysK)
  show ?thesis using KS.mult_closed[OF scaleK coeffK] up tq
    by (simp add: gs_row_scaled_system_mat_def)
qed

theorem row_scaled_matrix_has_bounded_algebraic_integer_kernel:
  assumes ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
    and a_eq: "gs_a d = (\<Sum>i<D. ca i * eta ^ i)"
    and cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
    and b_eq: "gs_b d = (\<Sum>i<D. cb i * eta ^ i)"
    and cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
    and w_eq: "gs_w d = (\<Sum>i<D. cw i * eta ^ i)"
    and npos: "gs_n h q > 0"
    and dvd: "2 * gs_m h dvd q ^ 2"
  obtains B :: int and v :: "complex vec" and x :: "int vec" where
    "v \<in> carrier_vec (q * q)"
    "v \<noteq> 0\<^sub>v (q * q)"
    "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v =
      0\<^sub>v (gs_m h * gs_n h q)"
    "\<forall>t<q * q. algebraic_int (v $ t)"
    "\<forall>t<q * q. v $ t =
      (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * eta ^ j)"
    "x \<in> carrier_vec (q * q * D)"
    "x \<noteq> 0\<^sub>v (q * q * D)"
    "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 B)"
proof -
  let ?m = "gs_m h"
  let ?n = "gs_n h q"
  let ?M = "gs_row_scaled_system_mat d ?m ?n q"
  have Mcar: "?M \<in> carrier_mat (?m * ?n) (q * q)" by simp
  have mnpos: "?m * ?n > 0" using npos by simp
  have bal: "q * q = 2 * (?m * ?n)"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have hpq: "2 * (?m * ?n) \<le> q * q" using bal by simp
  have entryK: "?M $$ (u,t) \<in> K"
    if up: "u < ?m * ?n" and tq: "t < q * q" for u t
    by (rule row_scaled_entry_in_K_from_rational_coordinates
      [OF ca_rat a_eq cb_rat b_eq cw_rat w_eq up tq])
  show thesis
    by (rule finite_K_matrix_has_bounded_algebraic_integer_kernel
      [OF Mcar mnpos hpq entryK]) (auto intro: that)
qed

theorem row_scaled_matrix_has_house_bounded_kernel:
  assumes ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
    and a_eq: "gs_a d = (\<Sum>i<D. ca i * eta ^ i)"
    and cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
    and b_eq: "gs_b d = (\<Sum>i<D. cb i * eta ^ i)"
    and cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
    and w_eq: "gs_w d = (\<Sum>i<D. cw i * eta ^ i)"
    and npos: "gs_n h q > 0"
    and dvd: "2 * gs_m h dvd q ^ 2"
    and house: "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow>
      EH.ehouse (\<lambda>e. e (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) \<le> H"
    and Hnonneg: "0 \<le> H"
  obtains L :: int and v :: "complex vec" and x :: "int vec" where
    "L > 0"
    "v \<in> carrier_vec (q * q)"
    "v \<noteq> 0\<^sub>v (q * q)"
    "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v =
      0\<^sub>v (gs_m h * gs_n h q)"
    "\<forall>t<q * q. algebraic_int (v $ t)"
    "\<forall>t<q * q. v $ t =
      (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * eta ^ j)"
    "x \<in> carrier_vec (q * q * D)"
    "x \<noteq> 0\<^sub>v (q * q * D)"
    "x \<in> Bounded_vec (2 * int (q * q * D) * max 1
      (ceiling (of_nat (card E) * power_basis_inverse_bound *
        (of_int L * H * power_basis_entry_bound))))"
proof -
  let ?m = "gs_m h"
  let ?n = "gs_n h q"
  let ?M = "gs_row_scaled_system_mat d ?m ?n q"
  have Mcar: "?M \<in> carrier_mat (?m * ?n) (q * q)" by simp
  have mnpos: "?m * ?n > 0" using npos by simp
  have bal: "q * q = 2 * (?m * ?n)"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have hpq: "2 * (?m * ?n) \<le> q * q" using bal by simp
  have entryK: "?M $$ (u,t) \<in> K"
    if up: "u < ?m * ?n" and tq: "t < q * q" for u t
    by (rule row_scaled_entry_in_K_from_rational_coordinates
      [OF ca_rat a_eq cb_rat b_eq cw_rat w_eq up tq])
  show thesis
    by (rule finite_K_matrix_has_house_bounded_algebraic_integer_kernel
      [OF Mcar mnpos hpq entryK house Hnonneg]) (auto intro: that)
qed

theorem row_scaled_matrix_has_exponential_denominator_bounded_kernel:
  assumes ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
    and a_eq: "gs_a d = (\<Sum>i<D. ca i * eta ^ i)"
    and cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
    and b_eq: "gs_b d = (\<Sum>i<D. cb i * eta ^ i)"
    and cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
    and w_eq: "gs_w d = (\<Sum>i<D. cw i * eta ^ i)"
    and npos: "gs_n h q > 0"
    and qpos: "q > 0"
    and dvd: "2 * gs_m h dvd q ^ 2"
    and house: "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow>
      EH.ehouse (\<lambda>e. e (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) \<le> H"
    and Hnonneg: "0 \<le> H"
  obtains T :: int and v :: "complex vec" and x :: "int vec" where
    "T > 0"
    "v \<in> carrier_vec (q * q)"
    "v \<noteq> 0\<^sub>v (q * q)"
    "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v =
      0\<^sub>v (gs_m h * gs_n h q)"
    "\<forall>t<q * q. algebraic_int (v $ t)"
    "\<forall>t<q * q. v $ t =
      (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * eta ^ j)"
    "x \<in> carrier_vec (q * q * D)"
    "x \<noteq> 0\<^sub>v (q * q * D)"
    "x \<in> Bounded_vec (2 * int (q * q * D) * max 1
      (ceiling (of_nat (card E) * power_basis_inverse_bound *
        (of_int (T ^ (gs_n h q + 2 * (gs_m h * q) + D)) * H *
          power_basis_entry_bound))))"
proof -
  let ?m = "gs_m h"
  let ?n = "gs_n h q"
  let ?M = "gs_row_scaled_system_mat d ?m ?n q"
  let ?N = "?n + 2 * (?m * q) + D"
  obtain T::int where Tp: "T > 0" and reps:
    "\<forall>u<?m * ?n. \<forall>t<q * q. \<forall>j<D.
      \<exists>c::nat \<Rightarrow> int.
        of_int (T ^ ?N) * (?M $$ (u,t) * eta ^ j) =
          (\<Sum>i<D. of_int (c i) * eta ^ i)"
    using row_scaled_matrix_entries_have_uniform_exponential_denominator
      [OF ca_rat a_eq cb_rat b_eq cw_rat w_eq npos qpos] by blast
  define f :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
    "f = (\<lambda>u t j. SOME c::nat \<Rightarrow> int.
      of_int (T ^ ?N) * (?M $$ (u,t) * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i))"
  have rep: "\<forall>u<?m * ?n. \<forall>t<q * q. \<forall>j<D.
    of_int (T ^ ?N) * (?M $$ (u,t) * eta ^ j) =
      (\<Sum>i<D. of_int (f u t j i) * eta ^ i)"
  proof (intro allI impI)
    fix u t j
    assume up: "u < ?m * ?n" and tq: "t < q * q" and jd: "j < D"
    have ex: "\<exists>c::nat \<Rightarrow> int.
      of_int (T ^ ?N) * (?M $$ (u,t) * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i)"
      using reps up tq jd by blast
    show "of_int (T ^ ?N) * (?M $$ (u,t) * eta ^ j) =
      (\<Sum>i<D. of_int (f u t j i) * eta ^ i)"
      using someI_ex[OF ex] by (simp only: f_def)
  qed
  have Mcar: "?M \<in> carrier_mat (?m * ?n) (q * q)" by simp
  have mnpos: "?m * ?n > 0" using npos by simp
  have bal: "q * q = 2 * (?m * ?n)"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have hpq: "2 * (?m * ?n) \<le> q * q" using bal by simp
  have entryK: "?M $$ (u,t) \<in> K"
    if up: "u < ?m * ?n" and tq: "t < q * q" for u t
    by (rule row_scaled_entry_in_K_from_rational_coordinates
      [OF ca_rat a_eq cb_rat b_eq cw_rat w_eq up tq])
  have Lp: "T ^ ?N > 0" using Tp by simp
  have repC: "\<forall>u<?m * ?n. \<forall>t<q * q. \<forall>j<D.
    of_int (T ^ ?N) * (?M $$ (u,t) * eta ^ j) =
      (\<Sum>k<D. of_int ((\<lambda>u t k j. f u t j k) u t k j) * eta ^ k)"
    using rep by simp
  show thesis
    by (rule finite_K_matrix_has_house_bounded_kernel_given_denominator
      [OF Mcar mnpos hpq entryK house Hnonneg Lp repC])
      (auto intro: that[OF Tp])
qed
theorem row_scaled_matrix_has_given_denominator_bounded_kernel:
  fixes T :: int
  assumes Tp: "T > 0"
    and prod: "\<forall>xs. (\<forall>x\<in>set xs.
      x = gs_a d \<or> x = gs_w d \<or> x = eta \<or>
      (\<exists>u v::nat. x = of_nat u + of_nat v * gs_b d)) \<longrightarrow>
      (\<exists>c::nat \<Rightarrow> int.
        of_int (T ^ length xs) * prod_list xs =
          (\<Sum>i<D. of_int (c i) * eta ^ i))"
    and ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
    and a_eq: "gs_a d = (\<Sum>i<D. ca i * eta ^ i)"
    and cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
    and b_eq: "gs_b d = (\<Sum>i<D. cb i * eta ^ i)"
    and cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
    and w_eq: "gs_w d = (\<Sum>i<D. cw i * eta ^ i)"
    and npos: "gs_n h q > 0"
    and qpos: "q > 0"
    and dvd: "2 * gs_m h dvd q ^ 2"
    and house: "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow>
      EH.ehouse (\<lambda>e. e (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) \<le> H"
    and Hnonneg: "0 \<le> H"
  obtains v :: "complex vec" and x :: "int vec" where
    "v \<in> carrier_vec (q * q)"
    "v \<noteq> 0\<^sub>v (q * q)"
    "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v =
      0\<^sub>v (gs_m h * gs_n h q)"
    "\<forall>t<q * q. algebraic_int (v $ t)"
    "\<forall>t<q * q. v $ t =
      (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * eta ^ j)"
    "x \<in> carrier_vec (q * q * D)"
    "x \<noteq> 0\<^sub>v (q * q * D)"
    "x \<in> Bounded_vec (2 * int (q * q * D) * max 1
      (ceiling (of_nat (card E) * power_basis_inverse_bound *
        (of_int (T ^ (gs_n h q + 2 * (gs_m h * q) + D)) * H *
          power_basis_entry_bound))))"
proof -
  let ?m = "gs_m h"
  let ?n = "gs_n h q"
  let ?M = "gs_row_scaled_system_mat d ?m ?n q"
  let ?N = "?n + 2 * (?m * q) + D"
  have reps:
    "\<forall>u<?m * ?n. \<forall>t<q * q. \<forall>j<D.
      \<exists>c::nat \<Rightarrow> int.
        of_int (T ^ ?N) * (?M $$ (u,t) * eta ^ j) =
          (\<Sum>i<D. of_int (c i) * eta ^ i)"
    by (rule row_scaled_matrix_entries_from_product_denominator
      [OF prod npos qpos])
  define f :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
    "f = (\<lambda>u t j. SOME c::nat \<Rightarrow> int.
      of_int (T ^ ?N) * (?M $$ (u,t) * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i))"
  have rep: "\<forall>u<?m * ?n. \<forall>t<q * q. \<forall>j<D.
    of_int (T ^ ?N) * (?M $$ (u,t) * eta ^ j) =
      (\<Sum>i<D. of_int (f u t j i) * eta ^ i)"
  proof (intro allI impI)
    fix u t j
    assume up: "u < ?m * ?n" and tq: "t < q * q" and jd: "j < D"
    have ex: "\<exists>c::nat \<Rightarrow> int.
      of_int (T ^ ?N) * (?M $$ (u,t) * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i)"
      using reps up tq jd by blast
    show "of_int (T ^ ?N) * (?M $$ (u,t) * eta ^ j) =
      (\<Sum>i<D. of_int (f u t j i) * eta ^ i)"
      using someI_ex[OF ex] by (simp only: f_def)
  qed
  have Mcar: "?M \<in> carrier_mat (?m * ?n) (q * q)" by simp
  have mnpos: "?m * ?n > 0" using npos by simp
  have bal: "q * q = 2 * (?m * ?n)"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have hpq: "2 * (?m * ?n) \<le> q * q" using bal by simp
  have entryK: "?M $$ (u,t) \<in> K"
    if up: "u < ?m * ?n" and tq: "t < q * q" for u t
    by (rule row_scaled_entry_in_K_from_rational_coordinates
      [OF ca_rat a_eq cb_rat b_eq cw_rat w_eq up tq])
  have Lp: "T ^ ?N > 0" using Tp by simp
  have repC: "\<forall>u<?m * ?n. \<forall>t<q * q. \<forall>j<D.
    of_int (T ^ ?N) * (?M $$ (u,t) * eta ^ j) =
      (\<Sum>k<D. of_int ((\<lambda>u t k j. f u t j k) u t k j) * eta ^ k)"
    using rep by simp
  show thesis
    by (rule finite_K_matrix_has_house_bounded_kernel_given_denominator
      [OF Mcar mnpos hpq entryK house Hnonneg Lp repC])
      (auto intro: that)
qed

end

locale gelfond_schneider_power_basis_scaled_norm_verified =
  gelfond_schneider_power_basis_field_norm_estimates
    K eta D emb ca cb cw d q h i0 A c5 c14
  for K :: "complex set"
  and eta :: complex
  and D :: nat
  and emb :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  and ca cb cw :: "nat \<Rightarrow> complex"
  and d
  and q h i0 :: nat
  and A c5 c14 :: real +
  fixes T :: int
  assumes Tp: "T > 0"
  assumes prod: "\<forall>xs. (\<forall>x\<in>set xs.
    x = gs_a d \<or> x = gs_w d \<or> x = eta \<or>
    (\<exists>u v::nat. x = of_nat u + of_nat v * gs_b d)) \<longrightarrow>
    (\<exists>z::nat \<Rightarrow> int.
      of_int (T ^ length xs) * prod_list xs =
        (\<Sum>i<D. of_int (z i) * eta ^ i))"
  assumes hD: "h = D"
  assumes A_choice: "A = gs_concrete_entry_bound"
  assumes c14_big:
    "(gs_house_growth_base *
      (of_int (T ^ (1 + 4 * gs_m h * gs_m h + D)) :: real) ^ 2) ^ (D - 1) *
      (gs_point_growth_base *
        of_int (T ^ (1 + 4 * gs_m h * gs_m h + D))) \<le> c14"
begin

theorem coordinate_contradiction: False
proof -
  let ?N = "gs_n h q + 2 * (gs_m h * q) + D"
  let ?B = "2 * int (q * q * D) * max 1
    (ceiling (of_nat (card E) * power_basis_inverse_bound *
      (of_int (T ^ ?N) * A * power_basis_entry_bound)))"
  have house: "EH.ehouse (\<lambda>e. e
    (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) \<le> A"
    if up: "u < gs_m h * gs_n h q" and tq: "t < q * q" for u t
  proof -
    have bound: "EH.ehouse (Aemb u t) \<le> gs_concrete_entry_bound"
      by (rule gs_row_scaled_entry_concrete_house_le[OF up tq])
    have fun_eq: "Aemb u t = (\<lambda>e. e
      (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t)))"
      by (rule ext) (simp add: Aemb_def)
    show ?thesis using bound by (simp only: A_choice fun_eq)
  qed
  have Anonneg: "0 \<le> A"
    using A_choice gs_concrete_entry_bound_nonneg by simp
  obtain v :: "complex vec" and x :: "int vec" where
      vcar: "v \<in> carrier_vec (q * q)"
    and vnz: "v \<noteq> 0\<^sub>v (q * q)"
    and ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v =
      0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>t<q * q. algebraic_int (v $ t)"
    and vrepr: "\<forall>t<q * q. v $ t =
      (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * eta ^ j)"
    and xcar: "x \<in> carrier_vec (q * q * D)"
    and xnz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and xbnd: "x \<in> Bounded_vec ?B"
    by (rule row_scaled_matrix_has_given_denominator_bounded_kernel
      [OF Tp prod ca_rat a_eq cb_rat b_eq cw_rat w_eq npos qpos dvd house Anonneg])
  have repr: "\<forall>t<q * q. Matrix.vec_index v t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0))"
    using vrepr by (simp add: basis_eq_power_at_identity_embedding[OF emb0])
  define r where "r = nat (gs_min_order (gs_m h) d q
    (\<lambda>t. Matrix.vec_index v t))"
  have coeff_nz: "\<exists>t<q * q. Matrix.vec_index v t \<noteq> 0"
    using vcar vnz by force
  have deriv_nz:
    "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
      (gs_min_order_node (gs_m h) d q
        (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
    unfolding r_def
    by (rule gs_min_order_deriv_nonzero_of_coeff_nonzero[OF d qpos coeff_nz])
  define c where "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
  define rho where "rho = (of_int c :: complex) *
    (gs_z d powi (- int r) *
      ((deriv ^^ r) (gs_aux_fun_vec d q
        (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q
          (\<lambda>t. Matrix.vec_index v t)))"
  have nle: "gs_n h q \<le> r"
    by (rule rho_order_ge_n[OF vcar vnz ker r_def])
  have rpos: "r > 0"
    by (rule rho_order_pos[OF vcar vnz ker r_def])
  have ai: "algebraic_int rho" and nz: "rho \<noteq> 0"
    by (rule rho_algebraic_int_nonzero[OF vcar vnz vint r_def
      deriv_nz c_def rho_def])+
  have xK: "rho \<in> K"
    by (rule rho_in_K[OF repr rho_def])
  have upper: "gs_abs_galois_norm rho \<le>
    c14 powr of_nat r *
      (of_nat r :: real) powr (- of_nat r / 2 + 3 * of_nat h / 2)"
    by (rule gs_rho_upper_from_concrete_witness_with_denominator
      [OF hD A_choice Tp c14_big vcar vnz ker repr xcar xbnd
        r_def rho_def c_def nle rpos ai xK])
  have pos: "0 < gs_abs_galois_norm rho"
    by (rule gs_abs_galois_norm_pos[OF xK nz])
  have inv: "inverse (gs_abs_galois_norm rho) < c5 powr of_nat r"
    by (rule inverse_gs_abs_galois_norm_lt_powr[OF xK ai nz c5_gt1 rpos])
  have choice: "gs_n h (gs_q_choice h (c14 * c5)) \<le> r"
    using nle by (simp add: q_def)
  have c5ge: "1 \<le> c5" using c5_gt1 by linarith
  show False
    by (rule gs_growth_contradiction_with_q_choice
      [OF hpos choice c14_ge1 c5ge pos upper inv])
qed

end

theorem no_gelfond_schneider_data_of_power_basis_norm_target_existence:
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
      (\<exists>K emb q h i0 Aemb C R A rho_norm c5 c14.
        gelfond_schneider_power_basis_norm_target K eta D emb ca cb cw d q h i0 Aemb C R A rho_norm c5 c14)"
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
  obtain K emb q h i0 Aemb C R A rho_norm c5 c14 where
    T: "gelfond_schneider_power_basis_norm_target K eta D emb ca cb cw d q h i0 Aemb C R A rho_norm c5 c14"
    by (meson gelfond_schneider_power_basis_norm_target.coordinate_contradiction)
  interpret T: gelfond_schneider_power_basis_norm_target
    K eta D emb ca cb cw d q h i0 Aemb C R A rho_norm c5 c14
    by (rule T)
  show False
    by (rule T.coordinate_contradiction)
qed

theorem gelfond_schneider_of_power_basis_norm_target_existence:
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
      (\<exists>K emb q h i0 Aemb C R A rho_norm c5 c14.
        gelfond_schneider_power_basis_norm_target K eta D emb ca cb cw d q h i0 Aemb C R A rho_norm c5 c14)"
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
  obtain K emb q h i0 Aemb C R A rho_norm c5 c14 where
    T: "gelfond_schneider_power_basis_norm_target K eta D emb ca cb cw d q h i0 Aemb C R A rho_norm c5 c14"
    by (meson gelfond_schneider_power_basis_norm_target.coordinate_contradiction)
  interpret T: gelfond_schneider_power_basis_norm_target
    K eta D emb ca cb cw d q h i0 Aemb C R A rho_norm c5 c14
    by (rule T)
  show False
    by (rule T.coordinate_contradiction)
qed (use assms(2-) in auto)

end
