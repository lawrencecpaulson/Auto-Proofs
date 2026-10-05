(*  Title:      Gelfond_Schneider/Gelfond_Schneider_Power_Basis_Norm_Direct.thy
    Author:     OpenAI Codex

Bridge from the primitive normal common-field existence theorem to the
power-basis rho-norm target interface.
*)

theory Gelfond_Schneider_Power_Basis_Norm_Direct
  imports
    Gelfond_Schneider_Power_Basis_House_Target
    Gelfond_Schneider_Power_Basis_Norm_Target
begin

theorem exists_finite_normal_galois_power_basis_coordinates_of_algebraic_triple:
  fixes a b w :: complex
  assumes alg_a: "algebraic a"
    and alg_b: "algebraic b"
    and alg_w: "algebraic w"
  obtains K eta D emb ca cb cw where
    "finite_normal_galois_power_basis K eta D emb"
    and "D > 0"
    and "(\<forall>i<D. ca i \<in> (\<rat> :: complex set))"
    and "a = (\<Sum>i<D. ca i * eta ^ i)"
    and "(\<forall>i<D. cb i \<in> (\<rat> :: complex set))"
    and "b = (\<Sum>i<D. cb i * eta ^ i)"
    and "(\<forall>i<D. cw i \<in> (\<rat> :: complex set))"
    and "w = (\<Sum>i<D. cw i * eta ^ i)"
proof -
  obtain eta D ca cb cw K emb where
      eta_int: "algebraic_int eta"
    and K_def: "K = eval_img (\<rat> :: complex set) eta"
    and D_def: "D = ext_degree (\<rat> :: complex set) eta"
    and Dpos: "D > 0"
    and ca_rat: "(\<forall>i<D. ca i \<in> (\<rat> :: complex set))"
    and a_eq: "a = (\<Sum>i<D. ca i * eta ^ i)"
    and cb_rat: "(\<forall>i<D. cb i \<in> (\<rat> :: complex set))"
    and b_eq: "b = (\<Sum>i<D. cb i * eta ^ i)"
    and cw_rat: "(\<forall>i<D. cw i \<in> (\<rat> :: complex set))"
    and w_eq: "w = (\<Sum>i<D. cw i * eta ^ i)"
    and finK: "finite_subfield_tower (\<rat> :: complex set) K"
    and normalK: "normal_extension K (\<rat> :: complex set)"
    and separableK: "separable_extension K (\<rat> :: complex set)"
    and ebij: "bij_betw emb {0..<D} (field_auto K (\<rat> :: complex set))"
    by (rule exists_normal_integral_primitive_common_field_coordinates_with_galois_enumeration[OF alg_a alg_b alg_w])
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  interpret Q: Subfield "(\<rat> :: complex set)"
    by (rule sfQ)
  interpret T: finite_subfield_tower "\<rat>" K
    by (rule finK)
  have etaK: "eta \<in> K"
    unfolding K_def by (rule Q.eval_img_self)
  have algQ: "algebraic_over (\<rat> :: complex set) eta"
    by (rule T.finite_extension_algebraic[OF etaK])
  have PB: "finite_normal_galois_power_basis K eta D emb"
    by unfold_locales (use K_def D_def algQ eta_int ebij finK normalK separableK in auto)
  show thesis
    by (rule that[OF PB Dpos ca_rat a_eq cb_rat b_eq cw_rat w_eq])
qed

theorem no_gelfond_schneider_data_of_power_basis_house_coordinate_contradiction:
  assumes d: "is_gelfond_schneider_data d"
  assumes coord_contradiction:
    "\<And>K eta D emb ca cb cw.
      finite_normal_galois_power_basis K eta D emb \<Longrightarrow>
      is_gelfond_schneider_data d \<Longrightarrow>
      D > 0 \<Longrightarrow>
      (\<forall>i<D. ca i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_a d = (\<Sum>i<D. ca i * eta ^ i) \<Longrightarrow>
      (\<forall>i<D. cb i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_b d = (\<Sum>i<D. cb i * eta ^ i) \<Longrightarrow>
      (\<forall>i<D. cw i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_w d = (\<Sum>i<D. cw i * eta ^ i) \<Longrightarrow>
      False"
  shows False
proof -
  from d have alg_a: "algebraic (gs_a d)"
    and alg_b: "algebraic (gs_b d)"
    and alg_w: "algebraic (gs_w d)"
    unfolding is_gelfond_schneider_data_def by auto
  obtain K eta D emb ca cb cw where
      PB: "finite_normal_galois_power_basis K eta D emb"
    and Dpos: "D > 0"
    and ca_rat: "(\<forall>i<D. ca i \<in> (\<rat> :: complex set))"
    and a_eq: "gs_a d = (\<Sum>i<D. ca i * eta ^ i)"
    and cb_rat: "(\<forall>i<D. cb i \<in> (\<rat> :: complex set))"
    and b_eq: "gs_b d = (\<Sum>i<D. cb i * eta ^ i)"
    and cw_rat: "(\<forall>i<D. cw i \<in> (\<rat> :: complex set))"
    and w_eq: "gs_w d = (\<Sum>i<D. cw i * eta ^ i)"
    by (rule exists_finite_normal_galois_power_basis_coordinates_of_algebraic_triple[OF alg_a alg_b alg_w])
  show False
    by (rule coord_contradiction[OF PB d Dpos ca_rat a_eq cb_rat b_eq cw_rat w_eq])
qed

theorem no_gelfond_schneider_data_of_finite_normal_power_basis_house_target_existence:
  assumes d: "is_gelfond_schneider_data d"
  assumes target:
    "\<And>K eta D emb ca cb cw.
      finite_normal_galois_power_basis K eta D emb \<Longrightarrow>
      is_gelfond_schneider_data d \<Longrightarrow>
      D > 0 \<Longrightarrow>
      (\<forall>i<D. ca i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_a d = (\<Sum>i<D. ca i * eta ^ i) \<Longrightarrow>
      (\<forall>i<D. cb i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_b d = (\<Sum>i<D. cb i * eta ^ i) \<Longrightarrow>
      (\<forall>i<D. cw i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_w d = (\<Sum>i<D. cw i * eta ^ i) \<Longrightarrow>
      (\<exists>q h i0 Aemb C R A H.
        gelfond_schneider_power_basis_house_target K eta D emb ca cb cw d q h i0 Aemb C R A H)"
  shows False
proof (rule no_gelfond_schneider_data_of_power_basis_house_coordinate_contradiction[OF d])
  fix K eta D emb ca cb cw
  assume PB: "finite_normal_galois_power_basis K eta D emb"
  assume d: "is_gelfond_schneider_data d"
  assume Dpos: "D > 0"
  assume ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
  assume a_eq: "gs_a d = (\<Sum>i<D. ca i * eta ^ i)"
  assume cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
  assume b_eq: "gs_b d = (\<Sum>i<D. cb i * eta ^ i)"
  assume cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
  assume w_eq: "gs_w d = (\<Sum>i<D. cw i * eta ^ i)"
  from target[OF PB d Dpos ca_rat a_eq cb_rat b_eq cw_rat w_eq]
  obtain q h i0 Aemb C R A H where
    T: "gelfond_schneider_power_basis_house_target K eta D emb ca cb cw d q h i0 Aemb C R A H"
    by (meson gelfond_schneider_power_basis_house_target.coordinate_contradiction)
  interpret T: gelfond_schneider_power_basis_house_target
    K eta D emb ca cb cw d q h i0 Aemb C R A H
    by (rule T)
  show False
    by (rule T.coordinate_contradiction)
qed

theorem gelfond_schneider_of_finite_normal_power_basis_house_target_existence:
  fixes a b w :: complex
  assumes target:
    "\<And>d K eta D emb ca cb cw.
      is_gelfond_schneider_data d \<Longrightarrow>
      finite_normal_galois_power_basis K eta D emb \<Longrightarrow>
      D > 0 \<Longrightarrow>
      (\<forall>i<D. ca i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_a d = (\<Sum>i<D. ca i * eta ^ i) \<Longrightarrow>
      (\<forall>i<D. cb i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_b d = (\<Sum>i<D. cb i * eta ^ i) \<Longrightarrow>
      (\<forall>i<D. cw i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_w d = (\<Sum>i<D. cw i * eta ^ i) \<Longrightarrow>
      (\<exists>q h i0 Aemb C R A H.
        gelfond_schneider_power_basis_house_target K eta D emb ca cb cw d q h i0 Aemb C R A H)"
  assumes "algebraic a"
  assumes "algebraic b"
  assumes "a \<noteq> 0"
  assumes "a \<noteq> 1"
  assumes "b \<notin> \<rat>"
  assumes "w \<in> power_values a b"
  shows "\<not> algebraic w"
proof
  assume alg_w: "algebraic w"
  from exists_gelfond_schneider_data_of_counterexample[OF assms(2,3) alg_w assms(4-7)]
  obtain d where d: "is_gelfond_schneider_data d"
    by blast
  show False
    by (rule no_gelfond_schneider_data_of_finite_normal_power_basis_house_target_existence[OF d])
       (use target in blast)
qed


theorem no_gelfond_schneider_data_of_finite_normal_power_basis_norm_target_existence:
  assumes d: "is_gelfond_schneider_data d"
  assumes target:
    "\<And>K eta D emb ca cb cw.
      finite_normal_galois_power_basis K eta D emb \<Longrightarrow>
      is_gelfond_schneider_data d \<Longrightarrow>
      D > 0 \<Longrightarrow>
      (\<forall>i<D. ca i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_a d = (\<Sum>i<D. ca i * eta ^ i) \<Longrightarrow>
      (\<forall>i<D. cb i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_b d = (\<Sum>i<D. cb i * eta ^ i) \<Longrightarrow>
      (\<forall>i<D. cw i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_w d = (\<Sum>i<D. cw i * eta ^ i) \<Longrightarrow>
      (\<exists>q h i0 Aemb C R A rho_norm c5 c14.
        gelfond_schneider_power_basis_norm_target K eta D emb ca cb cw d q h i0 Aemb C R A rho_norm c5 c14)"
  shows False
proof (rule no_gelfond_schneider_data_of_power_basis_house_coordinate_contradiction[OF d])
  fix K eta D emb ca cb cw
  assume PB: "finite_normal_galois_power_basis K eta D emb"
  assume d: "is_gelfond_schneider_data d"
  assume Dpos: "D > 0"
  assume ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
  assume a_eq: "gs_a d = (\<Sum>i<D. ca i * eta ^ i)"
  assume cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
  assume b_eq: "gs_b d = (\<Sum>i<D. cb i * eta ^ i)"
  assume cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
  assume w_eq: "gs_w d = (\<Sum>i<D. cw i * eta ^ i)"
  from target[OF PB d Dpos ca_rat a_eq cb_rat b_eq cw_rat w_eq]
  obtain q h i0 Aemb C R A rho_norm c5 c14 where
    T: "gelfond_schneider_power_basis_norm_target K eta D emb ca cb cw d q h i0 Aemb C R A rho_norm c5 c14"
    by (meson gelfond_schneider_power_basis_norm_target.coordinate_contradiction)
  interpret T: gelfond_schneider_power_basis_norm_target
    K eta D emb ca cb cw d q h i0 Aemb C R A rho_norm c5 c14
    by (rule T)
  show False
    by (rule T.coordinate_contradiction)
qed

theorem gelfond_schneider_of_finite_normal_power_basis_norm_target_existence:
  fixes a b w :: complex
  assumes target:
    "\<And>d K eta D emb ca cb cw.
      is_gelfond_schneider_data d \<Longrightarrow>
      finite_normal_galois_power_basis K eta D emb \<Longrightarrow>
      D > 0 \<Longrightarrow>
      (\<forall>i<D. ca i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_a d = (\<Sum>i<D. ca i * eta ^ i) \<Longrightarrow>
      (\<forall>i<D. cb i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_b d = (\<Sum>i<D. cb i * eta ^ i) \<Longrightarrow>
      (\<forall>i<D. cw i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_w d = (\<Sum>i<D. cw i * eta ^ i) \<Longrightarrow>
      (\<exists>q h i0 Aemb C R A rho_norm c5 c14.
        gelfond_schneider_power_basis_norm_target K eta D emb ca cb cw d q h i0 Aemb C R A rho_norm c5 c14)"
  assumes "algebraic a"
  assumes "algebraic b"
  assumes "a \<noteq> 0"
  assumes "a \<noteq> 1"
  assumes "b \<notin> \<rat>"
  assumes "w \<in> power_values a b"
  shows "\<not> algebraic w"
proof
  assume alg_w: "algebraic w"
  from exists_gelfond_schneider_data_of_counterexample[OF assms(2,3) alg_w assms(4-7)]
  obtain d where d: "is_gelfond_schneider_data d"
    by blast
  show False
    using d target
    by (rule no_gelfond_schneider_data_of_finite_normal_power_basis_norm_target_existence)

qed

theorem scaled_norm_contradiction_for_power_basis:
  assumes PB: "finite_normal_galois_power_basis K eta D emb"
    and d: "is_gelfond_schneider_data d"
    and Dpos: "D > 0"
    and ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
    and a_eq: "gs_a d = (\<Sum>i<D. ca i * eta ^ i)"
    and cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
    and b_eq: "gs_b d = (\<Sum>i<D. cb i * eta ^ i)"
    and cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
    and w_eq: "gs_w d = (\<Sum>i<D. cw i * eta ^ i)"
  shows False
proof -
  interpret PB: finite_normal_galois_power_basis K eta D emb by (rule PB)
  obtain i0 where i0lt: "i0 < D" and emb0: "emb i0 = identity K"
    by (rule PB.obtains_identity_embedding_index)
  have aK: "gs_a d \<in> K"
    using PB.sum_rat_power_in_K[OF ca_rat] by (simp only: a_eq)
  have bK: "gs_b d \<in> K"
    using PB.sum_rat_power_in_K[OF cb_rat] by (simp only: b_eq)
  have wK: "gs_w d \<in> K"
    using PB.sum_rat_power_in_K[OF cw_rat] by (simp only: w_eq)
  obtain T::int where Tp: "T > 0" and prod:
    "\<forall>xs. (\<forall>x\<in>set xs.
      x = gs_a d \<or> x = gs_w d \<or> x = eta \<or>
      (\<exists>u v::nat. x = of_nat u + of_nat v * gs_b d)) \<longrightarrow>
      (\<exists>z::nat \<Rightarrow> int.
        of_int (T ^ length xs) * prod_list xs =
          (\<Sum>i<D. of_int (z i) * eta ^ i))"
    using PB.data_generators_and_affines_uniform_product_denominator
      [OF aK bK wK] by blast
  let ?U = "(of_int (T ^ (1 + 4 * gs_m D * gs_m D + D)) :: real)"
  let ?HB = "gelfond_schneider_power_basis_field_norm_estimates.gs_house_growth_base eta D emb d D"
  let ?P = "gelfond_schneider_power_basis_field_norm_estimates.gs_point_growth_base eta D emb d D"
  define c14 where "c14 = max 1 ((?HB * ?U ^ 2) ^ (D - 1) * (?P * ?U))"
  have c14ge: "1 \<le> c14" by (simp add: c14_def)
  have Cge: "1 \<le> c14 * (2::real)" using c14ge by simp
  define q where "q = gs_q_choice D (c14 * (2::real))"
  have qpos: "q > 0" unfolding q_def
    by (rule gs_q_choice_pos[OF Dpos Cge])
  have dvd: "2 * gs_m D dvd q ^ 2" unfolding q_def
    by (rule gs_q_choice_dvd)
  have npos: "gs_n D q > 0"
  proof -
    have "6 * D \<le> gs_n D q"
      unfolding q_def by (rule gs_q_choice_six_h_le_n[OF Dpos Cge])
    then show ?thesis using Dpos by linarith
  qed
  define A where "A = gelfond_schneider_power_basis_field_norm_estimates.gs_concrete_entry_bound D emb d q D"
  have entryK: "gs_row_scaled_system_mat d (gs_m D) (gs_n D q) q $$ (u,t) \<in> K"
    if up: "u < gs_m D * gs_n D q" and tq: "t < q * q" for u t
    by (rule PB.row_scaled_entry_in_K_from_rational_coordinates
      [OF ca_rat a_eq cb_rat b_eq cw_rat w_eq up tq])
  have SV: "gelfond_schneider_power_basis_scaled_norm_verified
    K eta D emb ca cb cw d q D i0 A 2 c14 T"
  proof unfold_locales
    show "is_gelfond_schneider_data d" by (rule d)
    show "\<forall>i<D. ca i \<in> (\<rat> :: complex set)" by (rule ca_rat)
    show "gs_a d = (\<Sum>i<D. ca i * eta ^ i)" by (rule a_eq)
    show "\<forall>i<D. cb i \<in> (\<rat> :: complex set)" by (rule cb_rat)
    show "gs_b d = (\<Sum>i<D. cb i * eta ^ i)" by (rule b_eq)
    show "\<forall>i<D. cw i \<in> (\<rat> :: complex set)" by (rule cw_rat)
    show "gs_w d = (\<Sum>i<D. cw i * eta ^ i)" by (rule w_eq)
    show "q > 0" by (rule qpos)
    show "gs_n D q > 0" by (rule npos)
    show "2 * gs_m D dvd q ^ 2" by (rule dvd)
    show "i0 < D" by (rule i0lt)
    show "emb i0 = identity K" by (rule emb0)
    show "\<And>u t. u < gs_m D * gs_n D q \<Longrightarrow> t < q * q \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m D) (gs_n D q) q $$ (u,t) \<in> K"
      by (rule entryK)
    show "D > 0" by (rule Dpos)
    show "q = gs_q_choice D (c14 * 2)" by (rule q_def)
    show "1 \<le> c14" by (rule c14ge)
    show "1 < (2::real)" by simp
    show "T > 0" by (rule Tp)
    show "\<forall>xs. (\<forall>x\<in>set xs.
      x = gs_a d \<or> x = gs_w d \<or> x = eta \<or>
      (\<exists>u v::nat. x = of_nat u + of_nat v * gs_b d)) \<longrightarrow>
      (\<exists>z::nat \<Rightarrow> int.
        of_int (T ^ length xs) * prod_list xs =
          (\<Sum>i<D. of_int (z i) * eta ^ i))"
      by (rule prod)
    show "D = D" by simp
    show "A = gelfond_schneider_power_basis_field_norm_estimates.gs_concrete_entry_bound D emb d q D"
      by (rule A_def)
    show "(?HB * ?U ^ 2) ^ (D - 1) * (?P * ?U) \<le> c14"
      by (simp add: c14_def)
  qed
  interpret V: gelfond_schneider_power_basis_scaled_norm_verified
    K eta D emb ca cb cw d q D i0 A 2 c14 T by (rule SV)
  show False by (rule V.coordinate_contradiction)
qed

theorem no_gelfond_schneider_data_scaled:
  assumes d: "is_gelfond_schneider_data d"
  shows False
  by (rule no_gelfond_schneider_data_of_power_basis_house_coordinate_contradiction[OF d])
    (rule scaled_norm_contradiction_for_power_basis)

end
