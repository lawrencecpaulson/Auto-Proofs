(*  Title:      Baker/Gelfond_Schneider_Power_Basis_Direct.thy
    Author:     OpenAI Codex

Bridge from the primitive normal common-field existence theorem to the concrete
power-basis house-target interface. This isolates the remaining standalone gap
to the quantitative target-instantiation step.
*)

theory Gelfond_Schneider_Power_Basis_Direct
  imports
    Gelfond_Schneider_Power_Basis_House_Target
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

end
