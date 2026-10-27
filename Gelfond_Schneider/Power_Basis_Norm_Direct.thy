(*  Title:      Gelfond_Schneider/Power_Basis_Norm_Direct.thy
    Author:     OpenAI Codex

Instantiates the scaled-denominator power-basis contradiction for the
primitive normal common field.
*)

theory Power_Basis_Norm_Direct
  imports Power_Basis_Norm_Target
begin

theorem exists_finite_normal_galois_power_basis_coordinates_of_algebraic_triple:
  fixes a b w :: complex
  assumes alg_a: "algebraic a"
    and alg_b: "algebraic b"
    and alg_w: "algebraic w"
  obtains K eta D emb ca cb cw where
    "finite_normal_galois_power_basis K eta D emb"
    and "D > 0"
    and "rational_power_basis_coordinates D eta ca cb cw a b w"
proof -
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  interpret Q: Subfield "(\<rat> :: complex set)"
    by (rule sfQ)
  obtain eta D ca cb cw K emb where
      eta_int: "algebraic_int eta"
    and K_def: "K = eval_img (\<rat> :: complex set) eta"
    and D_def: "D = ext_degree (\<rat> :: complex set) eta"
    and Dpos: "D > 0"
    and coords: "rational_power_basis_coordinates D eta ca cb cw a b w"
    and finK: "finite_subfield_tower (\<rat> :: complex set) K"
    and normalK: "normal_extension K (\<rat> :: complex set)"
    and separableK: "separable_extension K (\<rat> :: complex set)"
    and ebij: "bij_betw emb {0..<D} (field_auto K (\<rat> :: complex set))"
    by (rule exists_normal_integral_primitive_common_field_coordinates_with_galois_enumeration[OF alg_a alg_b alg_w])
  interpret T: finite_subfield_tower "\<rat>" K
    by (rule finK)
  have etaK: "eta \<in> K"
    unfolding K_def by (rule Q.eval_img_self)
  have algQ: "algebraic_over (\<rat> :: complex set) eta"
    by (rule T.finite_extension_algebraic[OF etaK])
  have PB: "finite_normal_galois_power_basis K eta D emb"
    by unfold_locales (use K_def D_def algQ eta_int ebij finK normalK separableK in auto)
  show thesis
    by (rule that[OF PB Dpos coords])
qed

theorem no_gelfond_schneider_data_of_power_basis_house_coordinate_contradiction:
  assumes d: "is_gelfond_schneider_data d"
  assumes coord_contradiction:
    "\<And>K eta D emb ca cb cw.
      finite_normal_galois_power_basis K eta D emb \<Longrightarrow>
      is_gelfond_schneider_data d \<Longrightarrow>
      D > 0 \<Longrightarrow>
      rational_power_basis_coordinates D eta ca cb cw (gs_a d) (gs_b d) (gs_w d) \<Longrightarrow>
      False"
  shows False
proof -
  have alg_a: "algebraic (gs_a d)"
    and alg_b: "algebraic (gs_b d)"
    and alg_w: "algebraic (gs_w d)"
    using d unfolding is_gelfond_schneider_data_def by auto
  with exists_finite_normal_galois_power_basis_coordinates_of_algebraic_triple[OF alg_a alg_b alg_w] 
       coord_contradiction d show False by auto
qed

theorem scaled_norm_contradiction_for_power_basis:
  assumes PB: "finite_normal_galois_power_basis K eta D emb"
    and d: "is_gelfond_schneider_data d"
    and Dpos: "D > 0"
    and coords: "rational_power_basis_coordinates D eta ca cb cw (gs_a d) (gs_b d) (gs_w d)"
  shows False
proof -
  interpret PB: finite_normal_galois_power_basis K eta D emb by (rule PB)
  interpret Coords: rational_power_basis_coordinates D eta ca cb cw "gs_a d" "gs_b d" "gs_w d"
    by (rule coords)
  note ca_rat = Coords.ca_rat
  note a_eq = Coords.a_eq
  note cb_rat = Coords.cb_rat
  note b_eq = Coords.b_eq
  note cw_rat = Coords.cw_rat
  note w_eq = Coords.w_eq
  obtain aK: "gs_a d \<in> K" and  bK: "gs_b d \<in> K" and wK: "gs_w d \<in> K"
    using PB.sum_rat_power_in_K a_eq b_eq ca_rat cb_rat cw_rat w_eq by presburger
  obtain T::int where Tp: "T > 0" and prod:
              "\<forall>xs. (\<forall>x\<in>set xs. x = gs_a d \<or> x = gs_w d \<or> x = eta \<or>
                (\<exists>u v. x = of_nat u + of_nat v * gs_b d)) \<longrightarrow>
                (\<exists>z. of_int (T ^ length xs) * prod_list xs = (\<Sum>i<D. of_int (z i) * eta ^ i))"
    using PB.data_generators_and_affines_uniform_product_denominator
      [OF aK bK wK]
    unfolding PB.uniform_product_denominator_def
      PB.uniform_denominator_factor_def by blast
  let ?U = "(of_int (T ^ (1 + 4 * gs_m D * gs_m D + D)) :: real)"
  let ?HB = "gelfond_schneider_power_basis_field_norm_estimates.gs_house_growth_base eta D emb d D"
  let ?P = "gelfond_schneider_power_basis_field_norm_estimates.gs_point_growth_base eta D emb d D"
  define c14 where "c14 \<equiv> max 1 ((?HB * ?U ^ 2) ^ (D - 1) * (?P * ?U))"
  have Cge: "1 \<le> c14 * 2"
    using c14_def by linarith 
  define q where "q \<equiv> gs_q_choice D (c14 * (2::real))"
  define A where "A \<equiv> gelfond_schneider_power_basis_field_norm_estimates.gs_concrete_entry_bound D emb d q D"
  obtain i0 where i0lt: "i0 < D" and emb0: "emb i0 = identity K"
    by (rule PB.obtains_identity_embedding_index)
  have SV: "gelfond_schneider_power_basis_scaled_norm_verified K eta D emb ca cb cw d q D i0 A 2 c14 T"
  proof 
    show "q > 0"       
      unfolding q_def by (rule gs_q_choice_pos[OF Dpos Cge])
    show "gs_n D q > 0"
      using \<open>0 < q\<close> gs_n_q_choice_closed_form gs_q_choice_def q_def by auto
    show "2 * gs_m D dvd q ^ 2" 
      unfolding q_def by (rule gs_q_choice_dvd)
    show "gs_row_scaled_system_mat d (gs_m D) (gs_n D q) q $$ (u,t) \<in> K"
      if up: "u < gs_m D * gs_n D q" and tq: "t < q * q" for u t
      by (rule PB.row_scaled_entry_in_K_from_rational_coordinates
          [OF coords up tq])
  qed (use assms ca_rat a_eq cb_rat b_eq cw_rat w_eq prod d Tp i0lt emb0 q_def A_def c14_def in auto)
  interpret V: gelfond_schneider_power_basis_scaled_norm_verified
    K eta D emb ca cb cw d q D i0 A 2 c14 T by (rule SV)
  show False by (rule V.coordinate_contradiction)
qed

theorem no_gelfond_schneider_data_scaled:
  assumes d: "is_gelfond_schneider_data d"
  shows False
  using assms no_gelfond_schneider_data_of_power_basis_house_coordinate_contradiction
    scaled_norm_contradiction_for_power_basis by blast

end
