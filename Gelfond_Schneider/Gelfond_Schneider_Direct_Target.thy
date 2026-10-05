(*  Title:      Gelfond_Schneider/Gelfond_Schneider_Direct_Target.thy
    Author:     OpenAI Codex

Abstract packaging for the direct standalone Gelfond-Schneider route.
This removes the primitive-element reduction from the eventual number-field
instantiation theorem: once a contradiction is available for the coordinate
data of a normalized counterexample inside one simple extension Q(theta), the
public transcendence statement follows immediately.
*)

theory Gelfond_Schneider_Direct_Target
  imports
    Gelfond_Schneider_Setup
    Gelfond_Schneider_Common_Field
begin

theorem no_gelfond_schneider_data_of_coordinate_contradiction:
  assumes d: "is_gelfond_schneider_data d"
  assumes coord_contradiction:
    "\<And>\<theta> D ca cb cw.
      is_gelfond_schneider_data d \<Longrightarrow>
      D = ext_degree (\<rat> :: complex set) \<theta> \<Longrightarrow>
      D > 0 \<Longrightarrow>
      (\<forall>i<D. ca i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_a d = (\<Sum>i<D. ca i * \<theta> ^ i) \<Longrightarrow>
      (\<forall>i<D. cb i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_b d = (\<Sum>i<D. cb i * \<theta> ^ i) \<Longrightarrow>
      (\<forall>i<D. cw i \<in> (\<rat> :: complex set)) \<Longrightarrow>
      gs_w d = (\<Sum>i<D. cw i * \<theta> ^ i) \<Longrightarrow>
      False"
  shows False
proof -
  from d have alg_a: "algebraic (gs_a d)"
    and alg_b: "algebraic (gs_b d)"
    and alg_w: "algebraic (gs_w d)"
    unfolding is_gelfond_schneider_data_def by auto
  obtain \<theta> D ca cb cw where
      D_def: "D = ext_degree (\<rat> :: complex set) \<theta>"
    and Dpos: "D > 0"
    and ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
    and a_eq: "gs_a d = (\<Sum>i<D. ca i * \<theta> ^ i)"
    and cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
    and b_eq: "gs_b d = (\<Sum>i<D. cb i * \<theta> ^ i)"
    and cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
    and w_eq: "gs_w d = (\<Sum>i<D. cw i * \<theta> ^ i)"
    by (rule exists_primitive_rational_common_field_coordinates_of_algebraic_triple[OF alg_a alg_b alg_w])
  show False
    by (rule coord_contradiction[OF d D_def Dpos ca_rat a_eq cb_rat b_eq cw_rat w_eq])
qed

theorem gelfond_schneider_of_coordinate_contradiction:
  fixes a b w :: complex
  assumes coord_contradiction:
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
      False"
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
    by (rule no_gelfond_schneider_data_of_coordinate_contradiction[OF d coord_contradiction])
qed

end