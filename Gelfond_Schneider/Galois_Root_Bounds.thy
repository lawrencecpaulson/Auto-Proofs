(*  Title:      Gelfond_Schneider/Galois_Root_Bounds.thy
    Author:     OpenAI Codex

Root-bound transfer for algebraic integers inside finite Galois extensions of
the rational subfield. This is a standalone bridge from "all Galois images of
x are bounded" to "all roots of min_int_poly x are bounded", which is exactly
the shape needed by the direct Gelfond-Schneider contradiction layer.
*)

theory Galois_Root_Bounds
  imports
    Common_Field
    Gelfond_Schneider_Setup
    Gelfond_Schneider_House
    "New_Algebra.Field_Extension_Tower"
    "New_Algebra.Galois_Finite_Extension"
    "New_Algebra.Galois_Finite_Correspondence"
    "New_Algebra.Rats_Irreducibility"
begin

theorem exists_finite_normal_rational_extension_of_algebraic:
  fixes \<theta> :: complex
  assumes algQ: "algebraic_over (\<rat> :: complex set) \<theta>"
  obtains K where
      "finite_subfield_tower (\<rat> :: complex set) K"
    and "normal_extension K (\<rat> :: complex set)"
    and "separable_extension K (\<rat> :: complex set)"
    and "eval_img (\<rat> :: complex set) \<theta> \<subseteq> K"
proof -
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  interpret Q: Subfield "(\<rat> :: complex set)"
    by (rule sfQ)
  let ?p = "minpoly (\<rat> :: complex set) \<theta>"
  define K where "K = generate_field ((\<rat> :: complex set) \<union> poly_root_set ?p)"
  have p_over: "?p \<in> poly_over (\<rat> :: complex set)"
    by (rule Q.minpoly_over[OF algQ])
  have p0: "?p \<noteq> 0"
    by (rule Q.minpoly_nonzero[OF algQ])
  have split: "splitting_field (\<rat> :: complex set) ?p K"
    unfolding splitting_field_def K_def
    using p_over p0 by simp
  have fin_roots: "finite (poly_root_set ?p)"
    by (rule finite_poly_root_set[OF p0])
  have alg_roots:
    "\<And>r. r \<in> poly_root_set ?p \<Longrightarrow> algebraic_over (\<rat> :: complex set) r"
    by (rule splitting_field_root_algebraic[OF split])
  obtain L where
      finL: "finite_subfield_tower (\<rat> :: complex set) L"
    and QL: "(\<rat> :: complex set) \<subseteq> L"
    and rootsL: "poly_root_set ?p \<subseteq> L"
    using exists_finite_subfield_tower[OF sfQ fin_roots alg_roots] by blast
  interpret L: finite_subfield_tower "\<rat>" L
    by (rule finL)
  have sfK: "Subfield K"
    by (rule splitting_field_subfield[OF split])
  have QK: "(\<rat> :: complex set) \<subseteq> K"
    by (rule splitting_field_base_subset[OF split])
  have KL: "K \<subseteq> L"
  proof -
    have "(\<rat> :: complex set) \<union> poly_root_set ?p \<subseteq> L"
      using QL rootsL by blast
    then show ?thesis
      unfolding K_def by (rule generate_field_least[OF L.ext.Subfield_axioms])
  qed
  have finK: "finite_subfield_tower (\<rat> :: complex set) K"
    by (rule finite_subfield_tower_intermediate_left[OF finL sfK QK KL])
  have normal_sep: "normal_extension K (\<rat> :: complex set) \<and>
      separable_extension K (\<rat> :: complex set)"
    by (rule splitting_field_normal_separable[OF split complex_subfield_Rats])
  have normalK: "normal_extension K (\<rat> :: complex set)"
    using normal_sep by blast
  have separableK: "separable_extension K (\<rat> :: complex set)"
    using normal_sep by blast
  have theta_root: "\<theta> \<in> poly_root_set ?p"
    using Q.minpoly_root[OF algQ] by simp
  have thetaK: "\<theta> \<in> K"
    using theta_root splitting_field_roots_subset[OF split] by blast
  have eval_sub: "eval_img (\<rat> :: complex set) \<theta> \<subseteq> K"
  proof -
    have "generate_field ((\<rat> :: complex set) \<union> {\<theta>}) \<subseteq> K"
      by (rule generate_field_least[OF sfK]) (use QK thetaK in auto)
    then show ?thesis
      using Q.eval_img_eq_generate_field[OF algQ] by simp
  qed
  show thesis
    by (rule that[OF finK normalK separableK eval_sub])
qed

theorem exists_normal_common_field_coordinates_of_algebraic_triple:
  fixes a b w :: complex
  assumes alg_a: "algebraic a"
    and alg_b: "algebraic b"
    and alg_w: "algebraic w"
  obtains \<theta> D ca cb cw K where
      "D = ext_degree (\<rat> :: complex set) \<theta>"
    and "D > 0"
    and "(\<forall>i<D. ca i \<in> (\<rat> :: complex set))"
    and "a = (\<Sum>i<D. ca i * \<theta> ^ i)"
    and "(\<forall>i<D. cb i \<in> (\<rat> :: complex set))"
    and "b = (\<Sum>i<D. cb i * \<theta> ^ i)"
    and "(\<forall>i<D. cw i \<in> (\<rat> :: complex set))"
    and "w = (\<Sum>i<D. cw i * \<theta> ^ i)"
    and "finite_subfield_tower (\<rat> :: complex set) K"
    and "normal_extension K (\<rat> :: complex set)"
    and "separable_extension K (\<rat> :: complex set)"
    and "eval_img (\<rat> :: complex set) \<theta> \<subseteq> K"
    and "a \<in> K"
    and "b \<in> K"
    and "w \<in> K"
proof -
  obtain \<theta> where
      aE: "a \<in> eval_img (\<rat> :: complex set) \<theta>"
    and bE: "b \<in> eval_img (\<rat> :: complex set) \<theta>"
    and wE: "w \<in> eval_img (\<rat> :: complex set) \<theta>"
    and algQ: "algebraic_over (\<rat> :: complex set) \<theta>"
    and _ : "finite_subfield_tower (\<rat> :: complex set) (eval_img (\<rat> :: complex set) \<theta>)"
    by (rule exists_primitive_rational_common_field_of_algebraic_triple[OF alg_a alg_b alg_w])
  define D where "D = ext_degree (\<rat> :: complex set) \<theta>"
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  obtain ca where ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
    and a_eq: "a = (\<Sum>i<D. ca i * \<theta> ^ i)"
    using Subfield.power_basis_span[OF sfQ algQ aE]
    by (auto simp: D_def)
  obtain cb where cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
    and b_eq: "b = (\<Sum>i<D. cb i * \<theta> ^ i)"
    using Subfield.power_basis_span[OF sfQ algQ bE]
    by (auto simp: D_def)
  obtain cw where cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
    and w_eq: "w = (\<Sum>i<D. cw i * \<theta> ^ i)"
    using Subfield.power_basis_span[OF sfQ algQ wE]
    by (auto simp: D_def)
  have Dpos: "D > 0"
    unfolding D_def by (rule Subfield.ext_degree_pos[OF sfQ algQ])
  obtain K where
      finK: "finite_subfield_tower (\<rat> :: complex set) K"
    and normalK: "normal_extension K (\<rat> :: complex set)"
    and separableK: "separable_extension K (\<rat> :: complex set)"
    and eval_sub: "eval_img (\<rat> :: complex set) \<theta> \<subseteq> K"
    by (rule exists_finite_normal_rational_extension_of_algebraic[OF algQ])
  have aK: "a \<in> K"
    using aE eval_sub by blast
  have bK: "b \<in> K"
    using bE eval_sub by blast
  have wK: "w \<in> K"
    using wE eval_sub by blast
  show thesis
    by (rule that[OF D_def Dpos ca_rat a_eq cb_rat b_eq cw_rat w_eq
          finK normalK separableK eval_sub aK bK wK])
qed

theorem exists_normal_primitive_common_field_coordinates_of_algebraic_triple:
  fixes a b w :: complex
  assumes alg_a: "algebraic a"
    and alg_b: "algebraic b"
    and alg_w: "algebraic w"
  obtains \<theta> D ca cb cw K where
      "K = eval_img (\<rat> :: complex set) \<theta>"
    and "D = ext_degree (\<rat> :: complex set) \<theta>"
    and "D > 0"
    and "(\<forall>i<D. ca i \<in> (\<rat> :: complex set))"
    and "a = (\<Sum>i<D. ca i * \<theta> ^ i)"
    and "(\<forall>i<D. cb i \<in> (\<rat> :: complex set))"
    and "b = (\<Sum>i<D. cb i * \<theta> ^ i)"
    and "(\<forall>i<D. cw i \<in> (\<rat> :: complex set))"
    and "w = (\<Sum>i<D. cw i * \<theta> ^ i)"
    and "finite_subfield_tower (\<rat> :: complex set) K"
    and "normal_extension K (\<rat> :: complex set)"
    and "separable_extension K (\<rat> :: complex set)"
    and "a \<in> K"
    and "b \<in> K"
    and "w \<in> K"
proof -
  obtain \<theta>0 D0 ca0 cb0 cw0 K where
      D0_def: "D0 = ext_degree (\<rat> :: complex set) \<theta>0"
    and D0_pos: "D0 > 0"
    and ca0_rat: "(\<forall>i<D0. ca0 i \<in> (\<rat> :: complex set))"
    and a0_eq: "a = (\<Sum>i<D0. ca0 i * \<theta>0 ^ i)"
    and cb0_rat: "(\<forall>i<D0. cb0 i \<in> (\<rat> :: complex set))"
    and b0_eq: "b = (\<Sum>i<D0. cb0 i * \<theta>0 ^ i)"
    and cw0_rat: "(\<forall>i<D0. cw0 i \<in> (\<rat> :: complex set))"
    and w0_eq: "w = (\<Sum>i<D0. cw0 i * \<theta>0 ^ i)"
    and finK: "finite_subfield_tower (\<rat> :: complex set) K"
    and normalK: "normal_extension K (\<rat> :: complex set)"
    and separableK: "separable_extension K (\<rat> :: complex set)"
    and eval_sub: "eval_img (\<rat> :: complex set) \<theta>0 \<subseteq> K"
    and aK: "a \<in> K"
    and bK: "b \<in> K"
    and wK: "w \<in> K"
    by (rule exists_normal_common_field_coordinates_of_algebraic_triple[OF alg_a alg_b alg_w])
  interpret T: finite_subfield_tower "\<rat>" K
    by (rule finK)
  obtain \<theta> where \<theta>K: "\<theta> \<in> K"
    and prim: "primitive_element (\<rat> :: complex set) K \<theta>"
    using finite_separable_extension_is_simple[OF finK separableK] by blast
  have K_def: "K = eval_img (\<rat> :: complex set) \<theta>"
    by (rule primitive_elementD[OF prim])
  have algQ: "algebraic_over (\<rat> :: complex set) \<theta>"
    by (rule T.finite_extension_algebraic[OF \<theta>K])
  define D where "D = ext_degree (\<rat> :: complex set) \<theta>"
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  have aE: "a \<in> eval_img (\<rat> :: complex set) \<theta>"
    using aK by (simp add: K_def)
  have bE: "b \<in> eval_img (\<rat> :: complex set) \<theta>"
    using bK by (simp add: K_def)
  have wE: "w \<in> eval_img (\<rat> :: complex set) \<theta>"
    using wK by (simp add: K_def)
  obtain ca where ca_rat: "\<forall>i<D. ca i \<in> (\<rat> :: complex set)"
    and a_eq: "a = (\<Sum>i<D. ca i * \<theta> ^ i)"
    using Subfield.power_basis_span[OF sfQ algQ aE]
    by (auto simp: D_def)
  obtain cb where cb_rat: "\<forall>i<D. cb i \<in> (\<rat> :: complex set)"
    and b_eq: "b = (\<Sum>i<D. cb i * \<theta> ^ i)"
    using Subfield.power_basis_span[OF sfQ algQ bE]
    by (auto simp: D_def)
  obtain cw where cw_rat: "\<forall>i<D. cw i \<in> (\<rat> :: complex set)"
    and w_eq: "w = (\<Sum>i<D. cw i * \<theta> ^ i)"
    using Subfield.power_basis_span[OF sfQ algQ wE]
    by (auto simp: D_def)
  have Dpos: "D > 0"
    unfolding D_def by (rule Subfield.ext_degree_pos[OF sfQ algQ])
  show thesis
    by (rule that[OF K_def D_def Dpos ca_rat a_eq cb_rat b_eq cw_rat w_eq
          finK normalK separableK aK bK wK])
qed

theorem exists_normal_primitive_common_field_coordinates_with_galois_enumeration:
  fixes a b w :: complex
  assumes alg_a: "algebraic a"
    and alg_b: "algebraic b"
    and alg_w: "algebraic w"
  obtains \<theta> D ca cb cw K emb where
      "K = eval_img (\<rat> :: complex set) \<theta>"
    and "D = ext_degree (\<rat> :: complex set) \<theta>"
    and "D > 0"
    and "(\<forall>i<D. ca i \<in> (\<rat> :: complex set))"
    and "a = (\<Sum>i<D. ca i * \<theta> ^ i)"
    and "(\<forall>i<D. cb i \<in> (\<rat> :: complex set))"
    and "b = (\<Sum>i<D. cb i * \<theta> ^ i)"
    and "(\<forall>i<D. cw i \<in> (\<rat> :: complex set))"
    and "w = (\<Sum>i<D. cw i * \<theta> ^ i)"
    and "finite_subfield_tower (\<rat> :: complex set) K"
    and "normal_extension K (\<rat> :: complex set)"
    and "separable_extension K (\<rat> :: complex set)"
    and "a \<in> K"
    and "b \<in> K"
    and "w \<in> K"
    and "bij_betw emb {0..<D} (field_auto K (\<rat> :: complex set))"
proof -
  obtain \<theta> D ca cb cw K where
      K_def: "K = eval_img (\<rat> :: complex set) \<theta>"
    and D_def: "D = ext_degree (\<rat> :: complex set) \<theta>"
    and Dpos: "D > 0"
    and ca_rat: "(\<forall>i<D. ca i \<in> (\<rat> :: complex set))"
    and a_eq: "a = (\<Sum>i<D. ca i * \<theta> ^ i)"
    and cb_rat: "(\<forall>i<D. cb i \<in> (\<rat> :: complex set))"
    and b_eq: "b = (\<Sum>i<D. cb i * \<theta> ^ i)"
    and cw_rat: "(\<forall>i<D. cw i \<in> (\<rat> :: complex set))"
    and w_eq: "w = (\<Sum>i<D. cw i * \<theta> ^ i)"
    and finK: "finite_subfield_tower (\<rat> :: complex set) K"
    and normalK: "normal_extension K (\<rat> :: complex set)"
    and separableK: "separable_extension K (\<rat> :: complex set)"
    and aK: "a \<in> K"
    and bK: "b \<in> K"
    and wK: "w \<in> K"
    by (rule exists_normal_primitive_common_field_coordinates_of_algebraic_triple[OF alg_a alg_b alg_w])
  interpret T: finite_subfield_tower "\<rat>" K
    by (rule finK)
  have prim: "primitive_element (\<rat> :: complex set) K \<theta>"
    by (rule primitive_elementI[OF K_def])
  have degree_eq: "T.extension_degree = D"
    using T.primitive_element_degree[OF prim] by (simp add: D_def)
  have finG: "finite (field_auto K (\<rat> :: complex set))"
    by (rule finite_normal_separable_field_auto[OF finK normalK separableK])
  have cardG: "card (field_auto K (\<rat> :: complex set)) = T.extension_degree"
    by (rule finite_normal_separable_galois_degree[OF finK normalK separableK])
  obtain emb where emb:
      "bij_betw emb {0..<card (field_auto K (\<rat> :: complex set))} (field_auto K (\<rat> :: complex set))"
    using ex_bij_betw_nat_finite[OF finG] by blast
  have emb_D: "bij_betw emb {0..<D} (field_auto K (\<rat> :: complex set))"
    using emb by (simp add: cardG degree_eq)
  show thesis
    by (rule that[OF K_def D_def Dpos ca_rat a_eq cb_rat b_eq cw_rat w_eq
          finK normalK separableK aK bK wK emb_D])
qed

theorem exists_normal_integral_primitive_common_field_coordinates_with_galois_enumeration:
  fixes a b w :: complex
  assumes alg_a: "algebraic a"
    and alg_b: "algebraic b"
    and alg_w: "algebraic w"
  obtains \<eta> D ca cb cw K emb where
      "algebraic_int \<eta>"
    and "K = eval_img (\<rat> :: complex set) \<eta>"
    and "D = ext_degree (\<rat> :: complex set) \<eta>"
    and "D > 0"
    and "(\<forall>i<D. ca i \<in> (\<rat> :: complex set))"
    and "a = (\<Sum>i<D. ca i * \<eta> ^ i)"
    and "(\<forall>i<D. cb i \<in> (\<rat> :: complex set))"
    and "b = (\<Sum>i<D. cb i * \<eta> ^ i)"
    and "(\<forall>i<D. cw i \<in> (\<rat> :: complex set))"
    and "w = (\<Sum>i<D. cw i * \<eta> ^ i)"
    and "finite_subfield_tower (\<rat> :: complex set) K"
    and "normal_extension K (\<rat> :: complex set)"
    and "separable_extension K (\<rat> :: complex set)"
    and "a \<in> K"
    and "b \<in> K"
    and "w \<in> K"
    and "bij_betw emb {0..<D} (field_auto K (\<rat> :: complex set))"
proof -
  obtain \<theta> D ca0 cb0 cw0 K emb where
      K_def: "K = eval_img (\<rat> :: complex set) \<theta>"
    and D_def: "D = ext_degree (\<rat> :: complex set) \<theta>"
    and Dpos: "D > 0"
    and ca0_rat: "(\<forall>i<D. ca0 i \<in> (\<rat> :: complex set))"
    and a0_eq: "a = (\<Sum>i<D. ca0 i * \<theta> ^ i)"
    and cb0_rat: "(\<forall>i<D. cb0 i \<in> (\<rat> :: complex set))"
    and b0_eq: "b = (\<Sum>i<D. cb0 i * \<theta> ^ i)"
    and cw0_rat: "(\<forall>i<D. cw0 i \<in> (\<rat> :: complex set))"
    and w0_eq: "w = (\<Sum>i<D. cw0 i * \<theta> ^ i)"
    and finK: "finite_subfield_tower (\<rat> :: complex set) K"
    and normalK: "normal_extension K (\<rat> :: complex set)"
    and separableK: "separable_extension K (\<rat> :: complex set)"
    and aK: "a \<in> K"
    and bK: "b \<in> K"
    and wK: "w \<in> K"
    and ebij: "bij_betw emb {0..<D} (field_auto K (\<rat> :: complex set))"
    by (rule exists_normal_primitive_common_field_coordinates_with_galois_enumeration[OF alg_a alg_b alg_w])
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  interpret Q: Subfield "(\<rat> :: complex set)"
    by (rule sfQ)
  interpret T: finite_subfield_tower "\<rat>" K
    by (rule finK)
  have \<theta>K: "\<theta> \<in> K"
    using K_def Q.eval_img_self by simp
  have algQ: "algebraic_over (\<rat> :: complex set) \<theta>"
    by (rule T.finite_extension_algebraic[OF \<theta>K])
  have alg\<theta>: "algebraic \<theta>"
  proof -
    obtain p where p_over: "p \<in> poly_over (\<rat> :: complex set)"
      and p_nz: "p \<noteq> 0"
      and p_root: "poly p \<theta> = 0"
      using algQ unfolding algebraic_over_def by blast
    have coeff_rat: "\<forall>i. Polynomial.coeff p i \<in> (\<rat> :: complex set)"
      using p_over by (simp add: Q.poly_over_iff)
    show ?thesis
      unfolding algebraic_altdef
      using coeff_rat p_nz p_root by blast
  qed
  obtain c :: int where c_nz: "c \<noteq> 0"
    and cint: "algebraic_int (of_int c * \<theta>)"
    using exists_int_mul_algebraic_int[OF alg\<theta>] by blast
  define \<eta> where "\<eta> = of_int c * \<theta>"
  define ca where "ca i = ca0 i / of_int c ^ i" for i
  define cb where "cb i = cb0 i / of_int c ^ i" for i
  define cw where "cw i = cw0 i / of_int c ^ i" for i
  have cQ: "(of_int c :: complex) \<in> (\<rat> :: complex set)"
    by simp
  have cC_nz: "(of_int c :: complex) \<noteq> 0"
    using c_nz by simp
  have eta_int: "algebraic_int \<eta>"
    unfolding \<eta>_def by (rule cint)
  have K_eta: "K = eval_img (\<rat> :: complex set) \<eta>"
    unfolding \<eta>_def K_def
    using Q.eval_img_scale_eq[of \<theta> "of_int c", OF algQ cQ cC_nz] by simp
  have D_eta: "D = ext_degree (\<rat> :: complex set) \<eta>"
    unfolding \<eta>_def D_def
    using Q.ext_degree_scale_eq[of \<theta> "of_int c", OF algQ cQ cC_nz] by simp
  have ca_rat: "(\<forall>i<D. ca i \<in> (\<rat> :: complex set))"
    unfolding ca_def using ca0_rat by simp
  have cb_rat: "(\<forall>i<D. cb i \<in> (\<rat> :: complex set))"
    unfolding cb_def using cb0_rat by simp
  have cw_rat: "(\<forall>i<D. cw i \<in> (\<rat> :: complex set))"
    unfolding cw_def using cw0_rat by simp
  have a_eq: "a = (\<Sum>i<D. ca i * \<eta> ^ i)"
  proof -
    have "a = (\<Sum>i<D. ca0 i * \<theta> ^ i)"
      by (rule a0_eq)
    also have "\<dots> = (\<Sum>i<D. ca i * \<eta> ^ i)"
      unfolding ca_def \<eta>_def
      by (rule sum.cong[OF refl]) (use c_nz in \<open>simp add: field_simps power_mult_distrib\<close>)
    finally show ?thesis .
  qed
  have b_eq: "b = (\<Sum>i<D. cb i * \<eta> ^ i)"
  proof -
    have "b = (\<Sum>i<D. cb0 i * \<theta> ^ i)"
      by (rule b0_eq)
    also have "\<dots> = (\<Sum>i<D. cb i * \<eta> ^ i)"
      unfolding cb_def \<eta>_def
      by (rule sum.cong[OF refl]) (use c_nz in \<open>simp add: field_simps power_mult_distrib\<close>)
    finally show ?thesis .
  qed
  have w_eq: "w = (\<Sum>i<D. cw i * \<eta> ^ i)"
  proof -
    have "w = (\<Sum>i<D. cw0 i * \<theta> ^ i)"
      by (rule w0_eq)
    also have "\<dots> = (\<Sum>i<D. cw i * \<eta> ^ i)"
      unfolding cw_def \<eta>_def
      by (rule sum.cong[OF refl]) (use c_nz in \<open>simp add: field_simps power_mult_distrib\<close>)
    finally show ?thesis .
  qed
  show thesis
    by (rule that[OF eta_int K_eta D_eta Dpos ca_rat a_eq cb_rat b_eq cw_rat w_eq
          finK normalK separableK aK bK wK ebij])
qed

lemma indexed_galois_images_of_primitive_generator_inj:
  fixes K :: "complex set"
  fixes \<theta> :: complex
  fixes D :: nat
  fixes emb :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  assumes K_def: "K = eval_img (\<rat> :: complex set) \<theta>"
    and algQ: "algebraic_over (\<rat> :: complex set) \<theta>"
    and ebij: "bij_betw emb {0..<D} (field_auto K (\<rat> :: complex set))"
  shows "inj_on (\<lambda>i. emb i \<theta>) {0..<D}"
proof (rule inj_onI)
  fix i j
  assume i: "i \<in> {0..<D}"
  assume j: "j \<in> {0..<D}"
  assume eq: "emb i \<theta> = emb j \<theta>"
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  have si: "emb i \<in> field_auto K (\<rat> :: complex set)"
    using ebij i by (auto simp: bij_betw_def)
  have sj: "emb j \<in> field_auto K (\<rat> :: complex set)"
    using ebij j by (auto simp: bij_betw_def)
  have si': "emb i \<in> field_auto (eval_img (\<rat> :: complex set) \<theta>) (\<rat> :: complex set)"
    using si by (simp add: K_def)
  have sj': "emb j \<in> field_auto (eval_img (\<rat> :: complex set) \<theta>) (\<rat> :: complex set)"
    using sj by (simp add: K_def)
  have "emb i = emb j"
    by (rule field_auto_determined_by_gen[OF sfQ algQ si' sj' eq])
  then show "i = j"
    using ebij i j by (auto simp: bij_betw_def inj_on_def)
qed

lemma field_auto_power_basis_indep:
  fixes K :: "complex set"
  fixes \<theta> :: complex
  fixes \<sigma> :: "complex \<Rightarrow> complex"
  fixes c :: "nat \<Rightarrow> int"
  assumes K_def: "K = eval_img (\<rat> :: complex set) \<theta>"
    and algQ: "algebraic_over (\<rat> :: complex set) \<theta>"
    and sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)"
    and zero: "(\<Sum>i<ext_degree (\<rat> :: complex set) \<theta>. of_int (c i) * (\<sigma> \<theta>) ^ i) = 0"
  shows "\<forall>i<ext_degree (\<rat> :: complex set) \<theta>. c i = 0"
proof -
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  interpret Q: Subfield "(\<rat> :: complex set)"
    by (rule sfQ)
  have sfK: "Subfield K"
    unfolding K_def by (rule Q.subfield_eval_img[OF algQ])
  interpret KS: Subfield K
    by (rule sfK)
  have QK: "(\<rat> :: complex set) \<subseteq> K"
    unfolding K_def using Q.eval_img_base by blast
  define \<tau> where "\<tau> = (\<lambda>x\<in>K. inv_into K \<sigma> x)"
  have tau_auto: "\<tau> \<in> field_auto K (\<rat> :: complex set)"
    unfolding \<tau>_def by (rule field_auto_inverse[OF sfK sigma QK])
  have hom_tau: "field_hom_on K \<tau>"
    by (rule field_auto_imp_field_hom_on[OF sfK tau_auto])
  have thetaK: "\<theta> \<in> K"
    unfolding K_def by (rule Q.eval_img_self)
  have sigmaK: "\<sigma> \<in> K \<rightarrow>\<^sub>E K"
    using sigma by (simp add: field_auto_mem_iff)
  have sigma_bij: "bij_betw \<sigma> K K"
    using sigma by (simp add: field_auto_mem_iff)
  have sigma_thetaK: "\<sigma> \<theta> \<in> K"
    using sigmaK thetaK by (auto simp: PiE_iff)
  have tau_sigma_theta: "\<tau> (\<sigma> \<theta>) = \<theta>"
    unfolding \<tau>_def
    using thetaK sigmaK sigma_bij by (simp add: PiE_iff bij_betw_def inv_into_f_f)
  have coeff_fix: "\<tau> (of_int (c i)) = of_int (c i)" for i
    using tau_auto by (auto simp: field_auto_mem_iff)
  have term_in_K: "of_int (c i) * (\<sigma> \<theta>) ^ i \<in> K" for i
  proof -
    have coeffQ: "(of_int (c i) :: complex) \<in> (\<rat> :: complex set)"
      by simp
    have "of_int (c i) \<in> K"
      using QK coeffQ by blast
    moreover have "(\<sigma> \<theta>) ^ i \<in> K"
      by (rule KS.power_closed[OF sigma_thetaK])
    ultimately show ?thesis
      by (rule KS.mult_closed)
  qed
  have tau_term:
    "\<tau> (of_int (c i) * (\<sigma> \<theta>) ^ i) = of_int (c i) * \<theta> ^ i" for i
  proof -
    have coeffQ: "(of_int (c i) :: complex) \<in> (\<rat> :: complex set)"
      by simp
    have coeffK: "of_int (c i) \<in> K"
      using QK coeffQ by blast
    have "\<tau> (of_int (c i) * (\<sigma> \<theta>) ^ i) =
        \<tau> (of_int (c i)) * \<tau> ((\<sigma> \<theta>) ^ i)"
      by (rule field_hom_on.hom_mult[OF hom_tau coeffK]) (use sigma_thetaK in auto)
    also have "\<dots> = of_int (c i) * \<tau> ((\<sigma> \<theta>) ^ i)"
      by (simp add: coeff_fix)
    also have "\<dots> = of_int (c i) * (\<tau> (\<sigma> \<theta>)) ^ i"
      by (simp add: field_hom_on.hom_power[OF hom_tau sigma_thetaK])
    also have "\<dots> = of_int (c i) * \<theta> ^ i"
      by (simp add: tau_sigma_theta)
    finally show ?thesis .
  qed
  have zero_theta: "(\<Sum>i<ext_degree (\<rat> :: complex set) \<theta>. of_int (c i) * \<theta> ^ i) = 0"
  proof -
    have "0 = \<tau> 0"
      using field_hom_on.hom_0[OF hom_tau] by simp
    also have "\<dots> = \<tau> (\<Sum>i<ext_degree (\<rat> :: complex set) \<theta>. of_int (c i) * (\<sigma> \<theta>) ^ i)"
      using zero by simp
    also have "\<dots> = (\<Sum>i<ext_degree (\<rat> :: complex set) \<theta>. \<tau> (of_int (c i) * (\<sigma> \<theta>) ^ i))"
      by (rule field_hom_on.hom_sum[OF hom_tau]) (use term_in_K in auto)
    also have "\<dots> = (\<Sum>i<ext_degree (\<rat> :: complex set) \<theta>. of_int (c i) * \<theta> ^ i)"
      by (rule sum.cong[OF refl]) (rule tau_term)
    finally show ?thesis
      by simp
  qed
  have coeffQ':
    "\<And>i. i < ext_degree (\<rat> :: complex set) \<theta> \<Longrightarrow> (of_int (c i) :: complex) \<in> (\<rat> :: complex set)"
    by simp
  let ?coeff = "\<lambda>i. (of_int (c i) :: complex)"
  have coeff_zero:
    "\<forall>i<ext_degree (\<rat> :: complex set) \<theta>. ?coeff i = 0"
    by (rule Subfield.power_basis_indep[OF Q.Subfield_axioms algQ coeffQ' zero_theta])
  then show ?thesis
    by auto
qed

lemma field_auto_preserves_algebraic_int:
  fixes K :: "complex set"
  fixes \<sigma> :: "complex \<Rightarrow> complex"
  fixes x :: complex
  assumes Ksub: "Subfield K"
    and QK: "(\<rat> :: complex set) \<subseteq> K"
    and sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)"
    and xK: "x \<in> K"
    and ai: "algebraic_int x"
  shows "algebraic_int (\<sigma> x)"
proof -
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  have hom: "field_hom_on K \<sigma>"
    by (rule field_auto_imp_field_hom_on[OF Ksub sigma])
  have fixQ: "\<And>y. y \<in> (\<rat> :: complex set) \<Longrightarrow> \<sigma> y = y"
    using sigma by (auto simp: field_auto_mem_iff)
  obtain p :: "int poly" where p_root: "poly (map_poly of_int p) x = 0"
    and p_monic: "Polynomial.lead_coeff p = 1"
    using ai by (auto simp: algebraic_int_altdef_ipoly)
  have pQ: "map_poly of_int p \<in> poly_over (\<rat> :: complex set)"
    by (auto simp: poly_over_def)
  have pK: "map_poly of_int p \<in> poly_over K"
    using pQ poly_over_mono[OF QK] by blast
  have root_sigma: "poly (map_poly of_int p) (\<sigma> x) = 0"
    by (rule hom_preserves_roots[OF hom sfQ QK fixQ pQ xK p_root])
  show ?thesis
    using p_monic root_sigma by (auto simp: algebraic_int_altdef_ipoly)
qed

lemma indexed_galois_image_power_basis_indep:
  fixes K :: "complex set"
  fixes \<theta> :: complex
  fixes D :: nat
  fixes emb :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  fixes i :: nat
  fixes c :: "nat \<Rightarrow> int"
  assumes K_def: "K = eval_img (\<rat> :: complex set) \<theta>"
    and D_def: "D = ext_degree (\<rat> :: complex set) \<theta>"
    and algQ: "algebraic_over (\<rat> :: complex set) \<theta>"
    and ebij: "bij_betw emb {0..<D} (field_auto K (\<rat> :: complex set))"
    and ilt: "i < D"
    and zero: "(\<Sum>j<D. of_int (c j) * (emb i \<theta>) ^ j) = 0"
  shows "\<forall>j<D. c j = 0"
proof -
  have sigma: "emb i \<in> field_auto K (\<rat> :: complex set)"
    using ebij ilt by (auto simp: bij_betw_def)
  have zero': "(\<Sum>j<ext_degree (\<rat> :: complex set) \<theta>. of_int (c j) * (emb i \<theta>) ^ j) = 0"
    using zero by (simp add: D_def)
  have "(\<forall>j<ext_degree (\<rat> :: complex set) \<theta>. c j = 0)"
    by (rule field_auto_power_basis_indep[OF K_def algQ sigma zero'])
  then show ?thesis
    by (simp add: D_def)
qed

lemma indexed_galois_image_power_basis_algebraic_int:
  fixes K :: "complex set"
  fixes \<eta> :: complex
  fixes D :: nat
  fixes emb :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  assumes K_def: "K = eval_img (\<rat> :: complex set) \<eta>"
    and D_def: "D = ext_degree (\<rat> :: complex set) \<eta>"
    and algQ: "algebraic_over (\<rat> :: complex set) \<eta>"
    and ebij: "bij_betw emb {0..<D} (field_auto K (\<rat> :: complex set))"
    and ilt: "i < D"
    and eta_int: "algebraic_int \<eta>"
  shows "algebraic_int ((emb i \<eta>) ^ j)"
proof -
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  interpret Q: Subfield "(\<rat> :: complex set)"
    by (rule sfQ)
  have sfK: "Subfield K"
    unfolding K_def by (rule Q.subfield_eval_img[OF algQ])
  have QK: "(\<rat> :: complex set) \<subseteq> K"
    unfolding K_def using Q.eval_img_base by blast
  have sigma: "emb i \<in> field_auto K (\<rat> :: complex set)"
    using ebij ilt by (auto simp: bij_betw_def)
  have etaK: "\<eta> \<in> K"
    unfolding K_def by (rule Q.eval_img_self)
  have ai_emb: "algebraic_int (emb i \<eta>)"
    by (rule field_auto_preserves_algebraic_int[OF sfK QK sigma etaK eta_int])
  then show ?thesis
    by (rule algebraic_int_power)
qed

context
  fixes K :: "complex set"
  assumes finite: "finite_subfield_tower (\<rat> :: complex set) K"
    and normal: "normal_extension K (\<rat> :: complex set)"
    and separable: "separable_extension K (\<rat> :: complex set)"
begin

interpretation T: finite_subfield_tower "\<rat>" K
  by (rule finite)

lemma exists_galois_automorphism_enumeration:
  obtains emb where "bij_betw emb {0..<T.extension_degree} (field_auto K (\<rat> :: complex set))"
proof -
  have finG: "finite (field_auto K (\<rat> :: complex set))"
    by (rule finite_normal_separable_field_auto[OF finite normal separable])
  have cardG: "card (field_auto K (\<rat> :: complex set)) = T.extension_degree"
    by (rule finite_normal_separable_galois_degree[OF finite normal separable])
  obtain emb where emb: "bij_betw emb {0..<card (field_auto K (\<rat> :: complex set))} (field_auto K (\<rat> :: complex set))"
    using ex_bij_betw_nat_finite[OF finG] by blast
  have "bij_betw emb {0..<T.extension_degree} (field_auto K (\<rat> :: complex set))"
    using emb by (simp add: cardG)
  then show thesis
    by (rule that)
qed

lemma minpoly_root_of_min_int_poly_root:
  fixes x z :: complex
  assumes ai: "algebraic_int x"
    and zroot: "z \<in> set (complex_roots_of_int_poly (min_int_poly x))"
  shows "poly (minpoly (\<rat> :: complex set) x) z = 0"
proof -
  have alg: "algebraic x"
    using ai by auto
  have algQ: "algebraic_over (\<rat> :: complex set) x"
    by (rule algebraic_imp_algebraic_over_Rats[OF alg])
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  interpret Q: Subfield "(\<rat> :: complex set)"
    by (rule sfQ)
  let ?p = "of_int_poly (min_int_poly x)"
  have p_over: "?p \<in> poly_over (\<rat> :: complex set)"
    by (auto simp: poly_over_def)
  have p_root: "poly ?p x = 0"
    using alg by (auto simp: min_int_poly_represents)
  have p0: "min_int_poly x \<noteq> 0"
    using alg by auto
  have p_z: "poly ?p z = 0"
    using zroot complex_roots_of_int_poly(1)[OF p0] by simp
  have pdeg_ne0: "Polynomial.degree (min_int_poly x) \<noteq> 0"
    using alg by auto
  have prim_p: "primitive (min_int_poly x)"
    using irreducible_content[OF min_int_poly_irreducible[of x]] pdeg_ne0 by auto
  have cont_p: "content (min_int_poly x) = 1"
    using prim_p by (simp add: primitive_iff_content_eq_1)
  have irr_rat: "irreducible (map_poly of_int (min_int_poly x) :: rat poly)"
    by (rule irreducible_int_imp_rat[OF min_int_poly_irreducible[of x] pdeg_ne0 cont_p])
  have deg_rat_ne0: "Polynomial.degree (map_poly of_int (min_int_poly x) :: rat poly) \<noteq> 0"
    using pdeg_ne0 by (simp add: Polynomial.degree_map_poly)
  have deg_rat: "Polynomial.degree (map_poly of_int (min_int_poly x) :: rat poly) > 0"
    using deg_rat_ne0 by linarith
  have irr_Q: "irreducible_over (\<rat> :: complex set) ?p"
    using irreducible_imp_irreducible_over_Rats[OF irr_rat deg_rat] by simp
  have minQ: "is_minpoly (\<rat> :: complex set) x (minpoly (\<rat> :: complex set) x)"
    by (rule Subfield.is_minpoly_minpoly[OF sfQ algQ])
  show ?thesis
    by (rule Subfield.irreducible_over_root_is_minpoly_root[OF sfQ irr_Q p_over minQ p_root p_z])
qed

theorem cmod_root_le_of_finite_galois_image_bound:
  fixes x z :: complex
  assumes xK: "x \<in> K"
  assumes ai: "algebraic_int x"
  assumes zroot: "z \<in> set (complex_roots_of_int_poly (min_int_poly x))"
  assumes bound: "\<And>\<sigma>. \<sigma> \<in> field_auto K (\<rat> :: complex set) \<Longrightarrow> cmod (\<sigma> x) \<le> H"
  shows "cmod z \<le> H"
proof -
  have zmin: "poly (minpoly (\<rat> :: complex set) x) z = 0"
    by (rule minpoly_root_of_min_int_poly_root[OF ai zroot])
  obtain \<sigma> where sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)" and sx: "\<sigma> x = z"
    using finite_galois_root_transfer[OF finite normal separable xK zmin] by blast
  show ?thesis
    using bound[OF sigma] sx by simp
qed

lemma gs_house_le_of_finite_galois_image_bound:
  fixes x :: complex
  assumes xK: "x \<in> K"
  assumes ai: "algebraic_int x"
  assumes H_nonneg: "0 \<le> H"
  assumes bound: "\<And>\<sigma>. \<sigma> \<in> field_auto K (\<rat> :: complex set) \<Longrightarrow> cmod (\<sigma> x) \<le> H"
  shows "gs_house x \<le> H"
proof (rule gs_house_le_of_roots_le[OF H_nonneg])
  fix z
  assume z: "z \<in> set (complex_roots_of_int_poly (min_int_poly x))"
  show "cmod z \<le> H"
  proof (rule cmod_root_le_of_finite_galois_image_bound[OF xK ai z])
    fix \<sigma>
    assume "\<sigma> \<in> field_auto K (\<rat> :: complex set)"
    then show "cmod (\<sigma> x) \<le> H"
      by (rule bound)
  qed
qed

lemma cmod_root_le_of_indexed_galois_image_bound:
  fixes emb :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  fixes D :: nat
  fixes x z :: complex
  assumes ebij: "bij_betw emb {0..<D} (field_auto K (\<rat> :: complex set))"
  assumes xK: "x \<in> K"
  assumes ai: "algebraic_int x"
  assumes zroot: "z \<in> set (complex_roots_of_int_poly (min_int_poly x))"
  assumes bound: "\<And>i. i < D \<Longrightarrow> cmod (emb i x) \<le> H"
  shows "cmod z \<le> H"
proof -
  have bound_auto: "\<And>\<sigma>. \<sigma> \<in> field_auto K (\<rat> :: complex set) \<Longrightarrow> cmod (\<sigma> x) \<le> H"
  proof -
    fix \<sigma>
    assume sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)"
    have "\<sigma> \<in> emb ` {0..<D}"
      using bij_betw_imp_surj_on[OF ebij] sigma by blast
    then obtain i where i: "i < D" "\<sigma> = emb i"
      by auto
    show "cmod (\<sigma> x) \<le> H"
      by (simp add: i bound)
  qed
  show ?thesis
  proof (rule cmod_root_le_of_finite_galois_image_bound[OF xK ai zroot])
    fix \<sigma>
    assume "\<sigma> \<in> field_auto K (\<rat> :: complex set)"
    then show "cmod (\<sigma> x) \<le> H"
      by (rule bound_auto)
  qed
qed

lemma gs_house_le_of_indexed_galois_image_bound:
  fixes emb :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  fixes D :: nat
  fixes x :: complex
  assumes ebij: "bij_betw emb {0..<D} (field_auto K (\<rat> :: complex set))"
  assumes xK: "x \<in> K"
  assumes ai: "algebraic_int x"
  assumes H_nonneg: "0 \<le> H"
  assumes bound: "\<And>i. i < D \<Longrightarrow> cmod (emb i x) \<le> H"
  shows "gs_house x \<le> H"
proof (rule gs_house_le_of_roots_le[OF H_nonneg])
  fix z
  assume z: "z \<in> set (complex_roots_of_int_poly (min_int_poly x))"
  show "cmod z \<le> H"
  proof (rule cmod_root_le_of_indexed_galois_image_bound[OF ebij xK ai z])
    fix i
    assume "i < D"
    then show "cmod (emb i x) \<le> H"
      by (rule bound)
  qed
qed

end

end
