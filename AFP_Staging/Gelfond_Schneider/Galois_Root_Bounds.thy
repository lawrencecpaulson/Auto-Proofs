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
    GS_Setup
    GS_House
    "HOL-New_Algebra.Field_Extension_Tower"
    "HOL-New_Algebra.Galois_Simple_Degree"
    "HOL-New_Algebra.Galois_Finite_Correspondence"
    "HOL-New_Algebra.Galois_Transitivity"
begin

theorem exists_finite_normal_rational_extension_of_algebraic:
  fixes \<theta> :: complex
  assumes algQ: "algebraic_over \<rat> \<theta>"
  obtains K where "finite_subfield_tower \<rat> K"
    and "normal_extension K \<rat>"
    and "separable_extension K \<rat>"
    and "eval_img \<rat> \<theta> \<subseteq> K"
proof -
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  interpret Q: Subfield "(\<rat> :: complex set)"
    by (rule sfQ)
  let ?p = "minpoly \<rat> \<theta>"
  define K where "K \<equiv> generate_field (\<rat> \<union> poly_root_set ?p)"
  have p_over: "?p \<in> poly_over \<rat>"
    by (rule Q.minpoly_over[OF algQ])
  have p0: "?p \<noteq> 0"
    by (rule Q.minpoly_nonzero[OF algQ])
  have split: "splitting_field \<rat> ?p K"
    unfolding splitting_field_def K_def
    using p_over p0 by simp
  have fin_roots: "finite (poly_root_set ?p)"
    by (rule finite_poly_root_set[OF p0])
  have alg_roots: "\<And>r. r \<in> poly_root_set ?p \<Longrightarrow> algebraic_over \<rat> r"
    by (rule splitting_field_root_algebraic[OF split])
  obtain L where finL: "finite_subfield_tower \<rat> L"
    and QL: "\<rat> \<subseteq> L"
    and rootsL: "poly_root_set ?p \<subseteq> L"
    using exists_finite_subfield_tower[OF sfQ fin_roots alg_roots] by blast
  interpret L: finite_subfield_tower "\<rat>" L
    by (rule finL)
  have sfK: "Subfield K"
    by (rule splitting_field_subfield[OF split])
  have "\<rat> \<subseteq> K"
    by (rule splitting_field_base_subset[OF split])
  have KL: "K \<subseteq> L"
    by (simp add: K_def L.base_subset L.ext.Subfield_axioms generate_field_least rootsL)
  have finK: "finite_subfield_tower \<rat> K"
    by (rule finite_subfield_tower_intermediate_left[OF finL sfK \<open>\<rat> \<subseteq> K\<close> KL])
  have normal_sep: "normal_extension K \<rat> \<and> separable_extension K \<rat>"
    by (rule splitting_field_normal_separable[OF split complex_subfield_Rats])
  have theta_root: "\<theta> \<in> poly_root_set ?p"
    using Q.minpoly_root[OF algQ] by simp
  have thetaK: "\<theta> \<in> K"
    using theta_root splitting_field_roots_subset[OF split] by blast
  have eval_sub: "eval_img \<rat> \<theta> \<subseteq> K"
    by (simp add: Subfield.eval_img_eq_generate_field \<open>\<rat> \<subseteq> K\<close> algQ
        generate_field_least sfK sfQ thetaK)
  then show thesis
    using finK normal_sep that by force
qed

theorem exists_normal_common_field_coordinates_of_algebraic_triple:
  fixes a b w :: complex
  assumes alg_a: "algebraic a"
    and alg_b: "algebraic b"
    and alg_w: "algebraic w"
  obtains \<theta> D ca cb cw K where
      "D = ext_degree \<rat> \<theta>"
    and "D > 0"
    and "rational_power_basis_coordinates D \<theta> ca cb cw a b w"
    and "finite_subfield_tower \<rat> K"
    and "normal_extension K \<rat>"
    and "separable_extension K \<rat>"
    and "eval_img \<rat> \<theta> \<subseteq> K"
    and "a \<in> K" "b \<in> K" "w \<in> K"
proof -
  obtain \<theta> where aE: "a \<in> eval_img \<rat> \<theta>"
    and bE: "b \<in> eval_img \<rat> \<theta>"
    and wE: "w \<in> eval_img \<rat> \<theta>"
    and algQ: "algebraic_over \<rat> \<theta>"
    by (rule exists_primitive_rational_common_field_of_algebraic_triple[OF alg_a alg_b alg_w])
  define D where "D \<equiv> ext_degree \<rat> \<theta>"
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  obtain ca where ca_rat: "\<forall>i<D. ca i \<in> \<rat>" and a_eq: "a = (\<Sum>i<D. ca i * \<theta> ^ i)"
    using D_def Subfield.power_basis_span aE algQ sfQ by blast
  obtain cb where cb_rat: "\<forall>i<D. cb i \<in> \<rat>" and b_eq: "b = (\<Sum>i<D. cb i * \<theta> ^ i)"
    using D_def Subfield.power_basis_span algQ bE sfQ by blast
  obtain cw where cw_rat: "\<forall>i<D. cw i \<in> \<rat>" and w_eq: "w = (\<Sum>i<D. cw i * \<theta> ^ i)"
    using D_def Subfield.power_basis_span algQ wE sfQ by blast
  have "D > 0"
    unfolding D_def by (rule Subfield.ext_degree_pos[OF sfQ algQ])
  obtain K where finK: "finite_subfield_tower \<rat> K"
    and normalK: "normal_extension K \<rat>"
    and separableK: "separable_extension K \<rat>"
    and eval_sub: "eval_img \<rat> \<theta> \<subseteq> K"
    by (rule exists_finite_normal_rational_extension_of_algebraic[OF algQ])
  obtain "a \<in> K" "b \<in> K" "w \<in> K"
    using aE bE eval_sub wE by blast
  have "rational_power_basis_coordinates D \<theta> ca cb cw a b w"
    by unfold_locales (use ca_rat a_eq cb_rat b_eq cw_rat w_eq in auto)
  then show thesis
    using D_def \<open>0 < D\<close> \<open>a \<in> K\<close> \<open>b \<in> K\<close> \<open>w \<in> K\<close> eval_sub finK normalK
      separableK that by blast
qed

theorem exists_normal_primitive_common_field_coordinates_of_algebraic_triple:
  fixes a b w :: complex
  assumes alg_a: "algebraic a"
    and alg_b: "algebraic b"
    and alg_w: "algebraic w"
  obtains \<theta> D ca cb cw K where "K = eval_img \<rat> \<theta>"
    and "D = ext_degree \<rat> \<theta>"
    and "D > 0"
    and "rational_power_basis_coordinates D \<theta> ca cb cw a b w"
    and "finite_subfield_tower \<rat> K"
    and "normal_extension K \<rat>"
    and "separable_extension K \<rat>"
    and "a \<in> K" "b \<in> K" "w \<in> K"
proof -
  obtain \<theta>0 D0 ca0 cb0 cw0 K where D0_def: "D0 = ext_degree \<rat> \<theta>0"
    and "D0 > 0"
    and finK: "finite_subfield_tower \<rat> K"
    and normalK: "normal_extension K \<rat>"
    and separableK: "separable_extension K \<rat>"
    and eval_sub: "eval_img \<rat> \<theta>0 \<subseteq> K"
    and "a \<in> K" "b \<in> K" "w \<in> K"
    by (rule exists_normal_common_field_coordinates_of_algebraic_triple[OF alg_a alg_b alg_w])
  interpret T: finite_subfield_tower "\<rat>" K
    by (rule finK)
  obtain \<theta> where \<theta>K: "\<theta> \<in> K"
    and prim: "primitive_element \<rat> K \<theta>"
    using finite_separable_extension_is_simple[OF finK separableK] by blast
  have K_def: "K = eval_img \<rat> \<theta>"
    by (rule primitive_elementD[OF prim])
  have algQ: "algebraic_over \<rat> \<theta>"
    by (rule T.finite_extension_algebraic[OF \<theta>K])
  define D where "D = ext_degree \<rat> \<theta>"
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  obtain ca where ca_rat: "\<forall>i<D. ca i \<in> \<rat>" and a_eq: "a = (\<Sum>i<D. ca i * \<theta> ^ i)"
    using D_def K_def T.base.power_basis_span \<open>a \<in> K\<close> algQ by blast
  obtain cb where cb_rat: "\<forall>i<D. cb i \<in> \<rat>" and b_eq: "b = (\<Sum>i<D. cb i * \<theta> ^ i)"
    using D_def K_def T.base.power_basis_span \<open>b \<in> K\<close> algQ by blast
  obtain cw where cw_rat: "\<forall>i<D. cw i \<in> \<rat>" and w_eq: "w = (\<Sum>i<D. cw i * \<theta> ^ i)"
    using D_def K_def T.base.power_basis_span \<open>w \<in> K\<close> algQ by blast
  have "D > 0"
    unfolding D_def by (rule Subfield.ext_degree_pos[OF sfQ algQ])
  have "rational_power_basis_coordinates D \<theta> ca cb cw a b w"
    by unfold_locales (use ca_rat a_eq cb_rat b_eq cw_rat w_eq in auto)
  then show thesis
    using D_def K_def \<open>0 < D\<close> \<open>a \<in> K\<close> \<open>b \<in> K\<close> \<open>w \<in> K\<close> finK normalK
      separableK that by blast
qed

theorem exists_normal_primitive_common_field_coordinates_with_galois_enumeration:
  fixes a b w :: complex
  assumes alg_a: "algebraic a"
    and alg_b: "algebraic b"
    and alg_w: "algebraic w"
  obtains \<theta> D ca cb cw K emb where
      "K = eval_img \<rat> \<theta>"
    and "D = ext_degree \<rat> \<theta>"
    and "D > 0"
    and "rational_power_basis_coordinates D \<theta> ca cb cw a b w"
    and "finite_subfield_tower \<rat> K"
    and "normal_extension K \<rat>"
    and "separable_extension K \<rat>"
    and "a \<in> K" "b \<in> K" "w \<in> K"
    and "bij_betw emb {0..<D} (field_auto K \<rat>)"
proof -
  obtain \<theta> D ca cb cw K where
      K_def: "K = eval_img \<rat> \<theta>"
    and D_def: "D = ext_degree \<rat> \<theta>"
    and "D > 0"
    and coords: "rational_power_basis_coordinates D \<theta> ca cb cw a b w"
    and finK: "finite_subfield_tower \<rat> K"
    and normalK: "normal_extension K \<rat>"
    and separableK: "separable_extension K \<rat>"
    and "a \<in> K" "b \<in> K" "w \<in> K"
    by (rule exists_normal_primitive_common_field_coordinates_of_algebraic_triple[OF alg_a alg_b alg_w])
  interpret T: finite_subfield_tower "\<rat>" K
    by (rule finK)
  have degree_eq: "T.extension_degree = D"
    using D_def K_def T.primitive_element_degree primitive_elementI by blast
  have finG: "finite (field_auto K \<rat>)"
    by (rule finite_normal_separable_field_auto[OF finK normalK separableK])
  have cardG: "card (field_auto K \<rat>) = T.extension_degree"
    by (rule finite_normal_separable_galois_degree[OF finK normalK separableK])
  obtain emb where emb:
      "bij_betw emb {0..<card (field_auto K \<rat>)} (field_auto K \<rat>)"
    using ex_bij_betw_nat_finite[OF finG] by blast
  have emb_D: "bij_betw emb {0..<D} (field_auto K \<rat>)"
    using emb by (simp add: cardG degree_eq)
  show thesis
    by (rule that[OF K_def D_def \<open>D > 0\<close> coords
          finK normalK separableK \<open>a \<in> K\<close> \<open>b \<in> K\<close> \<open>w \<in> K\<close> emb_D])
qed

theorem exists_normal_integral_primitive_common_field_coordinates_with_galois_enumeration:
  fixes a b w :: complex
  assumes alg_a: "algebraic a"
    and alg_b: "algebraic b"
    and alg_w: "algebraic w"
  obtains \<eta> D ca cb cw K emb where
      "algebraic_int \<eta>"
    and "K = eval_img \<rat> \<eta>"
    and "D = ext_degree \<rat> \<eta>"
    and "D > 0"
    and "rational_power_basis_coordinates D \<eta> ca cb cw a b w"
    and "finite_subfield_tower \<rat> K"
    and "normal_extension K \<rat>"
    and "separable_extension K \<rat>"
    and "a \<in> K" "b \<in> K" "w \<in> K"
    and "bij_betw emb {0..<D} (field_auto K \<rat>)"
proof -
  obtain \<theta> D ca0 cb0 cw0 K emb where
      K_def: "K = eval_img \<rat> \<theta>"
    and D_def: "D = ext_degree \<rat> \<theta>"
    and "D > 0"
    and coords0: "rational_power_basis_coordinates D \<theta> ca0 cb0 cw0 a b w"
    and finK: "finite_subfield_tower \<rat> K"
    and normalK: "normal_extension K \<rat>"
    and separableK: "separable_extension K \<rat>"
    and "a \<in> K" "b \<in> K" "w \<in> K"
    and ebij: "bij_betw emb {0..<D} (field_auto K \<rat>)"
    by (rule exists_normal_primitive_common_field_coordinates_with_galois_enumeration[OF alg_a alg_b alg_w])
  interpret Coords0: rational_power_basis_coordinates D \<theta> ca0 cb0 cw0 a b w
    by (rule coords0)
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  interpret Q: Subfield "(\<rat> :: complex set)"
    by (rule sfQ)
  interpret T: finite_subfield_tower "\<rat>" K
    by (rule finK)
  have \<theta>K: "\<theta> \<in> K"
    using K_def Q.eval_img_self by simp
  have algQ: "algebraic_over \<rat> \<theta>"
    by (rule T.finite_extension_algebraic[OF \<theta>K])
  have alg\<theta>: "algebraic \<theta>"
    using algQ Q.poly_over_iff 
    unfolding algebraic_over_def by (meson algebraic_altdef)
  obtain c where c_nz: "c \<noteq> 0" and cint: "algebraic_int (of_int c * \<theta>)"
    using exists_int_mul_algebraic_int[OF alg\<theta>] by blast
  define \<eta> where "\<eta> \<equiv> of_int c * \<theta>"
  define ca where "ca i \<equiv> ca0 i / of_int c ^ i" for i
  define cb where "cb i \<equiv> cb0 i / of_int c ^ i" for i
  define cw where "cw i \<equiv> cw0 i / of_int c ^ i" for i
  have eta_int: "algebraic_int \<eta>"
    unfolding \<eta>_def by (rule cint)
  have K_eta: "K = eval_img \<rat> \<eta>"
    by (simp add: K_def Q.eval_img_scale_eq \<eta>_def algQ c_nz)
  have D_eta: "D = ext_degree \<rat> \<eta>"
    by (simp add: D_def Q.ext_degree_scale_eq \<eta>_def algQ c_nz)
  have a_eq: "a = (\<Sum>i<D. ca i * \<eta> ^ i)"
    using Coords0.a_eq ca_def \<eta>_def c_nz by (simp add: algebra_simps)
  have b_eq: "b = (\<Sum>i<D. cb i * \<eta> ^ i)"
    using Coords0.b_eq \<eta>_def c_nz cb_def by (simp add: algebra_simps)
  have w_eq: "w = (\<Sum>i<D. cw i * \<eta> ^ i)"
    using Coords0.w_eq \<eta>_def c_nz cw_def power_divide[of \<eta> c] by auto
  have ca_rat: "(\<forall>i<D. ca i \<in> \<rat>)"
    unfolding ca_def using Coords0.ca_rat by simp
  have cb_rat: "(\<forall>i<D. cb i \<in> \<rat>)"
    unfolding cb_def using Coords0.cb_rat by simp
  have cw_rat: "(\<forall>i<D. cw i \<in> \<rat>)"
    unfolding cw_def using Coords0.cw_rat by simp
  have coords: "rational_power_basis_coordinates D \<eta> ca cb cw a b w"
    by unfold_locales (use ca_rat a_eq cb_rat b_eq cw_rat w_eq in auto)
  show thesis
    by (rule that[OF eta_int K_eta D_eta \<open>D > 0\<close> coords
          finK normalK separableK \<open>a \<in> K\<close> \<open>b \<in> K\<close> \<open>w \<in> K\<close> ebij])
qed

lemma indexed_galois_images_of_primitive_generator_inj:
  fixes K :: "complex set"
  fixes \<theta> :: complex
  fixes D :: nat
  fixes emb :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  assumes K_def: "K = eval_img \<rat> \<theta>"
    and algQ: "algebraic_over \<rat> \<theta>"
    and ebij: "bij_betw emb {0..<D} (field_auto K \<rat>)"
  shows "inj_on (\<lambda>i. emb i \<theta>) {0..<D}"
proof (rule inj_onI)
  fix i j
  assume i: "i \<in> {0..<D}"
  assume j: "j \<in> {0..<D}"
  assume eq: "emb i \<theta> = emb j \<theta>"
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  have "emb i = emb j"
    by (metis (no_types) assms bij_betw_apply eq field_auto_determined_by_gen i j sfQ)
  then show "i = j"
    using ebij i j by (auto simp: bij_betw_def inj_on_def)
qed

lemma field_auto_power_basis_indep:
  fixes K :: "complex set"
  fixes \<theta> :: complex
  fixes \<sigma> :: "complex \<Rightarrow> complex"
  fixes c :: "nat \<Rightarrow> int"
  assumes K_def: "K = eval_img \<rat> \<theta>"
    and algQ: "algebraic_over \<rat> \<theta>"
    and sigma: "\<sigma> \<in> field_auto K \<rat>"
    and zero: "(\<Sum>i<ext_degree \<rat> \<theta>. of_int (c i) * (\<sigma> \<theta>) ^ i) = 0"
  shows "\<forall>i<ext_degree \<rat> \<theta>. c i = 0"
proof -
  interpret Q: Subfield "(\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  interpret KS: Subfield K
    unfolding K_def by (rule Q.subfield_eval_img[OF algQ])
  have "\<rat> \<subseteq> K"
    unfolding K_def using Q.eval_img_base by blast
  define \<tau> where "\<tau> \<equiv> (\<lambda>x\<in>K. inv_into K \<sigma> x)"
  have tau_auto: "\<tau> \<in> field_auto K \<rat>"
    by (simp add: KS.Subfield_axioms \<open>\<rat> \<subseteq> K\<close> \<tau>_def sigma field_auto_inverse)
  have hom_tau: "field_hom_on K \<tau>"
    using KS.Subfield_axioms field_auto_as_hom tau_auto by blast
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
  have tau_term: "\<tau> (of_int (c i) * (\<sigma> \<theta>) ^ i) = of_int (c i) * \<theta> ^ i" for i
  proof -
    have "\<tau> (of_int (c i) * (\<sigma> \<theta>) ^ i) = \<tau> (of_int (c i)) * \<tau> ((\<sigma> \<theta>) ^ i)"
      using \<open>\<rat> \<subseteq> K\<close> sigma_thetaK
      by (intro field_hom_on.hom_mult[OF hom_tau]) auto
    also have "\<dots> = of_int (c i) * \<theta> ^ i"
      by (simp add: coeff_fix tau_sigma_theta field_hom_on.hom_power[OF hom_tau sigma_thetaK])
    finally show ?thesis .
  qed
  have zero_theta: "(\<Sum>i<ext_degree \<rat> \<theta>. of_int (c i) * \<theta> ^ i) = 0"
  proof -
    have "0 = \<tau> (\<Sum>i<ext_degree \<rat> \<theta>. of_int (c i) * (\<sigma> \<theta>) ^ i)"
      using field_hom_on.hom_0[OF hom_tau] zero by simp
    also have "\<dots> = (\<Sum>i<ext_degree \<rat> \<theta>. \<tau> (of_int (c i) * (\<sigma> \<theta>) ^ i))"
      by (rule field_hom_on.hom_sum[OF hom_tau]) (use sigma_thetaK in auto)
    also have "\<dots> = (\<Sum>i<ext_degree \<rat> \<theta>. of_int (c i) * \<theta> ^ i)"
      using tau_term by presburger
    finally show ?thesis
      by simp
  qed
   show ?thesis
    using Subfield.power_basis_indep[OF Q.Subfield_axioms algQ _ zero_theta]
    by auto
qed

lemma field_auto_preserves_algebraic_int:
  fixes K :: "complex set"
  fixes \<sigma> :: "complex \<Rightarrow> complex"
  fixes x :: complex
  assumes Ksub: "Subfield K"
    and "\<rat> \<subseteq> K"
    and sigma: "\<sigma> \<in> field_auto K \<rat>"
    and xK: "x \<in> K"
    and ai: "algebraic_int x"
  shows "algebraic_int (\<sigma> x)"
proof -
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  have hom: "field_hom_on K \<sigma>"
    by (rule field_auto_imp_field_hom_on[OF Ksub sigma])
  have fixQ: "\<And>y. y \<in> \<rat> \<Longrightarrow> \<sigma> y = y"
    using sigma by (auto simp: field_auto_mem_iff)
  obtain p :: "int poly" where p_root: "poly (map_poly of_int p) x = 0"
    and p_monic: "Polynomial.lead_coeff p = 1"
    using ai by (auto simp: algebraic_int_altdef_ipoly)
  have pQ: "map_poly of_int p \<in> poly_over \<rat>"
    by (auto simp: poly_over_def)
  have pK: "map_poly of_int p \<in> poly_over K"
    using pQ poly_over_mono[OF \<open>\<rat> \<subseteq> K\<close>] by blast
  have root_sigma: "poly (map_poly of_int p) (\<sigma> x) = 0"
    by (rule hom_preserves_roots[OF hom sfQ \<open>\<rat> \<subseteq> K\<close> fixQ pQ xK p_root])
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
  assumes K_def: "K = eval_img \<rat> \<theta>"
    and D_def: "D = ext_degree \<rat> \<theta>"
    and algQ: "algebraic_over \<rat> \<theta>"
    and ebij: "bij_betw emb {0..<D} (field_auto K \<rat>)"
    and ilt: "i < D"
    and zero: "(\<Sum>j<D. of_int (c j) * (emb i \<theta>) ^ j) = 0"
  shows "\<forall>j<D. c j = 0"
proof -
  have sigma: "emb i \<in> field_auto K \<rat>"
    using ebij ilt by (auto simp: bij_betw_def)
  have "(\<Sum>j<ext_degree \<rat> \<theta>. of_int (c j) * (emb i \<theta>) ^ j) = 0"
    using zero by (simp add: D_def)
  then show ?thesis
    unfolding D_def
    using K_def algQ field_auto_power_basis_indep sigma by presburger
qed

lemma indexed_galois_image_power_basis_algebraic_int:
  fixes K :: "complex set"
  fixes \<eta> :: complex
  fixes D :: nat
  fixes emb :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  assumes K_def: "K = eval_img \<rat> \<eta>"
    and D_def: "D = ext_degree \<rat> \<eta>"
    and algQ: "algebraic_over \<rat> \<eta>"
    and ebij: "bij_betw emb {0..<D} (field_auto K \<rat>)"
    and ilt: "i < D"
    and eta_int: "algebraic_int \<eta>"
  shows "algebraic_int ((emb i \<eta>) ^ j)"
proof -
  interpret Q: Subfield "(\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  have sfK: "Subfield K"
    unfolding K_def by (rule Q.subfield_eval_img[OF algQ])
  have "\<rat> \<subseteq> K"
    unfolding K_def using Q.eval_img_base by blast
  have sigma: "emb i \<in> field_auto K \<rat>"
    using ebij ilt by (auto simp: bij_betw_def)
  have etaK: "\<eta> \<in> K"
    unfolding K_def by (rule Q.eval_img_self)
  then show ?thesis
    using \<open>\<rat> \<subseteq> K\<close> eta_int field_auto_preserves_algebraic_int sfK sigma
    by fastforce
qed

context
  fixes K :: "complex set"
  assumes finite: "finite_subfield_tower \<rat> K"
    and normal: "normal_extension K \<rat>"
    and separable: "separable_extension K \<rat>"
begin

interpretation T: finite_subfield_tower "\<rat>" K
  by (rule finite)

lemma exists_galois_automorphism_enumeration:
  obtains emb where "bij_betw emb {0..<T.extension_degree} (field_auto K \<rat>)"
proof -
  have finG: "finite (field_auto K \<rat>)"
    by (rule finite_normal_separable_field_auto[OF finite normal separable])
  have cardG: "card (field_auto K \<rat>) = T.extension_degree"
    by (rule finite_normal_separable_galois_degree[OF finite normal separable])
  obtain emb where emb: "bij_betw emb {0..<card (field_auto K \<rat>)} (field_auto K \<rat>)"
    using ex_bij_betw_nat_finite[OF finG] by blast
  then show thesis
    using emb that by (auto simp add: cardG)
qed

lemma minpoly_root_of_min_int_poly_root:
  fixes x z :: complex
  assumes ai: "algebraic_int x"
    and zroot: "z \<in> set (complex_roots_of_int_poly (min_int_poly x))"
  shows "poly (minpoly \<rat> x) z = 0"
proof -
  have alg: "algebraic x"
    using ai by auto
  have algQ: "algebraic_over \<rat> x"
    by (rule algebraic_imp_algebraic_over_Rats[OF alg])
  interpret Q: Subfield "(\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  let ?p = "of_int_poly (min_int_poly x)"
  have p_over: "?p \<in> poly_over \<rat>"
    by (auto simp: poly_over_def)
  have p_root: "poly ?p x = 0"
    using alg by (auto simp: min_int_poly_represents)
  have p_z: "poly ?p z = 0"
    using zroot complex_roots_of_int_poly(1) alg by simp
  have pdeg_ne0: "Polynomial.degree (min_int_poly x) \<noteq> 0"
    using alg by auto
  have prim_p: "primitive (min_int_poly x)"
    using irreducible_content[OF min_int_poly_irreducible[of x]] pdeg_ne0 by auto
  have cont_p: "Polynomial.content (min_int_poly x) = 1"
    using prim_p by (simp add: primitive_iff_content_eq_1)
  have irr_rat: "irreducible (map_poly of_int (min_int_poly x) :: rat poly)"
    using min_int_poly_irreducible[of x] pdeg_ne0 cont_p
    by (metis Polynomial_Factorial.irreducible_int_imp_rat)
  have deg_rat: "Polynomial.degree (map_poly of_int (min_int_poly x) :: rat poly) > 0"
    using pdeg_ne0 by (auto simp add: Polynomial.degree_map_poly)
  have irr_Q: "irreducible_over (\<rat> :: complex set) ?p"
    using irreducible_imp_irreducible_over_Rats[OF irr_rat deg_rat] by simp
  have minQ: "is_minpoly \<rat> x (minpoly \<rat> x)"
    by (simp add: T.base.is_minpoly_minpoly algQ)
  show ?thesis
    using T.base.irreducible_over_root_is_minpoly_root irr_Q minQ p_over p_root p_z
    by blast
qed

theorem cmod_root_le_of_finite_galois_image_bound:
  fixes x z :: complex
  assumes xK: "x \<in> K"
  assumes ai: "algebraic_int x"
  assumes zroot: "z \<in> set (complex_roots_of_int_poly (min_int_poly x))"
  assumes bound: "\<And>\<sigma>. \<sigma> \<in> field_auto K \<rat> \<Longrightarrow> cmod (\<sigma> x) \<le> H"
  shows "cmod z \<le> H"
proof -
  have zmin: "poly (minpoly \<rat> x) z = 0"
    by (rule minpoly_root_of_min_int_poly_root[OF ai zroot])
  obtain \<sigma> where sigma: "\<sigma> \<in> field_auto K \<rat>" and sx: "\<sigma> x = z"
    using finite_galois_root_transfer[OF finite normal separable xK zmin] by blast
  show ?thesis
    using bound[OF sigma] sx by simp
qed

lemma gs_house_le_of_finite_galois_image_bound:
  fixes x :: complex
  assumes "x \<in> K"
  assumes "algebraic_int x"
  assumes  "0 \<le> H"
  assumes "\<And>\<sigma>. \<sigma> \<in> field_auto K \<rat> \<Longrightarrow> cmod (\<sigma> x) \<le> H"
  shows "gs_house x \<le> H"
  using assms cmod_root_le_of_finite_galois_image_bound 
    gs_house_le_of_roots_le by presburger

lemma cmod_root_le_of_indexed_galois_image_bound:
  fixes emb :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  fixes D :: nat
  fixes x z :: complex
  assumes ebij: "bij_betw emb {0..<D} (field_auto K \<rat>)"
  assumes "x \<in> K"
  assumes "algebraic_int x"
  assumes "z \<in> set (complex_roots_of_int_poly (min_int_poly x))"
  assumes bound: "\<And>i. i < D \<Longrightarrow> cmod (emb i x) \<le> H"
  shows "cmod z \<le> H"
proof -
  have bound_auto: "\<And>\<sigma>. \<sigma> \<in> field_auto K \<rat> \<Longrightarrow> cmod (\<sigma> x) \<le> H"
    using bij_betw_imp_surj_on[OF ebij] bound by (metis atLeastLessThan_iff imageE) 
  show ?thesis
    using assms bound_auto cmod_root_le_of_finite_galois_image_bound
    by blast
qed

lemma gs_house_le_of_indexed_galois_image_bound:
  fixes emb :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  fixes D :: nat
  fixes x :: complex
  assumes ebij: "bij_betw emb {0..<D} (field_auto K \<rat>)"
  assumes xK: "x \<in> K"
  assumes ai: "algebraic_int x"
  assumes H_nonneg: "0 \<le> H"
  assumes bound: "\<And>i. i < D \<Longrightarrow> cmod (emb i x) \<le> H"
  shows "gs_house x \<le> H"
proof (rule gs_house_le_of_roots_le[OF H_nonneg])
  fix z
  assume "z \<in> set (complex_roots_of_int_poly (min_int_poly x))"
  then show "cmod z \<le> H"
    using xK ai bound cmod_root_le_of_indexed_galois_image_bound ebij
    by blast
qed

end

end
