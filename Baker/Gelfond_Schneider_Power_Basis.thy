(*  Title:      Baker/Gelfond_Schneider_Power_Basis.thy
    Author:     OpenAI Codex

Qualitative power-basis infrastructure for the standalone Gelfond-Schneider
route.  This packages the primitive normal field, its indexed Galois family,
and the resulting monogenic basis values `emb i eta ^ j` at the level needed
before any quantitative inverse-Vandermonde bounds are introduced.
*)

theory Gelfond_Schneider_Power_Basis
  imports Gelfond_Schneider_Galois_Root_Bounds
begin

locale finite_galois_power_basis =
  fixes K :: "complex set"
  fixes eta :: complex
  fixes D :: nat
  fixes emb :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  assumes K_def: "K = eval_img (\<rat> :: complex set) eta"
    and D_def: "D = ext_degree (\<rat> :: complex set) eta"
    and algQ: "algebraic_over (\<rat> :: complex set) eta"
    and eta_int: "algebraic_int eta"
    and ebij: "bij_betw emb {0..<D} (field_auto K (\<rat> :: complex set))"
begin

definition basis :: "nat \<Rightarrow> (complex \<Rightarrow> complex) \<Rightarrow> complex"
  where "basis j e = e eta ^ j"

lemma emb_in_field_auto:
  assumes "i < D"
  shows "emb i \<in> field_auto K (\<rat> :: complex set)"
  using ebij assms by (auto simp: bij_betw_def)

lemma indexed_images_inj:
  shows "inj_on (\<lambda>i. emb i eta) {0..<D}"
  by (rule indexed_galois_images_of_primitive_generator_inj[OF K_def algQ ebij])

lemma basis_indep_at_emb:
  assumes ilt: "i < D"
  assumes zero: "(\<Sum>j<D. of_int (c j) * basis j (emb i)) = 0"
  shows "\<forall>j<D. c j = 0"
proof -
  have "(\<Sum>j<D. of_int (c j) * (emb i eta) ^ j) = 0"
    using zero by (simp add: basis_def)
  then show ?thesis
    by (rule indexed_galois_image_power_basis_indep[OF K_def D_def algQ ebij ilt])
qed

lemma basis_algebraic_int_at_emb:
  assumes "i < D"
  shows "algebraic_int (basis j (emb i))"
  using indexed_galois_image_power_basis_algebraic_int[OF K_def D_def algQ ebij assms eta_int, of j]
  by (simp add: basis_def)

end


section \<open>Power basis bounds\<close>

context finite_galois_power_basis
begin

lemma Rats_subfield: "Subfield (\<rat> :: complex set)"
  using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)

lemma K_subfield: "Subfield K"
proof -
  interpret Q: Subfield "(\<rat> :: complex set)"
    by (rule Rats_subfield)
  show ?thesis
    unfolding K_def by (rule Q.subfield_eval_img[OF algQ])
qed

lemma Rats_subset_K: "(\<rat> :: complex set) \<subseteq> K"
proof -
  interpret Q: Subfield "(\<rat> :: complex set)"
    by (rule Rats_subfield)
  show ?thesis
    unfolding K_def using Q.eval_img_base by blast
qed

lemma eta_in_K: "eta \<in> K"
proof -
  interpret Q: Subfield "(\<rat> :: complex set)"
    by (rule Rats_subfield)
  show ?thesis
    unfolding K_def by (rule Q.eval_img_self)
qed

lemma identity_in_field_auto:
  "identity K \<in> field_auto K (\<rat> :: complex set)"
  by (rule field_auto_identity[OF K_subfield Rats_subset_K])

lemma obtains_identity_embedding_index:
  obtains i0 where "i0 < D" and "emb i0 = identity K"
proof -
  have "identity K \<in> emb ` {0..<D}"
    using ebij identity_in_field_auto
    by (auto simp: bij_betw_def)
  then obtain i0 where i0: "i0 < D" and emb0: "emb i0 = identity K"
    by auto
  show thesis
    using i0 emb0 that by auto
qed

lemma basis_at_identity [simp]:
  "basis j (identity K) = eta ^ j"
  using eta_in_K by (simp add: basis_def identity_apply)

lemma basis_eq_power_at_identity_embedding:
  assumes emb0: "emb i0 = identity K"
  shows "basis j (emb i0) = eta ^ j"
  using emb0 by simp

lemma basis_indep_at_identity_embedding:
  assumes i0lt: "i0 < D"
    and emb0: "emb i0 = identity K"
    and zero: "(\<Sum>j<D. of_int (c j) * basis j (emb i0)) = 0"
  shows "\<forall>j<D. c j = 0"
  using basis_indep_at_emb[OF i0lt] zero by simp

lemma emb_eta_in_K:
  assumes ilt: "i < D"
  shows "emb i eta \<in> K"
proof -
  have sigma: "emb i \<in> field_auto K (\<rat> :: complex set)"
    by (rule emb_in_field_auto[OF ilt])
  show ?thesis
    using sigma eta_in_K by (auto simp: field_auto_mem_iff PiE_iff)
qed

lemma basis_in_K_at_emb:
  assumes ilt: "i < D"
  shows "basis j (emb i) \<in> K"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have embK: "emb i eta \<in> K"
    by (rule emb_eta_in_K[OF ilt])
  show ?thesis
    unfolding basis_def by (rule KS.power_closed[OF embK])
qed

lemma sum_rat_power_in_K:
  assumes coeff_rat: "\<forall>i<D. c i \<in> (\<rat> :: complex set)"
  shows "(\<Sum>i<D. c i * eta ^ i) \<in> K"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have termK: "c i * eta ^ i \<in> K" if ilt: "i < D" for i
  proof -
    have ciK: "c i \<in> K"
      using coeff_rat ilt Rats_subset_K by blast
    have eta_pow_K: "eta ^ i \<in> K"
      by (rule KS.power_closed[OF eta_in_K])
    show ?thesis
      by (rule KS.mult_closed[OF ciK eta_pow_K])
  qed
  show ?thesis
    by (rule KS.sum_closed) (auto intro: termK)
qed

lemma sum_int_basis_at_emb_in_K:
  assumes ilt: "i < D"
  shows "(\<Sum>j<D. of_int (c j) * basis j (emb i)) \<in> K"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have termK: "of_int (c j) * basis j (emb i) \<in> K" if jlt: "j < D" for j
  proof -
    have coeffQ: "(of_int (c j) :: complex) \<in> (\<rat> :: complex set)"
      by simp
    have cintK: "of_int (c j) \<in> K"
      using Rats_subset_K coeffQ by blast
    have basisK: "basis j (emb i) \<in> K"
      by (rule basis_in_K_at_emb[OF ilt])
    show ?thesis
      by (rule KS.mult_closed[OF cintK basisK])
  qed
  show ?thesis
    by (rule KS.sum_closed) (auto intro: termK)
qed

lemma sum_int_power_algebraic_int:
  shows "algebraic_int (\<Sum>i<D. of_int (c i) * eta ^ i)"
proof (rule algebraic_int_sum)
  fix i
  assume imem: "i \<in> {..<D}"
  have cint: "algebraic_int (of_int (c i) :: complex)"
    by simp
  have etapow: "algebraic_int (eta ^ i)"
    by (rule algebraic_int_power[OF eta_int])
  show "algebraic_int (of_int (c i) * eta ^ i)"
    by (rule algebraic_int_times[OF cint etapow])
qed

lemma emb_sum_int_power:
  assumes ilt: "i < D"
  shows "emb i (\<Sum>j<D. of_int (c j) * eta ^ j) = (\<Sum>j<D. of_int (c j) * basis j (emb i))"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have sigma: "emb i \<in> field_auto K (\<rat> :: complex set)"
    by (rule emb_in_field_auto[OF ilt])
  have hom: "field_hom_on K (emb i)"
    by (rule field_auto_imp_field_hom_on[OF K_subfield sigma])
  have termK: "of_int (c j) * eta ^ j \<in> K" if jlt: "j < D" for j
  proof -
    have coeffQ: "(of_int (c j) :: complex) \<in> (\<rat> :: complex set)"
      by simp
    have cintK: "of_int (c j) \<in> K"
      using Rats_subset_K coeffQ by blast
    have etapowK: "eta ^ j \<in> K"
      by (rule KS.power_closed[OF eta_in_K])
    show ?thesis
      by (rule KS.mult_closed[OF cintK etapowK])
  qed
  have coeff_fix: "emb i (of_int (c j)) = of_int (c j)" for j
    using sigma by (auto simp: field_auto_mem_iff)
  have emb_term: "emb i (of_int (c j) * eta ^ j) = of_int (c j) * basis j (emb i)" if jlt: "j < D" for j
  proof -
    have coeffQ: "(of_int (c j) :: complex) \<in> (\<rat> :: complex set)"
      by simp
    have cintK: "of_int (c j) \<in> K"
      using Rats_subset_K coeffQ by blast
    have "emb i (of_int (c j) * eta ^ j) = emb i (of_int (c j)) * emb i (eta ^ j)"
      by (rule field_hom_on.hom_mult[OF hom cintK]) (use eta_in_K in auto)
    also have "... = of_int (c j) * emb i (eta ^ j)"
      by (simp add: coeff_fix)
    also have "... = of_int (c j) * (emb i eta) ^ j"
      by (simp add: field_hom_on.hom_power[OF hom eta_in_K])
    also have "... = of_int (c j) * basis j (emb i)"
      by (simp add: basis_def)
    finally show ?thesis .
  qed
  have "emb i (\<Sum>j<D. of_int (c j) * eta ^ j) = (\<Sum>j<D. emb i (of_int (c j) * eta ^ j))"
    by (rule field_hom_on.hom_sum[OF hom]) (use termK in auto)
  also have "... = (\<Sum>j<D. of_int (c j) * basis j (emb i))"
    by (rule sum.cong[OF refl]) (use emb_term in auto)
  finally show ?thesis .
qed

lemma sum_int_basis_at_emb_as_integral_element:
  assumes ilt: "i < D"
  obtains x where
    "x \<in> K"
    "algebraic_int x"
    "emb i x = (\<Sum>j<D. of_int (c j) * basis j (emb i))"
proof -
  let ?x = "(\<Sum>j<D. of_int (c j) * eta ^ j)"
  have xK: "?x \<in> K"
    by (rule sum_rat_power_in_K) auto
  have xint: "algebraic_int ?x"
    by (rule sum_int_power_algebraic_int)
  have xemb: "emb i ?x = (\<Sum>j<D. of_int (c j) * basis j (emb i))"
    by (rule emb_sum_int_power[OF ilt])
  show thesis
    by (rule that[of ?x]) (use xK xint xemb in auto)
qed

lemma represented_coordinate_as_integral_element:
  assumes ilt: "i < D"
  assumes repr:
    "\<forall>t<q * q.
      Matrix.vec_index v t =
        (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i))"
  assumes tlt: "t < q * q"
  obtains y where
    "y \<in> K"
    "algebraic_int y"
    "emb i y = Matrix.vec_index v t"
proof -
  have vt:
    "Matrix.vec_index v t =
      (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i))"
    using repr tlt by blast
  from sum_int_basis_at_emb_as_integral_element[OF ilt,
      where c = "\<lambda>j. Matrix.vec_index x (sg_pair_idx D t j)"]
  obtain y where yK: "y \<in> K"
    and yint: "algebraic_int y"
    and yemb:
      "emb i y =
        (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i))"
    by blast
  show thesis
    by (rule that[of y]) (use yK yint yemb vt in auto)
qed

lemma sum_int_basis_at_emb_as_integral_element_with_house_bound:
  assumes finite: "finite_subfield_tower (\<rat> :: complex set) K"
    and normal: "normal_extension K (\<rat> :: complex set)"
    and separable: "separable_extension K (\<rat> :: complex set)"
    and ilt: "i < D"
    and H_nonneg: "0 \<le> H"
    and emb_bound: "\<And>j. j < D \<Longrightarrow> cmod (\<Sum>k<D. of_int (c k) * basis k (emb j)) \<le> H"
  obtains x where
    "x \<in> K"
    "algebraic_int x"
    "emb i x = (\<Sum>k<D. of_int (c k) * basis k (emb i))"
    "gs_house x \<le> H"
proof -
  let ?x = "(\<Sum>k<D. of_int (c k) * eta ^ k)"
  have xK: "?x \<in> K"
    by (rule sum_rat_power_in_K) auto
  have xint: "algebraic_int ?x"
    by (rule sum_int_power_algebraic_int)
  have xemb: "emb i ?x = (\<Sum>k<D. of_int (c k) * basis k (emb i))"
    by (rule emb_sum_int_power[OF ilt])
  have xhouse: "gs_house ?x \<le> H"
  proof (rule gs_house_le_of_indexed_galois_image_bound[OF finite normal separable ebij xK xint H_nonneg])
    fix j
    assume jlt: "j < D"
    have "emb j ?x = (\<Sum>k<D. of_int (c k) * basis k (emb j))"
      by (rule emb_sum_int_power[OF jlt])
    then show "cmod (emb j ?x) \<le> H"
      using emb_bound[OF jlt] by simp
  qed
  show thesis
    by (rule that[of ?x]) (use xK xint xemb xhouse in auto)
qed

lemma represented_coordinate_as_integral_element_with_house_bound:
  assumes finite: "finite_subfield_tower (\<rat> :: complex set) K"
    and normal: "normal_extension K (\<rat> :: complex set)"
    and separable: "separable_extension K (\<rat> :: complex set)"
    and ilt: "i < D"
    and repr:
      "\<forall>t<q * q.
        Matrix.vec_index v t =
          (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i))"
    and tlt: "t < q * q"
    and H_nonneg: "0 \<le> H"
    and emb_bound:
      "\<And>j. j < D \<Longrightarrow>
        cmod (\<Sum>k<D. of_int (Matrix.vec_index x (sg_pair_idx D t k)) * basis k (emb j)) \<le> H"
  obtains y where
    "y \<in> K"
    "algebraic_int y"
    "emb i y = Matrix.vec_index v t"
    "gs_house y \<le> H"
proof -
  have vt:
    "Matrix.vec_index v t =
      (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i))"
    using repr tlt by blast
  let ?c = "\<lambda>j. Matrix.vec_index x (sg_pair_idx D t j)"
  have emb_bound0:
    "\<And>j. j < D \<Longrightarrow> cmod (\<Sum>k<D. of_int (?c k) * basis k (emb j)) \<le> H"
    using emb_bound by simp
  from sum_int_basis_at_emb_as_integral_element_with_house_bound[
      OF finite normal separable ilt H_nonneg emb_bound0]
  obtain y where yK: "y \<in> K"
    and yint: "algebraic_int y"
    and yemb: "emb i y = (\<Sum>j<D. of_int (?c j) * basis j (emb i))"
    and yhouse: "gs_house y \<le> H"
    by blast
  show thesis
    by (rule that[of y]) (use yK yint yemb yhouse vt in auto)
qed

lemma Dpos: "D > 0"
proof -
  interpret Q: Subfield "(\<rat> :: complex set)"
    by (rule Rats_subfield)
  show ?thesis
    unfolding D_def by (rule Subfield.ext_degree_pos[OF Rats_subfield algQ])
qed

lemma emb_eta_root_of_min_int_poly:
  assumes ilt: "i < D"
  shows "emb i eta \<in> set (complex_roots_of_int_poly (min_int_poly eta))"
proof -
  interpret Q: Subfield "(\<rat> :: complex set)"
    by (rule Rats_subfield)
  have sigma: "emb i \<in> field_auto K (\<rat> :: complex set)"
    by (rule emb_in_field_auto[OF ilt])
  have p_over: "of_int_poly (min_int_poly eta) \<in> poly_over (\<rat> :: complex set)"
    by (auto simp: poly_over_def)
  have root_eta: "poly (of_int_poly (min_int_poly eta)) eta = 0"
    using eta_int by (auto simp: min_int_poly_represents)
  have root_emb: "poly (of_int_poly (min_int_poly eta)) (emb i eta) = 0"
    by (rule field_auto_maps_root[OF K_subfield Rats_subfield Rats_subset_K sigma p_over eta_in_K root_eta])
  have p0: "min_int_poly eta \<noteq> 0"
    using eta_int by auto
  show ?thesis
    using root_emb complex_roots_of_int_poly(1)[OF p0] by simp
qed

lemma cmod_emb_eta_le_gs_house:
  assumes ilt: "i < D"
  shows "cmod (emb i eta) \<le> gs_house eta"
  by (rule cmod_le_gs_house_of_root[OF emb_eta_root_of_min_int_poly[OF ilt]])

lemma basis_algebraic_int_at_auto:
  assumes sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)"
    and jlt: "j < D"
  shows "algebraic_int (basis j \<sigma>)"
proof -
  have sfQ: "Subfield (\<rat> :: complex set)"
    by (rule Rats_subfield)
  have QK: "(\<rat> :: complex set) \<subseteq> K"
    by (rule Rats_subset_K)
  have ai_sigma: "algebraic_int (\<sigma> eta)"
    by (rule field_auto_preserves_algebraic_int[OF K_subfield QK sigma eta_in_K eta_int])
  show ?thesis
    using ai_sigma by (simp add: basis_def algebraic_int_power)
qed

lemma basis_indep_at_auto:
  assumes sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)"
    and zero: "(\<Sum>j<D. of_int (c j) * basis j \<sigma>) = 0"
  shows "\<forall>j<D. c j = 0"
proof -
  have zero': "(\<Sum>j<ext_degree (\<rat> :: complex set) eta. of_int (c j) * (\<sigma> eta) ^ j) = 0"
    using zero by (simp add: basis_def D_def)
  have all0: "\<forall>j<ext_degree (\<rat> :: complex set) eta. c j = 0"
    by (rule field_auto_power_basis_indep[OF K_def algQ sigma zero'])
  then show ?thesis
    by (simp add: D_def)
qed

lemma sigma_eta_root_of_min_int_poly:
  assumes sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)"
  shows "\<sigma> eta \<in> set (complex_roots_of_int_poly (min_int_poly eta))"
proof -
  have p_over: "of_int_poly (min_int_poly eta) \<in> poly_over (\<rat> :: complex set)"
    by (auto simp: poly_over_def)
  have root_eta: "poly (of_int_poly (min_int_poly eta)) eta = 0"
    using eta_int by (auto simp: min_int_poly_represents)
  have root_sigma: "poly (of_int_poly (min_int_poly eta)) (\<sigma> eta) = 0"
    by (rule field_auto_maps_root[OF K_subfield Rats_subfield Rats_subset_K sigma p_over eta_in_K root_eta])
  have p0: "min_int_poly eta \<noteq> 0"
    using eta_int by auto
  show ?thesis
    using root_sigma complex_roots_of_int_poly(1)[OF p0] by simp
qed

lemma cmod_sigma_eta_le_gs_house:
  assumes sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)"
  shows "cmod (\<sigma> eta) \<le> gs_house eta"
  by (rule cmod_le_gs_house_of_root[OF sigma_eta_root_of_min_int_poly[OF sigma]])

definition power_basis_entry_bound :: real
  where "power_basis_entry_bound = max 1 (gs_house eta) ^ (D - 1)"

lemma power_basis_entry_bound_nonneg [simp]:
  shows "0 \<le> power_basis_entry_bound"
  unfolding power_basis_entry_bound_def by simp

lemma basis_cmod_le_power_basis_entry_bound:
  assumes ilt: "i < D"
    and jlt: "j < D"
  shows "cmod (basis j (emb i)) \<le> power_basis_entry_bound"
proof -
  let ?H = "max 1 (gs_house eta)"
  have H_nonneg: "0 \<le> ?H"
    by simp
  have H_ge1: "1 \<le> ?H"
    by simp
  have emb_le: "cmod (emb i eta) \<le> ?H"
    using cmod_emb_eta_le_gs_house[OF ilt] by linarith
  have jle: "j \<le> D - 1"
    using jlt Dpos by simp
  have "cmod (basis j (emb i)) = cmod (emb i eta ^ j)"
    by (simp add: basis_def)
  also have "\<dots> = cmod (emb i eta) ^ j"
    by (simp add: norm_power)
  also have "\<dots> \<le> ?H ^ j"
    by (rule power_mono[OF emb_le]) simp
  also have "\<dots> \<le> ?H ^ (D - 1)"
    by (rule power_increasing[OF jle H_ge1])
  finally show ?thesis
    unfolding power_basis_entry_bound_def .
qed

lemma basis_cmod_le_power_basis_entry_bound_at_auto:
  assumes sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)"
    and jlt: "j < D"
  shows "cmod (basis j \<sigma>) \<le> power_basis_entry_bound"
proof -
  let ?H = "max 1 (gs_house eta)"
  have H_ge1: "1 \<le> ?H"
    by simp
  have emb_le: "cmod (\<sigma> eta) \<le> ?H"
    using cmod_sigma_eta_le_gs_house[OF sigma] by linarith
  have jle: "j \<le> D - 1"
    using jlt Dpos by simp
  have "cmod (basis j \<sigma>) = cmod (\<sigma> eta ^ j)"
    by (simp add: basis_def)
  also have "\<dots> = cmod (\<sigma> eta) ^ j"
    by (simp add: norm_power)
  also have "\<dots> \<le> ?H ^ j"
    by (rule power_mono[OF emb_le]) simp
  also have "\<dots> \<le> ?H ^ (D - 1)"
    by (rule power_increasing[OF jle H_ge1])
  finally show ?thesis
    unfolding power_basis_entry_bound_def .
qed

lemma gs_house_le_of_emb_bound:
  assumes finite: "finite_subfield_tower (\<rat> :: complex set) K"
    and normal: "normal_extension K (\<rat> :: complex set)"
    and separable: "separable_extension K (\<rat> :: complex set)"
    and ai: "algebraic_int x"
    and xK: "x \<in> K"
    and H_nonneg: "0 \<le> H"
    and bound: "\<And>i. i < D \<Longrightarrow> cmod (emb i x) \<le> H"
  shows "gs_house x \<le> H"
  by (rule gs_house_le_of_indexed_galois_image_bound[OF finite normal separable ebij xK ai H_nonneg bound])

end

end
