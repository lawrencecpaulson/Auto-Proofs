(*  Title:      Gelfond_Schneider/Power_Basis.thy
    Author:     OpenAI Codex

Qualitative power-basis infrastructure for the standalone Gelfond-Schneider
route.  This packages the primitive normal field, its indexed Galois family,
and the resulting monogenic basis values `emb i eta ^ j` at the level needed
before any quantitative inverse-Vandermonde bounds are introduced.
*)

theory Power_Basis
  imports Galois_Root_Bounds
begin

locale finite_galois_power_basis =
  fixes K :: "complex set"
  fixes eta :: complex
  fixes D :: nat
  fixes emb :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  assumes K_def: "K = eval_img \<rat> eta"
    and D_def: "D = ext_degree \<rat> eta"
    and algQ: "algebraic_over \<rat> eta"
    and eta_int: "algebraic_int eta"
    and ebij: "bij_betw emb {0..<D} (field_auto K \<rat>)"
begin

definition basis :: "nat \<Rightarrow> (complex \<Rightarrow> complex) \<Rightarrow> complex"
  where "basis j e = e eta ^ j"

lemma emb_in_field_auto:
  assumes "i < D"
  shows "emb i \<in> field_auto K \<rat>"
  using ebij assms by (auto simp: bij_betw_def)

lemma indexed_images_inj:
  shows "inj_on (\<lambda>i. emb i eta) {0..<D}"
  by (rule indexed_galois_images_of_primitive_generator_inj[OF K_def algQ ebij])

lemma basis_indep_at_emb:
  assumes ilt: "i < D"
  assumes zero: "(\<Sum>j<D. of_int (c j) * basis j (emb i)) = 0" and "j<D"
  shows "c j = 0"
proof -
  have "(\<Sum>j<D. of_int (c j) * (emb i eta) ^ j) = 0"
    using zero by (simp add: basis_def)
  then show ?thesis
    using D_def K_def algQ assms emb_in_field_auto field_auto_power_basis_indep by blast
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
  by (simp add: K_def Rats_subfield Subfield.subfield_eval_img algQ)

lemma Rats_subset_K: "\<rat> \<subseteq> K"
  using K_def Rats_subfield Subfield.eval_img_base by blast

lemma eta_in_K: "eta \<in> K"
  by (simp add: K_def Rats_subfield Subfield.eval_img_self)

lemma identity_in_field_auto:
  "identity K \<in> field_auto K \<rat>"
  by (rule field_auto_identity[OF K_subfield Rats_subset_K])

lemma obtains_identity_embedding_index:
  obtains i0 where "i0 < D" and "emb i0 = identity K"
proof -
  have "identity K \<in> emb ` {0..<D}"
    using ebij identity_in_field_auto by (auto simp: bij_betw_def)
  then show thesis
    using that by auto
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
    and "j<D"
  shows "c j = 0"
  using basis_indep_at_emb[OF i0lt] assms by simp

lemma emb_eta_in_K:
  assumes ilt: "i < D"
  shows "emb i eta \<in> K"
  using assms emb_in_field_auto eta_in_K field_auto_closed by blast

lemma basis_in_K_at_emb:
  assumes "i < D"
  shows "basis j (emb i) \<in> K"
  by (simp add: K_subfield Subfield.power_closed assms basis_def emb_eta_in_K)

lemma sum_rat_power_in_K:
  assumes coeff_rat: "\<forall>i<D. c i \<in> \<rat>"
  shows "(\<Sum>i<D. c i * eta ^ i) \<in> K"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  show ?thesis
  proof (rule KS.sum_closed)
    show "c i * eta ^ i \<in> K" if "i \<in> {..<D}" for i
    proof -
      have"c i \<in> K"
        using that coeff_rat Rats_subset_K by blast
      then show ?thesis
        using eta_in_K by blast
    qed
  qed
qed

lemma sum_int_basis_at_emb_in_K:
  assumes "i < D"
  shows "(\<Sum>j<D. of_int (c j) * basis j (emb i)) \<in> K"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  show ?thesis
    using assms basis_in_K_at_emb by fastforce
qed

lemma sum_int_power_algebraic_int:
  shows "algebraic_int (\<Sum>i<D. of_int (c i) * eta ^ i)"
  using eta_int by blast

lemma emb_sum_int_power:
  assumes "i < D"
  shows "emb i (\<Sum>j<D. of_int (c j) * eta ^ j) = (\<Sum>j<D. of_int (c j) * basis j (emb i))"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have sigma: "emb i \<in> field_auto K \<rat>"
    by (rule emb_in_field_auto[OF \<open>i < D\<close>])
  have hom: "field_hom_on K (emb i)"
    by (rule field_auto_imp_field_hom_on[OF K_subfield sigma])
  have coeff_fix: "emb i (of_int (c j)) = of_int (c j)" for j
    using sigma by (auto simp: field_auto_mem_iff)
  have emb_term: "emb i (of_int (c j) * eta ^ j) = of_int (c j) * basis j (emb i)" for j
  proof -
    have "emb i (of_int (c j) * eta ^ j) = emb i (of_int (c j)) * emb i (eta ^ j)"
      using eta_in_K field_hom_on.hom_mult hom by blast
    also have "... = of_int (c j) * basis j (emb i)"
      by (simp add: basis_def coeff_fix field_hom_on.hom_power[OF hom eta_in_K])
    finally show ?thesis .
  qed
  have "emb i (\<Sum>j<D. of_int (c j) * eta ^ j) = (\<Sum>j<D. emb i (of_int (c j) * eta ^ j))"
    by (rule field_hom_on.hom_sum[OF hom]) (use eta_in_K in auto)
  then show ?thesis
    using emb_term by force
qed

lemma sum_int_basis_at_emb_as_integral_element:
  assumes ilt: "i < D"
  obtains x where "x \<in> K" "algebraic_int x" "emb i x = (\<Sum>j<D. of_int (c j) * basis j (emb i))"
proof -
  let ?x = "(\<Sum>j<D. of_int (c j) * eta ^ j)"
  have xK: "?x \<in> K"
    by (rule sum_rat_power_in_K) auto
  then show thesis
    using emb_sum_int_power[OF ilt] sum_int_power_algebraic_int that xK by blast
qed

lemma represented_coordinate_as_integral_element:
  assumes ilt: "i < D"
  assumes repr:
    "\<forall>t<q * q.
      Matrix.vec_index v t =
        (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i))"
  assumes tlt: "t < q * q"
  obtains y where "y \<in> K" "algebraic_int y" "emb i y = Matrix.vec_index v t"
proof -
  have "Matrix.vec_index v t =
      (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i))"
    using repr tlt by blast
  with sum_int_basis_at_emb_as_integral_element[OF ilt,
      where c = "\<lambda>j. Matrix.vec_index x (sg_pair_idx D t j)"] that
  show thesis by auto
qed

lemma sum_int_basis_at_emb_as_integral_element_with_house_bound:
  assumes finite: "finite_subfield_tower \<rat> K"
    and normal: "normal_extension K \<rat>"
    and separable: "separable_extension K \<rat>"
    and ilt: "i < D"
    and H_nonneg: "0 \<le> H"
    and emb_bound: "\<And>j. j < D \<Longrightarrow> cmod (\<Sum>k<D. of_int (c k) * basis k (emb j)) \<le> H"
  obtains x where "x \<in> K" "algebraic_int x" "emb i x = (\<Sum>k<D. of_int (c k) * basis k (emb i))"
    "gs_house x \<le> H"
proof -
  let ?x = "(\<Sum>k<D. of_int (c k) * eta ^ k)"
  have xK: "?x \<in> K"
    by (rule sum_rat_power_in_K) auto
  have xint: "algebraic_int ?x"
    by (rule sum_int_power_algebraic_int)
  have "gs_house ?x \<le> H"
    using gs_house_le_of_indexed_galois_image_bound[OF finite normal separable ebij xK xint H_nonneg]
    using emb_bound emb_sum_int_power by presburger
  with emb_sum_int_power[OF ilt] show thesis
    using sum_int_power_algebraic_int that xK by blast
qed

lemma represented_coordinate_as_integral_element_with_house_bound:
  assumes finite: "finite_subfield_tower \<rat> K"
    and normal: "normal_extension K \<rat>"
    and separable: "separable_extension K \<rat>"
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
  obtains y where "y \<in> K" "algebraic_int y" "emb i y = Matrix.vec_index v t" "gs_house y \<le> H"
proof -
  let ?c = "\<lambda>j. Matrix.vec_index x (sg_pair_idx D t j)"
  have emb_bound0:
    "\<And>j. j < D \<Longrightarrow> cmod (\<Sum>k<D. of_int (?c k) * basis k (emb j)) \<le> H"
    using emb_bound by simp
  show thesis
    using that repr tlt sum_int_basis_at_emb_as_integral_element_with_house_bound[
      OF finite normal separable ilt H_nonneg emb_bound0] by auto
qed

lemma Dpos: "D > 0"
  by (metis gr_zeroI not_less_zero obtains_identity_embedding_index)

lemma emb_eta_root_of_min_int_poly:
  assumes ilt: "i < D"
  shows "emb i eta \<in> set (complex_roots_of_int_poly (min_int_poly eta))"
proof -
  have sigma: "emb i \<in> field_auto K \<rat>"
    by (rule emb_in_field_auto[OF ilt])
  have p_over: "of_int_poly (min_int_poly eta) \<in> poly_over \<rat>"
    by (auto simp: poly_over_def)
  have root_eta: "poly (of_int_poly (min_int_poly eta)) eta = 0"
    using eta_int by (auto simp: min_int_poly_represents)
  have "poly (of_int_poly (min_int_poly eta)) (emb i eta) = 0"
    by (rule field_auto_maps_root[OF K_subfield Rats_subfield Rats_subset_K sigma p_over eta_in_K root_eta])
  then show ?thesis
    using complex_roots_of_int_poly(1) by simp
qed

lemma cmod_emb_eta_le_gs_house:
  assumes ilt: "i < D"
  shows "cmod (emb i eta) \<le> gs_house eta"
  using assms cmod_le_gs_house_of_root emb_eta_root_of_min_int_poly by blast

lemma basis_indep_at_auto:
  assumes sigma: "\<sigma> \<in> field_auto K \<rat>"
    and zero: "(\<Sum>j<D. of_int (c j) * basis j \<sigma>) = 0"
    and "j<D"
  shows "c j = 0"
proof -
  have zero': "(\<Sum>j<ext_degree \<rat> eta. of_int (c j) * (\<sigma> eta) ^ j) = 0"
    using zero by (simp add: basis_def D_def)
  then show ?thesis
    using D_def K_def algQ assms field_auto_power_basis_indep by blast
qed

lemma sigma_eta_root_of_min_int_poly:
  assumes sigma: "\<sigma> \<in> field_auto K \<rat>"
  shows "\<sigma> eta \<in> set (complex_roots_of_int_poly (min_int_poly eta))"
proof -
  have p_over: "of_int_poly (min_int_poly eta) \<in> poly_over \<rat>"
    by (auto simp: poly_over_def)
  have root_eta: "poly (of_int_poly (min_int_poly eta)) eta = 0"
    using eta_int by (auto simp: min_int_poly_represents)
  have root_sigma: "poly (of_int_poly (min_int_poly eta)) (\<sigma> eta) = 0"
    by (rule field_auto_maps_root[OF K_subfield Rats_subfield Rats_subset_K sigma p_over eta_in_K root_eta])
  then show ?thesis
    using root_sigma complex_roots_of_int_poly(1) by simp
qed

lemma cmod_sigma_eta_le_gs_house:
  assumes sigma: "\<sigma> \<in> field_auto K \<rat>"
  shows "cmod (\<sigma> eta) \<le> gs_house eta"
  using cmod_le_gs_house_of_root sigma sigma_eta_root_of_min_int_poly by blast

definition power_basis_entry_bound :: real
  where "power_basis_entry_bound = max 1 (gs_house eta) ^ (D - 1)"

lemma power_basis_entry_bound_nonneg [simp]:
  shows "0 \<le> power_basis_entry_bound"
  unfolding power_basis_entry_bound_def by simp

lemma basis_cmod_le_power_basis_entry_bound:
  assumes "i < D" and "j < D"
  shows "cmod (basis j (emb i)) \<le> power_basis_entry_bound"
proof -
  let ?H = "max 1 (gs_house eta)"
  have H_nonneg: "0 \<le> ?H"
    by simp
  have H_ge1: "1 \<le> ?H"
    by simp
  have emb_le: "cmod (emb i eta) \<le> ?H"
    using cmod_emb_eta_le_gs_house[OF \<open>i < D\<close>] by linarith
  have jle: "j \<le> D - 1"
    using \<open>j < D\<close> Dpos by simp
  have "cmod (basis j (emb i)) = cmod (emb i eta) ^ j"
    by (simp add: basis_def norm_power)
  also have "\<dots> \<le> ?H ^ (D - 1)"
    using power_mono[OF emb_le] power_increasing[OF jle H_ge1]
    by (meson ge_trans norm_ge_zero)
  finally show ?thesis
    unfolding power_basis_entry_bound_def .
qed

lemma basis_cmod_le_power_basis_entry_bound_at_auto:
  assumes sigma: "\<sigma> \<in> field_auto K \<rat>"
    and "j < D"
  shows "cmod (basis j \<sigma>) \<le> power_basis_entry_bound"
proof -
  let ?H = "max 1 (gs_house eta)"
  have H_ge1: "1 \<le> ?H"
    by simp
  have emb_le: "cmod (\<sigma> eta) \<le> ?H"
    using cmod_sigma_eta_le_gs_house[OF sigma] by linarith
  have jle: "j \<le> D - 1"
    using \<open>j < D\<close> Dpos by simp
  have "cmod (basis j \<sigma>) = cmod (\<sigma> eta) ^ j"
    by (simp add: basis_def norm_power)
  also have "\<dots> \<le> ?H ^ (D - 1)"
    using power_mono[OF emb_le] power_increasing[OF jle H_ge1]
    by (meson ge_trans norm_ge_zero)
  finally show ?thesis
    unfolding power_basis_entry_bound_def .
qed

lemma gs_house_le_of_emb_bound:
  assumes "finite_subfield_tower \<rat> K"
    and "normal_extension K \<rat>"
    and "separable_extension K \<rat>"
    and "algebraic_int x"
    and "x \<in> K"
    and "0 \<le> H"
    and "\<And>i. i < D \<Longrightarrow> cmod (emb i x) \<le> H"
  shows "gs_house x \<le> H"
  using assms ebij gs_house_le_of_indexed_galois_image_bound by blast

end

end
