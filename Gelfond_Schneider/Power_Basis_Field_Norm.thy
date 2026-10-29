(*  Title:      Gelfond_Schneider/Power_Basis_Field_Norm.thy
    Author:     OpenAI Codex

Absolute field-norm style constructions for the finite normal Galois power-basis
setup. This packages the product of all Galois conjugates into a reusable
object for the remaining quantitative Gelfond-Schneider bounds.
*)

theory Power_Basis_Field_Norm
  imports
    Power_Basis_Inverse_Bounds
    "HOL-New_Algebra.Galois_Finite_Correspondence"
begin

context finite_normal_galois_power_basis
begin

definition gs_galois_norm :: "complex => complex"
  where "gs_galois_norm x \<equiv> (\<Prod>\<sigma>\<in>field_auto K \<rat>. \<sigma> x)"

definition gs_abs_galois_norm :: "complex => real"
  where "gs_abs_galois_norm x \<equiv> cmod (gs_galois_norm x)"

lemma field_auto_finite:
  "finite (field_auto K \<rat>)"
  by (rule finite_normal_separable_field_auto[OF finite normal separable])

lemma gs_galois_norm_in_K:
  assumes "x \<in> K"
  shows "gs_galois_norm x \<in> K"
  by (simp add: K_subfield Subfield.prod_closed assms field_auto_closed
      gs_galois_norm_def)

lemma gs_galois_norm_algebraic_int:
  assumes "x \<in> K"
  assumes ai: "algebraic_int x"
  shows "algebraic_int (gs_galois_norm x)"
  using K_subfield Rats_subset_K assms field_auto_preserves_algebraic_int gs_galois_norm_def
  by auto


lemma gs_galois_norm_nonzero:
  assumes "x \<in> K"
  assumes nz: "x \<noteq> 0"
  shows "gs_galois_norm x \<noteq> 0"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have img_nz: "\<sigma> x \<noteq> 0" if sigma: "\<sigma> \<in> field_auto K \<rat>" for \<sigma>
  proof
    assume sx0: "\<sigma> x = 0"
    have inj: "inj_on \<sigma> K"
      using sigma by (auto simp: field_auto_mem_iff bij_betw_def)
    have sig0: "\<sigma> 0 = 0"
      using sigma KS.zero_closed by (auto simp: field_auto_mem_iff)
    with nz sx0 assms inj show False
      by (auto simp: inj_on_def)
  qed
  show ?thesis
    unfolding gs_galois_norm_def
    by (intro prod_nonzeroI img_nz)
qed


lemma gs_abs_galois_norm_nonneg [simp]:
  "0 \<le> gs_abs_galois_norm x"
  unfolding gs_abs_galois_norm_def by simp

lemma gs_abs_galois_norm_pos:
  assumes "x \<in> K"
  assumes nz: "x \<noteq> 0"
  shows "0 < gs_abs_galois_norm x"
  unfolding gs_abs_galois_norm_def
  using gs_galois_norm_nonzero[OF \<open>x \<in> K\<close> nz] by simp

lemma gs_galois_norm_fixed:
  assumes tau: "\<tau> \<in> field_auto K \<rat>"
  assumes "x \<in> K"
  shows "\<tau> (gs_galois_norm x) = gs_galois_norm x"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  interpret TH: field_hom_on K \<tau>
    by (rule field_auto_imp_field_hom_on[OF K_subfield tau])
  let ?A = "field_auto K \<rat>"
  have imgK: "\<sigma> x \<in> K" if sigma: "\<sigma> \<in> ?A" for \<sigma>
    using sigma \<open>x \<in> K\<close> by (auto simp: field_auto_mem_iff PiE_iff)
  have hom_prod:
    "\<tau> (\<Prod>\<sigma>\<in>S. \<sigma> x) = (\<Prod>\<sigma>\<in>S. \<tau> (\<sigma> x))" if "finite S" "S \<subseteq> ?A" for S
    using that
  proof (induction S rule: finite_induct)
    case empty
    then show ?case
      using tau by (auto simp: field_auto_mem_iff)
  next
    case (insert \<sigma> S)
    have prodK: "(\<Prod>\<rho>\<in>S. \<rho> x) \<in> K"
      using insert imgK
      by (intro KS.prod_closed) (auto simp: field_auto_mem_iff PiE_iff)
    have "\<tau> (\<Prod>\<rho>\<in>insert \<sigma> S. \<rho> x) = \<tau> (\<sigma> x) * \<tau> (\<Prod>\<rho>\<in>S. \<rho> x)"
      using TH.hom_mult local.insert prodK imgK by auto
    also have "\<dots> = (\<Prod>\<rho>\<in>insert \<sigma> S. \<tau> (\<rho> x))"
      using insert by simp
    finally show ?case .
  qed
  define taui where "taui \<equiv> (\<lambda>y\<in>K. inv_into K \<tau> y)"
  have taui: "taui \<in> ?A"
    unfolding taui_def by (rule field_auto_inverse[OF K_subfield tau Rats_subset_K])
  have tau_bij: "bij_betw \<tau> K K"
    using tau by (simp add: field_auto_mem_iff)
  have tau_taui: "compose K \<tau> taui = identity K"
    unfolding taui_def using tau_bij by (simp add: bij_betw_imp_surj_on compose_id_inv_into)
  have taui_tau: "compose K taui \<tau> = identity K"
    unfolding taui_def using tau_bij by (simp add: compose_inv_into_id)
  have left_bij: "bij_betw (compose K \<tau>) ?A ?A"
  proof (rule bij_betwI)
    show "compose K \<tau> \<in> ?A \<rightarrow> ?A"
      by (auto simp: PiE_iff intro: field_auto_compose[OF K_subfield Rats_subset_K tau])
    show "compose K taui \<in> ?A \<rightarrow> ?A"
      by (auto simp: PiE_iff intro: field_auto_compose[OF K_subfield Rats_subset_K taui])
    fix \<sigma>
    assume sigma: "\<sigma> \<in> ?A"
    have sigma_fun: "\<sigma> \<in> K \<rightarrow> K" and sigma_ext: "\<sigma> \<in> K \<rightarrow>\<^sub>E K"
      using sigma by (auto simp: field_auto_mem_iff PiE_iff)
    have "compose K taui (compose K \<tau> \<sigma>) = compose K (identity K) \<sigma>"
      by (metis sigma_fun taui_tau compose_assoc)
    also have "\<dots> = \<sigma>"
      using sigma_ext by (auto simp: PiE_iff Id_compose)
    finally show "compose K taui (compose K \<tau> \<sigma>) = \<sigma>" .
  next
    fix \<sigma>
    assume sigma: "\<sigma> \<in> ?A"
    have sigma_fun: "\<sigma> \<in> K \<rightarrow> K" and sigma_ext: "\<sigma> \<in> K \<rightarrow>\<^sub>E K"
      using sigma by (auto simp: field_auto_mem_iff PiE_iff)
    have "compose K \<tau> (compose K taui \<sigma>) = compose K (identity K) \<sigma>"
      by (metis sigma_fun tau_taui compose_assoc)
    also have "\<dots> = \<sigma>"
      using sigma_ext by (auto simp: PiE_iff Id_compose)
    finally show "compose K \<tau> (compose K taui \<sigma>) = \<sigma>" .
  qed
  have "\<tau> (gs_galois_norm x) = \<tau> (\<Prod>\<sigma>\<in>?A. \<sigma> x)"
    unfolding gs_galois_norm_def by simp
  also have "\<dots> = (\<Prod>\<sigma>\<in>?A. \<tau> (\<sigma> x))"
    by (rule hom_prod[OF field_auto_finite subset_refl])
  also have "\<dots> = (\<Prod>\<sigma>\<in>?A. compose K \<tau> \<sigma> x)"
    by (intro prod.cong refl) (simp add: compose_eq \<open>x \<in> K\<close>)
  also have "\<dots> = (\<Prod>\<sigma>\<in>?A. \<sigma> x)"
    by (rule prod.reindex_bij_betw[OF left_bij])
  also have "\<dots> = gs_galois_norm x"
    unfolding gs_galois_norm_def by simp
  finally show ?thesis .
qed

lemma gs_galois_norm_in_rat:
  assumes "x \<in> K"
  shows "gs_galois_norm x \<in> \<rat>"
proof -
  have inter: "\<rat> \<in> inter_fields K \<rat>"
    using K_subfield Rats_subfield Rats_subset_K by (auto simp: inter_fields_iff)
  have "gs_galois_norm x \<in> fixed_field K (field_auto K \<rat>)"
    using assms gs_galois_norm_fixed[OF _ \<open>x \<in> K\<close>] 
    by (intro gs_galois_norm_in_K fixed_field_memI) auto
  then show ?thesis
    using finite_galois_fixed_field inter local.finite local.separable normal by blast
qed

lemma one_le_gs_abs_galois_norm_of_nonzero_algebraic_int:
  assumes "x \<in> K"
  assumes ai: "algebraic_int x"
  assumes nz: "x \<noteq> 0"
  shows "1 \<le> gs_abs_galois_norm x"
proof -
  have g_int: "gs_galois_norm x \<in> \<int>"
    by (simp add: assms gs_galois_norm_algebraic_int gs_galois_norm_in_rat
        rational_algebraic_int_is_int)
  obtain n :: int where n_def: "gs_galois_norm x = of_int n" and "n \<noteq> 0"
    using assms g_int gs_galois_norm_nonzero by (metis Ints_cases of_int_eq_0_iff)
  then show ?thesis
    by (auto simp: gs_abs_galois_norm_def)
qed

lemma inverse_gs_abs_galois_norm_le_one:
  assumes "x \<in> K" "algebraic_int x" "x \<noteq> 0"
  shows "inverse (gs_abs_galois_norm x) \<le> 1"
  by (simp add: assms inverse_le_1_iff one_le_gs_abs_galois_norm_of_nonzero_algebraic_int)

lemma emb_image_root_of_min_int_poly:
  assumes "i < D"
  assumes "x \<in> K"
  assumes ai: "algebraic_int x"
  shows "emb i x \<in> set (complex_roots_of_int_poly (min_int_poly x))"
proof -
  have sigma: "emb i \<in> field_auto K \<rat>"
    by (rule emb_in_field_auto[OF \<open>i < D\<close>])
  have p_over: "of_int_poly (min_int_poly x) \<in> poly_over \<rat>"
    by (auto simp: poly_over_def)
  have root_x: "poly (of_int_poly (min_int_poly x)) x = 0"
    using ai by (auto simp: min_int_poly_represents)
  have root_emb: "poly (of_int_poly (min_int_poly x)) (emb i x) = 0"
    by (rule field_auto_maps_root[OF K_subfield Rats_subfield Rats_subset_K sigma p_over \<open>x \<in> K\<close> root_x])
  with ai show ?thesis
    by (simp add: complex_roots_of_int_poly(1))
qed

lemma cmod_emb_image_le_gs_house:
  assumes "i < D"
  assumes "x \<in> K"
  assumes ai: "algebraic_int x"
  shows "cmod (emb i x) \<le> gs_house x"
  by (rule cmod_le_gs_house_of_root[OF emb_image_root_of_min_int_poly[OF \<open>i < D\<close> \<open>x \<in> K\<close> ai]])

lemma gs_abs_galois_norm_le_cmod_emb_mul_house_pow:
  assumes "i < D"
  assumes "x \<in> K"
  assumes ai: "algebraic_int x"
  shows "gs_abs_galois_norm x \<le> cmod (emb i x) * gs_house x ^ (D - 1)"
proof -
  have prod_reindex:
      "(\<Prod>\<sigma>\<in>field_auto K \<rat>. cmod (\<sigma> x)) = (\<Prod>j\<in>{0..<D}. cmod (emb j x))"
    by (metis (mono_tags, lifting)  prod.reindex_bij_betw[OF ebij] prod.cong)
  then have gs_le: "gs_abs_galois_norm x \<le> (\<Prod>j\<in>{0..<D}. cmod (emb j x))"
    unfolding gs_abs_galois_norm_def gs_galois_norm_def  by (metis norm_prod_le)
  have "(\<Prod>j\<in>{0..<D} - {i}. cmod (emb j x)) \<le> (\<Prod>j\<in>{0..<D} - {i}. gs_house x)"
    by (force intro!: prod_mono cmod_emb_image_le_gs_house[OF _ \<open>x \<in> K\<close> ai])
  then have tail_bnd: "(\<Prod>j\<in>{0..<D} - {i}. cmod (emb j x)) \<le> gs_house x ^ (D - 1)"
    using \<open>i < D\<close> by simp
  have "(\<Prod>j\<in>{0..<D}. cmod (emb j x)) = cmod (emb i x) * (\<Prod>j\<in>{0..<D} - {i}. cmod (emb j x))"
    using \<open>i < D\<close> by (simp add: prod.remove)
  then have "gs_abs_galois_norm x \<le> cmod (emb i x) * (\<Prod>j\<in>{0..<D} - {i}. cmod (emb j x))"
    using gs_le by simp
  also have "\<dots> \<le> cmod (emb i x) * gs_house x ^ (D - 1)"
    using tail_bnd by (intro mult_left_mono) simp_all
  finally show ?thesis .
qed

lemma gs_abs_galois_norm_le_cmod_emb_mul_bound_pow:
  assumes "i < D"
  assumes "x \<in> K"
  assumes ai: "algebraic_int x"
  assumes H_nonneg: "0 \<le> H"
  assumes bound: "\<And>j. j < D \<Longrightarrow> cmod (emb j x) \<le> H"
  shows "gs_abs_galois_norm x \<le> cmod (emb i x) * H ^ (D - 1)"
proof -
  have house_le: "gs_house x \<le> H"
    by (rule gs_house_le_of_emb_bound[OF finite normal separable ai \<open>x \<in> K\<close> H_nonneg bound])
  have norm_le: "gs_abs_galois_norm x \<le> cmod (emb i x) * gs_house x ^ (D - 1)"
    by (rule gs_abs_galois_norm_le_cmod_emb_mul_house_pow[OF \<open>i < D\<close> \<open>x \<in> K\<close> ai])
  also have "\<dots> \<le> cmod (emb i x) * H ^ (D - 1)"
    using house_le H_nonneg by (intro mult_left_mono power_mono) auto
  finally show ?thesis .
qed

lemma inverse_gs_abs_galois_norm_lt_powr:
  assumes "x \<in> K"
  assumes ai: "algebraic_int x"
  assumes nz: "x \<noteq> 0"
  assumes c5_gt1: "1 < c5"
  assumes rpos: "r > 0"
  shows "inverse (gs_abs_galois_norm x) < c5 powr of_nat r"
proof -
  have inv_le_one: "inverse (gs_abs_galois_norm x) \<le> 1"
    by (rule inverse_gs_abs_galois_norm_le_one[OF \<open>x \<in> K\<close> ai nz])
  have "1 < c5 powr of_nat r"
    by (simp add: c5_gt1 rpos)
  then show ?thesis
    using inv_le_one by linarith
qed

lemma gs_abs_galois_norm_le_from_analytic_house_bounds:
  fixes c8 c13 :: real
  assumes "i < D"
  assumes "x \<in> K"
  assumes ai: "algebraic_int x"
  assumes c8pos: "0 < c8"
  assumes c13pos: "0 < c13"
  assumes rpos: "0 < r"
  assumes house_bound:
    "gs_house x \<le> c8 powr of_nat r * of_nat r powr (of_nat r + 3 / 2)"
  assumes point_bound:
    "cmod (emb i x) \<le> c13 powr of_nat r *
      of_nat r powr (of_nat r * (3 - of_nat (2 * D + 2)) / 2 + 3 / 2)"
  shows "gs_abs_galois_norm x \<le>
    (c8 ^ (D - 1) * c13) powr of_nat r * of_nat r powr (- of_nat r / 2 + 3 * of_nat D / 2)"
proof -
  let ?R = "of_nat r :: real"
  let ?H = "c8 powr ?R * ?R powr (?R + 3 / 2)"
  let ?P = "c13 powr ?R * ?R powr (?R * (3 - of_nat (2 * D + 2)) / 2 + 3 / 2)"
  have Hpow: "gs_house x ^ (D - 1) \<le> ?H ^ (D - 1)"
    using house_bound by (intro power_mono) auto
  have norm_le: "gs_abs_galois_norm x \<le> cmod (emb i x) * gs_house x ^ (D - 1)"
    by (rule gs_abs_galois_norm_le_cmod_emb_mul_house_pow[OF \<open>i < D\<close> \<open>x \<in> K\<close> ai])
  also have "\<dots> \<le> ?P * ?H ^ (D - 1)"
    using point_bound Hpow by (intro mult_mono) auto
  also have "\<dots> = (c8 ^ (D - 1) * c13) powr ?R * ?R powr (- ?R / 2 + 3 * of_nat D / 2)"
    using c8pos c13pos rpos Dpos
    apply (simp add: powr_mult powr_powr of_nat_diff algebra_simps flip: powr_add powr_realpow)
    by argo
  finally show ?thesis .
qed

end

end
