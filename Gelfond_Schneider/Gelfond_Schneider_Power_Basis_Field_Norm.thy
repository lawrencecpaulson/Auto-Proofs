(*  Title:      Gelfond_Schneider/Gelfond_Schneider_Power_Basis_Field_Norm.thy
    Author:     OpenAI Codex

Absolute field-norm style constructions for the finite normal Galois power-basis
setup. This packages the product of all Galois conjugates into a reusable
object for the remaining quantitative Gelfond-Schneider bounds.
*)

theory Gelfond_Schneider_Power_Basis_Field_Norm
  imports
    Gelfond_Schneider_Power_Basis_Inverse_Bounds
    "New_Algebra.Galois_Finite_Correspondence"
begin

context finite_normal_galois_power_basis
begin

definition gs_galois_norm :: "complex => complex"
  where "gs_galois_norm x = (\<Prod>\<sigma>\<in>field_auto K (\<rat> :: complex set). \<sigma> x)"

definition gs_abs_galois_norm :: "complex => real"
  where "gs_abs_galois_norm x = cmod (gs_galois_norm x)"

lemma field_auto_finite:
  "finite (field_auto K (\<rat> :: complex set))"
  by (rule finite_normal_separable_field_auto[OF finite normal separable])

lemma gs_galois_norm_in_K:
  assumes xK: "x \<in> K"
  shows "gs_galois_norm x \<in> K"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have imgK: "\<sigma> x \<in> K" if sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)" for \<sigma>
    using sigma xK by (auto simp: field_auto_mem_iff PiE_iff)
  show ?thesis
    unfolding gs_galois_norm_def by (rule KS.prod_closed) (use imgK in auto)
qed

lemma gs_galois_norm_algebraic_int:
  assumes xK: "x \<in> K"
  assumes ai: "algebraic_int x"
  shows "algebraic_int (gs_galois_norm x)"
proof -
  have QK: "(\<rat> :: complex set) \<subseteq> K"
    by (rule Rats_subset_K)
  have img_ai: "algebraic_int (\<sigma> x)" if sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)" for \<sigma>
    by (rule field_auto_preserves_algebraic_int[OF K_subfield QK sigma xK ai])
  show ?thesis
    unfolding gs_galois_norm_def by (intro algebraic_int_prod img_ai)
qed

lemma gs_galois_norm_nonzero:
  assumes xK: "x \<in> K"
  assumes nz: "x \<noteq> 0"
  shows "gs_galois_norm x \<noteq> 0"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have img_nz: "\<sigma> x \<noteq> 0" if sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)" for \<sigma>
  proof
    assume sx0: "\<sigma> x = 0"
    have inj: "inj_on \<sigma> K"
      using sigma by (auto simp: field_auto_mem_iff bij_betw_def)
    have sig0: "\<sigma> 0 = 0"
      using sigma KS.zero_closed by (auto simp: field_auto_mem_iff)
    have "x = 0"
      by (rule Fun.inj_onD[OF inj]) (use sx0 sig0 xK KS.zero_closed in auto)
    with nz show False
      by contradiction
  qed
  show ?thesis
    unfolding gs_galois_norm_def
    by (intro prod_nonzeroI img_nz)
qed


lemma gs_abs_galois_norm_nonneg [simp]:
  "0 \<le> gs_abs_galois_norm x"
  unfolding gs_abs_galois_norm_def by simp

lemma gs_abs_galois_norm_pos:
  assumes xK: "x \<in> K"
  assumes nz: "x \<noteq> 0"
  shows "0 < gs_abs_galois_norm x"
  unfolding gs_abs_galois_norm_def
  using gs_galois_norm_nonzero[OF xK nz] by simp

lemma gs_galois_norm_fixed:
  assumes tau: "\<tau> \<in> field_auto K (\<rat> :: complex set)"
  assumes xK: "x \<in> K"
  shows "\<tau> (gs_galois_norm x) = gs_galois_norm x"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  interpret TH: field_hom_on K \<tau>
    by (rule field_auto_imp_field_hom_on[OF K_subfield tau])
  let ?A = "field_auto K (\<rat> :: complex set)"
  have imgK: "\<sigma> x \<in> K" if sigma: "\<sigma> \<in> ?A" for \<sigma>
    using sigma xK by (auto simp: field_auto_mem_iff PiE_iff)
  have hom_prod:
    "\<tau> (\<Prod>\<sigma>\<in>S. \<sigma> x) = (\<Prod>\<sigma>\<in>S. \<tau> (\<sigma> x))" if finS: "finite S" and Ssub: "S \<subseteq> ?A" for S
    using finS Ssub
  proof (induction S rule: finite_induct)
    case empty
    then show ?case
      using tau by (auto simp: field_auto_mem_iff)
  next
    case (insert \<sigma> S)
    have sigA: "\<sigma> \<in> ?A"
      using insert.prems by simp
    have sigK: "\<sigma> x \<in> K"
      by (rule imgK[OF sigA])
    have prodK: "(\<Prod>\<rho>\<in>S. \<rho> x) \<in> K"
    proof (rule KS.prod_closed)
      fix \<rho>
      assume rhoS: "\<rho> \<in> S"
      with insert.prems show "\<rho> x \<in> K"
        using xK by (auto simp: field_auto_mem_iff PiE_iff)
    qed
    have IH: "\<tau> (\<Prod>\<rho>\<in>S. \<rho> x) = (\<Prod>\<rho>\<in>S. \<tau> (\<rho> x))"
      by (rule insert.IH) (use insert.prems in auto)
    have "\<tau> (\<Prod>\<rho>\<in>insert \<sigma> S. \<rho> x) = \<tau> (\<sigma> x * (\<Prod>\<rho>\<in>S. \<rho> x))"
      using insert.hyps by simp
    also have "... = \<tau> (\<sigma> x) * \<tau> (\<Prod>\<rho>\<in>S. \<rho> x)"
      by (rule TH.hom_mult[OF sigK prodK])
    also have "... = \<tau> (\<sigma> x) * (\<Prod>\<rho>\<in>S. \<tau> (\<rho> x))"
      by (simp add: IH)
    also have "... = (\<Prod>\<rho>\<in>insert \<sigma> S. \<tau> (\<rho> x))"
      using insert.hyps by simp
    finally show ?case .
  qed
  define taui where "taui = (\<lambda>y\<in>K. inv_into K \<tau> y)"
  have taui: "taui \<in> ?A"
    unfolding taui_def by (rule field_auto_inverse[OF K_subfield tau Rats_subset_K])
  have tau_bij: "bij_betw \<tau> K K"
    using tau by (simp add: field_auto_mem_iff)
  have tau_taui: "compose K \<tau> taui = identity K"
    unfolding taui_def using tau_bij by (simp add: bij_betw_imp_surj_on compose_id_inv_into)
  have taui_tau: "compose K taui \<tau> = identity K"
    unfolding taui_def using tau_bij by (simp add: compose_inv_into_id)
  have left_bij: "bij_betw (compose K \<tau>) ?A ?A"
  proof (rule bij_betwI[where g = "compose K taui"])
    show "compose K \<tau> \<in> ?A \<rightarrow> ?A"
      by (auto simp: PiE_iff intro: field_auto_compose[OF K_subfield Rats_subset_K tau])
    show "compose K taui \<in> ?A \<rightarrow> ?A"
      by (auto simp: PiE_iff intro: field_auto_compose[OF K_subfield Rats_subset_K taui])
    fix \<sigma>
    assume sigma: "\<sigma> \<in> ?A"
    have sigma_fun: "\<sigma> \<in> K \<rightarrow> K"
      and sigma_ext: "\<sigma> \<in> K \<rightarrow>\<^sub>E K"
      using sigma by (auto simp: field_auto_mem_iff PiE_iff)
    have "compose K taui (compose K \<tau> \<sigma>) = compose K (compose K taui \<tau>) \<sigma>"
      by (rule compose_assoc[OF sigma_fun])
    also have "... = compose K (identity K) \<sigma>"
      by (simp add: taui_tau)
    also have "... = \<sigma>"
    proof (rule Id_compose)
      show "\<sigma> \<in> K \<rightarrow> K" by (rule sigma_fun)
      show "\<sigma> \<in> extensional K" using sigma_ext by (simp add: PiE_iff)
    qed
    finally show "compose K taui (compose K \<tau> \<sigma>) = \<sigma>" .
  next
    fix \<sigma>
    assume sigma: "\<sigma> \<in> ?A"
    have sigma_fun: "\<sigma> \<in> K \<rightarrow> K"
      and sigma_ext: "\<sigma> \<in> K \<rightarrow>\<^sub>E K"
      using sigma by (auto simp: field_auto_mem_iff PiE_iff)
    have "compose K \<tau> (compose K taui \<sigma>) = compose K (compose K \<tau> taui) \<sigma>"
      by (rule compose_assoc[OF sigma_fun])
    also have "... = compose K (identity K) \<sigma>"
      by (simp add: tau_taui)
    also have "... = \<sigma>"
    proof (rule Id_compose)
      show "\<sigma> \<in> K \<rightarrow> K" by (rule sigma_fun)
      show "\<sigma> \<in> extensional K" using sigma_ext by (simp add: PiE_iff)
    qed
    finally show "compose K \<tau> (compose K taui \<sigma>) = \<sigma>" .
  qed
  have "\<tau> (gs_galois_norm x) = \<tau> (\<Prod>\<sigma>\<in>?A. \<sigma> x)"
    unfolding gs_galois_norm_def by simp
  also have "... = (\<Prod>\<sigma>\<in>?A. \<tau> (\<sigma> x))"
    by (rule hom_prod[OF field_auto_finite subset_refl])
  also have "... = (\<Prod>\<sigma>\<in>?A. compose K \<tau> \<sigma> x)"
    by (intro prod.cong refl) (simp add: compose_eq xK)
  also have "... = (\<Prod>\<sigma>\<in>?A. \<sigma> x)"
    by (rule prod.reindex_bij_betw[OF left_bij])
  also have "... = gs_galois_norm x"
    unfolding gs_galois_norm_def by simp
  finally show ?thesis .
qed

lemma gs_galois_norm_in_rat:
  assumes xK: "x \<in> K"
  shows "gs_galois_norm x \<in> (\<rat> :: complex set)"
proof -
  have inter: "(\<rat> :: complex set) \<in> inter_fields K (\<rat> :: complex set)"
    using K_subfield Rats_subfield Rats_subset_K by (auto simp: inter_fields_iff)
  have fix_mem: "gs_galois_norm x \<in> fixed_field K (field_auto K (\<rat> :: complex set))"
  proof (rule fixed_field_memI)
    show "gs_galois_norm x \<in> K"
      by (rule gs_galois_norm_in_K[OF xK])
    fix \<tau>
    assume "\<tau> \<in> field_auto K (\<rat> :: complex set)"
    then show "\<tau> (gs_galois_norm x) = gs_galois_norm x"
      by (rule gs_galois_norm_fixed[OF _ xK])
  qed
  have "fixed_field K (field_auto K (\<rat> :: complex set)) = (\<rat> :: complex set)"
    by (rule finite_galois_fixed_field[OF finite normal separable inter])
  with fix_mem show ?thesis
    by simp
qed

lemma one_le_gs_abs_galois_norm_of_nonzero_algebraic_int:
  assumes xK: "x \<in> K"
  assumes ai: "algebraic_int x"
  assumes nz: "x \<noteq> 0"
  shows "1 \<le> gs_abs_galois_norm x"
proof -
  have g_ai: "algebraic_int (gs_galois_norm x)"
    by (rule gs_galois_norm_algebraic_int[OF xK ai])
  have g_rat: "gs_galois_norm x \<in> (\<rat> :: complex set)"
    by (rule gs_galois_norm_in_rat[OF xK])
  have g_int: "gs_galois_norm x \<in> (\<int> :: complex set)"
    by (rule rational_algebraic_int_is_int[OF g_ai g_rat])
  obtain n :: int where n_def: "gs_galois_norm x = of_int n"
    using g_int by (elim Ints_cases) auto
  have n_nz: "n \<noteq> 0"
    using gs_galois_norm_nonzero[OF xK nz] by (auto simp: n_def)
  have "1 \<le> cmod (gs_galois_norm x)"
    unfolding n_def using n_nz by auto
  then show ?thesis
    unfolding gs_abs_galois_norm_def .
qed

lemma inverse_gs_abs_galois_norm_le_one:
  assumes xK: "x \<in> K"
  assumes ai: "algebraic_int x"
  assumes nz: "x \<noteq> 0"
  shows "inverse (gs_abs_galois_norm x) \<le> 1"
proof -
  have ge1: "1 \<le> gs_abs_galois_norm x"
    by (rule one_le_gs_abs_galois_norm_of_nonzero_algebraic_int[OF xK ai nz])
  have pos: "0 < gs_abs_galois_norm x"
    by (rule gs_abs_galois_norm_pos[OF xK nz])
  show ?thesis
    using ge1 pos by (simp add: field_simps)
qed

lemma emb_image_root_of_min_int_poly:
  assumes ilt: "i < D"
  assumes xK: "x \<in> K"
  assumes ai: "algebraic_int x"
  shows "emb i x \<in> set (complex_roots_of_int_poly (min_int_poly x))"
proof -
  have sigma: "emb i \<in> field_auto K (\<rat> :: complex set)"
    by (rule emb_in_field_auto[OF ilt])
  have p_over: "of_int_poly (min_int_poly x) \<in> poly_over (\<rat> :: complex set)"
    by (auto simp: poly_over_def)
  have root_x: "poly (of_int_poly (min_int_poly x)) x = 0"
    using ai by (auto simp: min_int_poly_represents)
  have root_emb: "poly (of_int_poly (min_int_poly x)) (emb i x) = 0"
    by (rule field_auto_maps_root[OF K_subfield Rats_subfield Rats_subset_K sigma p_over xK root_x])
  have p0: "min_int_poly x \<noteq> 0"
    using ai by auto
  show ?thesis
    using root_emb complex_roots_of_int_poly(1)[OF p0] by simp
qed

lemma cmod_emb_image_le_gs_house:
  assumes ilt: "i < D"
  assumes xK: "x \<in> K"
  assumes ai: "algebraic_int x"
  shows "cmod (emb i x) \<le> gs_house x"
  by (rule cmod_le_gs_house_of_root[OF emb_image_root_of_min_int_poly[OF ilt xK ai]])

lemma gs_abs_galois_norm_le_cmod_emb_mul_house_pow:
  assumes ilt: "i < D"
  assumes xK: "x \<in> K"
  assumes ai: "algebraic_int x"
  shows "gs_abs_galois_norm x \<le> cmod (emb i x) * gs_house x ^ (D - 1)"
proof -
  have prod_reindex:
      "(\<Prod>\<sigma>\<in>field_auto K (\<rat> :: complex set). cmod (\<sigma> x)) =
        (\<Prod>j\<in>{0..<D}. cmod (emb j x))"
  proof -
    have "(\<Prod>j\<in>{0..<D}. cmod (emb j x)) =
        (\<Prod>\<sigma>\<in>field_auto K (\<rat> :: complex set). cmod (\<sigma> x))"
      by (rule prod.reindex_bij_betw[OF ebij])
    then show ?thesis
      by simp
  qed
  have gs_le: "gs_abs_galois_norm x \<le> (\<Prod>j\<in>{0..<D}. cmod (emb j x))"
  proof -
    have "gs_abs_galois_norm x = cmod (\<Prod>\<sigma>\<in>field_auto K (\<rat> :: complex set). \<sigma> x)"
      unfolding gs_abs_galois_norm_def gs_galois_norm_def by simp
    also have "... \<le> (\<Prod>\<sigma>\<in>field_auto K (\<rat> :: complex set). cmod (\<sigma> x))"
      by (rule norm_prod_le)
    also have "... = (\<Prod>j\<in>{0..<D}. cmod (emb j x))"
      using prod_reindex by simp
    finally show ?thesis .
  qed
  have prod_le:
      "(\<Prod>j\<in>{0..<D} - {i}. cmod (emb j x)) \<le> (\<Prod>j\<in>{0..<D} - {i}. gs_house x)"
  proof (rule prod_mono)
    fix j
    assume j: "j \<in> {0..<D} - {i}"
    show "0 \<le> cmod (emb j x) \<and> cmod (emb j x) \<le> gs_house x"
      using j by (auto intro: cmod_emb_image_le_gs_house[OF _ xK ai])
  qed
  have tail_bnd: "(\<Prod>j\<in>{0..<D} - {i}. cmod (emb j x)) \<le> gs_house x ^ (D - 1)"
  proof -
    have "(\<Prod>j\<in>{0..<D} - {i}. cmod (emb j x)) \<le> (\<Prod>j\<in>{0..<D} - {i}. gs_house x)"
      by (rule prod_le)
    also have "... = gs_house x ^ card ({0..<D} - {i})"
      by simp
    also have "... = gs_house x ^ (D - 1)"
      using ilt by simp
    finally show ?thesis .
  qed
  have split_prod:
      "(\<Prod>j\<in>{0..<D}. cmod (emb j x)) =
        cmod (emb i x) * (\<Prod>j\<in>{0..<D} - {i}. cmod (emb j x))"
    using ilt by (simp add: prod.remove)
  have ci_nonneg: "0 \<le> cmod (emb i x)"
    by simp
  have "gs_abs_galois_norm x \<le> cmod (emb i x) * (\<Prod>j\<in>{0..<D} - {i}. cmod (emb j x))"
    using gs_le split_prod by simp
  also have "... \<le> cmod (emb i x) * gs_house x ^ (D - 1)"
    using ci_nonneg tail_bnd by (intro mult_left_mono) simp
  finally show ?thesis .
qed

lemma gs_abs_galois_norm_le_cmod_emb_mul_bound_pow:
  assumes ilt: "i < D"
  assumes xK: "x \<in> K"
  assumes ai: "algebraic_int x"
  assumes H_nonneg: "0 \<le> H"
  assumes bound: "\<And>j. j < D \<Longrightarrow> cmod (emb j x) \<le> H"
  shows "gs_abs_galois_norm x \<le> cmod (emb i x) * H ^ (D - 1)"
proof -
  have house_le: "gs_house x \<le> H"
    by (rule gs_house_le_of_emb_bound[OF finite normal separable ai xK H_nonneg bound])
  have norm_le: "gs_abs_galois_norm x \<le> cmod (emb i x) * gs_house x ^ (D - 1)"
    by (rule gs_abs_galois_norm_le_cmod_emb_mul_house_pow[OF ilt xK ai])
  also have "... \<le> cmod (emb i x) * H ^ (D - 1)"
    using house_le H_nonneg by (intro mult_left_mono power_mono) auto
  finally show ?thesis .
qed

lemma inverse_gs_abs_galois_norm_lt_powr:
  assumes xK: "x \<in> K"
  assumes ai: "algebraic_int x"
  assumes nz: "x \<noteq> 0"
  assumes c5_gt1: "1 < c5"
  assumes rpos: "r > 0"
  shows "inverse (gs_abs_galois_norm x) < c5 powr of_nat r"
proof -
  have inv_le_one: "inverse (gs_abs_galois_norm x) \<le> 1"
    by (rule inverse_gs_abs_galois_norm_le_one[OF xK ai nz])
  have c5_powr_gt1: "1 < c5 powr of_nat r"
  proof -
    have "c5 powr 0 < c5 powr of_nat r"
      using c5_gt1 rpos by (intro powr_less_mono) auto
    then show ?thesis
      using c5_gt1 by simp
  qed
  show ?thesis
    using inv_le_one c5_powr_gt1 by linarith
qed

lemma gs_abs_galois_norm_le_from_analytic_house_bounds:
  fixes c8 c13 :: real
  assumes ilt: "i < D"
  assumes xK: "x \<in> K"
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
    (c8 ^ (D - 1) * c13) powr of_nat r *
      of_nat r powr (- of_nat r / 2 + 3 * of_nat D / 2)"
proof -
  let ?R = "of_nat r :: real"
  let ?H = "c8 powr ?R * ?R powr (?R + 3 / 2)"
  let ?P = "c13 powr ?R * ?R powr (?R * (3 - of_nat (2 * D + 2)) / 2 + 3 / 2)"
  have Hpow: "gs_house x ^ (D - 1) \<le> ?H ^ (D - 1)"
    using house_bound by (intro power_mono) auto
  have norm_le: "gs_abs_galois_norm x \<le> cmod (emb i x) * gs_house x ^ (D - 1)"
    by (rule gs_abs_galois_norm_le_cmod_emb_mul_house_pow[OF ilt xK ai])
  also have "... \<le> ?P * ?H ^ (D - 1)"
    using point_bound Hpow by (intro mult_mono) auto
  also have "... = (c8 ^ (D - 1) * c13) powr ?R *
      ?R powr (- ?R / 2 + 3 * of_nat D / 2)"
    using c8pos c13pos rpos Dpos
    apply (simp add: power_mult_distrib powr_mult powr_power powr_powr
        powr_realpow[symmetric] of_nat_diff algebra_simps powr_add[symmetric])
    apply (rule arg_cong[where f="(powr) (of_nat r :: real)"])
    by (simp add: field_simps algebra_simps)
  finally show ?thesis .
qed

end

end
