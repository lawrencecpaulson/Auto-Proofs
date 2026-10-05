(*  Title:      Baker/Gelfond_Schneider_Power_Basis_Inverse_Bounds.thy
    Author:     OpenAI Codex

Crude inverse-Vandermonde bounds for the power-basis route.  The aim here is
not sharp constants, only a clean reduction of the remaining `inv_bound` input
to explicit coefficient and denominator estimates.
*)

theory Gelfond_Schneider_Power_Basis_Inverse_Bounds
  imports
    Gelfond_Schneider_Power_Basis_Recovery
    Gelfond_Schneider_Power_Basis
begin

locale finite_normal_galois_power_basis = finite_galois_power_basis K eta D emb
  for K :: "complex set"
  and eta :: complex
  and D :: nat
  and emb :: "nat \<Rightarrow> complex \<Rightarrow> complex" +
  assumes finite: "finite_subfield_tower (\<rat> :: complex set) K"
    and normal: "normal_extension K (\<rat> :: complex set)"
    and separable: "separable_extension K (\<rat> :: complex set)"
begin

lemma emb_mem_K:
  assumes ilt: "i < D"
  shows "emb i eta \<in> K"
  using emb_in_field_auto[OF ilt] eta_in_K
  by (auto simp: field_auto_mem_iff PiE_iff)

lemma lagrange_denom_in_K:
  assumes ilt: "i < D"
  shows "lagrange_denom i \<in> K"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have facK: "emb i eta - emb m eta \<in> K" if m: "m \<in> {0..<D} - {i}" for m
  proof -
    have eiK: "emb i eta \<in> K"
      by (rule emb_mem_K[OF ilt])
    have emK: "emb m eta \<in> K"
      using m by (auto intro: emb_mem_K)
    have neg_emK: "- (emb m eta) \<in> K"
      by (rule KS.uminus_closed[OF emK])
    have sumK: "emb i eta + - (emb m eta) \<in> K"
      by (rule KS.add_closed[OF eiK neg_emK])
    show ?thesis
      using sumK by simp
  qed
  show ?thesis
    unfolding lagrange_denom_def by (rule KS.prod_closed) (use facK in auto)
qed


lemma lagrange_denom_algebraic_int:
  assumes ilt: "i < D"
  shows "algebraic_int (lagrange_denom i)"
proof -
  have ai_i: "algebraic_int (emb i eta)"
    using basis_algebraic_int_at_emb[OF ilt, of 1] by (simp add: basis_def)
  have fac_ai: "algebraic_int (emb i eta - emb m eta)" if m: "m \<in> {0..<D} - {i}" for m
  proof -
    have ai_m: "algebraic_int (emb m eta)"
      using m basis_algebraic_int_at_emb[of m 1] by (auto simp: basis_def)
    show ?thesis
      by (rule algebraic_int_diff[OF ai_i ai_m])
  qed
  show ?thesis
    unfolding lagrange_denom_def by (intro algebraic_int_prod fac_ai)
qed

lemma lagrange_factor_in_K:
  assumes ilt: "i < D"
    and m: "m \<in> {0..<D} - {i}"
  shows "emb i eta - emb m eta \<in> K"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have eiK: "emb i eta \<in> K"
    by (rule emb_mem_K[OF ilt])
  have emK: "emb m eta \<in> K"
    using m by (auto intro: emb_mem_K)
  have neg_emK: "- (emb m eta) \<in> K"
    by (rule KS.uminus_closed[OF emK])
  have sumK: "emb i eta + - (emb m eta) \<in> K"
    by (rule KS.add_closed[OF eiK neg_emK])
  show ?thesis
    using sumK by simp
qed

lemma lagrange_factor_algebraic_int:
  assumes ilt: "i < D"
    and m: "m \<in> {0..<D} - {i}"
  shows "algebraic_int (emb i eta - emb m eta)"
proof -
  have ai_i: "algebraic_int (emb i eta)"
    using basis_algebraic_int_at_emb[OF ilt, of 1] by (simp add: basis_def)
  have ai_m: "algebraic_int (emb m eta)"
    using m basis_algebraic_int_at_emb[of m 1] by (auto simp: basis_def)
  show ?thesis
    by (rule algebraic_int_diff[OF ai_i ai_m])
qed

lemma sigma_emb_eta_root_of_min_int_poly:
  assumes ilt: "i < D"
    and sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)"
  shows "\<sigma> (emb i eta) \<in> set (complex_roots_of_int_poly (min_int_poly eta))"
proof -
  have p_over: "of_int_poly (min_int_poly eta) \<in> poly_over (\<rat> :: complex set)"
    by (auto simp: poly_over_def)
  have p0: "min_int_poly eta \<noteq> 0"
    using eta_int by auto
  have emb_root: "poly (of_int_poly (min_int_poly eta)) (emb i eta) = 0"
    using emb_eta_root_of_min_int_poly[OF ilt] complex_roots_of_int_poly(1)[OF p0] by simp
  have root_sigma: "poly (of_int_poly (min_int_poly eta)) (\<sigma> (emb i eta)) = 0"
    by (rule field_auto_maps_root[OF K_subfield Rats_subfield Rats_subset_K sigma p_over emb_mem_K[OF ilt] emb_root])
  show ?thesis
    using root_sigma complex_roots_of_int_poly(1)[OF p0] by simp
qed

lemma cmod_sigma_emb_eta_le_gs_house:
  assumes ilt: "i < D"
    and sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)"
  shows "cmod (\<sigma> (emb i eta)) \<le> gs_house eta"
  by (rule cmod_le_gs_house_of_root[OF sigma_emb_eta_root_of_min_int_poly[OF ilt sigma]])

lemma cmod_sigma_lagrange_factor_le:
  assumes ilt: "i < D"
    and m: "m \<in> {0..<D} - {i}"
    and sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)"
  shows "cmod (\<sigma> (emb i eta - emb m eta)) \<le> 2 * max 1 (gs_house eta)"
proof -
  have hom: "field_hom_on K \<sigma>"
    by (rule field_auto_imp_field_hom_on[OF K_subfield sigma])
  have eiK: "emb i eta \<in> K"
    by (rule emb_mem_K[OF ilt])
  have emK: "emb m eta \<in> K"
    using m by (auto intro: emb_mem_K)
  have sigma_diff: "\<sigma> (emb i eta - emb m eta) = \<sigma> (emb i eta) - \<sigma> (emb m eta)"
    by (rule field_hom_on.hom_diff[OF hom eiK emK])
  have le_i: "cmod (\<sigma> (emb i eta)) \<le> max 1 (gs_house eta)"
    using cmod_sigma_emb_eta_le_gs_house[OF ilt sigma] by simp
  have mlt: "m < D"
    using m by simp
  have le_m: "cmod (\<sigma> (emb m eta)) \<le> max 1 (gs_house eta)"
    using cmod_sigma_emb_eta_le_gs_house[OF mlt sigma] by simp
  have "cmod (\<sigma> (emb i eta - emb m eta)) = cmod (\<sigma> (emb i eta) - \<sigma> (emb m eta))"
    by (simp add: sigma_diff)
  also have "... \<le> cmod (\<sigma> (emb i eta)) + cmod (\<sigma> (emb m eta))"
    by (rule norm_triangle_ineq4)
  also have "... \<le> max 1 (gs_house eta) + max 1 (gs_house eta)"
    by (rule add_mono[OF le_i le_m])
  also have "... = 2 * max 1 (gs_house eta)"
    by simp
  finally show ?thesis .
qed

lemma sigma_prod_lagrange_factor_eq:
  assumes ilt: "i < D"
    and sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)"
    and finS: "finite S"
    and Ssub: "S \<subseteq> {0..<D} - {i}"
  shows "\<sigma> (\<Prod>m\<in>S. emb i eta - emb m eta) = (\<Prod>m\<in>S. \<sigma> (emb i eta - emb m eta))"
using finS Ssub
proof (induction S rule: finite_induct)
  case empty
  then show ?case
    using sigma by (simp add: field_auto_mem_iff)
next
  case (insert m S)
  interpret KS: Subfield K
    by (rule K_subfield)
  have hom: "field_hom_on K \<sigma>"
    by (rule field_auto_imp_field_hom_on[OF K_subfield sigma])
  have mdom: "m \<in> {0..<D} - {i}"
    using insert.prems by auto
  have facK: "emb i eta - emb m eta \<in> K"
    by (rule lagrange_factor_in_K[OF ilt mdom])
  have Ssub': "S \<subseteq> {0..<D} - {i}"
    using insert.prems by auto
  have prodK: "(\<Prod>x\<in>S. emb i eta - emb x eta) \<in> K"
  proof (rule KS.prod_closed)
    fix x
    assume xS: "x \<in> S"
    with Ssub' have xdom: "x \<in> {0..<D} - {i}"
      by auto
    show "emb i eta - emb x eta \<in> K"
      by (rule lagrange_factor_in_K[OF ilt xdom])
  qed
  have "\<sigma> (\<Prod>x\<in>insert m S. emb i eta - emb x eta) = \<sigma> ((emb i eta - emb m eta) * (\<Prod>x\<in>S. emb i eta - emb x eta))"
    using insert.hyps by simp
  also have "... = \<sigma> (emb i eta - emb m eta) * \<sigma> (\<Prod>x\<in>S. emb i eta - emb x eta)"
    by (rule field_hom_on.hom_mult[OF hom facK prodK])
  also have "... = \<sigma> (emb i eta - emb m eta) * (\<Prod>x\<in>S. \<sigma> (emb i eta - emb x eta))"
    by (simp add: insert.IH[OF Ssub'])
  also have "... = (\<Prod>x\<in>insert m S. \<sigma> (emb i eta - emb x eta))"
    using insert.hyps by simp
  finally show ?case .
qed

lemma cmod_sigma_lagrange_denom_le:
  assumes ilt: "i < D"
    and sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)"
  shows "cmod (\<sigma> (lagrange_denom i)) \<le> (2 * max 1 (gs_house eta)) ^ (D - 1)"
proof -
  have finS: "finite ({0..<D} - {i})"
    by simp
  have Ssub: "{0..<D} - {i} \<subseteq> {0..<D} - {i}"
    by simp
  have sigma_prod: "\<sigma> (lagrange_denom i) = (\<Prod>m\<in>{0..<D} - {i}. \<sigma> (emb i eta - emb m eta))"
    unfolding lagrange_denom_def by (rule sigma_prod_lagrange_factor_eq[OF ilt sigma finS Ssub])
  have "cmod (\<sigma> (lagrange_denom i)) = cmod (\<Prod>m\<in>{0..<D} - {i}. \<sigma> (emb i eta - emb m eta))"
    by (simp add: sigma_prod)
  also have "... \<le> (\<Prod>m\<in>{0..<D} - {i}. cmod (\<sigma> (emb i eta - emb m eta)))"
    by (rule norm_prod_le)
  also have "... \<le> (\<Prod>m\<in>{0..<D} - {i}. 2 * max 1 (gs_house eta))"
    by (intro prod_mono conjI cmod_sigma_lagrange_factor_le[OF ilt _ sigma]) auto
  also have "... = (2 * max 1 (gs_house eta)) ^ card ({0..<D} - {i})"
    by simp
  also have "... = (2 * max 1 (gs_house eta)) ^ (D - 1)"
    using ilt by simp
  finally show ?thesis .
qed

lemma gs_house_lagrange_denom_le:
  assumes ilt: "i < D"
  shows "gs_house (lagrange_denom i) \<le> (2 * max 1 (gs_house eta)) ^ (D - 1)"
proof (rule gs_house_le_of_emb_bound[OF finite normal separable lagrange_denom_algebraic_int[OF ilt] lagrange_denom_in_K[OF ilt]])
  show "0 \<le> (2 * max 1 (gs_house eta)) ^ (D - 1)"
    by simp
  fix j
  assume jlt: "j < D"
  show "cmod (emb j (lagrange_denom i)) \<le> (2 * max 1 (gs_house eta)) ^ (D - 1)"
    by (rule cmod_sigma_lagrange_denom_le[OF ilt emb_in_field_auto[OF jlt]])
qed

lemma inverse_lagrange_denom_le:
  assumes ilt: "i < D"
  shows "cmod (inverse (lagrange_denom i)) \<le>
      ((2 * max 1 (gs_house eta)) ^ (D - 1)) ^
        (card (set (complex_roots_of_int_poly (min_int_poly (lagrange_denom i)))) - 1)"
proof -
  let ?r = "card (set (complex_roots_of_int_poly (min_int_poly (lagrange_denom i)))) - 1"
  let ?H = "(2 * max 1 (gs_house eta)) ^ (D - 1)"
  have ai: "algebraic_int (lagrange_denom i)"
    by (rule lagrange_denom_algebraic_int[OF ilt])
  have nz: "lagrange_denom i \<noteq> 0"
    by (rule lagrange_denom_nonzero[OF ilt])
  have one_le: "1 \<le> cmod (lagrange_denom i) * gs_house (lagrange_denom i) ^ ?r"
    by (rule one_le_self_mul_house_pow_of_nonzero_algebraic_int[OF ai nz])
  have cpos: "0 < cmod (lagrange_denom i)"
    using nz by simp
  have inv_le_real: "inverse (cmod (lagrange_denom i)) \<le> gs_house (lagrange_denom i) ^ ?r"
    using one_le cpos by (simp add: field_simps)
  have inv_le_house: "cmod (inverse (lagrange_denom i)) \<le> gs_house (lagrange_denom i) ^ ?r"
    using inv_le_real by (simp add: norm_inverse)
  have house_le: "gs_house (lagrange_denom i) \<le> ?H"
    by (rule gs_house_lagrange_denom_le[OF ilt])
  have H_nonneg: "0 \<le> ?H"
    by simp
  have house_pow_le: "gs_house (lagrange_denom i) ^ ?r \<le> ?H ^ ?r"
    by (rule power_mono[OF house_le]) (use H_nonneg in auto)
  show ?thesis
    using inv_le_house house_pow_le by linarith
qed

lemma coeff_linear_factor_mult_le:
  assumes coeff_bnd: "\<And>n. cmod (Polynomial.coeff p n) \<le> B"
  assumes B_nonneg: "0 \<le> B"
  shows "cmod (Polynomial.coeff ([:-a, 1:] * p) n) \<le> (1 + cmod a) * B"
proof (cases n)
  case 0
  have "cmod (Polynomial.coeff ([:-a, 1:] * p) 0) = cmod (a * Polynomial.coeff p 0)"
    by simp
  also have "... = cmod a * cmod (Polynomial.coeff p 0)"
    by (simp add: norm_mult)
  also have "... \<le> cmod a * B"
    using coeff_bnd[of 0] by (intro mult_left_mono) auto
  also have "... \<le> cmod a * B + B"
    using B_nonneg by linarith
  also have "... = (1 + cmod a) * B"
    by (simp add: distrib_right)
  finally show ?thesis
    using 0 by simp
next
  case (Suc m)
  have coeff_eq: "Polynomial.coeff ([:-a, 1:] * p) (Suc m) =
      - a * Polynomial.coeff p (Suc m) + Polynomial.coeff p m"
    by simp
  have "cmod (Polynomial.coeff ([:-a, 1:] * p) (Suc m)) \<le>
      cmod (- a * Polynomial.coeff p (Suc m)) + cmod (Polynomial.coeff p m)"
    unfolding coeff_eq by (rule norm_triangle_ineq)
  also have "... = cmod a * cmod (Polynomial.coeff p (Suc m)) + cmod (Polynomial.coeff p m)"
    by (simp add: norm_mult)
  also have "... \<le> cmod a * B + B"
    using coeff_bnd[of "Suc m"] coeff_bnd[of m]
    by (intro add_mono mult_left_mono) auto
  also have "... = (1 + cmod a) * B"
    by (simp add: distrib_right)
  finally show ?thesis
    using Suc by simp
qed

lemma coeff_prod_linear_factors_le_prod:
  assumes finS: "finite S"
  shows "\<And>k. cmod (Polynomial.coeff (\<Prod>m\<in>S. [:- f m, 1:]) k) \<le> (\<Prod>m\<in>S. (1 + cmod (f m)))"
using finS
proof (induction S rule: finite_induct)
  case empty
  then show ?case
    by (cases k) simp_all
next
  case (insert m S)
  have B_nonneg: "0 \<le> (\<Prod>x\<in>S. (1 + cmod (f x)))"
    by (intro prod_nonneg) simp_all
  have "cmod (Polynomial.coeff (\<Prod>x\<in>insert m S. [:- f x, 1:]) k) =
      cmod (Polynomial.coeff ([:- f m, 1:] * (\<Prod>x\<in>S. [:- f x, 1:])) k)"
    using insert.hyps by simp
  also have "... \<le> (1 + cmod (f m)) * (\<Prod>x\<in>S. (1 + cmod (f x)))"
    by (rule coeff_linear_factor_mult_le[OF insert.IH B_nonneg])
  also have "... = (\<Prod>x\<in>insert m S. (1 + cmod (f x)))"
    using insert.hyps by simp
  finally show ?case .
qed

lemma coeff_lagrange_numerator_le:
  assumes ilt: "i < D"
  shows "cmod (Polynomial.coeff (\<Prod>m\<in>{0..<D} - {i}. [:- emb m eta, 1:]) k) \<le>
      (2 * max 1 (gs_house eta)) ^ (D - 1)"
proof -
  have coeff_le_prod:
    "cmod (Polynomial.coeff (\<Prod>m\<in>{0..<D} - {i}. [:- emb m eta, 1:]) k) \<le>
      (\<Prod>m\<in>{0..<D} - {i}. (1 + cmod (emb m eta)))"
    by (rule coeff_prod_linear_factors_le_prod) simp
  have prod_le: "(\<Prod>m\<in>{0..<D} - {i}. (1 + cmod (emb m eta))) \<le>
      (\<Prod>m\<in>{0..<D} - {i}. (2 * max 1 (gs_house eta)))"
  proof (intro prod_mono)
    fix m
    assume m: "m \<in> {0..<D} - {i}"
    have mlt: "m < D"
      using m by simp
    have emb_le: "cmod (emb m eta) \<le> max 1 (gs_house eta)"
      using cmod_emb_eta_le_gs_house[OF mlt] by simp
    have nonneg: "0 \<le> 1 + cmod (emb m eta)"
      by simp
    have le: "1 + cmod (emb m eta) \<le> 2 * max 1 (gs_house eta)"
      using emb_le by linarith
    show "0 \<le> 1 + cmod (emb m eta) \<and> 1 + cmod (emb m eta) \<le> 2 * max 1 (gs_house eta)"
      using nonneg le by blast
  qed
  have "cmod (Polynomial.coeff (\<Prod>m\<in>{0..<D} - {i}. [:- emb m eta, 1:]) k) \<le>
      (\<Prod>m\<in>{0..<D} - {i}. (1 + cmod (emb m eta)))"
    by (rule coeff_le_prod)
  also have "... \<le> (\<Prod>m\<in>{0..<D} - {i}. (2 * max 1 (gs_house eta)))"
    by (rule prod_le)
  also have "... = (2 * max 1 (gs_house eta)) ^ card ({0..<D} - {i})"
    by simp
  also have "... = (2 * max 1 (gs_house eta)) ^ (D - 1)"
    using ilt by simp
  finally show ?thesis .
qed

lemma card_roots_min_int_poly_le_D:
  assumes xK: "x \<in> K"
    and ai: "algebraic_int x"
  shows "card (set (complex_roots_of_int_poly (min_int_poly x))) \<le> D"
proof -
  let ?R = "set (complex_roots_of_int_poly (min_int_poly x))"
  have sub: "?R \<subseteq> (\<lambda>\<sigma>. \<sigma> x) ` field_auto K (\<rat> :: complex set)"
  proof
    fix z
    assume zR: "z \<in> ?R"
    have zmin: "poly (minpoly (\<rat> :: complex set) x) z = 0"
      by (rule minpoly_root_of_min_int_poly_root[OF finite normal separable ai zR])
    obtain \<sigma> where sigma: "\<sigma> \<in> field_auto K (\<rat> :: complex set)" and sx: "\<sigma> x = z"
      using finite_galois_root_transfer[OF finite normal separable xK zmin] by blast
    show "z \<in> (\<lambda>\<sigma>. \<sigma> x) ` field_auto K (\<rat> :: complex set)"
      using sigma sx by blast
  qed
  have finG: "finite (field_auto K (\<rat> :: complex set))"
    by (rule finite_normal_separable_field_auto[OF finite normal separable])
  have finImg: "finite ((\<lambda>\<sigma>. \<sigma> x) ` field_auto K (\<rat> :: complex set))"
    using finG by simp
  have "card ?R \<le> card ((\<lambda>\<sigma>. \<sigma> x) ` field_auto K (\<rat> :: complex set))"
    by (rule card_mono[OF finImg sub])
  also have "... \<le> card (field_auto K (\<rat> :: complex set))"
    using finG by (rule card_image_le)
  also have "... = D"
  proof -
    have img_eq: "emb ` {0..<D} = field_auto K (\<rat> :: complex set)"
      using ebij by (simp add: bij_betw_def)
    have inj: "inj_on emb {0..<D}"
      using ebij by (simp add: bij_betw_def)
    have "card (field_auto K (\<rat> :: complex set)) = card (emb ` {0..<D})"
      by (simp add: img_eq)
    also have "... = card {0..<D}"
      using inj by (simp add: card_image)
    finally show ?thesis
      by simp
  qed
  finally show ?thesis .
qed

lemma inverse_lagrange_denom_le_uniform:
  assumes ilt: "i < D"
  shows "cmod (inverse (lagrange_denom i)) \<le>
      ((2 * max 1 (gs_house eta)) ^ (D - 1)) ^ (D - 1)"
proof -
  let ?R = "set (complex_roots_of_int_poly (min_int_poly (lagrange_denom i)))"
  let ?r = "card ?R - 1"
  let ?H = "(2 * max 1 (gs_house eta)) ^ (D - 1)"
  have root_le_D: "card ?R \<le> D"
    by (rule card_roots_min_int_poly_le_D[OF lagrange_denom_in_K[OF ilt] lagrange_denom_algebraic_int[OF ilt]])
  have p0: "min_int_poly (lagrange_denom i) \<noteq> 0"
    using lagrange_denom_algebraic_int[OF ilt] by auto
  have root_eq0: "poly (complex_of_int_poly (min_int_poly (lagrange_denom i))) (lagrange_denom i) = 0"
    using lagrange_denom_algebraic_int[OF ilt] by (auto simp: min_int_poly_represents)
  have root_mem: "lagrange_denom i \<in> ?R"
    using complex_roots_of_int_poly(1)[OF p0] root_eq0 by simp
  have finR: "finite ?R"
    by simp
  have root_nonempty: "?R \<noteq> {}"
    using root_mem by auto
  have root_pos: "0 < card ?R"
    using finR root_nonempty by (simp add: card_gt_0_iff)
  have r_le: "?r \<le> D - 1"
    using root_le_D root_pos by arith
  have H_ge_one: "1 \<le> ?H"
    by (rule one_le_power) simp
  have Hpow_le: "?H ^ ?r \<le> ?H ^ (D - 1)"
    by (rule power_increasing[OF r_le H_ge_one])
  show ?thesis
    by (rule order_trans[OF inverse_lagrange_denom_le[OF ilt] Hpow_le])
qed

definition power_basis_inverse_bound :: real
  where "power_basis_inverse_bound = ((2 * max 1 (gs_house eta)) ^ (D - 1)) ^ D"

lemma power_basis_inverse_bound_nonneg [simp]:
  shows "0 \<le> power_basis_inverse_bound"
  unfolding power_basis_inverse_bound_def by simp

lemma lagrange_basis_poly_coeff_le_power_basis_inverse_bound:
  assumes ilt: "i < D"
  shows "cmod (Polynomial.coeff (lagrange_basis_poly i) k) \<le> power_basis_inverse_bound"
proof -
  let ?H = "(2 * max 1 (gs_house eta)) ^ (D - 1)"
  have coeff_eq:
    "Polynomial.coeff (lagrange_basis_poly i) k =
      inverse (lagrange_denom i) * Polynomial.coeff (\<Prod>m\<in>{0..<D} - {i}. [:- emb m eta, 1:]) k"
    by (simp add: lagrange_basis_poly_def)
  have inv_le: "cmod (inverse (lagrange_denom i)) \<le> ?H ^ (D - 1)"
    by (rule inverse_lagrange_denom_le_uniform[OF ilt])
  have num_le: "cmod (Polynomial.coeff (\<Prod>m\<in>{0..<D} - {i}. [:- emb m eta, 1:]) k) \<le> ?H"
    by (rule coeff_lagrange_numerator_le[OF ilt])
  have "cmod (Polynomial.coeff (lagrange_basis_poly i) k) =
      cmod (inverse (lagrange_denom i)) *
      cmod (Polynomial.coeff (\<Prod>m\<in>{0..<D} - {i}. [:- emb m eta, 1:]) k)"
    by (simp add: coeff_eq norm_mult)
  also have "... \<le> ?H ^ (D - 1) * ?H"
    using inv_le num_le by (intro mult_mono) simp_all
  also have "... = ?H ^ D"
    using Dpos by (cases D) (simp_all add: power_add)
  finally show ?thesis
    by (simp add: power_basis_inverse_bound_def)
qed


lemma inverse_basis_matrix_entry_le_power_basis_inverse_bound:
  assumes ilt: "i < D"
    and klt: "k < D"
  shows "cmod (REC.inverse_basis_matrix_entry k i) \<le> power_basis_inverse_bound"
  by (rule inverse_basis_matrix_entry_bound_of_lagrange_coeff_bound[OF lagrange_basis_poly_coeff_le_power_basis_inverse_bound ilt klt])

end

end
