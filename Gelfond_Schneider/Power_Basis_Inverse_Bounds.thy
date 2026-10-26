(*  Title:      Gelfond_Schneider/Power_Basis_Inverse_Bounds.thy
    Author:     OpenAI Codex

Crude inverse-Vandermonde bounds for the power-basis route.  The aim here is
not sharp constants, only a clean reduction of the remaining `inv_bound` input
to explicit coefficient and denominator estimates.
*)

theory Power_Basis_Inverse_Bounds
  imports
    Power_Basis_Recovery
    Power_Basis
begin

locale finite_normal_galois_power_basis = finite_galois_power_basis K eta D emb
  for K :: "complex set"
  and eta :: complex
  and D :: nat
  and emb :: "nat \<Rightarrow> complex \<Rightarrow> complex" +
  assumes finite: "finite_subfield_tower \<rat> K"
    and normal: "normal_extension K \<rat>"
    and separable: "separable_extension K \<rat>"
begin

lemma lagrange_denom_in_K:
  assumes "i < D"
  shows "lagrange_denom i \<in> K"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have facK: "emb i eta - emb m eta \<in> K" if m: "m \<in> {0..<D} - {i}" for m
    using assms emb_eta_in_K m by auto
  show ?thesis
    unfolding lagrange_denom_def by (rule KS.prod_closed) (use facK in auto)
qed

lemma lagrange_factor_algebraic_int:
  assumes "i < D" "m < D"
  shows "algebraic_int (emb i eta - emb m eta)"
  using basis_algebraic_int_at_emb[of _ 1] assms by (auto simp: basis_def)

lemma lagrange_denom_algebraic_int:
  assumes "i < D"
  shows "algebraic_int (lagrange_denom i)"
  using assms by (force simp: lagrange_denom_def lagrange_factor_algebraic_int)

lemma lagrange_factor_in_K:
  assumes "i < D" "m \<in> {0..<D} - {i}"
  shows "emb i eta - emb m eta \<in> K"
  using K_subfield Subfield.diff_closed emb_eta_in_K assms by auto

lemma sigma_emb_eta_root_of_min_int_poly:
  assumes "i < D"
    and sigma: "\<sigma> \<in> field_auto K \<rat>"
  shows "\<sigma> (emb i eta) \<in> set (complex_roots_of_int_poly (min_int_poly eta))"
proof -
  have p_over: "of_int_poly (min_int_poly eta) \<in> poly_over \<rat>"
    by (auto simp: poly_over_def)
  show ?thesis
    using field_auto_maps_root[OF K_subfield Rats_subfield Rats_subset_K sigma]
          p_over emb_eta_in_K[OF \<open>i < D\<close>] complex_roots_of_int_poly(1) eta_int
    using assms(1) emb_eta_root_of_min_int_poly by force
qed

lemma cmod_sigma_emb_eta_le_gs_house:
  assumes "i < D"
    and sigma: "\<sigma> \<in> field_auto K \<rat>"
  shows "cmod (\<sigma> (emb i eta)) \<le> gs_house eta"
  by (rule cmod_le_gs_house_of_root[OF sigma_emb_eta_root_of_min_int_poly[OF \<open>i < D\<close> sigma]])

lemma cmod_sigma_lagrange_factor_le:
  assumes "i < D"
    and   "m \<in> {0..<D} - {i}"
    and sigma: "\<sigma> \<in> field_auto K \<rat>"
  shows "cmod (\<sigma> (emb i eta - emb m eta)) \<le> 2 * max 1 (gs_house eta)"
proof -
  have hom: "field_hom_on K \<sigma>"
    by (rule field_auto_imp_field_hom_on[OF K_subfield sigma])
  have sigma_diff: "\<sigma> (emb i eta - emb m eta) = \<sigma> (emb i eta) - \<sigma> (emb m eta)"
    using field_hom_on.hom_diff[OF hom] assms emb_eta_in_K by auto
  have le_i: "cmod (\<sigma> (emb i eta)) \<le> max 1 (gs_house eta)"
    using cmod_sigma_emb_eta_le_gs_house[OF \<open>i < D\<close> sigma] by simp
  have "cmod (\<sigma> (emb m eta)) \<le> max 1 (gs_house eta)"
    using cmod_sigma_emb_eta_le_gs_house assms by force
  then show ?thesis
    using le_i sigma_diff by (smt (verit, best) complex_mod_triangle_sub diff_add_cancel)
qed

lemma sigma_prod_lagrange_factor_eq:
  assumes "i < D"
    and sigma: "\<sigma> \<in> field_auto K \<rat>"
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
    by (rule lagrange_factor_in_K[OF \<open>i < D\<close> mdom])
  have Ssub': "S \<subseteq> {0..<D} - {i}"
    using insert.prems by auto
  have prodK: "(\<Prod>x\<in>S. emb i eta - emb x eta) \<in> K"
  proof (rule KS.prod_closed)
    fix x
    assume xS: "x \<in> S"
    with Ssub' have xdom: "x \<in> {0..<D} - {i}"
      by auto
    show "emb i eta - emb x eta \<in> K"
      by (rule lagrange_factor_in_K[OF \<open>i < D\<close> xdom])
  qed
  have "\<sigma> (\<Prod>x\<in>insert m S. emb i eta - emb x eta) = \<sigma> ((emb i eta - emb m eta) * (\<Prod>x\<in>S. emb i eta - emb x eta))"
    using insert.hyps by simp
  also have "\<dots> = \<sigma> (emb i eta - emb m eta) * \<sigma> (\<Prod>x\<in>S. emb i eta - emb x eta)"
    by (rule field_hom_on.hom_mult[OF hom facK prodK])
  also have "\<dots> = \<sigma> (emb i eta - emb m eta) * (\<Prod>x\<in>S. \<sigma> (emb i eta - emb x eta))"
    by (simp add: insert.IH[OF Ssub'])
  also have "\<dots> = (\<Prod>x\<in>insert m S. \<sigma> (emb i eta - emb x eta))"
    using insert.hyps by simp
  finally show ?case .
qed

lemma cmod_sigma_lagrange_denom_le:
  assumes "i < D"
    and sigma: "\<sigma> \<in> field_auto K \<rat>"
  shows "cmod (\<sigma> (lagrange_denom i)) \<le> (2 * max 1 (gs_house eta)) ^ (D - 1)"
proof -
  have finS: "finite ({0..<D} - {i})"
    by simp
  have Ssub: "{0..<D} - {i} \<subseteq> {0..<D} - {i}"
    by simp
  have sigma_prod: "\<sigma> (lagrange_denom i) = (\<Prod>m\<in>{0..<D} - {i}. \<sigma> (emb i eta - emb m eta))"
    unfolding lagrange_denom_def by (rule sigma_prod_lagrange_factor_eq[OF \<open>i < D\<close> sigma finS Ssub])
  have "cmod (\<sigma> (lagrange_denom i)) = cmod (\<Prod>m\<in>{0..<D} - {i}. \<sigma> (emb i eta - emb m eta))"
    by (simp add: sigma_prod)
  also have "\<dots> \<le> (\<Prod>m\<in>{0..<D} - {i}. cmod (\<sigma> (emb i eta - emb m eta)))"
    by (rule norm_prod_le)
  also have "\<dots> \<le> (\<Prod>m\<in>{0..<D} - {i}. 2 * max 1 (gs_house eta))"
    by (intro prod_mono conjI cmod_sigma_lagrange_factor_le[OF \<open>i < D\<close> _ sigma]) auto
  also have "\<dots> = (2 * max 1 (gs_house eta)) ^ card ({0..<D} - {i})"
    by simp
  also have "\<dots> = (2 * max 1 (gs_house eta)) ^ (D - 1)"
    using \<open>i < D\<close> by simp
  finally show ?thesis .
qed

lemma gs_house_lagrange_denom_le:
  assumes "i < D"
  shows "gs_house (lagrange_denom i) \<le> (2 * max 1 (gs_house eta)) ^ (D - 1)"
proof (rule gs_house_le_of_emb_bound[OF finite normal separable lagrange_denom_algebraic_int[OF \<open>i < D\<close>] lagrange_denom_in_K[OF \<open>i < D\<close>]])
  show "0 \<le> (2 * max 1 (gs_house eta)) ^ (D - 1)"
    by simp
  fix j
  assume jlt: "j < D"
  show "cmod (emb j (lagrange_denom i)) \<le> (2 * max 1 (gs_house eta)) ^ (D - 1)"
    by (rule cmod_sigma_lagrange_denom_le[OF \<open>i < D\<close> emb_in_field_auto[OF jlt]])
qed

lemma inverse_lagrange_denom_le:
  assumes "i < D"
  shows "cmod (inverse (lagrange_denom i)) \<le>
      ((2 * max 1 (gs_house eta)) ^ (D - 1)) ^
        (card (set (complex_roots_of_int_poly (min_int_poly (lagrange_denom i)))) - 1)"
proof -
  let ?r = "card (set (complex_roots_of_int_poly (min_int_poly (lagrange_denom i)))) - 1"
  let ?H = "(2 * max 1 (gs_house eta)) ^ (D - 1)"
  have ai: "algebraic_int (lagrange_denom i)"
    by (rule lagrange_denom_algebraic_int[OF \<open>i < D\<close>])
  have nz: "lagrange_denom i \<noteq> 0"
    by (rule lagrange_denom_nonzero[OF \<open>i < D\<close>])
  have one_le: "1 \<le> cmod (lagrange_denom i) * gs_house (lagrange_denom i) ^ ?r"
    by (rule one_le_self_mul_house_pow_of_nonzero_algebraic_int[OF ai nz])
  have cpos: "0 < cmod (lagrange_denom i)"
    using nz by simp
  have inv_le_real: "inverse (cmod (lagrange_denom i)) \<le> gs_house (lagrange_denom i) ^ ?r"
    using one_le cpos by (simp add: field_simps)
  have inv_le_house: "cmod (inverse (lagrange_denom i)) \<le> gs_house (lagrange_denom i) ^ ?r"
    using inv_le_real by (simp add: norm_inverse)
  have house_le: "gs_house (lagrange_denom i) \<le> ?H"
    by (rule gs_house_lagrange_denom_le[OF \<open>i < D\<close>])
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
  also have "\<dots> = cmod a * cmod (Polynomial.coeff p 0)"
    by (simp add: norm_mult)
  also have "\<dots> \<le> cmod a * B"
    using coeff_bnd[of 0] by (intro mult_left_mono) auto
  also have "\<dots> \<le> cmod a * B + B"
    using B_nonneg by linarith
  also have "\<dots> = (1 + cmod a) * B"
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
  also have "\<dots> = cmod a * cmod (Polynomial.coeff p (Suc m)) + cmod (Polynomial.coeff p m)"
    by (simp add: norm_mult)
  also have "\<dots> \<le> cmod a * B + B"
    using coeff_bnd[of "Suc m"] coeff_bnd[of m]
    by (intro add_mono mult_left_mono) auto
  also have "\<dots> = (1 + cmod a) * B"
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
  also have "\<dots> \<le> (1 + cmod (f m)) * (\<Prod>x\<in>S. (1 + cmod (f x)))"
    by (rule coeff_linear_factor_mult_le[OF insert.IH B_nonneg])
  also have "\<dots> = (\<Prod>x\<in>insert m S. (1 + cmod (f x)))"
    using insert.hyps by simp
  finally show ?case .
qed

lemma coeff_lagrange_numerator_le:
  assumes "i < D"
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
  also have "\<dots> \<le> (\<Prod>m\<in>{0..<D} - {i}. (2 * max 1 (gs_house eta)))"
    by (rule prod_le)
  also have "\<dots> = (2 * max 1 (gs_house eta)) ^ card ({0..<D} - {i})"
    by simp
  also have "\<dots> = (2 * max 1 (gs_house eta)) ^ (D - 1)"
    using \<open>i < D\<close> by simp
  finally show ?thesis .
qed

lemma card_roots_min_int_poly_le_D:
  assumes xK: "x \<in> K"
    and ai: "algebraic_int x"
  shows "card (set (complex_roots_of_int_poly (min_int_poly x))) \<le> D"
proof -
  let ?R = "set (complex_roots_of_int_poly (min_int_poly x))"
  have sub: "?R \<subseteq> (\<lambda>\<sigma>. \<sigma> x) ` field_auto K \<rat>"
    using finite_galois_root_transfer[OF finite normal separable xK]
    using ai finite separable minpoly_root_of_min_int_poly_root normal by blast 
  have finG: "finite (field_auto K \<rat>)"
    by (rule finite_normal_separable_field_auto[OF finite normal separable])
  have finImg: "finite ((\<lambda>\<sigma>. \<sigma> x) ` field_auto K \<rat>)"
    using finG by simp
  have "card ?R \<le> card (field_auto K \<rat>)"
    using finG card_mono[OF finImg sub] sub surj_card_le by blast
  also have "\<dots> = D"
  proof -
    have img_eq: "field_auto K \<rat>= emb ` {0..<D}"
      using ebij by (simp add: bij_betw_def)
    have "inj_on emb {0..<D}"
      using ebij by (simp add: bij_betw_def)
    then show ?thesis
      using img_eq by (simp add: card_image)
  qed
  finally show ?thesis .
qed

lemma inverse_lagrange_denom_le_uniform:
  assumes "i < D"
  shows "cmod (inverse (lagrange_denom i)) \<le>
      ((2 * max 1 (gs_house eta)) ^ (D - 1)) ^ (D - 1)"
proof -
  let ?R = "set (complex_roots_of_int_poly (min_int_poly (lagrange_denom i)))"
  let ?r = "card ?R - 1"
  let ?H = "(2 * max 1 (gs_house eta)) ^ (D - 1)"
  have root_le_D: "card ?R \<le> D"
    using assms card_roots_min_int_poly_le_D lagrange_denom_algebraic_int lagrange_denom_in_K
    by presburger
  have p0: "min_int_poly (lagrange_denom i) \<noteq> 0"
    using lagrange_denom_algebraic_int[OF \<open>i < D\<close>] by auto
  have "poly (complex_of_int_poly (min_int_poly (lagrange_denom i))) (lagrange_denom i) = 0"
    using lagrange_denom_algebraic_int[OF \<open>i < D\<close>] by (auto simp: min_int_poly_represents)
  then have "lagrange_denom i \<in> ?R"
    using complex_roots_of_int_poly(1)[OF p0] by simp
  then have root_pos: "0 < card ?R"
    using card_gt_0_iff by fastforce
  have r_le: "?r \<le> D - 1"
    using root_le_D root_pos by arith
  have "?H ^ ?r \<le> ?H ^ (D - 1)"
    using r_le by (smt (verit, ccfv_SIG) one_le_power pow_mono_exp)
  then show ?thesis
    using assms inverse_lagrange_denom_le by force
qed

definition power_basis_inverse_bound :: real
  where "power_basis_inverse_bound \<equiv> ((2 * max 1 (gs_house eta)) ^ (D - 1)) ^ D"

lemma power_basis_inverse_bound_nonneg [simp]:
  shows "0 \<le> power_basis_inverse_bound"
  unfolding power_basis_inverse_bound_def by simp

lemma lagrange_basis_poly_coeff_le_power_basis_inverse_bound:
  assumes "i < D"
  shows "cmod (Polynomial.coeff (lagrange_basis_poly i) k) \<le> power_basis_inverse_bound"
proof -
  let ?H = "(2 * max 1 (gs_house eta)) ^ (D - 1)"
  have "cmod (Polynomial.coeff (lagrange_basis_poly i) k) =
      cmod (inverse (lagrange_denom i)) * cmod (Polynomial.coeff (\<Prod>m\<in>{0..<D} - {i}. [:- emb m eta, 1:]) k)"
    by (simp add: lagrange_basis_poly_def norm_mult)
  also have "\<dots> \<le> ?H ^ (D - 1) * ?H"
    using inverse_lagrange_denom_le_uniform coeff_lagrange_numerator_le \<open>i < D\<close> 
    by (intro mult_mono) simp_all
  also have "\<dots> = ?H ^ D"
    using Dpos by (cases D) (simp_all add: power_add)
  finally show ?thesis
    by (simp add: power_basis_inverse_bound_def)
qed


lemma inverse_basis_matrix_entry_le_power_basis_inverse_bound:
  assumes "i < D"
  shows "cmod (REC.inverse_basis_matrix_entry k i) \<le> power_basis_inverse_bound"
  by (simp add: assms inverse_basis_matrix_entry_eq_lagrange_coeff
      lagrange_basis_poly_coeff_le_power_basis_inverse_bound)

end

end
