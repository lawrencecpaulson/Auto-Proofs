(*  Title:      Gelfond_Schneider/Power_Basis_Recovery.thy
    Author:     OpenAI Codex

Lagrange-interpolation recovery for the indexed Galois power basis.  This
provides the qualitative biorthogonality data needed by the finite-embedding
contradiction layers without yet addressing the quantitative inverse-matrix
bounds.
*)

theory Power_Basis_Recovery
  imports
    Power_Basis
    "Finite_Embedding_Bounds.Finite_Embedding_House"
begin

context finite_galois_power_basis
begin

definition E :: "(complex \<Rightarrow> complex) set"
  where "E = emb ` {0..<D}"

sublocale EH: finite_embedding_house E
proof
  show "finite E"
    unfolding E_def by simp
qed

lemma emb_bij_E: "bij_betw emb {0..<D} E"
  unfolding E_def using ebij
  by (auto simp: bij_betw_def)

definition lagrange_denom :: "nat \<Rightarrow> complex"
  where "lagrange_denom i = (\<Prod>m\<in>{0..<D} - {i}. emb i eta - emb m eta)"

definition lagrange_basis_poly :: "nat \<Rightarrow> complex poly"
  where "lagrange_basis_poly i \<equiv>
    Polynomial.smult (inverse (lagrange_denom i)) (\<Prod>m\<in>{0..<D} - {i}. [:- emb m eta, 1:])"

lemma lagrange_denom_nonzero:
  assumes "i < D"
  shows "lagrange_denom i \<noteq> 0"
proof -
  have inj: "inj_on (\<lambda>i. emb i eta) {0..<D}"
    by (rule indexed_images_inj)
  have nz: "\<And>m. m \<in> {0..<D} - {i} \<Longrightarrow> emb i eta - emb m eta \<noteq> 0"
    using assms indexed_images_inj by (auto simp: inj_on_def)
  have "(\<Prod>m\<in>S. emb i eta - emb m eta) \<noteq> 0" if "finite S" "S \<subseteq> {0..<D} - {i}" for S
    using that by (induction; use nz in fastforce)
  then show ?thesis
    unfolding lagrange_denom_def
    by (meson Diff_subset set_eq_subset subset_eq_atLeast0_lessThan_finite)
qed

lemma lagrange_basis_poly_eval:
  assumes "i < D" "j < D"
  shows "poly (lagrange_basis_poly i) (emb j eta) = (if i = j then 1 else 0)"
proof (cases "i = j")
  case True
  then show ?thesis
    using lagrange_denom_nonzero[OF \<open>i < D\<close>] 
    by (simp add: lagrange_denom_def lagrange_basis_poly_def poly_prod)
next
  case False
  with assms show ?thesis
    by (auto simp: lagrange_basis_poly_def poly_prod prod.remove)
qed

lemma lagrange_basis_poly_degree:
  assumes ilt: "i < D"
  shows "Polynomial.degree (lagrange_basis_poly i) \<le> D - 1"
proof -
  have prod_deg: "Polynomial.degree (\<Prod>m\<in>{0..<D} - {i}. [:- emb m eta, 1:]) = card ({0..<D} - {i})"
    by (simp add: degree_prod_eq_sum_degree)
  then show ?thesis
    unfolding lagrange_basis_poly_def
    using degree_smult_le assms by auto
qed

definition lagrange_interpolate :: "complex poly \<Rightarrow> complex poly"
  where "lagrange_interpolate p \<equiv>
    (\<Sum>i<D. Polynomial.smult (poly p (emb i eta)) (lagrange_basis_poly i))"

lemma lagrange_interpolate_eval:
  assumes jlt: "j < D"
  shows "poly (lagrange_interpolate p) (emb j eta) = poly p (emb j eta)"
proof -
  have "poly (lagrange_interpolate p) (emb j eta) =
      (\<Sum>i<D. poly p (emb i eta) * poly (lagrange_basis_poly i) (emb j eta))"
    unfolding lagrange_interpolate_def
    by (simp add: poly_sum)
  also have "\<dots> = (\<Sum>i<D. poly p (emb i eta) * (if i = j then 1 else 0))"
    using jlt by (intro sum.cong[OF refl]) (simp add: lagrange_basis_poly_eval)
  also have "\<dots> = poly p (emb j eta)"
    using assms by (simp add: if_distrib cong: if_cong)
  finally show ?thesis .
qed

lemma lagrange_interpolate_degree: "Polynomial.degree (lagrange_interpolate p) \<le> D - 1"
  unfolding lagrange_interpolate_def
proof (rule degree_sum_le)
  fix i
  assume "i \<in> {..<D}"
  then show "Polynomial.degree (Polynomial.smult (poly p (emb i eta)) (lagrange_basis_poly i)) \<le> D - 1"
    using lagrange_basis_poly_degree by force
qed auto

lemma lagrange_interpolate_eq:
  assumes pdeg: "Polynomial.degree p < D"
  shows "lagrange_interpolate p = p"
proof -
  let ?A = "(\<lambda>i. emb i eta) ` {0..<D}"
  have cardA: "card ?A = D"
    using indexed_images_inj by (simp add: card_image)
  have eval_eq: "\<And>x. x \<in> ?A \<Longrightarrow> poly (lagrange_interpolate p) x = poly p x"
    using lagrange_interpolate_eval by force
  have ideg: "Polynomial.degree (lagrange_interpolate p) < D"
    using assms interval_class.less_eq_dec_imp_less lagrange_interpolate_degree by blast
  show ?thesis
    by (rule poly_eqI_degree[where A = ?A]) (use eval_eq pdeg ideg cardA in auto)
qed

definition repr_coeff :: "nat \<Rightarrow> (complex \<Rightarrow> complex) \<Rightarrow> complex"
  where "repr_coeff k e \<equiv>
    (if e \<in> E then Polynomial.coeff (lagrange_basis_poly (inv_into {0..<D} emb e)) k else 0)"

lemma repr_coeff_emb [simp]:
  assumes ilt: "i < D"
  shows "repr_coeff k (emb i) = Polynomial.coeff (lagrange_basis_poly i) k"
proof -
  have inj: "inj_on emb {0..<D}"
    using ebij by (auto simp: bij_betw_def inj_on_def)
  show ?thesis
    unfolding repr_coeff_def E_def
    using ilt inj by simp
qed

sublocale REC: finite_embedding_indexed_recovery E D emb basis repr_coeff
proof
  show "bij_betw emb {0..<D} E"
    by (rule emb_bij_E)
next
  fix k j
  assume "k < D"
  assume "j < D"
  let ?m = "Polynomial.monom (1 :: complex) j"
  have step1: "(\<Sum>i<D. repr_coeff k (emb i) * (basis j (emb i))) =
      (\<Sum>i<D. Polynomial.coeff (Polynomial.smult (poly ?m (emb i eta)) (lagrange_basis_poly i)) k)"
    by (auto simp: basis_def poly_monom intro: sum.cong)
  have step2: "Polynomial.coeff (lagrange_interpolate ?m) k =
      (\<Sum>i<D. Polynomial.coeff
        (Polynomial.smult (poly ?m (emb i eta)) (lagrange_basis_poly i)) k)"
    unfolding lagrange_interpolate_def
    by (subst Polynomial.coeff_sum) simp
  have interp_monom: "lagrange_interpolate ?m = ?m"
    by (simp add: degree_monom_eq \<open>j<D\<close> lagrange_interpolate_eq)
  have step3: "Polynomial.coeff (lagrange_interpolate ?m) k = Polynomial.coeff ?m k"
    using interp_monom by simp
  have "(\<Sum>i<D. repr_coeff k (emb i) * basis j (emb i)) = Polynomial.coeff ?m k"
    using step1 step2 step3 by simp
  then show "(\<Sum>i<D. repr_coeff k (emb i) * basis j (emb i)) = (if j = k then 1 else 0)"
    by simp
qed

end


section \<open>Inverse basis matrix\<close>

context finite_galois_power_basis
begin

lemma inverse_basis_matrix_entry_eq_lagrange_coeff:
  assumes ilt: "i < D"
  shows "REC.inverse_basis_matrix_entry k i = Polynomial.coeff (lagrange_basis_poly i) k"
  using repr_coeff_emb[OF ilt, of k] by (simp add: REC.inverse_basis_matrix_entry_def)



lemma inverse_basis_matrix_entry_bound_of_lagrange_coeff_bound:
  assumes coeff_bnd: "\<And>i k. i < D \<Longrightarrow> k < D \<Longrightarrow> cmod (Polynomial.coeff (lagrange_basis_poly i) k) \<le> R"
  assumes ilt: "i < D"
    and klt: "k < D"
  shows "cmod (REC.inverse_basis_matrix_entry k i) \<le> R"
  using coeff_bnd[OF ilt klt] inverse_basis_matrix_entry_eq_lagrange_coeff[OF ilt, of k]
  by simp



end

end
