(*  Title:      Baker/Gelfond_Schneider_Power_Basis_Recovery.thy
    Author:     OpenAI Codex

Lagrange-interpolation recovery for the indexed Galois power basis.  This
provides the qualitative biorthogonality data needed by the finite-embedding
contradiction layers without yet addressing the quantitative inverse-matrix
bounds.
*)

theory Gelfond_Schneider_Power_Basis_Recovery
  imports
    Gelfond_Schneider_Power_Basis
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

lemma Dpos: "D > 0"
proof -
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  show ?thesis
    unfolding D_def by (rule Subfield.ext_degree_pos[OF sfQ algQ])
qed

lemma emb_bij_E: "bij_betw emb {0..<D} E"
  unfolding E_def using ebij
  by (auto simp: bij_betw_def)

definition lagrange_denom :: "nat \<Rightarrow> complex"
  where "lagrange_denom i = (\<Prod>m\<in>{0..<D} - {i}. emb i eta - emb m eta)"

definition lagrange_basis_poly :: "nat \<Rightarrow> complex poly"
  where "lagrange_basis_poly i =
    Polynomial.smult (inverse (lagrange_denom i))
      (\<Prod>m\<in>{0..<D} - {i}. [:- emb m eta, 1:])"

lemma lagrange_denom_nonzero:
  assumes ilt: "i < D"
  shows "lagrange_denom i \<noteq> 0"
proof -
  have inj: "inj_on (\<lambda>i. emb i eta) {0..<D}"
    by (rule indexed_images_inj)
  have nz: "\<And>m. m \<in> {0..<D} - {i} \<Longrightarrow> emb i eta - emb m eta \<noteq> 0"
  proof -
    fix m
    assume m: "m \<in> {0..<D} - {i}"
    have mit: "m < D"
      using m by simp
    have "emb i eta \<noteq> emb m eta"
      using inj ilt mit m by (auto simp: inj_on_def)
    then show "emb i eta - emb m eta \<noteq> 0"
      by simp
  qed
  have "finite ({0..<D} - {i})" by simp
  (*BETTER TO DO THE INDUCTION ON FINITE S \<le> {0..<D} - {i}*)
  then have "(\<Prod>m\<in>{0..<D} - {i}. emb i eta - emb m eta) \<noteq> 0"
  proof (induction "{0..<D} - {i}" rule: finite_induct)
    case empty
    then show ?case
      by (metis emptyE prod_nonzeroI)
  next
    case (insert m S)
    then have m_mem: "m \<in> {0..<D} - {i}" by blast
    have "emb i eta - emb m eta \<noteq> 0"
      by (rule nz[OF m_mem])
    moreover have "(\<Prod>x\<in>S. emb i eta - emb x eta) \<noteq> 0"
      using insert
      by (metis (no_types, lifting) insert_iff nz prod_nonzeroI)
    ultimately show ?case
      using insert.hyps nz by auto
  qed
  then show ?thesis
    unfolding lagrange_denom_def .
qed

lemma lagrange_basis_poly_eval:
  assumes ilt: "i < D"
    and jlt: "j < D"
  shows "poly (lagrange_basis_poly i) (emb j eta) = (if i = j then 1 else 0)"
proof (cases "i = j")
  case True
  have "poly (lagrange_basis_poly i) (emb j eta) =
      inverse (lagrange_denom i) *
        poly (\<Prod>m\<in>{0..<D} - {i}. [:- emb m eta, 1:]) (emb i eta)"
    using True by (simp add: lagrange_basis_poly_def)
  also have "\<dots> = inverse (lagrange_denom i) * lagrange_denom i"
    unfolding lagrange_denom_def by (simp add: poly_prod True)
  also have "\<dots> = 1"
    using lagrange_denom_nonzero[OF ilt] by simp
  finally show ?thesis
    using True by simp
next
  case False
  have jmem: "j \<in> {0..<D} - {i}"
    using ilt jlt False by auto
  have "poly (lagrange_basis_poly i) (emb j eta) =
      inverse (lagrange_denom i) *
        poly (\<Prod>m\<in>{0..<D} - {i}. [:- emb m eta, 1:]) (emb j eta)"
    by (simp add: lagrange_basis_poly_def)
  also have "\<dots> = inverse (lagrange_denom i) *
      (\<Prod>m\<in>{0..<D} - {i}. poly [:- emb m eta, 1:] (emb j eta))"
    by (simp add: poly_prod)
  also have "\<dots> = inverse (lagrange_denom i) *
      (poly [:- emb j eta, 1:] (emb j eta) *
        (\<Prod>m\<in>({0..<D} - {i}) - {j}. poly [:- emb m eta, 1:] (emb j eta)))"
    using jmem by (simp add: prod.remove)
  also have "\<dots> = 0"
    by simp
  finally show ?thesis
    using False by simp
qed

lemma lagrange_basis_poly_degree:
  assumes ilt: "i < D"
  shows "Polynomial.degree (lagrange_basis_poly i) \<le> D - 1"
proof -
  have prod_deg: "Polynomial.degree (\<Prod>m\<in>{0..<D} - {i}. [:- emb m eta, 1:]) = card ({0..<D} - {i})"
  proof -
    have fin: "finite ({0..<D} - {i})"
      by simp
    have nz: "\<And>m. m \<in> {0..<D} - {i} \<Longrightarrow> [:- emb m eta, 1:] \<noteq> (0 :: complex poly)"
      by simp
    have "Polynomial.degree (\<Prod>m\<in>{0..<D} - {i}. [:- emb m eta, 1:]) =
        (\<Sum>m\<in>{0..<D} - {i}. Polynomial.degree [:- emb m eta, 1:])"
      by (rule degree_prod_eq_sum_degree) (use nz in auto)
    also have "\<dots> = card ({0..<D} - {i})"
      by simp
    finally show ?thesis .
  qed
  have "Polynomial.degree (lagrange_basis_poly i) \<le>
      Polynomial.degree (\<Prod>m\<in>{0..<D} - {i}. [:- emb m eta, 1:])"
    unfolding lagrange_basis_poly_def
    by (rule degree_smult_le)
  also have "\<dots> = card ({0..<D} - {i})"
    by (rule prod_deg)
  also have "\<dots> = D - 1"
    using ilt by simp
  finally show ?thesis .
qed

definition lagrange_interpolate :: "complex poly \<Rightarrow> complex poly"
  where "lagrange_interpolate p =
    (\<Sum>i<D. Polynomial.smult (poly p (emb i eta)) (lagrange_basis_poly i))"

lemma lagrange_interpolate_eval:
  assumes jlt: "j < D"
  shows "poly (lagrange_interpolate p) (emb j eta) = poly p (emb j eta)"
proof -
  have step1:
    "poly (lagrange_interpolate p) (emb j eta) =
      (\<Sum>i<D. poly p (emb i eta) * poly (lagrange_basis_poly i) (emb j eta))"
    unfolding lagrange_interpolate_def
    by (simp add: poly_sum)
  have step2:
    "(\<Sum>i<D. poly p (emb i eta) * poly (lagrange_basis_poly i) (emb j eta)) =
      (\<Sum>i<D. poly p (emb i eta) * (if i = j then 1 else 0))"
    using jlt by (intro sum.cong[OF refl]) (simp add: lagrange_basis_poly_eval)
  have step3:
    "(\<Sum>i<D. poly p (emb i eta) * (if i = j then 1 else 0)) = poly p (emb j eta)"
  proof -
    have "(\<Sum>i<D. poly p (emb i eta) * (if i = j then 1 else 0)) =
        (\<Sum>i<D. if i = j then poly p (emb i eta) else 0)"
      by (intro sum.cong[OF refl]) simp
    also have "\<dots> = poly p (emb j eta)"
      using jlt by simp
    finally show ?thesis .
  qed


  show ?thesis
    using step1 step2 step3 by simp
qed

lemma lagrange_interpolate_degree:
  shows "Polynomial.degree (lagrange_interpolate p) \<le> D - 1"
proof -
  have term_deg:
    "\<And>i. i < D \<Longrightarrow>
      Polynomial.degree (Polynomial.smult (poly p (emb i eta)) (lagrange_basis_poly i)) \<le> D - 1"
  proof -
    fix i
    assume ilt: "i < D"
    have "Polynomial.degree (Polynomial.smult (poly p (emb i eta)) (lagrange_basis_poly i)) \<le>
        Polynomial.degree (lagrange_basis_poly i)"
      by (rule degree_smult_le)
    also have "\<dots> \<le> D - 1"
      by (rule lagrange_basis_poly_degree[OF ilt])
    finally show "Polynomial.degree (Polynomial.smult (poly p (emb i eta)) (lagrange_basis_poly i)) \<le> D - 1" .
  qed
  have deg_sum:
    "Polynomial.degree (\<Sum>i<D. Polynomial.smult (poly p (emb i eta)) (lagrange_basis_poly i)) \<le> D - 1"
  proof (rule degree_sum_le)
    show "finite {..<D}"
      by simp
  next
    fix i
    assume ilt: "i \<in> {..<D}"
    then show "Polynomial.degree (Polynomial.smult (poly p (emb i eta)) (lagrange_basis_poly i)) \<le> D - 1"
      using term_deg by simp
  qed

  show ?thesis
    unfolding lagrange_interpolate_def
    by (rule deg_sum)

qed

lemma lagrange_interpolate_eq:
  assumes pdeg: "Polynomial.degree p < D"
  shows "lagrange_interpolate p = p"
proof -
  let ?A = "(\<lambda>i. emb i eta) ` {0..<D}"
  have inj: "inj_on (\<lambda>i. emb i eta) {0..<D}"
    by (rule indexed_images_inj)
  have cardA: "card ?A = D"
    using inj by (simp add: card_image)
  have eval_eq: "\<And>x. x \<in> ?A \<Longrightarrow> poly (lagrange_interpolate p) x = poly p x"
  proof -
    fix x
    assume xA: "x \<in> ?A"
    then obtain j where jlt: "j < D" and x: "x = emb j eta"
      by auto
    show "poly (lagrange_interpolate p) x = poly p x"
      unfolding x by (rule lagrange_interpolate_eval[OF jlt])
  qed
  have ideg: "Polynomial.degree (lagrange_interpolate p) < D"
  proof -
    have "Polynomial.degree (lagrange_interpolate p) \<le> D - 1"
      by (rule lagrange_interpolate_degree)
    with Dpos show ?thesis
      by simp
  qed
  show ?thesis
    by (rule poly_eqI_degree[where A = ?A]) (use eval_eq pdeg ideg cardA in auto)
qed

definition repr_coeff :: "nat \<Rightarrow> (complex \<Rightarrow> complex) \<Rightarrow> complex"
  where "repr_coeff k e =
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
  assume klt: "k < D"
  assume jlt: "j < D"
  let ?m = "Polynomial.monom (1 :: complex) j"
  have step1: "(\<Sum>i<D. repr_coeff k (emb i) * (basis j (emb i))) =
      (\<Sum>i<D. Polynomial.coeff
        (Polynomial.smult (poly ?m (emb i eta)) (lagrange_basis_poly i)) k)"
  proof (rule sum.cong[OF refl])
    fix i
    assume ilt: "i \<in> {..<D}"
    have repr: "repr_coeff k (emb i) = Polynomial.coeff (lagrange_basis_poly i) k"
      using ilt by simp
    have bas: "basis j (emb i) = poly ?m (emb i eta)"
      using jlt by (simp add: basis_def poly_monom)
    have coeff:
        "Polynomial.coeff (Polynomial.smult (poly ?m (emb i eta)) (lagrange_basis_poly i)) k =
          poly ?m (emb i eta) * Polynomial.coeff (lagrange_basis_poly i) k"
      by (rule Polynomial.coeff_smult)
    show "repr_coeff k (emb i) * basis j (emb i) =
        Polynomial.coeff (Polynomial.smult (poly ?m (emb i eta)) (lagrange_basis_poly i)) k"
      using repr bas coeff by (simp add: mult_ac)
  qed



  have step2: "Polynomial.coeff (lagrange_interpolate ?m) k =
      (\<Sum>i<D. Polynomial.coeff
        (Polynomial.smult (poly ?m (emb i eta)) (lagrange_basis_poly i)) k)"
    unfolding lagrange_interpolate_def
    by (subst Polynomial.coeff_sum) simp



  have interp_monom: "lagrange_interpolate ?m = ?m"
  proof (rule lagrange_interpolate_eq)
    show "Polynomial.degree ?m < D"
      using jlt by (simp add: degree_monom_eq)
  qed

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
