theory Roth_Wronskian
  imports
    "Polynomial_Wronskians.Polynomial_Wronskians"
    Univariate_Index
    Hasse_Support
begin

section \<open>Univariate Hasse derivatives and Wronskians\<close>

lemma roth_mchoose_single [simp]:
  "roth_mchoose (Poly_Mapping.single v n) (Poly_Mapping.single v k) =
    (n choose k)"
  by (simp add: roth_mchoose_on_set[of "{v}"])

lemma roth_univariate_hasse_coeff:
  fixes p :: "rat poly"
  shows "MPoly_Type.coeff
      (roth_hasse (Poly_Mapping.single v k) (poly_to_mpoly v p))
      (Poly_Mapping.single v n) =
    Polynomial.coeff p (n + k) * of_nat ((n + k) choose k)"
  by (simp add: roth_hasse_coeff_exact
    Poly_Mapping.single_add[symmetric] coeff_poly_to_mpoly)

lemma roth_hasse_vars_subset:
  fixes P :: "rat mpoly"
  shows "vars (roth_hasse J P) \<subseteq> vars P"
  by (auto simp: vars_def in_keys_iff coeff_def[symmetric] roth_hasse_coeff_exact lookup_add)

lemma roth_univariate_hasse_one:
  fixes p :: "rat poly"
  shows "roth_hasse (Poly_Mapping.single v 1) (poly_to_mpoly v p) = poly_to_mpoly v (pderiv p)"
proof -
  have vl: "vars (roth_hasse (Poly_Mapping.single v 1) (poly_to_mpoly v p)) \<subseteq> {v}"
    using roth_hasse_vars_subset roth_vars_poly_to_mpoly by blast
  have peq: "mpoly_to_poly v (roth_hasse (Poly_Mapping.single v 1) (poly_to_mpoly v p)) =
    pderiv p"
    by (intro poly_eqI) (simp add: roth_univariate_hasse_coeff coeff_pderiv)
  show ?thesis using peq mpoly_to_poly_inverse[OF vl] by simp
qed

lemma roth_univariate_hasse_as_hderiv:
  "mpoly_to_poly 0 (roth_hasse (Poly_Mapping.single 0 k)
    (poly_to_mpoly 0 p)) = hderiv k p"
  by (rule poly_eqI) (simp add: roth_univariate_hasse_coeff)

end
