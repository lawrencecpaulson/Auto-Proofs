(*  Title:      Baker/Gelfond_Schneider_Power_Basis_Inverse.thy
    Author:     OpenAI Codex

Small reductions for the inverse Vandermonde matrix in the power-basis route.
These lemmas turn bounds on Lagrange interpolation coefficients into the raw
inverse-basis-entry bounds required downstream.
*)

theory Gelfond_Schneider_Power_Basis_Inverse
  imports Gelfond_Schneider_Power_Basis_Recovery
begin

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
