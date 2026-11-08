# Resultant multiplicity: paper-to-Isabelle audit

Date: 8 November 2026. Source: Appendix A of `no-siegel.tex`.

## Target

For a bivariate irreducible `F :: complex mpoly` of positive first-variable
degree, write `r = first_resultant_poly F` and `f_a = specialize_second a F`.
The outstanding theorem is `r != 0` and, for every `a,x`,

    Polynomial.order x f_a <= 1 + Polynomial.order a r.

The preceding bivariate theory already proves `f_a != 0` for every `a`.

## Checked components

- `first_resultant` is the AFP resultant of the polynomial in variable 0
  and its formal derivative; its variables are contained in `{1}`.
- `first_resultant_poly_degree_le` proves `degree r <= 2*d*d'`, with
  `d = MPoly_Type.degree F 0` and `d' = MPoly_Type.degree F 1`.
  The proof expands AFP's Sylvester determinant and bounds its entries.
- `first_resultant_bad_parameters_card` counts its zeros, conditional on
  `r != 0`.
- `first_resultant_specialize` identifies evaluation of `r` with the
  ordinary resultant of the specialised polynomial and derivative when
  the first-variable degree is preserved.
- `first_resultant_double_root` gives the degree-preserving double-root
  case. `sylvester_det_degree_drop` shows that the fixed-size Sylvester
  matrix has a zero column when specialization loses first-variable degree.
  Hence `first_resultant_double_root_any` removes the degree-preservation
  hypothesis and `first_resultant_degree_drop` covers the other exceptional
  case.
- `first_resultant_specialize_matrix` proves the fixed-size Sylvester
  determinant formula with generic dimensions `d` and `d-1`, including
  specialisations where the degree drops.
- `first_resultant_degree_preserved_somewhere` provides a parameter at which
  the first-variable degree is retained.
- `first_resultant_nonzero_of_coprime_specialization` reduces nonvanishing to
  finding a degree-preserving squarefree fibre. In degree one,
  `first_resultant_nonzero_degree_one` proves nonvanishing and
  `first_resultant_multiplicity_degree_one` proves the target order bound.
  `first_resultant_nonroot_fibre_simple` shows that nonzeros of the resultant
  are full-degree squarefree fibres. The target multiplicity inequality also
  holds for first-variable degree at most two, conditional on nonvanishing.
- `exceptional_first_fibre` names degree-losing or multiple-root fibres.
  For irreducible `F`, each is in the zero set of `r`; their number is at
  most `2*d*d'` conditional on `r != 0`.
- `root_power_dvd_sylvester_image` proves the appendix's polynomial
  divisibility claim for every specialized Sylvester image.
- `irreducible_resultant_pderiv_nonzero` proves the UFD argument over
  `complex poly poly`. `Bivariate_Polynomial.thy` now has conversions
  `bivariate_as_poly_poly` and `poly_poly_as_bivariate`, proves reconstruction
  of bivariate polynomials, injectivity, nonzero reflection, preservation
  of first-variable degree, and multiplicativity. Irreducibility, derivative,
  and resultant transport remain open.
- `determinant_zero_rows_order_set` proves that if `m` rows of a square
  polynomial matrix vanish at `a`, then its nonzero determinant has order
  at least `m` at `a`.

All these components have checked Isabelle proofs, without admitted steps.
The full Isabelle2026 `No_Siegel` session build passed on 8 November 2026 after the resultant and conversion edits.

## Remaining proof map

1. **Nonzero resultant in general.** Prove that irreducibility of `F` of
   positive variable-0 degree makes `F` coprime to its variable-0 derivative
   over `complex(z')`, or prove the equivalent existence of a
   degree-preserving squarefree fibre. AFP's
   `resultant_zero_imp_common_factor` handles polynomials over the UFD
   `complex poly`; the checked lemma above now completes the argument
   *after* translating the bivariate polynomial to `complex poly poly`.
   The new conversion reconstructs bivariate polynomials, preserves
   first-variable degree, and preserves multiplication. What remains is
   ring-compatible transport of irreducibility, the derivative, and the
   resultant. The coefficient ring
   `complex mpoly` has no UFD instance here.
2. **Rank defect.** If `mu = Polynomial.order x f_a`, show that the image
   of the specialised Sylvester multiplication map consists of polynomials
   divisible by `(z-x)^(mu-1)`; this divisibility is now proved by
   `root_power_dvd_sylvester_image`. It remains to connect the fixed-size
   Sylvester matrix to the map and prove that the codimension in polynomials
   of degree less than `2*d-1` is `mu-1`, yielding rank at most `2*d-mu`.
3. **Row transformation.** Use AFP Gauss-Jordan or a basis extension to
   obtain an invertible constant matrix whose product with the specialised
   Sylvester matrix has at least `mu-1` zero rows. Lift the matrix to
   constant polynomial entries and apply
   `determinant_zero_rows_order_set`. Its determinant identity must carry
   the result back to `first_resultant_poly F`.

## Fidelity and source errors

The checked degree estimate and zero-row divisibility follow the appendix's
Sylvester determinant proof. The paper's rank and basis-extension steps
remain explicit proof obligations; no replacement claim has been assumed.
No error has been identified in Appendix A. Degree loss on specialisation
is a formalisation pitfall, not a paper error: the appendix correctly keeps
its matrix at the generic size.
