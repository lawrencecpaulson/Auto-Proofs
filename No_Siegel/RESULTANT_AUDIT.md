# Resultant multiplicity: paper-to-Isabelle audit

Date: 8 November 2026. Source: Appendix A of `no-siegel.tex`.

## Target

For a bivariate irreducible `F :: complex mpoly` of positive first-variable
degree, write `r = first_resultant_poly F` and `f_a = specialize_second a F`.
Both nonvanishing `r != 0` and the following estimate for every `a,x`
are checked:

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
  For irreducible `F` of positive first-variable degree, each is in the
  zero set of `r`; their number is at most `2*d*d'`, without an extra
  nonvanishing hypothesis.
- `root_power_dvd_sylvester_image` proves the appendix's polynomial
  divisibility claim for every specialized Sylvester image.
- `irreducible_resultant_pderiv_nonzero` proves the UFD argument over
  `complex poly poly`. `Bivariate_Polynomial.thy` now proves that its
  conversions to and from this nested-polynomial representation preserve
  multiplication and units, recover bivariate polynomials, preserve
  first-variable degree, and transport irreducibility. The checked
  `first_resultant_poly_nested` identifies the two resultant definitions.
  Thus `first_resultant_nonzero_irreducible` proves general nonvanishing.
- `determinant_zero_rows_order_set` and its transpose form
  `determinant_zero_columns_order_set` give a lower bound on determinant
  order from rows or columns vanishing after specialisation.
- `first_resultant_multiplicity_irreducible` proves the full Appendix A
  inequality for arbitrary first-variable degree and arbitrary roots,
  including degree-dropping fibres. The older degree-at-most-two theorem
  remains as a useful conditional result; the zero-root theorem is now a
  corollary of the general theorem.
- `coeff_translate_below_order` and `coeff_pcompose_shift_zero` give the
  vanishing of translated coefficients. `taylor_column_change` is upper
  triangular with determinant `1`.
- `sylvester_descending_row_polynomial` identifies each Sylvester row with
  a monomial shift of the input polynomial or derivative.
  `specialized_sylvester_descending_row` carries this identity through
  fibre specialization. `taylor_product_entry` identifies the changed
  matrix entries with Taylor coefficients.
- `determinant_zero_columns_order_after_constant_change` lifts the Taylor
  matrix to constant polynomials and preserves determinant order. The final
  theorem applies it to the last `mu-1` columns.

All these components have checked Isabelle proofs, without admitted steps.
The full Isabelle2026 `No_Siegel` session build passed on 8 November 2026 after the resultant and conversion edits.

## Proof structure

The proof keeps the Sylvester matrix at its generic size `2*d-1`, even
when a fibre loses degree. For a root of multiplicity `mu`, its derivative
has order `mu-1`. The specialized Sylvester rows are monomial shifts of
the fibre polynomial and its derivative. After the Taylor column change,
the last `mu-1` columns vanish at the parameter. The column determinant
lemma therefore gives order at least `mu-1` for the resultant.

## Fidelity and source errors

The checked degree estimate and full multiplicity theorem follow the
appendix's Sylvester determinant argument. The Taylor column matrix makes
the paper's change of basis explicit. No error has been identified in
Appendix A. Degree loss on specialisation is a formalisation pitfall, not
a paper error: the appendix correctly keeps its matrix at the generic size.
