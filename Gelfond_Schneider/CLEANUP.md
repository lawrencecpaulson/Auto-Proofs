# Proof cleanup candidates

When reviewing a theory, look for long repeated blocks of **formulas or
proofs**, including blocks separated by renamed variables or a different
bound. Compare theorem assumptions and conclusions as well as proof text.
An exact contiguous-line scan is a useful first pass, but semantic comparison
is needed before extracting a common lemma or locale. Prefer an extraction
when it gives a meaningful shared mathematical statement.

Completed extractions:

- `Power_Basis_Norm_Target.thy`, the proofs of
  `row_scaled_matrix_entries_from_product_denominator` and
  `row_scaled_matrix_entries_have_uniform_exponential_denominator`: roughly
  45 identical lines pad the coefficient denominator exponent and scale a
  matrix row. Both now use
  `row_scaled_matrix_entries_from_coefficient_representation`.
- `Scaled_Bounded.thy`, the Hadamard and linear versions of
  `gs_exists_row_scaled_bounded_nonzero_algebraic_int_house_lower_bound`:
  both now use `gs_scaled_auxiliary_value_house_lower_bound` after
  constructing their respective bounded kernel vectors. This removed
  34 lines overall.

Remaining candidates identified on 2026-10-26:

- `Power_Basis_Norm_Target.thy`, the exponential-denominator and
  given-denominator versions of the row-scaled bounded-kernel theorem:
  roughly 35 identical lines choose integer coordinates, assemble their
  matrix representation, and invoke the house-bounded kernel theorem.
  A result parameterized by the available denominator representation would
  isolate this common argument.
- `Scaled_Bounded.thy` and `GS_Direct.thy` repeatedly state the
  `basis_int`, `basis_indep`, `mult_repr`, and `C_bnd` conditions. Consider a
  shared locale if further work touches several of those interfaces; a
  local proof extraction is likely simpler for isolated duplicates.
