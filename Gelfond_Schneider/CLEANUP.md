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
- `Power_Basis_Norm_Target.thy` now defines the scaled auxiliary value,
  its integer multiplier, and the witness growth prefactor once. Three
  pairs of house and point bound lemmas share their common assumptions
  through local contexts. Together these changes remove 75 theory lines.
- `Power_Basis_Norm_Target.thy` derives the exponential-denominator
  bounded-kernel theorem from the given-denominator version and the
  product-denominator existence result. This removes 24 theory lines
  while making the dependency between the results explicit.

Remaining candidates identified on 2026-10-26:

- `Power_Basis_Norm_Target.thy`, the two
  `gs_rho_upper_from_concrete_witness` lemmas repeat their witness premises;
  their denominator bounds differ. Grouping the common premises would
  save few lines and may obscure the two quantitative hypotheses; keep
  them explicit unless a broader witness interface is needed.
- `Scaled_Bounded.thy` and `GS_Direct.thy` repeatedly state the
  `basis_int`, `basis_indep`, `mult_repr`, and `C_bnd` conditions. Consider a
  shared locale if further work touches several of those interfaces; a
  local proof extraction is likely simpler for isolated duplicates.
