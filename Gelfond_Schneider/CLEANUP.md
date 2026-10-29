# Proof cleanup

Review repeated assumptions, conclusions, formulas, and proofs together.
An exact line scan is only a first pass: the same mathematical data may
recur with renamed variables or a different quantitative bound. Prefer an
extraction when it gives that data a meaningful name.

## Completed

- `Power_Basis_Norm_Target.thy` uses
  `row_scaled_matrix_entries_from_coefficient_representation` for the
  common denominator-padding and row-scaling argument. Its exponential
  denominator result now follows from the given-denominator theorem.
- `Structure_Constant_Kernels.thy` introduces `bounded_basis_kernel`.
  `GS_Direct.thy` extends it with `bounded_integral_basis_kernel` and a
  generic lemma deriving coordinate integrality from an integral basis.
  Bounded-kernel results in `Embedding_Kernel_Bounds.thy`, `GS_Direct.thy`,
  `Scaled_Bounded.thy`, and `Power_Basis_Norm_Target.thy` now use these
  named witnesses. The quantitative bound remains an explicit parameter.
- `GS_Direct.thy` defines `gs_bounded_auxiliary_witness` for the minimum
  order and nonzero derivative. Both ordinary and row-scaled bounded
  constructions use it. `Scaled_Bounded.thy` defines
  `gs_integral_scaled_auxiliary_value` for the multiplier, scaled value,
  integrality, and nonvanishing facts in the house and upper bounds.
- `GS_System.thy` supplies common balance inequalities used throughout the
  matrix and power-basis arguments.
- `Power_Basis_Norm_Target.thy` defines the uniform product-denominator
  properties instead of repeating their long universal formulas. It also
  defines the scaled auxiliary value and growth prefactor used in its
  final estimates.
- `Power_Basis_Norm_Target.thy` now names the factor count of a system
  coefficient, the row denominator budget and its order-based bound, the
  integer-kernel witness size, and the power-basis witness coordinate
  relation. The house and point growth exponents and their combined norm
  base are named separately. The positive-order lemma now follows from
  the stronger order bound instead of repeating its proof.
- `Statement_Shell.thy` defines the norm growth exponent used by the
  upper bound and final growth contradiction. The analytic field-norm
  theorem keeps its exact arithmetic exponent visible.
- The affected theories use Isabelle's ceiling and absolute-value notation
  consistently. The remaining `abs` in a set image is a function value.
- Related bounds in `GS_Direct.thy`, `Scaled_Bounded.thy`, and
  `Power_Basis_Norm_Target.thy` share common hypotheses through local
  contexts. The Hadamard and linear house-lower-bound results use the same
  lower-bound lemma after producing their respective vectors.

The `Gelfond_Schneider` session built successfully after these edits.

## Remaining candidates

- The four initial bounded-kernel theorems in `GS_Direct.thy` and
  `Scaled_Bounded.thy` still repeat the `basis_int`, `basis_indep`,
  `mult_repr`, and `C_bnd` premises. A matrix-parameterized locale may
  improve these theorem statements. The later results already share
  these premises through their contexts.
- `GS_Arithmetic.thy` still writes the raw multiplier and scaled-value
  formulas in several interfaces. The downstream bounded results now use
  a predicate. A shared definition at the arithmetic level could remove
  the upstream copies, but would change several theorem interfaces.
- The ordinary and denominator-adjusted house and point growth proofs in
  `Power_Basis_Norm_Target.thy` have similar structure. Their named bases
  and exponents now make the common mathematics visible; their distinct
  estimates remain explicit.
- The field-construction rules in `Galois_Root_Bounds.thy` strengthen their
  conclusions stage by stage. `finite_normal_galois_power_basis` already
  names the final state; it is not clear that another locale would improve
  the intermediate rules.

Keep bounds explicit where their exact formula is the point of a theorem.
