# Gelfond–Schneider in Isabelle/HOL

This entry proves the Gelfond–Schneider theorem for every logarithm branch.
The public theorem `gelfond_schneider` is in
[`Gelfond_Schneider.thy`](Gelfond_Schneider.thy). The same theory derives the
principal complex-power and positive real-power corollaries.

The proof is independent of the abandoned Baker two-logarithm development.
[`ROOT`](ROOT) selects the public theory and all its transitive imports in the
`Gelfond_Schneider_Standalone` session, with `quick_and_dirty = false`.

## Proof architecture

1. **Counterexample and auxiliary function.**
   [`Log_Values.thy`](Log_Values.thy) defines the branch-explicit `log_values`
   and `power_values` interfaces using `Complex_Transcendental`.
   [`GS_Setup.thy`](GS_Setup.thy) turns an
   algebraic counterexample into `gelfond_schneider_data`.
   The `Algebraic`, `Auxiliary`, `Order`, `System`, `Vanishing`, `Matrix`, and
   `Scaled_Matrix` theories construct the exponential sum, prove its
   non-vanishing and derivative identities, and encode the required vanishing
   conditions as an underdetermined matrix kernel. `Order` uses Isabelle's
   `zorder` and `zor_poly` machinery.
2. **Finite normal field and power basis.**
   [`Common_Field.thy`](Common_Field.thy)
   and
   [`Galois_Root_Bounds.thy`](Galois_Root_Bounds.thy)
   place the algebraic data in one finite normal extension
   `K = ℚ(η)`, with algebraic-integer generator `η`, degree `D`, rational
   power-basis coordinates, and an indexed family of automorphisms.
   `Power_Basis`, `Power_Basis_Recovery`, and `Power_Basis_Inverse_Bounds`
   establish independence, coordinate recovery through the inverse
   Vandermonde matrix, and quantitative inverse bounds. `House` and
   `Power_Basis_Field_Norm` control conjugates and the Galois norm.
3. **Bounded integral kernel.**
   [`Power_Basis_Norm_Target.thy`](Power_Basis_Norm_Target.thy)
   clears rational multiplication coordinates of the actual row-scaled
   matrix. A positive integer `T` is chosen from the fixed field data
   *before* the grid parameter `q`; a power `T^N` clears all relevant
   coordinates. The resulting integer matrix has a nonzero bounded kernel
   vector, which gives algebraic-integer coefficients for the auxiliary
   function. An integral basis of the full ring of integers is unnecessary
   for this route: rational power-basis coordinates plus the controlled
   denominator suffice.
4. **Norm contradiction and public theorem.**
   The same `Power_Basis_Norm_Target` theory bounds the distinguished
   nonzero algebraic integer `ρ` at the identity embedding and at its
   conjugates. Its norm is a nonzero rational algebraic integer, hence its
   absolute value is at least one; the analytic and house estimates force
   the opposite inequality for a suitable `q`. The locale
   `gelfond_schneider_power_basis_scaled_norm_verified` proves this
   contradiction.
   [`Power_Basis_Norm_Direct.thy`](Power_Basis_Norm_Direct.thy)
   chooses the global parameters in the required order and exports
   `no_gelfond_schneider_data_scaled`.
   [`Gelfond_Schneider.thy`](Gelfond_Schneider.thy) applies that result to
   discharge the counterexample and state the public theorem.

`Direct`, `Arithmetic`, `Scaled_Bounded`, `Rho_Bounds`, and
`Statement_Shell` supply the matrix construction and estimates used by the
final contradiction. Earlier conditional target locales and their bridge
theories were removed after the final proof was connected directly to the
scaled-denominator contradiction.

## Reusable library sessions

- [`Bounded_Integer_Kernels`](../Integer_Kernels/README.md) supplies the
  bounded nonzero integer-matrix kernel theorem.
- [`Finite_Embedding_Bounds`](../Finite_Embedding_Bounds/README.md) supplies
  finite-family house bounds, coordinate recovery, and lifted kernel bounds.

Both are separate sessions imported by the strict Gelfond–Schneider session.

## Build

With Isabelle2026-RC3 and a matching AFP development checkout, from the
`Auto-Proofs` directory:

```sh
/Applications/Isabelle2026-RC3.app/bin/isabelle build \
  -d Integer_Kernels \
  -d Finite_Embedding_Bounds \
  -d Gelfond_Schneider \
  -d /path/to/afp-devel/thys \
  -o document=false Gelfond_Schneider_Standalone
```

The development imports the `HOL-New_Algebra` session bundled with RC3.
The strict session passed a batch build on 2026-10-06 using AFP development
revision `153c5fc`. The older local AFP release checkout does not build with
RC3.

The local `Mathlib-GelfondSchneider`, `Mathlib-Numbertheory`, and
`Transcendental` directories contain ignored Lean reference copies; they
are not build dependencies. Their split proof suggested parts of the
auxiliary-function and number-field architecture, while the Isabelle proof
uses the power-basis and controlled-denominator route described above.
