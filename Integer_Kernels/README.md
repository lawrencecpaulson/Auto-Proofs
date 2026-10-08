# Bounded Integer Kernels

`Integer_Kernel_Bounds.thy` provides two bounds for a nonzero integer
kernel vector of an underdetermined integer matrix (used for Gelfond–Schneider):

- a general bound using `det_bound_hadamard`;
- a linear bound `2 * int q * max 1 Bnd` when `0 < p` and `2 * p ≤ q`.

The bounds are weaker than the exponent bound in Mathlib's
`NumberTheory/SiegelsLemma.lean`. The present entry uses existing AFP
matrix and mixed-integer-solution results.

To check this session in the current workspace:

```sh
/Applications/Isabelle2025-2.app/bin/isabelle build \
  -D Integer_Kernels \
  -d /Users/lawrpau/isabelle/afp/release/thys \
  -o document=false Bounded_Integer_Kernels
```
