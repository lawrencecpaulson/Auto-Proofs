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
/Applications/Isabelle2026-RC4.app/Contents/Resources/bin/isabelle build \
  -D Gelfond_Schneider \
  -d /path/to/afp-devel/thys \
  -o document=false Bounded_Integer_Kernels
```
