# Bounded Integer Kernels

`Integer_Kernel_Bounds.thy` provides bounds for a nonzero integer
kernel vector of an underdetermined integer matrix (used for Gelfond–Schneider and Roth):

- a general bound using `det_bound_hadamard`;
- a sharp pigeonhole form of Siegel's lemma: any natural number `C` satisfying
  `(q B C + 1)^p < (C + 1)^q` bounds a nonzero kernel vector for a
  `p × q` matrix whose entries have absolute value at most `B`;
- the explicit exponent bound `(q * max 1 Bnd) ^ (p / (q - p))` for
  `0 < p < q`, matching the exponent in Mathlib's
  `NumberTheory/SiegelsLemma.lean`;
- the earlier symmetric counting condition and linear bound
  `2 * int q * max 1 Bnd` when `2 * p ≤ q`, retained for existing callers.

The proof uses existing AFP matrix and mixed-integer-solution results. The
sharper counting argument translates each output row by its negative part,
reducing its range to at most `q B C + 1` possible values.

To check this session in the current workspace:

```sh
/Applications/Isabelle2026.app/bin/isabelle build \
  -D AFP_Staging/Bounded_Integer_Kernels \
  -d /path/to/afp/devel/thys \
  -o document=pdf Bounded_Integer_Kernels
```
