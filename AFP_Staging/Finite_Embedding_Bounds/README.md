# Finite Embedding Bounds

This standalone entry develops maximum-modulus bounds for finite families of
complex-valued maps, recovers coordinates through an indexed inverse basis
matrix, and lifts bounded integer kernels using integral structure constants.
The finite labels need not be embeddings of a particular number field; that
structure is supplied by an application. The session depends on the sibling
`Bounded_Integer_Kernels` entry.

## Main results

- `Finite_Embedding_House.thy` defines `ehouse` and proves its triangle,
  product, power, sum, and coordinate-recovery bounds.
- `Structure_Constant_Kernels.thy` lifts an integer kernel through an integral
  basis and provides determinant, linear, and Siegel-exponent bounds.
- `Embedding_Kernel_Bounds.thy` combines the lift with house estimates. For
  `0 < p < q`, basis rank `d > 0`, and structure constants bounded by `Bnd`,
  the integer coordinates satisfy the real bound
  `(q * d * max 1 Bnd) powr ((p * d) / (q * d - p * d))`; the house bound
  multiplies this by `d * K`, where `K` bounds the house of each basis element.
  A further theorem bounds the structure constants from the houses of the
  matrix entries and the coordinate-recovery data.
- `Gaussian_Integer_Example.thy` instantiates indexed recovery for the two
  conjugate images of the basis `1, i` and proves integer independence at the
  identity image.

The document explains the assumptions and cites the Mathlib developments that
motivated the abstraction. The entry is also used by the staged
Gelfond–Schneider development.

To check the session and PDF in the current workspace:

```sh
/Applications/Isabelle2026.app/bin/isabelle build \
  -d /Users/lawrpau/isabelle/afp/devel/thys \
  -d /Users/lawrpau/isabelle/Auto-Proofs/AFP_Staging/Bounded_Integer_Kernels \
  -D /Users/lawrpau/isabelle/Auto-Proofs/AFP_Staging/Finite_Embedding_Bounds \
  -o document=pdf Finite_Embedding_Bounds
```

The session, PDF, outline, browser presentation, and downstream
Gelfond–Schneider build passed with Isabelle2026 on 13 November 2026.
