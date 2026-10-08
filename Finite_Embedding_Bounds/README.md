# Bounds for finite embedding families

This session contains valuable results used in the
Gelfond–Schneider development:

- `Structure_Constant_Kernels`: bounded kernel vectors obtained by lifting
  integer solutions through integral structure constants;
- `Finite_Embedding_House`: maximum modulus over a finite family, coordinate
  recovery, and inverse basis-matrix identities;
- `Embedding_Kernel_Bounds`: uniform house bounds for the lifted kernel
  vectors.

The session depends on `Bounded_Integer_Kernels`. Its embedding family is
abstract, so it does not assert the existence of an integral basis for every
number field. The corresponding Mathlib sources are
`NumberTheory/NumberField/House.lean` and `EquivReindex.lean`.

In this workspace, check it with:

```sh
/Applications/Isabelle2025-2.app/bin/isabelle build \
  -D Integer_Kernels -D Finite_Embedding_Bounds \
  -d /Users/lawrpau/isabelle/afp/release/thys \
  -o document=false Finite_Embedding_Bounds
```
