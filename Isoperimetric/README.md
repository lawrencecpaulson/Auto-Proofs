# Isoperimetric AFP entry

This Isabelle2026 entry proves the planar isoperimetric inequality for
rectifiable simple closed curves, including the implication that equality
forces the curve image to be a circle. The proof uses arc-length
reparametrisation and develops a Wirtinger inequality, a convex-curve area formula,
and convexification. Its source is John Harrison's HOL Light
`100/isoperimetric.ml`; Claude assisted with the port, which required
substantial manual work. There were no additional textual sources.

`ROOT` lists the three local theories and depends on the AFP `Fourier`
session. The bounded-variation, absolute-continuity, and rectifiable-path
theories used here are supplied by Isabelle2026. The document source is
`document/root.tex`, and staged AFP metadata is at
`../metadata/entries/Isoperimetric.toml`. Update the metadata date when
submitting to the AFP.

For an AFP checkout, copy `ROOT`, the three `.thy` files, and `document/`
to `thys/Isoperimetric/`; copy the staged TOML file to `metadata/entries/`
and add `Isoperimetric` to `thys/ROOTS`. Local backup files ending in
`.thy~` and `.marks` files are outside the entry.

To check the session against Isabelle2026-RC4 and a compatible AFP:

```sh
USER_HOME=/private/tmp/isoperimetric_rc4_user \
  /Applications/Isabelle2026-RC4.app/bin/isabelle build \
  -d /Users/lawrpau/isabelle/afp/devel/thys \
  -d /Users/lawrpau/isabelle/Auto-Proofs/Isoperimetric \
  -o threads=8 -o document=pdf -o document_output=output \
  -o 'document_variants=document:outline=/proof,/ML' Isoperimetric
```

Generated PDFs in `output/` are ignored by Git.
