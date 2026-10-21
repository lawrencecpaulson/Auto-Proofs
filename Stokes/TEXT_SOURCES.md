# Reading the two downloaded PDF texts

Both PDFs have usable embedded text. I extracted them with Poppler's
`pdftotext -layout`, then checked the local Stokes signs against rendered
pages. Extraction is good for locating arguments and reading prose.
Displayed mathematics can lose fractions, superscripts, pullback stars,
and integral domains, so the PDF page remains the authority for a
formula.

For example, page-specific extraction can be repeated with:

    pdftotext -f 1 -l 2 -layout ~/Downloads/Sadun.pdf -
    pdftotext -f 57 -l 59 -layout ~/Downloads/Gualtieri.pdf -

For an image-only PDF, OCR (for example, `ocrmypdf` or `tesseract`) would
be needed first. These two files do not need OCR. Full extracted text
was kept only in `/private/tmp` for inspection; the source PDFs remain
in `~/Downloads`.

## Sadun, *Notes on Differential Forms, Part 2*

Source: `/Users/lawrpau/Downloads/Sadun.pdf` (4 PDF pages).

- **Page 1, Theorem 1.1:** compactly supported Stokes on the Euclidean
  half-space. Sadun puts the boundary-defining variable **last**,
  `x_n >= 0`, and gives the boundary orientation relative to the
  standard `x_1,...,x_(n-1)` coordinates as `(-1)^n`. The proof treats
  each coordinate coefficient separately using one-dimensional FTC
  and Fubini.
- **Pages 2-3, Theorem 2.1:** Stokes on a compact oriented manifold
  with boundary. The proof localises with a partition of unity,
  commutes exterior differentiation with pullback, extends
  chart-supported forms by zero to the half-space, and applies
  Theorem 1.1. Page 3 notes that a noncompact manifold instead needs
  compact support of the form.

Our milestone 2 uses the **first** coordinate `t >= 0`. With ambient
orientation `dt /\ dy_1 /\ ...`, its lower-face sign is `-1` in every
dimension. This is consistent with Sadun's `(-1)^n` because his
normal coordinate is last.

## Gualtieri, *Geometry and Topology I*

Source: `/Users/lawrpau/Downloads/Gualtieri.pdf` (62 PDF pages).

- **Page 9, Section 1.3:** manifolds with boundary use the half-space
  model. Definition 1.25 defines smoothness on a subset by local
  ambient smooth extensions. This makes the zero-extension
  regularity obligation in `MILESTONE_2_SPEC.md` explicit.
- **Page 39, Theorem 4.5:** constructs a partition of unity using
  bump functions on regular chart covers.
- **Page 57, Theorem 6.16:** defines integration of compactly
  supported top forms on an oriented manifold by chart integration
  and proves chart independence using a partition of unity.
- **Page 58, Proposition 6.17:** constructs the induced boundary
  orientation from an outward-pointing vector field. The page also
  carries the compactly supported local half-space calculation.
- **Page 59, Theorem 6.18:** states and proves Stokes for compactly
  supported forms on an oriented manifold with boundary by
  localising to charts. It does not require cubical chains.

Gualtieri also places the boundary-defining coordinate last. His
calculation on page 58 agrees with Sadun's sign convention. The
first-coordinate convention in this project is mathematically
equivalent, but the sign must be recalculated when translating
the formula.

## What the texts settle

The half-space theorem is the appropriate local milestone. Both
independent accounts derive it from FTC and Fubini, and both use it
directly in the manifold proof. They also confirm that chart
integration, induced boundary orientation, and localisation by a
partition of unity are separate obligations.
