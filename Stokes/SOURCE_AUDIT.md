# Source audit for the Stokes development

This audit is based on reading local source files. It does not claim that
either the Lean or prospective Isabelle developments have been built here.

## Lean manuscript and extracted source

The manuscript is `/Users/lawrpau/Downloads/stokes-lean.tex`; its extracted
source is `/Users/lawrpau/Downloads/lean-stokes-theorem-main`.
`lean-toolchain` pins Lean 4.29.1 and `lakefile.toml` pins mathlib
`v4.29.1`. A static search found 44 files under `LeanStokes/` and no
`sorry`, `admit`, or `axiom` declarations. These checks support the
existence of the stated source code, but they are not a substitute for
running `lake build`.

| Source file under `LeanStokes/` | What it establishes | Use here |
| --- | --- | --- |
| `CubeStokes/Defs.lean` | Coordinate near-top forms, signed coefficients, exterior derivative coefficient, box and face integrals | Sign and interface guide |
| `CubeStokes/Theorem.lean` | Box Stokes by direct application of mathlib's divergence theorem | Analytic target, not a directly portable proof |
| `CubeStokes/Smooth.lean` | Smooth-coefficient version of box Stokes | Regularity guide |
| `CubeStokes/Bridge.lean` | Coordinate formula agrees with mathlib's abstract `extDeriv` | Later interface check |
| `SingularCubeStokes/Theorem.lean` | Pullback and Stokes for smooth singular cubes | Optional cubical route |
| `Domain/HalfSpace.lean` | Definitions of half-space, boundary, interior; two elementary inclusions | Does not prove milestone 2 |
| `Domain/SmoothDomain.lean` | Structure for a compact regular sublevel set and elementary set inclusions | No integration or Stokes theorem; its compactness condition excludes a half-space |
| `Domain/BoundaryOrient.lean` | Defines a scalar sign; no induced-orientation theorem | Do not use as an orientation proof |
| `Integration/OrientedIntegral.lean` | Multiplies a Euclidean set integral by a given sign | Does not construct manifold integration |

The three-line proof of `CubeStokes.stokes_on_box` invokes
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'`.
The theorem and its substantial proof are present in the local mathlib
snapshot at
`/Users/lawrpau/isabelle/mathlib4-master/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`.
An Isabelle proof must supply the analytic slice/Fubini step or identify
an equivalent Isabelle theorem. Mathlib's result permits a countable set
of nondifferentiability points. Milestone 2 assumes `C^1` coefficients, so
that extra generality is not needed for the first Isabelle proof.

**Boundary-sign issue in the auxiliary Lean scaffolding.**
`Domain/HalfSpace.lean` uses the *first* coordinate and `t >= 0`.
For ambient orientation `dt /\ dy_1 /\ ...`, outward-normal-first gives
the `t = 0` boundary sign `-1` in every positive dimension. The separate
`Domain/BoundaryOrient.lean` defines `(-1)^(d-1)`, which does not match
that convention in odd dimensions. A source search found no use of this
definition elsewhere in the Lean files. The proven box formula uses its
own face signs, so this issue concerns the auxiliary domain sketch.

The repository states `GPL-3.0-only`. Any close source-level port intended
for publication will need its licensing handled explicitly. The present
documents describe mathematics and interfaces rather than copying code.

## Isabelle2026_RC4: analytic ingredients

Paths below are relative to
`/Applications/Isabelle2026-RC4.app/Contents/Resources/src/HOL/Analysis/`.

| Theory and declaration | What it supplies | Remaining work |
| --- | --- | --- |
| `Interval_Integral.thy:599`, `interval_integral_FTC_finite` | One-dimensional Lebesgue FTC | Apply uniformly to slices |
| `Equivalence_Lebesgue_Henstock_Integration.thy:930`, `integral_FTC_atLeastAtMost` | Closed-interval Lebesgue FTC | Relate slice derivative to the ambient partial derivative |
| `Lebesgue_Measure.thy:1180`, `lborel_prod` | Lebesgue measure on a Euclidean product is the product measure | Rewrite the product-box integral |
| `Bochner_Integration.thy:3156`, `integral_fst` | Product integral equals an iterated integral under integrability | Obtain slice/box identity |
| `Bochner_Integration.thy:3180`, `Fubini_integral` | Swap the order of iterated integrals | Use if the coordinate order requires it |
| `Lebesgue_Measure.thy:1219`, `borel_integrable_compact` | Continuity on compact set implies integrability after restriction | Discharge box integrability |
| `Henstock_Kurzweil_Integration.thy:6853`, `integral_prod_continuous` | Product-box formula for the gauge integral | Alternative if Lebesgue route becomes awkward |
| `Equivalence_Lebesgue_Henstock_Integration.thy:816`, `integral_lborel` | Gauge/Lebesgue identification under integrability | Needed only for the gauge alternative |
| `Change_Of_Vars.thy:3691`, `integral_change_of_variables` | Change of variables with absolute Jacobian determinant | Later chart integration; orientation supplies the sign |

The first-column lemmas have been read, not tried in a common theory.
The main local bottleneck is the coordinate/face representation, not the
one-dimensional FTC. In particular, Isabelle's `euclidean_space` class
requires a nonempty `Basis` (`Euclidean_Space.thy:27`); the dimension-one
case should be stated separately if a product `real * 'e::euclidean_space`
is used.

## AFP devel: geometric ingredients

Paths below are relative to
`/Users/lawrpau/isabelle/afp/devel/thys/Smooth_Manifolds/`.

| Theory | Existing result | Work still needed |
| --- | --- | --- |
| `Chart.thy` | Charts to open subsets of full Euclidean spaces | Charts into relatively open subsets of a half-space |
| `Differentiable_Manifold.thy` | Compatible smooth atlases | Boundary-compatible atlas and transition extensions |
| `Partition_Of_Unity.thy:365` | Locally finite smooth partition of unity on existing manifolds | Boundary version, or a proof that the construction adapts |
| `Cotangent_Space.thy` | Cotangent spaces, fields, and a path-integral FTC | Near-top forms, exterior derivative, and top-form integration |

The existing partition-of-unity theorem is valuable, but it is a
`c_manifold` theorem built on full-space charts. It cannot simply be
applied to a manifold-with-boundary whose charts have half-space images.
The general Stokes theorem will also need orientation and integration
independent of the chosen oriented chart.

The AFP `Green` development provides two-dimensional examples and sign
checks. Its chain and region-specific infrastructure is not a
prerequisite for the local half-space proof.
