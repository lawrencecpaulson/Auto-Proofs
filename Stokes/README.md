# Generalised Stokes theorem in Isabelle

This directory is for the Stokes development. The local half-space
theorem below was the first proof target. Its coordinate statement
allowed the analytic proof to precede the form and manifold
interfaces.

Working documents:

- `PROOF_STATUS.md`: Isabelle-checked results, remaining local proof
  obligations, and build details.
- `MILESTONE_1_SPEC.md`: near-top forms, exterior derivative, pullback,
  and the optional all-degree extension.
- `MILESTONE_2_SPEC.md`: mathematical statement, sign checks, and lemma
  decomposition.
- `MILESTONE_3_SPEC.md`: oriented integration on existing AFP manifolds.
- `MILESTONE_4_SPEC.md`: half-space charts and induced boundary geometry.
- `MILESTONE_5_SPEC.md`: integration on manifolds with boundary and
  single-chart Stokes.
- `MILESTONE_6_SPEC.md`: global compact-support Stokes by finite gluing.
- `MILESTONE_7_SPEC.md`: classical Green's theorem as a planar corollary.
- `SOURCE_AUDIT.md`: Lean, mathlib, Isabelle, and AFP source map.
- `OFFLINE_PLAN.md`: order of proof experiments when Isabelle is available.
- `MANIFOLD_ROADMAP.md`: dependencies from local Stokes to the global theorem.
- `REMAINING_MILESTONES_PLAN.md`: executable proof gates for milestones
  1a and 3–7, including the form/chart interface that completes 2.
- `BOUNDARY_CHART_DESIGN.md`: proposed relative-carrier boundary-chart
  interface and the first milestone 4 prototype.
- `TEXT_SOURCES.md`: page guide to the two downloaded mathematical texts.
- `DOWNLOADS.md`: local source inventory and any remaining optional download.

## Isabelle-checked starting point

`ROOT` builds the local theories with Isabelle2026-RC4. The first two prove
slice FTC/Fubini identities, dimension-one half-space Stokes,
two-dimensional box and half-space Stokes, and the all-dimensional
half-space signed coordinate sum. `Stokes_Chart_Local.thy` proves
zero-extension and one-sided boundary derivative lemmas.
`Stokes_Chart_Theorem.thy` proves the chart-local coordinate identity
for compactly supported coefficients on a relatively open half-space
chart. `Stokes_Form_Bridge.thy` proves the corresponding integral
identity conditional on pointwise form coefficient laws.
`Stokes_Forms.thy` proves a Cartesian near-top form model, Piola's
identity, and C² pullback naturality. `Stokes_Product_Forms.thy`
discharges both pointwise coefficient laws for product-coordinate
forms and proves the local chart form theorem.
`Stokes_Cart_Product.thy` identifies Cartesian and product exterior
derivatives and proves C² naturality in product coordinates.
`Stokes_Halfline_Forms.thy` proves the dimension-one form theorem.
The `Stokes_Boundary_Integration` session now checks chart-supported
Stokes equations for relative half-space atlas charts, including
the boundary integral's negative normal sign and the interior
zero-boundary case. It also checks conditional single-chart body
and boundary integrals, their partition-free local Stokes equality,
and the compact-support bridge from a near-top form to its exterior
coefficient and boundary restriction. A packaged chart-supported
theorem using one compact support set is Isabelle-checked. Body
integrability, body compatibility from the interior pullback law,
boundary compatibility from the same interior law and boundary
differentiability, and
coefficient continuity are derived in the theories. The direct
`Stokes_chart_supported_form_C1` theorem applies the single-chart
integrals to one near-top coordinate family. The checked
`Stokes_chart_supported_form_integrals_C1` theorem uses the
partition-defined manifold body and boundary integrals, completing
Milestone 5b for a form supported in one chart. Milestone 5a now
provides finite chartwise C¹ partitions for arbitrary compact
support, body and boundary partition independence, linearity, and
the local chart rules. A common C¹ partition evaluates both integrals
when the body and boundary coefficients have one compact support
bound.
`Stokes_Halfspace_Naturality.thy` proves naturality when ambient chart
extensions are inverse only on the halfspace and a boundary
cofactor coefficient law. `Stokes_Block_Determinant.thy` identifies
that cofactor with the restricted face Jacobian and proves the
positive normal-factor relation. The dependent
`Stokes_Integration` session checks the oriented chart-change
integral theorem and compact-support integrability. The further
`Stokes_Manifold` session checks the chart-independent `integral_top`
for compactly supported compatible top-coefficient families on the
existing AFP boundaryless manifold, including the local chart rule,
uniqueness, and linearity.
The separate `Stokes_Boundary` session checks a relative
half-space chart atlas, restricted boundary charts and
transition homeomorphisms, and C² boundary transitions under
ambient-extension hypotheses. It derives local inverse and
face-preservation laws from those extensions. A positively oriented
C² atlas, specified by one positive ambient transition extension
at each overlap,
has positive boundary-transition determinants and a checked
boundary form coefficient transition law. The dependent
`Stokes_Boundary_Integration` session checks boundary-chart change
of variables, compact-support integrability, and independence of
finite admissible partition sums. Its boundary integral obeys
the partition-sum rule whenever an admissible partition exists,
and is zero for an empty boundary. Relative charts and the boundary
carrier now have compactly contained relative neighborhoods.
The relative atlas has checked compact-support chartwise C¹
partitions of unity. Gluing the chart-supported theorem across
such a partition is the next gate.
Exact theorem assumptions and
build details are in `PROOF_STATUS.md`.

## Milestone 2: local Stokes on a half-space

Fix `n >= 1`. Write `x = (t, y)` in `R x R^(n-1)` and let
`H = {(t, y) | t >= 0}`. Let `a_1, ..., a_n` be continuously differentiable
on an open neighbourhood of `H`. Assume that the restriction of each `a_i`
to `H` has compact support *relative to H*. The target identity is

    integral H (sum i=1..n (-1)^(i-1) * partial_i a_i)
      = - integral R^(n-1) (lambda y. a_1 (0, y)).

All integrals are Lebesgue integrals with the standard Euclidean measures.
The boundary term may be nonzero: compact support relative to `H` does not
require vanishing on `{0} x R^(n-1)`.

The signs correspond to the standard orientation
`dt /\ dy_1 /\ ... /\ dy_(n-1)` on `H`. The outward normal at `t = 0` is
`-partial_t`, so the induced boundary orientation is the negative of the
standard `y` orientation. In dimension one, the identity is
`integral {t >= 0} a_1'(t) dt = -a_1(0)`.

Once Euclidean differential forms are available, set

    omega = sum i=1..n a_i *
      (dx_1 /\ ... /\ omit(dx_i) /\ ... /\ dx_n).

The coordinate identity should yield

    integral H (d omega) = integral (boundary H) omega.

The checked chart-local theorem establishes the coefficient version
on `H ∩ U`, for ambient-open `U`, by zero extension. The extension
lemmas use a one-sided normal derivative on the face `t = 0`.

## Lead from the Lean manuscript

`/Users/lawrpau/Downloads/stokes-lean.tex` describes a coordinate box-Stokes
theorem in its "Box Stokes" sections. It writes the top-degree exterior derivative as
the divergence of the signed coefficient field. This is a useful guide for
the coordinate definitions and boundary signs, but the TeX is not a
machine-checked proof: its claims about the Lean development still need to
be checked against the Lean source before relying on them.
Its "Reproducibility" section names
`https://github.com/d0d1/lean-stokes-theorem` as the source repository.
The source is available locally at
`/Users/lawrpau/Downloads/lean-stokes-theorem-main`. Its `lean-toolchain`
and `lakefile.toml` pin Lean 4.29.1 and mathlib `v4.29.1`.

Relevant Lean files:

- `LeanStokes/CubeStokes/Defs.lean`: coordinate form, signed coefficients,
  exterior derivative coefficient, box integral, and face integral.
- `LeanStokes/CubeStokes/Theorem.lean`: box Stokes as an application of
  mathlib's divergence theorem.
- `LeanStokes/CubeStokes/Smooth.lean`: derives the box theorem's hypotheses
  from smooth coefficients.
- `LeanStokes/CubeStokes/Bridge.lean`: relates the coordinate derivative to
  mathlib's `extDeriv`.
- `LeanStokes/SingularCubeStokes/Theorem.lean`: pulls box Stokes back along a
  smooth singular cube. This belongs to an optional cubical-chain branch.

`LeanStokes/Domain/HalfSpace.lean` defines the half-space and proves only
basic set inclusions. `LeanStokes/Domain/BoundaryOrient.lean` defines a
sign for a smooth domain; it does not establish a manifold boundary
orientation theory. A source scan found no `sorry`, `admit`, or `axiom`
declarations, but no Lean build has been run locally.

One possible route to the target above is to prove box Stokes first. Choose
`R` so that the support in `H` lies strictly inside
`[0, R] x [-R, R]^(n-1)` except possibly along `t = 0`. All box-face terms
other than the `t = 0` face then vanish, giving the half-space identity.
The manuscript obtains its box theorem from a mathlib divergence theorem;
that short Lean proof is not itself an Isabelle proof.

The manuscript's main theorem concerns smooth singular cubes in Euclidean
space. Its discussion explicitly leaves compactly supported half-space
Stokes, manifold integration, and boundary orientation for future work.
Cubical-chain machinery is therefore optional for the manifold route here.

## Subsequent milestones

1. Euclidean differential forms, exterior derivative, and pullback.
2. Local half-space Stokes (the target above).
3. Orientation and integration on manifolds without boundary.
4. Smooth manifolds with boundary and induced boundary orientation.
5. Boundary-compatible integration, then Stokes for forms supported in
   a single chart.
6. General compact-support Stokes by a partition of unity.

The existing AFP `Smooth_Manifolds` development provides smooth manifolds
and partitions of unity, but its charts have images open in the whole
Euclidean model space. Boundary charts therefore need an extension of that
interface. The first part of milestone 1 targets only the form degrees
needed for Stokes; a full all-degree exterior algebra is an optional
follow-on. Cubical-chain Stokes is a separate, optional development.
