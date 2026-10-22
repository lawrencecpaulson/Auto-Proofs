# Milestone 1: Euclidean forms needed for Stokes

This is the mathematical target and Isabelle-interface specification.
`Stokes_Forms.thy` checks the Cartesian coordinate representation,
its signed exterior-derivative coefficient, locality, support and
finite-sum laws, pullback composition, and C² naturality for local
inverse charts. The Piola identity used for naturality is proved.
`Stokes_Product_Forms.thy` checks a product-coordinate form model,
its boundary sign, chart-local Stokes theorem, linearity, support
and locality laws, and independence of the ambient extension at the
half-space face. `Stokes_Cart_Product.thy` checks Cartesian/product
coordinate transport. `Stokes_Halfspace_Naturality.thy` proves C²
pullback naturality when ambient chart extensions are inverse only
on the half-space, plus the local boundary coefficient pullback law.
`Stokes_Block_Determinant.thy` proves the cofactor-to-face-Jacobian
identity and positivity of the normal derivative under half-space
chart hypotheses.
`Stokes_Halfline_Forms.thy` handles dimension one. A general exterior
algebra is optional.

## Deliverable 1a: near-top and top forms

On an open subset `U` of an oriented `n`-dimensional Euclidean model,
for `n >= 1`, provide:

- Smooth `(n-1)`-forms and `n`-forms, with addition, finite sums, scalar
  multiplication by smooth functions, restriction, and support.
- Pullback of both degrees along sufficiently smooth maps between
  equal-dimensional coordinate domains. In coordinates, top-form
  pullback multiplies the coefficient by the Jacobian determinant.
- An exterior derivative

      d : Omega^(n-1)(U) -> Omega^n(U)

  that is linear, local under restriction, and natural under smooth
  pullback: `d (pullback f omega) = pullback f (d omega)`.
- The coordinate identity, for

      omega = sum_i a_i
        * (dx_1 /\ ... /\ omit(dx_i) /\ ... /\ dx_n),

      d omega =
        (sum_i (-1)^(i-1) * partial_i a_i)
        * (dx_1 /\ ... /\ dx_n).

The last equation is the interface with milestone 2. The pullback and
naturality laws are the interface with charts in milestones 3-5. Compact
support of `rho * omega` should follow from compact support of `omega`
and containment of the product's support in the intersection of
supports. The chart-local coefficient interpretation should be explicit.

For half-space charts, read "smooth" as admitting local smooth ambient
extensions, as specified in `MILESTONE_4_SPEC.md`. Restriction from an
ambient open set to a relatively open half-space set must preserve the
operations above.

## Representation decision

The shortest candidate represents a near-top form by its coefficients
`a_i` in the basis that omits coordinate `i`, and a top form by one
coefficient. This matches `LeanStokes/CubeStokes/Defs.lean` and makes
the local Stokes integrand transparent. Pullback of near-top forms then
uses Jacobian minors. Its naturality with `d` is a substantive
multivariable-calculus proof involving those minors and derivatives of
the Jacobian; it should be prototyped before committing to this
representation for manifold charts.

The alternative is general alternating multilinear maps. This gives
the usual coordinate-free pullback and exterior derivative, but needs
an exterior-form library that the inspected Isabelle/AFP trees do not
currently supply. Either representation must expose the same
mathematical laws above. The decision should be based on a small
checked prototype of pullback and naturality, not on the brevity of
the coordinate definition alone.

Regularity matters: a coordinate formula for `d omega` needs one
derivative of the coefficients, while the naturality proof for a chart
transition may differentiate its Jacobian and therefore use a `C^2`
transition. The eventual smooth-manifold locale supplies this
regularity. State every lemma with its actual assumptions.

## Deliverable 1b: optional full exterior algebra

If the aim is also a reusable library for *all* degrees, extend 1a to
alternating forms, wedge product, pullback in all degrees, the graded
Leibniz rule, and `d (d omega) = 0`. This completes the broader
interpretation of milestone 1. None of these extra results, including
the Leibniz rule, is needed for the finite-sum gluing proof in milestone
6: linearity and locality of `d` suffice once the partition gives a
finite decomposition of `omega`.

## Source and Isabelle checks

- `LeanStokes/CubeStokes/Defs.lean` gives the missing-coordinate
  coefficients; `CubeStokes/Bridge.lean` connects their signed
  derivative to mathlib's exterior derivative.
- The downloaded mathlib snapshot's
  `Analysis/Calculus/DifferentialForm/Basic.lean` supplies general
  `extDeriv`, pullback, and naturality (`extDeriv_pullback`). This is a
  guide to theorem interfaces, not an Isabelle dependency.
- AFP `Smooth_Manifolds/Cotangent_Space.thy` supplies some cotangent
  operations but not a general exterior-form library.
- `MILESTONE_2_SPEC.md` fixes the first-coordinate half-space
  convention and the `-1` lower-boundary sign.

## Completion criteria for 1a

1. The coordinate equation for `d` agrees with the milestone 2
   integrand, including signs in dimensions one, two, and three.
2. Pullback of top and near-top forms and naturality of `d` are proved
   on chart overlaps, with explicit regularity and orientation
   assumptions.
3. Restriction, smooth scalar multiplication, compact support, and
   finite-sum laws are available for chart localization.
4. Ambient-extension and half-space restriction versions needed by
   boundary charts are stated and proved. The zero-dimensional
   boundary in dimension one is handled separately.

## Status

Deliverable 1a is checked as a coordinate-coefficient interface for
Stokes, including local half-space pullback naturality and the
restricted-face Jacobian boundary law. The all-degree exterior algebra
in 1b and arbitrary-tangent evaluation remain optional extensions.
The signed coordinate formula covers dimensions two and three;
dimension one has a separate checked half-line theorem.
