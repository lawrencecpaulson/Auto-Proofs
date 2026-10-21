# Milestone 7: classical Green's theorem

This is a proposed corollary of Milestone 6, not a checked Isabelle
theory. It should state Green's theorem in the usual vector-calculus
notation and identify its two integrals with the manifold integrals
used for Stokes.

## Main statement

Let `R` be a compact oriented planar region with a sufficiently smooth
boundary, oriented by `dx /\ dy`. Let `P` and `Q` be C¹ on a neighbourhood
of `R`. With the boundary orientation induced by the outward-normal-first
rule, prove

    integral_R (partial_x Q - partial_y P) dA
      = contour_integral_(boundary R) (P dx + Q dy).

For a simply connected region, the induced boundary direction is
counterclockwise. For a region with holes, the outer boundary is
counterclockwise and inner boundaries are clockwise. These directions
should be proved from the orientation convention, rather than added
as separate sign assumptions.

## Bridge from Stokes

1. Instantiate the positive two-dimensional boundary atlas for the
   planar region. First use a region with a smooth boundary and a
   concrete atlas; identify which geometric hypotheses make a general
   planar-region statement meaningful in Isabelle.
2. Represent the one-form `P dx + Q dy` by the existing near-top
   coordinate family. Check that its exterior top coefficient is
   `partial_x Q - partial_y P`. The existing local convention
   `d(P dy + Q dt) = (partial_t P - partial_y Q) dt /\ dy`
   provides the sign check when `t = x`.
3. Identify `integral_body_top` with the usual planar area integral
   and `integral_boundary_top` with the oriented contour integral,
   including the boundary orientation and any conversion between
   Lebesgue and gauge integrals.
4. Apply Milestone 6. The compactness of `R` supplies compact support
   relative to its carrier. State a version for `P` and `Q` that are
   only C¹ near `R`; compact support in the ambient plane is unnecessary.

The separate `Green/` development already has Type I and Type II
region theorems and a line-integral interface. Reuse its definitions
or prove an explicit equivalence if that shortens the contour-integral
bridge. This milestone should culminate in a theorem with the
traditional area and contour integrals in its statement.

## Completion criteria

- The standard `partial_x Q - partial_y P` sign is checked.
- The boundary integral is expressed as an ordinary oriented line
  integral, with the correct direction on each component.
- The displayed Green identity follows from the global Stokes theorem
  in Isabelle, with no new planar subdivision argument.
