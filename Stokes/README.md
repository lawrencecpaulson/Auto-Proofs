# Stokes

This AFP entry contains one Isabelle session, `Stokes`, based on the AFP
`Smooth_Manifolds` session. Its `ROOT` lists the theories and builds the
article in `document/root.tex`.

The development proves Stokes' theorem for compactly supported near-top
coordinate form families on oriented smooth half-space atlases. It defines
chart-independent body and boundary integrals using finite smooth partitions
of unity and proves their equality by local half-space Stokes and gluing.
It also develops a one-dimensional exact-form theorem and proves a concrete
two-chart instance for the closed unit disk. The Green-form theorem identifies
the local coordinate sign. `Green_Rectangle_Contour.thy` proves Green's theorem
for a C¹ planar field on a rectangle using a Lebesgue area integral and the
real part of Isabelle's complex contour integral around `rectpath`.
`Green_Rectangular_Union.thy` extends the area identity to a finite union of
rectangles with disjoint interiors and a common C¹ neighborhood. It expresses
the boundary as a signed sum of horizontal and vertical edge integrals; whole
shared edges cancel. `Green_Edge_Subdivision.thy` cuts edges at every
rectangle coordinate, proves cancellation also at T-junctions, and states the
identity using the remaining oriented elementary segments.
`Green_Edge_Orientation.thy` shows that each elementary segment has
coefficient -1, 0, or 1. A nonzero sign records which side is occupied and
therefore the segment's boundary direction, including at T-junctions.
`Green_Edge_Flow.thy` proves that directed boundary edges balance at every
vertex. `Green_Boundary_Walks.thy` partitions them into closed walks, allowing
disconnected regions and vertices visited more than once.
`Green_Edge_Contour.thy` and `Green_Boundary_Contour.thy` relate the signed
edge integrals to complex `linepath` contour integrals.
`Green_Walk_Paths.thy` joins each walk into a closed polygonal path and states
Green's theorem as a sum of contour integrals over those paths.
`Green_Curl.thy` packages the same result for a C¹ planar vector field:
the integral of its scalar curl over the region equals the sum of
circulations around the closed boundary paths.
`Green_AC_Paths.thy` relates contour integrals and path length of an
absolutely continuous path to its almost-everywhere velocity. It also
derives almost-everywhere differentiability from absolute continuity.
The `green_ac_velocity` locale collects the velocity assumptions.
`Green_AC_Approximation.thy` approximates such a path by valid paths
with continuous velocity, preserving endpoints and controlling both
uniform path error and integrated velocity error. For a point off the
original path, sufficiently close approximants have the same winding
number. `Green_AC_Winding.thy` bounds the change of the Cauchy-kernel
contour integral under this approximation and proves its equality with
the path's winding number. Its final result needs only absolute continuity
and a point outside the path image.
`Green_AC_Measure.thy` proves that every rectifiable complex path, hence
every absolutely continuous complex path, has a negligible image.
`Green_Cauchy_Area.thy` proves local integrability of the planar Cauchy
kernel and a bound uniform over a bounded set of path points.
`Green_Cauchy_Fubini.thy` uses this bound to establish product-space
integrability and exchange the time and area integrals.
`Green_Cauchy_Winding_Area.thy` proves continuity of the Cauchy area
transform and a winding-weighted area identity for its contour integral
along an absolutely continuous path, for a compactly supported
continuous density.
`Green_Cauchy_Differentiability.thy` differentiates the translated area
integral for a compactly supported density with uniformly continuous
bounded derivative, expressing the derivative by integrating the density's
derivative against the fixed Cauchy kernel.
`Green_Cauchy_Curl.thy` packages the area transform as a planar field,
identifies its circulation with the real part of the contour integral,
and relates the field's curl to the Wirtinger \(\bar\partial\) derivative
where the transform is differentiable.
`Green_Cauchy_Pompeiu.thy` combines rectangular Green with the winding-area
identity and proves both \(T(\bar\partial u)=-\pi u\) and
\(\bar\partial(Tu)=-\pi u\) for a regular compactly supported density.
It also derives a winding-weighted complex Green formula for absolutely
continuous paths and a Cauchy-kernel contour identity for rectangles away
from the pole, using only local \(C^1\) regularity.
`Green_Cauchy_Pompeiu_Interior.thy` proves the interior rectangular
Cauchy–Pompeiu formula for a locally \(C^1\) function. Its punctured
rectangle identity and shrinking-square estimates establish both local
integrability of the singular area kernel and the residue contribution.
`Green_Cauchy_Local_Green.thy` proves winding-weighted complex Green for
a closed absolutely continuous path and a locally \(C^1\) function on an
open neighborhood of the path and its bounded interior. It also proves
integrability of the winding-weighted Wirtinger derivative.

The principal results are in:

- `BoundaryIntegration/Global_Gluing.thy`: global Stokes and corollaries.
- `One_Dimensional_Integration.thy`: the one-dimensional integral.
- `BoundaryIntegration/Disk_Stokes.thy`: the closed disk instance.
- `BoundaryIntegration/Green_Form.thy`: the Green-form coordinate identity.
- `Green_Rectangle_Contour.thy`: Green's theorem for a rectangular contour.
- `Green_Rectangular_Union.thy`: Green's theorem for finite rectangular unions.
- `Green_Edge_Subdivision.thy`: the exposed-segment boundary formula.
- `Green_Edge_Orientation.thy`: occupied-side and orientation criteria for
  elementary boundary segments.
- `Green_Edge_Flow.thy`: vertex balance for the subdivided boundary.
- `Green_Boundary_Walks.thy`: finite decomposition into closed directed walks.
- `Green_Edge_Contour.thy` and `Green_Boundary_Contour.thy`: edge-to-contour
  identities and the contour sum over the boundary.
- `Green_Walk_Paths.thy`: Green's theorem for closed polygonal boundary paths.
- `Green_Curl.thy`: the planar vector-field curl and circulation form.
- `Green_AC_Paths.thy`: the absolutely continuous path and velocity bridge.
- `Green_AC_Approximation.thy`: endpoint-preserving valid-path approximation
  and stability of winding number.
- `Green_AC_Winding.thy`: the Cauchy-kernel contour-integral formula for
  absolutely continuous paths, with or without a specified velocity.
- `Green_AC_Measure.thy`: negligible image of a rectifiable complex path.
- `Green_Cauchy_Area.thy`: local integrability and uniform area bounds for
  the Cauchy kernel against a compactly supported continuous function.
- `Green_Cauchy_Fubini.thy`: product-space integrability and Fubini exchange
  for the Cauchy area kernel along a path.
- `Green_Cauchy_Winding_Area.thy`: continuity of the Cauchy area transform
  and its contour-integral identity with winding-weighted area.
- `Green_Cauchy_Differentiability.thy`: Fréchet differentiability and \(C^1\)
  regularity of the Cauchy area transform for a regular compactly supported
  density.
- `Green_Cauchy_Curl.thy`: the planar field associated with a complex
  coefficient, its circulation, and its curl in terms of \(\bar\partial\).
  For a regular density, \(\bar\partial\) commutes with the Cauchy area
  transform, and the resulting curl is continuous.
- `Green_Cauchy_Pompeiu.thy`: complex rectangular Green, coordinate and
  measure bridges, the two Cauchy–Pompeiu inverse identities, and the
  winding-weighted Green formula `green_ac_contour_wirtinger_dbar_winding_area`.
- `Green_Cauchy_Pompeiu_Interior.thy`: the interior rectangular
  Cauchy–Pompeiu representation for locally \(C^1\) functions.
- `Green_Cauchy_Local_Green.thy`: winding-weighted Green for closed
  absolutely continuous paths and local \(C^1\) functions.

When this directory is placed alongside `Smooth_Manifolds` in an AFP theories
tree, build and check the document with:

```sh
isabelle build -d ../Smooth_Manifolds -D . -o document=pdf
```
