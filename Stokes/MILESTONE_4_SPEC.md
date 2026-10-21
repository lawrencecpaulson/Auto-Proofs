# Milestone 4: smooth manifolds with boundary

This is the specification and current proof ledger. The relative
half-space chart and atlas prototype now checks in
`Boundary/Stokes_Boundary_Charts.thy`. The mathematical references are Gualtieri,
`Gualtieri.pdf`, Section 1.3 (PDF page 9) and Proposition 6.17
(PDF page 58). Use the **first** coordinate as the boundary-defining
coordinate, consistently with `MILESTONE_2_SPEC.md`.

## Deliverable

Construct a smooth-manifold-with-boundary interface whose chart model is

    H('e) = {(t,y) : real * 'e | t >= 0}.

Define its boundary carrier, the restricted boundary charts, and the
induced boundary orientation. Prove that the restricted charts form a
smooth manifold without boundary in their **relative topology**, for
positive boundary dimension. Dimension one, whose boundary is discrete
and zero-dimensional, needs a separate representation and integral.

This milestone establishes geometry. Integration and the Stokes theorem
on this geometry are later milestones.

`Stokes_Halfspace_Naturality.thy` checks that a face-preserving
ambient chart map has zero normal/tangential Jacobian entries.
`Stokes_Block_Determinant.thy` identifies the boundary coefficient
pullback factor with the Jacobian determinant of the restricted face
map and proves positivity of the normal factor. This milestone
must lift those local results to a chart atlas and establish
chart-independent boundary orientation.

`BOUNDARY_CHART_DESIGN.md` gives the proposed first implementation:
an explicit manifold carrier, relatively open chart domains and
half-space codomains, and an explicit boundary carrier that may be
empty. It lists the small prototype lemmas to check before an atlas
locale is introduced.

## Checked geometry so far

`Stokes_Boundary` defines `halfspace_chart` and
`halfspace_atlas` on an explicit carrier. It proves relative chart
restriction, chart-independent boundary classification, relative
closedness of the boundary, and restricted boundary-chart
homeomorphisms. Boundary coordinate overlaps are open, and their
transitions are homeomorphisms. Checked identity atlases cover
nonempty and empty boundary cases.

`C2_halfspace_atlas` assumes local ambient C² extensions of chart
transitions and proves C² boundary transitions.
`positive_face_jacobian_from_inverse_extensions` gives a positive
face Jacobian when ambient C² extensions are inverse on the
half-space, the forward extension preserves the half-space and
face, and its ambient determinant is positive. It derives the
inverse-Jacobian equation at the face from the local inverse law.
`C2_halfspace_atlas.local_transition_extensions_inverse` now derives
locally inverse ambient extensions, half-space preservation, and
face preservation directly from the chart axioms and local C²
extensions. `product_halfspace_extension_jacobian_unique` proves
that local extensions have the same boundary Jacobian.
`positively_oriented_C2_halfspace_atlas` requires one positive
ambient extension at each overlap and proves positive
boundary-transition determinants. It also proves the
boundary coefficient pullback law for local near-top forms.
`Stokes_Boundary_Integration` proves the corresponding change of
variables for boundary overlaps and independence of finite
admissible partition sums. The abstract positive-orientation
locale still needs concrete smooth atlas instances. The
zero-dimensional boundary of a one-dimensional manifold uses
the separate halfline result.

## Boundary chart interface

A half-space chart `c` should contain:

- a domain open in the manifold's topology;
- a codomain relatively open in `H('e)`, equivalently `H('e) ∩ U` for
  some ambient open `U`;
- mutually inverse maps between domain and codomain, forming a
  homeomorphism;
- transition maps which, near each point of their half-space domain,
  admit smooth extensions to ambient open sets.

The existing AFP `Chart.thy` requires its codomain to be open in the
whole Euclidean model space (`Chart.thy:11,29,35`). Therefore a
boundary chart cannot be an instance of that `chart` type.
Similarly, `Smooth.thy:67,957` defines higher smoothness through
ambient derivatives. On a half-space this must be combined with the
local ambient-extension condition; using `smooth_on H` alone would
not express the desired smooth-up-to-boundary notion.

## Boundary set and restricted charts

1. Define `boundary M` as the points mapped to `t = 0` by a half-space
   chart, and `interior M` as the points mapped to `t > 0`.
2. Prove that the classification is independent of the chart.
   An efficient first interface can **require boundary preservation
   on chart overlaps** as a compatibility condition. Deriving this
   fact from homeomorphism alone is a separate topological theorem;
   it need not block the first Stokes development.
3. For a chart `c`, its boundary-coordinate domain is
   `{y | (0,y) ∈ codomain c}`, which is open in `'e` because the chart
   codomain is relatively open in `H('e)`. Restrict `c` to
   `boundary M ∩ domain c`, then take its `y` coordinate.
4. Prove the restricted chart domains are open **relative to
   `boundary M`** and the restricted transitions are smooth.

There is a type-design issue here: the AFP `manifold` locale uses
ordinary open chart domains in its ambient type, while a boundary
subset is usually not open in the original manifold. An empty
boundary also cannot be made into a subtype with an empty carrier
type in HOL. A relative-carrier chart locale, or an abstract separate
boundary type with a possibly empty carrier, avoids assuming that
`boundary M` is nonempty. This choice should be tested in a small
theory before porting the AFP manifold library.

## Induced orientation

Let `g` be a smooth transition between half-space charts, with
`g(0,y) = (0,g_B(y))`. Along `t = 0`, the derivative of the first
coordinate in tangential directions is zero. Its derivative matrix
is block triangular, with normal entry `a` and tangential block
`Dg_B`.

The normal entry is positive: the transition and inverse preserve
the half-space, and the ambient derivative is invertible. Deriving
invertibility at a boundary point from the locally extended
transition and inverse is an explicit proof obligation: differentiate
their inverse identities on the interior and pass to the boundary by
continuity. Hence

    det(Dg) = a * det(Dg_B),    a > 0.

If the ambient charts preserve orientation, their transition has
`det(Dg) > 0`; thus `det(Dg_B) > 0`. This is the chart-independence
lemma for boundary orientation. With our `t >= 0` first-coordinate
convention, outward-normal-first assigns the **negative** of the
standard `y` orientation to `t = 0`, in every dimension.

The auxiliary Lean `Domain/BoundaryOrient.lean` merely defines a
parity-dependent scalar and proves no such lemma. As recorded in
`SOURCE_AUDIT.md`, its displayed sign is inconsistent with the
Lean half-space file's first-coordinate convention in odd dimensions.
Use the direct orientation calculation above and the independent
PDF texts instead.

## Completion criteria

- Boundary/interior classification is chart independent.
- Every boundary point has a restricted chart, with smooth
  chart transitions and relatively open chart domains.
- The induced orientation is independent of its ambient chart.
- The empty-boundary and dimension-one cases have explicit
  statements; they are not hidden behind an unavailable
  zero-dimensional Euclidean-space instance.
