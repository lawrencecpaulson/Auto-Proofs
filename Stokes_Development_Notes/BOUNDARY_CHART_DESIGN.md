# Boundary-chart interface: design for the first Isabelle prototype

This began as an interface proposal for milestone 4. Its topology
and local C²-extension prototype now checks in
`Boundary/Stokes_Boundary_Charts.thy`. The local derivative and
boundary cofactor pullback laws in the core Stokes session are
also checked. Atlas-level orientation and boundary integration
remain.

## Choice of carrier and model

Use an ambient Hausdorff, second-countable type `'a` together with
an explicit set `M :: 'a set` as the manifold carrier. Chart domains
are open in `top_of_set M`. This is necessary for the identity chart
on a Euclidean half-space: `H` is not ambient-open, but it is open
relative to itself. The boundary is another set `B ⊆ M`, possibly
empty, in the **same** type `'a`; no nonempty boundary subtype is
required.

For positive boundary dimension, use coordinates
`p :: real × 'e::euclidean_space` and

    H = {p. 0 ≤ fst p}.

Every chart image `C` should satisfy `C = H ∩ U` for some
ambient-open `U`, or equivalently
`openin (top_of_set H) C`. Isabelle's `openin_open` supplies the
equivalence. The `real` coordinate is always first, matching the
checked local Stokes theorem.

## Minimal chart data

A small record or locale can carry the following data. These are
**proposed fields**, not syntax-checked declarations:

    domain_c   :: 'a set
    codomain_c :: (real × 'e) set
    to_c       :: 'a ⇒ real × 'e
    from_c     :: real × 'e ⇒ 'a

with laws

    openin (top_of_set M) domain_c
    openin (top_of_set H) codomain_c
    homeomorphism domain_c codomain_c to_c from_c.

An atlas covers `M` by chart domains. Its overlap transition from
`c` to `d` is `to_d ∘ from_c` on the coordinate image of their
domain intersection. Include both directions of an overlap rather
than an arbitrary global extension of the transition.

**Compatibility condition for the first version:** on overlaps,
`fst (to_c x) = 0` exactly when `fst (to_d x) = 0`. This makes

    B = {x ∈ M. some chart maps x to first coordinate 0}

chart independent without first proving topological invariance of
the boundary. The latter can be investigated later.

## Smoothness at the face

`k-smooth_on H f` from AFP uses derivatives within its set and does
not by itself state the ambient-extension condition chosen in
`MILESTONE_4_SPEC.md`. For each overlap point `p`, require an
ambient-open neighbourhood `V` and a smooth extension `F` on `V`
which agrees with the transition on `V ∩ H` inside its overlap.
Require the same for the inverse transition. A condition using
`Ck_on 2 F V` matches the current Piola plan; a smooth version may
be used for the eventual atlas.

`cart_halfspace_ambient_derivative_unique` proves that two
extensions agreeing on the half-space have the same derivative
at a boundary point. The boundary atlas uses the actual boundary
transition for its Jacobian; local extension derivatives enter
only its proof of positivity.

## First proof sequence

1. **Relative topology.** Prove that `H` is closed; that
   `{p ∈ H. fst p > 0}` is open in `H`; and that
   `{y. (0,y) ∈ C}` is open in `'e` for a relatively open
   `C ⊆ H`. Use `openin_open` and continuity of
   `y ↦ (0,y)`.
2. **Chart restriction.** Restrict a chart to a relatively open
   subset of its domain. Prove inverse and homeomorphism laws for
   the restriction. This is the operation used for overlap
   neighbourhoods and compactly supported localisation.
3. **Two examples.** Construct the identity chart for carrier `H`
   (nonempty boundary) and the identity chart for carrier
   `{p. fst p > 0}` (empty boundary). These test the relative-carrier
   and empty-boundary design without any manifold machinery.
4. **Boundary carrier.** With the overlap compatibility condition,
   show `B ∩ domain_c = {x ∈ domain_c. fst (to_c x)=0}`. Deduce
   that `B` is closed relative to `M`, because its complement is
   the union of chart interior sets.
5. **Restricted boundary chart.** On `B ∩ domain_c`, use
   `x ↦ snd (to_c x)`, with inverse
   `y ↦ from_c (0,y)`. Prove it is a homeomorphism to
   `{y. (0,y) ∈ codomain_c}`. Its domain is open relative to
   `B`. Restricted transitions are smooth via ambient extensions.
6. **Derivative on the face.** Show the normal coordinate of a
   transition has zero tangential derivative. Show its normal
   derivative is positive: half-space preservation gives
   nonnegativity, and invertibility of the ambient derivative
   excludes zero. Invertibility at the face needs a separate
   argument from inverse identities in the dense interior and
   continuity of the derivatives.
7. **Orientation.** Prove the block determinant law
   `det Dg = a * det Dg_B` with `a > 0`. Thus positively
   oriented ambient transitions give positively oriented boundary
   transitions. The outward-normal-first orientation is the
   negative of the standard `y` orientation for this first-coordinate
   convention.

All seven steps now have checked results in `Stokes_Boundary`,
subject to the explicit positive ambient transition condition
of `positively_oriented_C2_halfspace_atlas`.
`halfspace_atlas` proves chart-independent boundary classification,
relative closedness of the boundary, restricted boundary-chart
homeomorphisms, open face-coordinate overlaps, and boundary
transition homeomorphisms. Both a full-half-space atlas and an
empty-boundary atlas are checked. `C2_halfspace_atlas` assumes local
ambient C² extensions and proves C² boundary transitions.

`C2_halfspace_atlas.local_transition_extensions_inverse` derives
the local inverse and face laws from the ordinary smooth atlas
condition. `positive_face_jacobian_from_product_extensions`
proves the positive face Jacobian, and
`positively_oriented_C2_halfspace_atlas` transfers it to the
actual boundary transition. Its
`local_boundary_coefficient_transition` theorem also connects
the pulled-back near-top form to the boundary top-form law.

## Partition-of-unity consequence

AFP `Topological_Manifold.thy` defines its carrier as a union of
ambient-open chart domains, and `Chart.thy` requires an ambient-open
Euclidean codomain. Its chart type therefore cannot simply be reused
for `H`. Its proof of `precompact_neighborhoodE`, however, suggests
the relative-carrier analogue: choose a small ambient closed ball
around a chart point inside `U`, intersect it with `H`, and pull that
compact set back through the chart inverse. Use **relative closure
in `M`** throughout.

AFP `Partition_Of_Unity.thy` then supplies a proof pattern for a
locally finite refinement and normalised smooth bumps. The local
bump on `H ∩ U` can be the restriction of an ambient smooth bump;
its pullback through a smooth chart transition remains smooth up
to the boundary. This should be tested first for one compact set
inside one half-space chart. It is the first step toward the
boundary-compatible partition required in milestone 5a.

## Dimension one

The positive-boundary-dimension interface above assumes an
`'e::euclidean_space` tangential model. Isabelle's
`euclidean_space` class has a nonempty basis, so it does not cover
a zero-dimensional tangential space. Use a separate one-dimensional
chart model `real` with half-line `{t. 0 ≤ t}`. Its boundary is a
discrete carrier, and integration over it is a signed finite sum.
Keep its orientation convention consistent with the checked
`halfline_FTC_compact_support` theorem.
