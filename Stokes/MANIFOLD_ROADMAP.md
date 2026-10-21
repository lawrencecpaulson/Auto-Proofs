# Dependencies after the local theorem

This is an offline architecture sketch for compactly supported Stokes on an
oriented smooth manifold with boundary. It records mathematical obligations,
not checked Isabelle declarations.

## Intended final statement

For a positive-dimensional oriented smooth manifold `M` with boundary and
a compactly supported smooth form `omega` of degree `dim M - 1`,

    integral_M (d omega) = integral_(boundary M) (restrict omega).

The boundary uses the outward-normal-first orientation. Compact support
allows `M` and its boundary to be noncompact. The one-dimensional case
needs an explicit zero-dimensional boundary integral, likely a finite sum.

## Geometry and algebra

1. **Boundary charts.** AFP `Smooth_Manifolds/Chart.thy` charts into open
   subsets of a whole Euclidean space. Define an interface for charts
   into *relatively open* subsets of `H = {t >= 0}`. Transition maps must
   have smooth ambient extensions near boundary points and smooth
   inverses. This is separate from the current `c_manifold` locale.
2. **Boundary manifold.** Restrict boundary charts to `t = 0`.
   Prove their tangential transitions are smooth and their domains
   cover the boundary. The restricted domains are open relative to
   the boundary, which generally is not open in the original
   manifold's ambient type; a relative-carrier chart interface is
   needed. A type model `real * 'e::euclidean_space` makes the
   boundary model `'e` explicit for dimensions at least two.
3. **Orientation.** Ambient oriented transitions have positive
   determinant. At a boundary point, the transition derivative is
   block triangular: the boundary-defining coordinate has zero
   tangential derivatives and positive normal derivative. Therefore
   positivity of the ambient determinant implies positivity of the
   tangential determinant. This proves that the induced boundary
   orientation is chart independent.
4. **Forms.** For the shortest path to Stokes, only degrees `dim M - 1`
   and `dim M`, scalar multiplication, pullback under chart changes,
   and the derivative from near-top to top are strictly needed.
   A full all-degree exterior algebra would be a valuable later
   extension. The coordinate model from the Lean box development
   suggests a minimal near-top interface.

## Integration and gluing

5. **Oriented chart integration.** Milestone 3 constructs this on
   existing boundaryless AFP manifolds. Milestone 5 adapts it to
   half-space charts and to the relative-carrier boundary manifold.
   Show chart independence using Isabelle's absolute-Jacobian
   change-of-variables theorem together with positivity of oriented
   transition determinants. For half-space chart changes, first work
   in the open interior and then use nullity of the boundary
   hyperplane. Do the same for top forms on the boundary.
6. **Partition of unity.** AFP
   `Smooth_Manifolds/Partition_Of_Unity.thy:365` proves a locally finite
   smooth partition for its existing `c_manifold`. Since that locale
   uses full-space charts, adapt the proof to boundary charts, or
   factor out the topological and bump-function lemmas that do not
   depend on the full-space model.
7. **Chart-local Stokes.** If `omega` is supported in one interior chart,
   its boundary integral is zero and the Euclidean compact-support
   version applies. In a boundary chart, use milestone 2's
   half-space theorem and induced orientation.
8. **Global Stokes.** A compact set meets only finitely many supports
   of a locally finite partition. Thus only finitely many
   `rho_i * omega` are nonzero. Apply chart-local Stokes to each and
   sum, using linearity and the global finite decomposition
   `omega = sum_i rho_i * omega`. No Leibniz rule is needed for this
   last step.

The precise interfaces and completion criteria are in
`MILESTONE_1_SPEC.md` through `MILESTONE_6_SPEC.md`. Milestone 1a is the
minimal form library needed for Stokes; milestone 1b is the optional
full all-degree exterior algebra. Milestone 5a provides both
boundary-compatible integrals and 5b proves the single-chart identity.

## Milestone dependencies and independent results

| Milestone | Depends on | Useful result on its own |
| --- | --- | --- |
| 1a: near-top forms | Euclidean calculus | Pullback and naturality for near-top forms |
| 2: local half-space Stokes | FTC, Fubini, coordinate faces | Slice FTC, box Stokes, half-space formula |
| 3: integration without boundary | 1a top-form interface, existing AFP manifolds | Chart-independent oriented integral |
| 4: boundary geometry | Existing AFP manifold topology and smoothness ideas | Boundary charts and induced orientation |
| 5a: boundary-compatible integration | 1a, 3, 4, change of variables | Integrals on `M` and its boundary |
| 5b: single-chart Stokes | 1a, 2, 4, 5a | Interior and boundary chart identities |
| 6: global Stokes | 5b and a boundary-compatible partition of unity from 5a | Compact-support theorem and corollaries |

Milestones 1a, 2, and 4 can be developed largely independently.
Milestone 3 can proceed on the existing AFP `c_manifold` while
milestone 4's half-space chart design is being settled. The main
representation checkpoint is the near-top pullback/naturality
prototype in 1a; the main geometry checkpoint is a small
relative-carrier boundary-chart prototype in 4. These should be
checked before committing to large libraries built on either design.

## Decision points

- Decide whether to develop general forms first or the minimal
  near-top interface. The latter is enough for the target theorem;
  the former is a larger independent library milestone.
- Decide how the dimension-one boundary integral is represented.
  Isabelle's `euclidean_space` class has a nonempty basis, so a
  zero-dimensional Euclidean model cannot be obtained simply by
  instantiating that class.
- State the smooth-up-to-boundary condition carefully: chart
  transitions and form coefficients need local ambient extensions,
  while the compactly supported local theorem is easiest to prove
  under a global ambient extension hypothesis.
- Keep the local theorem's first-coordinate half-space convention
  throughout. This makes its lower-face orientation sign `-1`.
