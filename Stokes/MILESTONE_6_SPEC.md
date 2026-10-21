# Milestone 6: global compact-support Stokes

The compact-support gluing theorem is checked in
`BoundaryIntegration/Stokes_Global_Gluing.thy` for the existing
`smooth_oriented_C2_halfspace_atlas` coordinate-family interface.
The model space `real × real^'n` has dimension at least two. The
one-dimensional atlas case remains outside that interface.
`Stokes_One_Dimensional_Chain.thy` checks Stokes for finite oriented
interval presentations, including signed endpoint cancellation and
the closed-chain case. It also checks a possibly infinite interval
collection with finitely many active pieces. The half-line and
whole-line compact-support models are checked.
`Stokes_One_Dimensional_Atlas.thy` checks the local theorem on a
relatively open half-line chart and the finite boundary-partition
sum. `Stokes_One_Dimensional_Atlas_Gluing.thy` checks their
finite-atlas combination. `Stokes_One_Dimensional_Manifold.thy`
defines an oriented C¹ half-line atlas and its signed boundary.
`Stokes_One_Dimensional_Partition.thy` constructs finite C¹
partitions on compact subsets. `Stokes_One_Dimensional_Regularity.thy`
derives continuous one-sided coordinate derivatives of localized
forms. `Stokes_One_Dimensional_Global.thy` checks
`exact_body_integral_stokes`, partition independence, compact-support
independence, and the empty-boundary and compact-carrier corollaries.
Its integral is defined for exact one-forms by chartwise derivatives
of partition-weighted primitives. A general one-dimensional
integral for arbitrary one-forms, and a uniform theorem using the
same integral interface in every dimension, remain separate work.
The proof uses milestone 5's integrals and chart-local Stokes.
The independent proof pattern is Sadun, `Sadun.pdf`, Theorem 2.1
(PDF pages 2-3), and Gualtieri, `Gualtieri.pdf`, Theorem 6.18
(PDF pages 58-59).

## Main statement

Let `M` be an oriented smooth manifold with boundary, of positive
dimension `n`, and let `omega` be a smooth compactly supported
`(n-1)`-form, smooth up to the boundary in the ambient-extension
sense of milestone 4. With `j : boundary M -> M` the inclusion and
the outward-normal-first boundary orientation, prove

    integral_M (d omega)
      = integral_(boundary M) (j* omega).

Compact support is imposed on `omega`, so `M` may be noncompact. The
integrals and pullback have the meanings fixed in milestones 1a and 5.
The dimension-one case uses a signed finite sum on its discrete
zero-dimensional boundary.

## Finite gluing proof

Choose a smooth locally finite partition of unity `{rho_i}` subordinate
to oriented chart domains. If `K = supp omega` is compact, AFP
`Smooth_Manifolds/Analysis_More.thy:735`
(`locally_finite_compactD`) gives a finite index set `I_K` of
partition supports meeting `K`. Prove the finite decomposition

    omega = sum_(i in I_K) rho_i * omega

globally: at points outside `K`, each term vanishes; at points in `K`,
the partition sums to one. Each term is smooth, has compact support
inside its chart, and therefore satisfies milestone 5b.

Then use linearity and locality of `d`, linearity of both integrals,
and commutation of boundary restriction with finite sums:

    integral_M (d omega)
      = sum_(i in I_K) integral_M (d (rho_i * omega))
      = sum_(i in I_K) integral_(boundary M) (j* (rho_i * omega))
      = integral_(boundary M) (j* omega).

There is no need to expand `d (rho_i * omega)` by a Leibniz rule. The
finite decomposition and linearity of `d` are sufficient. Smoothness
and support of the product are still needed to invoke chart-local
Stokes.

## Small but meaningful corollaries

- If `boundary M` is empty, `integral_M (d omega) = 0`.
- For a compact `M`, every smooth form has compact support relative
  to its carrier, yielding the usual compact-manifold theorem.
- In dimension one, the statement becomes the fundamental theorem
  of calculus with signed endpoint values.
- The earlier local half-space theorem is recovered by taking `M`
  to be the Euclidean half-space, once that example is instantiated
  in the manifold-with-boundary interface.

## Completion criteria

1. **Checked for the atlas coordinate family:** a finite chartwise C¹
   partition and the form, exterior-coefficient, and boundary-coefficient
   decompositions, including support that meets the boundary.
2. **Checked:** reflected ambient extensions of each partition weight
   give the localized forms the precise differentiability and derivative
   continuity needed by milestone 5b.
3. **Checked:** `global_stokes`,
   `global_stokes_empty_boundary`, and
   `global_stokes_compact_carrier`.
4. **Checked in the one-dimensional atlas interface:**
   `exact_body_integral_stokes` proves the compact-support theorem
   for an arbitrary oriented C¹ half-line atlas, using a separately
   defined integral of exact one-forms. Its partition and
   compact-support independence are checked. The interval-chain,
   periodic, half-line, and whole-line presentations also check.
   A general one-form integral and comparison with it remain open.

## One-dimensional atlas bridge

A half-line coordinate points inward at every boundary point. On an
oriented compact interval it agrees with the orientation at the left
endpoint and disagrees at the right endpoint. Thus the
all-positive-transition atlas used in higher dimensions cannot encode
both endpoint signs in dimension one. A one-dimensional atlas needs
a chart orientation sign `eps i` and a boundary sign `- eps i`.

The atlas, oriented coordinate-change integral rule, finite C¹
partition, localized derivative regularity, face-point
identification, and finite-atlas gluing theorem are checked. The
exact-form body integral is constructed from this data and proved
independent of partition and support choice. Independence here
follows from the local fundamental theorem and signed boundary
gluing. A general one-form integral would instead need its own
common-refinement argument on overlaps; the checked oriented
coordinate-change rule supplies that analytic step.

Further variants for noncompactly supported integrable forms or
cubical chains are separate developments, not requirements for this
compact-support theorem.
