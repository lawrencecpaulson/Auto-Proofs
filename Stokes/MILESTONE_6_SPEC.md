# Milestone 6: global compact-support Stokes

This is a mathematical theorem and gluing plan, not a checked Isabelle
theory. It uses milestone 5's integrals and chart-local Stokes.
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

1. The finite index set and global form decomposition are proved,
   including forms whose support meets the boundary.
2. Each summand meets the precise compact-support and regularity
   hypotheses of milestone 5b.
3. The global identity and empty-boundary, compact-manifold, and
   dimension-one corollaries are checked in Isabelle.

Further variants for noncompactly supported integrable forms or
cubical chains are separate developments, not requirements for this
compact-support theorem.
