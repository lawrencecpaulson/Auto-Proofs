# Duplication cleanup (2026-10-27)

`Smooth_Cutoff.thy` now holds the shared compact-collar and finite
compact-chart-refinement proofs formerly repeated in
`One_Dimensional_Partition.thy` and
`BoundaryIntegration/Body_Local_Integration.thy`.

The coordinate-independent chartwise `C1` binary closure proof and
finite-partition construction are also in `Smooth_Cutoff.thy`. The
one-dimensional and boundary atlas theories retain their own
chart-specific definitions and closure lemmas, and interpret the shared
`scalar_partition_algebra` locale. Both theorem names remain available
in their atlas contexts.

`Forms.thy` holds the common Piola cancellation proof. The ordinary and
halfspace Piola theorems each establish the inverse-field derivative in
their own domain and invoke that proof.

`BoundaryIntegration/Single_Chart.thy` now uses two fixed contexts for
the boundary-chart and interior-chart theorem groups. These collect the
shared support and differentiability premises once while retaining the
exported theorem assumptions. The separate contexts preserve the
extra no-face premise of the interior results.

`Basis_Fubini.thy` and `Chart_Local.thy` repeat the finite-sum integration
argument but use different normal derivative hypotheses. A generic
integration lemma would shorten the two proofs only slightly after
stating its integrability and integral premises, so that extraction was
left for a later pass.

The Stokes session and document built successfully after these changes.
