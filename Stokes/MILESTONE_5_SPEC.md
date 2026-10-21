# Milestone 5: boundary-compatible integration and single-chart Stokes

Deliverables 5a and 5b are checked in the current coordinate-family
interface. The 5a construction is in
`BoundaryIntegration/Stokes_Body_Local_Integration.thy` and
`BoundaryIntegration/Stokes_Smooth_Partition.thy`.
It depends on milestone 1a's form interface, milestone
2's local half-space theorem, milestone 3's oriented integration
construction, and milestone 4's boundary charts and orientation.
Sadun, `Sadun.pdf`, Theorems 1.1 and 2.1 (PDF pages 1-3), and
Gualtieri, `Gualtieri.pdf`, Theorems 6.16 and 6.18 (PDF pages 57-59),
give the independent mathematical model.

## Deliverable 5a: integration on a manifold with boundary

For an oriented smooth `n`-manifold with boundary, define a linear
integral of compactly supported smooth `n`-forms over `M`. Define a
linear integral of compactly supported top forms over `boundary M`,
using the orientation induced in milestone 4. Prove both integrals
independent of charts and partitions of unity, and characterised by
their oriented local chart rules.

For an `n`-form `alpha` supported compactly inside an oriented boundary
chart `c`, let `alpha_c` be its top coefficient. Its chart rule is

    integral_M alpha = integral_(codomain c subset H) alpha_c.

On the boundary, restrict a near-top form `omega` by the boundary
inclusion `j`. With `t` the **first** coordinate, its coefficient in
the induced boundary orientation is `-a_1(0,y)` when `a_1` is the
coefficient omitting `dt`. Thus the boundary chart rule reads

    integral_(boundary M) (j* omega)
      = - integral_(boundary-coordinate domain) a_1(0,y)

for a form supported in that chart. The dimension-one instance is a
signed finite sum over boundary points, and needs an explicit
zero-dimensional integral.

Proof obligations:

1. Show `boundary M` is closed in `M`. Then restriction of a compactly
   supported form has compact support on the boundary.
2. For chart change in `H`, first try
   `Change_Of_Vars.integral_change_of_variables` directly on the
   relatively open, measurable subset of `H`: its derivative
   hypothesis is stated *within* the source set, and the smooth
   ambient extension supplies that derivative. Verify injectivity,
   absolute integrability, and the positive determinant explicitly.
   If the direct formulation is awkward in Isabelle, prove that the
   boundary hyperplane is Lebesgue null, apply change of variables
   on the open interior, and restore the boundary by nullity.
3. Transfer between the gauge integral used by
   `HOL/Analysis/Change_Of_Vars.thy:3691` and the Lebesgue integral
   used for the local theorem, using
   `HOL/Analysis/Equivalence_Lebesgue_Henstock_Integration.thy:954`
   on the compactly supported coordinate functions.
4. Construct compactly supported chart cutoffs on relatively open
   half-space chart domains. The checked construction uses finite
   compact chart refinements, ambient Euclidean smooth bumps, and
   a finite product formula for partition weights. Each weight is
   chartwise C¹ under the C² atlas hypotheses.
5. Use finite refinements and signed chart change, as in milestone 3,
   to prove independence and linearity for both integrals.

The boundary construction must use the relative-carrier chart design
chosen in milestone 4. In particular, an empty boundary should give
zero boundary integral without requiring a nonempty boundary type.

Checked: boundary and body overlap change of variables, compact-support
integrability, independence of arbitrary finite admissible partition
sums, and unconditional chart rules for chart-supported coefficient
families. `body_partition_exists` and `boundary_partition_exists`
provide finite partitions for arbitrary compact support.
`body_C1_partition_exists` and `boundary_C1_partition_exists` strengthen
these to nonnegative chartwise C¹ weights. The shared theorem
`common_C1_partition_integral_rules` evaluates both integrals with
one such body partition when their supports lie in a common compact
set. Both integrals are additive and homogeneous. The boundary
integral is zero on the empty boundary, and the separate one-dimensional
half-line model has an explicit signed finite-sum boundary integral.
The positive-dimensional atlas supplies C² positive transitions,
which suffice for chartwise C¹ weights. Its boundary is a carrier
set, so it can be empty.

## Deliverable 5b: Stokes for a form supported in one chart

Let `omega` be a smooth `(n-1)`-form with compact support contained in
the domain of one chart, so its coordinate support is compactly inside
that chart. Prove

    integral_M (d omega)
      = integral_(boundary M) (j* omega).

For an **interior chart**, extend the coordinate form by zero to the
whole Euclidean model. Its derivative has compact support, Euclidean
compact-support Stokes gives integral zero, and the boundary
restriction vanishes. For a **boundary chart**, extend by zero on the
half-space and apply milestone 2. Use the coefficient formula of
milestone 1a, naturality of `d`, and the boundary orientation rule
above to identify the chart integrals.

The zero-extension lemma in `MILESTONE_2_SPEC.md` must guarantee the
required differentiability across the edge of the chart's coordinate
domain. A partition bump function may first shrink the support to a
smaller chart neighbourhood; compact containment then gives an open
collar where the zero extension is identically zero. The form need
not vanish at the actual manifold boundary `t = 0`.

Checked in `BoundaryIntegration/Stokes_Single_Chart.thy`:
`Stokes_boundary_chart_form_C1` proves the coordinate identity in
each atlas boundary chart. `Stokes_boundary_chart_integral_top_C1`
identifies its right side with `integral_boundary_top` for a
compatible, compactly supported boundary coefficient family when
an admissible partition is supplied.
`Stokes_boundary_chart_gauge_C1` converts the body side to the gauge
integral when its Lebesgue integrability is available.
`integral_boundary_top_normal_sign` checks the sign
`- integral_y fst (A (0,y))`. For an interior chart with empty face,
`Stokes_interior_chart_integral_top_C1` gives equality with the zero
boundary coefficient integral. These statements apply to any
coordinate form meeting their C¹ and support hypotheses, including
a partition-weighted form when those hypotheses hold.
The partition-sum body and boundary integrals are defined below;
their chart rules on chart-supported forms complete the local
equation.

Update, 21 October 2026: `Stokes_Body_Local_Integration.thy` now has
a checked compact-support bridge from an atlas-wide family of
near-top coordinate fields to its interior exterior coefficient and
boundary restriction. It also defines single-chart body and
boundary integrals with conditional chart rules. The checked
`Stokes_single_boundary_chart_local_integrals_C1` gives their
Stokes equality under explicit coefficient compatibility and
regularity assumptions. A stronger theorem,
`Stokes_chart_supported_near_top_C1`, derives all three compact
support witnesses from one compact support set and is now
Isabelle-checked. It also derives body integrability and body
coefficient compatibility from the interior pullback law.
The packaged Stokes theorem now derives boundary coefficient
compatibility from the interior pullback law and differentiability at
the boundary: the interior law first transfers to geometric local
atlas extensions and then extends to the face by continuity. The checked
`Stokes_chart_supported_form_C1` directly integrates the exterior
and boundary coefficients of a single compactly supported
near-top coordinate family. A general smooth-form interface must
still supply the coordinate family and its interior pullback law.
`body_single_chart_partition_exists` and
`boundary_single_chart_partition_exists` construct one-chart
cutoffs. `Stokes_chart_supported_form_integrals_C1` is the checked
Milestone 5b statement in terms of `integral_body_top` and
`integral_boundary_top`. Both partition-defined integrals agree
with their single-chart versions for chart-supported forms.
Milestone 5a supplies finite partitions and partition independence
for arbitrary compact support.

## Completion criteria

- Both integrals exist for compactly supported top forms, obey the
  local chart rules, and are independent of charts and partitions.
- The boundary chart rule has the first-coordinate `-1` sign, and
  dimension one and empty boundary have explicit meanings.
- Chart-local Stokes is proved for any smooth near-top form with
  compact support inside one interior or boundary chart.
- The chart-local statement applies to `rho * omega` for each
  subordinate partition function `rho` used in milestone 6.
