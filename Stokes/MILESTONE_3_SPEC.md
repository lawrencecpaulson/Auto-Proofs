# Milestone 3: integration on oriented manifolds without boundary

This is the mathematical specification. Its main deliverable is now
checked in `Manifold/Stokes_Manifold_Integration.thy` against
Isabelle2026-RC4 and AFP `Smooth_Manifolds`. The independent model is Gualtieri,
`Gualtieri.pdf`, Proposition 6.15 and Theorem 6.16 (PDF pages 57-58).

## Deliverable

For an oriented smooth `n`-manifold without boundary, construct a linear
functional on compactly supported smooth top forms

    integral_top : Omega_c^n(M) -> real

characterised by the **local chart rule**: if `c` is an
orientation-preserving chart and `alpha` is supported compactly inside
its domain, then its manifold integral equals the ordinary Euclidean
integral of the coefficient of `alpha` in `c` coordinates. Prove
existence, independence of chart and partition of unity, and uniqueness
from this rule. This is a useful endpoint even before Stokes is stated.

## Minimal orientation and form interfaces

- Start with the AFP `c_manifold` at a regularity sufficient for smooth
  chart transitions and partitions of unity (ideally `k = infinity`),
  and a chosen family of oriented charts covering its carrier. On
  every overlap, the derivative of the
  transition `g = d o inv_chart c` has positive determinant.
  Orientation reversal may be represented by changing the chosen
  family with a reflection in one Euclidean coordinate.
- A minimal top form can be represented by its coefficient function
  `alpha_c : codomain c -> real` in each oriented chart. On an overlap,
  the compatibility equation is

      alpha_c(x) = det(Dg(x)) * alpha_d(g(x)).

  The full alternating-tensor representation can later be connected to
  this coordinate interface. Milestone 3 does not require every form
  degree or exterior differentiation.
- Specify compact support relative to the manifold carrier and prove
  that a top form supported inside one chart has compactly supported
  coordinates in that chart.

## Proof obligations in order

1. **Signed chart change.** For a top-form coefficient supported in the
   overlap of two oriented charts, use
   `Change_Of_Vars.integral_change_of_variables` on the chart
   transition. Its factor is `abs(det Dg)`; oriented transitions have
   `det Dg > 0`, so it agrees with the top-form compatibility equation.
   Check measurability of the coordinate overlap, injectivity, and
   integrability explicitly.
2. **Local functional.** Define the integral for forms supported in
   one oriented chart. Prove that another oriented chart gives the
   same value when both apply.
3. **Global functional.** Choose the existing AFP smooth partition of
   unity subordinate to oriented chart domains. If `K` is the compact
   support of `alpha`, `Analysis_More.locally_finite_compactD` implies
   that only finitely many partition supports meet `K`. Integrate
   the finite family `rho_i * alpha` chart by chart.
4. **Independence.** Given two choices of partition and charts, expand
   both by their common finite refinement
   `rho_i * sigma_j * alpha`. Apply the signed chart-change lemma
   termwise and sum. The same decomposition proves the local chart
   rule and uniqueness.
5. **Basic consequences.** Prove linearity, vanishing for the zero
   form, and sign reversal when the manifold orientation is reversed.

## Checked implementation

`Stokes_Integration` proves positive-Jacobian change of variables,
finite refinement of two partitions, and absolute integrability of a
continuous compactly supported coefficient. `Stokes_Manifold` defines
`oriented_c_manifold`, compatible top-form coefficient families,
`admissible_top_partition`, and `integral_top`. It proves:

- smooth partitions subordinate to oriented chart domains exist for
  compact support;
- localized chart integrals and any two smooth chart partitions agree;
- the local chart rule and uniqueness among extensional linear
  functionals with that rule;
- addition, scalar multiplication, and the zero-form value.

The coefficient family represents a form only on oriented chart
codomains; `integral_top_unique` explicitly requires extensionality on
those values. A separate sign-reversal theorem comparing two chosen
orientations has not been proved. The all-degree alternating-form
representation remains the optional Milestone 1b extension.

## Existing Isabelle/AFP ingredients

- `Smooth_Manifolds/Chart.thy`: open chart domains and codomains,
  homeomorphism, and chart inverse.
- `Smooth_Manifolds/Differentiable_Manifold.thy`: smooth transitions and
  the `c_manifold` locale.
- `Smooth_Manifolds/Partition_Of_Unity.thy:365`:
  `partitions_of_unityE`, providing smooth functions with locally
  finite closed supports subordinate to an open cover.
- `Smooth_Manifolds/Analysis_More.thy:735`:
  `locally_finite_compactD`, giving the finite index set used above.
- `HOL/Analysis/Change_Of_Vars.thy:3691`:
  `integral_change_of_variables`, with absolute determinant.
- `HOL/Analysis/Determinant_Linear_Function.thy`:
  `eucl_det_conv_matrix_det`, relating the linear-map determinant in
  change of variables to the Cartesian matrix determinant in form
  pullback.
- `HOL/Analysis/Equivalence_Lebesgue_Henstock_Integration.thy:954`:
  `set_borel_integral_eq_integral`, if chart integration is presented
  with Lebesgue integrals while using the existing gauge-integral
  change-of-variables theorem.

## Decisions and constraints

- Keep the theorem on the existing no-boundary AFP `c_manifold`.
  The boundary-chart work of milestone 4 is a separate interface.
- Use compactly supported forms from the start. This makes the finite
  partition-of-unity argument and chart integrability precise on a
  noncompact manifold.
- State the integral first for chart-compatible top-form coefficients.
  This isolates the measure-theoretic construction from the larger
  differential-form algebra.
- The easiest `Change_Of_Vars` theorem is expressed with Isabelle's
  gauge `integral`; milestone 2 uses Lebesgue integrals.
  Establish their equivalence under compact-support integrability
  rather than silently switching notation.
