# Original offline plan and checked outcome

This was the source-based proof plan before Isabelle was available.
`PROOF_STATUS.md` records the results now checked by Isabelle2026-RC4.
The analytic chart-local coordinate theorem is complete; the genuine
differential-form and manifold integration work remains.

## Analytic proof spine for milestone 2

The key lemma is a coordinate-slice fundamental theorem of calculus:

> For a continuously differentiable scalar function on a rectangular box,
> the integral of its partial derivative in coordinate `i` equals the
> integral of the function on the upper `i`-face minus its integral on the
> lower `i`-face.

It follows by splitting off coordinate `i`, applying one-dimensional FTC
to each slice, and integrating the resulting equality over the remaining
coordinates. Isabelle2026_RC4 has candidate ingredients:

- `Interval_Integral.interval_integral_FTC_finite` for one-dimensional
  Lebesgue integration (line 599 of `Interval_Integral.thy`).
- `Equivalence_Lebesgue_Henstock_Integration.integral_FTC_atLeastAtMost`
  for a closed real interval (line 930).
- `Henstock_Kurzweil_Integration.integral_prod_continuous` for a
  product of two Euclidean boxes (line 6853).
- `Lebesgue_Measure.lborel_prod` (line 1180) and
  `Bochner_Integration.integral_fst` (line 3156) for Lebesgue integration
  on a product; `Fubini_integral` can swap the integration order.

Use Lebesgue set integrals for the target theorem. The gauge integral on
boxes remains a fallback if its product rule gives a much shorter proof;
that route would require a conversion lemma.

The original box-based route was:

1. Multiply its `i`-th instance by `(-1)^(i-1)` and sum over the finite
   coordinate index set. This is coordinate box Stokes, with the same
   signed-coefficient convention as the Lean repository.
2. Given coefficients supported compactly in
   `H = {(t,y) | t >= 0}`, choose a box large enough that all outer faces
   miss the support. Box Stokes leaves only the `t = 0` face, with sign
   minus. This is the half-space theorem in `README.md`.
3. Prove a zero-extension lemma for coefficients compactly supported in
   a relatively open subset of `H`. This yields the chart-local version.

The slice lemma is also a useful standalone result. It is the part supplied
by mathlib's divergence theorem in
`LeanStokes/CubeStokes/Theorem.lean`; the three-line Lean box proof starts
*after* that analytic work.

## Choices made in the checked development

- **Coordinates and dimension one.** The checked half-space theorem uses
  `real × 'a::euclidean_space` and a finite subset of `Basis` for
  tangential directions. `Stokes_Local.thy` handles dimension one
  separately.
- **Regularity.** The chart-local theorem assumes directional
  derivatives and continuous derivative coefficients on the chart
  image. The normal derivative at `t = 0` is one-sided. Zero extension
  preserves exactly these laws.
- **Signs.** With `H = {t >= 0}` and orientation
  `dt /\ dy_1 /\ ... /\ dy_(n-1)`, the `t = 0` face has sign `-1`.
  Check against the one-dimensional formula
  `integral_0^R a'(t) dt = a(R) - a(0)` and the two-dimensional form
  `P(t,y) dy + Q(t,y) dt`.
- **Scope.** The extracted Lean `HalfSpace.lean` has definitions and
  basic inclusions but no local half-space Stokes theorem. Its singular
  cube and chain results do not need to be ported to establish this
  milestone.

## Outcome and next dependency

The checked proof uses direct normal FTC plus tangential Fubini, then
proves chart-local zero extension. It does not require a global
ambient `C^1` extension near the whole half-space or an arbitrary
coordinate-face representation. `Stokes_chart_form_interface` states
the two pointwise laws that milestone 1 must establish for actual
forms and pullbacks.

`MILESTONE_2_SPEC.md` contains the precise mathematical signatures and
the checked proof decomposition.
