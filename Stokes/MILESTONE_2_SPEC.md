# Milestone 2: precise mathematical target

This records the mathematical target and proof decomposition for the
all-dimensional coordinate theorem. Isabelle2026-RC4 checks the
half-space identity in `Stokes_Basis_Fubini.thy`, its one-sided normal
version and the chart-local zero-extension lemmas in
`Stokes_Chart_Local.thy`, and the relatively open chart identity in
`Stokes_Chart_Theorem.thy`. `Stokes_Form_Bridge.thy` checks a
conditional form-coefficient integration interface. See
`PROOF_STATUS.md` for exact assumptions, limitations, and build status.

## Convention and theorem

Let `n >= 1`, write `x = (t, y)` in `R x R^(n-1)`, and orient this space by
`dt /\ dy_1 /\ ... /\ dy_(n-1)`. Put `H = {(t, y) | t >= 0}`.
For `i = 1, ..., n`, let `a_i` be `C^1` on an open neighbourhood of `H`.
Suppose the union of their supports *restricted to H* has compact closure
in `H`. Write `D_i a_i` for the derivative in the `i`-th coordinate.
The target identity is

    integral_H (sum_i (-1)^(i-1) * D_i a_i)
      = - integral_R^(n-1) (lambda y. a_1 (0, y)).

The orientation sign is constant `-1` with this first-coordinate
half-space convention. It does not depend on the parity of `n`.
The boundary value `a_1 (0, y)` need not vanish.

For dimension one the statement is the compact-support version of

    integral_{t >= 0} a_1'(t) dt = -a_1(0).

This should be a separate Isabelle corollary if the chosen Euclidean model
has no zero-dimensional tangential type.

## Proof decomposition and checked results

1. **Normal slice FTC.** For a compact Euclidean box `C`, `a <= b`, and
   a `C^1` scalar function `F` near `[a,b] x C`, let
   `D(t,y) = d/dt F(t,y)`. Then

       integral_{[a,b] x C} D
         = integral_C (lambda y. F(b,y))
           - integral_C (lambda y. F(a,y)).

   For each `y` this is one-dimensional FTC. Since `D` is continuous on a
   compact box, Fubini moves the slice integral through the `y` integral.
   The starting Isabelle signature uses
   domain `real * 'e::euclidean_space`, with `C = cbox c d` and Lebesgue
   set integrals. It is also a useful theorem independently of Stokes.

2. **Coordinate slice FTC.** Transport the normal-slice result to any
   coordinate `i` of a finite-dimensional Cartesian Euclidean space.
   The transport must describe both a coordinate permutation and the
   lower-dimensional face integral. These are substantial representation
   obligations; the Lean source handles them with `Fin.succAbove` and
   `Fin.insertNth`. The checked development instead uses Fubini along
   an arbitrary Euclidean basis coordinate, avoiding an explicit
   coordinate permutation.

3. **Coordinate box Stokes.** The two-dimensional rectangular-box
   identity is checked in `Stokes_Local.thy`. The all-dimensional
   half-space proof sums the normal FTC and vanishing tangential
   integrals directly; it does not need an all-dimensional box theorem.

4. **Compact support.** The checked proof derives derivative support,
   integrability, and the vanishing of the tangential integrals
   directly from compact relative support of each coefficient and
   continuity of its stated derivative. The normal FTC gives the
   `-1` boundary sign.

5. **Chart-local zero extension.** The checked lemmas extend
   coefficients supported in compact `K ⊆ V`, with
   `V = H ∩ U` and ambient-open `U`, by zero to `H`. They prove the
   required directional derivative laws at the edge of `V`. The
   normal derivative is one-sided at `t = 0`. Applying the half-space
   result yields `Stokes_relatively_open_chart_C1`.

The checked form interface assumes, but does not prove, that a
pulled-back exterior derivative has the signed derivative-sum
coefficient and that the boundary pullback has coefficient `-P(0,y)`.
Constructing forms and proving those laws belong to milestone 1.

## Low-dimensional sign checks

- In dimension one, a function supported in `[0,R)` gives
  `integral_0^R a'(t) dt = a(R) - a(0) = -a(0)`.
- In dimension two, write `omega = P(t,y) dy + Q(t,y) dt`.
  Then `d omega = (partial_t P - partial_y Q) dt /\ dy`.
  Integrating the `y` derivative gives zero by compact support.
  The boundary contribution is `- integral_y P(0,y)`.
- In dimension three, with ambient orientation `dt /\ dy_1 /\ dy_2`,
  the lower `t` face still has sign `-1`. This is a useful check
  against any parity-dependent boundary sign.

## Integral convention

Use Lebesgue integrals as the target convention. The local Isabelle
library contains `lborel_prod`, Fubini for `lborel`, and
`integral_FTC_atLeastAtMost`, so the normal-slice lemma can be proved
without changing integral notions. The gauge-integral lemma
`integral_prod_continuous` remains a fallback. If used, transfer to
Lebesgue integrals with the lemmas in
`Equivalence_Lebesgue_Henstock_Integration.thy`.

The checked proof uses `lborel` set integrals throughout.
