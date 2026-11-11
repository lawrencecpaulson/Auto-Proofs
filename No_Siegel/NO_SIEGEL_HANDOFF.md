# No_Siegel handoff — 11 November 2026

## Verified checkpoint

`No_Siegel` builds with Isabelle2026 and AFP `devel`. The latest full
build completed on 11 November after integrating the Section 5
odd-prime determinant and valuation theories:

```
isabelle build -b -d /Users/lawrpau/isabelle/afp/devel/thys -D . No_Siegel
Finished No_Siegel (0:10:29 elapsed time, 0:33:07 cpu time)
```

The preceding archimedean and Frobenius checkpoint is commit `2671f50`.
The character-classification bridge through
`primitive_real_character_fundamental_discriminant` was committed as
`371b8b0`. It supplies the conditional quadratic-character locale for
every primitive real Dirichlet character. Section 3 row independence,
including the paper's lattice and parameter instances, was checked
before this checkpoint.

The new Section 4 theories in `ROOT` establish:

- `Quadratic_Gram.thy`: integral quadratic derivative rows, the trace
  pairing, and positivity of its quadratic form.
- `Gram_Determinant.thy`: an integer Gram matrix and positive
  paper-parameter determinant, with Cauchy–Binet nonnegativity.
- `Gram_Hadamard.thy`: the determinant bound by the product of squared
  feature-row norms.
- `Archimedean_Rows.thy`, `Archimedean_Entry_Bound.thy`, and
  `Archimedean_Conjugate.thy`: lattice coordinates, derivative entries,
  and the two quadratic embeddings.
- `Archimedean_Feature_Bound.thy` and
  `Archimedean_Determinant_Bound.thy`: the paper-parameter squared row
  and determinant product bounds.
- `Archimedean_Log_Bound.thy`: the displayed Section 4 logarithmic
  determinant estimate, `green_paper_gram_archimedean_log`.

The two-embedding argument gives factor `2 N² J` inside the logarithm
of the row bound. `STATEMENT_AUDIT.md` records why this needs a distinct
argument from the row norm printed in Green's paper.
`Archimedean_Parameter_Bound.thy` now proves
`green_paper_gram_archimedean_parameter`, the explicit bound
`log det G ≤ (1/2 + 11/C) X² J log X`. The full `No_Siegel` session
built successfully after this addition on 11 November.
`Inert_Frobenius.thy` is also integrated and checked. It proves that
for an odd inert prime `p` and natural lattice coordinates `x,y`,
`(x+y√d)^p-(x-y√d)` is a multiple of `p` in `ℤ[√d]`.
`Inert_Rows.thy` proves that the transformed derivative entries lie in
`p^h ℤ[√d]`, expands each transformed row as the original row plus
rows with smaller first index, and proves `p^(2∑ h)` divisibility for
the transformed Gram determinant. `Inert_Transform_Order.thy`,
`Gram_Transformation.thy`, `Row_Coeff_Transform.thy`, and
`Inert_Determinant_Transfer.thy` identify the row change as a
determinant-one triangular matrix and transfer this divisibility to
Green's **original** Gram determinant for odd inert primes. These
Section 5 theories passed the full `No_Siegel` build on 11 November
and were committed as `7bc173a`. `Inert_Valuation.thy` also proves the explicit
valuation lower bound when the determinant is nonzero, including at
Green's paper parameters where positivity has already been checked.

## Section 6 completion

`Inert_Prime_Sums.thy` proves that the possible inert prime `2` changes
the weighted inert-prime sum by less than `1`.
`Prime_Valuation_Log.thy` proves the generic weighted prime-valuation
upper bound for a positive integer determinant. Both theories checked
separately under `HOL-Analysis` on 11 November.
`Inert_Valuation_Sum.thy` connects that bound to Green's odd inert
valuation theorem; the user checked it in jEdit on 11 November.
`Inert_Weighted_Floor.thy` applies the existing floor-sum lemma to
this valuation bound and substitutes the archimedean determinant
bound at Green's parameters. The user checked it in jEdit and fixed
its `ppos` proof. `Inert_Prime_Formula.thy` states the exact
reciprocal-prime, theta, and inverse-square expansions and passed a
standalone `HOL-Analysis` check. Its checked algebra lemmas rearrange
the comparison, apply conditional prime-sum bounds, deduce the
`8C + 4` constant, and bound `X/(X div C)` by `2C`.
`Inert_Prime_Comparison.thy` combines the expansions with the
paper-parameter weighted floor theorem and was checked in jEdit.
`Inert_Prime_Rearranged.thy` states the resulting paper-parameter
weight inequality and was checked in jEdit.
`Inert_Prime_Conditional.thy` applies these to state the paper's
`8C + 5` bound under three explicit prime-sum estimates and was
checked in jEdit. `Inert_Prime_Analytic.thy` proves those three estimates:
it uses AFP's first Mertens theorem and theta bound, and bounds the
inverse-square sum by AFP's prime-power remainder estimate
`9/pi^2 < 2`. The analytic bridge passed an isolated Isabelle2026
check with the newly built `Prime_Number_Theorem` heap.
`Inert_Prime_Bound.thy` assembles the parameter bound, removes the
choice of lattice enumeration, gives the explicit threshold `q >= 2C`,
specialises to `C = 64`, and applies the character-classification
bridge. All new Section 6 theories are uncommitted.
The new theories have no standalone `unfolding` commands;
`apply_timeout` does not bound such commands.

The integrated `No_Siegel` build succeeded with Isabelle2026 and AFP
`devel` after all Section 6 additions:

```
isabelle build -v -b -j 2 -d /Users/lawrpau/isabelle/afp/devel/thys -D . No_Siegel
Finished No_Siegel (0:11:37 elapsed time, 0:36:44 cpu time)
```

The final theorem is `green_primitive_real_inert_bound`, valid for each
even `C >= 2` and `q >= 2C`; `green_primitive_real_inert_bound_64`
is the fixed-scale instance. The Section 6 duplication review
factored the repeated finite-prime comparison into
`green_odd_inert_sum_le_all_primes`. The other repeated assumptions
belong to distinct intermediate estimates and remain explicit.
`Finite_Grid.thy` now uses the direct natural-number cast rule in place
of a slow `metis` call; it passed the integrated build. A source scan
found no `sorry`, `oops`, or `admit` in the project theories.

`PLAN.md` records AFP staging as the next task after No_Siegel.
`STATEMENT_AUDIT.md` records the paper corrections. The external
zero-sensitive Dirichlet-L estimate and its zero-free deduction remain
outside the required paper theorem.

## Repository scope

The Stokes edits in `../Stokes/CLEANUP.md` and
`../Stokes/Green_AC_Winding.thy` are independent work and are excluded
from this No_Siegel checkpoint.
