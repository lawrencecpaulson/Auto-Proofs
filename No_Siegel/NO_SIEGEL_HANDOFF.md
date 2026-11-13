# No_Siegel handoff — 12 November 2026

## Verified checkpoint

`No_Siegel` builds with Isabelle2026 and AFP `devel`. The latest full
build completed on 12 November after the theory cleanup:

```
isabelle build -v -b -j 2 -d /Users/lawrpau/isabelle/afp/devel/thys -D . No_Siegel
Finished No_Siegel (0:35:25 elapsed time, 0:38:51 cpu time)
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
- `Archimedean_Conjugate.thy`: lattice coordinates, derivative entries,
  and the two quadratic embeddings.
- `Archimedean_Log_Bound.thy`: the paper-parameter squared row and
  determinant product bounds, and the displayed Section 4 logarithmic
  estimate `green_paper_gram_archimedean_log`.

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
`Gram_Transformation.thy`, and `Inert_Determinant_Transfer.thy`
identify the row change as a
determinant-one triangular matrix and transfer this divisibility to
Green's **original** Gram determinant for odd inert primes.
`Inert_Determinant_Transfer.thy` also proves the explicit valuation
lower bound when the determinant is nonzero. The original Section 5
chain passed the full `No_Siegel` build on 11 November and was
committed as `7bc173a`.

## Section 6 completion

`Prime_Valuation_Log.thy` proves that the possible inert prime `2`
changes the weighted inert-prime sum by less than `1`, and proves the
generic weighted prime-valuation upper bound for a positive integer
determinant. `Inert_Prime_Conditional.thy` connects that bound to
Green's odd inert valuation theorem, applies the floor-sum lemma,
and substitutes the archimedean determinant bound at Green's
parameters. `Inert_Prime_Formula.thy` states the exact
reciprocal-prime, theta, and inverse-square expansions and passed a
standalone `HOL-Analysis` check. Its checked algebra lemmas rearrange
the comparison, apply conditional prime-sum bounds, deduce the
`8C + 4` constant, and bound `X/(X div C)` by `2C`.
`Inert_Prime_Conditional.thy` also combines these expansions, states
the paper-parameter weight inequality, and obtains the paper's
`8C + 5` bound under three explicit prime-sum estimates.
`Inert_Prime_Analytic.thy` proves those three estimates:
it uses AFP's first Mertens theorem and theta bound, and bounds the
inverse-square sum by AFP's prime-power remainder estimate
`9/pi^2 < 2`. The analytic bridge passed an isolated Isabelle2026
check with the newly built `Prime_Number_Theorem` heap.
`Inert_Prime_Bound.thy` assembles the parameter bound, removes the
choice of lattice enumeration, gives the explicit threshold `q >= 2C`,
specialises to `C = 64`, and applies the character-classification
bridge. The completed theorem was committed as `eba36bb`.

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

## Cleanup (12 November 2026)

Related short theories were folded into their successors within the
same proof stage: local character structure, row parameters, Section 4
archimedean bounds, Section 5 determinant transfer and valuation, and
Section 6 prime comparisons. The theory count fell from 46 to 30;
the count at or below 10 KB fell from 35 to 13. The analytic prime
estimates remain in `Inert_Prime_Analytic.thy` because combining them
with the final bound changes Isabelle's implicit sum-structure context.

All `apply_timeout` declarations were removed. Two unused
paper-parameter valuation specializations and a repeated syntax
declaration were removed. The generic valuation lemma remains beside
the Section 5 determinant-transfer proof; brief one-use intermediate
facts in it now use cartouche references. The repeated parameter
assumptions, symmetric local-character cases, and successive prime
estimates were reviewed; their different conclusions remain explicit.
The full session build above checked the consolidated development.

## Repository scope

The Stokes edits in `../Stokes/CLEANUP.md` and
`../Stokes/Green_AC_Winding.thy` are independent work and are excluded
from this No_Siegel checkpoint.
