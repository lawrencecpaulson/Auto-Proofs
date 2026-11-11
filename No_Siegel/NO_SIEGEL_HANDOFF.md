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
and are uncommitted. `Inert_Valuation.thy` also proves the explicit
valuation lower bound when the determinant is nonzero, including at
Green's paper parameters where positivity has already been checked.

## Next proof obligations

1. Account for a possible inert prime `2` separately in Section 6.
2. Complete the Section 6 weighted prime bound with uniform quantifier
   order, then connect it to the final character theorem.

`PLAN.md` lists the remaining path and later AFP packaging work.
`STATEMENT_AUDIT.md` lists the paper statement issues. Green's full
paper theorem has not yet been verified.

## Repository scope

The Stokes edits in `../Stokes/CLEANUP.md` and
`../Stokes/Green_AC_Winding.thy` are independent work and are excluded
from this No_Siegel checkpoint.
