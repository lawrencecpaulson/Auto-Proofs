# AFP entry boundaries

The formalisation of Green's paper stays in the `No_Siegel` session. Its
prerequisites are separate entries only when their statements and imports
stand on their own. A generic result used by Green may cite the paper as its
source without becoming part of the paper session.

## Proposed dependency order

1. `Bivariate_Resultants`: polynomial conversion, factorisation,
   specialisation, resultant degree, and multiplicity bounds from Green's
   Appendix A. These are stated for arbitrary bivariate complex
   polynomials. `No_Siegel` imports this entry.
2. `Primitive_Real_Characters`: local prime-power
   characters, CRT assembly, quadratic reciprocity, and construction of a
   fundamental discriminant. Its
   `primitive_real_character_discriminant` theorem has no Green lattice
   assumption. `No_Siegel/Quadratic_Character.thy` supplies the bridge to
   Green's lattice locale.
3. `No_Siegel`: the diagonal lattice and its zero count, derivative-row
   independence for Green's configuration, paper parameters, Gram
   determinant, Frobenius and valuation argument, and the weighted inert-prime
   theorem.

`Finite_Grid.thy` contains both a general finite-grid zero bound and Green's
diagonal-grid specialisation. It stays with the paper for now. The
`Bivariate_Resultants` theories do not use any of its declarations and can
instead import their AFP prerequisites directly.

## Bivariate resultant entry assessment

`Bivariate_Resultants` is a useful independent AFP candidate. Its main
statements concern arbitrary bivariate complex polynomials: factorisation
with nonzero specialisations, the degree of the first-variable resultant,
the multiplicity bound at every fibre (including degree drops), and a bound
on exceptional fibres. No Green lattice, diagonal grid, derivative row, or
paper parameter occurs in those statements. `No_Siegel` uses the general
factorisation and resultant bounds in `Row_Independence`, where the
point-configuration argument remains.

The existing AFP `Factor_Algebraic_Polynomial.Multivariate_Resultant` supplies
resultant construction and specialisation facts. It does not supply the
derivative-resultant multiplicity or exceptional-fibre bounds proved here.
The entry now also has a resultant for **two** bivariate polynomials, a
weighted degree bound, fixed-size and regular-fibre specialisation theorems,
a common-root fibre bound, and a corollary for generic full-degree,
root-squarefree fibres. These extend the existing AFP construction, which
pairs a multivariate polynomial with a univariate one. The determinant
degree argument was consolidated into a row-wise lemma; the old uniform
bound remains a corollary. Unused special cases of the multiplicity theorem
were removed, and the general factorisation theorems have descriptive
names. Green's Appendix A is cited in the entry's document. The staged
session, PDF, browser output, and outline passed on 13 November 2026.

The character entry builds without `No_Siegel` and exports the discriminant
definition and classification theorem. `No_Siegel` retains the lattice
consequences and the Green-specific bridge.

Small generic estimates used only inside Green's determinant or prime-sum
argument stay with `No_Siegel`. An AFP entry needs a coherent mathematical
result and public theorem interface, not merely a reusable lemma.

`../Exploratory/No_Siegel/Statement_Audit.thy` concerns the optional analytic
zero-free deduction. It is outside the formalisation of Green's weighted-prime
theorem and remains local exploratory material until a separate extension is
prepared.

## Verification gate

The two prerequisite entries' independent sessions and PDFs, followed by
`No_Siegel` with its PDF, passed on 12 November 2026. The character
classification theories were removed from `No_Siegel` after that check; the
paper locale extends the independent character-data locale, so its assumptions
are stated only once. The bivariate entry contains general specialisation
and resultant bounds, while `Row_Independence` retains Green's specific
derivative-row argument.

After the bivariate pair-resultant extension and factorisation-theorem
rename, `Bivariate_Resultants` passed its AFP-style session and document
build, and `No_Siegel` passed with its PDF against the revised entry on
13 November 2026.
