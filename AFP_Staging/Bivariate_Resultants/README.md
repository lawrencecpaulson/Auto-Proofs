# Bivariate resultants and multiplicity

This staged AFP entry develops bivariate complex polynomial specialisation
and resultants. Its factorisation and multiplicity arguments abstract
Section 3 and Appendix A of Ben Green's note *On Landau–Siegel zeros*.
It has one session, `Bivariate_Resultants`, with three theories:

* `Bivariate_Polynomial` supplies bivariate specialisation, factorisation,
  and coordinate-degree bounds. `bivariate_factorization_regular` states the
  factorisation and nonzero-specialisation property for arbitrary nonzero
  bivariate complex polynomials.
* `Resultant_Multiplicity` proves the resultant degree estimate and
  `first_resultant_multiplicity_irreducible`, including fibres whose degree
  drops. It also bounds the number of exceptional fibres.
* `Bivariate_Resultant_Pairs` extends the interface to two arbitrary
  bivariate polynomials. It supplies a fixed-size specialisation theorem,
  a regular-fibre common-root criterion, the weighted degree bound
  `deg_x(G) deg_y(F) + deg_x(F) deg_y(G)`, and a bound on fibres with a
  common root. It also states directly that an irreducible polynomial has
  full-degree, root-squarefree specialisations outside a bounded set.

The entry imports AFP polynomial infrastructure directly. The diagonal grid,
Green's derivative rows, and all paper parameters remain in `No_Siegel`.

To check the entry with the current AFP checkout, build its session with
`document=pdf` and then rebuild `No_Siegel` using this directory as an
additional session directory.
