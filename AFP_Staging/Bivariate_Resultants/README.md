# Bivariate resultants and multiplicity

This staged AFP entry extracts the general polynomial arguments used in
Section 3 and Appendix A of Ben Green's note *On Landau–Siegel zeros*.
It has one session, `Bivariate_Resultants`, with two theories:

* `Bivariate_Polynomial` supplies bivariate specialisation, factorisation,
  and coordinate-degree bounds. `green_factorization_regular` states the
  factorisation and nonzero-specialisation property for arbitrary nonzero
  bivariate complex polynomials.
* `Resultant_Multiplicity` proves the resultant degree estimate and
  `first_resultant_multiplicity_irreducible`, including fibres whose degree
  drops. It also bounds the number of exceptional fibres.

The entry imports AFP polynomial infrastructure directly. The diagonal grid,
Green's derivative rows, and all paper parameters remain in `No_Siegel`.

After the standalone session passes, rebuild `No_Siegel` using this directory
as an additional session directory.
