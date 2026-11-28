# Polynomial Wronskians

This entry proves that binomial evaluation matrices at distinct natural
arguments are nonsingular and that the Hasse Wronskian of a linearly
independent finite family of rational polynomials is nonzero. It defines the
univariate Hasse derivative through iterated polynomial derivatives.

For multivariate rational polynomials, the entry develops Kronecker
substitution and its derivative expansion. Its generalized Wronskian theorem
states that, given a linearly independent family of polynomials in a finite
exponent box, one can choose Hasse derivative indices of total order at most
the row number whose determinant is nonzero. This part uses the separate
`Multivariate_Hasse_Derivatives` entry.

Build with Isabelle2026 and the matching AFP checkout:

    isabelle build -b -d /path/to/afp/thys -d /path/to/Multivariate_Hasse_Derivatives -d . Polynomial_Wronskians
