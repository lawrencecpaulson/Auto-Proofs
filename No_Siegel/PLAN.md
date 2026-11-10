# Formalising Green's weighted prime bound

Planning date: 7 November 2026. Source: [Green's note](no-siegel.tex).
Target prover: Isabelle2026, using the installed AFP where appropriate.

## Scope and completion criteria

The required goal is to formalise the theorem proved in Green's note and
all prerequisites used in its proof: for a primitive, nonprincipal real
Dirichlet character of sufficiently large conductor \(q\), and sufficiently
large even \(C\), with \(X=q^C\),
\[
  \sum_{\substack{p\leq X\\\chi(p)=-1}}\frac{\log p}{p}
    \leq \left(\frac12+O(1/C)\right)\log X+O_C(1).
\]
Milestone 1 must fix the order of quantifiers and explicit constants in this
statement. A checked fixed-\(C\) instance is useful progress, but does not
by itself establish the full theorem stated in the paper.

The note cites an external analytic argument for deducing a Landau–Siegel
zero-free region from this bound. Formalising that deduction would be a
valuable **optional extension**; it is not part of the paper's proof and is
not a completion criterion for this project.

Completion means a checked Isabelle proof of the note's theorem and its
prerequisites, with no admitted steps, and all required sessions building
under Isabelle2026. Record and resolve any errors found in the paper's
arguments.

In each theory, and near a major theorem when helpful, identify the
corresponding section or result of the paper in the Isabelle source.

After each mathematical milestone, review the affected theories for
repeated assumptions, formulas, and proof arguments. Name useful shared
mathematics with definitions, locales, or general lemmas, while keeping
distinct estimates explicit.

## Milestones and estimates

Estimates are full-time **person-weeks for one experienced Isabelle
developer**. A day means roughly one fifth of a person-week. These are
planning ranges, not timings from proof attempts.

| No. | Milestone and deliverable | Estimate |
| --- | --- | ---: |
| 1 | **Statement and source audit.** Fix explicit inequalities, the order of quantifiers for \(C,q\), and dependencies of the error constants. Check each argument in the note and record corrections. | **1–2 weeks** |
| 2 | **Finite-grid bound.** Obtain the exact zero-counting corollary of Schwartz–Zippel for Green's lattice of points, including the coordinate change. | **2–5 days** |
| 3 | **Bivariate polynomial infrastructure.** Establish the factorisation, specialisation, degree, and multiplicity API needed for the independence proof, choosing one representation for bivariate polynomials. | **2–4 weeks** |
| 4 | **Resultant multiplicity bound.** Formalise the appendix lemma that bounds the multiplicity of a specialised root by the order of a resultant, together with the necessary degree bound. | **2–4 weeks** |
| 5 | **Quadratic-character bridge.** Relate the relevant primitive real characters and their conductors to the quadratic description used for the lattice points and inert primes. Account explicitly for primes dividing the conductor. | **3–6 weeks** |
| 6 | **Core of Green's proof.** Prove independence of the evaluation rows, positivity and integrality of the Gram determinant, the Hadamard bound, the Frobenius congruence, and the determinant valuation bound. | **2–4 weeks once milestones 2–5 are ready** |
| 7 | **Quantitative finish.** Check the chosen \(R,S,J,N\), prove the floor-sum estimates, and obtain the weighted inert-prime theorem with the uniformity fixed in milestone 1. | **1–2 weeks** |
| 8 | **Integration and cleanup.** Stabilise imports and theorem interfaces, review duplicated mathematics throughout the new development, document the results, and run full Isabelle2026 session builds. | **1–2 weeks** |

**Initial required-project estimate: approximately 12–25 person-weeks, or 3–6
full-time months.** The remaining-work estimate is below. An optional
analytic zero-free deduction would add an estimated **8–18 person-weeks**.
Green's argument from its algebraic
prerequisites to the weighted prime bound is approximately milestones 6–7, **3–6 weeks**; this is consistent
with a **2–4 week** estimate for the core paper when all prerequisites
and suitable theorem interfaces are already available.

## Progress (7 November 2026)

Milestone 2 is checked in `Finite_Grid.thy`. The theorem
`natural_diagonal_grid_bound` proves that for any nonzero bivariate complex
polynomial and any nonzero coordinate parameter `a`, the number of zeros on
`diagonal_grid a (natural_grid N)` is at most `J * total_degree P` when
`0 < N <= J`. The proof includes an invertible polynomial coordinate
substitution and an injective map from the parameter grid to the point set.
The `No_Siegel` session builds with Isabelle2026 and AFP `devel`.

`Finite_Grid.thy` also proves `natural_diagonal_grid_second_distinct`:
the second-coordinate projection is injective on the point set whenever
the slope `a` is irrational over `Rats`. `Quadratic_Character.thy` now
establishes this for the paper's square root under its locale assumptions;
the finite-grid estimate itself needs only `a != 0`.

Milestone 1 is recorded in `STATEMENT_AUDIT.md` and the arithmetic deduction
is checked in `Statement_Audit.thy`.  The audit reconstructs an explicit
fixed-parameter version of Green's claimed prime bound: at the even parameter
`C = 64`, it suffices to prove `S_{-1}(q^64) ≤ 43 log q + 517` for all
sufficiently large eligible conductors.  Together with Banks's explicit
zero-sensitive prime-bias inequality, Mertens' theorem, and the ramified-prime
bound, it implies `(1-β) log q ≥ 77/32768` once `log q ≥ 54`.
The note's Hadamard logarithm loses a factor of two in the stated norm bound,
and its valuation lemma omits the possible inert prime `2`; the audit records
both corrections. The numerical prime bound remains a required proof
obligation. The analytic prime-bias inequality is needed only for the optional zero-free
extension; the checked arithmetic deduction is exploratory work towards it.

Milestone 3 is checked in `Bivariate_Polynomial.thy`. The chosen
representation is `complex mpoly`, viewed as a univariate polynomial with
multivariate coefficients by AFP's `mpoly_to_mpoly_poly`; specialisation uses
AFP's `partial_insertion`. The theory supplies evaluation and ring laws,
coordinate-degree bounds, formal derivative commutation, derivative vanishing
implying root multiplicity, and degree and multiplicity sums for products.

The theorem `green_factorization_regular` gives exactly the algebraic split
used in Green's independence proof: a nonzero bivariate polynomial is a factor
in the second variable times a list of irreducible factors of positive
first-variable degree. Every such irreducible factor has a nonzero
specialisation at every second coordinate. This follows from the checked
factor-theorem bridge `bivariate_specialization_zero_divisor`: if a
specialisation is identically zero, then the polynomial is divisible by
`Var 1 - Const a`. The exceptional indices where the pure second-variable
factor vanishes number at most its second-variable degree when those
coordinates are distinct. The new theory is in `ROOT` and I/Q reports no
errors, warnings, or admitted proofs.

## Milestone 4 result (8 November 2026)

`Resultant_Multiplicity.thy` proves the degree bound
`degree (first_resultant_poly F) <= 2 * degree F 0 * degree F 1`.
It also proves that the resultant is nonzero for every irreducible bivariate
`F` of positive first-variable degree. The conversion in
`Bivariate_Polynomial.thy` is now multiplicative in both directions, preserves
units and irreducibility, and commutes with specialisation. The checked
`first_resultant_poly_nested` identifies the multivariate resultant with the
resultant over `complex poly`, including at degree-dropping fibres. These
facts reduce nonvanishing to AFP's UFD resultant lemma.

The count of degree-losing or multiple-root fibres is unconditional under
those irreducibility and positive-degree hypotheses. The full Appendix A
multiplicity inequality is checked for arbitrary first-variable degree and
an arbitrary root, including fibres whose degree drops. Its proof uses the
fixed-size Sylvester matrix and a triangular Taylor column change of
determinant `1`. A fibre root of multiplicity `mu` makes the last `mu-1`
columns of the changed matrix vanish, forcing that much order in the
resultant. The former zero-root proof is now a one-line corollary of this
general result. Milestone 4's principal estimates build in Isabelle2026
without admitted proofs; see `RESULTANT_AUDIT.md` for the paper-to-code map.

`Quantitative_Finish.thy` starts milestone 7 with checked Section 6
arithmetic: the minimum and reversed-index sums, a floor-division estimate,
the exact index sum, and a square-error bound. `green_double_min_sum_real_bound`
combines these into the paper's per-prime lower estimate.
`green_weighted_min_mass_bound` sums it with arbitrary nonnegative weights
under an explicit upper-bound hypothesis for the valuation mass. The theory
names the row-sum mass, floor main term, and floor error as definitions.
The determinant valuation bound, bounds for the remaining prime sums, and
the uniform final theorem still need proofs. The full Isabelle2026 `No_Siegel`
session build passed on 8 November 2026, with no admitted steps.

## Milestone 5 progress (9 November 2026)

`Quadratic_Character.thy` supplies a locale for Green's quadratic character
data. Within it, the Isabelle2026-checked results give `|d| = q`,
`|sqrt(d)| = sqrt(q)`, irrationality of the complex square root, distinct
second coordinates for the paper's lattice, and the specialised finite-grid
bound. They also give `p | q` iff `p | d`, `chi p = 0` iff `p | q` for primes,
the corresponding zero Legendre value at ramified primes, and (for odd primes)
`chi p = -1` iff the Legendre symbol is `-1`. Euler's criterion then proves
the congruence used in Green's Frobenius argument.

The locale assumes that `d` is a fundamental discriminant,
`q = nat (abs d)`, and agreement of `chi` with the Legendre symbol at odd
primes not dividing `q`. Nonsquareness of `d` is derived from these
assumptions and the nontriviality of the character. The classification
theorem below supplies these assumptions for primitive real characters.
The AFP supplies `real_dcharacter` in `Dirichlet_L` and
`primitive_dchar`, induced moduli, and a conductor in `Gauss_Sums`.
These provide the starting assumptions and conductor facts for the
classification. The prime `2` remains separate in the paper's odd-prime
valuation lemma.

`Quadratic_Classification.thy` now starts from AFP's primitive real
Dirichlet-character locales. It proves that the conductor is the modulus,
the character is nonprincipal, and its square is principal. It also
derives the character's value on square residues, translates this to
`QuadRes` and `Legendre`, and proves that at prime modulus the character
agrees at every argument with the Legendre symbol. This settles the
prime-modulus local character calculation.

`Odd_Prime_Power.thy` proves that every unit congruent to `1` modulo
an odd prime `p` is a square modulo `p^k`. It follows that a primitive
real character of modulus `p^k` has `k = 1`. `Two_Prime_Power.thy`
proves the analogous lifting statement for residues congruent to `1`
modulo `8`, using the order of `25` modulo `2^k`. A primitive real
character of modulus `2^k` therefore has `k = 2` or `k = 3`.
The common step from square lifting to an induced modulus is factored
into `induced_modulus_of_square_lifts`.

`Prime_Power_Values.thy` determines the surviving two-power local
characters on unit generators: at modulus `4`, `chi 3 = -1`; at modulus
`8`, `chi 5 = -1`, `chi 7 = -chi 3`, and `chi 3` is either `1` or `-1`.
Together with periodicity and multiplicativity, these are the complete
local value tables.

`CRT_Assembly.thy` gives the two local characters for coprime factors,
factorises the global character, and transfers primitivity and realness.
`Character_Conductor_Shape.thy` applies this to a global character:
each odd prime has conductor exponent one, while the exponent at two is
two or three when present. `Quadratic_Local_Identification.thy` identifies
the modulus-four factor with `(-1/p)` and the two modulus-eight factors
with `(2/p)` and `(-2/p)` at odd primes. It also proves, by CRT induction,
that an odd squarefree primitive real character is the Jacobi character
at every argument, and uses quadratic reciprocity to choose the signed
odd discriminant.

`Character_Discriminant_Assembly.thy` combines the odd part with the
two-power factor. Its checked
`primitive_real_character_fundamental_discriminant` theorem constructs
`d` for any primitive real Dirichlet character and establishes the
`green_quadratic_character` locale, including `q = nat (abs d)` and the
Legendre values at odd unramified primes. The locale already derives zero
values at ramified primes. Any inert-prime treatment of `p = 2` remains
in the later valuation argument.

## Milestone 6 progress (9 November 2026)

`Row_Independence.thy` now assembles the finite zero count, regular
factorisation, resultant multiplicity estimate, and degree budgets from
Green's Section 3. Its checked `vanishing_polynomial_degree_bound` proves
the paper's counting inequality for a nonzero bivariate polynomial whose
first `J` derivatives vanish at every configured point.
`no_vanishing_polynomial` rules out such a polynomial under Green's strict
dimension condition. This is the polynomial core of Lemma 3.1.

`Row_Vector.thy` now supplies that bridge. Its checked
`green_rows_independent` encodes a relation among all derivative rows as a
bivariate coefficient polynomial and recovers each coefficient from the
zero polynomial. This proves the general finite-configuration form of
Green's Lemma 3.1. `Lattice_Rows.thy` applies it to the diagonal grid using
the checked zero count and distinct-coordinate bounds. Its dimension lemma
reduces the strict inequality to `N² ≥ 4R`, `S = J`, and `0 < J < R`.
`Parameter_Rows.thy` checks these inequalities and `J ≥ N` for
`R = t²`, `N = 2t`, and `S = J = R div C`, assuming `C ≥ 2` and `t ≥ 2C`.
`Paper_Parameters.thy` checks the paper's substitution
`t = q^(C div 2)` for even `C`, names `X`, `N`, and `J`, and proves
both inequalities under the explicit sufficient-size condition
`2C ≤ q^(C div 2)`. Its checked `green_paper_rows_independent` states
the row-independence result for Green's quadratic lattice in the
quadratic-character locale. `green_row_relation` names the derivative
relation shared by the general, lattice, and paper-specific versions.

## Remaining verification path (9 November 2026)

**Green's paper is not yet verified.** Milestones 2–4 check component
results used in its Section 3 and Appendix A, and milestone 7 has checked
arithmetic lemmas. Milestone 6 now has Green's Section 3 row-independence
proof, including the quadratic-lattice instance and paper parameters
under the explicit sufficient-size hypothesis. The Gram determinant
arguments, valuation lemma, and weighted prime theorem are still missing.
Milestone 5 now has the checked classification theorem connecting any
primitive real character to the conditional quadratic-character locale.

The remaining obligations are:

1. **Paper proof: positive integral Gram determinant and upper bound
   (Sections 2 and 4, milestone 6).** Define the rows and trace pairing,
   prove integrality and positive definiteness, and formalise Hadamard's
   estimate with the corrected factor `4` inside its first logarithm.
2. **Paper proof: odd-prime valuation (Section 5, milestone 6).** Lift
   the checked Euler congruence to the Frobenius statement in `ℤ[√d]`;
   formalise the derivative and triangular row transformation, its
   divisibility, and Green's valuation lemma. Bound a possible inert
   prime `2` separately.
3. **Paper proof: uniform quantitative theorem (Section 6, milestone 7).**
   Combine the checked floor-sum lemmas with determinant bounds and
   explicit prime-sum estimates. Prove the parameter inequalities and a
   bound with constants and quantifiers valid for all sufficiently large
   even `C` and eligible conductors `q`. The audited `C = 64` inequality
   is an intermediate target, not a replacement for the paper's theorem.
4. **Final verification (milestone 8).** Connect the theorem to the character
   classification, check every source correction and prerequisite, review
   duplicated mathematics, and rebuild all required Isabelle2026 sessions.

At the original milestone ranges, the remaining paper proof and final
verification are **4–8 person-weeks** for one experienced Isabelle
developer. These are planning estimates; determinant integration carries
the greatest uncertainty.

## Dependencies and useful intermediate results

The milestone 1 audit identifies Banks, Lemma 2.1(2.3), as the
zero-sensitive Dirichlet-\(L\) input for the optional zero-free deduction.
It is not a prerequisite of the weighted prime theorem.

The main proof path is:

```text
statement and source audit
    ├── finite-grid bound ───────────────┐
    ├── bivariate tools → resultant ─────┼→ Green's determinant
    └── quadratic-character bridge ─────┘         ↓
                                          weighted prime bound
                                          (required project complete)
```

The finite-grid lemma, polynomial and resultant lemmas, and determinant
divisibility argument should be stated generally enough to be useful
beyond this proof. Keep the character-specific facts and the numerical
parameter choices separate from those general results.

At milestone 7, the theorem actually proved by Green's note is a
standalone, checked result. Milestone 8 completes the required project.

An optional follow-on project could develop the missing zero-sensitive
Dirichlet-\(L\) estimates, combine them with milestone 7, and prove a
uniform zero-free theorem. The present estimate for that extension is
8–18 person-weeks, excluding any treatment of finitely many small
conductors if a statement for every \(q\geq3\) is desired.

## Principal uncertainties

- **Uniformity:** the dependencies of the \(O(1/C)\) and \(O_C(1)\)
  terms must match the theorem stated in the note, with their quantifier
  dependencies made explicit.
- **Determinant integration:** the checked Section 3 row independence
  must be connected to the integral trace pairing and its positive
  determinant.
- **Optional analytic bridge:** a later zero-free deduction would need
  zero-sensitive Dirichlet-\(L\) and prime-number-theorem estimates in a
  precise uniform form. This is a major risk for that optional extension.

The estimates assume one developer, the existing Isabelle2026 and AFP
libraries, and that the mathematical arguments withstand the initial
audit. They do not include research time to repair a substantive gap in
the source arguments.
