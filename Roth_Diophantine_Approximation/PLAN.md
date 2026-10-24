# Roth's theorem on rational approximation: formalisation plan

## Scope and endpoint

Prove the classical real theorem first. For an irrational algebraic
`α :: real` and `δ > 0`, only finitely many reduced pairs `(p, q)` with
`p :: int`, `q :: nat`, `q > 0` satisfy

`|α - p/q| < q powr -(2 + δ)`.

The public theorem should also offer the contrapositive form used by
`Transcendence_Series_Hancl_Rucki/Transcendence_Series.thy`:
an infinite set of reduced approximants satisfying an exponent `κ`
implies `κ ≤ 2`. A final bridge should interpret that entry's
`RothsTheorem` locale and expose its two results without the locale
assumption. Keep the bridge separate from the core Roth proof, so
neither entry depends cyclically on the other.

The first project does **not** include the number-field or finite-places
extension, Schlickewei's theorem, or Schmidt's subspace theorem.

## Proof route and representations

Follow Section 3 of `../arXiv-2502.00731v1/v2.tex` for the sequence

auxiliary polynomial → high index at good approximants → Roth's lemma
→ contradiction.

Specialise it to `ℚ` throughout:

* Work with reduced rationals `p/q` and positive natural denominators.
  Their elementary height is `max |p| q`. For approximants near a fixed
  real `α`, this is comparable to `q` by a constant depending on `α`.
* Construct an **integer** multivariate polynomial. Its coefficients
  after Hasse differentiation remain integral. Evaluation at rational
  points then has an integer numerator after multiplication by
  `∏ qᵢ ^ rᵢ`. This replaces the paper's product formula and Weil-height
  argument in the lower-index theorem.
* Use the AFP `Polynomials` multivariate-polynomial type, with variables
  indexed by natural numbers and proofs that support is contained in
  `{0..<m}`. Confirm its coefficient, substitution, and degree APIs
  before committing to a derivative representation.
* Define the weighted index by the least weight of a nonzero Taylor
  coefficient at a point, valued in `ereal`, with index `∞` for the zero
  polynomial. Translation, product bounds, and differentiation should
  not require repeated raw coefficient expansions.
* Use projective coefficient height over `ℚ` only where Roth's lemma
  needs a height of *factors*. An integer sup norm suffices elsewhere.

Each milestone below must end in a built Isabelle session with no
`sorry`, `oops`, or new axioms. Build only the changed session and its
uncached prerequisites. Do not start Isabelle proof work until this plan
has been reviewed.

## Milestones

### 0. Reusable Siegel base

**Current state:** `Gelfond_Schneider/Integer_Kernels` is already an
independent `Bounded_Integer_Kernels` session. It now has a verified
counting form: if an integer `p × q` matrix has entries bounded by `B`
and `(2qBC + 1)^p < (C + 1)^q`, it has a nonzero integer kernel vector
bounded by `C`. The earlier corollary gives `C = 2qB` when
`0 < p` and `2p ≤ q`. This was built with Isabelle2026 RC4.

**Deliverable:** keep this as the reusable Siegel dependency, document
its theorem interface, and decide its eventual AFP packaging. No
stronger exponent bound is required by the chosen Roth construction:
the auxiliary system will be arranged to satisfy `2p ≤ q`. If an
already-existing Isabelle Siegel entry is intended as the home, identify
it before relocating this session; none was found in the inspected AFP
checkout.

### 1. Approximation interface and integral reduction

**Status:** complete under Isabelle2026 RC4. `Roth_Approximation.thy`
provides finite reduced-pair sets with integer and natural denominators,
the denominator-bound and `κ ≤ 2` equivalences, the height bound, and
scaling of reduced approximants. `Roth_Integral_Reduction.thy` proves
`roth_reduction_to_integral`: finiteness for algebraic integers at every
exponent above `2` implies finiteness for all algebraic irrationals at
every exponent above `2`. The Roth session built successfully on
23 October 2026.

**Deliverables:**

1. A finite-set version over reduced `(p,q)` pairs, an equivalent
   eventual denominator-bound version, and the locale-compatible
   `κ ≤ 2` form, including the conversion between the public natural
   denominator and the locale's integer denominator. Prove denominator
   unboundedness for an infinite set of reduced pairs and the elementary
   rational-height comparison near fixed `α`.
2. Reduce an arbitrary algebraic irrational `α` to an algebraic integer
   by multiplying by a positive integer. Track how reduced
   denominators change: for reduced `p/q`, the reduced denominator of
   `cp/q` lies between `q/c` and `q`. Allow a smaller positive
   approximation margin after scaling.

**Reuse:** AFP
`Hermite_Lindemann/More_Algebraic_Numbers_HLW.thy` supplies the
algebraic-integer scaling lemma. The approximation arithmetic uses
Isabelle/HOL's rational normalization and gcd lemmas. The eventual
denominator-bound form is stated through
`finite_roth_good_pairs_iff_bounded_denominator`.

### 2. Multivariate Taylor coefficients and weighted index

**Status:** complete under Isabelle2026 RC4; the
`Roth_Diophantine_Approximation` session built on 23 October 2026.
`Roth_MPoly_Box` supplies finite exponent boxes and partial-degree
bounds. `Roth_Hasse` and `Roth_Hasse_Derivative` give the Taylor identity
in Hasse-derivative form. `Roth_Index` and `Roth_Disjoint_Index` prove the
weighted-index laws, including exact multiplication for disjoint
variables. `Roth_Hasse_Support` proves the derivative index and degree
bounds, the exact coefficient formula
`coeff (D_J P) I = coeff P (I+J) * of_nat (roth_mchoose (I+J) J)`,
the composition law `D_I (D_J P) =
Const (of_nat (roth_mchoose (I+J) I)) * D_(I+J) P`, and the explicit integer coefficient
bound for polynomials in a degree box. The coefficient formula also
shows directly that Hasse derivatives of integer polynomials have
integer coefficients.

**Deliverables:** finite-box polynomial support and partial-degree
lemmas; Hasse coefficients `D_I P(a)` with the Taylor identity
`P(X) = Σ_I D_I P(a) (X-a)^I`; coefficient integrality; composition of
Hasse derivatives; degree and coefficient bounds. Define weighted
index for positive degrees `rᵢ`, then prove:

* vanishing of all Hasse coefficients below weight `θ` is equivalent
  to `Ind(P) ≥ θ`;
* `Ind(P+Q) ≥ min(Ind(P), Ind(Q))`;
* `Ind(PQ) ≥ Ind(P)+Ind(Q)`;
* `Ind(D_I P) ≥ Ind(P)-Σ iₕ/rₕ`;
* exact index addition for factors in **disjoint** variable sets.

The last, narrower equality is what Roth's lemma uses. It avoids
building a general weighted initial-form theory solely for this proof.
This milestone is independently useful polynomial infrastructure.

### 3. Count low-weight multi-indices

**Status:** complete under Isabelle2026 RC4; the Roth session built on
23 October 2026. `Roth_Index_Count` proves the box cardinality,
the finite-grid second-moment estimate, `roth_low_indices_count`,
and `roth_taylor_conditions_dimension`. The last theorem gives the
strict `2d` dimension gap for the Taylor conditions used in
Milestone 4.

Assume `m > 0`, `r v > 0` for `v < m`, and `0 < ε < 1`. First prove
`card (roth_exponent_box m r) = ∏_{v<m}(r v + 1)`, and denote this
positive number by `N`. For
`L = {I ∈ roth_exponent_box m r.
roth_weight m r I ≤ m(1-ε)/2}`, prove the division-free count
`card L * m * ε² ≤ N` (with the natural numbers cast to reals).
Consequently, `2d < m ε²` implies `2d * card L < N`, the exact
dimension gap needed in Milestone 4.

Use an elementary second-moment calculation: each uniform coordinate
`iₕ/rₕ` has mean `1/2`, its squared deviation is at most `1/4`,
and cross terms sum to zero. In finite-sum form, the sum over the box
of the squared centered total weight is at most `N*m/4`. Every index
in `L` contributes at least `m²*ε²/4`. This proves the count without
a probability library. The count with `≤` safely covers the Taylor
conditions with weight `< m(1-ε)/2`.

This replaces the paper's exponential estimate. The weaker bound
suffices because `m` is freely chosen and gives exactly the dimension
gap needed by the existing linear Siegel theorem. Prove the count as
a reusable finite-product theorem without importing a probability
library.

### 4. Bounded integral power basis and auxiliary polynomial

**Status:** complete under Isabelle2026 RC4; the Roth session built on
23 October 2026. `Roth_Power_Basis` gives integer coordinates for all
powers of `α` with bound `roth_power_base f ^ k`.
`Roth_Auxiliary_Matrix` constructs the bounded integer Taylor system,
and `Roth_Auxiliary_Polynomial` applies the integer kernel theorem.
The theorem `roth_auxiliary_polynomial_monic_exp` gives a nonzero
integer polynomial in the box, index at least `m(1-ε)/2`, and
coefficient bound `2 * (4 * roth_power_base f) ^ (Σrₕ)` whenever
`2d < m ε²`.

Fix an algebraic integer `α` and choose **any** monic
`f ∈ ℤ[X]` of degree `d > 0` with `f(α)=0`. The minimal polynomial is
unnecessary. Use reduction modulo `f` to choose an integer coordinate
vector for every `α^k` in `1, α, ..., α^(d-1)`, bounded by `Cα^k`
for a fixed `Cα ≥ 1`. These vectors need not be unique if `f` is not
minimal; only their evaluation and bounds matter. Prove both by a
recurrence on the coefficients of `f`, avoiding a general integral
basis of the number field.

For positive `r₁,...,rₘ`, make one unknown for each monomial in the
degree box and one integer equation for each basis coordinate of each
low-weight Taylor condition at `(α,...,α)`. Show the matrix has
`q = ∏(rₕ+1)` columns, at most `p = d × (number of conditions)` rows,
and coefficients bounded by `B ≤ Cα^(Σrₕ)` after absorbing binomial
factors. Apply Milestone 0 with `2p ≤ q`.

**Target theorem:** there is a nonzero `P ∈ ℤ[X₁,...,Xₘ]` with partial
degrees at most `rₕ`, index at `(α,...,α)` at least
`m(1-ε)/2`, and
`log(max(1, coefficient_sup P)) ≤ C × Σrₕ` for a constant depending
only on `α` and `ε`. An exponential bound without logarithms is an
equivalent implementation interface.

### 5. High index at good rational approximants

Prove the rational denominator lemma: if `T` is an integer polynomial
of partial degrees at most `rₕ`, `βₕ=pₕ/qₕ` are reduced, and
`T(β) ≠ 0`, then
`|T(β)| ≥ 1/∏ qₕ^rₕ`.

Choose a working exponent margin `0 < δ' < min 1 δ` below the exponent
`2+δ` in the final theorem. Milestone 1's comparison of height with
denominator converts sufficiently large good approximants into
`|α-βₕ| ≤ H(βₕ)^-(2+δ')`. Choose `ε > 0` small enough that
`(2+δ')(1-3ε)/2 > 1+ε`; this is the strict exponent gap needed below.

Use the Taylor expansion at `(α,...,α)` and the auxiliary polynomial's
vanishing to bound `|D_J P(β)|` above when each
`|α-βₕ| ≤ H(βₕ)^-(2+δ')`. Under balanced values of `rₕ log H(βₕ)`,
a sufficiently large denominator contradicts the preceding lower
bound unless every derivative with weight below `εm` vanishes.

**Target theorem:** for the auxiliary `P`, sufficiently good and
balanced rational approximants with sufficiently large denominators
satisfy `Ind_β(P) ≥ εm`. First prove the explicit upper and lower
evaluation bounds as separate theorems; the index conclusion should
be a short application of them. This is the real-number replacement
for the paper's Section 3 "Index Lemma".

**Status (24 October 2026): conditional index transfer complete.**
`Roth_Rational_Evaluation` proves the denominator lower bound,
including height and real forms. `Roth_Taylor_Evaluation` gives an
exponential upper bound from the index at the algebraic tuple.
`Roth_Evaluation_Height` bounds the Taylor coefficients using the
integer coefficient supremum and transfers rational indices to real
coefficients. `Roth_Index_Transfer` and
`Roth_Auxiliary_Index_Transfer` derive the rational index conclusion
from an explicit logarithmic gap and the auxiliary polynomial's
height bound. Establishing that gap is part of the final parameter
choice in Milestone 7.

### 6. Roth's lemma over rational points

This is the principal proof risk and has a separate
[Milestone 6 proof plan](ROTH_LEMMA_PLAN.md). Its seven checkpoints cover
rational projective heights, the univariate order bound, generalized
Wronskians, tensor splitting, determinant height and index estimates,
and the final induction. The plan states a proposed rational-point
theorem and audits the numerical constants in the source exposition.
It can proceed independently of Milestones 3–5 once Milestone 2 is
available.

**Status (24 October 2026): complete and batch-built.**
`Roth_Lemma.roth_lemma` proves the rational-point theorem with the
height allowance `h_proj(P) + 4*m*r 0` and conclusion
`Ind_β(P) ≤ 2*m*η`. `Roth_Lemma_Int.roth_lemma_integer` gives the
integer-polynomial corollary with
`ln (real (roth_int_coeff_sup Q)) + 4*m*r 0` in its hypothesis.
The proof uses the generalized Wronskian, disjoint determinant
factorization, projective-height and quadratic determinant-index
bounds, and induction on the number of variables.

### 7. Choose approximants and derive the contradiction

Assume infinitely many approximants with exponent `2+δ`, and apply
Milestone 5 with a smaller working margin `δ'`. Use unbounded rational
heights to choose `β₁,...,βₘ` with sufficiently rapid successive
growth, including the **first** gap from `β₁` to
`β₂`. Choose `r₁` sufficiently large and
`rₕ ≈ r₁ log H(β₁)/log H(βₕ)` so that

* `rₕ log H(βₕ)` are nearly equal;
* `rₕ₊₁/rₕ` satisfy Roth's lemma;
* the height threshold in Roth's lemma holds.

Take `η = ε/4`. Milestone 5 gives `Ind_β(P) ≥ εm`;
Milestone 6 gives `Ind_β(P) ≤ εm/2`, a contradiction.
Return first the algebraic-integer theorem, then apply Milestone 1
to obtain the theorem for every irrational real algebraic `α`.

**Status (24 October 2026): complete and batch-built.**
`Roth_Conditional_Contradiction` combines the auxiliary polynomial,
index transfer, and Roth's lemma into a contradiction under explicit
parameter inequalities. `Roth_Approximant_Selection` obtains finite
rapidly growing sequences from infinitely many good pairs.
`Roth_Approximation_Height` converts sufficiently large good pairs
into the rational-height error bound and selects sequences satisfying
it. `Roth_Degree_Selection` rounds inverse logarithmic heights to
positive integer degrees while preserving a specified ratio.
`Roth_Parameter_Bounds` and `Roth_Parameter_Costs` choose the global
parameters. `Roth_Selected_Contradiction` discharges the height
allowance and strict logarithmic gap. `Roth_Algebraic_Integer` proves
finiteness of good approximants for algebraic integers and applies the
Milestone 1 reduction to irrational real algebraic numbers.

### 8. AFP integration and cleanup

Provide a standalone Roth session with `ROOT`, document source,
bibliography, and a precise main theorem. Keep the reusable Siegel
session separately importable. Add a small bridge session importing
both Roth and `Transcendence_Series_Hancl_Rucki`; interpret its
`RothsTheorem` locale and export the resulting unconditional
Hančl–Rucki corollaries. Review theorem names, unused facts,
redundant `have` steps, and session dependencies. Run the narrow
session builds, then the entry build and document build once.

**Status (24 October 2026): proof integration complete.** The
standalone Roth session, classical real theorem, and PDF document are
batch-built. `Roth_Hancl_Rucki` interprets the locale and exports both
corollaries; its session and PDF document are also batch-built.
Bibliography and wider cleanup remain as editorial work.

## Source audit and decision points

The local `v2.tex` is a route map, not a source to translate line by
line. Before proving each major lemma, cross-check its statement and
constants against Bombieri–Gubler, *Heights in Diophantine Geometry*,
Chapter 6, or Mahler, *Lectures on Diophantine Approximations,
Part 1: g-adic numbers and Roth's theorem*, Chapter 5. Mahler's
chapter on Roth's lemma and generalized Wronskians is accessible
through Project Euclid (`ndml/1175197418`) and provides a direct
classical check on Milestone 6. Access to Bombieri–Gubler would be
especially useful for height estimates, but is not needed for
Milestones 1–4. Mathlib's `NumberTheory/SiegelsLemma.lean` is a
useful comparison for Milestone 0; its sharper exponent bound is
outside the critical path.

Concrete issues in the local exposition to resolve rather than copy:

* Its general number-field Siegel lemma writes arbitrary `K`
  coefficients in an integral basis with integer coordinates without
  first clearing denominators. Milestone 4 avoids this by using
  powers of an algebraic integer.
* Its index properties are left to the reader. They are essential
  theorems in Milestone 2.
* Its Kronecker substitution must use a base greater than the maximum
  exponent, not merely equal to it.
* Near the end of its Roth-lemma proof, `r_m ≤ η² r_m` cannot hold for
  positive `r_m` and `η ≤ 1/2`; rederive the needed degree-ratio
  estimate.
* Its final choice of rapidly growing points states gaps for
  `2 ≤ j ≤ m-1`, but the first gap is also needed. Milestone 7
  will state and prove all gaps explicitly.
* The passage from the general theorem to an algebraic-integer
  auxiliary polynomial needs the scaling reduction in Milestone 1.

## Stop criteria and expected scale

After Milestones 2–5, reassess the exact rational Roth-lemma statement
and its height infrastructure before starting the long induction.
If the Wronskian proof or factor-height estimates require a broad
new algebra library, complete and package those as useful results
before resuming Roth. Do not replace the missing lemma with an
assumption in the final entry.

This is a large project. Milestones 1–5 and 8 have relatively clear
interfaces; Milestone 6 may take as much work as the others combined.
The plan succeeds only when the main theorem and the unconditional
Hančl–Rucki bridge build without extra axioms.
