# Milestone 6: Roth's lemma at rational points

This is the proof plan for Milestone 6 of [PLAN.md](PLAN.md). It is
independent of the auxiliary-polynomial construction in Milestones 3–5;
it uses the multivariate polynomial, Hasse derivative, and index
infrastructure from Milestone 2. The intended result is an upper bound
for the index of a nonzero polynomial at a tuple of rational points.

**Completed and batch-built (24 October 2026).**
`Roth_Lemma.roth_lemma` is the rational theorem and
`Roth_Lemma.roth_lemma_integer` is the integer-polynomial interface
for Milestone 7. The latter uses
`ln (real (roth_int_coeff_sup Q)) + 4*m*r 0` as its height allowance.

## Public theorem and conventions

Use zero-based variables `0, ..., m-1`. Let `P :: rat mpoly` be nonzero
and supported in `roth_exponent_box m r`, with `m > 0` and `r v > 0` for
`v < m`. Let `β v :: rat` and `0 < η ≤ 1/2`. Put
`σ = η ^ (2 ^ (m-1))`. The proposed theorem is:

* `r (v+1) ≤ σ * r v` for `v+1 < m`, with casts to `real`;
* `h_proj(P) + 4*m*r 0 ≤ σ * r v * h_rat(β v)` for every `v < m`;
* then `roth_index m r β P ≤ ereal (2*m*η)`.

Here `H_rat(p/q) = max(|p|,q)` for a reduced fraction with `q > 0`,
`h_rat = log ∘ H_rat`, and `h_proj` is the logarithm of the largest
absolute coefficient of a primitive integral representative of the
nonzero rational polynomial. State the height hypothesis
coordinatewise in Isabelle; it is equivalent to using
`min_{v<m}(r v * h_rat(β v))` and avoids a nonempty finite `Min`.

The coefficient type must be rational: the induction factors a
polynomial into rational polynomials. Integer polynomials enter through
the cast from Milestone 4. The constant `4` is a proposed safe
allowance, contingent on proving the determinant bound below. Retain
this allowance or enlarge it if the checked bound requires more; the
final argument only needs a fixed constant times `m*r 0`.

For `m=1`, `σ=η`. Prove the sharper conclusion `index ≤ η` in the
univariate step. The weaker `2η` then follows and the sharper version
is what the induction uses for its one-variable factor.

## Layer 6.0: heights and scale invariance

Suggested theory: `Primitive_Height.thy`.

1. Construct a primitive integer representative of every nonzero
   `rat mpoly`, unique up to sign. Define `H_proj(P) ≥ 1` and
   `h_proj(P) = log H_proj(P)`. Prove invariance under multiplication
   by a nonzero rational, and
   `H_proj(replace_coeff of_int P) ≤ max(1, coefficient_sup P)`
   for nonzero integer `P`.
2. For polynomials in disjoint variable sets, prove the coefficient
   identity already underlying `roth_disjoint_prod_coeff`, including
   the maximum-coefficient identity for nonzero *integer* factors.
   Their product is primitive when both factors are primitive:
   the coefficients are pairwise products, so their gcd is the
   product of the two coefficient gcds. This suffices for
   `h_proj(U₁ U₂) = h_proj(U₁) + h_proj(U₂)` for disjoint rational
   factors. A general multivariate Gauss lemma is unnecessary.
3. Prove `H_rat β ≥ 1` and connect `h_rat` to the rational height used
   by Milestone 1. Establish the ordinary logarithm and scaling
   inequalities before the induction.

Do not use the maximum absolute coefficient of a *chosen rational*
representative as `h_proj`: it changes under rational rescaling.
Nor does its affine height have the disjoint-factor equality needed
below. AFP `Polynomials/MPoly_Type.thy` has `primitive` and
`content_primitive`; inspect their exact hypotheses before reuse.

**Checkpoint:** a standalone rational height API and a proof of
disjoint-factor height additivity, with no Wronskian imports.

## Layer 6.1: the one-variable bound

Suggested theory: `Univariate_Index.thy`.

For nonzero `Q :: rat poly` of degree at most `r > 0` and rational
`β`, let `l` be the multiplicity of `β` as a root. Prove

`l * h_rat β ≤ h_proj Q + r`.

Connect multiplicity to the first nonzero Hasse coefficient, giving
`roth_index 1 (λ_. r) (λ_. β) P = ereal (real l / real r)` for the
corresponding one-variable `mpoly`. The height hypothesis with `m=1`
then yields `index ≤ η`.

A possible route is the AFP
`Berlekamp_Zassenhaus/Mahler_Measure.thy`:
`mahler_measure_dvd` and `Landau_inequality_mahler_measure` give
factor monotonicity and the coefficient bound. For reduced `p/q`,
the primitive factor `q*X-p` has Mahler measure `H_rat(p/q)`.
Check whether the import cost and the bridge from rational-root
multiplicity are lower than a direct integer-polynomial proof.

**Checkpoint:** the univariate index theorem stated with the same
height definition and `η` used by the public theorem.

## Layer 6.2: Wronskians

Suggested theory: `Roth_Wronskian.thy`.

**Progress (24 October 2026):** This layer is proved and batch-built.
`roth_wr_independent` proves the univariate nonvanishing criterion;
the Kronecker theories establish substitution, its derivative
expansion, and determinant reflection.
`Kronecker_Minor.roth_generalized_wronskian` proves the boxed
multivariate criterion with the row-order bound below.

Use Hasse derivatives `roth_hasse I` and the determinant for
`'a mat` in AFP `Jordan_Normal_Form/Determinant.thy`. First prove
the univariate criterion over `ℚ`: independent polynomials
`ψ₀, ..., ψₖ₋₁` have nonzero determinant of the rows
`D^i ψ_j`, `i < k`. A concrete proof is to make a new basis with
strictly increasing degrees; the top coefficient of the determinant
is the determinant of the matrix `binomial (degree ψ_j) i`, times the
product of leading coefficients. That numeric matrix is nonsingular
because `binomial X i`, for `i < k`, form a basis of polynomials of
degree below `k`: a nonzero linear combination cannot vanish at the
`k` distinct degrees. This avoids needing a closed Vandermonde
determinant formula. Record any
finite-matrix and polynomial-to-`mpoly` bridge lemmas separately.

For independent `φ₀, ..., φₖ₋₁ ∈ ℚ[X₀,...,Xₛ₋₁]`, prove existence of
multi-indices `μ_i` supported on `{..<s}` with
`|μ_i| ≤ i` and

`det (mat k k (λ(i,j). roth_hasse (μ_i) (φ_j))) ≠ 0`.

The preferred route is Kronecker substitution followed by the
univariate criterion:

1. Choose a base **strictly larger** than every partial degree of
   every `φ_j`. Prove injectivity of
   `I ↦ Σ_{v<s} lookup I v * base^v` on the common exponent box.
2. Let `S(X_v)=t^(base^v)`. Prove by induction on `i` that
   `D_t^i(S φ)` is a `ℚ[t]`-linear combination of
   `S(roth_hasse μ φ)` with `|μ|≤i`. The first derivative follows
   from the chain rule; repeated derivatives also differentiate the
   combination coefficients.
3. Expand the univariate determinant by row multilinearity. If it
   is nonzero, at least one substituted generalized Wronskian is
   nonzero, hence so is that Wronskian before substitution.

The direct finite-jet proof is a fallback if the substitution chain
rule becomes the larger development. Freeze one proof route after
testing its first two lemmas. No full multivariate rational-function
differential algebra is needed.

**Checkpoint:** the generalized Wronskian criterion with order bound
`|μ_i|≤i`, independently useful outside Roth's theorem.

## Layer 6.3: tensor rank and determinant identity

Suggested theory: `Tensor_Determinant.thy`.

**Progress (24 October 2026):** This layer is proved and batch-built.
`Tensor_Determinant` chooses the independent coefficient basis;
`Det_Factor_Bounds` proves the determinant product identity and
supplies the factor support and degree boxes.

For `m≥2`, write `P` as a polynomial in `X_(m-1)` with coefficients
in `ℚ[X₀,...,X_(m-2)]`. Choose a basis of the span of its coefficient
polynomials. Obtain

`P = Σ_{j<k} φ_j(X₀,...,X_(m-2)) ψ_j(X_(m-1))`,

where `1≤k≤r(m-1)+1` and both families are linearly independent
over `ℚ`. Prove the split and recombination as reusable lemmas;
minimality of an unspecified decomposition is a less convenient
formal interface.

Choose the generalized Wronskian orders `μ_i` for the `φ_j`, and
ordinary orders `j` for the `ψ_j`. Define `U_left` and `U_last` as
their determinants. Both are nonzero, and

`V = det (mat k k
       (λ(i,j). roth_hasse (μ_i + single (m-1) j) P))
   = U_left * U_last`.

Check the order of matrix factors when invoking `det_mult`.
Record the carrier conditions and the fact that the two factors use
disjoint variable sets. Their partial degrees are bounded by
`k*r v` in the respective variables.

**Checkpoint:** a nonzero determinant `V`, its factorization, and
degree bounds, without any height or index estimates.

## Layer 6.4: determinant height

Suggested theory: `Roth_Determinant_Bounds.thy`.

Prove a coefficient estimate for Hasse derivatives of a primitive
integral representative of `P`. Milestone 2 already gives
`roth_hasse_coeff_exact` and `roth_hasse_coeff_bound` for integer
polynomials. Use the box bound
`card(roth_exponent_box m r) ≤ 2^(Σr v)` and the determinant's
permutation expansion. A deliberately generous candidate is

`H_proj(V) ≤ H_proj(P)^k * k! * 4^(k * Σ_{v<m} r v)`.

For `m≥2`, the ratio hypothesis gives
`Σr v ≤ 2*r 0`, and `k! ≤ 2^(k*r(m-1)) ≤ 2^(k*r 0)`.
Consequently the candidate gives
`h_proj(V) ≤ k * (h_proj(P) + 5*log(2)*r 0)`,
and `5*log(2) < 4` gives the working bound

`h_proj(V) ≤ k * (h_proj(P) + 4*r 0)`.

Prove the multiplicative integer estimate first; apply `log` only
after all factors are positive. Because `V` and `U_left*U_last`
are equal and use disjoint variables, Layer 6.0 then gives each
factor height at most `h_proj(V)`.

**Checkpoint:** the explicit height bound above. If the candidate
coefficient estimate needs a larger constant, recalculate the
public theorem's allowance before starting the induction.

## Layer 6.5: determinant index

Suggested theory: `Det_Factor_Bounds.thy`.

Work with the real value of the index for **nonzero** polynomials;
use `roth_index_attained` to leave `ereal` only at the interface.
Milestone 2 already proves `roth_index_hasse`,
`roth_index_add`, and `roth_disjoint_index_mult`. Apply them to
the permutation expansion of `V`.

Write `t = index(P)` and `ρ = r(m-1)/r(m-2)`. Since
`|μ_i|≤i≤k-1≤r(m-1)` and the earlier `r v` are decreasing,
each row's derivative loss is at most
`ρ + j/r(m-1)` in column `j`. First prove the precise bound

`index(V) + k*ρ ≥
  Σ_{j<k} max(0, t - j/r(m-1))`.

Then prove the separate finite-sum inequality

`Σ_{j<k} max(0, t - j/r(m-1)) ≥ k*t²/(2*m)`

for `0≤t≤m` and `1≤k≤r(m-1)+1`. The upper bound `t≤m`
comes from the degree box and nonzero `P`. Keep the finite-sum
lemma independent of polynomials.

**Checkpoint:** `index(V)+k*ρ ≥ k*index(P)^2/(2m)`.

## Layer 6.6: induction and public theorem

Suggested theory: `Roth_Lemma.thy`.

Induct on `m`. The case `m=1` is Layer 6.1. For `m≥2`, use the
factorization and the bound
`h_proj(V) ≤ k(h_proj(P)+4r 0)`.
The factor `U_last` satisfies the one-variable hypothesis with
degree bound `k*r(m-1)` and parameter `σ`; this gives
`index_(r(m-1))(U_last) ≤ kσ`.

For `U_left`, use degree bounds `k*r v` and parameter `η²`.
The ratio condition is unchanged because
`(η²)^(2^(m-2)) = σ`. Its height threshold follows from

`h_proj(U_left)+4(m-1)k*r 0
 ≤ k(h_proj(P)+4m*r 0)`.

Thus `index(U_left) ≤ 2k(m-1)η²`. Disjoint-factor index
additivity yields
`index(V) ≤ kσ + 2k(m-1)η²`.
As `σ≤η²` and `ρ≤σ` for `m≥2`, Layer 6.5 gives
`index(P)^2 ≤ 4m²η²`, hence the stated upper bound.

Keep the univariate factor result and determinant-index inequality
as named theorems. The final induction should only combine them.

## Audit and integration gates

The local `arXiv-2502.00731v1/v2.tex` is a route map, not a source of
unchecked constants. Its Kronecker base equals a stated upper degree
bound, whereas digit injectivity needs a strictly larger base. Its
last displayed estimate also contains the impossible inequality
`r_m ≤ η² r_m`; the needed bound is `r_m/r_(m-1) ≤ σ ≤ η²`. Its height
discussion needs a scale-invariant projective interpretation for
rational factors. Its `2m*r₁` allowance depends on the sharper
determinant bound stated there; use the explicit, more generous
allowance above until that bound is proved in Isabelle. Cross-check
the Wronskian and induction route against Mahler, *Lectures on
Diophantine Approximations*, Part 1, Chapter 5 (Project Euclid
`ndml/1175197418`); use Bombieri–Gubler, Chapter 6, if available.

Before claiming Milestone 6 complete:

1. State and build each checkpoint theorem with no `sorry`.
2. Check the final height constant against the proved determinant
   bound, especially the `U_left` induction threshold.
3. Give an integer-polynomial corollary by casting Milestone 4's
   output to `rat mpoly`, preserving nonzeroness and the index at
   rational points. Record precisely the height inequality that
   Milestone 7 must satisfy.
4. Build the narrow Roth session once after the incremental checks.

Any extra reusable height or Wronskian session should be created
only if it gives a shorter build cycle or a clear independent AFP
interface; theory layers within Roth suffice otherwise.
