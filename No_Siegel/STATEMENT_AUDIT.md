# Statement and analytic audit of Green's note

Source: `no-siegel.tex`, especially the introduction, “Archimedean bound”,
“$p$-adic bound”, and “Completion of the proof”.  The analytic input below is
**not** proved in Green's note: it is Banks, *On the OpenAI proof that
Landau–Siegel zeros do not exist*, arXiv:2610.15483v1, Lemma 2.1(2.3).
Kerr, arXiv:2610.21099v1, Lemma 1, states a less explicit version.

This audit gives concrete witnesses for Green's big-O terms **conditional on
his determinant and valuation claims**.  It does not assert that all those
claims have been formalised.  Keep the exact inequalities below as the targets
for their later proofs; never use the asymptotic notation as an Isabelle
assumption.

## Objects and quantifiers

Let `χ` be a primitive, nonprincipal, real Dirichlet character with conductor
`q ≥ 3`.  The quadratic-character bridge must supply a nonsquare fundamental
discriminant `d` with `|d| = q` and `χ(p) = (d|p)` for primes not dividing `q`.
Choose an **even natural number** `C`, fix it independently of `q`, and put

- `X = q^C`, `R = X`, `S = J = ⌊X/C⌋`, `N = 2 q^(C/2)`;
- `S_a(X) = ∑_{p≤X, χ(p)=a} (log p)/p`, for `a ∈ {-1,0,1}`;
- `S_all(X) = ∑_{p≤X} (log p)/p`.

Here `χ(p)=0` iff `p|q`.  The analytic argument needs Green's inequality at
**one fixed** sufficiently large even `C`.  A sufficient precise version of
the paper's theorem is:

> There is a fixed even `C` (we choose `64`) and `Q` such that for every
> eligible `χ` with conductor `q ≥ Q`, one has
> `S_{-1}(q^64) ≤ 43 log q + 517`.

The constants `43` and `517` below are conservative witnesses reconstructed
from the displayed estimates. They are not printed in the paper. The
quadratic bridge, independence proof, determinant bounds, and the
conditions `J ≥ N` and `N²J > 2RS + J(R+S)` have Isabelle proofs. The
transformed derivative entries, determinant invariance under their
triangular row change, and `p^(2∑h)` divisibility and the resulting
valuation lower bound for Green's original Gram determinant at odd
inert primes are checked. The weighted prime
estimates and the separate treatment of `p = 2` remain to be checked
before this inequality becomes a theorem. For fixed `C`,
`J ≥ N` follows once `X ≥ 16 C²`; the dimension condition follows from
`C > 1` and `S < X`.
Thus a `Q` depending on the fixed `C` suffices.  The paper's phrase
“sufficiently large conductor” does not by itself fix a uniform threshold in
both `q` and `C`; no such stronger quantifier order is needed here.

## Reconstructing the error terms in Green's proof

The norm bound on a row of the Gram matrix, as *stated* in the paper, is
`||v_(r,s)|| ≤ 2 (N² S)^(1/2) R^S (2N√q)^(r+s)`.
Hadamard therefore gives the explicit upper bound

```text
H = RS log(4 N² S) + 2 S RS log R + RS(R+S) log(2N√q)
log det G ≤ H.
```

The last term uses `R+S` rather than the sharper `R+S-2` to follow the paper.
For `q≥3`, even `C≥2`, and `X=q^C`, use `S≤X/C`, `X≥2C`,
`log(4)≤(2/C)log X`, and `log(16)≤(4/C)log X`.  Dividing the three
summands of `H` by `X²S log X` bounds them respectively by
`4/C`, `2/C`, and `1/2+17/(4C)`.  Consequently

```text
log det G ≤ (1/2 + 11/C) X² S log X.                 (A)
```

`green_paper_gram_archimedean_parameter` in
`Archimedean_Parameter_Bound.thy` checks (A) under the paper's explicit
parameter and lattice-index hypotheses. It uses the sharper checked
`2N²S` squared-row factor and still obtains the same constant `11`.

For an **odd** inert prime `p`, write
`k_p(r)=⌊r/p⌋`, `h_p(r,s)=min(k_p(r),S-1-s)`, and
`V_p=2∑_{r<R,s<S} h_p(r,s)`.  Green's valuation lemma gives
`V_p ≤ ord_p(det G)`.  For every natural `k`, the elementary sum used
in the note satisfies `∑_{s<S} min(k,S-1-s) ≥ S k-k²`.  Then
`k_p(r) ≥ r/p-1` and `k_p(r)² ≤ r²/p²` yield

```text
V := ∑_{odd p≤X, χ(p)=-1} V_p log p
  ≥ S X(X-1) S_{-1}^{odd}(X)
    - 2 S X θ_{-1}^{odd}(X)
    - 2 X³ ∑_{p≤X} (log p)/p².                         (B)
```

Here `θ_{-1}^{odd}(X)=∑_{odd p≤X,χ(p)=-1} log p`.
The elementary estimate `log n ≤ √n` gives
`∑_{p≤X}(log p)/p² ≤ ∑_{n≥2}n^(-3/2) ≤ 2`.
AFP's `Prime_Counting_Functions.θ_upper_bound` gives
`θ_{-1}^{odd}(X) ≤ θ(X) < (log 4) X`.
AFP's `Mertens_Theorems.mertens_first_theorem` gives
`S_{-1}^{odd}(X) ≤ S_all(X) < log X+2` and also
`S_all(X)>log X-2` for `X≥1`.  Combining (A), (B), and
`V≤log det G`, and using `X/S≤2C`, gives

```text
S_{-1}^{odd}(X)
  ≤ (1/2 + 11/C) log X + (log X+2)/X + 2 log 4 + 4 X/S
  ≤ (1/2 + 11/C) log X + 8C + 4.                     (C)
```

The second line uses `X≥9`, `2 log 4+1<4`.
The possible inert prime `2` contributes at most `log 2/2<1`, so the
paper's claimed bound, with this omission repaired, follows in the explicit
form

```text
S_{-1}(X) ≤ (1/2 + 11/C) log X + 8C + 5.             (D)
```

At `C=64`, (D) is `S_{-1}(q^64) ≤ 43 log q+517`.
These witnesses preserve the paper's determinant comparison.  The auxiliary
prime-sum bounds only resolve its suppressed `O(X³)` terms.

## Analytic deduction and its exact input

Put `L=log q` and `δ=1-β`, where `β∈(0,1)` is a real zero of `L(s,χ)`.
Banks's cited Lemma 2.1(2.3), with its allowed `λ=3/2` and rounded-up
constants `C₁=1`, `C₂=5/4`, states for `X≥8`:

```text
S_1(X) + (1/2) S_0(X) ≤ (5/4)L + δ (log X)².        (E)
```

This is a **required analytic prerequisite**, not a consequence of the
existing `Dirichlet_L` AFP session.  At `X=q^64`, its last term is
`4096 δ L²`.  The elementary ramified-prime bound is `S_0(X)≤L`, since
the product of distinct prime divisors of `q` divides `q`.  Mertens and the
character's three possible prime values give

```text
64L - 2 ≤ S_all(q^64) = S_{-1}(q^64)+S_0(q^64)+S_1(q^64).
```

Using (D) and (E) thus gives

```text
(77/4)L ≤ 519 + 4096 δ L².
```

When `L≥54`, the constant `519` is at most `(77/8)L`, so

```text
(1-β) log q = δL ≥ 77/32768 > 0.                     (F)
```

The elementary implication from the four mass bounds to (F) is checked in
`Statement_Audit.thy`.  Once (D), (E), the character partition, and the
ramified bound have Isabelle proofs, (F) yields the uniform theorem for all
sufficiently large conductors.  The remaining finite conductors require a
separate argument if the target is every `q≥3`.

## Error and assumption ledger

1. **Wrong logarithm constant.**  The row-norm bound printed just before
   equation `log-g-arch` has a factor `2`.  Squaring it for Hadamard produces
   `log(4N²J)`, while the next displayed line says `log(2N²J)`.
   Formula (A) uses `4`; the main theorem is unaffected after increasing
   the explicit error constant. The checked two-embedding argument in
   `Archimedean_Feature_Bound.thy` directly bounds the *squared* feature-row
   norm by `2N²J R^(2J) (2N√q)^(2(r+s))`.
   `green_paper_gram_archimedean_log` in `Archimedean_Log_Bound.thy`
   checks the resulting logarithmic bound with `log(2N²J)`. This does
   not make the implication from the paper's printed row-norm bound valid.
2. **Missing prime 2.**  Lemma 5.1 proves the determinant valuation only for
   odd `p`, but equation `chi-p-bd` sums over every `p` with `χ(p)=-1`.
   Bound `p=2` separately as above.  No claim about a Frobenius valuation
   at `2` is used.
3. **Suppressed finite errors.**  The completion invokes several `O(X³)`
   terms without stating their constants.  Equation (B) supplies a finite
   inequality with a named prime-square sum; the bounds following it are
   sufficient to obtain the stated `8C+5` witness.  The constant is a
   reconstruction, not a quotation.
4. **Implicit arithmetic setup.**  Pairwise distinctness of the lattice
   coordinates requires the chosen square root to be irrational.  The bound
   `√|d|≤√q` requires the fundamental-discriminant relation `|d|=q`.
   Formal proofs of these belong to the quadratic-character bridge.
5. **Analytic citation.**  Green's note does not prove (E); it points to the
   companion OpenAI proof.  Banks makes the needed estimate explicit.  Its
   log-derivative estimate, including the relevant zero sum, remains to be
   developed in Isabelle.  The unconditional deduction has therefore not
   been checked yet.
