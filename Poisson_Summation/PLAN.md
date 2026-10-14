# Poisson summation in Isabelle/HOL

## Target platform

Use `/Applications/Isabelle2026-RC3.app/bin/isabelle` and its bundled
`HOL-Analysis` and `HOL-Library` sessions. The local AFP `Fourier` session
builds against this release (verified 2026-10-13 with `isabelle build -d
/Users/lawrpau/isabelle/afp/devel/thys -o threads=8 -o document=false
Fourier`). Keep the Mathlib snapshot as a proof reference, not as the
implementation library.

## Goal

Prove the one-dimensional formula, for every real `x`,

\[
\sum_{n\in\mathbb Z} f(x+n)
  = \sum_{k\in\mathbb Z} \widehat f(k)\,e^{2\pi i kx},
\qquad
\widehat f(\xi)=\int_{\mathbb R}f(t)e^{-2\pi i\xi t}\,dt.
\]

The first theorem should assume:

1. `f : real ⇒ complex` is continuous.
2. There is a summable nonnegative majorant `M : int ⇒ real` such that
   `norm (f (t + real_of_int n)) ≤ M n` for every `t ∈ {0..1}` and `n : int`.
3. The values `k ↦ \widehat f (real_of_int k)` are absolutely summable.

The majorant is a convenient Isabelle interface for Mathlib's local uniform
summability assumption. It should also imply integrability of `f`; initially
that fact can be a separate lemma. Prove the formula at all `x`, with the
usual identity at `x = 0` as a corollary.

## Existing material

- Lean reference:
  `upstream/mathlib4/Mathlib/Analysis/Fourier/PoissonSummation.lean`, pinned
  in `README.md`. Its core is the Fourier-coefficient identity for the
  periodization, followed by reconstruction of a periodic function.
- The local AFP `Fourier` session has real-valued Fourier series of period
  `2*pi`, including `Fourier_Fejer_Cesaro_summable_simple` and a
  differentiability-based pointwise convergence theorem. It does **not**
  directly offer the complex-valued, unit-period Fourier coefficients needed
  here.
- Bundled `HOL-Analysis.Infinite_Sum` provides `summable_on`, `infsum`, and
  reindexing lemmas for sums over `int`. Prefer this theory to
  `Infinite_Set_Sum`, which its own header marks obsolete.
- Bundled `HOL-Analysis.Bochner_Integration` has `integral_suminf` for
  natural-number series; `HOL-Library.Periodic_Fun` has a period-one locale
  and integer-translation lemmas. Use these where their hypotheses match.
- The RC3 HOL and local AFP audit found no directly usable continuous
  real-line Fourier transform. Define the small transform above in this
  project unless a better existing API turns up during implementation.

## Proof sequence

1. **Preflight (done).** AFP `Fourier` builds with Isabelle2026-RC3. The
   bundled `Infinite_Sum`, Bochner-integration, and periodic-function APIs
   have been located. Check their exact theorem hypotheses while writing the
   first theory.
2. **Fourier conventions (done).** The `Poisson_Summation` session now
   defines normalized complex exponential coefficients of a `2*pi`-periodic
   function, with kernel `cis (-(of_int k * x))`. The real and imaginary
   projections are proved. The real-line transform `\widehat f` is defined,
   and its normalization against the `2*pi` coefficients is proved.
3. **Uniqueness bridge (done).** `Complex_Fourier_Series.thy` proves that a
   continuous complex-valued `2*pi`-periodic function with all exponential
   Fourier coefficients zero is zero, using AFP Fejér convergence for its
   real and imaginary parts. Built with Isabelle2026-RC3 on 2026-10-13.
4. **Periodization (done).** `Periodization.thy` defines
   `P_f(x) = ∑_{n∈ℤ} f(x+n)` using `infsum`. The majorant gives absolute
   convergence, uniform convergence on `{0..1}`, continuity everywhere,
   period one, and integrability of `f` over the real line. The theory also
   proves integer-indexed tiling and exchanges the periodization sum with
   the integral.
5. **Coefficient identity (done).** `Fourier_Transform.thy` proves
   the unit-period identity
   \[
   \int_0^1 P_f(t)e^{-2\pi ikt}\,dt=\widehat f(k)
   \quad(k\in\mathbb Z).
   \]
   For `G(t) = P_f(t/(2*pi))`, affine scaling and periodicity give
   \[
   \frac{1}{2\pi}\int_{-\pi}^{\pi}G(t)e^{-ikt}\,dt
       = \widehat f(k)
   \quad(k\in\mathbb Z).
   \]
   This is the theorem `periodization_complex_fourier_coefficient`. The
   integer frequency makes the exponential unchanged by translation
   through an integer.
6. **Reconstruction (done).** `Reconstruction.thy` defines the complex
   Fourier series and proves continuity and period `2*pi` from absolute
   summability. Its coefficients are the supplied sequence. The complex
   uniqueness theorem then identifies it with the rescaled periodization,
   giving the all-`x` theorem `poisson_summation`.
7. **Usable corollaries (done).** The `x = 0` formula is
   `poisson_summation_zero`. The theorem `poisson_summation_power_decay`
   replaces both summability hypotheses by bounds of the form
   `A * (1 + |x|) powr (-p)` for `f` and
   `B * (1 + |ξ|) powr (-q)` for its transform, with real `p,q > 1`.
   `Tent_Function.thy` checks the normalization: the tent function has
   periodization 1 and Fourier samples equal to 1 at zero and 0 at every
   other integer. The samples are calculated both through the coefficient
   identity and directly from the real-line integral.
8. **Gaussian example (done).** `Gaussian_Example.thy` imports
   `HOL-Probability.Characteristic_Functions`, obtains the Fourier
   transform of the standard normal density from its characteristic
   function, and proves quadratic decay estimates for the density and
   its transform. `standard_gaussian_poisson` gives the explicit summation
   formula at every real shift.
9. **Theta transformation (done).** `Fourier_Transform.thy` proves the
   positive-dilation rule for the real-line Fourier transform.
   `Gaussian_Example.thy` uses it to compute the transform and quadratic
   decay bounds for dilated standard normal densities. Applying Poisson
   summation and proving summability of the theta series yields
   `jacobi_theta_transformation`,
   `sqrt t * jacobi_theta t = jacobi_theta (1/t)` for every `t > 0`.

## Boundaries of the first milestone

- Work in one real dimension and use complex-valued functions.
- Do not make Schwartz-space infrastructure a prerequisite. Mathlib's
  Schwartz corollary can follow once such an API exists in Isabelle.
- Do not require a general Fourier-inversion theorem. Fejér uniqueness is
  enough when the Fourier samples are absolutely summable.
- Make the summation convention over `int` explicit with RC3 `infsum`.
  The available `integral_suminf` lemma is indexed by `nat`; for exchanging
  the integer sum and integral, split positive and negative integers or prove
  a reusable bridge to `infsum`.

## Completion checks

- A new `Poisson_Summation` Isabelle session builds under
  Isabelle2026-RC3 with no admitted facts.
- The all-`x` theorem and the `x = 0` corollary have explicit integrability
  and summability facts available to downstream users.
- The Fourier normalization is tested in `Tent_Function.thy`. Both explicit
  sums equal 1 for every `x`.
