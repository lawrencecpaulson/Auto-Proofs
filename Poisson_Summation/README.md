# Poisson summation project

See `PLAN.md` for the proposed Isabelle theorem and proof sequence.

The `Poisson_Summation` session contains six theories:
`Complex_Fourier_Series.thy` proves uniqueness for continuous complex
`2*pi`-periodic functions via AFP Fourier's real-valued Fejér theorem.
`Periodization.thy` proves convergence, continuity, period one, real-line
integrability, integral exchange, and integer-cell tiling under a summable
majorant. `Fourier_Transform.thy` defines the real-line transform and proves
that its integer samples are the `2*pi`-periodic Fourier coefficients of the
rescaled periodization. This gives the coefficient identity needed for
reconstruction via uniqueness. `Reconstruction.thy` proves the all-`x`
Poisson formula, its `x = 0` corollary, and a version assuming power decay
of `f` and its Fourier transform with exponents greater than one. The
`Tent_Function.thy` checks the Fourier normalization: the tent function
periodizes to 1, and its integer Fourier samples are 1 at zero and 0
elsewhere. The sample values are also calculated directly from the
real-line integral, independently of the coefficient identity.
`Gaussian_Example.thy` derives the Fourier transform of the standard normal
density from `HOL-Probability`'s characteristic function theorem, proves
quadratic decay bounds on both sides, and obtains an explicit Gaussian
Poisson identity for every real shift. A Fourier scaling lemma gives the
transform for every positive Gaussian dilation. Applying Poisson summation
to that family proves the Jacobi theta transformation
`sqrt t * jacobi_theta t = jacobi_theta (1/t)` for `t > 0`, where
`jacobi_theta t` is the complex-valued sum of `exp (-pi*t*n^2)` over integer
`n`. Its summability for `t > 0` is proved separately. The session builds with
Isabelle2026-RC3:

```sh
USER_HOME=/private/tmp/poisson_rc3_user \
  /Applications/Isabelle2026-RC3.app/bin/isabelle build \
  -d /Users/lawrpau/isabelle/afp/devel/thys \
  -d /Users/lawrpau/isabelle/Auto-Proofs/Poisson_Summation \
  -o threads=8 -o document=false Poisson_Summation
```

The upstream Lean reference is in
`upstream/mathlib4/Mathlib/Analysis/Fourier/PoissonSummation.lean`.
The complete Mathlib source snapshot, its `lake-manifest.json`, and the eight
version-pinned package sources are stored under `upstream/mathlib4/`. The
corresponding Lean and Std library sources are under `upstream/lean4/src/`.

- Mathlib revision: `10f994e919838c3cc14b37a58c9aa31f0c35ef73`
- Lean toolchain: `leanprover/lean4:v4.35.0`
- Lean source tag: `leanprover/lean4` `v4.35.0`
- Sources: `leanprover-community/mathlib4` and `leanprover/lean4` on GitHub
- Retrieved: 2026-10-13

The package sources are in `upstream/mathlib4/.lake/packages/`, at the
revisions specified by `upstream/mathlib4/lake-manifest.json`. A source import
scan from `PoissonSummation.lean` found 4,390 reachable Lean modules and no
unresolved imports. The upstream snapshots are ignored by Git so that future
Isabelle work can be tracked here without adding thousands of vendored files.

No Lean compiler binary or compiled Mathlib cache is included. This is a
source reference; running it requires the toolchain named above.
