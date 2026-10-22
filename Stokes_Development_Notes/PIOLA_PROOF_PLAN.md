# Piola identity for smooth pullback

`Stokes_Forms.thy` now proves the pointwise identity

    exterior_top (cofactor_column f g j) x = 0.

Here `F(x) = jacobian f (at x)`, `G(x) = jacobian g (at (f x))`,
`F(x) ** G(x) = mat 1`, and the `i`th entry of the cofactor column is
`det F(x) * G(x)$i$j`. For a local inverse `g`, the target is the
Euclidean Piola identity `div (det F * F⁻¹ * e_j) = 0`.

## Checked coordinate calculation

Write `F[a,b] = ∂_b f_a`, `G = F⁻¹`, and use indices in the finite type
`'n`. The proof needs three derivative facts:

1. **Jacobi formula.**
   `∂_i det F = det F * Σ_{a,b} G[b,a] * ∂_i F[a,b]`.
2. **Inverse matrix derivative.** Differentiating `F ** G = 1` gives
   `∂_i G[i,j] = - Σ_{a,b} G[i,a] * ∂_i F[a,b] * G[b,j]`.
   This can use the *composite* Jacobian `G(x)` directly, so no separate
   derivative formula for `jacobian g` is needed.
3. **Mixed partial symmetry.**
   `∂_i F[a,b] = ∂_b F[a,i]` under a local `C²` hypothesis on `f`.

The product rule then reduces the desired divergence to

    det F * Σ_{i,a,b}
      (G[b,a] * ∂_i F[a,b] * G[i,j]
       - G[i,a] * ∂_i F[a,b] * G[b,j]).

Apply mixed partial symmetry to the first term and exchange the dummy
indices `i` and `b`; the sums cancel. This finite-sum step is checked as
`piola_coordinate_cancellation` in `Stokes_Forms.thy`. No integration
theorem is used.

## Isabelle proof dependencies

`matrix_det_differentiable` proves regularity of the determinant from
its finite permutation expansion. The later lemmas calculate the
derivative at the identity, reduce the invertible case using
`det (F ** K) = det F * det K`, and differentiate the local inverse
matrix equation. The finite-sum reindexing is independent of
analytic estimates.

### Source lemmas found in Isabelle2026-RC4

| Obligation | Existing lemma | Source theory |
| --- | --- | --- |
| Multilinearity of determinant | `det_row_add`, `det_row_mul` | `HOL-Analysis.Determinants` |
| Determinant of identity and product | `det_I`, `det_mul` | `HOL-Analysis.Determinants` |
| Coordinate derivative of a map | `jacobian_component` | `HOL-Analysis.Cartesian_Euclidean_Space` |
| Extract scalar `C²` components of a vector map | `Ck_on_component` | `HOL-Analysis.Higher_Differentiability_Multi` |
| Unpack `C²` into differentiability of first derivatives | `Ck_on_Suc_iff` | `HOL-Analysis.Higher_Differentiability_Multi` |
| Swap scalar mixed second partials | `mixed_coordinate_second_derivative_eq` | `HOL-Analysis.Higher_Differentiability_Multi` |
| Product derivative | `has_derivative_mult` | `HOL.Deriv` |

`HOL-Analysis.Analysis`, already imported by `Stokes_Forms.thy`,
imports `Ck_Implicit_Function`, which imports
`Higher_Differentiability_Multi`; these lemmas need no new session
dependency. The search of HOL-Analysis and AFP found no ready-made
Jacobi derivative or Piola theorem.

### Checked theorem ladder

1. Prove the determinant differential at the identity,
   `D det(I)[K] = trace K`. The determinant's permutation expansion or
   `det_row_add` and `det_row_mul` can provide this. Check explicitly
   that a nonidentity permutation cannot contribute a first-order
   term. Checked as `matrix_det_has_derivative_at_I`.
2. Derive `D det(F)[K] = det F * trace(G ** K)` when
   `F ** G = G ** F = I`, using `det_mul`. Checked as
   `matrix_det_has_derivative_invertible`.
3. For differentiable matrix-valued `F` and `G` whose product is the
   identity throughout a neighbourhood of `x`, derive
   `D G(x)[h] = - G(x) ** D F(x)[h] ** G(x)`. The neighbourhood
   hypothesis is essential: an inverse equation only at `x` cannot be
   differentiated. Checked as `matrix_inverse_field_derivative`.
4. Define `H i = frechet_derivative F (at x) (axis i 1)`
   (a matrix-valued directional derivative), and prove
   `H i $ a $ b = H b $ a $ i` from `Ck_on 2 f U`,
   `Ck_on_component`, `jacobian_component`, and
   `mixed_coordinate_second_derivative_eq`. Checked as
   `Ck_on_2_jacobian_mixed`.
5. Combine the two derivative formulas, the product rule,
   `piola_coordinate_cancellation`, and `exterior_top_coordinate`
   to close every `cofactor_column`. Checked as
   `cofactor_column_closed_C2`.

The core Piola theorem uses explicit matrix fields
`F, G : real^'n ⇒ real^'n^'n`. That isolates matrix calculus from chart
bookkeeping. It should assume their local inverse equation, their
pointwise differentiability, and the symmetry in step 4. A chart
corollary takes `F y = jacobian f (at y)` and
`G y = jacobian g (at (f y))`, with `f` of class `C²` on an open
neighbourhood and `g` a sufficiently regular local inverse. The
existing `exterior_top_pull_near_top_if_piola` consumes the result.
This final step is checked as `exterior_top_pull_near_top_C2`.

## Source check

Kupferman and Shachar, *The Piola identity and its applications*,
describe the classical coordinate proof through cancellation of mixed
partials. Their geometric proof uses a divergence theorem; the
coordinate proof avoids depending on the Stokes result being developed.
The supplied `lean-stokes-theorem-main` repository has no Piola theorem:
`LeanStokes/CubeStokes/Naturality.lean` explicitly describes its
coordinate `pullback` as coefficient precomposition, rather than the
Jacobian based pullback used here.
