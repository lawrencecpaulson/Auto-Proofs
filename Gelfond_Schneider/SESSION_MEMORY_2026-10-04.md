# Gelfond-Schneider Session Memory — 2026-10-04

## Latest status (supersedes the earlier checkpoints below)

The public `gelfond_schneider` theorem now uses the scaled
power-basis norm proof and is fully processed by jEdit I/Q with zero
errors. The `Baker_Two_Logarithms` import and proof were removed from
the public theory. `Baker/Standalone/ROOT` now sets
`quick_and_dirty = false`. The strict standalone build **succeeded**
on October 4, 2026, in 5m47s for the session itself.
See “Public theorem connected” near the end for the proof path. Earlier
“remaining work” descriptions below document intermediate states and
are no longer current.

## Objective

Finish the **standalone Gelfond-Schneider theorem**, and stop thinking about the
broader Baker project unless it is strictly needed for that goal.

The right target is:

- `Baker/Gelfond_Schneider.thy`
- theorem `gelfond_schneider`

But the current critical path runs through the newer power-basis norm route,
not through the old `Baker_Two_Logarithms` detour.

## Honest current status

We are **not finished yet**, but the project is much closer to completion than
it was at the start of the day.

The important update is:

- `rho_inv_lt` is no longer the conceptual blocker.
- The next serious mathematical task is `rho_upper`.
- After that, the remaining work should mostly be integration/splicing rather
  than new mathematics.

So the current state is:

1. The field-norm infrastructure exists.
2. The concrete `rho_inv_lt` step is essentially done.
3. The concrete `rho_upper` step is still assumed, not yet derived.
4. The public theorem `Gelfond_Schneider.thy` still uses the temporary
   `Baker_Two_Logarithms` route.

## What is genuinely in place now

### 1. Power-basis field norm machinery

The theory

- `Baker/Gelfond_Schneider_Power_Basis_Field_Norm.thy`

contains the key absolute-norm infrastructure for the power-basis route.

Most important theorem:

- `inverse_gs_abs_galois_norm_lt_powr`
  in `Gelfond_Schneider_Power_Basis_Field_Norm.thy`

This proves the inverse norm bound once we know:

- `x ∈ K`
- `algebraic_int x`
- `x ≠ 0`
- `1 < c5`
- `r > 0`

That is exactly the shape needed for the concrete `rho_inv_lt` goal.

### 2. Concrete local facts about `rho`

In

- `Baker/Gelfond_Schneider_Power_Basis_Norm_Target.thy`

the following concrete lemmas are already present:

- `rho_in_K`
- `rho_order_pos`
- `rho_algebraic_int_nonzero`

These are the key bridge facts needed to feed the field-norm lemma above.

### 3. The concrete `rho_inv_lt` bridge is effectively done

In

- `Baker/Gelfond_Schneider_Power_Basis_Norm_Target.thy`

inside the concrete locale

- `gelfond_schneider_power_basis_field_norm_target`

the `rho_inv_lt` subgoal is discharged by combining:

- `rho_in_K`
- `rho_algebraic_int_nonzero`
- `rho_order_pos`
- `inverse_gs_abs_galois_norm_lt_powr`

The relevant discharge is at the end of the big `sublocale TARGET` proof, at
the final `show ... inverse (gs_abs_galois_norm rho) < c5 powr of_nat r`.

This means:

- the inverse inequality is no longer the main obstacle;
- if there are failures there tomorrow, they should be proof-engineering
  failures, not missing mathematics.

### 4. The generic contradiction interfaces already exist

Important files:

- `Baker/Gelfond_Schneider_Number_Field_Target.thy`
- `Baker/Gelfond_Schneider_Number_Field_Norm_Target.thy`
- `Baker/Gelfond_Schneider_Power_Basis_Norm_Target.thy`
- `Baker/Gelfond_Schneider_Power_Basis_Norm_Direct.thy`

Important theorems already present:

- `coordinate_contradiction`
  in `Gelfond_Schneider_Power_Basis_Norm_Target.thy`
- `no_gelfond_schneider_data_of_power_basis_norm_target_existence`
  in `Gelfond_Schneider_Power_Basis_Norm_Target.thy`
- `gelfond_schneider_of_power_basis_norm_target_existence`
  in `Gelfond_Schneider_Power_Basis_Norm_Target.thy`
- `no_gelfond_schneider_data_of_finite_normal_power_basis_norm_target_existence`
  in `Gelfond_Schneider_Power_Basis_Norm_Direct.thy`
- `gelfond_schneider_of_finite_normal_power_basis_norm_target_existence`
  in `Gelfond_Schneider_Power_Basis_Norm_Direct.thy`

Important caveat:

these are only as strong as the assumptions of the enclosing locales.  The big
remaining assumption is still `rho_upper`.

## What is still conditional

This is the most important point to remember tomorrow.

In

- `Baker/Gelfond_Schneider_Power_Basis_Norm_Target.thy`

the concrete locale

- `gelfond_schneider_power_basis_field_norm_target`

still has an assumption

- `rho_upper`

of the form:

- `gs_abs_galois_norm rho ≤ c14 powr of_nat r * ...`

So although the field-norm route is now much more concrete than before, it is
**not yet fully instantiated**.

Put differently:

- `rho_inv_lt` is basically solved;
- `rho_upper` is the last big quantitative estimate still missing on the
  critical path.

## Best current understanding of the remaining gap

The next serious theorem to prove is:

- the concrete `rho_upper` assumption inside
  `gelfond_schneider_power_basis_field_norm_target`
  in `Baker/Gelfond_Schneider_Power_Basis_Norm_Target.thy`

This should show:

- `gs_abs_galois_norm rho ≤ c14 powr of_nat r * of_nat r powr (...)`

for the concrete `rho`.

### Why this looks feasible

This no longer looks like a missing “big idea” problem.

We already have:

1. the power-basis recovery layer;
2. basis-entry and inverse-entry bounds;
3. house machinery;
4. absolute field-norm lemmas; and
5. the surrounding contradiction interfaces.

In particular, `Baker/Gelfond_Schneider_Power_Basis_Field_Norm.thy` contains:

- `gs_abs_galois_norm_le_cmod_emb_mul_house_pow`
- `gs_abs_galois_norm_le_cmod_emb_mul_bound_pow`

These strongly suggest the intended route:

1. bound `cmod rho` at the distinguished embedding;
2. bound `gs_house rho`;
3. combine them using the field-norm lemma;
4. conclude the desired `rho_upper`.

### Likely route to `rho_upper`

The expected proof strategy is:

1. Work inside
   `gelfond_schneider_power_basis_field_norm_target`.
2. Reuse the existing local facts:
   - `rho_in_K`
   - `rho_algebraic_int_nonzero`
   - `rho_order_pos`
3. Prove a concrete embedding bound for `rho`, probably at `emb i0`, where
   `emb i0 = identity K`.
4. Prove or reuse a `gs_house rho ≤ H` style estimate.
5. Apply
   `gs_abs_galois_norm_le_cmod_emb_mul_bound_pow`.
6. Massage constants into the exact `c14 powr of_nat r * ...` shape.

The key question tomorrow is not “what theorem should we prove?” but “which
existing upper bounds already in the project can be reused to produce the two
inputs for the field-norm lemma?”

## Relation to the older house/product route

There is a parallel scaffold in:

- `Baker/Gelfond_Schneider_Power_Basis_House_Target.thy`
- `Baker/Gelfond_Schneider_Power_Basis_Product_Target.thy`

Those files still package:

- `gs_house rho ≤ H`, and
- `cmod rho * gs_house rho^(deg - 1)` style upper bounds

through abstract assumptions.

That is useful because it suggests the norm route is not inventing something
new; it is specializing an already understood estimate into the field-norm
language.

If tomorrow’s direct `rho_upper` proof gets messy, a good fallback is:

1. identify the strongest already-ported `cmod rho` / `house rho` estimate;
2. derive the norm estimate from it, instead of reproving everything from
   scratch.

## What still blocks the final public theorem

Even after `rho_upper` lands, there are still two finishing tasks:

1. splice the completed power-basis norm route cleanly into the standalone
   contradiction chain; and
2. replace the temporary import/use of `Baker_Two_Logarithms` in
   `Baker/Gelfond_Schneider.thy`.

At the moment:

- `Baker/Gelfond_Schneider.thy`

still imports:

- `Baker_Two_Logarithms`

and the theorem

- `no_gelfond_schneider_data`

still ends by invoking:

- `baker_two_logarithms_homogeneous_irrational_core`

That is the old detour and should ultimately disappear.

## Theories that were in usable shape by the end of today

From the interactive work today, the following were reported as loading cleanly
at various points:

- `Baker/Gelfond_Schneider_Number_Field_Target.thy`
- `Baker/Gelfond_Schneider_Power_Basis_Norm_Target.thy`
- `Baker/Gelfond_Schneider_Power_Basis_Norm_Direct.thy`

Also relevant:

- `Baker/Gelfond_Schneider_Power_Basis_Field_Norm.thy`

contains the important new norm lemmas and is central tomorrow.

Important caution:

- “loads in jEdit” is not the same as “the full standalone session is
  mathematically finished”.
- The session still has `quick_and_dirty = true` in
  `Baker/Standalone/ROOT`, so successful builds can hide remaining `sorry`s.

## Session / build notes

### Standalone session root

The standalone session is defined in:

- `Baker/Standalone/ROOT`

Session name:

- `Gelfond_Schneider_Standalone`

Current session dependencies listed there include:

- `Algebraic_Numbers`
- `HOL-Complex_Analysis`
- `HOL-Examples`
- `Linear_Inequalities`
- `New_Algebra`

### Important caveat about `New_Algebra`

`New_Algebra` is not a standard released Isabelle session in the current
installation, so if jEdit or `isabelle build` complains about bad imports, the
cause is usually that the local `New-Algebra` checkout has not been supplied as
a session root correctly.

This was a recurring source of confusion.

### Image-building note

The image build that definitely worked today was:

```sh
isabelle build -b -o record_theories=true \
  -d /Users/lawrpau/isabelle/Auto-Proofs/Baker/Core/Vanishing \
  Gelfond_Schneider_Vanishing_Image
```

This succeeded in about four minutes and is useful for faster startup on the
older vanishing/matrix side.

For the standalone session, remember:

- `-b` both checks and produces a heap image;
- without `-b`, you do not get the heap image.

### About `record_theories=true`

This build option tells Isabelle to record more theory/source metadata in the
heap.  That is useful for downstream interactive use and dependency browsing.
It is not a mathematical option.

## Tooling notes

### I/Q and I/R

The intent was to use the jEdit-side interactive bridge, but in this Codex
surface the direct I/Q and I/R tools were not actually available as callable
tools.  Work therefore proceeded by:

- shell inspection;
- theory editing on disk;
- ordinary Isabelle session/file checking.

If tomorrow a true I/Q bridge is available again, prefer it for live jEdit work.

### jEdit

This machine repeatedly exhibited odd jEdit hangs or blank-window startup
behavior, especially when the wrong session root or dependency setup was used.

If jEdit is relaunched tomorrow, start from the standalone session and focus on
one of these files first:

- `Baker/Gelfond_Schneider_Power_Basis_Field_Norm.thy`
- `Baker/Gelfond_Schneider_Power_Basis_Norm_Target.thy`

Those are the two files most directly on the critical path.

## Recommended first move tomorrow

Open:

- `Baker/Gelfond_Schneider_Power_Basis_Norm_Target.thy`

and go straight to the concrete locale:

- `gelfond_schneider_power_basis_field_norm_target`

Then focus only on the assumption currently called:

- `rho_upper`

The first question to answer there is:

- can the needed bound be obtained directly from already-ported `cmod rho`
  and `gs_house rho` estimates, via
  `gs_abs_galois_norm_le_cmod_emb_mul_bound_pow`?

If yes, that is the shortest route to the finish.

## Suggested exact work order for tomorrow

1. Re-check the local proof state around `rho_upper` in
   `Gelfond_Schneider_Power_Basis_Norm_Target.thy`.
2. Search for the strongest existing concrete upper bounds on:
   - `cmod rho`
   - `gs_house rho`
3. Try to derive the norm bound using
   `gs_abs_galois_norm_le_cmod_emb_mul_bound_pow`.
4. Once `rho_upper` is proved, re-check the enclosing locale instantiation.
5. Then wire the completed power-basis norm route into
   `Gelfond_Schneider.thy` and remove the old two-logarithm dependency.
6. Only after that, do cleanup/refactoring.

## Cleanup notes for later

Even once the proof is finished, the current power-basis norm bridge is too
long and assumption-heavy.  The final cleanup pass should:

- replace long duplicated assumption lists with locales or shorter structural
  lemmas;
- remove the old Baker detour from the standalone theorem;
- consider renaming/repackaging the directory structure so the finished AFP
  entry is clearly standalone Gelfond-Schneider rather than “Baker”.

But that cleanup is **after** the mathematical completion, not before.

## Bottom line

The project is now in a good position to finish.

The main remaining mathematical task is:

- prove the concrete `rho_upper` in
  `Baker/Gelfond_Schneider_Power_Basis_Norm_Target.thy`

After that, the rest should be integration and cleanup rather than a new deep
mathematical development.

## Evening update — October 4, 2026

The standalone Gelfond–Schneider development advanced in the loaded jEdit
session. `Baker_Two_Logarithms.thy` remains abandoned. All lemmas below were
edited through I/Q and checked with `get_diagnostics(wait_until_processed=True)`;
each edited theory reported zero errors. No `sorry` or `oops` occurs in these
edited theories.

- `Gelfond_Schneider_Power_Basis_Field_Norm.thy`:
  `gs_abs_galois_norm_le_from_analytic_house_bounds` combines a bound at the
  identity embedding with a bound on the house into the exact norm exponent
  needed for `rho_upper`.
- `Gelfond_Schneider_Order.thy`: the circle node distance bound, maximum
  modulus wrapper, entire finite-zero quotient, and contour product lower
  bound are proved.
- `Gelfond_Schneider_Vanishing.thy`: the auxiliary function has an entire
  normalization by its interpolation-node zeros. The auxiliary exponential
  sum bound, normalized circle bound, product identity, Cauchy derivative
  bound, specialized minimum-order derivative bound, balanced-dimension
  circle clearance, and explicit bound on `gs_rho_idx` are proved.
- `Gelfond_Schneider_Scaled_Bounded.thy`:
  `gs_bounded_vec_min_order_derivative_bound` plugs the existing bounded
  integer-vector coefficient estimate into the new analytic derivative bound.
- `Gelfond_Schneider_Statement_Shell.thy` and
  `Gelfond_Schneider_Rho_Bounds.thy`: `gs_q_choice_ge_four` and
  `gs_q_choice_circle_clearance` prove that the chosen `q` supplies the contour
  clearance once `gs_n h q ≤ r`.

The key current derivative estimate has the shape

`fact r * (q² * V * exp(T * m * (1+r/q)) / (m*r/q)^(m*r)) * (2*m+1)^(m*r)`,

where `V` is the bounded coefficient norm and
`T = q * (1 + cmod(gs_b d)) * cmod(gs_z d)`. This is a genuine analytic bound,
but has **not** yet been converted to `rho_upper`.

**Important correction to the earlier "one goal" description:** proving
`rho_upper` from the current `gelfond_schneider_power_basis_field_norm_target`
locale assumptions is not the right formulation. The locale allows an
arbitrarily enlarged entry bound `A` while `c14` stays fixed. Its witness
bound grows with `A`, and integer kernel witnesses can be scaled accordingly.
The intended quantitative theorem therefore needs a *specified* entry bound
as a function of `q` and the fixed algebraic data, with `c14` chosen to
dominate its constants. The locale also leaves `h` independent of the field
degree `D`; the norm argument needs their intended relation (for example
choosing `h = D` in the existential construction). These are missing
parameter links, not Isabelle tactic failures.

Next work: derive an explicit uniform bound on the conjugates of the
row-scaled matrix entries; choose the resulting concrete `A`, `h`, and `c14`
before `q`; prove a house bound for `rho`; combine it with the checked
analytic identity-embedding bound to obtain the actual norm estimate. The
public theorem still uses the older Baker detour and has not been rewired.

## Later progress on October 4

The loaded I/Q session checked these further lemmas with zero errors:

- `Gelfond_Schneider_Power_Basis_Norm_Target.thy` now has a uniform
  conjugate bound for row-scaled matrix entries and the explicit
  `gs_concrete_entry_bound`. It also has
  `gs_house_rho_le_of_bounded_vec`, an explicit bound for all conjugates of
  `rho`, and `gs_rho_cmod_le_of_bounded_vec`, the analytic bound at the
  distinguished embedding. These are the two main inputs to the norm bound.
- `Gelfond_Schneider_Rho_Bounds.thy` now has
  `gs_q_choice_le_two_mr`, `gs_aux_exp_growth_le`,
  `gs_balanced_radius_ge_sqrt`, `gs_balanced_radius_power_ge`, and
  `gs_q_choice_radius_power_ge`. These absorb the auxiliary exponential
  term into a fixed constant to the power `r` and convert the Cauchy
  denominator into a factor of at least
  `r powr (gs_m h * r / 2)`.

The remaining quantitative work is to bound the concrete matrix entry
estimate and bounded witness by a uniform constant to the power `r` times
a controlled power of `r`, combine the identity bound and house bound,
and choose `h = D` and `c14` sufficiently large in the existential
construction. The current `rho_upper` locale assumption cannot be
removed for arbitrary `A`, `c14`, and `h`.

**Sharper bounds checked later tonight:** The balanced equality yields
`q ≤ sqrt(2mr)`. The generic lemma `gs_entry_power_le_r_half` converts
the concrete matrix entry bound to
`A ≤ K^r * r powr (r/2)`. The concrete lemma
`gs_concrete_entry_bound_le_growth` now has exactly this sharp form; the
earlier `r^r` bound is too weak for `rho_upper`.

The witness bound is now explicit:
`gs_witness_bound_le_growth_simple` bounds the real size of the canonical
integer witness by a fixed constant times `r * K^r * r powr (r/2)`.
The ceiling step and the extra `q²` factor are checked.

The house side is substantially advanced:
`gs_house_aux_factor_le_growth` bounds the combined `c1` scale and
auxiliary factors by `K^r * r powr (r/2)`;
`gs_house_rho_le_growth_absorbed` bounds the house by
`gs_house_growth_base ^ r * r powr (r + 3/2)`, with
`gs_house_growth_base_pos` proved. This is the exact exponent required
by `gs_abs_galois_norm_le_from_analytic_house_bounds`.

For the point side, `gs_scale_factor_le_r_power`,
`gs_negative_powi_norm`, `gs_aux_exp_growth_le`,
`gs_q_choice_radius_power_ge`, `fact_le_power` (library), and
`gs_point_growth_power_identity` now supply the separate numerical
pieces. They have **not yet been assembled** into the needed point
bound. The final parameter choice `h = D`, sufficiently large `c14`,
and the public theorem integration also remain.

## Final evening checkpoint — October 4

The point estimate was assembled and checked. Inside the independent
estimates locale, `gs_rho_cmod_le_growth_absorbed` proves the exact
`c13^r * r powr ((3-m)r/2 + 3/2)` bound, with
`gs_point_growth_base_pos`. The house estimate has the matching
`gs_house_rho_le_growth_absorbed` form.

The large concrete locale was **split**. New parent
`gelfond_schneider_power_basis_field_norm_estimates` contains the
analytic, conjugate, witness, and norm estimates without assuming
`rho_upper` or an entry house bound. The original
`gelfond_schneider_power_basis_field_norm_target` remains as a child for
the legacy conditional interface. Its `entry_bnd` assumption was
corrected to refer to `EH.ehouse`; the prior unqualified `ehouse`
introduced an unintended universally quantified function.

In the parent, `gs_rho_upper_verified` proves the **exact old
`rho_upper` proposition** from three explicit parameter conditions:
`h = D`, `A = gs_concrete_entry_bound`, and
`gs_house_growth_base^(D-1) * gs_point_growth_base ≤ c14`.
The new locale
`gelfond_schneider_power_basis_field_norm_verified` assumes exactly
these choices in addition to the parent data and interprets the
legacy conditional target. Its `coordinate_contradiction` checks in
jEdit with zero errors. This is a genuine proof of the quantitative
step under the necessary parameter choices, not a reuse of
`rho_upper`.

**Remaining work:** construct a global witness of the verified locale
for the finite normal power-basis data by choosing `h = D`, choosing
`c14` large before `q`, defining `q = gs_q_choice ...`, and setting
`A = gs_concrete_entry_bound`; prove/instantiate its remaining
arithmetic and matrix representation assumptions. Then connect the
verified locale through the existential target interface and replace
the old Baker dependency in the public theorem. The standalone
Gelfond–Schneider theorem is **not finished** yet.

## Instantiation audit — October 4, around 20:00 UTC

The checked `gelfond_schneider_power_basis_field_norm_verified` locale
has **no `rho_upper` assumption**. It proves and interprets the old
conditional field-norm target from:

- `h = D`;
- `A = gs_concrete_entry_bound`; and
- `gs_house_growth_base^(D-1) * gs_point_growth_base ≤ c14`.

All seven edited `.thy` files listed in the earlier checkpoint have no
`sorry` or `oops` text; I/Q diagnostics for the two central theories
reported zero errors after full processing.

The outstanding existential construction is more than arithmetic
bookkeeping. The verified locale still assumes `entryK` and integer
structure constants `mult_repr` for multiplication of row-scaled
entries in the power basis. The available finite normal primitive
power-basis theorem gives **rational** power-basis coordinates and an
algebraic-integer generator. It does not by itself make the power basis
an integral basis or show these particular row entries preserve
`Z[eta]`. `Gelfond_Schneider_Integral_Basis_Bridge.thy` can produce
structure constants from an `integral_span` assumption, but existence
of that integral-span basis has not been located in the local
`New-Algebra` sources. The older checklist's suggestion that any
monogenic order suffices overlooks the need for the row entries to lie
in that order.

Next investigation should choose a sound way to discharge `mult_repr`:
an actual integral basis and its existence theorem, or a revised
scaled system whose entries provably lie in `Z[eta]`. Do not assert
that the public theorem follows just by selecting `c14`. The public
`Gelfond_Schneider.thy` still imports `Baker_Two_Logarithms`, and
`Baker/Standalone/ROOT` still has `quick_and_dirty = true`.

## Rational scaling bridge — October 4, around 20:20 UTC

The scalar-denominator alternative has now been formalized in
`Gelfond_Schneider_Power_Basis_Norm_Target.thy`, following the verified
locale. Full I/Q file processing reported zero errors after each final
edit. The new checked results are:

- `finite_Rats_common_denominator`: a finite set of rational complex
  numbers has a common positive integer denominator.
- `rational_coordinates_of_product`: every `x * eta^j`, for `x ∈ K`,
  has rational power-basis coordinates.
- `finite_entries_have_scaled_integer_structure_constants` and
  `finite_matrix_has_scaled_integer_structure_constants`: a single
  positive integer clears all multiplication coordinates for a finite
  matrix over `K`.
- `complex_smult_mat_vec` and
  `bounded_kernel_of_scaled_integer_structure_constants`: the
  existing bounded integer kernel theorem applies to an integer
  multiple of the matrix, and its kernel vector remains a kernel
  vector of the original matrix.
- `finite_K_matrix_has_bounded_algebraic_integer_kernel`: every
  sufficiently underdetermined finite `K`-valued matrix has a nonzero
  algebraic-integer kernel vector with bounded integer power-basis
  coordinates. The bound is explicit in the maximum absolute
  structure constant, but this maximum has no useful growth estimate
  yet.
- `row_scaled_entry_in_K_from_rational_coordinates` proves the
  specific Gelfond–Schneider entries are in `K` without an `entryK`
  assumption. `row_scaled_matrix_has_bounded_algebraic_integer_kernel`
  applies the new theorem to that matrix.
- `scaled_structure_constants_transport_to_embedding` transports the
  integer coordinate identity through every field embedding.
- `scaled_structure_constant_abs_le` uses inverse power-basis
  recovery to bound each integer structure constant by
  `ceiling (card E * power_basis_inverse_bound *
            (L * A * power_basis_entry_bound))`
  when the entry house is at most `A`. This pins down the sole extra
  factor introduced by rational denominator clearing: `L`.
- `finite_K_matrix_has_house_bounded_algebraic_integer_kernel`
  combines that bound with the scaled integer kernel theorem. Its
  witness bound is exactly
  `2 * int (q * D) * max 1
    (ceiling (card E * power_basis_inverse_bound *
      (L * H * power_basis_entry_bound)))`.
  `row_scaled_matrix_has_house_bounded_kernel` specializes this to
  the Gelfond–Schneider matrix from the rational coordinates.

The latest full I/Q check of
`Gelfond_Schneider_Power_Basis_Norm_Target.thy` reported **0 errors**
with all 1,945 commands processed. It reported parser ambiguity
warnings for `$`/`$$` notation in these new lemmas; Isabelle resolved
them and checked the proofs. No `sorry` or `oops` occurs in the
`Gelfond_Schneider_*.thy` files.

Thus an integral basis is **not needed for qualitative kernel
existence**. With the new inverse-basis bound, the missing quantitative
step is specifically a bound on the common denominator `L` controlled
by fixed field/data constants and at most exponential in the order
`r`. The finite-set argument picks `L` *after* `q` is fixed, so its
output cannot yet be used to choose `c14` before `q`. The analytic
`rho_upper` proof also still expects the old unscaled witness bound;
its witness-growth base must be enlarged to absorb `L`. Until those
two changes are proved, the checked row-scaled kernel does not
instantiate the verified contradiction locale or complete the public
Gelfond–Schneider theorem.

## Uniform exponential denominator — October 4, around 20:55 UTC

The quantitative denominator gap described above is now substantially
closed in `Gelfond_Schneider_Power_Basis_Norm_Target.thy`. Full jEdit I/Q
processing reported **zero errors** after the latest edits.

- `data_generators_and_affines_uniform_product_denominator` supplies
  one fixed positive integer `T` for products of `gs_a d`, `gs_w d`,
  `eta`, and every `of_nat u + of_nat v * gs_b d`.
- `system_coefficients_times_basis_have_uniform_denominator` shows
  that `T^(k+a*l+b*l+j)` clears the power-basis coordinates of
  `gs_system_coeff d a b l k * eta^j`.
- `gs_system_coeff_idx_basis_exponent_le` and
  `row_scaled_matrix_entries_have_uniform_exponential_denominator`
  pad all relevant exponents to
  `N = gs_n h q + 2 * (gs_m h * q) + D`. Thus `T^N` clears every
  multiplication coordinate of the actual row-scaled matrix. `T` is
  selected from the fixed data before `q`.
- `finite_K_matrix_has_house_bounded_kernel_given_denominator`
  refactors the bounded kernel proof to accept a specified `L`.
  `row_scaled_matrix_has_exponential_denominator_bounded_kernel`
  applies it with `L = T^N`, obtaining algebraic-integer kernel
  coordinates bounded by
  `2 * int (q*q*D) * max 1
    (ceiling (card E * power_basis_inverse_bound *
      (T^N * H * power_basis_entry_bound)))`.
- In the quantitative estimates locale,
  `gs_row_denominator_exponent_le_order` proves
  `N ≤ (1 + 4*gs_m h*gs_m h + D)*r` for `r>0` and `gs_n h q ≤ r`.
  `gs_row_denominator_power_le_order` bounds `T^N` by a fixed base
  raised to `r`.
- `gs_witness_bound_le_growth_with_denominator` proves the enlarged
  witness-growth inequality. It replaces the old entry growth base
  `K` with `K * T^(1+4*m*m+D)`.

The **next mathematical task** is to feed this enlarged witness bound
through the house and point analytic estimates and the field norm
bound. The old `gs_rho_upper_verified` only accepts a witness bound
without `T^N`; a generalized `rho_upper` lemma needs larger house
and point growth bases, with `c14` selected to dominate their product.
After that, instantiate the contradiction for the concrete kernel
and reconnect the public theorem. Do not claim the theorem is done;
`Gelfond_Schneider.thy` still imports abandoned
`Baker_Two_Logarithms.thy`, and `Standalone/ROOT` still has
`quick_and_dirty = true`.

## Direct scaled-denominator contradiction — October 4, around 21:10 UTC

The analytic and algebraic parts of the scaled route now meet in a
**checked contradiction locale**. The latest full jEdit I/Q processing
of `Gelfond_Schneider_Power_Basis_Norm_Target.thy` reported zero errors
with all commands processed.

The analytic locale `gelfond_schneider_power_basis_field_norm_estimates`
no longer assumes integral multiplication constants. That unused
assumption was moved to its legacy child locales, whose old
contradiction proofs still check.

New checked analytic results:

- `gs_house_rho_le_growth_with_factor` and
  `gs_house_rho_le_growth_absorbed_with_factor` handle a witness growth
  base enlarged from `K` to `K*U`; the house base becomes
  `gs_house_growth_base*U^2`.
- `gs_rho_cmod_le_growth_absorbed_with_factor` gives point base
  `gs_point_growth_base*U`.
- `gs_norm_upper_from_concrete_house_point_with_factor` combines those
  estimates, and
  `gs_rho_upper_from_concrete_witness_with_denominator` applies them
  with `U = T^(1+4*gs_m h*gs_m h+D)`.

The denominator can now be supplied *before* `q`:

- `system_coefficients_times_basis_from_product_denominator`;
- `row_scaled_matrix_entries_from_product_denominator`;
- `row_scaled_matrix_has_given_denominator_bounded_kernel`.

These take the fixed product-denominator property supplied by
`data_generators_and_affines_uniform_product_denominator`.

Finally, `gelfond_schneider_power_basis_scaled_norm_verified` extends
the integral-constant-free estimates locale with a fixed `T`, `h=D`,
`A=gs_concrete_entry_bound`, and the enlarged `c14` threshold. Its
`coordinate_contradiction: False` is **fully checked**. It constructs
the actual algebraic-integer kernel vector, establishes `rho` in `K`
and nonzero, uses the enlarged norm upper bound and inverse norm
bound, then applies `gs_growth_contradiction_with_q_choice`.

The remaining global step is selecting `T`, `c14`, `q`, the identity
embedding index, and the locale parameters from the primitive normal
power-basis data, and connecting that to the public
`Gelfond_Schneider.thy`. In particular, `T` must be selected from the
fixed data before `c14` and `q`; this is why the given-denominator
theorems were added. No public standalone theorem is claimed yet.

## Public theorem connected — October 4, around 21:20 UTC

The global parameter choice is now checked in
`Gelfond_Schneider_Power_Basis_Norm_Direct.thy`:

- `scaled_norm_contradiction_for_power_basis` selects the identity
  embedding and a fixed `T` from the primitive normal power basis,
  chooses `c14` using the globally exported house and point bases,
  then sets `q = gs_q_choice D (c14*2)`. The resulting scaled
  contradiction locale is instantiated with zero I/Q errors.
- `no_gelfond_schneider_data_scaled` applies that theorem to the
  normalized counterexample data using the existing common-field
  construction. It also checks with zero I/Q errors.
- `Gelfond_Schneider.thy` now imports
  `Gelfond_Schneider_Power_Basis_Norm_Direct` instead of
  `Baker_Two_Logarithms`; its `no_gelfond_schneider_data` theorem uses
  the scaled result, and its public `gelfond_schneider` theorem checks
  in I/Q.

The public file was synchronized to disk through I/Q `open_file` with
explicit overwrite after the jEdit buffer and filesystem briefly
diverged. Disk inspection confirmed the Baker import and proof are
gone, as are all `sorry` and `oops` occurrences in
`Gelfond_Schneider*.thy`.

`Baker/Standalone/ROOT` was changed to
`quick_and_dirty = false`. Its theory list was reduced to the public
`Gelfond_Schneider` root, so Isabelle checks precisely its transitive
imports. An initial strict build with the old expanded ROOT list
timed out after ten seconds at a command in
`Gelfond_Schneider_Integral_Basis_Field_Target.thy`, which is unused by
the public proof. The strict build with the focused ROOT **succeeded**:

```text
Finished Gelfond_Schneider_Standalone
(0:05:47 elapsed time, 0:18:40 cpu time)
```

Command used:

```sh
/Users/lawrpau/bin/isabelle build \
  -d /Users/lawrpau/isabelle/Auto-Proofs/Baker/Standalone \
  -d /Users/lawrpau/isabelle/New-Algebra \
  -d /Users/lawrpau/isabelle/afp/release/thys \
  -o document=false Gelfond_Schneider_Standalone
```

**The standalone Gelfond–Schneider theorem is complete and strictly
built.** The broader Baker project remains outside this goal.
