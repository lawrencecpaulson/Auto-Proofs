# Checked Stokes results and next proof obligations

The `Stokes` session in `ROOT` checks `Stokes_Local.thy`,
`Stokes_Basis_Fubini.thy`, `Stokes_Chart_Local.thy`,
`Stokes_Chart_Theorem.thy`, `Stokes_Form_Bridge.thy`,
`Stokes_Forms.thy`, `Stokes_Product_Forms.thy`,
`Stokes_Cart_Product.thy`, `Stokes_Halfline_Forms.thy`,
`Stokes_Smooth_Cutoff.thy`, and
`Stokes_Halfspace_Naturality.thy`, and
`Stokes_Block_Determinant.thy` with
Isabelle2026-RC4. The full development build completed successfully on
21 October 2026. The theories contain no `sorry`, `oops`, or axioms.
The dependent `Stokes_Integration` session checks
`Stokes_Oriented_Integration.thy`. The further dependent
`Stokes_Manifold` session checks `Stokes_Manifold_Integration.thy`
against AFP `Smooth_Manifolds`.
`Stokes_Boundary` checks `Stokes_Boundary_Charts.thy`, and
`Stokes_Boundary_Integration` checks
`Stokes_Boundary_Integration.thy`,
`Stokes_Body_Overlap.thy`,
`Stokes_Body_Local_Integration.thy`,
`Stokes_Smooth_Partition.thy`, and
`Stokes_Single_Chart.thy`.

On 21 October 2026, `Stokes_Boundary_Integration` built successfully
after adding `exterior_top_zero_off_near_support` and
`exterior_top_support_subset` to
`Stokes_Body_Local_Integration.thy`. These prove that the exterior
coefficient of a near-top form vanishes off its compact support in
interior charts. The session also checks the single-chart body and
boundary integral definitions and the partition-free, conditional
`Stokes_single_boundary_chart_local_integrals_C1`.

After manual approval, `Stokes_chart_supported_near_top_C1`
in `Stokes_Single_Chart.thy` also built successfully. It packages one
compact atlas-wide support set into coordinate, body, and boundary
support witnesses. Body integrability follows from compact support
and continuity, with the boundary face removed as a null set.
Body and boundary coefficient continuity follow from the stated
coordinate regularity, so these are no longer separate premises.

The checked `product_cart_jacobian_det` identifies the Cartesian
Jacobian determinant in the naturality theorem with the product
coordinate Fréchet determinant in body integration. The checked
`body_coeff_compatible_from_pullback` derives body coefficient
compatibility from the interior near-top pullback law.
`boundary_coefficient_transition_for_extensions` now proves the
boundary coefficient law for the specific geometric extensions
supplied by the atlas. The checked
`boundary_coeff_compatible_from_geometric_pull` derives boundary
coefficient compatibility from `near_top_face_pull_compatible`.
`product_pull_near_top_cong_open`,
`body_transition_homeomorphism`, and
`geometric_interior_pull_eq_transition` identify the pullback by
smooth geometric extensions with the ordinary interior transition
pullback. `geometric_face_pull_from_interior_agreement` extends this
identity to a boundary point by continuity. Consequently,
`near_top_face_pull_compatible_from_pullback` derives the face law
from the interior pullback law and differentiability on chart
codomains.
The direct `Stokes_chart_supported_form_C1` theorem applies the
single-chart integrals to the exterior and boundary coefficients of
the same atlas-wide near-top coordinate family. It assumes interior
pullback, C¹ regularity, and compact support in one chart; the face
law and both coefficient compatibilities are proved internally.
The checked `boundary_single_chart_cutoff` and
`body_single_chart_partition_exists` supply admissible one-chart
partitions. `body_partition_integral_local_chart` shows that every
admissible body partition computes the same chart integral on a
chart-supported form. Thus `integral_body_single_top_eq_top_chart`
and `integral_boundary_single_top_eq_top_chart` connect the earlier
single-chart integrals to the partition-defined body and boundary
integrals.
`Stokes_chart_supported_form_integrals_C1` proves the Milestone 5b
equation using `integral_body_top` and `integral_boundary_top` for
an atlas-wide near-top coordinate family supported in one chart.
The family itself is the form representation in this theorem.
Milestone 5a is checked for the coordinate-family interface.
`body_partition_exists` and `boundary_partition_exists` construct
finite admissible partitions for arbitrary compact supports.
`body_partition_integral_independent_admissible` and the analogous
boundary theorem make both integrals independent of the partition.
Both are additive and homogeneous and obey unconditional local
chart rules. `Stokes_Smooth_Cutoff.thy` builds Euclidean C¹ cutoffs.
`body_C1_partition_exists` and `boundary_C1_partition_exists` produce
finite, nonnegative chartwise C¹ partitions subordinate to body and
boundary charts. `body_boundary_C1_partition_exists` produces a
single partition admissible for both integrals, and
`common_C1_partition_integral_rules` evaluates both with that
partition. The atlas assumes C² transitions; the proved chartwise
C¹ regularity is the regularity used for localization. The
zero-dimensional boundary integral in the separate half-line model
is a signed finite sum.

## Checked analytic results

- `normal_slice_FTC_integral`: integrates a one-dimensional FTC identity
  over arbitrary Euclidean tangential coordinates using Fubini. Its
  integrability hypothesis is stated on the product region.
- `second_slice_FTC_integral` and `second_slice_FTC_zero`: the matching
  tangential slice identity and zero-face consequence.
- `normal_halfspace_FTC_C1`: for `real × 'a::euclidean_space`,
  compact relative support of a coefficient and a continuous normal
  derivative give the negative boundary integral. Derivative
  integrability is derived from these hypotheses.
- `Stokes_box_2D`: signed upper-minus-lower face formula for a rectangle,
  with `P dy + Q dt` and integrand `partial_t P - partial_y Q`.
- `halfline_FTC_compact_support`: dimension-one half-space Stokes from
  compact relative support of a coefficient.
- `Stokes_halfspace_2D_C1`: two-dimensional half-space Stokes,

      integral_{t>=0,y∈R} (partial_t P - partial_y Q)
        = - integral_{y∈R} P(0,y).

  It assumes compact relative supports of `P` and `Q`, ambient
  directional derivatives at points of the half-space, and continuity
  of those derivatives there. Integrability of the derivatives on the
  half-space is proved inside the theory, not assumed in this theorem.
- `lborel_integral_basis_slice`: Fubini isolates any selected Euclidean
  basis coordinate under a Lebesgue integral. The integrand must be
  integrable for `lborel` and Borel measurable; the latter is an explicit
  requirement of Isabelle's `integral_distr` theorem.
- `lborel_integral_basis_derivative_zero`: an all-dimensional tangential
  derivative integrates to zero when its primitive vanishes on both ends
  of a common coordinate strip and the derivative vanishes outside it.
- `lborel_integral_basis_derivative_zero_compact`: compact support of
  the primitive supplies the strip, face, and tail conditions. It still
  assumes integrability and Borel measurability of the derivative and
  continuity along coordinate lines.
- `tangential_halfspace_derivative_support_basis`: the derivative of
  a tangential coefficient inherits compact relative support in the
  half-space. The proof handles the normal and tangential tails
  separately, using local constancy outside a bounding cylinder.
- `tangential_halfspace_integral_zero_basis_C1`: the half-space integral
  of any Euclidean basis-direction derivative is zero, assuming compact
  relative support of its coefficient and continuity of the derivative.
  Derivative support, integrability, and measurability are derived.
- `Stokes_halfspace_basis_sum_C1`: for any finite `B ⊆ Basis`,

      integral_{t>=0,y} (P_t(t,y) - sum_{b∈B} Q_b(b,t,y))
        = - integral_y P(0,y).

  The coefficients `P` and `Q b` have compact relative support in the
  half-space; their stated normal or basis-direction derivatives are
  continuous there. Their integrability follows in the proof. This is
  the all-dimensional analytic coordinate identity.
- `normal_halfspace_FTC_within` and
  `Stokes_halfspace_basis_sum_within`: the corresponding half-space
  results with a one-sided normal derivative at `t = 0`. The tangential
  derivatives remain ordinary derivatives along basis-coordinate
  lines. The proof derives derivative integrability from support and
  continuity.
- `normal_zero_extension_C1` and `tangential_zero_extension_C1`:
  extend a coefficient supported in a compact subset of
  `({0..} × UNIV) ∩ U` by zero to the whole half-space. They establish
  compact relative support, continuity of the extended derivative
  coefficient, and the appropriate directional derivative law across
  the edge of the chart image.
- `Stokes_relatively_open_chart_C1`: the all-dimensional, chart-local
  coordinate identity on `({0..} × UNIV) ∩ U` for ambient-open `U`.
  Each coefficient is zero outside a compact subset of the chart
  image. The conclusion integrates the signed coordinate-derivative
  sum over the chart image and the negatively oriented `t = 0` face.
  This discharges the analytic chart-local part of milestone 2.
- `Stokes_chart_form_interface`: a conditional integration theorem
  replacing the signed derivative sum by the coefficient of a
  pulled-back exterior derivative and the negative boundary trace by
  a boundary-form coefficient. It assumes the two pointwise
  coefficient identities explicitly. It does not construct
  differential forms or prove their pullback and orientation laws.

The first-coordinate half-space and boundary sign agree with
`MILESTONE_2_SPEC.md`. The proved analytic formulation is in scalar
coordinates. It applies to half-space charts with a one-sided normal
derivative and needs no global ambient derivative at the boundary.

## Checked milestone 1 results

`Stokes_Forms.thy` represents a near-top form in oriented Cartesian
coordinates by the vector field contracted with the standard volume
form, and a top form by its scalar coefficient. It checks:

- `exterior_top_signed_coeff`: the exterior derivative is the signed
  sum of coordinate derivatives. The signs are supplied as a
  coordinate-orientation parameter.
- `exterior_top_add`, `exterior_top_sum`, `exterior_top_scale`, and
  `exterior_top_restrict_near_top`: linearity, finite sums, the scalar
  product rule, and locality on an open restriction.
- `near_top_scale_compact_support` and
  `top_scale_compact_support`: multiplication by a scalar function
  preserves compact support on a specified carrier.
- `pull_top` and `pull_near_top`: top and near-top pullback
  coefficients using Jacobians of a map and its proposed inverse.
  Both have checked pointwise composition laws under the stated
  differentiability and inverse-composition conditions.
- `exterior_top_pull_near_top_affine`: naturality of the exterior
  derivative for invertible affine coordinate changes.
- `matrix_det_differentiable` and
  `cofactor_column_differentiable`: regularity results needed for
  smooth pullback.
- `piola_coordinate_cancellation`: the finite triple sums in the
  coordinate Piola calculation cancel under mixed-partial symmetry.
- `exterior_top_pull_near_top_if_piola`: smooth-map naturality
  follows from the inverse-Jacobian equation and the zero divergence
  of each cofactor column.
- `matrix_det_has_derivative_invertible` and
  `matrix_inverse_field_derivative`: Jacobi's formula and
  differentiation of a local inverse matrix field.
- `Ck_on_2_jacobian_mixed`, `piola_matrix_field_closed`, and
  `cofactor_column_closed_C2`: mixed second partials and the Piola
  identity for a C² chart map with a C² local inverse.
- `exterior_top_pull_near_top_C2`: smooth pullback naturality for
  those local inverse chart maps.
- `pull_near_top_differentiable_C2`: regularity of the near-top
  pullback needed to transport its exterior derivative.
- `Stokes_product_form_chart_C1`: an unconditional chart Stokes
  formula for a product-coordinate near-top form represented by
  `A : real × 'a ⇒ real × 'a`. Its derivative and boundary
  coefficients discharge both pointwise premises of
  `Stokes_chart_form_interface`. It assumes ambient differentiability
  of `A` on the chart image, continuity of the displayed derivative
  coefficients, and compact support of each component.
- `halfspace_ambient_derivative_unique` and
  `product_exterior_top_halfspace_extension`: two differentiable
  ambient extensions agreeing on the halfspace have the same
  derivative and exterior-top coefficient at its face.
- `halfspace_ambient_derivative_unique_local`,
  `product_exterior_top_halfspace_local_extension`, and
  `halfspace_form_eq_exterior`: the extension result works on a
  relatively open halfspace chart; the extension-equivalence
  relation respects addition, scaling, restriction, and `d`.
- `product_exterior_top_restrict`: locality on an ambient open set.
- `product_exterior_top_add`, `product_exterior_top_scale`,
  `product_exterior_top_sum`, and `product_scale_compact_support`:
  product-form linearity, the scalar product rule, finite sums,
  and support preservation under scalar multiplication.
- `cart_form_of_product_frechet_derivative` and
  `exterior_top_cart_form_of_product`: the derivative and exterior
  coefficient agree under the explicit linear isomorphism
  `real × real^'n ≃ real^(unit + 'n)`.
- `Ck_on_cart_map_of_product` and
  `product_exterior_top_pull_near_top_C2_on`: C² regularity and
  pullback naturality in product chart coordinates on ambient-open
  inverse chart neighborhoods.
- `Stokes_halfline_form_C1`: the dimension-one form theorem with
  the negatively signed zero-dimensional boundary value.
- `matrix_inverse_field_derivative_halfspace`,
  `cofactor_column_closed_C2_halfspace`, and
  `product_exterior_top_pull_near_top_C2_halfspace`: Piola and
  pullback naturality for C² ambient extensions that are inverse
  only on their halfspace chart domains.
- `face_preserving_jacobian_tangential_zero` and
  `product_boundary_coeff_pull_cofactor`: face preservation forces
  the inverse Jacobian's normal/tangential entries to vanish,
  giving the local boundary coefficient pullback law with a
  cofactor factor.
- `halfspace_chart_normal_positive`: an invertible half-space
  transition has positive normal derivative along the face.
- `det_normal_tangential_block`,
  `tangential_block_product_face_jacobian`, and
  `product_boundary_coeff_pull_face_local_inverse`: the boundary
  cofactor is the determinant of the restricted face map's Jacobian.
  `cart_halfspace_boundary_orientation` states the positive
  normal-factor relation for an orientation-preserving chart.

Milestone 1a is complete as a coordinate-coefficient interface for
Stokes. The optional all-degree algebra and arbitrary-tangent
evaluation have not been developed.

`PIOLA_PROOF_PLAN.md` records the now-completed dependency ladder and
the limitation of the supplied Lean repository's coordinate pullback.

## Interface to later milestones

The local product-form chart interface, including boundary-point
naturality and the face Jacobian boundary law, has been discharged.
`Stokes_Integration` proves `oriented_integral_change_of_variables`,
`oriented_chart_overlap_integral`, `integral_common_refinement`, and
`absolutely_integrable_compact_support`. `Stokes_Manifold` connects
these to the AFP atlas. Its `oriented_c_manifold` locale carries a
positive oriented chart cover. It proves finite smooth partitions on
compact support, localized chart comparison, automatic absolute
integrability of weighted coefficients, and independence of the
chosen smooth partition. The checked `integral_top` satisfies the
local chart rule, addition, scalar multiplication, zero-form
vanishing, and uniqueness among extensional linear functionals
satisfying the chart rule. Milestone 3's main gate is complete;
comparison between opposite orientations remains optional.
`integral_top_ext` additionally proves that values outside oriented
chart codomains do not affect the integral.

`Stokes_Boundary` now checks the half-space chart and atlas
prototype. It proves chart-independent boundary classification,
relative closedness, restricted boundary-chart homeomorphisms,
open face-coordinate overlaps, and homeomorphic boundary
transitions. `halfspace_chart.compact_relative_neighborhood`
and `halfspace_atlas.boundary_compact_relative_neighborhood`
provide compactly contained relative neighborhoods for later
partition construction.
`halfspace_atlas.finite_boundary_chart_neighborhoods` gives a
finite cover of every compact boundary subset by such chart
neighborhoods. `C2_halfspace_atlas.boundary_transition_C2` proves
smoothness given local ambient C² transition extensions.
`C2_halfspace_atlas.local_transition_extensions_inverse` derives
locally inverse forward and reverse extensions from these weaker
C² atlas assumptions. It also establishes half-space and
face preservation for both extensions.
`positive_face_jacobian_from_inverse_extensions` proves the
local positive boundary Jacobian from C² extensions that are
inverse on the half-space, half-space and face preservation,
and positive ambient determinant; it derives the inverse
Jacobian at the face.
`product_halfspace_extension_jacobian_unique` makes ambient
transition Jacobians independent of the chosen local extension.
`positively_oriented_C2_halfspace_atlas.positive_boundary_transition`
proves positivity at every boundary overlap from the C² atlas
plus one positive ambient extension at each overlap.
`local_boundary_coefficient_transition` identifies the
boundary coefficient of a pulled-back near-top form with
the ordinary top-form transition law on the boundary.

`Stokes_Boundary_Integration` proves `boundary_overlap_integral`,
`boundary_form_support_chart`,
`boundary_chart_coeff_absolutely_integrable`,
`boundary_weight_absolutely_integrable`,
`boundary_localized_chart_integral_eq`, and
`boundary_chart_partition_integral_independent`.
The last theorem compares any two finite admissible boundary
partition sums. `boundary_partition_integral_independent_admissible`
discharges integrability of their common refinement from
continuous, compactly localized partition weights.
`integral_boundary_top_eq_partition` establishes the resulting
integral's partition-sum rule whenever an admissible partition
exists, and `integral_boundary_top_empty` proves the value zero
for an empty boundary. `integral_boundary_top_zero_coeff`
proves zero for the zero coefficient family.
`integral_boundary_top_local_chart` gives the chart rule for a
compactly supported boundary form when an admissible partition
is supplied, while `boundary_single_chart_integral_independent`
compares the unweighted chart integrals without a partition.
`Stokes_Single_Chart.thy` checks the C¹ coordinate Stokes identity
in an atlas chart, identifies the boundary side with
`integral_boundary_top` under that partition condition, gives its
explicit negative normal sign, and handles an interior chart with
empty face and zero boundary coefficient. Its gauge-integral
corollary assumes Lebesgue integrability of the body coefficient.

The partition-defined body integral and the global single-chart
form equation are now checked in the smooth oriented half-space
atlas locale. General partition existence and independence for
arbitrarily supported forms, an optional abstract form datatype,
and finite gluing remain open. The smooth oriented integration
locale explicitly assumes C², positively oriented interior chart
transitions.
`Stokes_Body_Overlap.thy` establishes openness and bijective
chart transition of the interior coordinate overlaps, and proves
`body_overlap_integral` under explicit C² and positive determinant
assumptions. This is the change-of-variables step needed by a
future body integral; the current boundary atlas does not impose
those interior transition assumptions.

## Build note

The registered RC4 user components initially tried to compile an
older `ic2` Scala component and failed before checking the theory.
The proof checks used an isolated temporary Isabelle home at
`/private/tmp/stokes-isabelle-home`, with cloned `Pure` and `HOL`
heaps. Its first `HOL-Analysis` build took 13 minutes; later `Stokes`
builds used the cached parent heap and took about eight seconds each:

    USER_HOME=/private/tmp/stokes-isabelle-home \
      /Applications/Isabelle2026-RC4.app/Contents/Resources/bin/isabelle \
      build -D Stokes -j 2

The user reports that AutoCorrode's `isa26` branch fixes the RC4
component problem. That branch was not needed for the isolated proof
checks, and the shared component registration was not changed.

The dependent AFP and boundary checks use the cached heaps:

    USER_HOME=/private/tmp/stokes-isabelle-home \
      /Applications/Isabelle2026-RC4.app/Contents/Resources/bin/isabelle \
      build -d /Users/lawrpau/isabelle/afp/devel/thys/Smooth_Manifolds \
      -d Stokes -d Stokes/Integration -D Stokes/Manifold -j 2

    USER_HOME=/private/tmp/stokes-isabelle-home \
      /Applications/Isabelle2026-RC4.app/Contents/Resources/bin/isabelle \
      build -d Stokes -D Stokes/Boundary -j 2

    USER_HOME=/private/tmp/stokes-isabelle-home \
      /Applications/Isabelle2026-RC4.app/Contents/Resources/bin/isabelle \
      build -d Stokes -d Stokes/Integration -d Stokes/Boundary \
      -D Stokes/BoundaryIntegration -j 2
