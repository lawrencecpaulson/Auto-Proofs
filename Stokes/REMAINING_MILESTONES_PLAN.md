# Remaining milestones: implementation order and proof gates

This plan refines `MILESTONE_1_SPEC.md` through `MILESTONE_7_SPEC.md`.
`PROOF_STATUS.md` is the record of checked theorems. The first local
form gate was checked in Isabelle2026-RC4 on 20 October 2026.

## Where the project stands

| Milestone | Status | Next reviewable result |
| --- | --- | --- |
| 1a, Euclidean near-top and top forms | Complete for the Stokes coordinate interface, including face Jacobian boundary law | Optional all-degree algebra |
| 2, local half-space Stokes | Form chart theorem checked | Integrate with the eventual boundary chart locale |
| 3, oriented integration without boundary | `integral_top`, partition independence, local chart rule, uniqueness, and linearity checked in `Stokes_Manifold` | Optional two-orientation sign comparison |
| 4, boundary geometry | Relative-carrier atlas, C² transitions, locally inverse extensions, positive induced boundary orientation, and form boundary coefficient law checked | Instantiate smooth oriented atlases beyond the abstract locale; one-dimensional boundary uses the separate halfline model |
| 5a, integration with boundary | Complete for the coordinate-family interface: finite chartwise C¹ partitions, both partition-independent linear integrals, chart rules, and a common body/boundary partition | Use the common partition in Milestone 6 |
| 5b, single-chart Stokes | Complete: `Stokes_chart_supported_form_integrals_C1` equates the partition-defined body and boundary integrals for a chart-supported coordinate form | Optional abstract form datatype; Milestone 6 needs regularity of partition-weighted forms |
| 6, global Stokes | Planned | Compact-support theorem by a finite partition sum |
| 7, classical Green's theorem | Planned after 6 | Planar `P dx + Q dy` corollary with area and oriented contour integrals |

The optional all-degree form algebra (1b) and cubical-chain Stokes are
outside the critical path.

## First gate: local form interface (checked)

`Stokes_Forms.thy` proves Piola and C² naturality.
`Stokes_Product_Forms.thy` proves `Stokes_product_form_chart_C1`,
an actual chart-supported form theorem without assumed pointwise
coefficient identities. `Stokes_Cart_Product.thy` transports
Cartesian naturality to product chart coordinates with tangential
type `real^'n`. `Stokes_Halfline_Forms.thy` handles dimension one.
The analytic coordinate theorem remains independently usable.

The halfspace-only inverse naturality theorem, local boundary
cofactor pullback law, block-Jacobian identity, positive normal
factor, and relative ambient-extension equivalence are checked.
The milestone 4 atlas interface and induced boundary orientation are
checked. The relative-carrier interface now has finite chartwise C¹
partitions on arbitrary compact supports.

## Milestone 3: oriented integration on existing boundaryless manifolds

The main gate is checked. It uses only the top-form transition law and
does not depend on exterior differentiation.

### 3a. Signed change of chart

- Use the existing AFP `c_manifold` and an atlas of oriented charts.
  Represent a top form initially by compatible chart coefficient
  functions. On an overlap, compatibility is
  `alpha_c(x) = det(Dg(x)) * alpha_d(g x)`.
- Prove the coefficient change-of-variables equation for a compactly
  supported coefficient inside an overlap. The theorem
  `integral_change_of_variables` in `HOL-Analysis.Change_Of_Vars`
  needs a measurable source set, derivative on that set, injectivity,
  and absolute integrability on one side. Orientation gives the
  positive sign needed to remove the absolute value.
- `HOL-Analysis.Determinant_Linear_Function` already has
  `eucl_det_conv_matrix_det`, connecting the `eucl.det` in change of
  variables to the Cartesian matrix determinant used for top-form
  pullback. `set_borel_integral_eq_integral` in
  `HOL-Analysis.Equivalence_Lebesgue_Henstock_Integration` connects
  Lebesgue and gauge set integrals under integrability.

**Gate:** the same compactly supported top form has equal coordinate
integrals in two oriented charts on their overlap. This is checked.
The orientation-reversing comparison remains optional.

### 3b. Global integral and its characterisation

- Prove coordinate integrability from continuity and compact support,
  including compactness of support after a chart homeomorphism.
- Apply AFP `partitions_of_unityE` to the oriented chart cover.
  Use `locally_finite_compactD` to select finitely many partition
  supports meeting the form support. Define the integral as the sum
  of their local integrals.
- Compare any two choices through the finite refinement
  `rho_i * sigma_j * alpha`. Prove the chart rule, uniqueness from
  that rule, linearity, and sign reversal.

**Gate:** a chart-independent linear integral of compactly supported
top-coefficient families on the existing boundaryless AFP manifold.
This is checked in `Stokes_Manifold`, with continuity of each chart
coefficient and compact support inside the carrier stated explicitly.

## Milestone 4: geometry of half-space charts

Do this as a new relative-carrier interface. Existing AFP `chart`
requires an ambient-open codomain and cannot directly represent a
relatively open half-space image.

### 4a. Small chart prototype

- Define `H = {p::real × 'e. 0 ≤ fst p}` and a chart record with a
  domain relatively open in the manifold carrier, codomain
  `H ∩ U` for ambient-open `U`, inverse maps, and a homeomorphism
  on those domains.
- Require smooth ambient extensions of transitions and their local
  inverses near boundary points. State chart compatibility so
  transitions preserve the zero face; proving preservation from
  topology alone can be a later theorem.
- Prove restriction of a chart to a smaller relatively open subset,
  composition of transitions, and the carrier/interior/boundary
  cover. Test an explicit half-space example and an empty-boundary
  example before introducing a large atlas locale.

**Gate:** a checked reusable half-space chart interface with
transition composition and boundary classification independent of
the chosen chart.

### 4b. Boundary charts and orientation

- Restrict a half-space chart to `t = 0`. Its coordinate image
  `{y. (0,y) ∈ codomain c}` is open in `'e`; the chart domain is open
  relative to the boundary carrier. Prove restricted transition
  smoothness.
- At a boundary point show the transition derivative is block
  triangular: tangential directions contribute zero to the normal
  coordinate. Obtain positivity of its normal derivative from
  half-space preservation and invertibility of the ambient
  derivative. Invertibility at the face follows by differentiating
  inverse identities on the interior and passing to the face by
  continuity.
- Prove `det(Dg) = normal_factor * det(Dg_boundary)`, with positive
  normal factor. Ambient orientation preservation then implies
  boundary-chart orientation preservation. With `t` first and
  `t ≥ 0`, the induced boundary coefficient has sign `-1`.
- Keep boundary points as a **carrier set** rather than making a
  nonempty subtype. An empty boundary must be representable. For
  dimension one, give a separate discrete boundary-chart and
  signed-sum interface.

**Gate:** chart-independent boundary carrier, restricted atlas, and
outward-normal-first orientation, including empty boundary and
dimension one.

## Milestone 5: integration and the single-chart theorem

### 5a. Integration on a manifold with boundary

- Prove that the boundary carrier is closed in the manifold carrier,
  so restricting a compactly supported form preserves compactness.
- First prove a signed change-of-chart rule on the half-space model.
  The existing `integral_change_of_variables` accepts any measurable
  source set and a derivative **within** that set. Try applying it
  directly to a relatively open subset of `H`, using the ambient
  derivative supplied by the transition extension. If its
  integrability or derivative premises become awkward, apply it on
  the open interior and add back the null boundary face.
- Build a boundary-compatible chartwise C¹ partition of unity
  on each compact support. This is checked using finite compact
  chart refinement and smooth Euclidean cutoffs transferred through
  the C² relative atlas.
- Define the manifold integral and the boundary integral by finite
  local sums. Use double refinement to prove independence, local
  chart rules, and linearity. The boundary integral on an empty
  carrier is zero; in dimension one it is a signed finite sum.

**Gate checked:** `common_C1_partition_integral_rules` gives one finite
chartwise C¹ partition on which both partition-independent integrals
can be evaluated. The signed finite-sum integral for dimension one
is checked in the separate half-line model.

**Gate:** both integrals exist and obey their local chart rules,
including the boundary coefficient `-a_1(0,y)`.

### 5b. Forms supported in one chart

- The interior-chart compact-support identity and zero boundary
  coefficient integral are checked in `Stokes_Single_Chart.thy`.
- The boundary-chart coordinate identity and its boundary integral
  rule are checked there when a compatible global boundary
  coefficient family and an admissible partition are provided.
  The gauge body integral form additionally assumes Lebesgue
  integrability of the exterior coefficient. The coefficient
  of the induced boundary orientation is explicitly `-a_1(0,y)`.
- Construct atlas-wide near-top forms, prove their coordinate
  derivative and boundary-restriction laws. The single-chart body
  integral and its conditional chart rule are now defined and
  checked, as is the partition-free conditional Stokes equation.
  Compact support of the near-top form now yields the interior
  exterior coefficient and boundary support inclusions. The
  packaged theorem `Stokes_chart_supported_near_top_C1` is checked.
- The Cartesian/product determinant bridge and the implication from
  the interior near-top pullback law to
  `body_top_coeff_compatible` are checked. The boundary coefficient
  law now applies to the specific `F` and `G` supplied by
  `local_transition_extensions_inverse`. The interior pullback law
  extends to these geometric maps at the face by continuity, giving
  `boundary_top_coeff_compatible` without a separate face premise.
  Connect an atlas-wide smooth-form interface to these coordinate
  fields.
- Compact support and continuity give absolute integrability of
  the body exterior coefficient. One-chart cutoffs, finite partitions
  for arbitrary compact supports, and the partition-defined
  integrals' local chart rules are checked.
- Check that multiplying a form by a subordinate partition function
  leaves compact support inside that chart and supplies precisely
  the regularity of the local theorem.

**Gate checked:** `Stokes_chart_supported_form_integrals_C1` gives
`integral_body_top (d omega) = integral_boundary_top (j* omega)`
for an atlas-wide near-top coordinate form compactly supported
inside one interior or boundary chart.

## Milestone 6: global compact-support Stokes

- Let `K` be the compact support of `omega` and choose the finite
  chartwise C¹ partition from 5a. Use
  `body_boundary_C1_partition_exists` to use the same partition
  for the body and boundary coefficients.
- Prove globally that `omega` equals the finite sum of
  `rho_i * omega`. Outside `K` both sides vanish; on `K` the
  partition sums to one. Prove the support and regularity of each
  summand.
- Apply 5b termwise. Use linearity of `d`, both integrals, and boundary
  restriction to sum the equalities. The gluing calculation needs no
  graded Leibniz rule.
- Check the empty-boundary, compact-manifold, and one-dimensional FTC
  corollaries. Keep the arbitrary noncompact manifold statement
  under the compact-support hypothesis.

**Gate:** the global compact-support Stokes theorem and these
corollaries are checked, with no assumed Piola, coefficient,
chart-independence, or partition identities.

## Milestone 7: classical Green's theorem

- Instantiate the two-dimensional positive boundary atlas for a
  compact smooth planar region and its oriented boundary.
- For the one-form `P dx + Q dy`, identify the exterior coefficient
  as `partial_x Q - partial_y P`.
- Identify the two Stokes integrals with the usual planar area
  integral and the oriented contour integral. Check counterclockwise
  orientation on the outer boundary and clockwise orientation around
  holes.
- Apply Milestone 6 to obtain the traditional formula. Compare with
  the separate `Green/` development's Type I and Type II region
  results and reuse its line-integral interface when suitable.

**Gate:** a checked Isabelle theorem states Green's theorem using
ordinary area and contour integrals, without a new subdivision proof.

## Scheduling and risk

Milestones 3a–3b and 4a–4b can start independently of the remaining
Piola proof. Milestone 5 needs both; milestone 6 should start only
after the two single-chart cases of 5b are available.

The early design checkpoints are: (1) Cartesian/product coefficient
bridge, (2) relative-carrier half-space chart prototype, (3)
boundary-compatible partition bump, and (4) signed chart
change of variables. These are the points where the intended
interfaces may need revision. Keep each as a small checked theory
before building an atlas or integration API on top of it.
