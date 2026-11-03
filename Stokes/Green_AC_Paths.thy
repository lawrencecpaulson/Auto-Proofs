theory Green_AC_Paths
  imports Green_Curl "HOL-Analysis.Absolute_Continuity"
    "HOL-Analysis.Lebesgue_Differentiation"
begin

lemma green_ac_path_is_path:
  fixes g :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
  shows "path g"
  unfolding path_def
  by (rule absolutely_continuous_on_imp_continuous[OF ac is_interval_cc])

lemma green_ac_path_rectifiable:
  fixes g :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
  shows "rectifiable_path g"
  unfolding rectifiable_path_def
  using green_ac_path_is_path[OF ac]
    absolutely_continuous_on_imp_has_bounded_variation_on[OF ac bounded_closed_interval]
  by blast

lemma green_ac_path_derivative_ae:
  fixes g :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
  shows "negligible {t \<in> {0..1}. \<not> g differentiable (at t)}"
proof -
  have bv: "has_bounded_variation_on g {0..1}"
    using absolutely_continuous_on_imp_has_bounded_variation_on
      [OF ac bounded_closed_interval] .
  show ?thesis
    by (rule Lebesgue_differentiation_thm[OF is_interval_cc bv])
qed

lemma green_ac_velocity_absolutely_integrable:
  fixes g g' :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (g has_vector_derivative g' t) (at t)"
  shows "g' absolutely_integrable_on {0..1}"
  by (rule absolutely_integrable_absolutely_continuous_derivative[OF ac null])
    (use deriv in \<open>auto intro: has_vector_derivative_at_within\<close>)

lemma green_ac_contour_integrable:
  fixes g :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (g has_vector_derivative g' t) (at t)"
    and cont: "continuous_on (path_image g) f"
  shows "f contour_integrable_on g"
proof -
  have gc: "continuous_on {0..1} g"
    by (rule absolutely_continuous_on_imp_continuous[OF ac is_interval_cc])
  have fc: "continuous_on {0..1} (\<lambda>t. f (g t))"
    by (rule continuous_on_compose2[OF cont gc])
      (auto simp: path_image_def)
  have bounded: "bounded ((\<lambda>t. f (g t)) ` {0..1})"
    by (rule compact_imp_bounded)
      (rule compact_continuous_image[OF fc compact_Icc])
  have measurable: "(\<lambda>t. f (g t)) \<in>
      borel_measurable (lebesgue_on {0..1})"
    by (rule continuous_imp_measurable_on_sets_lebesgue[OF fc]) simp
  have derivative_integrable: "g' absolutely_integrable_on {0..1}"
    by (rule green_ac_velocity_absolutely_integrable[OF ac null deriv])
  have product_integrable:
      "(\<lambda>t. f (g t) * g' t) absolutely_integrable_on {0..1}"
    by (rule absolutely_integrable_bounded_measurable_product
      [OF bilinear_times measurable _ bounded derivative_integrable])
      simp
  have product_int: "(\<lambda>t. f (g t) * g' t) integrable_on {0..1}"
    using product_integrable by (simp add: absolutely_integrable_on_def)
  have derivative_eq: "vector_derivative g (at t) = g' t"
    if "t \<in> {0..1} - N" for t
    by (rule vector_derivative_at[OF deriv[OF that]])
  have "(\<lambda>t. f (g t) * vector_derivative g (at t))
      integrable_on {0..1}"
    by (rule integrable_spike[OF product_int null])
      (use derivative_eq in auto)
  then show ?thesis
    by (simp add: contour_integrable_on)
qed

lemma green_ac_contour_integral:
  fixes g :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (g has_vector_derivative g' t) (at t)"
    and cont: "continuous_on (path_image g) f"
  shows "contour_integral g f =
    integral {0..1} (\<lambda>t. f (g t) * g' t)"
proof -
  have eq: "vector_derivative g (at t) = g' t"
    if "t \<in> {0..1} - N" for t
    by (rule vector_derivative_at[OF deriv[OF that]])
  show ?thesis
    unfolding contour_integral_integral
    by (rule integral_spike[OF null])
      (use eq in auto)
qed

lemma green_ac_path_length:
  fixes g :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (g has_vector_derivative g' t) (at t)"
  shows "path_length g = integral {0..1} (\<lambda>t. norm (g' t))"
  unfolding path_length_def
  by (rule vector_variation_integral_norm_derivative[OF null _ ac deriv])
    simp

lemma green_ac_subinterval_integral:
  fixes g :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (g has_vector_derivative g' t) (at t)"
    and t: "t \<in> {0..1}"
  shows "integral {0..t} g' = g t - g 0"
proof -
  have sub: "{0..t} \<subseteq> {0..1}"
    using t by auto
  have ac_sub: "absolutely_continuous_on {0..t} g"
    by (rule absolutely_continuous_on_subset[OF ac sub])
  have der_sub: "(g has_vector_derivative g' x) (at x within {0..t})"
    if "x \<in> {0..t} - N" for x
    by (rule has_vector_derivative_at_within)
      (rule deriv[of x]; use that sub in auto)
  have "(g' has_integral (g t - g 0)) {0..t}"
    by (rule fundamental_theorem_of_calculus_absolutely_continuous
      [OF null _ ac_sub der_sub])
      (use t in auto)
  then show ?thesis
    by (rule integral_unique)
qed

lemma green_ac_winding_kernel_integrable:
  fixes g :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (g has_vector_derivative g' t) (at t)"
    and away: "z \<notin> path_image g"
  shows "(\<lambda>w. 1 / (w - z)) contour_integrable_on g"
  by (rule green_ac_contour_integrable[OF ac null deriv])
    (use away in \<open>auto intro!: continuous_intros\<close>)

lemma green_continuous_velocity_has_derivative:
  fixes h :: "real \<Rightarrow> complex"
  assumes hc: "continuous_on UNIV h"
    and x: "x \<in> {0<..<1}"
  shows "((\<lambda>t. integral {0..t} h) has_vector_derivative h x) (at x)"
proof -
  have hI: "continuous_on {0..1} h"
    by (rule continuous_on_subset[OF hc]) simp
  have hi: "h integrable_on {0..1}"
    by (rule integrable_continuous_real[OF hI])
  have hx: "continuous (at x) h"
    using hc by (simp add: continuous_on_eq_continuous_at)
  have hxI: "continuous (at x within ({0..1} - {})) h"
    by (rule continuous_at_imp_continuous_within[OF hx])
  have xI: "x \<in> {0..1} - {}"
    using x by auto
  have ider0: "((\<lambda>t. integral {0..t} h) has_vector_derivative h x)
      (at x within ({0..1} - {}))"
    by (rule integral_has_vector_derivative_continuous_at
      [OF hi xI finite.emptyI hxI])
  have eq: "at x within {0..1} = at x"
    by (rule at_within_interior) (use x in auto)
  show ?thesis
    using ider0 by (simp only: Diff_empty eq)
qed

lemma green_continuous_velocity_valid_path:
  fixes h :: "real \<Rightarrow> complex"
  assumes hc: "continuous_on UNIV h"
  shows "valid_path (\<lambda>t. c + integral {0..t} h)"
proof -
  let ?q = "\<lambda>t. integral {0..t} h"
  let ?I = "{0..1::real}"
  let ?J = "?I - {0,1}"
  have hI: "continuous_on ?I h"
    by (rule continuous_on_subset[OF hc]) simp
  have hi: "h integrable_on ?I"
    by (rule integrable_continuous_real[OF hI])
  have qc: "continuous_on ?I ?q"
    by (rule indefinite_integral_continuous_1[OF hi])
  have qder_at: "(?q has_vector_derivative h x) (at x)"
    if x: "x \<in> ?J" for x
    by (rule green_continuous_velocity_has_derivative[OF hc])
      (use x in auto)
  have qdiff: "?q differentiable at x" if "x \<in> ?J" for x
    by (rule differentiableI_vector) (rule qder_at[OF that])
  have qder_eq: "vector_derivative ?q (at x) = h x"
    if "x \<in> ?J" for x
    by (rule vector_derivative_at[OF qder_at[OF that]])
  have hJ: "continuous_on ?J h"
    by (rule continuous_on_subset[OF hc]) simp
  have qdc: "continuous_on ?J (\<lambda>x. vector_derivative ?q (at x))"
    by (rule continuous_on_eq[OF hJ])
      (use qder_eq in auto)
  have qC1: "?q C1_differentiable_on ?J"
    using qdiff qdc by (simp add: C1_differentiable_on_eq)
  have "valid_path ?q"
    unfolding valid_path_def piecewise_C1_differentiable_on_def
    using qc qC1 by (intro conjI exI[where x="{0,1}"]) simp_all
  then have "valid_path ((+) c \<circ> ?q)"
    by (simp add: valid_path_translation_eq)
  then show ?thesis
    by (simp add: o_def)
qed

lemma green_continuous_velocity_derivative:
  fixes h :: "real \<Rightarrow> complex"
  assumes hc: "continuous_on UNIV h"
    and x: "x \<in> {0<..<1}"
  shows "vector_derivative (\<lambda>t. c + integral {0..t} h) (at x) = h x"
proof -
  have ider: "((\<lambda>t. integral {0..t} h) has_vector_derivative h x) (at x)"
    by (rule green_continuous_velocity_has_derivative[OF hc x])
  have cder: "((\<lambda>t::real. c) has_vector_derivative 0) (at x)"
    by (rule has_vector_derivative_const)
  have "((\<lambda>t. c + integral {0..t} h) has_vector_derivative
      0 + h x) (at x)"
    by (rule has_vector_derivative_add[OF cder ider])
  then show ?thesis
    by (simp add: vector_derivative_at)
qed

lemma green_continuous_velocity_contour_integral:
  fixes h :: "real \<Rightarrow> complex"
  assumes hc: "continuous_on UNIV h"
  shows "contour_integral (\<lambda>t. c + integral {0..t} h) f =
    integral {0..1}
      (\<lambda>t. f (c + integral {0..t} h) * h t)"
proof -
  have eq: "vector_derivative
      (\<lambda>u. c + integral {0..u} h) (at t) = h t"
    if "t \<in> {0..1} - {0,1}" for t
    by (rule green_continuous_velocity_derivative[OF hc])
      (use that in auto)
  show ?thesis
    unfolding contour_integral_integral
    by (rule integral_spike[of "{0,1}"])
      (use eq in auto)
qed

locale green_ac_velocity =
  fixes g :: "real \<Rightarrow> complex"
    and velocity :: "real \<Rightarrow> complex"
    and exceptional :: "real set"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and null: "negligible exceptional"
    and deriv: "\<And>t. t \<in> {0..1} - exceptional \<Longrightarrow>
      (g has_vector_derivative velocity t) (at t)"
begin

lemma velocity_absolutely_integrable:
  "velocity absolutely_integrable_on {0..1}"
  by (rule green_ac_velocity_absolutely_integrable[OF ac null])
    (use deriv in auto)

lemmas path = green_ac_path_is_path[OF ac]
  and rectifiable = green_ac_path_rectifiable[OF ac]
  and contour_integrable = green_ac_contour_integrable[OF ac null deriv]
  and contour_integral = green_ac_contour_integral[OF ac null deriv]
  and path_length = green_ac_path_length[OF ac null deriv]
  and subinterval_integral = green_ac_subinterval_integral[OF ac null deriv]
  and winding_kernel_integrable =
    green_ac_winding_kernel_integrable[OF ac null deriv]

end

end
