theory Rectifiable_Path
  imports Absolute_Continuity
begin

text \<open>
  Rectifiable paths and arc length, following HOL Light's
  @{text "Multivariate/integration.ml"} (lines 23827--25750).

  A path is rectifiable iff it is continuous and has bounded variation on
  @{term "{0..1}"}. The path length is the vector variation on that interval.
\<close>

section \<open>Definitions\<close>

definition rectifiable_path :: "(real \<Rightarrow> 'a::euclidean_space) \<Rightarrow> bool" where
  "rectifiable_path g \<longleftrightarrow> path g \<and> has_bounded_variation_on g {0..1}"

definition path_length :: "(real \<Rightarrow> 'a::euclidean_space) \<Rightarrow> real" where
  "path_length g = vector_variation {0..1} g"

section \<open>Basic properties\<close>

lemma rectifiable_path_imp_path:
  "rectifiable_path g \<Longrightarrow> path g"
  unfolding rectifiable_path_def by simp

lemma path_length_pos_le:
  "rectifiable_path g \<Longrightarrow> 0 \<le> path_length g"
  sorry

lemma path_length_eq_0:
  "rectifiable_path g \<Longrightarrow>
    (path_length g = 0 \<longleftrightarrow> (\<exists>c. \<forall>t \<in> {0..1}. g t = c))"
  sorry

lemma simple_path_length_pos_lt:
  "rectifiable_path g \<Longrightarrow> simple_path g \<Longrightarrow> 0 < path_length g"
  sorry

section \<open>Invariance under transformations\<close>

lemma rectifiable_path_translation_eq:
  "rectifiable_path ((\<lambda>x. a + x) \<circ> g) \<longleftrightarrow> rectifiable_path g"
  sorry

lemma path_length_translation:
  "path_length ((\<lambda>x. a + x) \<circ> g) = path_length g"
  sorry

lemma rectifiable_path_linear_image_eq:
  assumes "linear f" "inj f"
  shows "rectifiable_path (f \<circ> g) \<longleftrightarrow> rectifiable_path g"
  sorry

lemma path_length_linear_image:
  assumes "linear f" "\<And>x. norm (f x) = norm x"
  shows "path_length (f \<circ> g) = path_length g"
  sorry

lemma rectifiable_path_eq:
  "\<lbrakk>\<And>t. t \<in> {0..1} \<Longrightarrow> g t = h t; rectifiable_path g\<rbrakk> \<Longrightarrow> rectifiable_path h"
  sorry

lemma path_length_eq:
  "\<lbrakk>\<And>t. t \<in> {0..1} \<Longrightarrow> g t = h t; rectifiable_path g\<rbrakk> \<Longrightarrow>
    path_length g = path_length h"
  sorry

section \<open>Subpaths, joins, reversal\<close>

lemma rectifiable_path_reversepath:
  "rectifiable_path g \<Longrightarrow> rectifiable_path (reversepath g)"
  sorry

lemma path_length_reversepath:
  "rectifiable_path g \<Longrightarrow> path_length (reversepath g) = path_length g"
  sorry

lemma rectifiable_path_subpath:
  "\<lbrakk>rectifiable_path g; u \<in> {0..1}; v \<in> {0..1}\<rbrakk> \<Longrightarrow>
    rectifiable_path (subpath u v g)"
  sorry

lemma path_length_subpath:
  "path_length (subpath s t g) = vector_variation (closed_segment s t) g"
  sorry

lemma rectifiable_path_join:
  assumes "pathfinish g1 = pathstart g2"
  shows "rectifiable_path (g1 +++ g2) \<longleftrightarrow>
    rectifiable_path g1 \<and> rectifiable_path g2"
  sorry

lemma path_length_join:
  "\<lbrakk>rectifiable_path g1; rectifiable_path g2; pathfinish g1 = pathstart g2\<rbrakk> \<Longrightarrow>
    path_length (g1 +++ g2) = path_length g1 + path_length g2"
  sorry

section \<open>Shiftpath\<close>

lemma rectifiable_path_shiftpath:
  "\<lbrakk>rectifiable_path g; pathfinish g = pathstart g; t \<in> {0..1}\<rbrakk> \<Longrightarrow>
    rectifiable_path (shiftpath t g)"
  sorry

lemma path_length_shiftpath:
  "\<lbrakk>rectifiable_path g; pathfinish g = pathstart g; t \<in> {0..1}\<rbrakk> \<Longrightarrow>
    path_length (shiftpath t g) = path_length g"
  sorry

section \<open>Lipschitz and distance bounds\<close>

lemma lipschitz_imp_rectifiable_path:
  assumes "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow>
    norm (g x - g y) \<le> B * norm (x - y)"
  shows "rectifiable_path g"
  sorry

lemma path_length_lipschitz:
  assumes "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow>
    norm (g x - g y) \<le> B * norm (x - y)"
  shows "path_length g \<le> B"
  sorry

lemma dist_points_le_path_length:
  "\<lbrakk>rectifiable_path g; a \<in> {0..1}; b \<in> {0..1}\<rbrakk> \<Longrightarrow>
    dist (g a) (g b) \<le> path_length g"
  sorry

lemma dist_endpoints_le_path_length:
  "rectifiable_path g \<Longrightarrow> dist (pathstart g) (pathfinish g) \<le> path_length g"
  sorry

lemma path_length_eq_line_segment:
  "\<lbrakk>rectifiable_path g; path_length g = dist (pathstart g) (pathfinish g)\<rbrakk> \<Longrightarrow>
    path_image g = closed_segment (pathstart g) (pathfinish g)"
  sorry

section \<open>Linepath\<close>

lemma rectifiable_path_linepath:
  "rectifiable_path (linepath (a, b))"
  sorry

lemma path_length_linepath:
  "path_length (linepath (a, b)) = dist a b"
  sorry

section \<open>Rectifiable path image bound\<close>

lemma rectifiable_path_image_subset_cball:
  "rectifiable_path g \<Longrightarrow>
    path_image g \<subseteq> cball (pathstart g) (path_length g)"
  sorry

section \<open>Absolutely continuous paths\<close>

lemma rectifiable_path_differentiable:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "negligible S"
    "g absolutely_continuous_on {0..1}"
    "\<And>t. t \<in> {0..1} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "rectifiable_path g"
  sorry

lemma path_length_differentiable:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "negligible S"
    "g absolutely_continuous_on {0..1}"
    "\<And>t. t \<in> {0..1} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "path_length g = integral {0..1} (\<lambda>t. norm (g' t))"
  sorry

end
