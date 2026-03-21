theory Arc_Length_Reparametrization
  imports Rectifiable_Path
begin

text \<open>
  Arc length reparametrization for rectifiable paths, following HOL Light's
  @{text "Multivariate/integration.ml"} (lines 24391--24980).

  Given a rectifiable path @{term g}, there exists a reparametrization @{term h}
  that is Lipschitz with constant @{term "path_length g"}, preserves the path image,
  and has the property that arc length grows linearly with the parameter.
\<close>

section \<open>Reparametrization\<close>

lemma rectifiable_path_reparametrization:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "rectifiable_path g"
    "\<phi> continuous_on {0..1}" "\<phi> ` {0..1} \<subseteq> {0..1}"
    "\<phi> 0 = 0" "\<phi> 1 = 1"
  shows "rectifiable_path (g \<circ> \<phi>)"
  sorry

lemma path_length_reparametrization:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "rectifiable_path g"
    "\<phi> continuous_on {0..1}" "\<phi> ` {0..1} \<subseteq> {0..1}"
    "\<phi> 0 = 0" "\<phi> 1 = 1"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> x \<le> y \<Longrightarrow> \<phi> x \<le> \<phi> y"
  shows "path_length (g \<circ> \<phi>) = path_length g"
  sorry

section \<open>Arc length reparametrization\<close>

theorem arc_length_reparametrization:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "rectifiable_path g"
  shows "\<exists>h. rectifiable_path h \<and>
    path_image h = path_image g \<and>
    pathstart h = pathstart g \<and>
    pathfinish h = pathfinish g \<and>
    path_length h = path_length g \<and>
    (arc g \<longrightarrow> arc h) \<and>
    (simple_path g \<longrightarrow> simple_path h) \<and>
    (\<forall>t \<in> {0..1}. path_length (subpath 0 t h) = path_length g * t) \<and>
    (\<forall>x \<in> {0..1}. \<forall>y \<in> {0..1}.
      dist (h x) (h y) \<le> path_length g * dist x y)"
  sorry

section \<open>Uniqueness and minimality\<close>

lemma arc_length_unique:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "rectifiable_path g"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow>
      dist (g x) (g y) \<le> path_length g * dist x y"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t g) = path_length g * t"
    "rectifiable_path h"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow>
      dist (h x) (h y) \<le> path_length h * dist x y"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = path_length h * t"
    "path_image g = path_image h"
    "pathstart g = pathstart h"
  shows "g = h"
  sorry

lemma arc_length_minimal:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "rectifiable_path g" "arc g"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow>
      dist (g x) (g y) \<le> path_length g * dist x y"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t g) = path_length g * t"
    "rectifiable_path h" "path_image h = path_image g"
    "pathstart h = pathstart g" "pathfinish h = pathfinish g"
  shows "path_length g \<le> path_length h"
  sorry

lemma simple_path_length_minimal:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "rectifiable_path g" "simple_path g" "pathfinish g = pathstart g"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow>
      dist (g x) (g y) \<le> path_length g * dist x y"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t g) = path_length g * t"
    "rectifiable_path h" "simple_path h" "pathfinish h = pathstart h"
    "path_image h = path_image g"
  shows "path_length g \<le> path_length h"
  sorry

section \<open>Continuous dependence of path length on subpath\<close>

lemma continuous_on_path_length_subpath_right:
  "rectifiable_path g \<Longrightarrow>
    (\<lambda>t. path_length (subpath s t g)) continuous_on {0..1}"
  sorry

lemma continuous_on_path_length_subpath_left:
  "rectifiable_path g \<Longrightarrow>
    (\<lambda>s. path_length (subpath s t g)) continuous_on {0..1}"
  sorry

end
