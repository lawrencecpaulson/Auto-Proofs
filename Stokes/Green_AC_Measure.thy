theory Green_AC_Measure
  imports Green_AC_Winding
begin

lemma green_rectifiable_path_image_negligible:
  fixes g :: "real \<Rightarrow> complex"
  assumes rect: "rectifiable_path g"
  shows "negligible (path_image g)"
proof -
  obtain h where "rectifiable_path h"
    and image: "path_image h = path_image g"
    and "pathstart h = pathstart g"
    and "pathfinish h = pathfinish g"
    and "path_length h = path_length g"
    and "arc g \<Longrightarrow> arc h"
    and "simple_path g \<Longrightarrow> simple_path h"
    and "\<forall>t\<in>{0..1}. path_length (subpath 0 t h) = path_length g * t"
    and lip: "\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}.
        dist (h x) (h y) \<le> path_length g * dist x y"
    by (rule arc_length_reparametrization[OF rect]) blast
  let ?S = "(of_real :: real \<Rightarrow> complex) ` {0..1}"
  have small: "negligible ?S"
    by (rule negligible_differentiable_image_lowdim)
      (auto simp: differentiable_on_def)
  have length_nonneg: "0 \<le> path_length g"
    using path_length_pos_le[OF rect] by simp
  have local_lip:
    "\<exists>T B. open T \<and> x \<in> T \<and>
      (\<forall>y\<in>?S \<inter> T.
        norm (h (Re y) - h (Re x)) \<le> B * norm (y - x))"
    if x: "x \<in> ?S" for x
  proof (intro exI[where x=UNIV] exI[where x="path_length g"] conjI ballI)
    show "open (UNIV :: complex set)" by simp
    show "x \<in> UNIV" by simp
    fix y assume y: "y \<in> ?S \<inter> UNIV"
    have xI: "Re x \<in> {0..1}" and yI: "Re y \<in> {0..1}"
      using x y by auto
    have "norm (h (Re y) - h (Re x)) \<le>
        path_length g * \<bar>Re (y - x)\<bar>"
      using lip xI yI by (simp add: dist_norm)
    also have "\<dots> \<le> path_length g * norm (y - x)"
      by (rule mult_left_mono[OF abs_Re_le_cmod length_nonneg])
    finally show "norm (h (Re y) - h (Re x)) \<le>
        path_length g * norm (y - x)" .
  qed
  have "negligible ((\<lambda>z. h (Re z)) ` ?S)"
    by (rule negligible_locally_Lipschitz_image)
      (use small local_lip in auto)
  then show ?thesis
    using image by (simp add: path_image_def image_comp)
qed

corollary green_ac_path_image_negligible:
  fixes g :: "real \<Rightarrow> complex"
  assumes "absolutely_continuous_on {0..1} g"
  shows "negligible (path_image g)"
  by (rule green_rectifiable_path_image_negligible
    [OF green_ac_path_rectifiable[OF assms]])

corollary green_ac_cauchy_contour_integrable_ae:
  fixes g :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
  shows "negligible
    {z. \<not> (\<lambda>w. 1 / (w - z)) contour_integrable_on g}"
proof -
  let ?N = "{t \<in> {0..1}. \<not> g differentiable (at t)}"
  have null: "negligible ?N"
    by (rule green_ac_path_derivative_ae[OF ac])
  have deriv: "(g has_vector_derivative (vector_derivative g (at t))) (at t)"
    if "t \<in> {0..1} - ?N" for t
    using that by (simp add: vector_derivative_works)
  have integrable: "(\<lambda>w. 1 / (w - z)) contour_integrable_on g"
    if "z \<notin> path_image g" for z
    by (rule green_ac_winding_kernel_integrable[OF ac null deriv that])
  have "{z. \<not> (\<lambda>w. 1 / (w - z)) contour_integrable_on g}
      \<subseteq> path_image g"
    using integrable by blast
  then show ?thesis
    by (rule negligible_subset[OF green_ac_path_image_negligible[OF ac]])
qed

end
