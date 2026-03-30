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
  unfolding rectifiable_path_def path_length_def
  by (auto intro: vector_variation_pos_le)

lemma path_length_eq_0:
  "rectifiable_path g \<Longrightarrow>
    (path_length g = 0 \<longleftrightarrow> (\<exists>c. \<forall>t \<in> {0..1}. g t = c))"
  unfolding rectifiable_path_def path_length_def
  by (rule vector_variation_const_eq) auto

lemma simple_path_length_pos_lt:
  "rectifiable_path g \<Longrightarrow> simple_path g \<Longrightarrow> 0 < path_length g"
 proof -
  assume rect: "rectifiable_path g" and sp: "simple_path g"
  have "path_length g \<noteq> 0"
  proof
    assume "path_length g = 0"
    then obtain c where c: "\<And>t. t \<in> {0..1} \<Longrightarrow> g t = c"
      using path_length_eq_0[OF rect] by auto
    hence "g (1/4) = g (3/4)" by auto
    moreover from sp have "inj_on g {0<..<1}" by (rule simple_path_inj_on)
    ultimately have "(1/4::real) = 3/4"
      by (auto dest: inj_onD)
    thus False by simp
  qed
  with path_length_pos_le[OF rect] show "0 < path_length g"
    by linarith
 qed

section \<open>Invariance under transformations\<close>

lemma rectifiable_path_translation_eq:
  "rectifiable_path ((\<lambda>x. a + x) \<circ> g) \<longleftrightarrow> rectifiable_path g"
proof -
  have "path g"
    if "path (\<lambda>x. a + g x)"
      and "has_bounded_variation_on (\<lambda>x. a + g x) {0..1}"
    using that path_translation_eq[of a g] by (simp add: o_def)
  moreover have "has_bounded_variation_on g {0..1}"
    if "path (\<lambda>x. a + g x)"
      and "has_bounded_variation_on (\<lambda>x. a + g x) {0..1}"
  proof -
    have "has_bounded_variation_on (\<lambda>x. a + g x + (- a)) {0..1}"
      using that(2) has_bounded_variation_on_const[of "-a" "{0..1}"]
      by (rule has_bounded_variation_on_add)
    then show ?thesis by simp
  qed
  moreover have "path (\<lambda>x. a + g x)"
    if "path g"
      and "has_bounded_variation_on g {0..1}"
    using that path_translation_eq[of a g] by (simp add: o_def)
  moreover have "has_bounded_variation_on (\<lambda>x. a + g x) {0..1}"
    if "path g"
      and "has_bounded_variation_on g {0..1}"
    using that(2) has_bounded_variation_on_const[of a "{0..1}"]
    by (auto intro: has_bounded_variation_on_add)
  ultimately show ?thesis
    by (auto simp: o_def rectifiable_path_def)
qed

lemma path_length_translation:
  "path_length ((\<lambda>x. a + x) \<circ> g) = path_length g"
  unfolding path_length_def vector_variation_def comp_def
  by (simp add: algebra_simps)

lemma has_bounded_variation_on_linear_image:
  assumes "linear f" "has_bounded_variation_on g {0..1}"
  shows "has_bounded_variation_on (f \<circ> g) {0..1}"
proof -
  have bl: "bounded_linear f" using assms(1) linear_conv_bounded_linear by auto
  have bound: "\<And>d. d division_of {0..1} \<Longrightarrow>
    (\<Sum>k\<in>d. norm ((f \<circ> g) (Sup k) - (f \<circ> g) (Inf k)))
    \<le> onorm f * vector_variation {0..1} g"
  proof -
    fix d :: "real set set" assume div: "d division_of {0..1}"
    have "(\<Sum>k\<in>d. norm ((f \<circ> g) (Sup k) - (f \<circ> g) (Inf k)))
      = (\<Sum>k\<in>d. norm (f (g (Sup k) - g (Inf k))))" 
      using assms(1) by (simp add: o_def linear_diff)
    also have "\<dots> \<le> (\<Sum>k\<in>d. onorm f * norm (g (Sup k) - g (Inf k)))" 
      by (intro sum_mono onorm[OF bl])
    also have "\<dots> = onorm f * (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))" 
      by (simp add: sum_distrib_left)
    also have "\<dots> \<le> onorm f * vector_variation {0..1} g" 
      by (intro mult_left_mono has_bounded_variation_works(1)[OF assms(2) div order_refl]
          onorm_pos_le[OF bl])
    finally show "(\<Sum>k\<in>d. norm ((f \<circ> g) (Sup k) - (f \<circ> g) (Inf k)))
      \<le> onorm f * vector_variation {0..1} g" .
  qed
  then show ?thesis
    unfolding has_bounded_variation_on_interval by blast
qed

lemma rectifiable_path_linear_image_eq:
  assumes "linear f" "inj f"
  shows "rectifiable_path (f \<circ> g) \<longleftrightarrow> rectifiable_path g"
proof
  assume "rectifiable_path g"
  then show "rectifiable_path (f \<circ> g)"
    unfolding rectifiable_path_def
    using path_linear_image_eq[OF assms] has_bounded_variation_on_linear_image[OF assms(1)]
    by auto
next
  assume fg: "rectifiable_path (f \<circ> g)"
  have invf: "has_bounded_variation_on g {0..1}"
  proof -
    obtain B where "B > 0" and Bbound: "\<And>x. B * norm x \<le> norm (f x)"
      using linear_inj_bounded_below_pos[OF assms(1) assms(2)] by auto
    have bv_fg: "has_bounded_variation_on (f \<circ> g) {0..1}"
      using fg unfolding rectifiable_path_def by auto
    show ?thesis unfolding has_bounded_variation_on_interval
    proof -
      obtain C where C: "\<And>d. d division_of {0..1} \<Longrightarrow>
        (\<Sum>k\<in>d. norm ((f \<circ> g) (Sup k) - (f \<circ> g) (Inf k))) \<le> C"
        using bv_fg unfolding has_bounded_variation_on_interval by auto
      { fix d :: "real set set" assume div: "d division_of {0..1}"
        have "(\<Sum>k\<in>d. B * norm (g (Sup k) - g (Inf k)))
          \<le> (\<Sum>k\<in>d. norm (f (g (Sup k) - g (Inf k))))" 
          by (intro sum_mono Bbound)
        also have "\<dots> = (\<Sum>k\<in>d. norm ((f \<circ> g) (Sup k) - (f \<circ> g) (Inf k)))"
          using assms(1) by (simp add: o_def real_vector.linear_diff)
        also have "\<dots> \<le> C" using C[OF div] .
        finally have "B * (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> C"
          by (simp add: sum_distrib_left)
        then have "(\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> C / B"
          using \<open>B > 0\<close> by (simp add: field_simps) }
      then show "\<exists>B. \<forall>d. d division_of {0..1} \<longrightarrow>
        (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> B" by blast
    qed
  qed
  moreover have "path g"
    using fg path_linear_image_eq[OF assms(1) assms(2)] unfolding rectifiable_path_def by auto
  ultimately show "rectifiable_path g"
    unfolding rectifiable_path_def by auto
qed


lemma path_length_linear_image:
  assumes "linear f" "\<And>x. norm (f x) = norm x"
  shows "path_length (f \<circ> g) = path_length g"
proof -
  have eq: "\<And>k. norm (f (g (Sup k)) - f (g (Inf k))) = norm (g (Sup k) - g (Inf k))"
    by (metis assms(1) assms(2) real_vector.linear_diff)
  then show ?thesis
    unfolding path_length_def vector_variation_def set_variation_def comp_def by presburger
qed


lemma rectifiable_path_eq:
  assumes eq: "\<And>t. t \<in> {0..1} \<Longrightarrow> g t = h t"
    and rect: "rectifiable_path g"
  shows "rectifiable_path h"
proof -
  have "path h"
  proof -
    have "continuous_on {0..1} h = continuous_on {0..1} g"
      by (rule continuous_on_cong_simp[OF refl]) (use eq in \<open>simp add: simp_implies_def\<close>)
    then show ?thesis using rect unfolding rectifiable_path_def path_def by auto
  qed
  moreover have "has_bounded_variation_on h {0..1}"
  proof -
    from rect have bv: "has_bounded_variation_on g {0..1}"
      unfolding rectifiable_path_def by auto
    have sup_inf_in: "Sup k \<in> {0..1} \<and> Inf k \<in> {0..1}"
      if "d division_of {(0::real)..1}" "k \<in> d" for d k
    proof -
      from division_ofD(2)[OF that] have ks: "k \<subseteq> {0..1}" .
      from division_ofD(3)[OF that] have kne: "k \<noteq> {}" .
      from division_ofD(4)[OF that] obtain a b where kab: "k = cbox a b" by auto
      with kne have "a \<le> b" by auto
      then have "Sup k = b" "Inf k = a"
        using kab by (auto simp: cSup_atLeastAtMost cInf_atLeastAtMost)
      then show ?thesis using ks kab \<open>a \<le> b\<close> by auto
    qed
    have sums_eq: "(\<Sum>k\<in>d. norm (h (Sup k) - h (Inf k))) = (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))"
      if "d division_of {(0::real)..1}" for d
      using sup_inf_in[OF that] by (intro sum.cong refl) (auto simp: eq)
    then show ?thesis
      using bv unfolding has_bounded_variation_on_interval by auto
  qed
  ultimately show ?thesis unfolding rectifiable_path_def by auto
qed

lemma path_length_eq:
  assumes eq: "\<And>t. t \<in> {0..1} \<Longrightarrow> g t = h t"
    and rect: "rectifiable_path g"
  shows "path_length g = path_length h"
proof -
  have sup_inf_in: "Sup k \<in> {0..1} \<and> Inf k \<in> {0..1}"
    if "d division_of t" "t \<subseteq> {(0::real)..1}" "k \<in> d" for d t k
  proof -
    from division_ofD(2)[OF that(1) that(3)] that(2) have ks: "k \<subseteq> {0..1}" by auto
    from division_ofD(3)[OF that(1) that(3)] have kne: "k \<noteq> {}" .
    from division_ofD(4)[OF that(1) that(3)] obtain a b where kab: "k = cbox a b" by auto
    with kne have "a \<le> b" by auto
    then have "Sup k = b" "Inf k = a"
      using kab by (auto simp: cSup_atLeastAtMost cInf_atLeastAtMost)
    then show ?thesis using ks kab \<open>a \<le> b\<close> by auto
  qed
  have sums_eq: "(\<Sum>k\<in>d. norm (h (Sup k) - h (Inf k))) = (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))"
    if "d division_of t" "t \<subseteq> {(0::real)..1}" for d t
    using sup_inf_in[OF that] by (intro sum.cong refl) (auto simp: eq)
  have "{\<Sum>k\<in>d. norm (h (Sup k) - h (Inf k)) |d. \<exists>t. d division_of t \<and> t \<subseteq> {0..1}}
      = {\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)) |d. \<exists>t. d division_of t \<and> t \<subseteq> {0..1}}"
    by (metis (lifting) sums_eq)
  then show ?thesis
    unfolding path_length_def vector_variation_def set_variation_def by auto
qed


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
