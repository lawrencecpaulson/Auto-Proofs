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
  unfolding path_length_def reversepath_def comp_def[symmetric]
  using vector_variation_reflect[of 0 1 g 1] by simp

lemma rectifiable_path_subpath:
  "\<lbrakk>rectifiable_path g; u \<in> {0..1}; v \<in> {0..1}\<rbrakk> \<Longrightarrow>
    rectifiable_path (subpath u v g)"
  unfolding rectifiable_path_def subpath_def
proof (intro conjI)
  assume rect: "path g \<and> has_bounded_variation_on g {0..1}" and u: "u \<in> {0..1}" and v: "v \<in> {0..1}"
  show "path (\<lambda>x. g ((v - u) * x + u))"
    using rect u v path_subpath unfolding subpath_def by auto
  have bv: "has_bounded_variation_on g {0..1}" using rect by auto
  have seg: "closed_segment u v \<subseteq> {0..1}" using u v
    by (auto simp: closed_segment_eq_real_ivl split: if_splits)
  show "has_bounded_variation_on (\<lambda>x. g ((v - u) * x + u)) {0..1}"
  proof (cases "u \<le> v")
    case True
    have mono: "mono_on {0..1} (\<lambda>x. (v - u) * x + u)"
      using True by (auto intro!: mono_onI mult_left_mono)
    have "has_bounded_variation_on g {u..v}"
      using bv seg True by (auto simp: closed_segment_eq_real_ivl
        intro: has_bounded_variation_on_subset)
    then show ?thesis
      using has_bounded_variation_compose_monotone(1)[of g "\<lambda>x. (v-u)*x+u" 0 1]
        mono True by (simp add: comp_def)
  next
    case False
    then have vu: "v \<le> u" by auto
    have mono: "mono_on {0..1} (\<lambda>x. (u - v) * x + v)"
      using vu by (auto intro!: mono_onI mult_left_mono)
    have bvvu: "has_bounded_variation_on g {v..u}"
      using bv seg vu
      by (auto simp: closed_segment_eq_real_ivl split: if_splits
        intro: has_bounded_variation_on_subset)
    have "(\<lambda>x. g ((v - u) * x + u)) = (\<lambda>x. g ((u - v) * (1 - x) + v))"
      by (auto simp: algebra_simps)
    also have "\<dots> = (g \<circ> (\<lambda>x. (u-v)*x + v)) \<circ> (\<lambda>x. 1 - x)"
      by (auto simp: comp_def)
    finally have eq: "(\<lambda>x. g ((v - u) * x + u)) = (g \<circ> (\<lambda>x. (u-v)*x + v)) \<circ> (-) 1"
      by (auto simp: comp_def)
    have "has_bounded_variation_on (g \<circ> (\<lambda>x. (u-v)*x + v)) {0..1}"
      using has_bounded_variation_compose_monotone(1)[of g "\<lambda>x. (u-v)*x+v" 0 1]
        mono bvvu by (simp add: comp_def)
    then have "has_bounded_variation_on (g \<circ> (\<lambda>x. (u-v)*x + v)) {1 - 1..1 - 0}"
      by simp
    then have "has_bounded_variation_on ((g \<circ> (\<lambda>x. (u-v)*x + v)) \<circ> (-) 1) {0..1}"
      by (rule has_bounded_variation_on_reflect)
    then show ?thesis
      using eq by simp
  qed
qed

lemma division_of_affine_image:
  fixes c d :: real
  assumes cpos: "c > 0" and div: "D division_of T" and sub: "T \<subseteq> {a..b}"
  shows "((`) (\<lambda>x. c * x + d)) ` D division_of ((\<lambda>x. c * x + d) ` T)"
    and "(\<lambda>x. c * x + d) ` T \<subseteq> {c*a+d..c*b+d}"
proof -
  let ?\<phi> = "\<lambda>x::real. c * x + d"
  have inj: "inj ?\<phi>" using cpos by (intro injI) simp
  have mono: "mono ?\<phi>" using cpos by (intro monoI) auto
  show sub': "?\<phi> ` T \<subseteq> {c*a+d..c*b+d}"
    using sub cpos by (auto simp: mult_left_mono)
  show "((`) ?\<phi>) ` D division_of (?\<phi> ` T)"
    unfolding division_of_def
  proof (intro conjI ballI impI)
    show "finite (((`) ?\<phi>) ` D)"
      using division_ofD(1)[OF div] by auto
  next
    fix K assume "K \<in> ((`) ?\<phi>) ` D"
    then obtain K0 where K0: "K0 \<in> D" "K = ?\<phi> ` K0" by auto
    from division_ofD(2)[OF div K0(1)] have K0sub: "K0 \<subseteq> T" .
    from division_ofD(3)[OF div K0(1)] have K0ne: "K0 \<noteq> {}" .
    then show "K \<subseteq> ?\<phi> ` T" "K \<noteq> {}" using K0(2) K0sub by auto
    from division_ofD(4)[OF div K0(1)] obtain \<alpha> \<beta> where ab: "K0 = cbox \<alpha> \<beta>" by auto
    then have "K0 = {\<alpha>..\<beta>}" by auto
    with K0ne have \<alpha>\<beta>: "\<alpha> \<le> \<beta>" by auto
    have "K = ?\<phi> ` {\<alpha>..\<beta>}" using K0(2) \<open>K0 = {\<alpha>..\<beta>}\<close> by auto
    also have "\<dots> = {c*\<alpha>+d..c*\<beta>+d}"
    proof -
      have "?\<phi> ` {\<alpha>..\<beta>} = {y. \<exists>x. \<alpha> \<le> x \<and> x \<le> \<beta> \<and> y = c*x+d}"
        by (auto simp: image_def)
      also have "\<dots> = {c*\<alpha>+d..c*\<beta>+d}"
      proof (auto simp: mult_left_mono[OF _ less_imp_le[OF cpos]])
        fix y assume "c * \<alpha> + d \<le> y" "y \<le> c * \<beta> + d"
        then have "\<alpha> \<le> (y - d) / c" "((y - d) / c) \<le> \<beta>"
          using cpos by (auto simp: field_simps)
        moreover have "y = c * ((y - d) / c) + d" using cpos by auto
        ultimately show "\<exists>x\<ge>\<alpha>. x \<le> \<beta> \<and> y = c * x + d" by auto
      qed
      finally show ?thesis .
    qed
    finally show "\<exists>\<alpha> \<beta>. K = cbox \<alpha> \<beta>" by (auto simp: cbox_interval)
  next
    fix K1 K2
    assume "K1 \<in> ((`) ?\<phi>) ` D" "K2 \<in> ((`) ?\<phi>) ` D" "K1 \<noteq> K2"
    then obtain K1' K2' where K1': "K1' \<in> D" "K1 = ?\<phi> ` K1'"
      and K2': "K2' \<in> D" "K2 = ?\<phi> ` K2'" by auto
    have "K1' \<noteq> K2'" using \<open>K1 \<noteq> K2\<close> K1'(2) K2'(2) inj_image_eq_iff[OF inj] by auto
    then have disj: "interior K1' \<inter> interior K2' = {}"
      using division_ofD(5)[OF div K1'(1) K2'(1)] by auto
    show "interior K1 \<inter> interior K2 = {}"
    proof (rule ccontr)
      assume "interior K1 \<inter> interior K2 \<noteq> {}"
      then obtain y where "y \<in> interior K1" "y \<in> interior K2" by auto
      from division_ofD(4)[OF div K1'(1)] obtain a1 b1 where "K1' = cbox a1 b1" by auto
      from division_ofD(4)[OF div K2'(1)] obtain a2 b2 where "K2' = cbox a2 b2" by auto
      then have K1eq: "K1' = {a1..b1}" and K2eq: "K2' = {a2..b2}"
        using \<open>K1' = cbox a1 b1\<close> by auto
      from division_ofD(3)[OF div K1'(1)] K1eq have "a1 \<le> b1" by (auto split: if_splits)
      from division_ofD(3)[OF div K2'(1)] K2eq have "a2 \<le> b2" by (auto split: if_splits)
      have K1img: "K1 = {c*a1+d..c*b1+d}" 
      proof -
        have "K1 = ?\<phi> ` {a1..b1}" using K1'(2) K1eq by auto
        also have "\<dots> = {c*a1+d..c*b1+d}"
        proof safe
          fix x assume "x \<in> {a1..b1}"
          then show "?\<phi> x \<in> {c*a1+d..c*b1+d}" using cpos
            by (auto intro: mult_left_mono)
        next
          fix y assume "y \<in> {c*a1+d..c*b1+d}"
          then have mem: "(y-d)/c \<in> {a1..b1}" using cpos by (auto simp: field_simps)
          moreover have "?\<phi> ((y-d)/c) = y" using cpos by (simp add: field_simps)
          ultimately show "y \<in> ?\<phi> ` {a1..b1}" by force
        qed
        finally show ?thesis .
      qed
      have K2img: "K2 = {c*a2+d..c*b2+d}"
      proof -
        have "K2 = ?\<phi> ` {a2..b2}" using K2'(2) K2eq by auto
        also have "\<dots> = {c*a2+d..c*b2+d}"
        proof safe
          fix x assume "x \<in> {a2..b2}"
          then show "?\<phi> x \<in> {c*a2+d..c*b2+d}" using cpos
            by (auto intro: mult_left_mono)
        next
          fix y assume "y \<in> {c*a2+d..c*b2+d}"
          then have "(y-d)/c \<in> {a2..b2}" using cpos by (auto simp: field_simps)
          moreover have "?\<phi> ((y-d)/c) = y" using cpos by (simp add: field_simps)
          ultimately show "y \<in> ?\<phi> ` {a2..b2}" by force
        qed
        finally show ?thesis .
      qed
      from \<open>y \<in> interior K1\<close> K1img have "c*a1+d < y" "y < c*b1+d"
        using \<open>a1 \<le> b1\<close> interior_atLeastAtMost_real by auto
      then have "a1 < (y-d)/c" "(y-d)/c < b1" using cpos by (auto simp: field_simps)
      then have "(y-d)/c \<in> interior K1'"
        using K1eq interior_atLeastAtMost_real by auto
      from \<open>y \<in> interior K2\<close> K2img have "c*a2+d < y" "y < c*b2+d"
        using \<open>a2 \<le> b2\<close> interior_atLeastAtMost_real by auto
      then have "a2 < (y-d)/c" "(y-d)/c < b2" using cpos by (auto simp: field_simps)
      then have "(y-d)/c \<in> interior K2'"
        using K2eq interior_atLeastAtMost_real by auto
      with \<open>(y-d)/c \<in> interior K1'\<close> disj show False by auto
    qed
  next
    have "\<Union> (((`) ?\<phi>) ` D) = ?\<phi> ` (\<Union> D)" by auto
    also have "\<Union> D = T" using division_ofD(6)[OF div] by auto
    finally show "\<Union> (((`) ?\<phi>) ` D) = ?\<phi> ` T" .
  qed
qed

lemma vector_variation_affine_eq:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space" and c d :: real
  assumes "c > 0" "a \<le> b"
  shows "vector_variation {a..b} (g \<circ> (\<lambda>x. c * x + d)) = vector_variation {c*a+d..c*b+d} g"
proof -
  let ?\<phi> = "\<lambda>x::real. c * x + d"
  let ?\<psi> = "\<lambda>x::real. (x - d) / c"
  have cne: "c \<noteq> 0" using assms(1) by auto
  have cpos: "0 < c" using assms(1) .
  have inj_\<phi>: "inj ?\<phi>" using cne by (intro injI) simp
  have \<phi>\<psi>: "\<And>x. ?\<phi> (?\<psi> x) = x" using cne by (simp add: field_simps)
  have \<psi>\<phi>: "\<And>x. ?\<psi> (?\<phi> x) = x" using cne by (simp add: field_simps)
  have ab': "c*a+d \<le> c*b+d" using assms by (auto intro: mult_left_mono)
  have img_ivl: "\<And>\<alpha> \<beta>. \<alpha> \<le> \<beta> \<Longrightarrow> ?\<phi> ` {\<alpha>..\<beta>} = {c*\<alpha>+d..c*\<beta>+d}"
  proof safe
    fix \<alpha> \<beta> x :: real assume "\<alpha> \<le> \<beta>" "x \<in> {\<alpha>..\<beta>}"
    then show "?\<phi> x \<in> {c*\<alpha>+d..c*\<beta>+d}" using cpos by (auto intro: mult_left_mono)
  next
    fix \<alpha> \<beta> y :: real assume "\<alpha> \<le> \<beta>" "y \<in> {c*\<alpha>+d..c*\<beta>+d}"
    then have "(y-d)/c \<in> {\<alpha>..\<beta>}" using cpos by (auto simp: field_simps)
    moreover have "?\<phi> ((y-d)/c) = y" using cne by (simp add: field_simps)
    ultimately show "y \<in> ?\<phi> ` {\<alpha>..\<beta>}" by force
  qed
  \<comment> \<open>Key: the variation sums over divisions of any T equal those over \<phi>(T)\<close>
  have sum_transform: "(\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
    = (\<Sum>k\<in>((`) ?\<phi>) ` D. norm (g (Sup k) - g (Inf k)))"
    if "D division_of T" for D :: "real set set" and T :: "real set"
  proof -
    have div: "D division_of T" using that .
    have inj_on_img: "inj_on ((`) ?\<phi>) D"
      using inj_image_eq_iff[OF inj_\<phi>] by (auto intro!: inj_onI)
    have "(\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>D. norm (g (?\<phi> (Sup k)) - g (?\<phi> (Inf k))))" by (simp add: o_def)
    also have "\<dots> = (\<Sum>k\<in>D. norm (g (Sup (?\<phi> ` k)) - g (Inf (?\<phi> ` k))))"
    proof (intro sum.cong refl arg_cong[where f=norm] arg_cong2[where f="(-)"])
      fix k assume "k \<in> D"
      from division_ofD(4)[OF div this] obtain \<alpha> \<beta> where kab: "k = cbox \<alpha> \<beta>" by auto
      from division_ofD(3)[OF div \<open>k \<in> D\<close>] have kne: "k \<noteq> {}" .
      with kab have le: "\<alpha> \<le> \<beta>" by auto
      have k_ivl: "k = {\<alpha>..\<beta>}" using kab by auto
      have img: "?\<phi> ` k = {c*\<alpha>+d..c*\<beta>+d}" using img_ivl[OF le] k_ivl by simp
      have le': "c*\<alpha>+d \<le> c*\<beta>+d" using le cpos by (auto intro: mult_left_mono)
      show "g (?\<phi> (Sup k)) = g (Sup (?\<phi> ` k))"
        using k_ivl le img le' by (simp add: cSup_atLeastAtMost)
      show "g (?\<phi> (Inf k)) = g (Inf (?\<phi> ` k))"
        using k_ivl le img le' by (simp add: cInf_atLeastAtMost)
    qed
    also have "\<dots> = (\<Sum>k\<in>((`) ?\<phi>) ` D. norm (g (Sup k) - g (Inf k)))"
      by (metis (no_types, lifting) inj_on_img sum.reindex_cong)
    finally show "(\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>((`) ?\<phi>) ` D. norm (g (Sup k) - g (Inf k)))" .
  qed
  \<comment> \<open>Now show the Sup sets in the vector_variation definition are equal\<close>
  have sets_eq: "{\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)) |D.
      \<exists>T. D division_of T \<and> T \<subseteq> {a..b}}
    = {\<Sum>k\<in>D. norm (g (Sup k) - g (Inf k)) |D.
      \<exists>T. D division_of T \<and> T \<subseteq> {c*a+d..c*b+d}}"
  proof safe
    fix D T assume div: "D division_of T" and sub: "T \<subseteq> {a..b}"
    let ?D' = "((`) ?\<phi>) ` D"
    have div': "?D' division_of (?\<phi> ` T)"
      using division_of_affine_image(1)[OF cpos div sub] .
    have sub': "?\<phi> ` T \<subseteq> {c*a+d..c*b+d}"
      using division_of_affine_image(2)[OF cpos div sub] .
    have sum_eq: "(\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>?D'. norm (g (Sup k) - g (Inf k)))"
      using sum_transform[OF div] .
    show "\<exists>Da. (\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>Da. norm (g (Sup k) - g (Inf k)))
      \<and> (\<exists>T. Da division_of T \<and> T \<subseteq> {c*a+d..c*b+d})"
      using sum_eq div' sub' by blast
  next
    fix D T assume div: "D division_of T" and sub: "T \<subseteq> {c*a+d..c*b+d}"
    \<comment> \<open>Map back via the inverse affine map (1/c)*x + (-d/c)\<close>
    let ?c' = "1/c" and ?d' = "-d/c"
    have cpos': "?c' > 0" using cpos by auto
    have div': "((`) (\<lambda>x. ?c' * x + ?d')) ` D division_of ((\<lambda>x. ?c' * x + ?d') ` T)"
      using division_of_affine_image(1)[OF cpos' div sub] .
    have sub': "(\<lambda>x. ?c' * x + ?d') ` T \<subseteq> {?c'*(c*a+d)+?d'..?c'*(c*b+d)+?d'}"
      using division_of_affine_image(2)[OF cpos' div sub] .
    have endpoints: "?c'*(c*a+d)+?d' = a" "?c'*(c*b+d)+?d' = b"
      using cne by (auto simp: field_simps)
    \<comment> \<open>The inverse map equals \<psi>\<close>
    have inv_eq: "(\<lambda>x::real. ?c' * x + ?d') = ?\<psi>"
      by (rule ext) (simp add: diff_divide_distrib)
    have div'': "((`) ?\<psi>) ` D division_of (?\<psi> ` T)"
      using div' unfolding inv_eq .
    have sub'': "?\<psi> ` T \<subseteq> {a..b}"
    proof -
      have "(\<lambda>x::real. ?c' * x + ?d') ` T \<subseteq> {a..b}"
        using sub' endpoints by auto
      then show ?thesis unfolding inv_eq .
    qed
    \<comment> \<open>Show the sum over D equals the sum over \<psi>-image composed with \<phi>\<close>
    have sum_eq: "(\<Sum>k\<in>((`) ?\<psi>) ` D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>((`) ?\<phi>) ` ((`) ?\<psi>) ` D. norm (g (Sup k) - g (Inf k)))"
      using sum_transform[OF div''] .
    have \<phi>\<psi>_img: "?\<phi> ` ?\<psi> ` S = S" for S :: "real set"
    proof -
      have "?\<phi> ` ?\<psi> ` S = (?\<phi> \<circ> ?\<psi>) ` S" by (simp add: image_image)
      also have "(?\<phi> \<circ> ?\<psi>) = id"
        using cne by (auto simp: o_def field_simps)
      also have "id ` S = S" by simp
      finally show ?thesis .
    qed
    have img_back: "((`) ?\<phi>) ` ((`) ?\<psi>) ` D = D"
    proof -
      have "((`) ?\<phi>) ` ((`) ?\<psi>) ` D = ((`) ?\<phi> \<circ> (`) ?\<psi>) ` D"
        by (simp add: image_comp)
      also have "((`) ?\<phi> \<circ> (`) ?\<psi>) = id"
        by (rule ext) (simp add: \<phi>\<psi>_img)
      also have "id ` D = D" by simp
      finally show ?thesis .
    qed
    have sum_eq': "(\<Sum>k\<in>((`) ?\<psi>) ` D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>D. norm (g (Sup k) - g (Inf k)))"
      using sum_eq img_back by simp
    show "\<exists>E. (\<Sum>k\<in>D. norm (g (Sup k) - g (Inf k))) = (\<Sum>k\<in>E. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      \<and> (\<exists>T. E division_of T \<and> T \<subseteq> {a..b})"
      using sum_eq' div'' sub'' by (metis (no_types, lifting))
  qed
  show ?thesis
    unfolding vector_variation_def set_variation_def using sets_eq by auto
qed

lemma path_length_subpath_eq:
  assumes "s \<in> {0..1}" "t \<in> {0..1}"
    and rect: "rectifiable_path g"
  shows "path_length (subpath s t g) = vector_variation (closed_segment s t) g"
  using assms
proof (cases "s \<le> t")
  case True
  then have cs: "closed_segment s t = {s..t}"
    by (simp add: closed_segment_eq_real_ivl)
  show ?thesis
  proof (cases "s = t")
    case True
    then show ?thesis
    proof -
      from \<open>s = t\<close> have cs': "closed_segment s t = {t..t}" using cs by simp
      have "path_length (subpath t t g) = 0"
        by (metis \<open>t \<in> {0..1}\<close> eq_iff_diff_eq_0 mult_zero_left path_length_eq_0 rect
            rectifiable_path_subpath subpath_def)
      moreover have "vector_variation {t..t} g = 0"
        by (rule vector_variation_on_null) (simp add: content_real_eq_0)
      ultimately show ?thesis using \<open>s = t\<close> cs' by simp
    qed
  next
    case False
    with \<open>s \<le> t\<close> have "s < t" by auto
    then have "t - s > 0" by auto
    have "path_length (subpath s t g) = vector_variation {0..1} (g \<circ> (\<lambda>x. (t-s)*x + s))"
      unfolding path_length_def subpath_def by (simp add: comp_def)
    also have "\<dots> = vector_variation {(t-s)*0+s..(t-s)*1+s} g"
      using vector_variation_affine_eq[OF \<open>t - s > 0\<close> zero_le_one, where d=s and g=g] by simp
    also have "\<dots> = vector_variation {s..t} g"
      by simp
    finally show ?thesis by (simp add: cs)
  qed
next
  case False
  then have ts: "t < s" by auto
  then have cs: "closed_segment s t = {t..s}"
    by (simp add: closed_segment_eq_real_ivl)
  have "s - t > 0" using ts by auto
  have "path_length (subpath s t g) = vector_variation {0..1} (\<lambda>x. g ((t - s) * x + s))"
    unfolding path_length_def subpath_def by simp
  also have "\<dots> = vector_variation {0..1} (g \<circ> (\<lambda>x. (s - t) * x + t) \<circ> (-) 1)"
    by (simp add: comp_def algebra_simps)
  finally
   show ?thesis
    using vector_variation_affine_eq[OF \<open>s - t > 0\<close> zero_le_one, where d=t and g=g]
    by (simp add: cs vector_variation_reflect)
qed

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
  "rectifiable_path (linepath a b)"
  sorry

lemma path_length_linepath:
  "path_length (linepath a b) = dist a b"
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
