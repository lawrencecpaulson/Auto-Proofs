theory Isoperimetric
  imports Arc_Length_Reparametrization "Fourier.Square_Integrable" "Green.Integrals" "../Euclidean_Space_Transfer"
    "HOL-ex.Sketch_and_Explore" "../../AutoCorrode-aws-version/iq/Isar_Explore"
begin

hide_const (open) Polynomial.content

section \<open>Library material\<close>

(*added to Jordan_Curve 2026-06*)
lemma exists_double_arc_explicit:
  fixes g :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "simple_path g" and loop: "pathfinish g = pathstart g"
    and a01: "a \<in> {0..1}" and b01: "b \<in> {0..1}" and "a \<le> b" "g a \<noteq> g b"
  obtains u d where "arc u" "arc d" "pathstart u = g a" "pathfinish u = g b"
                    "pathstart d = g b" "pathfinish d = g a"
                    "path_image u = g ` {a..b}"
                    "path_image d = g ` ({0..1} - {a<..<b})"
                    "(path_image u) \<inter> (path_image d) = {g a, g b}"
                    "(path_image u) \<union> (path_image d) = path_image g"
proof -
  have lf: "loop_free g" using assms by (simp add: simple_path_def)
  have g01: "g 0 = g 1" using loop by (simp add: path_defs)
  show ?thesis
  proof (cases "a=0")
    case a [simp]: True
    show thesis
    proof
      show "arc (subpath 0 b g)" "arc (subpath b 1 g)"
        using assms by (auto simp: arc_simple_path_subpath path_defs)
      show "path_image (subpath 0 b g) = g ` {a..b}"
        by (metis a \<open>a \<le> b\<close> path_image_subpath)
      have "path_image (subpath 0 b g) = g ` {0..b}" "path_image (subpath b 1 g) = g ` {b..1}"
        using assms by (simp_all add: path_image_subpath)
      moreover have "g ` {0..b} \<inter> g ` {b..1} = {g 0, g b}"
      proof (intro equalityI subsetI)
        fix x assume "x \<in> g ` {0..b} \<inter> g ` {b..1}"
        then obtain S t where st: "S \<in> {0..b}" "t \<in> {b..1}" "g S = x" "g t = x" "g S = g t"
          by auto
        then have "S = t \<or> S = 0 \<and> t = 1 \<or> S = 1 \<and> t = 0"
          using lf st assms by (auto simp: loop_free_def)
        then show "x \<in> {g 0, g b}" using st by auto
      next
        fix x assume "x \<in> {g 0, g b}"
        then show "x \<in> g ` {0..b} \<inter> g ` {b..1}"
          using assms g01 by (auto intro: rev_image_eqI)
      qed
      ultimately show "path_image (subpath 0 b g) \<inter> path_image (subpath b 1 g) = {g a, g b}"
        by simp
      show "path_image (subpath b 1 g) = g ` ({0..1} - {a<..<b})"
        using g01 assms by (force simp add: path_image_subpath)
      have "g ` {0..b} \<union> g ` {b..1} = g ` {0..1}"
        by (metis b01 atLeastAtMost_iff image_Un ivl_disj_un_two_touch(4))
      then show "path_image (subpath 0 b g) \<union> path_image (subpath b 1 g) = path_image g"
        by (metis b01 atLeastAtMost_iff path_image_def path_image_subpath)
    qed (use g01 in auto)
  next
    case a_nonzero: False
    show thesis
    proof (cases "b=1")
      case b [simp]: True
      show thesis
      proof
        show "arc (subpath a b g)" "arc (subpath 0 a g)"
          using assms a_nonzero by (auto simp: arc_simple_path_subpath path_defs)
        show "path_image (subpath a b g) = g ` {a..b}"
          by (meson assms(5) path_image_subpath)
        show "path_image (subpath 0 a g) = g ` ({0..1} - {a<..<b})"
        proof -
          have "0 \<le> a \<Longrightarrow> \<exists>x\<in>{0..a}. g 1 = g x"
            by (metis g01 atLeastAtMost_iff order_refl)
          then have "path_image (subpath 0 a g) = g ` ({0..a} \<union> {1})"
            using assms by (auto simp: path_image_subpath image_iff)
          also have "\<dots> = g ` ({0..1} - {a<..<b})"
            using assms a_nonzero by auto
          finally show ?thesis .
        qed
        show "path_image (subpath a b g) \<inter> path_image (subpath 0 a g) = {g a, g b}"
        proof -
          have img: "path_image (subpath a b g) = g ` {a..1}" "path_image (subpath 0 a g) = g ` {0..a}"
            using assms by (simp_all add: path_image_subpath)
          have "g ` {a..1} \<inter> g ` {0..a} = {g a, g 1}"
          proof (intro equalityI subsetI)
            fix x assume "x \<in> g ` {a..1} \<inter> g ` {0..a}"
            then obtain S t where st: "S \<in> {a..1}" "t \<in> {0..a}" "g S = x" "g t = x" "g S = g t"
              by auto
            then have "S = t \<or> S = 0 \<and> t = 1 \<or> S = 1 \<and> t = 0"
              using lf st assms by (auto simp: loop_free_def)
            then show "x \<in> {g a, g 1}" using st by auto
          next
            fix x assume "x \<in> {g a, g 1}"
            then show "x \<in> g ` {a..1} \<inter> g ` {0..a}"
              using assms g01 by (auto intro: rev_image_eqI)
          qed
          then show ?thesis using img by (simp add: path_defs)
        qed
        have "g ` {a..1} \<union> g ` {0..a} = g ` {0..1}"
          using assms by (auto simp: image_Un[symmetric] ivl_disj_un_two_touch)
        then show "path_image (subpath a b g) \<union> path_image (subpath 0 a g) = path_image g"
          by (metis assms(3) atLeastAtMost_iff b path_image_def path_image_subpath)
      qed (use g01 in auto)
    next
      case b_nonzero: False
      let ?d = "subpath b 1 g +++ subpath 0 a g"
      have *: "path_image (subpath a b g) = g ` {a..b}" "path_image ?d = g ` {b..1} \<union> g ` {0..a}"
        using assms g01 by (simp_all add: path_image_join path_image_subpath)
      show thesis
      proof
        show "arc (subpath a b g)"
          using assms a_nonzero b_nonzero arc_simple_path_subpath by blast
        have arcs: "arc (subpath b 1 g)" "arc (subpath 0 a g)"
          using assms a_nonzero b_nonzero
          by (auto intro!: arc_simple_path_subpath_interior simp: path_defs)
        have "path_image (subpath b 1 g) \<inter> path_image (subpath 0 a g) \<subseteq> {pathstart (subpath 0 a g)}"
        proof (intro subsetI)
          fix x assume "x \<in> path_image (subpath b 1 g) \<inter> path_image (subpath 0 a g)"
          then obtain S t where S: "S \<in> {b..1}" "g S = x" and t: "t \<in> {0..a}" "g t = x" "g S = g t"
            using assms by (auto simp: path_image_subpath)
          then have "S = t \<or> S = 0 \<and> t = 1 \<or> S = 1 \<and> t = 0"
            using lf assms by (auto simp: loop_free_def)
          then have "t = 0"
            using S t assms by (metis atLeastAtMost_iff nle_le order.trans)
          then show "x \<in> {pathstart (subpath 0 a g)}"
            using t by simp
        qed
        then show "arc ?d"
          using arcs g01 by (simp add: arc_join_eq)
        show "path_image (subpath a b g) = g ` {a..b}"
          by (metis *(1))
        show "path_image ?d = g ` ({0..1} - {a<..<b})"
          using assms g01 by (auto simp add: path_image_join path_image_subpath)
        have "g ` {a..b} \<inter> (g ` {b..1} \<union> g ` {0..a}) = {g a, g b}"
          using lf assms by (force simp: image_iff loop_free_def)
        with * show "path_image (subpath a b g) \<inter> path_image ?d = {g a, g b}"
          by simp
        have "g ` {a..b} \<union> (g ` {b..1} \<union> g ` {0..a}) = g ` {0..1}"
          using a01 b01 by fastforce
        with * show "path_image (subpath a b g) \<union> path_image ?d = path_image g"
          by (simp add: path_image_def sup_assoc)
      qed (use g01 in auto)
    qed
  qed
qed

(*added to Convex_Euclidean_Space 2026-06*)
lemma any_closest_point_affine_orthogonal:
  fixes S :: "('a::euclidean_space) set"
  assumes "affine S" "b \<in> S" "\<And>x. x \<in> S \<Longrightarrow> dist a b \<le> dist a x"
  shows "\<And>x. x \<in> S \<Longrightarrow> orthogonal (x - b) (a - b)"
proof -
  fix x assume "x \<in> S"
  have convS: "convex S" using assms(1) affine_imp_convex by blast
  have closS: "closed S" using assms(1) affine_closed by blast
  have le1: "(a - b) \<bullet> (x - b) \<le> 0"
    using any_closest_point_dot[OF convS closS assms(2) \<open>x \<in> S\<close>] assms(3) by blast
  have "2 *\<^sub>R b - x \<in> S"
    by (metis \<open>x \<in> S\<close> assms(1,2) diff_diff_eq2 mem_affine_3_minus2 scaleR_2 scaleR_one)
  then have le2: "(a - b) \<bullet> ((2 *\<^sub>R b - x) - b) \<le> 0"
    using any_closest_point_dot[OF convS closS assms(2)] assms(3) by blast
  then show "orthogonal (x - b) (a - b)"
    using le1 by (simp add: inner_diff_right algebra_simps orthogonal_def inner_commute)
qed

(*added to Convex_Euclidean_Space 2026-06*)
lemma orthogonal_any_closest_point:
  fixes S :: "('a::euclidean_space) set"
  assumes "b \<in> S" "\<And>x. x \<in> S \<Longrightarrow> orthogonal (x - b) (a - b)"
  shows "\<And>x. x \<in> S \<Longrightarrow> dist a b \<le> dist a x"
proof -
  fix x assume "x \<in> S"
  have orth: "orthogonal (x - b) (a - b)"
    using assms(2)[OF \<open>x \<in> S\<close>] .
  have "orthogonal (a - b) (x - b)"
    using orth by (simp add: orthogonal_commute)
  then have "orthogonal (a - b) (b - x)"
    using orthogonal_clauses(3)[of "a - b" "x - b"] by (simp add: algebra_simps)
  then have "(norm ((a - b) + (b - x)))\<^sup>2 = (norm (a - b))\<^sup>2 + (norm (b - x))\<^sup>2"
    by (rule norm_add_Pythagorean)
  then have "(norm (a - x))\<^sup>2 \<ge> (norm (a - b))\<^sup>2"
    by (simp add: algebra_simps)
  then have "norm (a - x) \<ge> norm (a - b)"
    by (simp add: power2_le_iff_abs_le)
  then show "dist a b \<le> dist a x"
    by (simp add: dist_norm)
qed

(*added to Convex_Euclidean_Space 2026-06*)
lemma closest_point_affine_orthogonal:
  fixes S :: "('a::euclidean_space) set"
  assumes "affine S" "S \<noteq> {}" "x \<in> S"
  shows "orthogonal (x - closest_point S a) (a - closest_point S a)"
proof -
  have "closed S" using assms(1) affine_closed by blast
  have "closest_point S a \<in> S"
    using closest_point_in_set[OF \<open>closed S\<close> assms(2)] .
  have "\<And>y. y \<in> S \<Longrightarrow> dist a (closest_point S a) \<le> dist a y"
    using closest_point_le[OF \<open>closed S\<close>] by (simp add: dist_commute)
  then show ?thesis
    using any_closest_point_affine_orthogonal[OF assms(1) \<open>closest_point S a \<in> S\<close>] assms(3)
    by blast
qed

(*added to Convex_Euclidean_Space 2026-06*)
lemma closest_point_affine_orthogonal_eq:
  fixes S :: "('a::euclidean_space) set"
  assumes "affine S" "b \<in> S"
  shows "(closest_point S a = b) \<longleftrightarrow> (\<forall>x. x \<in> S \<longrightarrow> orthogonal (x - b) (a - b))"
proof (rule iffI)
  assume eq: "closest_point S a = b"
  show "\<forall>x. x \<in> S \<longrightarrow> orthogonal (x - b) (a - b)"
    using assms(1) closest_point_affine_orthogonal eq by blast
next
  assume orth: "\<forall>x. x \<in> S \<longrightarrow> orthogonal (x - b) (a - b)"
  have "\<forall>z\<in>S. dist a b \<le> dist a z"
    using orthogonal_any_closest_point[OF assms(2)] orth by blast
  then have "b = closest_point S a"
    by (simp add: affine_closed affine_imp_convex assms closest_point_unique)
  then show "closest_point S a = b" by simp
qed


(*added to Derivative 2026-05*)
corollary vector_differentiable:
  "f differentiable net \<longleftrightarrow> (\<exists>f'. (f has_vector_derivative f') net)"
  using differentiableI_vector vector_derivative_works by blast

(*added to Limits 2026-05*)
lemma Zfun_cong: "eventually (\<lambda>x. f x = g x) F \<Longrightarrow> Zfun f F = Zfun g F"
  by (smt (verit) Zfun_ssubst eventually_mono)

(*added to Deriv 2026-05*)
lemma has_vector_derivative_within_1D:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  shows "(f has_vector_derivative f') (at x within S) \<longleftrightarrow>
         ((\<lambda>y. (f y - f x) /\<^sub>R (y - x)) \<longlongrightarrow> f') (at x within S)"
proof -
  have ev_eq: "\<forall>\<^sub>F y in at x within S. (f y - f x) /\<^sub>R (y - x) - f' = (f y - f x - (y - x) *\<^sub>R f') /\<^sub>R (y - x)"
    unfolding eventually_at_filter by (simp add: scaleR_diff_right scaleR_scaleR)
  show ?thesis
  proof
    assume "(f has_vector_derivative f') (at x within S)"
    then have "Zfun (\<lambda>y. (f y - f x - (y - x) *\<^sub>R f') /\<^sub>R \<bar>y - x\<bar>) (at x within S)"
      unfolding has_vector_derivative_def has_derivative_at_within tendsto_Zfun_iff by auto
    then have "Zfun (\<lambda>y. norm ((f y - f x - (y - x) *\<^sub>R f') /\<^sub>R \<bar>y - x\<bar>)) (at x within S)"
      using Zfun_norm_iff by fastforce
    then show "((\<lambda>y. (f y - f x) /\<^sub>R (y - x)) \<longlongrightarrow> f') (at x within S)"
      using Zfun_norm_iff Zfun_ssubst ev_eq tendsto_Zfun_iff by fastforce
  next
    assume R: "((\<lambda>y. (f y - f x) /\<^sub>R (y - x)) \<longlongrightarrow> f') (at x within S)"
    have "Zfun (\<lambda>y. (f y - f x) /\<^sub>R (y - x) - f') (at x within S)"
      using R by (simp add: tendsto_Zfun_iff)
    then have "Zfun (\<lambda>y. (f y - f x - (y - x) *\<^sub>R f') /\<^sub>R (y - x)) (at x within S)"
      by (smt (verit, del_insts) Zfun_ssubst ev_eq eventually_mono)
    then have "Zfun (\<lambda>y. (f y - f x - (y - x) *\<^sub>R f') /\<^sub>R \<bar>y - x\<bar>) (at x within S)"
      using Zfun_norm_iff by (fastforce simp add: Zfun_le)
    then show "(f has_vector_derivative f') (at x within S)"
      unfolding has_vector_derivative_def has_derivative_at_within tendsto_Zfun_iff
      using bounded_linear_scaleR_left by auto
  qed
qed

(*added to Infinite_Sum 2026-05*)
lemma convergent_eq_Cauchy_within:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::complete_space"
  shows "(\<exists>l. (f \<longlongrightarrow> l) (at a within S)) \<longleftrightarrow>
         (\<forall>e>0. \<exists>d>0. \<forall>x\<in>S. \<forall>y\<in>S.
            x \<noteq> a \<and> dist x a < d \<and> y \<noteq> a \<and> dist y a < d \<longrightarrow> dist (f x) (f y) < e)"
proof -
  have "(\<exists>l. (f \<longlongrightarrow> l) (at a within S)) \<longleftrightarrow> convergent_filter (filtermap f (at a within S))"
    unfolding filterlim_def convergent_filter_iff by auto
  also have "\<dots> \<longleftrightarrow> (\<forall>e>0. \<exists>P. eventually P (at a within S) \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist (f x) (f y) < e))"
    by (simp add: cauchy_filter_metric_filtermap convergent_filter_iff_cauchy)
  also have "\<dots> \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. \<forall>x\<in>S. \<forall>x'\<in>S.
      x \<noteq> a \<and> dist x a < d \<and> x' \<noteq> a \<and> dist x' a < d \<longrightarrow> dist (f x) (f x') < e)"
    (is "?L \<longleftrightarrow> ?R")
  proof
    assume ?L
    show ?R
    proof (intro allI impI)
      fix e :: real assume "e > 0"
      with \<open>?L\<close> obtain P where ev: "eventually P (at a within S)"
        and P: "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> dist (f x) (f y) < e" by auto
      then show "\<exists>d>0. \<forall>x\<in>S. \<forall>x'\<in>S. x \<noteq> a \<and> dist x a < d \<and> x' \<noteq> a \<and> dist x' a < d \<longrightarrow> dist (f x) (f x') < e"
        by (metis eventually_at)
    qed
  next
    assume ?R
    show ?L
    proof (intro allI impI)
      fix e :: real assume "e > 0"
      with \<open>?R\<close> obtain d where "d > 0"
        and d: "\<And>x x'. x \<in> S \<Longrightarrow> x' \<in> S \<Longrightarrow> x \<noteq> a \<Longrightarrow> dist x a < d \<Longrightarrow> x' \<noteq> a \<Longrightarrow> dist x' a < d \<Longrightarrow> dist (f x) (f x') < e"
        by auto
      have "\<forall>\<^sub>F x in at a within S. x \<in> S \<and> x \<noteq> a \<and> dist x a < d"
        unfolding eventually_at using \<open>d > 0\<close> by auto
      with d show "\<exists>P. eventually P (at a within S) \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist (f x) (f y) < e)"
        by blast
    qed
  qed
  finally show ?thesis .
qed

(*All added to Absolute_Continuity 2026-05*)
declare absolutely_continuous_on_const [continuous_intros] 
declare absolutely_continuous_on_neg [continuous_intros] 
declare absolutely_continuous_on_add [continuous_intros] 
declare absolutely_continuous_on_sub [continuous_intros]
declare absolutely_continuous_on_mul [continuous_intros]
declare absolutely_continuous_on_cmul [continuous_intros]

(*All added to Absolute_Continuity 2026-05*)
lemma absolutely_continuous_on_real_mult [continuous_intros]:
  fixes f :: \<open>real \<Rightarrow> real\<close> and g :: \<open>real \<Rightarrow> real\<close>
  assumes \<open>absolutely_continuous_on S f\<close> \<open>absolutely_continuous_on S g\<close> \<open>is_interval S\<close> \<open>bounded S\<close> 
  shows \<open>absolutely_continuous_on S (\<lambda>x. f x * g x)\<close>
  using absolutely_continuous_on_mul assms by fastforce

(*already in The forthcoming version*)
lemma integral_change_of_variables_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes "linear g"
      and "f absolutely_integrable_on (g ` S) \<or> (f \<circ> g) absolutely_integrable_on S"
    shows "integral (g ` S) f = \<bar>eucl.det g\<bar> *\<^sub>R integral S (f \<circ> g)"
  sorry (*PROVED ELSEWHERE; ASSUMED HERE*)

(*added to bounded_variation 2026-05*)
lemma has_bounded_variation_countable_discontinuities:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "has_bounded_variation_on f {a..b}"
  shows "countable {x \<in> {a..b}. \<not> isCont f x}"
proof -
  define V where "V \<equiv> \<lambda>x. vector_variation {a..x} f"
  have "\<And>x y. \<lbrakk>a \<le> x; y \<le> b; x \<le> y\<rbrakk>
           \<Longrightarrow> vector_variation {a..x} f \<le> vector_variation {a..y} f"
    by (metis assms atLeastatMost_subset_iff order.trans eq_refl
        has_bounded_variation_on_combine vector_variation_monotone)
  then have V_mono: "mono_on {a..b} V"
    by (auto simp: V_def monotone_on_def)
  have discont_within: "countable {x \<in> {a..b}. \<not> continuous (at x within {a..b}) f}"
    using vector_variation_continuous[OF assms] mono_on_ctble_discont[OF V_mono] unfolding V_def
    by (metis (mono_tags, lifting) Collect_cong)
  have "{x \<in> {a..b}. \<not> isCont f x} \<subseteq> {x \<in> {a..b}. \<not> continuous (at x within {a..b}) f} \<union> {a, b}"
    by (auto simp: at_within_Icc_at)
  then show ?thesis
    using countable_subset discont_within by (meson countable_Un countable_insert countable_empty)
qed

(*added to bounded_variation 2026-05*)
lemma vector_variation_isometric:
  fixes f g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "\<And>x y. dist (f x) (f y) = dist (g x) (g y)"
  shows "vector_variation S f = vector_variation S g"
proof -
  have "\<And>k. norm (f (\<Squnion> k) - f (\<Sqinter> k)) = norm (g (\<Squnion> k) - g (\<Sqinter> k))"
    using assms by (simp add: dist_norm)
  then show ?thesis
    unfolding vector_variation_def set_variation_def by (simp cong: sum.cong)
qed

(*added to bounded_variation 2026-05*)
lemma vector_variation_isometric_compose:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a" and g :: "real \<Rightarrow> 'a"
  assumes "\<And>x y. dist (f x) (f y) = dist x y"
  shows "vector_variation S (f \<circ> g) = vector_variation S g"
  by (rule vector_variation_isometric) (metis assms comp_apply)

(*added to bounded_variation 2026-05*)
lemma has_bounded_variation_on_translation:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  shows "has_bounded_variation_on (\<lambda>x. a + f x) S \<longleftrightarrow> has_bounded_variation_on f S"
  unfolding has_bounded_variation_on_def by simp

(*added to bounded_variation 2026-05*)
lemma vector_variation_translation:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  shows "vector_variation S (\<lambda>x. a + f x) = vector_variation S f"
  unfolding vector_variation_def set_variation_def by simp

(*added to bounded_variation 2026-05*)
lemma has_bounded_variation_on_componentwise:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  shows "has_bounded_variation_on f S \<longleftrightarrow> (\<forall>i\<in>Basis. has_bounded_variation_on (\<lambda>x. f x \<bullet> i) S)"
proof
  assume "has_bounded_variation_on f S"
  then show "\<forall>i\<in>Basis. has_bounded_variation_on (\<lambda>x. f x \<bullet> i) S"
    using has_bounded_variation_on_inner_left by blast
next
  assume comp: "\<forall>i\<in>Basis. has_bounded_variation_on (\<lambda>x. f x \<bullet> i) S"
  show "has_bounded_variation_on f S"
    unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def
  proof (intro exI allI impI)
    fix d T assume "d division_of T \<and> T \<subseteq> S"
    then have dT: "d division_of T" "T \<subseteq> S" by auto
    have "(\<Sum>k\<in>d. norm (f (\<Squnion> k) - f (\<Sqinter> k)))
        \<le> (\<Sum>k\<in>d. \<Sum>b\<in>Basis. \<bar>(f (\<Squnion> k) - f (\<Sqinter> k)) \<bullet> b\<bar>)"
      by (rule sum_mono) (rule norm_le_l1)
    also have "\<dots> = (\<Sum>b\<in>Basis. \<Sum>k\<in>d. \<bar>f (\<Squnion> k) \<bullet> b - f (\<Sqinter> k) \<bullet> b\<bar>)"
      by (subst sum.swap) (auto simp: inner_diff_left)
    also have "\<dots> \<le> (\<Sum>b\<in>Basis. vector_variation S (\<lambda>x. f x \<bullet> b))"
    proof (rule sum_mono)
      fix b :: 'a assume "b \<in> Basis"
      with comp have bv: "has_bounded_variation_on (\<lambda>x. f x \<bullet> b) S" by auto
      have "(\<Sum>k\<in>d. \<bar>f (\<Squnion> k) \<bullet> b - f (\<Sqinter> k) \<bullet> b\<bar>)
          = (\<Sum>k\<in>d. norm (f (\<Squnion> k) \<bullet> b - f (\<Sqinter> k) \<bullet> b))"
        by (simp add: real_norm_def)
      also have "\<dots> \<le> vector_variation S (\<lambda>x. f x \<bullet> b)"
        using has_bounded_variation_works(1)[OF bv dT(1) dT(2)]
        unfolding vector_variation_def by simp
      finally show "(\<Sum>k\<in>d. \<bar>f (\<Squnion> k) \<bullet> b - f (\<Sqinter> k) \<bullet> b\<bar>)
          \<le> vector_variation S (\<lambda>x. f x \<bullet> b)" .
    qed
    finally show "(\<Sum>k\<in>d. norm (f (\<Squnion> k) - f (\<Sqinter> k)))
        \<le> (\<Sum>b\<in>Basis. vector_variation S (\<lambda>x. f x \<bullet> b))" .
  qed
qed

(*added to Homotopy 2026-05*)
lemma locally_compact_diff_finite:
  fixes S :: "'a :: t1_space set"
  assumes "locally compact S" "finite T"
  shows "locally compact (S - T)"
  using assms(2,1)
proof (induction T arbitrary: S)
  case empty
  then show ?case 
    by auto
next
  case (insert x T)
  then have "locally compact (S - {x})"
    using locally_compact_delete by blast
  then show ?case
    by (metis Diff_insert2 local.insert(3))
qed

(*added to Homotopy 2026-05*)
lemma interval_contains_compact_neighbourhood:
  fixes S :: "'a::euclidean_space set"
  assumes "is_interval S" "x \<in> S"
  shows "\<exists>a b d. 0 < d \<and> x \<in> cbox a b \<and> cbox a b \<subseteq> S \<and> ball x d \<inter> S \<subseteq> cbox a b"
proof -
  have claim_lo: "\<And>i. i \<in> Basis \<Longrightarrow>
    \<exists>a. (\<exists>y\<in>S. y \<bullet> i = a) \<and> (a < x \<bullet> i \<or> a = x \<bullet> i \<and> (\<forall>y\<in>S. a \<le> y \<bullet> i))"
    by (metis \<open>x \<in> S\<close> leI)
  then obtain lo where lo: "\<And>i. i \<in> Basis \<Longrightarrow>
    (\<exists>y\<in>S. y \<bullet> i = lo i) \<and> (lo i < x \<bullet> i \<or> lo i = x \<bullet> i \<and> (\<forall>y\<in>S. lo i \<le> y \<bullet> i))"
    by metis
  have claim_hi: "\<And>i. i \<in> Basis \<Longrightarrow>
    \<exists>b. (\<exists>y\<in>S. y \<bullet> i = b) \<and> (x \<bullet> i < b \<or> b = x \<bullet> i \<and> (\<forall>y\<in>S. y \<bullet> i \<le> b))"
    by (metis \<open>x \<in> S\<close> leI)
  then obtain hi where hi: "\<And>i. i \<in> Basis \<Longrightarrow>
    (\<exists>y\<in>S. y \<bullet> i = hi i) \<and> (hi i > x \<bullet> i \<or> hi i = x \<bullet> i \<and> (\<forall>y\<in>S. y \<bullet> i \<le> hi i))"
    by metis
  define a where "a = (\<Sum>i\<in>Basis. lo i *\<^sub>R i)"
  define b where "b = (\<Sum>i\<in>Basis. hi i *\<^sub>R i)"

  define dl where "dl = Min ((\<lambda>i. if a \<bullet> i < x \<bullet> i then x \<bullet> i - a \<bullet> i else 1) ` Basis)"
  define dh where "dh = Min ((\<lambda>i. if x \<bullet> i < b \<bullet> i then b \<bullet> i - x \<bullet> i else 1) ` Basis)"
  define d where "d = min dl dh"
  have dl_pos: "0 < dl"
    unfolding dl_def using  obtains_MIN [OF finite_Basis nonempty_Basis]
    by (smt (verit) diff_gt_0_iff_gt zero_less_one)
  have dh_pos: "0 < dh"
    unfolding dh_def using  obtains_MIN [OF finite_Basis nonempty_Basis]
    by (smt (verit) diff_gt_0_iff_gt zero_less_one)
  have d_pos: "0 < d"
    unfolding d_def using dl_pos dh_pos by auto

  have x_in_box: "x \<in> cbox a b"
    unfolding mem_box
    using a_def b_def hi lo by fastforce
  have a_in_s: "a \<in> S"
    using lo a_def image_iff
    by (intro mem_box_componentwiseI [OF \<open>is_interval S\<close>]) (fastforce simp: a_def image_iff)
  have b_in_s: "b \<in> S"
    using hi a_def image_iff
    by (intro mem_box_componentwiseI [OF \<open>is_interval S\<close>]) (fastforce simp: b_def image_iff)
  have box_sub: "cbox a b \<subseteq> S"
    using interval_subset_is_interval[OF assms(1)] a_in_s b_in_s x_in_box
    by (auto simp: mem_box)

  have ball_sub: "ball x d \<inter> S \<subseteq> cbox a b"
  proof (intro subsetI)
    fix y assume "y \<in> ball x d \<inter> S"
    then have y_in: "y \<in> S" and y_ball: "dist x y < d"
      by auto
    have dist_coord: "\<bar>x \<bullet> i - y \<bullet> i\<bar> < d" if "i \<in> Basis" for i
      using Euclidean_dist_upper[OF that, of x y] y_ball
      by (auto simp: dist_real_def)
    have lo_bound: "a \<bullet> i \<le> y \<bullet> i" if "i \<in> Basis" for i
    proof (cases "a \<bullet> i < x \<bullet> i")
      case True
      then have "d \<le> x \<bullet> i - a \<bullet> i"
        unfolding d_def dl_def using that finite_Basis
        by (simp add: min_le_iff_disj)
      then show ?thesis using dist_coord[OF that] by linarith
    next
      case False
      then show ?thesis using lo that y_in by (force simp: a_def)
    qed
    have hi_bound: "y \<bullet> i \<le> b \<bullet> i" if "i \<in> Basis" for i
    proof (cases "x \<bullet> i < b \<bullet> i")
      case True
      then have "d \<le> b \<bullet> i - x \<bullet> i"
        unfolding d_def dh_def using that finite_Basis
        by (simp add: min_le_iff_disj)
      then show ?thesis using dist_coord[OF that] by linarith
    next
      case False then show ?thesis using hi that y_in by (force simp: b_def)
    qed
    show "y \<in> cbox a b"
      unfolding mem_box using lo_bound hi_bound by auto
  qed
  show ?thesis
    using d_pos x_in_box box_sub ball_sub
    by (intro exI[of _ a] exI[of _ b] exI[of _ d]) auto
qed

(*added to Homotopy 2026-05*)
lemma is_interval_locally_compact_interval:
  fixes S :: "'a::euclidean_space set"
  assumes "is_interval S"
  shows "locally (\<lambda>k. \<exists>a b. k = cbox a b) S"
proof (clarsimp simp: locally_def)
  fix W x
  assume ow: "openin (top_of_set S) W" and xw: "x \<in> W"
  then obtain t where "open t" and wst: "W = S \<inter> t"
    by (auto simp: openin_open)
  then have "x \<in> S" "x \<in> t" using xw by auto
  obtain a b e where "0 < e" "x \<in> cbox a b" "cbox a b \<subseteq> S" and ab: "ball x e \<inter> S \<subseteq> cbox a b"
    using interval_contains_compact_neighbourhood[OF assms \<open>x \<in> S\<close>] by blast
  obtain c d where "x \<in> box c d" "cbox c d \<subseteq> t" "\<forall>i\<in>Basis. c \<bullet> i < d \<bullet> i"
    using open_contains_cbox[OF \<open>open t\<close> \<open>x \<in> t\<close>] by metis
  \<comment> \<open>The three witnesses\<close>
  define U where "U = S \<inter> ball x e \<inter> box c d"
  define V where "V = cbox a b \<inter> cbox c d"
  have U_open: "openin (top_of_set S) U"
    unfolding U_def Int_assoc
    by (intro openin_open_Int open_Int open_ball open_box)
  have V_cbox: "\<exists>a' b'. V = cbox a' b'"
    unfolding V_def Int_interval by blast
  have xU: "x \<in> U"
    unfolding U_def using \<open>x \<in> S\<close> \<open>0 < e\<close> \<open>x \<in> box c d\<close> by auto
  have UV: "U \<subseteq> V"
    using ab box_subset_cbox by (force simp: U_def V_def)
  have Vw: "V \<subseteq> W"
    using \<open>cbox a b \<subseteq> S\<close> \<open>cbox c d \<subseteq> t\<close> wst by (force simp: V_def)
  show "\<exists>U. openin (top_of_set S) U \<and>
               (\<exists>V. (\<exists>a b. V = cbox a b) \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W)"
    using U_open V_cbox xU UV Vw by blast
qed

(*added to Homotopy 2026-05*)
lemma is_interval_imp_locally_compact:
  fixes S :: "real set"
  assumes "is_interval S"
  shows "locally compact S"
proof -
  have "closed (closure S)" by simp
  then have lc: "locally compact (closure S)"
    by (rule closed_imp_locally_compact)
  have "S = closure S - (frontier S - S)"
  proof
    show "S \<subseteq> closure S - (frontier S - S)"
      using closure_subset by auto
    show "closure S - (frontier S - S) \<subseteq> S"
      unfolding frontier_def
      using interior_subset by fastforce
  qed
  moreover have "finite (frontier S - S)"
    using finite_frontier_interval_real[OF assms] by (auto intro: finite_subset)
  ultimately show ?thesis
    using locally_compact_diff_finite[OF lc] by metis
qed

(*added to Lebesgue_diff_thm 2026-06*)
lemma Lebesgue_diff_aux1:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and a b :: real
  assumes "has_bounded_variation_on f {a..b}"
  shows "\<exists>t. negligible t \<and>
             (\<forall>x \<in> {a..b} - t.
                \<exists>B>0. eventually (\<lambda>y. norm (f y - f x) \<le> B * norm (y - x)) (at x))"
proof -
  define t where "t = {x \<in> {a<..<b}. isCont f x \<and>
    \<not> (\<exists>B>0. eventually (\<lambda>y. norm (f y - f x) \<le> B * norm (y - x)) (at x))}"
    \<comment> \<open>the "bad set": points in the open interval where f is continuous 
        but fails to have a local Lipschitz bound.\<close>
  obtain B where B: "\<And>d T. \<lbrakk>d division_of T; T \<subseteq> {a..b}\<rbrakk> \<Longrightarrow>
      (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B"
    using assms unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def
    by blast
  obtain T where tn: "negligible T" and
    tc: "\<And>x. x \<in> {a..b} - T \<Longrightarrow> isCont f x \<Longrightarrow>
       \<exists>B>0. eventually (\<lambda>y. norm (f y - f x) \<le> B * norm (y - x)) (at x)"
  proof 
    show "negligible ({a, b} \<union> t)"
    proof (rule negligible_Un)
      show "negligible t"
        unfolding negligible_outer_le
      proof (intro strip)
        fix \<epsilon> :: real
        assume "0 < \<epsilon>"
        define M where "M = 3 * (\<bar>B\<bar> + 1) / \<epsilon>"
        have "0 < M"
          unfolding M_def using \<open>0 < \<epsilon>\<close> by (auto intro: divide_pos_pos)
        have interval_witness: 
          "\<exists>u v. u \<in> {a..b} \<and> v \<in> {a..b} \<and> x \<in> {u<..<v} \<and>
                  M * \<bar>v - u\<bar> \<le> norm (f u - f v)" if "x \<in> t" for x
        proof -
          from that have xab: "x \<in> {a<..<b}" and xcont: "isCont f x"
            and xnlip: "\<not> (\<exists>B>0. eventually (\<lambda>y. norm (f y - f x) \<le> B * norm (y - x)) (at x))"
            unfolding t_def by auto
          from xab obtain d where "d > 0" and dsub: "\<And>x'. \<bar>x' - x\<bar> < d \<Longrightarrow> x' \<in> {a<..<b}"
            by (meson open_greaterThanLessThan open_real)
          have False if "d > 0" 
            and hd: "\<And>y. 0 < dist y x \<Longrightarrow> dist y x < d \<Longrightarrow> norm (f y - f x) \<le> (3*M) * norm (y-x)" for d
          proof -
            have "eventually (\<lambda>y. norm (f y - f x) \<le> (3 * M) * norm (y - x)) (at x)"
              unfolding eventually_at using \<open>d > 0\<close> hd by auto
            then show False using xnlip \<open>M>0\<close> by auto
          qed
          then obtain y where yx: "0 < dist y x" "dist y x < d"
            and ylip: "(3 * M) * norm (y - x) < norm (f y - f x)"
            by (meson \<open>0 < d\<close> not_le)
          have yab: "y \<in> {a<..<b}"
            using dsub yx(2) by (auto simp: dist_real_def)
          have xab': "x \<in> {a..b}" and yab': "y \<in> {a..b}"
            using xab yab by auto
          \<comment> \<open>Use continuity to find a point z on the opposite side of x from y,
              then the pair (min y z, max y z) witnesses the claim.\<close>
          define \<delta> where "\<delta> = \<bar>y - x\<bar>"
          have "\<delta> > 0" unfolding \<delta>_def using yx by (auto simp: dist_real_def)
          have M\<delta>: "M * \<delta> > 0" using \<open>0 < M\<close> \<open>\<delta> > 0\<close> by auto
          have ylip': "3 * M * \<delta> < norm (f y - f x)"
            using ylip unfolding \<delta>_def by (simp add: real_norm_def)
          from xcont have "(f \<longlongrightarrow> f x) (at x)" by (simp add: isCont_def)
          from tendstoD[OF this M\<delta>]
          obtain d' where "d' > 0" and
            hd': "\<And>z. z \<noteq> x \<Longrightarrow> dist z x < d' \<Longrightarrow> dist (f z) (f x) < M * \<delta>"
            unfolding eventually_at by auto
          \<comment> \<open>Pick z on the opposite side of x from y, close to x\<close>
          define z where "z = (if x < y then x - min \<delta> (min d d') / 2
                                        else x + min \<delta> (min d d') / 2)"
          have zx: "z \<noteq> x"
            unfolding z_def using \<open>d > 0\<close> \<open>d' > 0\<close> \<open>\<delta> > 0\<close> by (auto simp: min_def)
          have dist_zx: "dist z x < min \<delta> (min d d')"
            unfolding z_def \<delta>_def dist_real_def
            using yx \<open>d > 0\<close> \<open>d' > 0\<close>
            by (auto simp: dist_real_def min_def split: if_splits)
          have xbetween: "x \<in> {min y z <..< max y z}"
            unfolding z_def using yx \<open>d > 0\<close> \<open>d' > 0\<close> \<open>\<delta> > 0\<close>
            by (simp add: \<delta>_def dist_real_def min_def max_def field_simps split: if_split_asm)
          have zab: "z \<in> {a<..<b}"
            using dist_real_def dist_zx dsub by force
          have zab': "z \<in> {a..b}" using zab by auto
          have fz_bound: "norm (f z - f x) < M * \<delta>"
            by (metis dist_norm dist_zx hd' min_less_iff_conj zx)
          have gap_bound: "\<bar>max y z - min y z\<bar> < 2 * \<delta>"
            by (smt (verit) \<delta>_def dist_real_def dist_zx)
          have key: "norm (f z - f y) > 2 * M * \<delta>"
            using norm_triangle_ineq[of "f y - f z" "f z - f x"] ylip' fz_bound
            by (simp add: norm_minus_commute)
          have "M * \<bar>max y z - min y z\<bar> < norm (f (min y z) - f (max y z))"
          proof -
            have "M * \<bar>max y z - min y z\<bar> < M * (2 * \<delta>)"
              using gap_bound \<open>0 < M\<close> by auto
            also have "\<dots> < norm (f (min y z) - f (max y z))"
              using key by (simp add: min_def norm_minus_commute)
            finally show ?thesis .
          qed
          then show ?thesis
            using zab' yab' xbetween
            by (intro exI[of _ "min y z"] exI[of _ "max y z"]) auto
        qed
        then obtain u v where uv: "\<And>x. x \<in> t \<Longrightarrow> u x \<in> {a..b} \<and> v x \<in> {a..b} \<and> x \<in> {u x <..< v x}
                             \<and> M * \<bar>v x - u x\<bar> \<le> norm (f (u x) - f (v x))"
          by metis
        let ?UVT = "(\<lambda>x. box (u x) (v x)) ` t"
        obtain \<F> where "\<F> \<subseteq> ?UVT" "countable \<F>" "\<Union>\<F> = \<Union>?UVT"
          by (smt (verit, best) Lindelof imageE open_box)
        then obtain c where "countable c" and "c \<subseteq> t" 
          and c: "\<Union>((\<lambda>x. box (u x) (v x)) ` c) = \<Union> ?UVT"
          by (metis (lifting) countable_subset_image)
        show "\<exists>T. t \<subseteq> T \<and> T \<in> lmeasurable \<and> Sigma_Algebra.measure lebesgue T \<le> \<epsilon>"
        proof (rule ccontr)
          assume non: "\<nexists>T. t \<subseteq> T \<and> T \<in> lmeasurable \<and> Sigma_Algebra.measure lebesgue T \<le> \<epsilon>"
          let ?\<C> =  "(\<lambda>x. cbox (u x) (v x)) ` c"
          have cnt: "countable ?\<C>"
            using \<open>countable c\<close> by auto
          have meas: "\<And>D. D \<in> ?\<C> \<Longrightarrow> D \<in> lmeasurable"
            by (auto intro: lmeasurable_cbox)
          have tsub: "t \<subseteq> \<Union>?\<C>"
          proof
            fix x assume "x \<in> t"
            then obtain z where "z \<in> c" "x \<in> box (u z) (v z)"
              using c uv by fastforce
            then show "x \<in> \<Union>?\<C>"
              using box_subset_cbox by blast
          qed
          have "\<exists>P. finite P \<and> P \<subseteq> ?\<C> \<and> \<epsilon> < measure lebesgue (\<Union>P)"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            then have bound: "\<And>\<E>. \<E> \<subseteq> ?\<C> \<Longrightarrow> finite \<E> \<Longrightarrow> measure lebesgue (\<Union>\<E>) \<le> \<epsilon>"
              by (meson linorder_not_less)
            then have "\<exists>T. t \<subseteq> T \<and> T \<in> lmeasurable \<and> measure lebesgue T \<le> \<epsilon>"
              using tsub
              by (metis (no_types, lifting) cnt fmeasurable_Union_bound meas measure_Union_bound)
            then show False using non by auto
          qed
          then obtain p where "finite p" "p \<subseteq> c"
            and p: "\<epsilon> < measure lebesgue (Union ((\<lambda>x. cbox (u x) (v x)) ` p))"
            by (metis (no_types, lifting) finite_subset_image)
          show False
          proof -
            define \<D> where "\<D> = (\<lambda>x. cbox (u x) (v x)) ` p"
            have fin\<D>: "finite \<D>" unfolding \<D>_def using \<open>finite p\<close> by auto
            have cube: "\<exists>k a' b'. D = cbox a' b' \<and> (\<forall>i\<in>Basis. b' \<bullet> i - a' \<bullet> i = k)"
              if "D \<in> \<D>" for D
            proof -
              from that obtain x where "x \<in> p" "D = cbox (u x) (v x)"
                unfolding \<D>_def by auto
              then show ?thesis
                by (intro exI[of _ "v x - u x"] exI[of _ "u x"] exI[of _ "v x"])
                   (auto simp: Basis_real_def inner_real_def)
            qed
            obtain \<C> where "\<C> \<subseteq> \<D>" "disjoint \<C>"
              and \<C>meas: "measure lebesgue (\<Union>\<D>) / 3 ^ DIM(real) \<le> measure lebesgue (\<Union>\<C>)"
              using Austin_Lemma[OF fin\<D> cube] by auto
            have "\<epsilon> / 3 < measure lebesgue (\<Union>\<C>)"
              using p \<C>meas \<D>_def by force
            moreover obtain p' where "p' \<subseteq> p" and \<C>_eq: "\<C> = (\<lambda>x. cbox (u x) (v x)) ` p'"
              and inj: "inj_on (\<lambda>x. cbox (u x) (v x)) p'"
            proof -
              let ?f = "\<lambda>x. cbox (u x) (v x)"
              have Csub_im: "\<C> \<subseteq> ?f ` p"
                using \<open>\<C> \<subseteq> \<D>\<close> unfolding \<D>_def by auto
              define p' where "p' = inv_into p ?f ` \<C>"
              have p'_sub: "p' \<subseteq> p"
                unfolding p'_def using Csub_im by (auto intro: inv_into_into)
              have C_eq: "\<C> = ?f ` p'"
                by (metis Csub_im image_inv_into_cancel p'_def)
              have "inj_on ?f p'"
              proof (rule inj_onI)
                fix x y assume "x \<in> p'" "y \<in> p'" and eq: "?f x = ?f y"
                from \<open>x \<in> p'\<close> obtain K1 where "K1 \<in> \<C>" and K1: "x = inv_into p ?f K1"
                  unfolding p'_def by auto
                from \<open>y \<in> p'\<close> obtain K2 where "K2 \<in> \<C>" and K2: "y = inv_into p ?f K2"
                  unfolding p'_def by auto
                have "K1 = ?f (inv_into p ?f K1)"
                  using f_inv_into_f[of K1 ?f p] \<open>K1 \<in> \<C>\<close> Csub_im by auto
                also have "\<dots> = ?f (inv_into p ?f K2)" 
                  using eq K1 K2 by fastforce
                also have "\<dots> = K2"
                  using f_inv_into_f[of K2 ?f p] \<open>K2 \<in> \<C>\<close> Csub_im by auto
                finally have "K1 = K2" .
                then show "x = y" using K1 K2 by simp
              qed
              then show ?thesis using that p'_sub C_eq by blast
            qed
            have finp': "finite p'" using \<open>p' \<subseteq> p\<close> \<open>finite p\<close> finite_subset by blast
            have p'sub: "p' \<subseteq> t" using \<open>p' \<subseteq> p\<close> \<open>p \<subseteq> c\<close> \<open>c \<subseteq> t\<close> by auto
            have ux_less_vx: "u x < v x" if "x \<in> p'" for x
              using uv[of x] p'sub that by auto
            have "measure lebesgue (\<Union>\<C>) \<le> (\<Sum>x\<in>p'. v x - u x)"
            proof -
              have "measure lebesgue (\<Union>\<C>) \<le> (\<Sum>D\<in>\<C>. measure lebesgue D)"
                by (metis (no_types, lifting) \<C>_eq \<open>\<C> \<subseteq> \<D>\<close> cbox_borel fin\<D> finite_subset 
                    imageE measure_Union_le sets_completionI_sets sets_lborel)
              also have "\<dots> \<le> (\<Sum>x\<in>p'. measure lebesgue (cbox (u x) (v x)))"
                by (metis (no_types, lifting) \<C>_eq dual_order.eq_iff inj sum.reindex_cong)
              also have "\<dots> = (\<Sum>x\<in>p'. v x - u x)"
                by (simp add: measure_lborel_cbox_eq content_real less_imp_le ux_less_vx)
              finally show ?thesis .
            qed
            also have "\<dots> \<le> (\<Sum>x\<in>p'. norm (f (u x) - f (v x))) / M"
            proof -
              have "(\<Sum>x\<in>p'. v x - u x) \<le> (\<Sum>x\<in>p'. norm (f (u x) - f (v x)) / M)"
              proof (intro sum_mono)
                fix x assume "x \<in> p'"
                then have "M * (v x - u x) \<le> norm (f (u x) - f (v x))"
                  using uv p'sub ux_less_vx by fastforce
                then show "v x - u x \<le> norm (f (u x) - f (v x)) / M"
                  using \<open>0 < M\<close> by (simp add: field_simps)
              qed
              also have "\<dots> = (\<Sum>x\<in>p'. norm (f (u x) - f (v x))) / M"
                by (simp add: sum_divide_distrib)
              finally show ?thesis .
            qed
            also have "\<dots> \<le> B / M"
            proof -
              have div: "\<C> division_of \<Union>\<C>"
                unfolding division_of_def
              proof (intro conjI)
                show "finite \<C>"
                  using finp' unfolding \<C>_eq by auto
                show "\<forall>K\<in>\<C>. K \<subseteq> \<Union>\<C> \<and> K \<noteq> {} \<and> (\<exists>a b. K = cbox a b)"
                  unfolding \<C>_eq using p'sub uv by fastforce
                show "\<forall>K1\<in>\<C>. \<forall>K2\<in>\<C>. K1 \<noteq> K2 \<longrightarrow> interior K1 \<inter> interior K2 = {}"
                  by (metis \<open>disjoint \<C>\<close> disjointD interior_Int interior_empty)
              qed auto
              have Csub: "\<Union>\<C> \<subseteq> {a..b}"
                unfolding \<C>_eq using p'sub uv by fastforce
              have "(\<Sum>x\<in>p'. norm (f (u x) - f (v x)))
                    = (\<Sum>x\<in>p'. norm (f (Sup (cbox (u x) (v x))) - f (Inf (cbox (u x) (v x)))))"
                by (simp add: less_imp_le ux_less_vx norm_minus_commute)
              also have "\<dots> = (\<Sum>K\<in>\<C>. norm (f (Sup K) - f (Inf K)))"
                unfolding \<C>_eq using sum.reindex[OF inj, of "\<lambda>K. norm (f (Sup K) - f (Inf K))"]
                by (simp add: comp_def)
              also have "\<dots> \<le> B" using B[OF div Csub] .
              finally have "(\<Sum>x\<in>p'. norm (f (u x) - f (v x))) \<le> B" .
              then show ?thesis using \<open>0 < M\<close> by (simp add: divide_right_mono)
            qed
            also have "\<dots> < \<epsilon> / 3"
              unfolding M_def using \<open>0 < \<epsilon>\<close> by (simp add: abs_if field_simps)
            ultimately show False by linarith
          qed
        qed
      qed
    qed auto
  qed (auto simp: t_def)
  define D where "D = {x \<in> {a..b}. \<not> isCont f x}"
  have "countable D"
    unfolding D_def using has_bounded_variation_countable_discontinuities[OF assms] .
  hence "negligible (T \<union> D)"
    using tn negligible_Un countable_imp_negligible by blast
  then show ?thesis
    using D_def tc by blast
qed

(*added to Lebesgue_diff_thm 2026-06*)
lemma cover_T:
  fixes f :: "real \<Rightarrow> real" and a b k :: real
  assumes f: "has_bounded_variation_on f {a..b}" and "0 < k"
    and key_fn: "\<And>x. x \<in> T \<Longrightarrow> {cx x..dx x} \<in> D \<and> x \<in> {cx x<..<dx x} \<and>
                   ux x \<in> {cx x<..<dx x} \<and> vx x \<in> {cx x<..<dx x} \<and>
                   x \<in> {ux x<..<vx x} \<and>
                   (f (cx x) \<le> f (dx x) \<longrightarrow> f (vx x) - f (ux x) \<le> -k * (vx x - ux x)) \<and>
                   (f (dx x) < f (cx x) \<longrightarrow> k * (vx x - ux x) \<le> f (vx x) - f (ux x))"
    and D_div: "D division_of {a..b}"
    and D_sum: "vector_variation {a..b} f - k * e / 3 < (\<Sum>K\<in>D. norm (f (Sup K) - f (Inf K)))"
  obtains C where "T \<subseteq> C" "C \<in> lmeasurable" "measure lebesgue C \<le> e"
proof (rule ccontr)
  assume non: "\<not> ?thesis"
    \<comment> \<open>Apply Lindelöf to the family of open intervals\<close>
  have fin_D: "finite D"
    using D_div division_of_finite by blast
  let ?UVT = "(\<lambda>x. {ux x<..<vx x}) ` T"
  obtain \<F> where "\<F> \<subseteq> ?UVT" "countable \<F>" "\<Union>\<F> = \<Union>?UVT"
    by (smt (verit, best) Lindelof imageE open_greaterThanLessThan)
  then obtain c where "countable c" and "c \<subseteq> T"
    and c_union: "\<Union>((\<lambda>x. {ux x<..<vx x}) ` c) = \<Union>?UVT"
    by (metis (lifting) countable_subset_image)
  have "\<exists>p. finite p \<and> p \<subseteq> (\<lambda>x. {ux x..vx x}) ` c \<and> e < measure lebesgue (\<Union>p)"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have le_e: "\<And>p. p \<subseteq> (\<lambda>x. {ux x..vx x}) ` c \<Longrightarrow> finite p \<Longrightarrow> measure lebesgue (\<Union>p) \<le> e"
      by (meson linorder_not_less)
    have union_le: "measure lebesgue (\<Union>((\<lambda>x. {ux x..vx x}) ` c)) \<le> e"
      by (rule measure_Union_bound)
        (use \<open>countable c\<close> le_e lmeasurable_cbox in \<open>auto simp: cbox_interval\<close>)
    have "T \<subseteq> \<Union>((\<lambda>x. {ux x..vx x}) ` c)"
    proof
      fix x assume "x \<in> T"
      then have "x \<in> \<Union>((\<lambda>x. {ux x<..<vx x}) ` T)" using key_fn by auto
      then show "x \<in> \<Union>((\<lambda>x. {ux x..vx x}) ` c)" using c_union by force
    qed
    moreover have "\<Union>((\<lambda>x. {ux x..vx x}) ` c) \<in> lmeasurable"
      using \<open>countable c\<close> le_e by (intro fmeasurable_Union_bound[where B=e]) auto
    ultimately have *: "e < measure lebesgue (\<Union>((\<lambda>x. {ux x..vx x}) ` c))"
      using non that union_le by blast
    with union_le show False by linarith
  qed
  then obtain Q where "finite Q" "Q \<subseteq> (\<lambda>x. {ux x..vx x}) ` c"
    "e < measure lebesgue (\<Union>Q)" by auto
  from finite_subset_image[OF \<open>finite Q\<close> \<open>Q \<subseteq> (\<lambda>x. {ux x..vx x}) ` c\<close>]
  obtain p where "p \<subseteq> c" "finite p" "Q = (\<lambda>x. {ux x..vx x}) ` p" by auto
  then have fin_p: "finite p" and p_sub: "p \<subseteq> c"
    and p_meas: "e < measure lebesgue (\<Union>((\<lambda>x. {ux x..vx x}) ` p))"
    using \<open>e < measure lebesgue (\<Union>Q)\<close> by auto                                       
      \<comment> \<open>Apply Austin's lemma to the finite collection of intervals\<close>
  define \<D> where "\<D> = (\<lambda>x. {ux x..vx x}) ` p"
  have fin\<D>: "finite \<D>" unfolding \<D>_def using fin_p by auto
  have cube: "\<exists>k a b. D = cbox a b \<and> (\<forall>i\<in>Basis. b \<bullet> i - a \<bullet> i = k)" if "D \<in> \<D>" for D
    using \<D>_def that by auto
  obtain d where "d \<subseteq> \<D>" "disjoint d"
    and d_meas: "measure lebesgue (\<Union>\<D>) / 3 ^ DIM(real) \<le> measure lebesgue (\<Union>d)"
    using Austin_Lemma[OF fin\<D> cube] by auto
  have "\<exists>j. j \<in> D \<and> i \<subseteq> j" if "i \<in> d" for i    
  proof -
    from that \<open>d \<subseteq> \<D>\<close> obtain x where "x \<in> p" and x: "i = {ux x..vx x}"
      unfolding \<D>_def by auto
    then have "x \<in> T" using p_sub \<open>c \<subseteq> T\<close> by auto
    from key_fn[OF this] show ?thesis
      by (metis atLeastatMost_subset_iff greaterThanLessThan_iff less_eq_real_def x)
  qed
  then have d_decomp: "\<Union>d = (\<Union>j\<in>D. \<Union>{i \<in> d. i \<subseteq> j})"
    by blast
  let ?F = "(\<lambda>j. \<Union>{i \<in> d. i \<subseteq> j}) ` D"
  have fin_F: "finite ?F"
    using fin_D by auto
  have fin_d: "finite d" using finite_subset[OF \<open>d \<subseteq> \<D>\<close> fin\<D>] .
  have meas_F: "S \<in> sets lebesgue" if "S \<in> ?F" for S           
    using fin_d \<open>d \<subseteq> \<D>\<close> fmeasurableD[OF fmeasurable_cbox] that
    by (auto intro!: sets.finite_Union simp: \<D>_def cbox_interval)
  have "measure lebesgue (\<Union>d) = measure lebesgue (\<Union>?F)"
    using d_decomp by (simp add: image_UN)
  also have "\<dots> \<le> sum (measure lebesgue) ?F"
    using measure_Union_le[OF fin_F meas_F] .
  also have "\<dots> \<le> (\<Sum>j\<in>D. measure lebesgue (\<Union>{i \<in> d. i \<subseteq> j}))"
    using sum_image_le [unfolded o_def] fin_D measure_nonneg by blast
  also have "\<dots> < e / 3"
  proof -
    have per_elt: "measure lebesgue (\<Union>{i \<in> d. i \<subseteq> K}) * k \<le> vector_variation K f - norm (f (Sup K) - f (Inf K))"
      if "K \<in> D" for K
    proof -
      obtain l r where K_eq: "K = {l..r}" and "l \<le> r"
        using division_ofD[OF D_div] \<open>K \<in> D\<close> by (metis atLeastatMost_empty_iff2 box_real(2))
      have meas_i: "i \<in> sets lebesgue" if "i \<in> d" "i \<subseteq> {l..r}" for i
        using fmeasurableD[OF fmeasurable_cbox[of "ux x" "vx x"]]
        using \<D>_def \<open>d \<subseteq> \<D>\<close> that(1) by auto
      define d' where "d' = {i \<in> d. i \<subseteq> {l..r}}"
      have disj_d': "disjoint d'"
        using \<open>disjoint d\<close> d'_def pairwise_subset by force
      have d'_ne: "K \<noteq> {}" if "K \<in> d'" for K
      proof -
        from that obtain x where "x \<in> p" "K = {ux x..vx x}"
          using \<open>d \<subseteq> \<D>\<close> unfolding d'_def \<D>_def by auto
        then have "x \<in> T" using p_sub \<open>c \<subseteq> T\<close> by auto
        from key_fn[OF this]  show ?thesis using \<open>K = {ux x..vx x}\<close> by auto
      qed
      have fin_d': "finite d'" unfolding d'_def using fin_d by auto
      have d'_div: "d' division_of \<Union>d'"
        unfolding division_of_def
      proof (intro conjI ballI impI)
        fix K assume "K \<in> d'"
        then have "K \<in> \<D>" using \<open>d \<subseteq> \<D>\<close> d'_def by blast
        then show "\<exists>a b. K = cbox a b"
          unfolding \<D>_def by (auto simp: cbox_interval)
      next
        fix K1 K2 assume "K1 \<in> d'" "K2 \<in> d'" "K1 \<noteq> K2"
        then show "interior K1 \<inter> interior K2 = {}"
          using disj_d' by (metis disjointD interior_Int interior_empty)
      qed (use fin_d' d'_ne in auto)
      have d'_sub_lr: "\<Union>d' \<subseteq> {l..r}"
        unfolding d'_def by auto
      obtain d'' where d'_sub_d'': "d' \<subseteq> d''" and d''_div: "d'' division_of {l..r}"
        and "finite d''"
        by (metis box_real(2) d'_div d'_sub_lr division_of_finite partial_division_extend_interval)
      have "measure lebesgue (\<Union> d') \<le> (\<Sum>i\<in>d'. measure lebesgue i)"
        using meas_i d'_div by (intro measure_Union_le) (auto simp: d'_def)
      also have "\<dots> \<le> (vector_variation {l..r} f - \<bar>f r - f l\<bar>) / k"
      proof -
        define s where "s \<equiv> if f l \<le> f r then (1::real) else -1"
        have s_abs: "s * (f r - f l) = \<bar>f r - f l\<bar>"
          unfolding s_def by auto
        have bv_lr: "has_bounded_variation_on f {l..r}"
          by (metis D_div K_eq assms(1) cbox_division_memE has_bounded_variation_on_subset that)
        have sum_abs_le: "(\<Sum>i\<in>d''. \<bar>f (Sup i) - f (Inf i)\<bar>) \<le> vector_variation {l..r} f"
          using has_bounded_variation_works(1)[OF bv_lr d''_div order_refl]
          by (simp add: real_norm_def)
        have sum_telesc: "(\<Sum>i\<in>d''. f (Sup i) - f (Inf i)) = f r - f l"
          using division_telescope_eq[OF d''_div \<open>l \<le> r\<close>] .
        have elt_bound: "measure lebesgue i * k \<le> \<bar>f (Sup i) - f (Inf i)\<bar> - s * (f (Sup i) - f (Inf i))"
          if i_in_d': "i \<in> d'" for i
        proof -
          from i_in_d' obtain x where "x \<in> p" "i = {ux x..vx x}"
            using \<open>d \<subseteq> \<D>\<close> unfolding d'_def \<D>_def by auto
          have "x \<in> T" using \<open>x \<in> p\<close> p_sub \<open>c \<subseteq> T\<close> by auto
          have uv_lt: "ux x < vx x" using key_fn[OF \<open>x \<in> T\<close>] by auto
          have i_sub_lr: "{ux x..vx x} \<subseteq> {l..r}"
            using i_in_d' unfolding d'_def \<open>i = {ux x..vx x}\<close> by auto
          have "interior {l..r} \<inter> interior {cx x..dx x} \<noteq> {}"
            using key_fn[OF \<open>x \<in> T\<close>] i_sub_lr by auto
          then have "{cx x..dx x} = {l..r}"
            using D_div K_eq \<open>K \<in> D\<close> key_fn[OF \<open>x \<in> T\<close>] by blast
          then have "cx x = l" "dx x = r"
            using key_fn[OF \<open>x \<in> T\<close>] \<open>l \<le> r\<close> by (auto simp: Icc_eq_Icc)
          have meas_eq: "measure lebesgue i = vx x - ux x"
            unfolding \<open>i = {ux x..vx x}\<close>
            using uv_lt by (simp add: measure_lborel_cbox_eq content_real less_imp_le cbox_interval)
          have eq: "Sup i = vx x" "Inf i = ux x" unfolding \<open>i = {ux x..vx x}\<close>
            using uv_lt by (simp_all add: less_imp_le)
          show ?thesis
          proof (cases "f l \<le> f r")
            case True
            then have "f (vx x) - f (ux x) \<le> - k * (vx x - ux x)"
              using key_fn[OF \<open>x \<in> T\<close>] \<open>cx x = l\<close> \<open>dx x = r\<close> by auto
            with True uv_lt \<open>0 < k\<close>
            have fvu_neg: "f (vx x) - f (ux x) \<le> 0"
              by (smt (verit, ccfv_threshold) mult_neg_pos)
            then show ?thesis unfolding eq meas_eq s_def
              using \<open>f (vx x) - f (ux x) \<le> - k * (vx x - ux x)\<close> uv_lt \<open>0 < k\<close> True
              by (simp add: mult.commute)
          next
            case False
            then have "k * (vx x - ux x) \<le> f (vx x) - f (ux x)"
              using key_fn[OF \<open>x \<in> T\<close>] \<open>cx x = l\<close> \<open>dx x = r\<close> by auto
            with False uv_lt \<open>0 < k\<close>
            have fvu_pos: "f (vx x) - f (ux x) \<ge> 0"
              by (metis order.trans ge_iff_diff_ge_0 less_le zero_le_mult_iff)
            then show ?thesis unfolding eq meas_eq s_def
              using \<open>k * (vx x - ux x) \<le> f (vx x) - f (ux x)\<close> uv_lt \<open>0 < k\<close>
              by (simp add: False mult.commute)
          qed
        qed
        have "(\<Sum>i\<in>d'. measure lebesgue i) * k = (\<Sum>i\<in>d'. measure lebesgue i * k)"
          by (simp add: sum_distrib_right)
        also have "\<dots> \<le> (\<Sum>i\<in>d'. \<bar>f (Sup i) - f (Inf i)\<bar> - s * (f (Sup i) - f (Inf i)))"
          by (rule sum_mono) (use elt_bound in auto)
        also have "\<dots> \<le> (\<Sum>i\<in>d''. \<bar>f (Sup i) - f (Inf i)\<bar> - s * (f (Sup i) - f (Inf i)))"
          using \<open>finite d''\<close> d'_sub_d''
          by (intro sum_mono2) (auto simp: s_def)
        also have "\<dots> = (\<Sum>i\<in>d''. \<bar>f (Sup i) - f (Inf i)\<bar>) - s * (\<Sum>i\<in>d''. f (Sup i) - f (Inf i))"
          by (simp add: sum_subtractf sum_distrib_left[symmetric])
        also have "\<dots> = (\<Sum>i\<in>d''. \<bar>f (Sup i) - f (Inf i)\<bar>) - s * (f r - f l)"
          by (simp add: sum_telesc)
        also have "\<dots> \<le> vector_variation {l..r} f - \<bar>f r - f l\<bar>"
          using sum_abs_le by (simp add: s_abs)
        finally show ?thesis using \<open>0 < k\<close>
          by (simp add: divide_simps)
      qed
      finally show ?thesis using \<open>l \<le> r\<close> \<open>k>0\<close>
        by (simp add: K_eq d'_def divide_simps)
    qed
    have "(\<Sum>j\<in>D. measure lebesgue (\<Union>{i \<in> d. i \<subseteq> j})) * k
        = (\<Sum>j\<in>D. measure lebesgue (\<Union>{i \<in> d. i \<subseteq> j}) * k)"
      by (simp add: sum_distrib_right)
    also have "\<dots> \<le> (\<Sum>j\<in>D. vector_variation j f - norm (f (Sup j) - f (Inf j)))"
      by (rule sum_mono) (rule per_elt)
    also have "\<dots> = (\<Sum>j\<in>D. vector_variation j f) - (\<Sum>K\<in>D. norm (f (Sup K) - f (Inf K)))"
      by (simp add: sum_subtractf)
    also have "\<dots> \<le> vector_variation {a..b} f - (\<Sum>K\<in>D. norm (f (Sup K) - f (Inf K)))"
    proof -
      have "(\<Sum>j\<in>E. vector_variation j f) \<le> vector_variation (\<Union>E) f"
        if "finite E" "E \<subseteq> D" for E
        using that 
      proof (induction rule: finite_induct)
        case empty
        then show ?case by (simp add: vector_variation_def set_variation_def)
      next
        case (insert K F)
        then have "F \<subseteq> D" and K_in_D: "K \<in> D" by auto
        have IH: "(\<Sum>j\<in>F. vector_variation j f) \<le> vector_variation (\<Union>F) f"
          using insert(3)[OF \<open>F \<subseteq> D\<close>] .
        have disj_int: "interior K \<inter> interior (\<Union>F) = {}"
        proof (rule Int_interior_Union_intervals)
          fix U assume "U \<in> F"
          then have "U \<in> D" using \<open>F \<subseteq> D\<close> by auto
          show "\<exists>a b. U = cbox a b"
            using division_ofD(4)[OF D_div \<open>U \<in> D\<close>] by auto
          have "K \<noteq> U" using insert \<open>U \<in> F\<close> by auto
          show "interior K \<inter> interior U = {}"
            using division_ofD(5)[OF D_div K_in_D \<open>U \<in> D\<close> \<open>K \<noteq> U\<close>] .
        qed (use insert in auto)
        have bv_KF: "has_bounded_variation_on f (K \<union> \<Union>F)"
          using division_ofD(2)[OF D_div] insert(4)
          by (intro has_bounded_variation_on_subset[OF assms(1)]) auto
        have "(\<Sum>j\<in>insert K F. vector_variation j f) = vector_variation K f + (\<Sum>j\<in>F. vector_variation j f)"
          using insert by auto
        also have "\<dots> \<le> vector_variation (K \<union> \<Union>F) f"
          using vector_variation_le_Un[OF bv_KF disj_int] IH by linarith
        also have "K \<union> \<Union>F = \<Union>(insert K F)" by auto
        finally show ?case by simp
      qed
      then show ?thesis
        by (metis (lifting) ext D_div diff_mono division_ofD(6) fin_D order.refl)
    qed
    finally have sum_k_le: "(\<Sum>j\<in>D. measure lebesgue (\<Union>{i \<in> d. i \<subseteq> j})) * k
                \<le> vector_variation {a..b} f - (\<Sum>K\<in>D. norm (f (Sup K) - f (Inf K)))" .
    with D_sum have "(\<Sum>j\<in>D. measure lebesgue (\<Union>{i \<in> d. i \<subseteq> j})) * k < k * e / 3"
      by linarith
    then show ?thesis
      using \<open>0 < k\<close> by (simp add: field_simps)
  qed
  finally have d_bound: "measure lebesgue (\<Union>d) < e / 3" .
  show False
    using p_meas d_meas d_bound unfolding \<D>_def by auto
qed

(*added to Lebesgue_diff_thm 2026-06*)
lemma Lebesgue_diff_aux2:
  fixes f :: "real \<Rightarrow> real" and a b k :: real
  assumes f: "has_bounded_variation_on f {a..b}" and "a < b" "0 < k"
  shows "negligible
           {x \<in> {a..b}.
              \<forall>S. open S \<and> x \<in> S \<longrightarrow>
                (\<exists>u v. u \<in> {a..b} \<and> u \<in> S \<and>
                       v \<in> {a..b} \<and> v \<in> S \<and>
                       x \<in> {u<..<v} \<and> k \<le> (f v - f u) / (v - u)) \<and>
                (\<exists>u v. u \<in> {a..b} \<and> u \<in> S \<and>
                       v \<in> {a..b} \<and> v \<in> S \<and>
                       x \<in> {u<..<v} \<and> (f v - f u) / (v - u) \<le> -k)}" (is "negligible ?N")
proof -
  define N where "N \<equiv> ?N"
  have "negligible N"
    unfolding negligible_outer_le
  proof (intro allI impI)
    fix e :: real assume "e > 0"
    have ke3_pos: "0 < k * e / 3"
      using \<open>0 < k\<close> \<open>e > 0\<close> by auto
        \<comment> \<open>Get a division D of @{term \<open>{a..b}\<close>} whose sum exceeds $\text{vector\_variation} - k\varepsilon/3$\<close>
    define S where "S \<equiv> {\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) |d. d division_of {a..b}}"
    have S_ne: "S \<noteq> {}"
      by (metis (mono_tags, lifting) S_def box_real(2) elementary_interval empty_Collect_eq)
    have "vector_variation {a..b} f - k * e / 3 < Sup S"
      using ke3_pos vector_variation_on_interval[OF f] unfolding S_def by linarith
    then obtain x where "x \<in> S" "vector_variation {a..b} f - k * e / 3 < x"
      using less_cSupD[OF S_ne] by auto
    then obtain D where D_div: "D division_of {a..b}"
      and D_sum: "vector_variation {a..b} f - k * e / 3 < (\<Sum>K\<in>D. norm (f (Sup K) - f (Inf K)))"
      unfolding S_def by auto
    have fin_D: "finite D"
      using D_div division_of_finite by blast
    define N' where "N' \<equiv> N - \<Union>(frontier ` D)"
    have neg_frontiers: "negligible (\<Union>(frontier ` D))"
      using fin_D D_div convex_box(1) negligible_convex_frontier by blast
        \<comment> \<open>For each x in t, find division element and witnessing u, v\<close>
    have key: "\<exists>c d u v. {c..d} \<in> D \<and> x \<in> {c<..<d} \<and> u \<in> {c<..<d} \<and> v \<in> {c<..<d} \<and>
                  x \<in> {u<..<v} \<and>
                  (f c \<le> f d \<longrightarrow> f v - f u \<le> -k * (v - u)) \<and>
                  (f d < f c \<longrightarrow> k * (v - u) \<le> f v - f u)" if "x \<in> N'" for x
    proof -
      have xN: "x \<in> N" and xnf: "x \<notin> \<Union>(frontier ` D)" and xab: "x \<in> {a..b}"
        using that unfolding N'_def N_def by auto
          \<comment> \<open>Find the division element containing x\<close>
      have "x \<in> \<Union>D" using xab division_ofD(6)[OF D_div] by auto
      then obtain K c d where "K \<in> D" "x \<in> K" and Kcd: "K = {c..d}"
        by (metis D_div UnionE box_real(2) division_ofD(4))
      then obtain KD: "{c..d} \<in> D" and xK: "x \<in> {c..d}" 
        by blast
      have "x \<notin> frontier K" using xnf \<open>K \<in> D\<close> by auto
      then have "x \<notin> {c..d} - {c<..<d}"
        by (simp add: Kcd frontier_def)
      then have x_int: "x \<in> {c<..<d}" using xK by auto
          \<comment> \<open>Apply the N property with open set {c<..<d}\<close>
      show ?thesis
      proof (cases "f c \<le> f d")
        case True
        from x_int xN obtain u v where
          uv: "u \<in> {c<..<d}" "v \<in> {c<..<d}" "x \<in> {u<..<v}" "(f v - f u) / (v - u) \<le> -k"
          using N_def by auto
        then have "f v - f u \<le> -k * (v - u)" 
          by (simp add: pos_divide_le_eq mult.commute)
        then show ?thesis
          by (smt (verit, ccfv_SIG) KD True uv x_int)
      next
        case False
        from x_int xN obtain u v where uv: "u \<in> {c<..<d}" "v \<in> {c<..<d}" 
                    "x \<in> {u<..<v}" "k \<le> (f v - f u) / (v - u)"
          using N_def by auto
        then have "k * (v - u) \<le> f v - f u" by (simp add: pos_le_divide_eq mult.commute)
        then show ?thesis using False KD uv x_int by blast
      qed
    qed
    then obtain cx dx ux vx where
      key_fn: "\<And>x. x \<in> N' \<Longrightarrow> {cx x..dx x} \<in> D \<and> x \<in> {cx x<..<dx x} \<and>
                   ux x \<in> {cx x<..<dx x} \<and> vx x \<in> {cx x<..<dx x} \<and>
                   x \<in> {ux x<..<vx x} \<and>
                   (f (cx x) \<le> f (dx x) \<longrightarrow> f (vx x) - f (ux x) \<le> -k * (vx x - ux x)) \<and>
                   (f (dx x) < f (cx x) \<longrightarrow> k * (vx x - ux x) \<le> f (vx x) - f (ux x))"
      by metis
        \<comment> \<open>Reduce to finding a cover\<close>
    obtain C where C_sub: "N' \<subseteq> C" and C_meas: "C \<in> lmeasurable" and C_bound: "measure lebesgue C \<le> e"
      using cover_T [OF f \<open>k>0\<close> key_fn D_div D_sum] by metis
    define T where "T \<equiv> C \<union> \<Union>(frontier ` D)"
    have "N \<subseteq> T" unfolding T_def using C_sub unfolding N'_def by auto
    moreover have "T \<in> lmeasurable"
      using T_def C_meas neg_frontiers negligible_imp_measurable by blast
    moreover have "measure lebesgue T \<le> e"
      by (simp add: C_bound C_meas T_def measure_Un2 neg_frontiers negligible_diff
          negligible_imp_measurable negligible_imp_measure0)
    ultimately show "\<exists>T. N \<subseteq> T \<and> T \<in> lmeasurable \<and> measure lebesgue T \<le> e"
      by blast
  qed
  then show ?thesis
    by (simp add: N_def)
qed

(*added to Lebesgue_diff_thm 2026-06*)
lemma Lebesgue_diff_aux3:
  fixes f :: "real \<Rightarrow> real" and a b k :: real
  assumes "has_bounded_variation_on f {a..b}" "a < b" "0 < k"
  defines "I \<equiv> \<lambda>n x. ball x (inverse (real n + 1)) \<inter> {a..b}"
  shows "negligible
           {x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and>
                             u \<noteq> x \<and> v \<noteq> x \<and> k \<le> (f v - f x) / (v - x) \<and>
                             (f u - f x) / (u - x) \<le> -k}" (is "negligible ?T")
proof -
  define T where "T \<equiv> ?T"
  \<comment> \<open>The superset: endpoints \<union> discontinuities \<union> previous set is negligible\<close>
  define L2 where "L2 \<equiv> {x \<in> {a..b}.
      \<forall>S. open S \<and> x \<in> S \<longrightarrow>
        (\<exists>u v. u \<in> {a..b} \<and> u \<in> S \<and> v \<in> {a..b} \<and> v \<in> S \<and>
               x \<in> {u<..<v} \<and> k/2 \<le> (f v - f u) / (v - u)) \<and>
        (\<exists>u v. u \<in> {a..b} \<and> u \<in> S \<and> v \<in> {a..b} \<and> v \<in> S \<and>
               x \<in> {u<..<v} \<and> (f v - f u) / (v - u) \<le> -(k/2))}"
  have neg_endpts: "negligible {a, b}"
    by (rule negligible_finite) simp
  have neg_discont: "negligible {x \<in> {a..b}. \<not> isCont f x}"
    using countable_imp_negligible[OF has_bounded_variation_countable_discontinuities[OF assms(1)]] .
  have neg_L2: "negligible L2"
    unfolding L2_def using Lebesgue_diff_aux2[OF assms(1,2), of "k/2"] assms(3) by simp
  have neg_super: "negligible (({a, b} \<union> {x \<in> {a..b}. \<not> isCont f x}) \<union> L2)"
    by (rule negligible_Un[OF negligible_Un[OF neg_endpts neg_discont] neg_L2])
  show "negligible T"
  proof (rule negligible_subset[OF neg_super])
    show "T \<subseteq> ({a, b} \<union> {x \<in> {a..b}. \<not> isCont f x}) \<union> L2"
    proof (rule subsetI)
      fix x assume "x \<in> T"
      show "x \<in> ({a, b} \<union> {x \<in> {a..b}. \<not> isCont f x}) \<union> L2"
      proof (cases "x = a \<or> x = b \<or> \<not> isCont f x")
        case True
        with \<open>x \<in> T\<close> show ?thesis by (auto simp: T_def)
      next
        case False
          \<comment> \<open>x is interior, continuous, and has the oscillation property\<close>
        have "x \<in> L2"
          unfolding L2_def
        proof (intro CollectI conjI strip)
          show "x \<in> {a..b}"
            using \<open>x \<in> T\<close> by (auto simp: T_def)
        next
          fix S :: "real set"
          assume "open S \<and> x \<in> S"
          then have "open S" "x \<in> S" by auto
          have "x \<in> {a<..<b}"
            using \<open>x \<in> T\<close> False by (auto simp: T_def)
          have "open (S \<inter> {a<..<b})"
            using \<open>open S\<close> open_real_greaterThanLessThan by blast
          then have "\<exists>e>0. ball x e \<subseteq> S \<inter> {a<..<b}"
            using \<open>x \<in> S\<close> \<open>x \<in> {a<..<b}\<close>
            by (simp add: open_contains_ball)
          then obtain e where "e > 0" "ball x e \<subseteq> S \<inter> {a<..<b}"
            by auto
          obtain n :: nat where n_pos: "n \<noteq> 0" and inv_lt: "inverse (real n) < e"
            using real_arch_invD[OF \<open>e > 0\<close>] by blast
          have inv_n1_lt: "inverse (real n + 1) < e"
            by (smt (verit) inv_lt less_imp_inverse_less n_pos of_nat_0_eq_iff of_nat_less_0_iff)
          have ball_sub: "ball x (inverse (real n + 1)) \<subseteq> S \<inter> {a<..<b}"
            using \<open>ball x e \<subseteq> S \<inter> {a<..<b}\<close> inv_n1_lt by auto
          from \<open>x \<in> T\<close> obtain u v where
            uv: "u \<in> I n x" "v \<in> I n x" "u \<noteq> x" "v \<noteq> x" 
                "k \<le> (f v - f x) / (v - x)" "(f u - f x) / (u - x) \<le> -k"
            by (force simp add: T_def)
          have uS: "u \<in> S" and u_int: "u \<in> {a<..<b}" and vS: "v \<in> S" and v_int: "v \<in> {a<..<b}"
            and uab: "u \<in> {a..b}" and vab: "v \<in> {a..b}"
            using uv ball_sub by (auto simp: I_def)
          have fx_cont: "isCont f x" using False by simp
          have cont_slope: "isCont (\<lambda>y. (f v - f y) / (v - y)) x"
            by (intro fx_cont continuous_intros) (auto simp: uv)
          then have eps_delta: "\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y. \<bar>y - x\<bar> < \<delta> \<longrightarrow>
              \<bar>(f v - f y) / (v - y) - (f v - f x) / (v - x)\<bar> < \<epsilon>"
            by (simp add: continuous_at_real_range real_norm_def)
          with half_gt_zero[OF \<open>k>0\<close>]
          obtain d where "d > 0" and
            d_prop: "\<forall>y. \<bar>y - x\<bar> < d \<longrightarrow> \<bar>(f v - f y) / (v - y) - (f v - f x) / (v - x)\<bar> < k / 2"
            by blast
          have min_pos: "min d (inverse (real n + 1)) > 0"
            using \<open>d > 0\<close> by (simp add: min_def)
          show "\<exists>u v. u \<in> {a..b} \<and> u \<in> S \<and> v \<in> {a..b} \<and> v \<in> S \<and> x \<in> {u<..<v} \<and> k / 2 \<le> (f v - f u) / (v - u)"
          proof (cases "v < x")
            case True
              \<comment> \<open>v < x; witness y = x + min d (inv(n+1)) / 2 to the right of x\<close>
            define y where "y = x + min d (inverse (real n + 1)) / 2"
            have y_gt_x: "x < y"
              unfolding y_def using min_pos by simp
            have y_dist_d: "\<bar>y - x\<bar> < d" and y_in_ball: "y \<in> ball x (inverse (real n + 1))"
              unfolding y_def using \<open>d > 0\<close> min_pos by (auto simp: min_def dist_real_def ball_def)
            have yS: "y \<in> S" and y_int: "y \<in> {a<..<b}" and yab: "y \<in> {a..b}"
              using y_in_ball ball_sub by auto
            have x_between: "x \<in> {v<..<y}"
              using True y_gt_x by auto
            have "(f v - f y) / (v - y) > (f v - f x) / (v - x) - k / 2"
              using d_prop y_dist_d by (smt (verit))
            with uv have "(f v - f y) / (v - y) > k / 2"
              by linarith
            hence "k / 2 \<le> (f y - f v) / (y - v)"
              using True y_gt_x by (simp add: field_simps)
            then show ?thesis
              using vS vab x_between yS yab by blast
          next
            case False
            define y where "y = x - min d (inverse (real n + 1)) / 2"
            have y_dist: "\<bar>y - x\<bar> < inverse (real n + 1)" and y_dist_d: "\<bar>y - x\<bar> < d"
              unfolding y_def using \<open>d > 0\<close> min_pos by (auto simp: min_def)
            have y_in_ball: "y \<in> ball x (inverse (real n + 1))"
              using y_dist by (simp add: dist_real_def ball_def)
            have yS: "y \<in> S" and y_int: "y \<in> {a<..<b}"
              using y_in_ball ball_sub by auto
            have x_between: "x \<in> {y<..<v}"
              using y_def min_pos False uv by (fastforce simp: I_def)
            have slope_close: "(f v - f y) / (v - y) > (f v - f x) / (v - x) - k / 2"
              using d_prop y_dist_d by (smt (verit))
            with uv have "(f v - f y) / (v - y) > k / 2"
              by linarith
            then show ?thesis
              using less_le uv vS x_between yS y_int by (fastforce simp: I_def)
          qed
          have cont_slope_u: "isCont (\<lambda>y. (f u - f y) / (u - y)) x"
            by (intro fx_cont continuous_intros) (auto simp: uv)
          then have eps_delta_u: "\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y. \<bar>y - x\<bar> < \<delta> \<longrightarrow>
                \<bar>(f u - f y) / (u - y) - (f u - f x) / (u - x)\<bar> < \<epsilon>"
            by (simp add: continuous_at_real_range real_norm_def)
          obtain d' where "d' > 0" and
            d'_prop: "\<forall>y. \<bar>y - x\<bar> < d' \<longrightarrow>
                \<bar>(f u - f y) / (u - y) - (f u - f x) / (u - x)\<bar> < k / 2"
            using \<open>0 < k / 2\<close> eps_delta_u by blast
          have min_pos': "min d' (inverse (real n + 1)) > 0"
            using \<open>d' > 0\<close> by (simp add: min_def)
          show "\<exists>u v. u \<in> {a..b} \<and> u \<in> S \<and> v \<in> {a..b} \<and> v \<in> S \<and> x \<in> {u<..<v} \<and> (f v - f u) / (v - u) \<le> - (k / 2)"
          proof (cases "u < x")
            case True
              \<comment> \<open>u < x; witness y = x + min d' (inv(n+1)) / 2 to the right of x\<close>
            define y where "y = x + min d' (inverse (real n + 1)) / 2"
            have y_gt_x: "x < y"
              unfolding y_def using min_pos' by simp
            have y_dist: "\<bar>y - x\<bar> < inverse (real n + 1)" and y_dist_d: "\<bar>y - x\<bar> < d'"
              unfolding y_def using \<open>d' > 0\<close> min_pos' by (auto simp: min_def)
            have y_in_ball: "y \<in> ball x (inverse (real n + 1))"
              using y_dist by (simp add: dist_real_def ball_def)
            have yS: "y \<in> S" and y_int: "y \<in> {a<..<b}"
              using y_in_ball ball_sub by auto
            have x_between: "x \<in> {u<..<y}"
              using True y_gt_x by auto
            have "\<bar>(f u - f y) / (u - y) - (f u - f x) / (u - x)\<bar> < k / 2"
              using d'_prop y_dist_d by auto
            then have slope_upper: "(f u - f y) / (u - y) < - (k / 2)"
              using uv by linarith
            have "(f y - f u) / (y - u) = (f u - f y) / (u - y)"
              using True y_gt_x by (simp add: field_simps)
            hence "(f y - f u) / (y - u) \<le> - (k / 2)"
              using slope_upper by linarith
            then show ?thesis
              using uS uv x_between yS y_int less_le_not_le by (force simp: I_def)
          next
            case False
              \<comment> \<open>x < u; witness y is to the left of x\<close>
            hence xu: "x < u" using uv by linarith
            define y where "y = x - min d' (inverse (real n + 1)) / 2"
            have y_lt_x: "y < x"
              unfolding y_def using min_pos' by simp
            have y_dist: "\<bar>y - x\<bar> < inverse (real n + 1)"
              unfolding y_def using \<open>d' > 0\<close> min_pos' by (auto simp: min_def)
            have y_dist_d: "\<bar>y - x\<bar> < d'"
              unfolding y_def using \<open>d' > 0\<close> min_pos' by (auto simp: min_def)
            have y_in_ball: "y \<in> ball x (inverse (real n + 1))"
              using y_dist by (simp add: dist_real_def ball_def)
            have yS: "y \<in> S" and y_int: "y \<in> {a<..<b}"
              using y_in_ball ball_sub by auto
            have yab: "y \<in> {a..b}"
              using y_int by auto
            have x_between: "x \<in> {y<..<u}"
              using y_lt_x xu by auto
            have y_lt_u: "y < u" using y_lt_x xu by linarith
            have "\<bar>(f u - f y) / (u - y) - (f u - f x) / (u - x)\<bar> < k / 2"
              using d'_prop y_dist_d by auto
            with uv have slope_upper: "(f u - f y) / (u - y) \<le> - (k / 2)"
              by linarith
            then show ?thesis
              using uS uv x_between yS yab unfolding I_def by blast
          qed
        qed
        then show ?thesis
          by fastforce 
      qed
    qed
  qed
qed

(*added to Lebesgue_diff_thm 2026-06*)
lemma Lebesgue_diff_aux4:
  fixes f :: "real \<Rightarrow> real" and a b k :: real
  assumes f: "has_bounded_variation_on f {a..b}" and "a < b" "0 < k"
  defines "I \<equiv> \<lambda>n x. ball x (inverse (real n + 1)) \<inter> {a..b}"
  shows "negligible
           {x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> (f v - f x) / (v - x) - (f u - f x) / (u - x)}" 
     (is "negligible ?T")
proof -
  define T where "T \<equiv> ?T"
  \<comment> \<open>we get a negligible set outside which f has a local Lipschitz bound\<close>
  from Lebesgue_diff_aux1[OF assms(1)]
  obtain U where neg_U: "negligible U" 
    and U_prop: "\<forall>x \<in> {a..b} - U. \<exists>B>0. \<forall>\<^sub>F y in at x. norm (f y - f x) \<le> B * norm (y - x)"
    by auto
  \<comment> \<open>Define the rational-indexed family: for each q \<in> \<rat>, the set of x where
      the v-quotient is \<ge> q + k/3 and the u-quotient is \<le> q - k/3\<close>
  define S where "S q \<equiv> {x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                             k / 3 \<le> (f v - f x) / (v - x) - q \<and>
                             (f u - f x) / (u - x) - q \<le> -(k / 3)}" for q :: real
  \<comment> \<open>The target set T is a subset of this\<close>
  have neg_super: "negligible (U \<union> \<Union>(S ` \<rat>))"
  proof (rule negligible_Un[OF neg_U])
    show "negligible (\<Union>(S ` \<rat>))"
    proof (rule negligible_countable_Union)
      show "countable (S ` \<rat>)"
        using countable_rat by (rule countable_image)
    next
      fix Sq assume "Sq \<in> S ` \<rat>"
      then obtain q where "q \<in> \<rat>" and "Sq = S q" by auto
      show "negligible Sq"
      proof -
        define g where "g \<equiv> \<lambda>x. f x - q * x"
        have bv_id: "has_bounded_variation_on id {a..b}"
          by (rule increasing_bounded_variation) (auto simp: mono_on_def)
        have "has_bounded_variation_on (\<lambda>x. q *\<^sub>R x) {a..b}"
          using has_bounded_variation_on_cmul[OF bv_id] by simp
        then have bv_g: "has_bounded_variation_on g {a..b}"
          unfolding g_def using f has_bounded_variation_on_sub by force
        have Sq_eq: "S q = {x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                             k / 3 \<le> (g v - g x) / (v - x) \<and> (g u - g x) / (u - x) \<le> -(k / 3)}"
          unfolding S_def
            apply (intro arg_cong[where f="\<lambda>P. {x \<in> {a..b}. P x}"] ext all_cong1 ex_cong1)
            by (auto simp: g_def algebra_simps divide_simps)
        show ?thesis unfolding \<open>Sq = S q\<close> Sq_eq
          using Lebesgue_diff_aux3[OF bv_g \<open>a<b\<close>, of "k/3"] \<open>k>0\<close> by (simp add: I_def)
      qed
    qed
  qed
  show "negligible T"
  proof (rule negligible_subset[OF neg_super])
    show "T \<subseteq> U \<union> \<Union>(S ` \<rat>)"
    proof (rule subsetI)
      fix x assume "x \<in> T"
      then obtain xab: "x \<in> {a..b}" and
        xprop: "\<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                               k \<le> (f v - f x) / (v - x) - (f u - f x) / (u - x)"
        unfolding T_def by blast
      show "x \<in> U \<union> \<Union>(S ` \<rat>)"
      proof (cases "x \<in> U")
        case True then show ?thesis by auto
      next
        case False
        \<comment> \<open>x \<notin> U, so f has a local Lipschitz bound at x\<close>
        have "x \<in> {a..b} - U" using xab False by auto
        from U_prop[rule_format, OF this]
        obtain B where "B > 0" and
          B_ev: "eventually (\<lambda>y. norm (f y - f x) \<le> B * norm (y - x)) (at x)"
          by auto
        \<comment> \<open>The difference quotients are bounded near x; extract a uniform bound on
            difference quotients in sufficiently small balls, then find a rational separator\<close>
        obtain N where dq_bound: "\<And>n u. N \<le> n \<Longrightarrow> u \<in> ball x (inverse (real n + 1)) \<Longrightarrow> u \<noteq> x
            \<Longrightarrow> \<bar>(f u - f x) / (u - x)\<bar> \<le> B"
        proof -
          from B_ev obtain d :: real where "d > 0" and
            d_prop: "\<And>y. y \<noteq> x \<Longrightarrow> dist y x < d \<Longrightarrow> norm (f y - f x) \<le> B * norm (y - x)"
            unfolding eventually_at by auto
          from real_arch_invD[OF \<open>d > 0\<close>]
          obtain N :: nat where "N \<noteq> 0" and "inverse (real N) < d" by auto
          show thesis
          proof 
            fix n u
            assume "N \<le> n" "u \<in> ball x (inverse (real n + 1))" "u \<noteq> x"
            then have "dist u x < inverse (real n + 1)"
              by (simp add: mem_ball dist_commute)
            also have "inverse (real n + 1) \<le> inverse (real N)"
              using \<open>N \<le> n\<close> \<open>N \<noteq> 0\<close> by auto
            also have "\<dots> < d" by fact
            finally have "dist u x < d" .
            have "\<bar>u - x\<bar> > 0" using \<open>u \<noteq> x\<close> by auto
            with d_prop[OF \<open>u \<noteq> x\<close>] show "\<bar>(f u - f x) / (u - x)\<bar> \<le> B"
              by (simp add: \<open>dist u x < d\<close> pos_divide_le_eq)
          qed
        qed
        have balls_nonempty: "\<And>n. \<exists>u. u \<in> I n x \<and> u \<noteq> x"
          using xprop by blast 
        \<comment> \<open>The infimum of difference quotients over shrinking balls converges\<close>
        define DQ where "DQ n = {(f u - f x) / (u - x) | u.
          u \<in> I n x \<and> u \<noteq> x}" for n
        have S_nonempty: "DQ n \<noteq> {}" for n
          using balls_nonempty[of n] unfolding DQ_def by blast
        have S_bdd: "bdd_below (DQ n)" if "N \<le> n" for n
          using DQ_def abs_le_D2[OF dq_bound[OF \<open>N \<le> n\<close>]] that 
          by (auto simp: bdd_below.unfold minus_le_iff I_def)
        have S_subset: "DQ n \<subseteq> DQ m" if "m \<le> n" for m n
          unfolding DQ_def I_def using less_le_trans that by fastforce
        define g where "g \<equiv> \<lambda>n. Inf (DQ n)"
        have g_mono: "g m \<le> g n" if "N \<le> m" "m \<le> n" for m n
          by (simp add: S_bdd S_nonempty S_subset cInf_superset_mono g_def that)
        have g_bounded: "norm (g (n + N)) \<le> B" for n
        proof -
          have nN: "N \<le> n + N" by simp
          obtain u where u: "u \<in> ball x (inverse (real (n + N) + 1))" "u \<in> {a..b}" "u \<noteq> x"
            using balls_nonempty[of "n + N"] I_def by auto
          have mem: "(f u - f x) / (u - x) \<in> DQ (n + N)" 
            unfolding DQ_def I_def using u by auto
          have "g (n + N) \<le> (f u - f x) / (u - x)"
            unfolding g_def by (rule cInf_lower[OF mem S_bdd[OF nN]])
          also have "\<dots> \<le> B"
            using abs_le_D1[OF dq_bound[OF nN u(1) u(3)]] .
          finally have upper: "g (n + N) \<le> B" .
          have "- B \<le> y" if y: "y \<in> DQ (n + N)" for y
            using dq_bound nN y  
            by (simp add: DQ_def I_def) (metis of_nat_add abs_divide abs_le_D2 add.commute le_add1 minus_le_iff)
          then have "- B \<le> Inf (DQ (n + N))"
            using le_cInf_iff[OF S_nonempty S_bdd[OF nN]] by auto
          with upper show ?thesis
            by (simp add: g_def abs_le_iff)
        qed
        have bseq: "Bseq (\<lambda>n. g (n + N))"
          unfolding Bseq_def using \<open>B > 0\<close> g_bounded by auto
        have "convergent g"
          using Bseq_monoseq_convergent'_inc bseq g_mono by blast
        then obtain l where l_conv: "g \<longlonglongrightarrow> l" using convergentD by auto
        \<comment> \<open>The supremum of difference quotients over shrinking balls converges\<close>
        have S_upper: "y \<le> B" if "N \<le> n" "y \<in> DQ n" for n y
          using abs_le_D1[OF dq_bound] DQ_def I_def that by auto 
        have S_bdd_above: "bdd_above (DQ n)" if "N \<le> n" for n
          using S_upper[OF \<open>N \<le> n\<close>] by fastforce
        define h where "h \<equiv> \<lambda>n. Sup (DQ n)" 
        have h_mono: "h n \<le> h m" if "N \<le> m" "m \<le> n" for m n
          by (simp add: S_bdd_above S_nonempty S_subset cSup_subset_mono h_def that)
        have h_bounded: "norm (h (n + N)) \<le> B" for n
        proof -
          have nN: "N \<le> n + N" by simp
          have upper: "h (n + N) \<le> B"
            using cSup_le_iff[OF S_nonempty S_bdd_above[OF nN]]
            by (metis S_upper add.commute h_def le_add1)
          obtain u where u: "u \<in> ball x (inverse (real (n + N) + 1))" "u \<in> {a..b}" "u \<noteq> x"
            using balls_nonempty[of "n + N"] I_def by auto
          have mem: "(f u - f x) / (u - x) \<in> DQ (n + N)" 
            unfolding DQ_def I_def using u by auto
          have "(f u - f x) / (u - x) \<le> h (n + N)"
            unfolding h_def by (rule cSup_upper[OF mem S_bdd_above[OF nN]])
          moreover have "- B \<le> (f u - f x) / (u - x)"
            using abs_le_D2[OF dq_bound[OF nN u(1) u(3)]] by linarith
          ultimately have lower: "- B \<le> h (n + N)" by linarith
          from upper lower show ?thesis
            by (simp add: abs_le_iff real_norm_def)
        qed
        have bseq_h: "Bseq (\<lambda>n. h (n + N))"
          unfolding Bseq_def using \<open>B > 0\<close> h_bounded by auto
        obtain m where m_conv: "h \<longlonglongrightarrow> m" 
          using convergentD Bseq_monoseq_convergent'_dec bseq_h h_mono by blast 
        have diff_conv: "(\<lambda>n. h n - g n) \<longlonglongrightarrow> m - l"
          by (rule tendsto_diff[OF m_conv l_conv])
        have "k \<le> (\<lambda>n. h n - g n) n" if "N \<le> n" for n
        proof -
          obtain u v where uv: "u \<in> I n x" "v \<in> I n x" "u \<noteq> x" "v \<noteq> x"
            and kle: "k \<le> (f v - f x) / (v - x) - (f u - f x) / (u - x)"
            by (meson xab xprop)
          have *: "(f u - f x) / (u - x) \<in> DQ n"  "(f v - f x) / (v - x) \<in> DQ n"
            unfolding DQ_def using uv by auto
          have "g n \<le> (f u - f x) / (u - x)"
            by (simp add: "*" S_bdd g_def cInf_lower that)
          moreover have "(f v - f x) / (v - x) \<le> h n"
            by (simp add: "*" S_bdd_above h_def cSup_upper that)
          ultimately show "k \<le> (\<lambda>n. h n - g n) n" using kle by linarith
        qed
        then have k_le: "k \<le> m - l" using Lim_bounded2[OF diff_conv]
          by blast
            \<comment> \<open>find a rational witness q\<close>
        have mid: "(l + m) / 2 - k / 6 < (l + m) / 2 + k / 6"
          using assms by auto
        then obtain q where q: "q \<in> \<rat>" "(l + m) / 2 - k / 6 < q" "q < (l + m) / 2 + k / 6"
          using Rats_dense_in_real by blast
        with k_le \<open>0 < k\<close>  have q_l: "k / 3 < q - l" and q_m: "k / 3 < m - q"
          by (auto simp add: field_simps)
        have main: "\<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                            k / 3 \<le> (f v - f x) / (v - x) - q \<and>
                            (f u - f x) / (u - x) - q \<le> - (k / 3)" for n
        proof -
          \<comment> \<open>First reduction: not all dq's in DQ n are \<ge> q - k/3\<close>
          have neg_lower: False 
            if A: "\<forall>u. u \<in> I n x \<and> u \<noteq> x
                \<longrightarrow> q - k / 3 \<le> (f u - f x) / (u - x)"
          proof -
            have lb: "q - k / 3 \<le> y" if "y \<in> DQ p" "n \<le> p" for y p
              using S_subset[OF that(2)] that(1) using A DQ_def by auto
            have "q - k / 3 \<le> g p" if "max n N \<le> p" for p
            proof -
              have "q - k / 3 \<le> Inf (DQ p)"
                using le_cInf_iff[OF S_nonempty S_bdd[OF max.cobounded2[THEN le_trans[OF _ that]]]]
                  lb[OF _ max.cobounded1[THEN le_trans[OF _ that]]]
                by auto
              then show ?thesis unfolding g_def .
            qed
            with Lim_bounded2[OF l_conv] have "q - k / 3 \<le> l" by blast
            with q_l show False by linarith
          qed
            \<comment> \<open>Second reduction: not all dq's in DQ n are \<le> q + k/3\<close>
          have neg_upper: False
            if A: "\<forall>v. v \<in> I n x \<and> v \<noteq> x
                  \<longrightarrow> (f v - f x) / (v - x) \<le> k / 3 + q"
          proof -
            have ub: "y \<le> k / 3 + q" if "y \<in> DQ p" "n \<le> p" for y p
              using S_subset[OF that(2)] that(1) using A DQ_def by auto 
            have "h p \<le> k / 3 + q" if "max n N \<le> p" for p
            proof -
              have "Sup (DQ p) \<le> k / 3 + q"
                using cSup_le_iff[OF S_nonempty S_bdd_above[OF max.cobounded2[THEN le_trans[OF _ that]]]]
                  ub[OF _ max.cobounded1[THEN le_trans[OF _ that]]]
                by auto
              then show ?thesis unfolding h_def .
            qed
            then have "\<forall>p \<ge> max n N. h p \<le> k / 3 + q" by auto
            with Lim_bounded[OF m_conv] have "m \<le> k / 3 + q" .
            with q_m show False by linarith
          qed
          show ?thesis
            by (smt (verit) neg_lower neg_upper)
        qed
        have "x \<in> S q" unfolding S_def using xab main by auto
        with \<open>q \<in> \<rat>\<close> q_l show ?thesis
          by blast
      qed
    qed
  qed
qed

(*added to Lebesgue_diff_thm 2026-06*)
lemma Lebesgue_diff_aux5:
  fixes f :: "real \<Rightarrow> real" and a b k :: real
  assumes f: "has_bounded_variation_on f {a..b}" and "a < b" "0 < k"
  defines "I n x \<equiv> ball x (inverse (real n + 1)) \<inter> {a..b}" 
  shows "negligible
           {x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> \<bar>(f v - f x) / (v - x) - (f u - f x) / (u - x)\<bar>}"
proof -
  have neg_union: "negligible (
           {x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and>
                             u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> (f v - f x) / (v - x) - (f u - f x) / (u - x)} \<union>
           {x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and>
                             u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> ((-f v) - (-f x)) / (v - x) - ((-f u) - (-f x)) / (u - x)})"
    using Lebesgue_diff_aux4 assms unfolding I_def
    by (blast intro: negligible_Un has_bounded_variation_on_neg[OF f])+
  \<comment> \<open>The target set is a subset of the union\<close>
  then show ?thesis
  proof (rule negligible_subset)
    show "{x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and>
                             u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> \<bar>(f v - f x) / (v - x) - (f u - f x) / (u - x)\<bar>} \<subseteq>
           {x \<in> {a..b}. \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and>
                             u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> (f v - f x) / (v - x) - (f u - f x) / (u - x)} \<union>
           {x \<in> {a..b}. \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and>
                             u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> ((-f v) - (-f x)) / (v - x) - ((-f u) - (-f x)) / (u - x)}"
    proof (rule subsetI)
      fix x assume x: "x \<in> {x \<in> {a..b}.
              \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and>
                             u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> \<bar>(f v - f x) / (v - x) - (f u - f x) / (u - x)\<bar>}"
      \<comment> \<open>For any m, n, use m+n to get witnesses in the smaller ball\<close>
      have key: "\<exists>u v. (u \<in> I m x \<and> v \<in> I m x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                         k \<le> (f v - f x) / (v - x) - (f u - f x) / (u - x)) \<or>
                       (u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                         k \<le> ((-f v) - (-f x)) / (v - x) - ((-f u) - (-f x)) / (u - x))" for m n
      proof -
        from x
        obtain u v where uv: "u \<in> I (m+n) x" "v \<in> I (m+n) x" "u \<noteq> x" "v \<noteq> x"
          "k \<le> \<bar>(f v - f x) / (v - x) - (f u - f x) / (u - x)\<bar>"
          by blast
        have ball_m: "ball x (inverse (real (m+n) + 1)) \<subseteq> ball x (inverse (real m + 1))"
          by (intro subset_ball le_imp_inverse_le) linarith+
        have ball_n: "ball x (inverse (real (m+n) + 1)) \<subseteq> ball x (inverse (real n + 1))"
          by (intro subset_ball le_imp_inverse_le) linarith+
        from uv have "k \<le> (f v - f x) / (v - x) - (f u - f x) / (u - x) \<or>
                         k \<le> -((f v - f x) / (v - x) - (f u - f x) / (u - x))"
          by linarith
        then show ?thesis
          using uv ball_m ball_n x unfolding I_def
          by (smt (verit, ccfv_threshold) mem_Collect_eq)
      qed
      \<comment> \<open>From \<forall>m n. P m \<or> Q n, deduce (\<forall>m. P m) \<or> (\<forall>n. Q n)\<close>
      show "x \<in> {x \<in> {a..b}. \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> (f v - f x) / (v - x) - (f u - f x) / (u - x)} \<union>
                {x \<in> {a..b}. \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                             k \<le> ((-f v) - (-f x)) / (v - x) - ((-f u) - (-f x)) / (u - x)}"
        using x key by simp metis
    qed
  qed
qed

(*added to Lebesgue_diff_thm 2026-06*)
lemma Lebesgue_diff_aux6:
  fixes f :: "real \<Rightarrow> real"
  assumes "has_bounded_variation_on f {a..b}" "a < b"
  defines "I \<equiv> \<lambda>n x. ball x (inverse (real n + 1)) \<inter> {a..b}"
  shows "negligible {x \<in> {a..b}. \<not> f differentiable (at x within {a..b})}"
proof -
  have "negligible {x \<in> {a..b}. \<not> (\<exists>f'. ((\<lambda>y. (f y - f x) / (y - x)) \<longlongrightarrow> f') (at x within {a..b}))}"
  proof -
    define S where "S m = {x \<in> {a..b}.
      \<forall>n::nat. \<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                     inverse (real m + 1) \<le> \<bar>(f v - f x) / (v - x) - (f u - f x) / (u - x)\<bar>}" for m
    have neg: "negligible (S m)" for m
      unfolding S_def using Lebesgue_diff_aux5 assms by auto
    have "negligible (\<Union>(range S))"
      by (rule negligible_Union_nat[OF neg])
    moreover have "{x \<in> {a..b}. \<not> (\<exists>f'. ((\<lambda>y. (f y - f x) / (y - x)) \<longlongrightarrow> f') (at x within {a..b}))} \<subseteq> \<Union>(range S)"
    proof (rule subsetI)
      fix x assume x: "x \<in> {x \<in> {a..b}. \<not> (\<exists>f'. ((\<lambda>y. (f y - f x) / (y - x)) \<longlongrightarrow> f') (at x within {a..b}))}"
      then obtain e where "e > 0" and osc: "\<forall>d>0. \<exists>u\<in>{a..b}. \<exists>v\<in>{a..b}.
          u \<noteq> x \<and> dist u x < d \<and> v \<noteq> x \<and> dist v x < d \<and>
          e \<le> dist ((f u - f x) / (u - x)) ((f v - f x) / (v - x))"
        unfolding convergent_eq_Cauchy_within by (force simp: not_less)
      obtain m where m: "inverse (real m + 1) < e"
        using reals_Archimedean[OF \<open>e > 0\<close>] by (metis add.commute of_nat_Suc)
      have "x \<in> S m"
        unfolding S_def
      proof (intro CollectI conjI allI)
        fix n :: nat
        have "inverse (real n + 1) > 0" by auto
        with osc obtain u v where "u \<in> {a..b}" "v \<in> {a..b}" "u \<noteq> x" "dist u x < inverse (real n + 1)"
          "v \<noteq> x" "dist v x < inverse (real n + 1)"
          "e \<le> dist ((f u - f x) / (u - x)) ((f v - f x) / (v - x))"
          by blast
        then have "inverse (real m + 1) \<le> \<bar>(f v - f x) / (v - x) - (f u - f x) / (u - x)\<bar>"
          using m by (simp add: dist_real_def)
        moreover have "u \<in> ball x (inverse (real n + 1))" "v \<in> ball x (inverse (real n + 1))"
          using \<open>dist u x < inverse (real n + 1)\<close> \<open>dist v x < inverse (real n + 1)\<close>
          by (simp_all add: dist_commute)
        ultimately show "\<exists>u v. u \<in> I n x \<and> v \<in> I n x \<and> u \<noteq> x \<and> v \<noteq> x \<and>
                     inverse (real m + 1) \<le> \<bar>(f v - f x) / (v - x) - (f u - f x) / (u - x)\<bar>"
          using \<open>u \<in> {a..b}\<close> \<open>v \<in> {a..b}\<close> \<open>u \<noteq> x\<close> \<open>v \<noteq> x\<close>
          using I_def by blast
      qed (use x in auto)
      then show "x \<in> \<Union>(range S)" by auto
    qed
    ultimately show ?thesis by (rule negligible_subset)
  qed
  moreover
  have "\<And>x. f differentiable (at x within {a..b}) \<longleftrightarrow>
            (\<exists>D. ((\<lambda>y. (f y - f x) / (y - x)) \<longlongrightarrow> D) (at x within {a..b}))"
    unfolding vector_differentiable has_vector_derivative_within_1D
    by (simp add: real_scaleR_def mult.commute[of "inverse _"] divide_inverse[symmetric])
  ultimately show ?thesis by simp
qed

(*added to Lebesgue_diff_thm 2026-06*)
theorem Lebesgue_differentiation_theorem_compact:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "has_bounded_variation_on f (cbox a b)"
  shows "negligible {x \<in> cbox a b. \<not> f differentiable (at x)}"
proof -
  let ?g = "\<lambda>i. (\<lambda>x. f x \<bullet> i)"
  have cw: "(f differentiable at x) = (\<forall>i\<in>Basis. ?g i differentiable at x)" for x
  proof -
    have "at x within UNIV = at x" by (rule at_within_open[OF UNIV_I open_UNIV])
    then show ?thesis using differentiable_componentwise_within[where S=UNIV and a=x and f=f]
      by simp
  qed
  have eq: "{x \<in> cbox a b. \<not> f differentiable (at x)} =
            (\<Union>i\<in>Basis. {x \<in> cbox a b. \<not> ?g i differentiable (at x)})"
    by (auto simp: cw)
  show ?thesis unfolding eq
  proof (rule negligible_Union[OF finite_imageI[OF finite_Basis]], clarsimp)
    fix i :: 'a assume "i \<in> Basis"
    show "negligible {x. a \<le> x \<and> x \<le> b \<and> \<not> ?g i differentiable (at x)}"
    proof (cases "a < b")
      case True
      have sub: "{x \<in> {a..b}. \<not> ?g i differentiable (at x)} \<subseteq>
             insert a (insert b {x \<in> {a..b}. \<not> ?g i differentiable (at x within {a..b})})"
        by (auto simp: at_within_Icc_at)
      have "negligible (insert a (insert b {x \<in> {a..b}. \<not> ?g i differentiable (at x within {a..b})}))"
        using Lebesgue_diff_aux6 [OF has_bounded_variation_on_inner_left] assms True by auto
      with negligible_subset [OF _ sub] show ?thesis by simp
    next
      case False
      then show ?thesis
        by (force intro: negligible_subset[OF negligible_sing[of a]])
    qed
  qed
qed

(*added to Lebesgue_diff_thm 2026-06*)
lemma Lebesgue_differentiation_theorem_open:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "open S" "has_bounded_variation_on f S"
  shows "negligible {x \<in> S. \<not> f differentiable (at x)}"
proof -
  obtain \<D> where cnt: "countable \<D>" and sub: "\<D> \<subseteq> Pow S"
    and boxes: "\<And>X. X \<in> \<D> \<Longrightarrow> \<exists>a b. X = cbox a b" and cov: "\<Union> \<D> = S"
    using open_countable_Union_open_cbox[OF assms(1)] by metis
  have eq: "{x \<in> S. \<not> f differentiable (at x)} = \<Union> ((\<lambda>T. {x \<in> T. \<not> f differentiable (at x)}) ` \<D>)"
    using cov by auto
  have "negligible (\<Union> ((\<lambda>T. {x \<in> T. \<not> f differentiable (at x)}) ` \<D>))"
  proof (rule negligible_countable_Union)
    show "countable ((\<lambda>T. {x \<in> T. \<not> f differentiable (at x)}) ` \<D>)"
      using cnt by (rule countable_image)
  next
    fix U assume "U \<in> (\<lambda>T. {x \<in> T. \<not> f differentiable (at x)}) ` \<D>"
    then obtain T where T: "T \<in> \<D>" and Seq: "U = {x \<in> T. \<not> f differentiable (at x)}"
      by auto
    obtain a b where Tab: "T = cbox a b" using boxes[OF T] by auto
    have "has_bounded_variation_on f T"
      using has_bounded_variation_on_subset[OF assms(2)] sub T by auto
    then show "negligible U"
      unfolding Seq Tab
      by (rule Lebesgue_differentiation_theorem_compact)
  qed
  then show ?thesis using eq by simp
qed

(*added to Lebesgue_diff_thm 2026-06*)
corollary Lebesgue_differentiation_theorem:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "is_interval S" "has_bounded_variation_on f S"
  shows "negligible {x \<in> S. \<not> f differentiable (at x)}"
proof -
  have sub: "{x \<in> S. \<not> f differentiable (at x)} \<subseteq>
             {x \<in> frontier S. \<not> f differentiable (at x)} \<union>
             {x \<in> interior S. \<not> f differentiable (at x)}"
    using closure_subset[of S] by (auto simp: frontier_def)
  have fr: "negligible {x \<in> frontier S. \<not> f differentiable (at x)}"
  proof (rule negligible_subset[OF negligible_finite])
    show "finite (frontier S)"
      using finite_frontier_interval_real[OF assms(1)] by blast
    show "{x \<in> frontier S. \<not> f differentiable (at x)} \<subseteq> frontier S"
      by auto
  qed
  have int: "negligible {x \<in> interior S. \<not> f differentiable (at x)}"
  proof -
    have bv: "has_bounded_variation_on f (interior S)"
      using has_bounded_variation_on_subset[OF assms(2) interior_subset] .
    have op: "open (interior S)" by (rule open_interior)
    \<comment> \<open>Reduces to the open-set case, proved below\<close>
    show ?thesis using Lebesgue_differentiation_theorem_open[OF op bv] .
  qed
  show ?thesis
    using negligible_subset[OF negligible_Un[OF fr int] sub] .
qed

(*added to Lebesgue_diff_thm 2026-06*)
corollary Lebesgue_differentiation_theorem_alt:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "is_interval S" "has_bounded_variation_on f S"
  shows "\<exists>t. t \<subseteq> S \<and> negligible t \<and> (\<forall>x \<in> S - t. f differentiable (at x))"
proof -
  let ?t = "{x \<in> S. \<not> f differentiable (at x)}"
  have "?t \<subseteq> S" "negligible ?t"
    using Lebesgue_differentiation_theorem[OF assms] by auto
  moreover have "\<forall>x \<in> S - ?t. f differentiable (at x)" by auto
  ultimately show ?thesis by blast
qed

(*added to Lebesgue_diff_thm 2026-06*)
corollary Lebesgue_differentiation_theorem_gen:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "countable (components S)" "has_bounded_variation_on f S"
  shows "negligible {x \<in> S. \<not> f differentiable (at x)}" proof -
  have "\<exists>y\<in>components S. x \<in> y"
    if "x \<in> S" and "\<not> f differentiable at x"
    for x
    using that
    by (metis UnionE Union_components)
  then have eq: "{x \<in> S. \<not> f differentiable (at x)} =
            \<Union> ((\<lambda>C. {x \<in> C. \<not> f differentiable (at x)}) ` components S)"
    using in_components_subset by blast
  show ?thesis unfolding eq
  proof (rule negligible_countable_Union)
    show "countable ((\<lambda>C. {x \<in> C. \<not> f differentiable (at x)}) ` components S)"
      using assms(1) by (rule countable_image)
  next
    fix U assume "U \<in> (\<lambda>C. {x \<in> C. \<not> f differentiable (at x)}) ` components S"
    then obtain C where C: "C \<in> components S" and Seq: "U = {x \<in> C. \<not> f differentiable (at x)}"
      by auto
    have "is_interval C"
      using in_components_connected[OF C] is_interval_connected_1 by auto
    moreover have "has_bounded_variation_on f C"
      using has_bounded_variation_on_subset[OF assms(2) in_components_subset[OF C]] .
    ultimately show "negligible U"
      unfolding Seq by (rule Lebesgue_differentiation_theorem)
  qed
qed

(*added to Lebesgue_diff_thm 2026-06*)
corollary Lebesgue_differentiation_theorem_increasing:
  fixes f :: "real \<Rightarrow> real"
  assumes "is_interval S" "mono_on S f"
  shows "negligible {x \<in> S. \<not> f differentiable (at x)}"
proof -
  let ?N = "{x \<in> S. \<not> f differentiable (at x)}"
  have "locally negligible ?N"
    unfolding locally_def
  proof (intro allI impI)
    fix w x assume wx: "openin (top_of_set ?N) w \<and> x \<in> w"
    then have xN: "x \<in> ?N" using openin_imp_subset by blast
    then have "x \<in> S" by simp
    from interval_contains_compact_neighbourhood[OF \<open>is_interval S\<close> this]
    obtain a b d where "0 < d" "x \<in> cbox a b" "cbox a b \<subseteq> S"
      and ball_sub: "ball x d \<inter> S \<subseteq> cbox a b"
      by auto
    have mono_ab: "mono_on {a..b} f"
      using mono_on_subset[OF \<open>mono_on S f\<close> \<open>cbox a b \<subseteq> S\<close>] by (simp add: cbox_interval)
    have neg: "negligible {y \<in> cbox a b. \<not> f differentiable (at y)}"
      by (rule Lebesgue_differentiation_theorem_compact[OF
            increasing_bounded_variation[OF mono_ab, folded cbox_interval]])
    let ?U = "w \<inter> ball x d"
    let ?V = "{y \<in> cbox a b. \<not> f differentiable (at y)} \<inter> w"
    have U_open: "openin (top_of_set ?N) ?U"
      using wx by (auto intro!: openin_Int_open[OF _ open_ball])
    have "x \<in> ?U" using wx \<open>0 < d\<close> by auto
    moreover have "?U \<subseteq> ?V"
    proof
      fix y assume "y \<in> ?U"
      then have "y \<in> w" "y \<in> ball x d" by auto
      from \<open>y \<in> w\<close> wx have "y \<in> ?N" using openin_imp_subset by blast
      then have "y \<in> S" "\<not> f differentiable (at y)" by auto
      from \<open>y \<in> ball x d\<close> \<open>y \<in> S\<close> ball_sub have "y \<in> cbox a b" by auto
      with \<open>\<not> f differentiable (at y)\<close> \<open>y \<in> w\<close> show "y \<in> ?V" by auto
    qed
    moreover have "negligible ?V"
      by (rule negligible_subset[OF neg]) auto
    moreover have "?V \<subseteq> w" by auto
    ultimately show "\<exists>U V. openin (top_of_set ?N) U \<and> negligible V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> w"
      using U_open by blast
  qed
  then show ?thesis by (simp add: locally_negligible)
qed

(*added to Lebesgue_diff_thm 2026-06*)
corollary Lebesgue_differentiation_theorem_decreasing:
  fixes f :: "real \<Rightarrow> real"
  assumes "is_interval S" "antimono_on S f"
  shows "negligible {x \<in> S. \<not> f differentiable (at x)}"
proof -
  have mono: "mono_on S (\<lambda>x. - f x)"
    using assms(2) by (auto simp: monotone_on_def)
  have sub: "{x \<in> S. \<not> f differentiable (at x)} \<subseteq> {x \<in> S. \<not> (\<lambda>x. - f x) differentiable (at x)}"
  proof -
    have "\<And>x. (\<lambda>x. - f x) differentiable (at x) \<Longrightarrow> f differentiable (at x)"
      using differentiable_minus[of "(\<lambda>x. - f x)"] by simp
    then show ?thesis by auto
  qed
  moreover have "negligible {x \<in> S. \<not> (\<lambda>x. - f x) differentiable (at x)}"
    by (rule Lebesgue_differentiation_theorem_increasing[OF assms(1) mono])
  ultimately show ?thesis by (rule negligible_subset[rotated])
qed

(*added to Real 2026-06*)
lemma le_iff_forall_rat_less_imp:
  fixes x y :: real
  shows "x \<le> y \<longleftrightarrow> (\<forall>q \<in> \<rat>. y < q \<longrightarrow> x < q)"
  by (meson Rats_dense_in_real less_asym less_le_trans not_less)

(*added to Convex_Euclidean_Space 2026-06*)
lemma limpt_of_convex:
  fixes S :: "'a::real_normed_vector set"
  assumes "convex S" "x \<in> S"
  shows "x islimpt S \<longleftrightarrow> S \<noteq> {x}"
proof -
  have "\<And>u. \<lbrakk>\<not> x islimpt S; u \<in> S\<rbrakk> \<Longrightarrow> u = x"
  using assms connected_imp_perfect convex_connected by blast
  with assms show ?thesis
    by (auto simp: islimpt_finite)
qed

(*added to Deriv 2026-06*)
lemma norm_vector_derivatives_le_within:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector" and g :: "real \<Rightarrow> 'b::real_normed_vector"
  assumes limpt: "x islimpt S"
    and fderiv: "(f has_vector_derivative f') (at x within S)"
    and gderiv: "(g has_vector_derivative g') (at x within S)"
    and ev: "eventually (\<lambda>y. norm (f y - f x) \<le> norm (g y - g x)) (at x within S)"
  shows "norm f' \<le> norm g'"
proof (rule tendsto_le)
  show nontrivial: "at x within S \<noteq> \<bottom>"
    using limpt trivial_limit_within by blast
  let ?f = "\<lambda>y. norm(inverse(y - x) *\<^sub>R (f y - f x))"
  let ?g = "\<lambda>y. norm(inverse(y - x) *\<^sub>R (g y - g x))"
  show "(?f \<longlongrightarrow> norm f') (at x within S)" 
       "(?g \<longlongrightarrow> norm g') (at x within S)"
    using fderiv gderiv has_vector_derivative_within_1D tendsto_norm by blast+
  show "\<forall>\<^sub>F x in at x within S. ?f x \<le> ?g x"
    using eventually_mono [OF ev] by (simp add: mult_left_mono)
qed

(*Added to Elementary_Metric_Spaces 2026-05*)
lemma diameter_translation:
  fixes a :: "'a::real_normed_vector"
  shows "diameter ((+) a ` S) = diameter S"
proof (cases "S = {}")
  case False
  then show ?thesis
    by (simp add: diameter_def image_comp split_def flip: image_paired_Times)
qed (simp add: diameter_def)

lemma diameter_eq_0:
  fixes S :: "'a::metric_space set"
  assumes "bounded S"
  shows "diameter S = 0 \<longleftrightarrow> S = {} \<or> (\<exists>a. S = {a})"
proof
  assume "diameter S = 0"
  then have "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x = y"
    using diameter_bounded_bound[OF assms] by auto
  then show "S = {} \<or> (\<exists>a. S = {a})"
    by (metis empty_iff insertI1 set_eq_iff singletonD)
next
  assume "S = {} \<or> (\<exists>a. S = {a})"
  then show "diameter S = 0"
    using diameter_empty diameter_singleton by auto
qed


(*Added to Elementary_Normed_Spaces 2026-05*)
lemma bounded_translation_eq [simp]:
  fixes a :: "'a :: real_normed_vector"
  shows "bounded ((+) a ` S) \<longleftrightarrow> bounded S"
  by (metis bounded_iff bounded_translation imageI norm_add_leD)

(*Added to Elementary_Metric_Spaces 2026-05*)
lemma bounded_cnj_image: "bounded (cnj ` S) = bounded S"
  by (auto simp: bounded_iff)

(*Added to Path_Connected 2026-05*)
lemma inside_translation:
  fixes a :: "'a :: real_normed_vector"
  shows "inside ((+) a ` S) = (+) a ` inside S"
proof (rule set_eqI)
  fix x :: 'a
  define y where "y \<equiv> x - a"
  then have xy: "x = a + y" by simp
  have homeo: "homeomorphism (- S) ((+) a ` (- S)) ((+) a) ((+) (- a))"
    using homeomorphism_symD homeomorphism_translation by blast
  have "connected_component_set (- ((+) a ` S)) x =
        (+) a ` connected_component_set (- S) y"
    using connected_component_set_homeomorphism[OF homeo]
    by (metis ComplD ComplI connected_component_eq_empty imageI image_is_empty translation_Compl
        xy)
  with xy show "(x \<in> inside ((+) a ` S)) = (x \<in> (+) a ` inside S)"
    by (auto simp: inside_def)
qed

(*Added to Path_Connected 2026-05*)
lemma inside_cnj_image:
  shows "inside (cnj ` S) = cnj ` inside S"
proof (rule set_eqI)
  fix x
  define y where "y \<equiv> cnj x"
  then have xy: "x = cnj y" by simp
  have homeo: "homeomorphism (- S) (cnj ` (- S)) (cnj) cnj"
    by (simp add: homeomorphism_def image_cnj_conv_vimage_cnj)
  have "connected_component_set (- (cnj ` S)) x = cnj ` connected_component_set (- S) y"
    using connected_component_set_homeomorphism[OF homeo]
    by (metis complex_cnj_cnj connected_component_eq_empty image_cnj_conv_vimage_cnj image_is_empty
        in_image_cnj_iff vimage_Compl y_def)
  with xy show "(x \<in> inside (cnj ` S)) = (x \<in> cnj ` inside S)"
    by (auto simp: inside_def bounded_cnj_image)
qed

(*Added to Path_Connected 2026-05*)
lemma loop_free_cnj: "loop_free (cnj \<circ> g) = loop_free g"
  by (simp add: inj_on_def linear_cnj loop_free_linear_image_eq)

(*Added to Equivalence_Lebesgue_Henstock_Integration 2026-05*)
lemma Re_absolutely_integrable_on:
  assumes "g absolutely_integrable_on S"
  shows "(\<lambda>t. Re (g t)) absolutely_integrable_on S"
  using absolutely_integrable_component [OF assms]
  by (metis (lifting) ext complex_inner_1_right)

(*Added to Equivalence_Lebesgue_Henstock_Integration 2026-05*)
lemma Im_absolutely_integrable_on:
  assumes "g absolutely_integrable_on S"
  shows "(\<lambda>t. Im (g t)) absolutely_integrable_on S"
  using absolutely_integrable_component [OF assms]
  by (metis (lifting) ext complex_inner_i_right)

(*Added to Equivalence_Measurable_On_Borel 2026-06*)
lemma measurable_bounded_by_integrable_imp_absolutely_integrable_ae:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f_meas: "f \<in> borel_measurable (lebesgue_on S)"
    and S_meas: "S \<in> sets lebesgue"
    and g_int: "g integrable_on S"
    and neg_T: "negligible T"
    and bound: "\<And>x. x \<in> S - T \<Longrightarrow> norm (f x) \<le> g x"
  shows "f absolutely_integrable_on S"
proof -
  have ST_meas: "S - T \<in> sets lebesgue"
    using S_meas neg_T negligible_imp_sets by (metis sets.Diff)
  have neg_ST: "negligible (S \<inter> T)"
    using neg_T by (meson Int_lower2 negligible_subset)
  have null_ST: "S \<inter> T \<in> null_sets (lebesgue_on S)"
    using null_sets_restrict_space[of S lebesgue "S \<inter> T"] S_meas neg_ST
    by (simp add: Int_commute negligible_iff_null_sets)
  have f_meas_ST: "f \<in> borel_measurable (lebesgue_on (S - T))"
    using borel_measurable_diff_null[OF null_ST S_meas] f_meas
    by (metis Diff_Diff_Int Diff_subset Int_absorb1)
  have g_int_ST: "g integrable_on (S - T)"
    using integrable_spike_set_eq[of "S - T" S g] g_int neg_ST
    by (simp add: Diff_Diff_Int)
  have "f absolutely_integrable_on (S - T)"
    by (rule measurable_bounded_by_integrable_imp_absolutely_integrable
        [OF f_meas_ST ST_meas g_int_ST bound])
  then show "f absolutely_integrable_on S"
    using absolutely_integrable_spike_set_eq[of "S - T" S f] neg_ST
    by (simp add: negligible_subset subset_iff)
qed

\<comment> \<open>All added to \<open>Complex\<close> 2026-05.\<close>
lemma dist_cnj [simp]: "dist (cnj a) (cnj b) = dist a b"
  by (metis complex_cnj_diff complex_mod_cnj dist_norm)

\<comment> \<open>Added to \<open>Elementary_Metric_Spaces\<close> 2026-05.\<close>
lemma diameter_image_cnj: "diameter (cnj ` S) = diameter S"
proof -
  have "(\<lambda>(x,y). dist x y) ` (cnj ` S \<times> cnj ` S) = (\<lambda>(x,y). dist x y) ` (S \<times> S)"
    by (force simp: image_iff)
  then show ?thesis
    by (simp add: diameter_def)
qed

(*Added to Starlike 2026-06*)
lemma convex_open_segment_cases:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "x \<in> closure S" "y \<in> closure S"
  shows "open_segment x y \<subseteq> rel_frontier S \<or> open_segment x y \<subseteq> rel_interior S"
proof -
  have seg_in_clos: "open_segment x y \<subseteq> closure S"
    using convex_closure[OF assms(1)] assms(2,3)
    by (meson convex_contains_segment segment_open_subset_closed subset_trans)
  show ?thesis
  proof (cases "open_segment x y \<inter> rel_interior S = {}")
    case True
    then show ?thesis
      using seg_in_clos by (auto simp: rel_frontier_def)
  next
    case False
    then obtain c where c: "c \<in> open_segment x y" "c \<in> rel_interior S"
      by auto
    have "open_segment x y \<subseteq> rel_interior S"
    proof -
      have xc: "open_segment x c \<subseteq> rel_interior S"
        using rel_interior_closure_convex_segment[OF assms(1) c(2) assms(2)]
        by (simp add: open_segment_commute)
      have cy: "open_segment c y \<subseteq> rel_interior S"
        using rel_interior_closure_convex_segment[OF assms(1) c(2) assms(3)]
        by simp
      from Un_open_segment[OF c(1)] xc c(2) cy
      show ?thesis by auto
    qed
    then show ?thesis by simp
  qed
qed

(*Added to Starlike 2026-06*)
lemma convex_open_segment_cases_alt:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "x \<in> closure S" "y \<in> closure S"
  shows "open_segment x y \<subseteq> frontier S \<or> open_segment x y \<subseteq> interior S"
proof (cases "interior S = {}")
  case True then show ?thesis
    by (metis Diff_empty assms convex_closure convex_contains_open_segment frontier_def)
next
  case False
  then have "rel_interior S = interior S" "rel_frontier S = frontier S"
    using rel_interior_nonempty_interior rel_frontier_nonempty_interior by auto
  with convex_open_segment_cases[OF assms] show ?thesis by simp
qed

\<comment> \<open>Added to \<open>Absolute_Continuity\<close> 2026-05.\<close>
lemma absolutely_continuous_on_reflect:
  assumes "absolutely_continuous_on {S - b..S - a} f"
  shows "absolutely_continuous_on {a..b} (f \<circ> (-) S)"
proof -
  show ?thesis
    unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
  proof (intro allI impI)
    fix \<epsilon> :: real assume "\<epsilon> > 0"
    with assms obtain \<delta> where "\<delta> > 0"
      and \<delta>: "\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> {S - b..S - a} \<Longrightarrow> (\<Sum>k\<in>d. content k) < \<delta> \<Longrightarrow>
             (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>"
      unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def by meson
    show "\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> {a..b} \<and>
          (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
          (\<Sum>k\<in>d. norm ((f \<circ> (-) S) (Sup k) - (f \<circ> (-) S) (Inf k))) < \<epsilon>"
    proof (intro exI conjI allI impI)
      show "\<delta> > 0" by fact
      fix d T assume "d division_of T \<and> T \<subseteq> {a..b} \<and>
          (\<Sum>k\<in>d. content k) < \<delta>"
      then have dv: "d division_of T" and sub: "T \<subseteq> {a..b}"
        and sm: "(\<Sum>k\<in>d. content k) < \<delta>" by auto
      have sub': "(-) S ` T \<subseteq> {S - b..S - a}"
        using sub by auto
      have inj: "inj_on ((`) ((-) S)) d"
        by (simp add: inj_on_image)
      have content_eq: "content ((-) S ` k) = content k" if "k \<in> d" for k
      proof -
        obtain c e :: real where ce: "k = cbox c e" and "c \<le> e"
          using \<open>k \<in> d\<close> dv
          by (metis atLeastatMost_empty_iff box_real(2) cbox_division_memE)
        then show "content ((-) S ` k) = content k"
          unfolding ce by (simp add: Henstock_Kurzweil_Integration.content_real)
      qed
      have osc_eq: "(\<Sum>k\<in>d. norm ((f \<circ> (-) S) (Sup k) - (f \<circ> (-) S) (Inf k))) =
                    (\<Sum>k'\<in>(`) ((-) S) ` d. norm (f (Sup k') - f (Inf k')))"
      proof -
        have "(\<Sum>k'\<in>(`) ((-) S) ` d. norm (f (Sup k') - f (Inf k'))) =
              (\<Sum>k\<in>d. norm (f (Sup ((-) S ` k)) - f (Inf ((-) S ` k))))"
          using sum.reindex[OF inj] by simp
        also have "\<dots> = (\<Sum>k\<in>d. norm (f (S - Inf k) - f (S - Sup k)))"
        proof (intro sum.cong refl)
          fix k assume "k \<in> d"
          then obtain c e :: real where ce: "k = cbox c e" and "c \<le> e"
            by (metis atLeastatMost_empty_iff box_real(2) cbox_division_memE dv)
          then show "norm (f (Sup ((-) S ` k)) - f (Inf ((-) S ` k))) =
                     norm (f (S - Inf k) - f (S - Sup k))"
            unfolding ce 
            by (auto simp: image_affinity_atLeastAtMost cSup_atLeastAtMost cInf_atLeastAtMost)
        qed
        also have "\<dots> = (\<Sum>k\<in>d. norm ((f \<circ> (-) S) (Sup k) - (f \<circ> (-) S) (Inf k)))"
          by (intro sum.cong refl) (simp add: norm_minus_commute)
        finally show ?thesis by simp
      qed
      have sm': "(\<Sum>k\<in>(`) ((-) S) ` d. content k) < \<delta>"
        by (metis content_eq inj sm sum.reindex_cong)
      show "(\<Sum>k\<in>d. norm ((f \<circ> (-) S) (Sup k) - (f \<circ> (-) S) (Inf k))) < \<epsilon>"
        unfolding osc_eq using \<delta>[OF division_of_reflect[OF dv] sub' sm'] .
    qed
  qed
qed

\<comment> \<open>Added to \<open>Absolute_Continuity\<close> 2026-05.\<close>
lemma fundamental_theorem_of_calculus_strong:
  fixes f :: "real \<Rightarrow> 'a::banach" and f' :: "real \<Rightarrow> 'a"
  assumes "countable S"
    and "a \<le> b"
    and "continuous_on {a..b} f"
    and "\<And>x. x \<in> {a..b} - S \<Longrightarrow>
      (f has_vector_derivative f' x) (at x within {a..b})"
  shows "(f' has_integral (f b - f a)) {a..b}"
proof (intro fundamental_theorem_of_calculus_Bartle assms)
  show "negligible S"
    by (simp add: assms(1) countable_imp_negligible)
next
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  obtain \<sigma>::"nat\<Rightarrow>real" and T where \<sigma>: "inj_on \<sigma> T" and Seq: "S = \<sigma> ` T"
    by (meson assms(1) countable_as_injective_image_subset)

  \<comment> \<open>Left inverse of $\sigma$ on T\<close>
  define n where "n \<equiv> the_inv_into T \<sigma>"

  \<comment> \<open>For each x, obtain $d(x) > 0$ with the continuity bound\<close>
  have "\<exists>d. d > 0 \<and>
            (x \<in> {a..b} \<and> x \<in> \<sigma> ` T \<longrightarrow> (\<forall>y. \<bar>y - x\<bar> < d \<and> y \<in> {a..b} \<longrightarrow> norm (f y - f x) \<le> \<epsilon> / 2^(4 + n x)))" 
      for x
  proof (cases "x \<in> {a..b}")
    case False
    then show ?thesis by (intro exI[of _ 1]) auto
  next
    case x_ab: True
    show ?thesis
    proof (cases "x \<in> \<sigma> ` T")
      case False
      then show ?thesis by (intro exI[of _ 1]) auto
    next
      case True
      have cont: "continuous_on {a..b} f" by fact
      have eps_pos: "\<epsilon> / 2^(4 + n x) > 0"
        using \<open>0 < \<epsilon>\<close> by simp
      obtain \<delta> where "\<delta> > 0"
        and "\<And>y. y \<in> {a..b} \<Longrightarrow> dist y x < \<delta> \<Longrightarrow> dist (f y) (f x) < \<epsilon> / 2^(4 + n x)"
        using cont[unfolded continuous_on_iff] x_ab eps_pos by blast
      then show ?thesis
        by (metis dist_norm dist_real_def less_eq_real_def)
    qed
  qed
  then obtain d :: "real \<Rightarrow> real" where d_pos: "\<And>x. d x > 0"
    and d_bound: "\<And>x. x \<in> {a..b} \<Longrightarrow> x \<in> \<sigma> ` T \<Longrightarrow>
      (\<forall>y. \<bar>y - x\<bar> < d x \<and> y \<in> {a..b} \<longrightarrow> norm (f y - f x) \<le> \<epsilon> / 2^(4 + n x))"
    by metis

  show "\<exists>g. gauge g \<and> (\<forall>p. p tagged_partial_division_of cbox a b \<and> g fine p \<and> fst ` p \<subseteq> S \<longrightarrow> norm (\<Sum>(x, k)\<in>p. f (\<Squnion> k) - f (\<Sqinter> k)) < \<epsilon>)"
  proof (intro exI conjI allI impI)
    show "gauge (\<lambda>x. ball x (d x))"
      using d_pos by (intro gauge_ball_dependent) auto
  next
    fix p assume p_hyp: "p tagged_partial_division_of cbox a b \<and>
      (\<lambda>x. ball x (d x)) fine p \<and> fst ` p \<subseteq> S"
    then have p_div: "p tagged_partial_division_of cbox a b"
      and p_fine: "(\<lambda>x. ball x (d x)) fine p" and p_tags: "fst ` p \<subseteq> S"
      by auto
    have p_finite: "finite p"
      using tagged_partial_division_ofD(1)[OF p_div] .
    have finite_snd: "finite {k. (x,k) \<in> p \<and> P x k}" for P x
        using finite_subset finite_imageI[OF p_finite]
        by (metis (mono_tags, lifting) image_eqI mem_Collect_eq snd_conv subsetI)

    show "norm (\<Sum>(x, k)\<in>p. f (\<Squnion> k) - f (\<Sqinter> k)) < \<epsilon>"
    proof -
      let ?S' = "{(x,k). (x,k) \<in> p \<and> x \<in> \<sigma> ` T \<and> content k \<noteq> 0}"
      let ?t = "norm (\<Sum>(x,k)\<in>?S'. - (f (\<Squnion> k) - f (\<Sqinter> k)))"
      \<comment> \<open>Show that zero-content terms vanish, so the sum over @{term p} equals the sum over @{term "?S'"}\<close>
      have zero_content: "f (\<Squnion> k) - f (\<Sqinter> k) = 0"
        if "(x, k) \<in> p" "content k = 0" for x k
      proof -
        from tagged_partial_division_ofD(4)[OF p_div that(1)]
        obtain u v where k_eq: "k = cbox u v" by auto
        from tagged_partial_division_ofD(2)[OF p_div that(1)]
        have "x \<in> k" .
        then have "u \<le> v" using k_eq by (auto simp: mem_box)
        with that(2) have "u = v"
          using k_eq by (auto simp: content_cbox_if Basis_real_def)
        then have "\<Squnion> k = \<Sqinter> k"
          using k_eq \<open>u \<le> v\<close> by (simp add: Sup_atLeastAtMost Inf_atLeastAtMost)
        then show ?thesis by simp
      qed
      have sum_eq: "(\<Sum>(x,k)\<in>p. f (\<Squnion> k) - f (\<Sqinter> k)) =
                    (\<Sum>(x,k)\<in>?S'. f (\<Squnion> k) - f (\<Sqinter> k))"
      proof (rule sum.same_carrierI[OF p_finite _ _ _ _ refl])
        show "?S' \<subseteq> p" by auto
        show "p \<subseteq> p" by auto
      next
        fix a assume "a \<in> p - p"
        then show "(case a of (x, k) \<Rightarrow> f (\<Squnion> k) - f (\<Sqinter> k)) = 0" by auto
      next
        fix b assume "b \<in> p - ?S'"
        then obtain x k where bxk: "b = (x, k)" "(x, k) \<in> p"
          and extra: "x \<notin> \<sigma> ` T \<or> content k = 0"
          by (cases b) auto
        have "x \<in> \<sigma> ` T"
          using p_tags bxk Seq by (force simp: image_iff)
        with extra have "content k = 0" by blast
        then show "(case b of (x, k) \<Rightarrow> f (\<Squnion> k) - f (\<Sqinter> k)) = 0"
          using zero_content[OF bxk(2)] bxk(1) by simp
      qed
      have neg_eq: "- (\<Sum>(x,k)\<in>p. f (\<Squnion> k) - f (\<Sqinter> k)) =
                    (\<Sum>(x,k)\<in>?S'. - (f (\<Squnion> k) - f (\<Sqinter> k)))"
        unfolding sum_eq sum_negf[symmetric] by (simp add: case_prod_unfold)
      have "norm (\<Sum>(x,k)\<in>p. f (\<Squnion> k) - f (\<Sqinter> k)) = ?t"
        by (subst neg_eq[symmetric], subst norm_minus_cancel[symmetric]) (rule refl)
      also have "\<dots> \<le> (\<Sum>(x,k)\<in>?S'. \<epsilon>/2 ^ (3 + n x))"
      proof (rule sum_norm_le)
        fix z assume z_in: "z \<in> ?S'"
        obtain x k where z_eq: "z = (x, k)" and xk_in: "(x, k) \<in> p"
          and x_img: "x \<in> \<sigma> ` T" and k_nz: "content k \<noteq> 0"
          using z_in by (cases z) auto
        obtain u v where k_eq: "k = cbox u v" and x_in_k: "x \<in> k"
          using tagged_partial_division_ofD p_div xk_in by metis
        then have uv: "u \<le> v" using k_eq by (auto simp: mem_box)
        from k_nz have "u < v"
          using k_eq uv by (auto simp: content_cbox_if Basis_real_def)
        have sup_k: "\<Squnion> k = v" and inf_k: "\<Sqinter> k = u"
          using k_eq uv by (simp_all add: Sup_atLeastAtMost Inf_atLeastAtMost)
        have k_sub: "k \<subseteq> cbox a b"
          using tagged_partial_division_ofD(3)[OF p_div xk_in] .
        have x_ab: "x \<in> {a..b}" using x_in_k k_sub by auto
        have u_ab: "u \<in> {a..b}" and v_ab: "v \<in> {a..b}"
          using k_sub k_eq \<open>u \<le> v\<close> by auto
        \<comment> \<open>From fineness, u and v are within @{term \<open>d x\<close>} of x\<close>
        have k_ball: "k \<subseteq> ball x (d x)"
          using fineD[OF p_fine xk_in] .
        have "u \<in> ball x (d x)" and "v \<in> ball x (d x)"
          using k_ball k_eq \<open>u \<le> v\<close> by auto
        then have du: "\<bar>u - x\<bar> < d x" and dv: "\<bar>v - x\<bar> < d x"
          by (auto simp: mem_ball dist_real_def)

        have bnd_v: "norm (f v - f x) \<le> \<epsilon> / 2^(4 + n x)"
          using d_bound[OF x_ab x_img, rule_format, of v] dv v_ab by auto
        have bnd_u: "norm (f u - f x) \<le> \<epsilon> / 2^(4 + n x)"
          using d_bound[OF x_ab x_img, rule_format, of u] du u_ab by auto

        have bnd_xu: "norm (f x - f u) \<le> \<epsilon> / 2^(4 + n x)"
          using bnd_u by (subst norm_minus_commute) 
        have bound: "norm (-(f (\<Squnion> k) - f (\<Sqinter> k))) \<le> \<epsilon>/2 ^ (3 + n x)"
        proof -
          have "norm (-(f (\<Squnion> k) - f (\<Sqinter> k))) = norm (f (\<Squnion> k) - f (\<Sqinter> k))"
            by (rule norm_minus_cancel)
          also have "\<dots> = norm (f v - f u)"
            by (simp add: sup_k inf_k)
          also have "\<dots> = norm ((f v - f x) + (f x - f u))" by simp
          also have "\<dots> \<le> norm (f v - f x) + norm (f x - f u)"
            by (rule norm_triangle_ineq)
          also have "\<dots> \<le> \<epsilon> / 2^(4 + n x) + \<epsilon> / 2^(4 + n x)"
            by (intro add_mono bnd_v bnd_xu)
          also have "\<dots> = \<epsilon>/2 ^ (3 + n x)"
          proof -
            have "(2::real) ^ (4 + n x) = 2 * 2 ^ (3 + n x)" by (simp add: power_add)
            then show ?thesis by (simp add: field_simps)
          qed
          finally show ?thesis .
        qed
        show "norm (case z of (x, k) \<Rightarrow> - (f (\<Squnion> k) - f (\<Sqinter> k))) \<le>
                      (case z of (x, k) \<Rightarrow> \<epsilon>/2 ^ (3 + n x))"
          using bound z_eq by simp
      qed
      also have "\<dots> < \<epsilon>"
      proof -
        let ?tags = "fst ` ?S'"
        have S'_finite: "finite ?S'"
          by (simp add: case_prod_unfold p_finite)
        have tags_finite: "finite ?tags" using S'_finite by blast

        \<comment> \<open>Group the sum by first component (the tag) via Sigma decomposition\<close>
        define B where "B x \<equiv> {k. (x,k) \<in> ?S'}" for x
        have B_finite: "finite (B x)" for x
          using B_def finite_snd by force
        have S'_Sigma: "?S' = (SIGMA x:?tags. B x)"
          unfolding B_def by force

        have reduce: "(\<Sum>x\<in>?tags. real (card (B x)) / 2 ^ n x) \<le> 4 \<Longrightarrow>
              (\<Sum>(x,k)\<in>?S'. \<epsilon>/2 ^ (3 + n x)) < \<epsilon>"
        proof (rule order_le_less_trans[of _ "\<epsilon>/2"])
          assume bound: "(\<Sum>x\<in>?tags. real (card (B x)) / 2 ^ n x) \<le> 4"
            \<comment> \<open>Combine\<close>
          have "(\<Sum>(x,k)\<in>?S'. \<epsilon>/2 ^ (3 + n x)) =
                (\<Sum>(x,k)\<in>(SIGMA x:?tags. B x). \<epsilon>/2 ^ (3 + n x))"
            using S'_Sigma by presburger
          also have "\<dots> = (\<Sum>x\<in>?tags. (\<Sum>k\<in>B x. \<epsilon>/2 ^ (3 + n x)))"
            by (metis (no_types, lifting) ext B_finite sum.Sigma tags_finite)
          also have "\<dots> = (\<epsilon> / 8) * (\<Sum>x\<in>?tags. real (card (B x)) / 2 ^ n x)"
            by (simp add: power_add sum_distrib_left field_simps)
          also have "\<dots> \<le> (\<epsilon> / 8) * 4"
            using \<open>0 < \<epsilon>\<close> bound by (intro mult_left_mono) auto
          also have "\<dots> = \<epsilon>/2" by simp
          finally show "(\<Sum>(x,k)\<in>?S'. \<epsilon>/2 ^ (3 + n x)) \<le> \<epsilon>/2" .
        qed (use \<open>0 < \<epsilon>\<close> in auto)
        show ?thesis
        proof (rule reduce)
          show "(\<Sum>x\<in>?tags. real (card (B x)) / 2 ^ n x) \<le> 4"
          proof (rule order_trans[where y="(\<Sum>x\<in>\<sigma> ` T \<inter> fst ` p. real (card (B x)) / 2 ^ n x)"])
            show "(\<Sum>x\<in>?tags. real (card (B x)) / 2 ^ n x) \<le>
                  (\<Sum>x\<in>\<sigma> ` T \<inter> fst ` p. real (card (B x)) / 2 ^ n x)"
            proof (rule sum_mono2)
              show "finite (\<sigma> ` T \<inter> fst ` p)"
                using p_finite by (auto intro: finite_Int finite_imageI)
              show "?tags \<subseteq> \<sigma> ` T \<inter> fst ` p"
                by force
              show "\<And>i. i \<in> \<sigma> ` T \<inter> fst ` p - ?tags \<Longrightarrow> 0 \<le> real (card (B i)) / 2 ^ n i"
                by (auto intro: divide_nonneg_nonneg)
            qed
            show "(\<Sum>x\<in>\<sigma> ` T \<inter> fst ` p. real (card (B x)) / 2 ^ n x) \<le> 4"
            proof (rule order_trans[where y="(\<Sum>x\<in>\<sigma> ` T \<inter> fst ` p. 2 / 2 ^ n x)"])
              show "(\<Sum>x\<in>\<sigma> ` T \<inter> fst ` p. real (card (B x)) / 2 ^ n x) \<le>
                    (\<Sum>x\<in>\<sigma> ` T \<inter> fst ` p. 2 / 2 ^ n x)"
              proof (rule sum_mono)
                fix x assume "x \<in> \<sigma> ` T \<inter> fst ` p"
                show "real (card (B x)) / 2 ^ n x \<le> 2 / 2 ^ n x"
                proof (rule divide_right_mono)
                  show "real (card (B x)) \<le> 2"
                  proof -
                    have "card (B x) \<le> 2"
                    proof -
                      \<comment> \<open>Classify each interval by whether @{term \<open>\<Sqinter> k < x\<close>} (True).\<close>
                      \<comment> \<open>This is injective: two intervals in the same class have overlapping interiors.\<close>
                      define h where "h k = (\<Sqinter> k < x)" for k :: "real set"
                      have disj: "interior k1 \<inter> interior k2 = {}"
                        if "k1 \<in> B x" "k2 \<in> B x" "k1 \<noteq> k2" for k1 k2
                        using that tagged_partial_division_ofD(5)[OF p_div] by (force simp: B_def)
                      have x_in: "x \<in> k" if "k \<in> B x" for k
                        using that tagged_partial_division_ofD(2)[OF p_div] by (force simp: B_def)
                      have is_cbox: "\<exists>u v. k = cbox u v \<and> u < v" if "k \<in> B x" for k
                        using that tagged_partial_division_ofD(4)[OF p_div] content_real_eq_0 not_less
                        by (force simp: B_def)
                      have "inj_on h (B x)"
                      proof (rule inj_onI)
                        fix k1 k2 assume k1B: "k1 \<in> B x" and k2B: "k2 \<in> B x"
                          and heq: "h k1 = h k2"
                        show "k1 = k2"
                        proof (rule ccontr)
                          assume neq: "k1 \<noteq> k2"
                          from is_cbox[OF k1B] obtain u1 v1
                            where k1: "k1 = cbox u1 v1" "u1 < v1" by auto
                          from is_cbox[OF k2B] obtain u2 v2
                            where k2: "k2 = cbox u2 v2" "u2 < v2" by auto
                          have x1: "u1 \<le> x" "x \<le> v1"
                            using x_in[OF k1B] k1(1) by (auto simp: mem_box)
                          have x2: "u2 \<le> x" "x \<le> v2"
                            using x_in[OF k2B] k2(1) by (auto simp: mem_box)
                          have int1: "interior k1 = {u1<..<v1}"
                            using k1(1) by (simp add: interior_cbox box_real)
                          have int2: "interior k2 = {u2<..<v2}"
                            using k2(1) by (simp add: interior_cbox box_real)
                          have disjoint: "{u1<..<v1} \<inter> {u2<..<v2} = {}"
                            using disj[OF k1B k2B neq] int1 int2 by simp
                          then have disjoint': "{max u1 u2 <..< min v1 v2} = {}"
                            by (simp add: Int_greaterThanLessThan)
                          have inf1: "\<Sqinter> k1 = u1" using k1 x1
                            by (simp add: Inf_atLeastAtMost)
                          have inf2: "\<Sqinter> k2 = u2" using k2 x2
                            by (simp add: Inf_atLeastAtMost)
                          \<comment> \<open>Both in the same class: show max u1 u2 < min v1 v2, contradicting disjointness.\<close>
                          show False
                            using heq inf1 inf2 x1 x2 k1 k2 disjoint' by (force simp add: h_def)
                        qed
                      qed
                      have "card (B x) = card (h ` B x)"
                        using card_image[OF \<open>inj_on h (B x)\<close>] by simp
                      also have "\<dots> \<le> card (UNIV :: bool set)"
                        by (intro card_mono) auto
                      also have "\<dots> = 2" by (rule card_UNIV_bool)
                      finally show ?thesis .
                    qed
                    then show ?thesis by auto
                  qed
                next
                  show "(0::real) \<le> 2 ^ n x" by simp
                qed
              qed
            next
              show "(\<Sum>x\<in>\<sigma> ` T \<inter> fst ` p. 2 / (2::real) ^ n x) \<le> 4"
              proof -
                have A_finite: "finite (\<sigma> ` T \<inter> fst ` p)"
                  using p_finite by (auto intro: finite_Int finite_imageI)
                have n_inj: "inj_on n (\<sigma> ` T \<inter> fst ` p)"
                  by (simp add: \<sigma> inj_on_Int inj_on_the_inv_into n_def)
                have nA_finite: "finite (n ` (\<sigma> ` T \<inter> fst ` p))" using A_finite by auto
                \<comment> \<open>Directly prove bound on the reindexed sum\<close>
                have "(\<Sum>i\<in>n ` (\<sigma> ` T \<inter> fst ` p). 2 / (2::real) ^ i) \<le> 4"
                proof (cases "n ` (\<sigma> ` T \<inter> fst ` p) = {}")
                  case False
                  have "(\<Sum>i\<in>n ` (\<sigma> ` T \<inter> fst ` p). 2 / (2::real) ^ i) \<le> (\<Sum>i\<le>Max (n ` (\<sigma> ` T \<inter> fst ` p)). 2 / 2 ^ i)"
                  proof (rule sum_mono2)
                    show "finite {..Max (n ` (\<sigma> ` T \<inter> fst ` p))}" by simp
                    show "n ` (\<sigma> ` T \<inter> fst ` p) \<subseteq> {..Max (n ` (\<sigma> ` T \<inter> fst ` p))}"
                      using nA_finite by (auto intro: Max_ge)
                  qed simp
                  also have "\<dots> = 2 * (\<Sum>i\<le>Max (n ` (\<sigma> ` T \<inter> fst ` p)). (1/2) ^ i)"
                    by (simp add: sum_distrib_left power_divide)
                  also have "\<dots> = 2 * ((1 - (1/2) ^ Suc (Max (n ` (\<sigma> ` T \<inter> fst ` p)))) / (1 - 1/2))"
                    using sum_gp0[of "1/2::real" "Max (n ` (\<sigma> ` T \<inter> fst ` p))"] by simp
                  also have "\<dots> \<le> 2 * (1 / (1 - 1/(2::real)))"
                    by (intro mult_left_mono divide_right_mono diff_mono) auto
                  also have "\<dots> = (4::real)" by simp
                  finally show ?thesis .
                qed auto
                then show ?thesis
                  using sum.reindex[OF n_inj, of "\<lambda>i. 2 / (2::real) ^ i"] by auto
              qed
            qed
          qed
        qed
      qed
      finally show ?thesis .
    qed
  qed
qed

\<comment> \<open>Added to \<open>Absolute_Continuity\<close> 2026-05.\<close>
lemma fundamental_theorem_of_calculus_interior_strong:
  fixes f :: "real \<Rightarrow> 'a::banach" and f' :: "real \<Rightarrow> 'a"
  assumes "countable S"
    and "a \<le> b"
    and "continuous_on {a..b} f"
    and f': "\<And>x. x \<in> {a<..<b} - S \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
  shows "(f' has_integral (f b - f a)) {a..b}"
proof -
  have "(f' has_integral (f b - f a)) {a..b}"
  proof (rule fundamental_theorem_of_calculus_strong[where S = "insert a (insert b S)"])
    show "countable (insert a (insert b S))"
      using assms(1) by auto
    show "a \<le> b" by fact
    show "continuous_on {a..b} f" by fact
    fix x assume "x \<in> {a..b} - insert a (insert b S)"
    with f' have "(f has_vector_derivative f' x) (at x)"
      by auto
    then show "(f has_vector_derivative f' x) (at x within {a..b})"
      using has_vector_derivative_at_within by blast
  qed
  then show ?thesis .
qed

(*Added to Henstock 2026-06*)
lemma integral_has_vector_derivative_pointwise:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "f integrable_on {a..b}"
    and "x \<in> {a..b}"
    and "continuous (at x within {a..b}) f"
  shows "((\<lambda>u. integral {a..u} f) has_vector_derivative f x) (at x within {a..b})"
  using integral_has_vector_derivative_continuous_at[where S="{}", simplified] assms by auto

(*Added to Absolute_Continuity 2026-06*)
lemma has_integral_substitution_strong:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and g g' :: "real \<Rightarrow> real"
  assumes "countable k"
    and intf: "f integrable_on {c..d}"
    and contg: "continuous_on {a..b} g"
    and g: "g \<in> {a..b} \<rightarrow> {c..d}"
    and derg: "\<And>x. x \<in> {a..b} - k \<Longrightarrow>
      (g has_vector_derivative g' x) (at x within {a..b}) \<and> continuous (at (g x) within {c..d}) f"
    and "a \<le> b" and "c \<le> d" and "g a \<le> g b"
  shows "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral integral {g a..g b} f) {a..b}"
proof -
  define ff where "ff \<equiv> \<lambda>x. integral {c..x} f"
  have ff_cont: "continuous_on {c..d} ff"
    unfolding ff_def using indefinite_integral_continuous_1[OF assms(2)] .
  have fg_cont: "continuous_on {a..b} (ff \<circ> g)"
    using continuous_on_compose2[OF ff_cont contg] g unfolding comp_def by blast
  have ftc: "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral ((ff \<circ> g) b - (ff \<circ> g) a)) {a..b}"
  proof (rule fundamental_theorem_of_calculus_interior_strong[where S = k])
    show "countable k" by fact
    show "a \<le> b" by fact
    show "continuous_on {a..b} (ff \<circ> g)" by fact
    fix x assume xk: "x \<in> {a<..<b} - k"
    have g_deriv: "(g has_vector_derivative g' x) (at x within {a..b})"
      and f_cont: "continuous (at (g x) within {c..d}) f"
      using derg xk by auto
    have ff_deriv: "(ff has_vector_derivative f (g x)) (at (g x) within {c..d})"
      unfolding ff_def
      using integral_has_vector_derivative_pointwise[OF assms(2) _ f_cont] 
      using g xk by (auto simp: Pi_iff)
    have ff_deriv': "(ff has_vector_derivative f (g x)) (at (g x) within g ` {a..b})"
      using has_vector_derivative_within_subset[OF ff_deriv] g by (simp add: funcset_image)

    have chain: "((ff \<circ> g) has_vector_derivative g' x *\<^sub>R f (g x)) (at x within {a..b})"
      using vector_diff_chain_within[OF g_deriv ff_deriv'] .
    \<comment> \<open>x is in the interior, so at x within {a..b} = at x\<close>
    have "x \<in> interior {a..b}"
      using xk by (simp add: interior_atLeastAtMost_real)
    with chain at_within_interior 
    show "((ff \<circ> g) has_vector_derivative g' x *\<^sub>R f (g x)) (at x)"
      by metis
  qed
  have "(ff \<circ> g) b - (ff \<circ> g) a = integral {g a..g b} f"
  proof -
    obtain c_ga: "c \<le> g a" and "c \<le> g b" "g b \<le> d"
      by (metis Pi_mem g \<open>a \<le> b\<close> atLeastAtMost_iff nle_le)
    then have "f integrable_on {c..g b}"
      using integrable_on_subinterval[OF assms(2), of c "g b"] by auto
    then have combine: "integral {c..g a} f + integral {g a..g b} f = integral {c..g b} f"
      using Henstock_Kurzweil_Integration.integral_combine[OF c_ga \<open>g a \<le> g b\<close>] by auto
    have "(ff \<circ> g) b - (ff \<circ> g) a = integral {c..g b} f - integral {c..g a} f"
      by (simp add: ff_def)
    also have "\<dots> = integral {g a..g b} f"
      using combine by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  with ftc show ?thesis by simp
qed

(*Added to Absolute_Continuity 2026-06*)
text \<open>Composition of Lipschitz with absolutely continuous is absolutely continuous.\<close>
lemma absolutely_continuous_on_Lipschitz_compose: 
  fixes g :: "real \<Rightarrow> 'a::euclidean_space" and \<phi> :: "real \<Rightarrow> real"
  assumes ac: "absolutely_continuous_on {a..b} \<phi>"
    and lip: "\<And>x y. x \<in> \<phi> ` {a..b} \<Longrightarrow> y \<in> \<phi> ` {a..b} \<Longrightarrow> norm (g x - g y) \<le> L * \<bar>x - y\<bar>"
    and "0 \<le> L"
  shows "absolutely_continuous_on {a..b} (g \<circ> \<phi>)"
proof -
  have ac_\<phi>: "absolutely_setcontinuous_on (\<lambda>k. \<phi> (\<Squnion> k) - \<phi> (\<Sqinter> k)) {a..b}"
    using ac unfolding absolutely_continuous_on_def .
  show ?thesis unfolding absolutely_continuous_on_def
    unfolding absolutely_setcontinuous_on_def
  proof (intro allI impI)
    fix \<epsilon> :: real assume "0 < \<epsilon>"
    have pos: "0 < \<epsilon> / (L + 1)" using \<open>0 < \<epsilon>\<close> \<open>0 \<le> L\<close> by (auto intro: divide_pos_pos)
    then obtain \<delta> where "0 < \<delta>" and \<delta>:
      "\<And>d T. d division_of T \<Longrightarrow> T \<subseteq> {a..b} \<Longrightarrow>
        (\<Sum>k\<in>d. content k) < \<delta> \<Longrightarrow>
        (\<Sum>k\<in>d. norm (\<phi> (\<Squnion> k) - \<phi> (\<Sqinter> k))) < \<epsilon> / (L + 1)"
      using ac_\<phi>[unfolded absolutely_setcontinuous_on_def] by meson
    show "\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> {a..b} \<and>
      (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
      (\<Sum>k\<in>d. norm ((g \<circ> \<phi>) (\<Squnion> k) - (g \<circ> \<phi>) (\<Sqinter> k))) < \<epsilon>"
    proof (intro exI conjI allI impI)
      show "0 < \<delta>" by fact
    next
      fix d :: "real set set" and T
      assume hyp: "d division_of T \<and> T \<subseteq> {a..b} \<and> (\<Sum>k\<in>d. content k) < \<delta>"
      then have divi: "d division_of T" and sub: "T \<subseteq> {a..b}"
        and cont: "(\<Sum>k\<in>d. content k) < \<delta>"
        by auto
      have K_in: "\<Squnion> K \<in> {a..b}" "\<Sqinter> K \<in> {a..b}" if Kd: "K \<in> d" for K
      proof -
        obtain u v where Kuv: "K = cbox u v" and ne: "u \<le> v"
          by (metis Kd atLeastatMost_empty_iff box_real(2) cbox_division_memE divi)
        then obtain uv_in: "u \<in> {a..b}" "v \<in> {a..b}" 
          by (smt (verit, best) Kd divi division_of_def in_mono mem_box_real(2) sub)
        moreover have "\<Squnion> K = v" "\<Sqinter> K = u"
          unfolding Kuv box_real using ne interval_bounds_real by auto
        ultimately show "\<Squnion> K \<in> {a..b}" "\<Sqinter> K \<in> {a..b}" by auto
      qed
      have term_bound: "norm ((g \<circ> \<phi>) (\<Squnion> K) - (g \<circ> \<phi>) (\<Sqinter> K)) \<le> L * norm (\<phi> (\<Squnion> K) - \<phi> (\<Sqinter> K))"
        if "K \<in> d" for K
        using K_in lip that by auto
      have "(\<Sum>k\<in>d. norm ((g \<circ> \<phi>) (\<Squnion> k) - (g \<circ> \<phi>) (\<Sqinter> k)))
        \<le> (\<Sum>k\<in>d. L * norm (\<phi> (\<Squnion> k) - \<phi> (\<Sqinter> k)))"
        using term_bound by (intro sum_mono)
      also have "\<dots> = L * (\<Sum>k\<in>d. norm (\<phi> (\<Squnion> k) - \<phi> (\<Sqinter> k)))"
        by (simp add: sum_distrib_left)
      also have "\<dots> < \<epsilon>"
      proof (cases "L = 0")
        case True then show ?thesis using \<open>0 < \<epsilon>\<close> by simp
      next
        case False
        then have "0 < L" using \<open>0 \<le> L\<close> by linarith
        have "L * (\<Sum>k\<in>d. norm (\<phi> (\<Squnion> k) - \<phi> (\<Sqinter> k))) < L * (\<epsilon> / (L + 1))"
          using \<delta>[OF divi sub cont] \<open>0 < L\<close> by (intro mult_strict_left_mono) auto
        also have "\<dots> \<le> \<epsilon>"
          using \<open>0 < \<epsilon>\<close> \<open>0 \<le> L\<close> by (simp add: field_simps)
        finally show ?thesis .
      qed
      finally show "(\<Sum>k\<in>d. norm ((g \<circ> \<phi>) (\<Squnion> k) - (g \<circ> \<phi>) (\<Sqinter> k))) < \<epsilon>" .
    qed
  qed
qed

(*Added to Absolute_Continuity 2026-06*)
text \<open>1D substitution for absolutely continuous monotone functions.\<close>
lemma has_integral_substitution_ac:
  fixes \<phi> :: "real \<Rightarrow> real" and \<phi>' :: "real \<Rightarrow> real" and f :: "real \<Rightarrow> real"
  assumes "a \<le> b" "\<phi> a \<le> \<phi> b"
    and \<phi>: "absolutely_continuous_on {a..b} \<phi>"
    and "negligible S"
    and vec: "\<And>t. t \<in> {a..b} - S \<Longrightarrow> (\<phi> has_vector_derivative \<phi>' t) (at t)"
    and contf: "continuous_on {\<phi> a..\<phi> b} f"
    and mono: "\<And>x y. x \<in> {a..b} \<Longrightarrow> y \<in> {a..b} \<Longrightarrow> x \<le> y \<Longrightarrow> \<phi> x \<le> \<phi> y"
  shows "((\<lambda>t. \<phi>' t * f (\<phi> t)) has_integral (integral {\<phi> a..\<phi> b} f)) {a..b}"
proof -
  define ff where "ff \<equiv> \<lambda>x. integral {\<phi> a..x} f"
  have f_int: "f integrable_on {\<phi> a..\<phi> b}"
    using integrable_continuous_real contf by blast
  \<comment> \<open>f is bounded — needed for Lipschitz property of ff\<close>
  obtain M where M_pos: "0 \<le> M" and M_bound: "\<And>t. t \<in> {\<phi> a..\<phi> b} \<Longrightarrow> \<bar>f t\<bar> \<le> M"
    using continuous_on_compact_bound[of "{\<phi> a..\<phi> b}" f, OF _ contf]
    by (auto simp: norm_real)
  \<comment> \<open>ff is Lipschitz\<close>
  have ff_lip_half: "norm (ff x - ff y) \<le> M * \<bar>x - y\<bar>"
    if x: "x \<in> {\<phi> a..\<phi> b}" and y: "y \<in> {\<phi> a..\<phi> b}" "x \<le> y" for x y
  proof -
    obtain f_int: "f integrable_on {x..y}" "f integrable_on {\<phi> a..y}"
      using integrable_on_subinterval[OF f_int] x y by auto
    then have "ff y - ff x = integral {x..y} f"
      unfolding ff_def
      using Henstock_Kurzweil_Integration.integral_combine that by fastforce
    also have "norm \<dots> \<le> M * (y - x)"
      using integral_bound[OF \<open>x \<le> y\<close> continuous_on_subset[OF contf]]
              that M_bound by (auto simp: norm_real)
    finally show ?thesis
      by (simp add: \<open>x \<le> y\<close>)
  qed
  have ff_lip: "norm (ff x - ff y) \<le> M * \<bar>x - y\<bar>"
    if "x \<in> {\<phi> a..\<phi> b}" "y \<in> {\<phi> a..\<phi> b}" for x y
    by (metis ff_lip_half linorder_class.linear norm_minus_commute real_norm_def that)
  have \<phi>_range: "\<phi> t \<in> {\<phi> a..\<phi> b}" if "t \<in> {a..b}" for t
    using mono[of a t] mono[of t b] that by auto
  have ac_comp: "absolutely_continuous_on {a..b} (ff \<circ> \<phi>)"
  proof (rule absolutely_continuous_on_Lipschitz_compose[OF \<phi> _ M_pos])
  qed (use \<phi>_range ff_lip in auto)
  have deriv: "((ff \<circ> \<phi>) has_vector_derivative \<phi>' t *\<^sub>R f (\<phi> t)) (at t within {a..b})" 
    if "t \<in> {a..b} - S" for t
  proof -
    have \<phi>_deriv: "(\<phi> has_vector_derivative \<phi>' t) (at t within {a..b})"
      using vec[OF that] has_vector_derivative_at_within by blast
    have \<phi>t_in: "\<phi> t \<in> {\<phi> a..\<phi> b}"
      using \<phi>_range that by auto
    have f_cont: "continuous (at (\<phi> t) within {\<phi> a..\<phi> b}) f"
      using contf \<phi>t_in continuous_on_eq_continuous_within by blast
    have ff_deriv: "(ff has_vector_derivative f (\<phi> t)) (at (\<phi> t) within {\<phi> a..\<phi> b})"
      unfolding ff_def
      using integral_has_vector_derivative_pointwise[OF f_int \<phi>t_in f_cont] .
    have "\<phi> ` {a..b} \<subseteq> {\<phi> a..\<phi> b}"
      using \<phi>_range by auto
    then show ?thesis using vector_diff_chain_within[OF \<phi>_deriv]
      by (metis ff_deriv has_vector_derivative_within_subset) 
  qed
  have ftc: "((\<lambda>t. \<phi>' t *\<^sub>R f (\<phi> t)) has_integral ((ff \<circ> \<phi>) b - (ff \<circ> \<phi>) a)) {a..b}"
    using fundamental_theorem_of_calculus_absolutely_continuous [OF \<open>negligible S\<close> \<open>a \<le> b\<close> ac_comp] 
    using deriv by auto
  have "(ff \<circ> \<phi>) b - (ff \<circ> \<phi>) a = integral {\<phi> a..\<phi> b} f"
    using ff_def by auto

  with ftc show ?thesis by (simp add: real_scaleR_def)
qed

(*Added to Lebesgue_Measure 2026-06*)
lemma lborel_distr_complex_pair:
  "distr (lborel :: (real \<times> real) measure) borel (\<lambda>(x,y). Complex x y) = (lborel :: complex measure)"
proof (rule lborel_eqI[symmetric])
  let ?C = "\<lambda>(x::real, y::real). Complex x y"
  show "sets (distr lborel borel ?C) = sets borel"
    by simp
  fix l u :: complex
  assume basis: "\<And>b. b \<in> Basis \<Longrightarrow> l \<bullet> b \<le> u \<bullet> b"
  have meas_C: "?C \<in> lborel \<rightarrow>\<^sub>M borel"
  proof -
    have "continuous_on UNIV (\<lambda>p. Complex (fst p) (snd p))"
      by (intro continuous_on_Complex continuous_on_fst continuous_on_snd continuous_on_id)
    then have "?C \<in> borel_measurable borel"
      by (simp add: borel_measurable_continuous_onI case_prod_unfold)
    then show ?thesis by (simp add: measurable_lborel1)
  qed
  have "emeasure (distr lborel borel ?C) (box l u) = emeasure lborel (?C -` box l u)"
    using emeasure_distr[OF meas_C] by simp
  also have "?C -` box l u = box (Re l, Im l) (Re u, Im u)"
    by (auto simp: mem_box Basis_complex_def Basis_prod_def inner_complex_def
          inner_Pair_0 complex.sel split: prod.splits)
  also have "emeasure lborel (box (Re l, Im l) (Re u, Im u)) = ennreal (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
  proof -
    have "emeasure lborel (box (Re l, Im l) (Re u, Im u)) =
          ennreal (\<Prod>b\<in>Basis. ((Re u, Im u) - (Re l, Im l)) \<bullet> b)"
    proof (rule emeasure_lborel_box)
      fix b :: "real \<times> real"
      assume "b \<in> Basis"
      then show "(Re l, Im l) \<bullet> b \<le> (Re u, Im u) \<bullet> b"
        using basis
        by (metis Pair_mono complex_Basis_1 complex_Basis_i complex_inner_1_right complex_inner_i_right inner_Basis_mono)
    qed
    also have "(\<Prod>b\<in>(Basis :: (real \<times> real) set). ((Re u, Im u) - (Re l, Im l)) \<bullet> b) =
              (\<Prod>b\<in>(Basis :: complex set). (u - l) \<bullet> b)"
      by (simp add: Basis_complex_def Basis_prod_def inner_complex_def inner_Pair_0
            complex.sel)
    finally show ?thesis .
  qed
  finally show "emeasure (distr lborel borel ?C) (box l u) = ennreal (\<Prod>b\<in>Basis. (u - l) \<bullet> b)" .
qed

(*Added to Starlike 2026-06*)
lemma supporting_hyperplane_rel_frontier:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "x \<in> rel_frontier S"
  shows "\<exists>a. a \<noteq> 0 \<and> (\<forall>y \<in> closure S. a \<bullet> x \<le> a \<bullet> y) \<and>
             (\<forall>y \<in> rel_interior S. a \<bullet> x < a \<bullet> y)"
proof -
  have "x \<in> closure S" "x \<notin> rel_interior S"
    using assms(2) unfolding rel_frontier_def by auto
  then show ?thesis
    using supporting_hyperplane_rel_boundary[OF convex_closure[OF assms(1)]]
    by (metis convex_rel_interior_closure[OF assms(1)])
qed

(*Added to Starlike 2026-06*)
lemma supporting_hyperplane_frontier:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "x \<in> frontier S"
  shows "\<exists>a. a \<noteq> 0 \<and> (\<forall>y \<in> closure S. a \<bullet> x \<le> a \<bullet> y)"
proof (cases "interior S = {}")
  case True
  then obtain a b where "a \<noteq> 0" "S \<subseteq> {x. a \<bullet> x = b}"
    using empty_interior_subset_hyperplane[OF assms(1)] by blast
  then have "closure S \<subseteq> {x. a \<bullet> x = b}"
    by (simp add: closed_hyperplane closure_minimal)
  moreover have "x \<in> closure S"
    using assms(2) unfolding frontier_def by auto
  ultimately have "\<forall>y \<in> closure S. a \<bullet> x \<le> a \<bullet> y"
    by (simp add: subset_eq)
  then show ?thesis using \<open>a \<noteq> 0\<close> by blast
next
  case False
  then have "x \<in> rel_frontier S"
    by (simp add: assms(2) rel_frontier_nonempty_interior)
  then obtain a where "a \<noteq> 0" "\<forall>y \<in> closure S. a \<bullet> x \<le> a \<bullet> y"
    using supporting_hyperplane_rel_frontier[OF assms(1)] by blast
  then show ?thesis by blast
qed

(*Added to Path_Connected 2026-06*)
lemma convex_triple_rel_frontier_between:
  fixes S :: "complex set" and a b c d :: complex and e :: real
  assumes "between (a,b) c"
    and d: "d \<bullet> c = e" "d \<bullet> b = e" "d \<bullet> a = e"
    and ne: "b \<noteq> c" "a \<noteq> c" "a \<noteq> b"
    and abc: "a \<in> rel_frontier S" "b \<in> rel_frontier S" "c \<in> rel_frontier S"
    and "convex S"
    and "d \<noteq> 0"
  shows "S \<subseteq> {x. d \<bullet> x \<le> e} \<or> S \<subseteq> {x. d \<bullet> x \<ge> e}"
proof -
  obtain d' where "d' \<noteq> 0" 
            and d'_clo: "\<forall>y \<in> closure S. d' \<bullet> c \<le> d' \<bullet> y"
            and d'_int: "\<forall>y \<in> rel_interior S. d' \<bullet> c < d' \<bullet> y"
    using supporting_hyperplane_rel_frontier [OF \<open>convex S\<close>] \<open>c \<in> rel_frontier S\<close>
    by blast
  define e' where "e' \<equiv> d' \<bullet> c"
  have "c \<in> open_segment a b"
    using \<open>between (a,b) c\<close> ne
    by (auto simp: between_mem_segment open_segment_def)
  then obtain u where "0 < u" "u < 1" and u: "c = (1 - u) *\<^sub>R a + u *\<^sub>R b"
    by (meson in_segment(2))
  obtain ineqs: "d' \<bullet> ((1 - u) *\<^sub>R a + u *\<^sub>R b) \<le> d' \<bullet> a"
                "d' \<bullet> ((1 - u) *\<^sub>R a + u *\<^sub>R b) \<le> d' \<bullet> b"
    using abc d'_clo rel_frontier_def u by auto
  then have "d' \<bullet> a = e'"
    using \<open>0 < u\<close> \<open>u < 1\<close> 
    apply (simp add: e'_def u algebra_simps)
    by (smt (verit) scaleR_eq_iff affine_ineq real_scaleR_def)
  have "d' \<bullet> b = e'"
    using \<open>0 < u\<close> \<open>u < 1\<close> 
    apply (simp add: e'_def u algebra_simps)
    by (smt (verit, ccfv_SIG) inner_add_right ineqs inner_mult_right
        mult_le_cancel_left_pos scaleR_conv_of_real segment_bound_lemma)
  have hyp_eq: "{x. d' \<bullet> x = e'} = {x. d \<bullet> x = e}"
  proof -
    have abc_in_d': "{a, b, c} \<subseteq> {x. d' \<bullet> x = e'}"
      using \<open>d' \<bullet> a = e'\<close> \<open>d' \<bullet> b = e'\<close> e'_def by auto
    have abc_in_d: "{a, b, c} \<subseteq> {x. d \<bullet> x = e}"
      using assms by auto
    have c_in_aff: "c \<in> affine hull {a, b}"
      by (metis affine_hull_closed_segment assms(1) between_mem_segment hull_inc)
    then have aff_abc: "aff_dim {a, b, c} = 1"
      using aff_dim_insert[of c "{a, b}"] aff_dim_2[of a b] \<open>a \<noteq> b\<close>
      by (simp add: insert_commute hull_inc)
    have "affine hull {a, b, c} = affine hull {x::complex. d' \<bullet> x = e'}"
      using aff_dim_hyperplane[OF \<open>d' \<noteq> 0\<close>] aff_dim_eq_full_gen[OF abc_in_d'] aff_abc by auto
    then have "affine hull {a, b, c} = {x. d' \<bullet> x = e'}"
      by (simp add: affine_hyperplane)
    moreover 
    have "affine hull {a, b, c} = affine hull {x::complex. d \<bullet> x = e}"
      using aff_dim_hyperplane[OF \<open>d \<noteq> 0\<close>] aff_dim_eq_full_gen[OF abc_in_d] aff_abc by auto
    then have "affine hull {a, b, c} = {x. d \<bullet> x = e}"
      by (simp add: affine_hyperplane)
    ultimately show ?thesis by simp
  qed
  have "rel_interior S \<subseteq> {x. d \<bullet> x < e} \<or> rel_interior S \<subseteq> {x. e < d \<bullet> x}"
  proof -
    have conn: "connected (rel_interior S)"
      by (meson \<open>convex S\<close> convex_connected convex_rel_interior)
    have disj: "{x. d \<bullet> x < e} \<inter> {x. e < d \<bullet> x} \<inter> rel_interior S = {}"
      by auto
    have sub: "rel_interior S \<subseteq> {x. d \<bullet> x < e} \<union> {x. e < d \<bullet> x}"
      by (smt (verit) UnCI d'_int e'_def hyp_eq mem_Collect_eq subsetI)
    have "{x. d \<bullet> x < e} \<inter> rel_interior S = {} \<or>
          {x::complex. e < d \<bullet> x} \<inter> rel_interior S = {}"
      using connectedD[OF conn open_halfspace_lt open_halfspace_gt disj sub] .
    then show ?thesis using sub by blast
  qed
  then show ?thesis
      using closure_mono convex_closure_rel_interior[OF \<open>convex S\<close>] \<open>d \<noteq> 0\<close>
      by (metis (no_types, lifting) ext closure_halfspace_gt closure_halfspace_lt 
          closure_subset order.trans)
qed

(*Added to Path_Connected 2026-06*)
lemma convex_triple_rel_frontier:
  fixes S :: "complex set" and a b c d :: complex and e :: real
  assumes "convex S"
    and "a \<in> rel_frontier S" "b \<in> rel_frontier S" "c \<in> rel_frontier S"
    and "a \<noteq> b" "a \<noteq> c" "b \<noteq> c"
    and eqe: "d \<bullet> a = e" "d \<bullet> b = e" "d \<bullet> c = e"
  shows "S \<subseteq> {x. d \<bullet> x \<le> e} \<or> S \<subseteq> {x. d \<bullet> x \<ge> e}"
proof (cases "d=0")
  case False
  have "aff_dim {a, b, c} \<le> aff_dim {x. d \<bullet> x = e}"
    by (simp add: aff_dim_subset eqe)
  also have "\<dots> \<le> 1"
    using False by (simp add: aff_dim_hyperplane)
  finally have "collinear {a,b,c}"
    by (simp add: collinear_aff_dim)
  then have "between (b,c) a \<or> between (c,a) b \<or> between (a,b) c"
    by (simp add: collinear_between_cases)      
  with False convex_triple_rel_frontier_between show ?thesis
    using assms by blast
qed auto

(*Added to Path_Connected 2026-06*)
lemma lipschitz_convex_spherical_projection_explicit:
  fixes r :: real and S :: "'a::euclidean_space set"
  assumes "convex S" "0 < r" "0 \<in> S"
    and ball_sub: "ball 0 r \<inter> affine hull S \<subseteq> rel_interior S"
    and x_rf: "x \<in> rel_frontier S" and y_rf: "y \<in> rel_frontier S"
  shows "dist (x /\<^sub>R norm x) (y /\<^sub>R norm y) \<le> inverse r * dist x y"
proof -
  have x_ne: "x \<noteq> 0" and y_ne: "y \<noteq> 0"
  proof -
    have "0 \<in> ball 0 r" using \<open>0 < r\<close> by simp
    moreover have "0 \<in> affine hull S" using \<open>0 \<in> S\<close> by (rule hull_inc)
    ultimately have "0 \<in> rel_interior S" using ball_sub by auto
    moreover have "x \<notin> rel_interior S" "y \<notin> rel_interior S"
      using x_rf y_rf by (auto simp: rel_frontier_def)
    ultimately show "x \<noteq> 0" "y \<noteq> 0" by auto
  qed
  have x_aff: "x \<in> affine hull S" and y_aff: "y \<in> affine hull S"
    using x_rf y_rf rel_frontier_affine_hull by auto
  have norm_x: "norm x \<ge> r" and norm_y: "norm y \<ge> r"
  proof -
    have x_not_ri: "x \<notin> rel_interior S" and y_not_ri: "y \<notin> rel_interior S"
      using x_rf y_rf by (auto simp: rel_frontier_def)
    have "\<not> (norm x < r)"
    proof
      assume "norm x < r"
      then have "x \<in> ball 0 r" by (simp add: mem_ball_0)
      then have "x \<in> ball 0 r \<inter> affine hull S" using x_aff by auto
      then have "x \<in> rel_interior S" using ball_sub by auto
      with x_not_ri show False by contradiction
    qed
    then show "norm x \<ge> r" by linarith
    have "\<not> (norm y < r)"
    proof
      assume "norm y < r"
      then have "y \<in> ball 0 r" by (simp add: mem_ball_0)
      then have "y \<in> ball 0 r \<inter> affine hull S" using y_aff by auto
      then have "y \<in> rel_interior S" using ball_sub by auto
      with y_not_ri show False by contradiction
    qed
    then show "norm y \<ge> r" by linarith
  qed
  \<comment> \<open>Key inequality: min(\<Parallel>x\<Parallel>, \<Parallel>y\<Parallel>) * dist(x/\<Parallel>x\<Parallel>, y/\<Parallel>y\<Parallel>) \<le> dist(x, y)\<close>
  have descale: "min (norm x) (norm y) * dist (x /\<^sub>R norm x) (y /\<^sub>R norm y) \<le> dist x y"
  proof -
    have nx: "norm x > 0" and ny: "norm y > 0"
      using x_ne y_ne by auto
    let ?u = "x /\<^sub>R norm x" and ?v = "y /\<^sub>R norm y"
    have nu: "norm ?u = 1" and nv: "norm ?v = 1"
      using nx ny by simp_all
    \<comment> \<open>Express dist(x,y)² and (min * dist(u,v))² in terms of inner products\<close>
    have expand_xy: "(dist x y)\<^sup>2 = (norm x)\<^sup>2 + (norm y)\<^sup>2 - 2 * (norm x) * (norm y) * (?u \<bullet> ?v)"
    proof -
      have "x = norm x *\<^sub>R ?u" using nx by simp
      moreover have "y = norm y *\<^sub>R ?v" using ny by simp
      ultimately have "(dist x y)\<^sup>2 = (norm (norm x *\<^sub>R ?u - norm y *\<^sub>R ?v))\<^sup>2"
        by (simp add: dist_norm)
      also have "\<dots> = (norm x *\<^sub>R ?u - norm y *\<^sub>R ?v) \<bullet> (norm x *\<^sub>R ?u - norm y *\<^sub>R ?v)"
        by (rule power2_norm_eq_inner)
      also have "\<dots> = (norm x)\<^sup>2 * (?u \<bullet> ?u) - 2 * norm x * norm y * (?u \<bullet> ?v) + (norm y)\<^sup>2 * (?v \<bullet> ?v)"
        by (simp add: inner_diff_left inner_diff_right inner_scaleR_left inner_scaleR_right
                      algebra_simps power2_eq_square inner_commute)
      also have "\<dots> = (norm x)\<^sup>2 + (norm y)\<^sup>2 - 2 * norm x * norm y * (?u \<bullet> ?v)"
        using nu nv by (simp add: power2_norm_eq_inner[symmetric])
      finally show ?thesis .
    qed
    have expand_uv: "(dist ?u ?v)\<^sup>2 = 2 - 2 * (?u \<bullet> ?v)"
    proof -
      have "(dist ?u ?v)\<^sup>2 = (norm (?u - ?v))\<^sup>2" by (simp add: dist_norm)
      also have "\<dots> = (?u - ?v) \<bullet> (?u - ?v)" by (rule power2_norm_eq_inner)
      also have "\<dots> = ?u \<bullet> ?u - 2 * (?u \<bullet> ?v) + ?v \<bullet> ?v"
        by (simp add: inner_diff_left inner_diff_right algebra_simps inner_commute)
      also have "\<dots> = 2 - 2 * (?u \<bullet> ?v)"
        using nu nv by (simp add: power2_norm_eq_inner[symmetric])
      finally show ?thesis .
    qed
    \<comment> \<open>Show (min * dist(u,v))² \<le> dist(x,y)²\<close>
    have sq_ineq: "(min (norm x) (norm y) * dist ?u ?v)\<^sup>2 \<le> (dist x y)\<^sup>2"
    proof -
      let ?m = "min (norm x) (norm y)"
      let ?M = "max (norm x) (norm y)"
      have m_pos: "?m > 0" using nx ny by simp
      have M_pos: "?M > 0" using nx ny by linarith
      have m_le_M: "?m \<le> ?M" by simp
      have uv_bound: "?u \<bullet> ?v \<le> 1"
        using norm_cauchy_schwarz[of ?u ?v] nu nv by simp
      have "(?m * dist ?u ?v)\<^sup>2 = ?m\<^sup>2 * (dist ?u ?v)\<^sup>2"
        by (simp add: power_mult_distrib)
      also have "\<dots> = ?m\<^sup>2 * (2 - 2 * (?u \<bullet> ?v))"
        using expand_uv by simp
      also have "\<dots> \<le> ?m * ?M * (2 - 2 * (?u \<bullet> ?v))"
      proof -
        have "?m\<^sup>2 \<le> ?m * ?M"
          using m_pos m_le_M by (simp add: power2_eq_square mult_left_mono)
        moreover have "2 - 2 * (?u \<bullet> ?v) \<ge> 0" using uv_bound by linarith
        ultimately show ?thesis by (intro mult_right_mono) auto
      qed
      also have "\<dots> = (norm x) * (norm y) * (2 - 2 * (?u \<bullet> ?v))"
        by (auto simp: min_def max_def field_simps)
      also have "\<dots> = 2 * norm x * norm y - 2 * norm x * norm y * (?u \<bullet> ?v)"
        by algebra
      also have "\<dots> \<le> (norm x)\<^sup>2 + (norm y)\<^sup>2 - 2 * norm x * norm y * (?u \<bullet> ?v)"
      proof -
        have "2 * norm x * norm y \<le> (norm x)\<^sup>2 + (norm y)\<^sup>2"
          by (metis sum_squares_bound)
        then show ?thesis by linarith
      qed
      also have "\<dots> = (dist x y)\<^sup>2" using expand_xy by simp
      finally show ?thesis .
    qed
    \<comment> \<open>Conclude from squared inequality\<close>
    have "min (norm x) (norm y) * dist ?u ?v \<ge> 0"
      using nx ny by (simp add: min_def zero_le_dist)
    then show ?thesis
      using sq_ineq
      by (meson pos2 power_mono_iff zero_le_dist)
  qed
  \<comment> \<open>Combine descale with norm bounds\<close>
  have "min (norm x) (norm y) \<ge> r"
    using norm_x norm_y by linarith
  moreover have "dist (x /\<^sub>R norm x) (y /\<^sub>R norm y) \<ge> 0"
    by (simp add: zero_le_dist)
  ultimately have "r * dist (x /\<^sub>R norm x) (y /\<^sub>R norm y) \<le> 
                   min (norm x) (norm y) * dist (x /\<^sub>R norm x) (y /\<^sub>R norm y)"
    by (simp add: mult_right_mono)
  also have "\<dots> \<le> dist x y" by (rule descale)
  finally have "r * dist (x /\<^sub>R norm x) (y /\<^sub>R norm y) \<le> dist x y" .
  then show ?thesis
    using \<open>0 < r\<close> by (simp add: field_simps)
qed

(*Added to Path_Connected 2026-06*)
lemma lipschitz_convex_spherical_projection:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "0 \<in> rel_interior S"
  shows "\<exists>B. \<forall>x y. x \<in> rel_frontier S \<longrightarrow> y \<in> rel_frontier S \<longrightarrow>
              dist (x /\<^sub>R norm x) (y /\<^sub>R norm y) \<le> B * dist x y"
proof -
  from assms(2) obtain r where "r > 0" and
    sub: "ball 0 r \<inter> affine hull S \<subseteq> S"
    using mem_rel_interior_ball by (auto simp: mem_rel_interior_ball)
  have "0 \<in> S" using assms(2) rel_interior_subset by auto
  have ball_ri: "ball 0 r \<inter> affine hull S \<subseteq> rel_interior S"
  proof -
    have "openin (top_of_set (affine hull S)) (affine hull S \<inter> ball 0 r)"
      by (intro openin_open_Int open_ball)
    then have "openin (top_of_set (affine hull S)) (ball 0 r \<inter> affine hull S)"
      by (simp add: Int_commute)
    then show ?thesis
      using sub openin_subset_relative_interior by blast
  qed
  show ?thesis
  proof (intro exI allI impI)
    fix x y assume "x \<in> rel_frontier S" "y \<in> rel_frontier S"
    show "dist (x /\<^sub>R norm x) (y /\<^sub>R norm y) \<le> inverse r * dist x y"
      by (rule lipschitz_convex_spherical_projection_explicit
            [OF \<open>convex S\<close> \<open>r > 0\<close> \<open>0 \<in> S\<close> ball_ri
             \<open>x \<in> rel_frontier S\<close> \<open>y \<in> rel_frontier S\<close>])
  qed
qed

(*Added to Linear_Algebra 2026-06*)
lemma norm_le_norm_add_orthogonal:
  assumes "orthogonal x y"
  shows "norm x \<le> norm (x + y)"
proof -
  have "(norm x)\<^sup>2 \<le> (norm x)\<^sup>2 + (norm y)\<^sup>2"
    by simp
  also have "\<dots> = (norm (x + y))\<^sup>2"
    using norm_add_Pythagorean[OF assms] by simp
  finally show ?thesis
    by (rule power2_le_imp_le) simp
qed

(*Added to Line_Segment 2026-06*)
lemma dist_scaleR_ge_min:
  fixes x y :: "'a::real_inner"
  assumes "0 \<le> a" "0 \<le> b" "x \<bullet> y \<le> 0"
  shows "min a b * dist x y \<le> dist (a *\<^sub>R x) (b *\<^sub>R y)"
proof -
  have minab: "0 \<le> min a b" using assms by simp
  have sq: "(min a b)\<^sup>2 * ((x - y) \<bullet> (x - y)) \<le> (a *\<^sub>R x - b *\<^sub>R y) \<bullet> (a *\<^sub>R x - b *\<^sub>R y)"
  proof -
    have expand_rhs: "(a *\<^sub>R x - b *\<^sub>R y) \<bullet> (a *\<^sub>R x - b *\<^sub>R y) =
        a\<^sup>2 * (x \<bullet> x) + b\<^sup>2 * (y \<bullet> y) - 2 * a * b * (x \<bullet> y)"
      by (simp add: inner_commute inner_diff_right power2_eq_square)
    have expand_lhs: "(min a b)\<^sup>2 * ((x - y) \<bullet> (x - y)) =
        (min a b)\<^sup>2 * (x \<bullet> x) + (min a b)\<^sup>2 * (y \<bullet> y) - 2 * (min a b)\<^sup>2 * (x \<bullet> y)"
      by (simp add: inner_diff_left inner_diff_right
                    inner_commute[of y x] power2_eq_square algebra_simps)
    have 1: "(min a b)\<^sup>2 * (x \<bullet> x) \<le> a\<^sup>2 * (x \<bullet> x)"
      by (intro mult_right_mono power_mono minab min.cobounded1 assms inner_ge_zero)
    have 2: "(min a b)\<^sup>2 * (y \<bullet> y) \<le> b\<^sup>2 * (y \<bullet> y)"
      by (intro mult_right_mono power_mono minab min.cobounded2 assms inner_ge_zero)
    have ab_ge: "(min a b)\<^sup>2 \<le> a * b"
      using assms(1,2) by (auto simp: power2_eq_square min_def intro: mult_mono)
    have nxy: "0 \<le> - (x \<bullet> y)" using assms(3) by simp
    have 3: "(min a b)\<^sup>2 * (- (x \<bullet> y)) \<le> a * b * (- (x \<bullet> y))"
      by (intro mult_right_mono ab_ge nxy)
    show ?thesis
      unfolding expand_lhs expand_rhs
      using 1 2 3 by (simp add: algebra_simps)
  qed
  have "(min a b * dist x y)\<^sup>2 = (min a b)\<^sup>2 * (dist x y)\<^sup>2"
    by (simp add: power_mult_distrib)
  also have "\<dots> = (min a b)\<^sup>2 * ((x - y) \<bullet> (x - y))"
    by (simp add: dist_norm power2_norm_eq_inner)
  also have "\<dots> \<le> (a *\<^sub>R x - b *\<^sub>R y) \<bullet> (a *\<^sub>R x - b *\<^sub>R y)"
    by (rule sq)
  also have "\<dots> = (dist (a *\<^sub>R x) (b *\<^sub>R y))\<^sup>2"
    by (simp add: dist_norm power2_norm_eq_inner)
  finally show ?thesis
    by (rule power2_le_imp_le) (simp add: mult_nonneg_nonneg minab zero_le_dist)
qed

(*Added to Line_Segment 2026-06*)
lemma dist_scaleR_ge_min_between:
  fixes x y w :: "'a::real_inner"
  assumes "0 \<le> a" "0 \<le> b" and bet: "between (x, y) w" and orth: "orthogonal w (x - y)"
  shows "min a b * dist x y \<le> dist (a *\<^sub>R x) (b *\<^sub>R y)"
proof -
  from bet obtain u where "0 \<le> u" "u \<le> 1" and u: "w = (1 - u) *\<^sub>R x + u *\<^sub>R y"
    by (auto simp: between_mem_segment closed_segment_def)
  have \<section>: "x - w = u *\<^sub>R (x - y)" "y - w = (u - 1) *\<^sub>R (x - y)"
    by (simp_all add: u algebra_simps)
  have dot_le: "(x - w) \<bullet> (y - w) \<le> 0"
    by (simp add: "\<section>"(1,2) \<open>0 \<le> u\<close> \<open>u \<le> 1\<close> mult_nonpos_nonneg)
  have dist_eq: "dist (x - w) (y - w) = dist x y"
    by (simp add: dist_norm)
  have step1: "min a b * dist x y \<le> dist (a *\<^sub>R (x - w)) (b *\<^sub>R (y - w))"
    using dist_scaleR_ge_min[OF assms(1,2) dot_le] dist_eq by simp
  have decomp: "a *\<^sub>R x - b *\<^sub>R y = (a *\<^sub>R (x - w) - b *\<^sub>R (y - w)) + (a - b) *\<^sub>R w"
    by (simp add: algebra_simps)
  have "orthogonal (a *\<^sub>R (x - w) - b *\<^sub>R (y - w)) ((a - b) *\<^sub>R w)"
    using orthogonal_clauses orth
    by (metis "\<section>" orthogonal_commute)
  then have "dist (a *\<^sub>R (x - w)) (b *\<^sub>R (y - w)) \<le> dist (a *\<^sub>R x) (b *\<^sub>R y)"
    by (simp add: decomp dist_norm norm_le_norm_add_orthogonal)
  with step1 show ?thesis by linarith
qed

(*FIXME: not clear where this belongs. Past Starlike.*)
lemma collinear_orthogonal_dist_product:
  fixes z x x' w y :: "'a::euclidean_space"
  assumes "collinear {z, x, x'}" "collinear {w, x, y}"
    "orthogonal (z - w) (x - y)" "orthogonal (y - x') (z - x')"
    "x' \<noteq> z" "y \<noteq> w"
  shows "dist z w * dist x y = dist y x' * dist z x"
proof -
  \<comment> \<open>Translate so that x is at the origin. All conditions are translation-invariant.\<close>
  define u v where "u = x' - x" and "v = y - x"
  have col1: "collinear {0, z - x, u}" 
    using assms(1) collinear_3[of z x x'] by (simp add: u_def)
  have col2: "collinear {0, w - x, v}" 
    using assms(2) collinear_3[of w x y] by (simp add: v_def)
  have orth1: "(z - x) \<bullet> v - (w - x) \<bullet> v = 0"
    using assms(3) by (simp add: orthogonal_def v_def algebra_simps)
  have orth2: "v \<bullet> (z - x) - v \<bullet> u - u \<bullet> (z - x) + u \<bullet> u = 0"
    using assms(4) by (simp add: orthogonal_def u_def v_def algebra_simps)
  show "dist z w * dist x y = dist y x' * dist z x"
  proof (cases "u = 0")
    case True
    then have xeq: "x' = x" by (simp add: u_def)
    then show ?thesis
      using dist_commute True col2 inner_commute[of v "z - x"]
        norm_cauchy_schwarz_equal[of "w - x" v] orth1 orth2 v_def by force
  next
    case False
    then have u_ne: "u \<noteq> 0" .
    with col1 obtain a where za: "z - x = a *\<^sub>R u"
      by (metis (no_types, lifting) collinear_lemma insert_commute scaleR_zero_left)
    have v_ne: "v \<noteq> 0"
      using \<open>x' \<noteq> z\<close> orth2 u_def za by force 
    with col2 obtain b where wb: "w - x = b *\<^sub>R v"
      by (metis collinear_lemma doubleton_eq_iff scaleR_zero_left)
        \<comment> \<open>Express distances in terms of norms.\<close>
    have dzw: "dist z w = norm (a *\<^sub>R u - b *\<^sub>R v)"
      using za wb by (simp add: dist_norm algebra_simps)
    have dxy: "dist x y = norm v"
      by (simp add: dist_norm v_def norm_minus_commute)
    have dyx': "dist y x' = norm (v - u)"
      by (simp add: dist_norm u_def v_def algebra_simps norm_minus_commute)
    have dzx: "dist z x = norm (a *\<^sub>R u)"
      using za by (simp add: dist_norm norm_minus_commute)
    define uu where "uu = u \<bullet> u"
    define uv where "uv = u \<bullet> v"
    define vv where "vv = v \<bullet> v"
    have "(norm (a *\<^sub>R u - b *\<^sub>R v))\<^sup>2 = a * a * (u \<bullet> u) - 2 * (a * b) * (u \<bullet> v) + b * b * (v \<bullet> v)"
      by (simp add: power2_norm_eq_inner inner_commute algebra_simps)
    then have "(norm (a *\<^sub>R u - b *\<^sub>R v))\<^sup>2 = a\<^sup>2 * uu - 2 * a * b * uv + b\<^sup>2 * vv"
      by (simp add: uu_def uv_def vv_def power2_eq_square)
    then have lhs_sq: "(dist z w * dist x y)\<^sup>2 = (a\<^sup>2 * uu - 2 * a * b * uv + b\<^sup>2 * vv) * vv"
      by (simp add: dxy dzw power2_norm_eq_inner power_mult_distrib vv_def)
    have rhs_sq: "(dist y x' * dist z x)\<^sup>2 = a\<^sup>2 * uu * (vv - 2 * uv + uu)"
      by (simp add: dyx' dzx power2_norm_eq_inner uu_def uv_def vv_def inner_commute algebra_simps)
    have "(a - 1) * uv = (a - 1) * uu" 
      using orth2 za by (simp add: uv_def uu_def inner_commute algebra_simps)
    then have uv_eq: "uv = uu"
      using orth2 za \<open>x' \<noteq> z\<close> u_def za by auto
        \<comment> \<open>Key derived facts.\<close>
    have 1: "a * uv = b * vv"
      using orth1 uv_def vv_def wb za by force
    have lhs_eq: "(dist z w * dist x y)\<^sup>2 = (a\<^sup>2 * uu - 2 * a * b * uu + b\<^sup>2 * vv) * vv"
      using lhs_sq uv_eq by simp
    also have "\<dots> = a\<^sup>2 * uu * (vv - uu)"
      using 1 unfolding uv_eq by algebra
    also have "\<dots> = (dist y x' * dist z x)\<^sup>2"
      using rhs_sq uv_eq by simp
    finally have "(dist z w * dist x y)\<^sup>2 = (dist y x' * dist z x)\<^sup>2" .
    then show ?thesis by simp
  qed
qed

lemma inverse_lipschitz_convex_spherical_projection_explicit:
  fixes x y :: "'a::euclidean_space"
  assumes "convex S" "r>0" "0 \<in> S"
    and reli: "ball 0 r \<inter> affine hull S \<subseteq> rel_interior S"
    and S: "S \<subseteq> cball 0 R"
    and x: "x \<in> rel_frontier S" and y: "y \<in> rel_frontier S"
  shows "r / R\<^sup>2 * dist x y \<le> dist ((1 / norm x) *\<^sub>R x) ((1 / norm y) *\<^sub>R y)"
proof (cases "R\<le>0")
  case True
  have "0 \<in> cball (0::'a) R" using \<open>0 \<in> S\<close> S by (meson subsetD)
  then have "0 \<le> R" by simp
  with True show ?thesis
    by simp
next
  case False
  have "0 \<in> rel_interior S"
    using assms(2,3) hull_subset reli by fastforce
  obtain x_ne: "x \<noteq> 0" and y_ne: "y \<noteq> 0"
    using \<open>0 \<in> rel_interior S\<close> x y rel_frontier_def by auto
  have r_le: "\<And>z. z \<in> rel_frontier S \<Longrightarrow> r \<le> norm z"
    unfolding rel_frontier_def using closure_affine_hull reli
    by (smt (verit, del_insts) DiffD1 DiffD2 Int_iff in_mono mem_ball_0) 
  have norm_le: "\<And>z. z \<in> rel_frontier S \<Longrightarrow> norm z \<le> R"
    unfolding rel_frontier_def using S closed_cball closure_minimal
    by (metis Diff_subset mem_cball_0 subset_iff)
  have "r \<le> R" and "0 < R"
    using r_le[OF x] norm_le[OF x] \<open>r>0\<close> by linarith+
  show ?thesis 
  proof (cases "x \<bullet> y \<le> 0 \<or> x=y")
    case True
    have "0 \<le> 1 / norm x" and "0 \<le> 1 / norm y" using x_ne y_ne by auto
    then have key: "min (1 / norm x) (1 / norm y) * dist x y
               \<le> dist ((1 / norm x) *\<^sub>R x) ((1 / norm y) *\<^sub>R y)"
      by (metis True dist_scaleR_ge_min dist_self mult_zero_right order_eq_refl)
    have rR2_le_invR: "r / R\<^sup>2 \<le> 1 / R"
      using \<open>0 < R\<close> \<open>r \<le> R\<close> by (simp add: divide_simps power2_eq_square)
    have invR_le_invx: "1 / R \<le> 1 / norm x"
      using norm_le[OF x] r_le[OF x] \<open>r>0\<close> \<open>0 < R\<close>
      by (intro frac_le) linarith+
    have "1 / R \<le> 1 / norm y"
      using norm_le[OF y] r_le[OF y] \<open>r>0\<close> \<open>0 < R\<close>
      by (intro frac_le) linarith+
    then have "r / R\<^sup>2 \<le> min (1 / norm x) (1 / norm y)"
      using rR2_le_invR invR_le_invx by simp
    then show ?thesis
      by (meson key order.trans mult_right_mono zero_le_dist)
  next
    case False
    then have "x \<bullet> y > 0" "x\<noteq>y"
      by auto
        \<comment> \<open>Project the origin onto the affine hull of @{term \<open>{x, y}\<close>}\<close>
    define w where "w = closest_point (affine hull {x, y}) 0"
    have aff_closed: "closed (affine hull {x, y})" by (rule closed_affine_hull)
    have aff_ne: "affine hull {x, y} \<noteq> {}" by (simp add: affine_hull_eq_empty)
    have w_in: "w \<in> affine hull {x, y}"
      unfolding w_def by (rule closest_point_in_set[OF aff_closed aff_ne])
    have w_dist: "dist 0 w \<le> dist 0 z" if "z \<in> affine hull {x, y}" for z
      using closest_point_le that w_def by blast
    have w_orth: "orthogonal (v - w) w" if "v \<in> affine hull {x, y}" for v
      using closest_point_affine_orthogonal[OF affine_affine_hull aff_ne]
      by (metis add_diff_cancel_left' diff_0 diff_minus_eq_add orthogonal_clauses(5) that w_def)
    have x_in_aff: "x \<in> affine hull {x, y}" by (rule hull_inc) simp
    have y_in_aff: "y \<in> affine hull {x, y}" by (rule hull_inc) simp
    have orth_x: "orthogonal (x - w) w" by (rule w_orth[OF x_in_aff])
    have orth_y: "orthogonal (y - w) w" by (rule w_orth[OF y_in_aff])
    have norm_w_le_x: "norm w \<le> norm x"
      using w_dist[OF x_in_aff] by (simp add: dist_norm)
    have norm_w_le_y: "norm w \<le> norm y"
      using w_dist[OF y_in_aff] by (simp add: dist_norm)
        \<comment> \<open>Derive orthogonality of @{term \<open>x - y\<close>} and @{term w}\<close>
    have orth_xy_w: "orthogonal (x - y) w"
      using orthogonal_clauses(10)[OF orth_x orth_y] by (simp add: algebra_simps)
        \<comment> \<open>Collinearity and case analysis\<close>
    have collinear_wxy: "collinear {w, x, y}"
      by (meson False collinear_3_affine_hull collinear_between_cases w_in)
    have betw_cases: "between (x, y) w \<or> between (y, w) x \<or> between (w, x) y"
      using collinear_wxy[unfolded collinear_between_cases] by blast
    show ?thesis
    proof (cases "between (x,y) w")
      case True
      have orth_w: "orthogonal w (x - y)"
        using orth_xy_w by (simp add: orthogonal_commute)
      have step: "min (1 / norm x) (1 / norm y) * dist x y
                          \<le> dist ((1 / norm x) *\<^sub>R x) ((1 / norm y) *\<^sub>R y)"
        by (rule dist_scaleR_ge_min_between) (auto simp: x_ne y_ne intro: True orth_w)
      have "r / R\<^sup>2 \<le> min (1 / norm x) (1 / norm y)"
        using \<open>R>0\<close> \<open>r \<le> R\<close> norm_le[OF x] norm_le[OF y] x_ne y_ne
        by (simp add: divide_simps mult_mono power2_eq_square)
      then have "r / R\<^sup>2 * dist x y \<le> min (1 / norm x) (1 / norm y) * dist x y"
        using mult_right_mono[of "r / R\<^sup>2" "min (1 / norm x) (1 / norm y)" "dist x y"]
        by (simp add: zero_le_dist)
      then show ?thesis
        using step by linarith 
    next
      case False
      then have *: "between (y,w) x \<or> between (x,w) y"
        by (metis betw_cases between_commute)
          \<comment> \<open>Extract a lemma that works for either orientation\<close>
      have "r / R\<^sup>2 * dist x y \<le> dist ((1 / norm x) *\<^sub>R x) ((1 / norm y) *\<^sub>R y)"
        if betx: "between (y, w) x" and orthw: "orthogonal (x - w) w" 
          and nbetw: "\<not> between (x,y) w"
          and xfr: "x \<in> rel_frontier S" and yfr: "y \<in> rel_frontier S"
          and xne: "x \<noteq> 0" and yne: "y \<noteq> 0"
          and rnx: "r \<le> norm x" and rny: "r \<le> norm y"
          and nwx: "norm w \<le> norm x" and xR: "norm x \<le> R"
          and yR: "norm y \<le> R"
          and dot_pos: "0 < x \<bullet> y" and xy_ne: "x \<noteq> y"
        for x y :: "'a"
      proof -
        obtain "w\<noteq>x" "w\<noteq>y"
          using nbetw by fastforce
            \<comment> \<open>Project @{term y} onto the line through @{term \<open>0::'a\<close>} and @{term x}\<close>
        define x' where "x' = closest_point (affine hull {0, x}) y"
        have aff_ne': "affine hull {(0::'a), x} \<noteq> {}"
          by (simp add: affine_hull_eq_empty)
        have aff_closed': "closed (affine hull {(0::'a), x})"
          by (rule closed_affine_hull)
        have x'_orth: "orthogonal (v - x') (y - x')" if "v \<in> affine hull {0, x}" for v
          by (simp add: closest_point_affine_orthogonal that x'_def)
        have orth_0: "orthogonal (0 - x') (y - x')"
          by (rule x'_orth[OF hull_inc]) simp
        have orth_x: "orthogonal (x - x') (y - x')"
          by (rule x'_orth[OF hull_inc]) simp
        have "inverse R \<le> abs (inverse (norm y))"
          by (simp add: le_imp_inverse_le yR yne)
        moreover have "r / R * dist x y \<le> dist ((norm y / norm x) *\<^sub>R x) y"
        proof -
          have r_le_w: "r \<le> norm w"
          proof (rule ccontr)
            assume "\<not> r \<le> norm w"
            then have "w \<in> ball 0 r" by (simp add: dist_norm)
            moreover have "w \<in> affine hull S"
              by (smt (verit, best) affine_affine_hull x y bot.extremum insert_subset
                  rel_frontier_affine_hull subset_hull subset_iff w_in)
            ultimately have "w \<in> rel_interior S"
              using reli by auto
            moreover have "y \<in> closure S"
              using yfr rel_frontier_def by auto
            ultimately have "open_segment w y \<subseteq> rel_interior S"
              using rel_interior_closure_convex_segment[OF \<open>convex S\<close>] by auto
            moreover have "x \<in> open_segment w y"
              using betx \<open>w \<noteq> x\<close> xy_ne
              by (simp add: between_mem_segment open_segment_def closed_segment_commute)
            ultimately have "x \<in> rel_interior S" by auto
            then show False using xfr rel_frontier_def by auto
          qed
          have "r * dist x y \<le> dist 0 w * dist x y"
            using r_le_w by (intro mult_right_mono) auto
          also have "\<dots> = dist y x' * dist 0 x"
          proof (intro collinear_orthogonal_dist_product)
            show "collinear {0, x, x'}"
              using closest_point_in_set[OF aff_closed' aff_ne'] affine_hull_3_imp_collinear
              unfolding x'_def by blast
            show "collinear {w, x, y}"
              by (simp add: collinear_between_cases betx)
            show "orthogonal (0 - w) (x - y)"
              by (smt (verit, ccfv_SIG) \<open>w \<noteq> x\<close> diff_0 between_implies_scaled_diff between_triv2
                  minus_diff_eq orthogonal_clauses(3) orthogonal_commute orthogonal_scaleR right_minus_eq
                  scaleR_zero_left betx xy_ne orthw)
            show "orthogonal (y - x') (0 - x')"
              using orth_0 by (simp add: orthogonal_commute)
            show "x' \<noteq> 0"
              using orth_x orthogonal_def dot_pos by force
            show "y \<noteq> w"
              using \<open>w \<noteq> y\<close> by auto
          qed
          also have "\<dots> \<le> dist y x' * R"
            by (simp add: mult_left_mono xR)
          finally have "r / R * dist x y \<le> dist y x'"
            by (simp add: \<open>0 < R\<close> mult_imp_div_pos_le)
          also have "\<dots> \<le> dist ((norm y / norm x) *\<^sub>R x) y"
            by (simp add: dist_commute closest_point_le collinear_3_imp_in_affine_hull collinear_lemma xne
                x'_def)
          finally show ?thesis .
        qed
        ultimately have "r / R\<^sup>2 * dist x y \<le> \<bar>inverse (norm y)\<bar> * dist ((norm y / norm x) *\<^sub>R x) y"
          by (metis abs_inverse abs_norm_cancel divide_divide_eq_left' divide_inverse_commute frac_le
              power2_eq_square yR yne times_divide_eq_left zero_le_dist zero_less_norm_iff)
        also have "\<dots> = dist ((1 / norm x) *\<^sub>R x) ((1 / norm y) *\<^sub>R y)"
        proof -
          have "(1 / norm x) *\<^sub>R x = inverse (norm y) *\<^sub>R ((norm y / norm x) *\<^sub>R x)"
            using yne by (simp add: scaleR_scaleR)
          then have "dist ((1 / norm x) *\<^sub>R x) ((1 / norm y) *\<^sub>R y) =
                    \<bar>inverse (norm y)\<bar> * dist ((norm y / norm x) *\<^sub>R x) y"
            by (metis (mono_tags, lifting) dist_norm inverse_eq_divide norm_scaleR
                scaleR_right_diff_distrib)
          then show ?thesis by simp
        qed
        finally show ?thesis .
      qed
      then show ?thesis using * False \<open>0 < x \<bullet> y\<close> x y
        by (metis between_commute dist_commute dist_self inner_commute less_eq_real_def local.norm_le
            norm_w_le_x norm_w_le_y orth_x orth_y r_le real_scaleR_def scaleR_zero_right x_ne y_ne)
    qed
  qed
qed



\<comment> \<open>HOL Light: INVERSE_LIPSCHITZ_CONVEX_SPHERICAL_PROJECTION\<close>
lemma inverse_lipschitz_convex_spherical_projection:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "bounded S" "0 \<in> rel_interior S"
  shows "\<exists>B>0. \<forall>x y. x \<in> rel_frontier S \<longrightarrow> y \<in> rel_frontier S \<longrightarrow>
         B * dist x y \<le> dist ((1 / norm x) *\<^sub>R x) ((1 / norm y) *\<^sub>R y)"
proof -
  obtain R where "R > 0" and R: "\<forall>x\<in>S. norm x \<le> R"
    using assms(2) bounded_pos by blast
  then have s_cball: "S \<subseteq> cball 0 R"
    by (auto simp: mem_cball_0)
  obtain r where "r > 0" and r: "ball 0 r \<inter> affine hull S \<subseteq> S"
    using assms(3) by (auto simp: mem_rel_interior_ball)
  have ball_sub: "ball 0 r \<inter> affine hull S \<subseteq> rel_interior S"
  proof -
    have "openin (top_of_set (affine hull S)) (affine hull S \<inter> ball 0 r)"
      by (intro openin_open_Int open_ball)
    then have "openin (top_of_set (affine hull S)) (ball 0 r \<inter> affine hull S)"
      by (simp add: Int_commute)
    then show ?thesis
      using r openin_subset_relative_interior by blast
  qed
  have "0 \<in> S"
    using assms(3) rel_interior_subset by blast
  have "0 < r / R\<^sup>2"
    using \<open>r > 0\<close> \<open>R > 0\<close> by (auto intro: divide_pos_pos zero_less_power)
  moreover have "\<forall>x y. x \<in> rel_frontier S \<longrightarrow> y \<in> rel_frontier S \<longrightarrow>
      r / R\<^sup>2 * dist x y \<le> dist ((1 / norm x) *\<^sub>R x) ((1 / norm y) *\<^sub>R y)"
  proof (intro allI impI)
    fix x y assume "x \<in> rel_frontier S" "y \<in> rel_frontier S"
    then show "r / R\<^sup>2 * dist x y \<le> dist ((1 / norm x) *\<^sub>R x) ((1 / norm y) *\<^sub>R y)"
      using inverse_lipschitz_convex_spherical_projection_explicit
        [OF assms(1) \<open>r > 0\<close> \<open>0 \<in> S\<close> ball_sub s_cball]
      by blast
  qed
  ultimately show ?thesis by blast
qed

\<comment> \<open>HOL Light: BILIPSCHITZ_HOMEOMORPHISM_SPHERICAL_PROJECTION\<close>
lemma bilipschitz_homeomorphism_spherical_projection:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "bounded S" "0 \<in> rel_interior S"
  shows "\<exists>g. homeomorphism (rel_frontier S) (sphere 0 1 \<inter> affine hull S)
               (\<lambda>x. x /\<^sub>R norm x) g \<and>
             (\<exists>B. \<forall>x y. x \<in> rel_frontier S \<longrightarrow> y \<in> rel_frontier S \<longrightarrow>
                   norm (x /\<^sub>R norm x - y /\<^sub>R norm y) \<le> B * norm (x - y)) \<and>
             (\<exists>B. \<forall>x y. x \<in> sphere 0 1 \<inter> affine hull S \<longrightarrow>
                         y \<in> sphere 0 1 \<inter> affine hull S \<longrightarrow>
                   norm (g x - g y) \<le> B * norm (x - y))"
proof -
  \<comment> \<open>Get Lipschitz bound for the spherical projection\<close>
  obtain B where B: "\<And>x y. x \<in> rel_frontier S \<Longrightarrow> y \<in> rel_frontier S \<Longrightarrow>
      dist (x /\<^sub>R norm x) (y /\<^sub>R norm y) \<le> B * dist x y"
    using lipschitz_convex_spherical_projection[OF assms(1,3)] by blast
  \<comment> \<open>Get inverse Lipschitz bound\<close>
  obtain b where "b > 0" and b: "\<And>x y. x \<in> rel_frontier S \<Longrightarrow> y \<in> rel_frontier S \<Longrightarrow>
      b * dist x y \<le> dist ((1 / norm x) *\<^sub>R x) ((1 / norm y) *\<^sub>R y)"
    using inverse_lipschitz_convex_spherical_projection[OF assms] by blast
  \<comment> \<open>The projection is continuous on rel_frontier S\<close>
  have cont: "continuous_on (rel_frontier S) (\<lambda>x. x /\<^sub>R norm x)"
  proof -
    have "0 \<notin> rel_frontier S"
      using assms(3) by (auto simp: rel_frontier_def)
    then show ?thesis
      using continuous_on_Borsuk_map[of 0 "rel_frontier S"] by simp
  qed

  \<comment> \<open>The image equals sphere 0 1 \<inter> affine hull S\<close>
  have zero_in_s: "0 \<in> S"
    using assms(3) rel_interior_subset by blast
  have zero_aff: "0 \<in> affine hull S"
    using zero_in_s hull_subset[of S affine] by blast

  have aff_eq_span: "affine hull S = span S"
    using affine_hull_span_0[OF zero_aff] .
  have image_eq: "(\<lambda>x. x /\<^sub>R norm x) ` rel_frontier S = sphere 0 1 \<inter> affine hull S"
  proof (rule set_eqI, rule iffI)
    fix u assume "u \<in> (\<lambda>x. x /\<^sub>R norm x) ` rel_frontier S"
    then obtain x where x_rf: "x \<in> rel_frontier S" and u_eq: "u = x /\<^sub>R norm x"
      by auto
    have "x \<noteq> 0"
      using x_rf assms(3) by (auto simp: rel_frontier_def)
    then have "norm u = 1"
      by (simp add: u_eq)
    moreover have "u \<in> affine hull S"
    proof -
      have "x \<in> affine hull S"
        using x_rf rel_frontier_affine_hull by blast
      then have "x \<in> span S" using aff_eq_span by simp
      then have "inverse (norm x) *\<^sub>R x \<in> span S"
        by (rule subspace_mul[OF real_vector.subspace_span])
      then show ?thesis
        using aff_eq_span u_eq by (simp add: field_simps)
    qed
    ultimately show "u \<in> sphere 0 1 \<inter> affine hull S"
      by (simp add: sphere_def)
  next
    fix u assume u_in: "u \<in> sphere 0 1 \<inter> affine hull S"
    then have "norm u = 1" and "u \<in> affine hull S"
      by (auto simp: sphere_def)
    then have "u \<noteq> 0" by auto
    have "0 + u \<in> affine hull S"
      using \<open>u \<in> affine hull S\<close> by simp
    from ray_to_rel_frontier[OF assms(2) assms(3) this \<open>u \<noteq> 0\<close>]
    obtain d where "d > 0" and d_rf: "0 + d *\<^sub>R u \<in> rel_frontier S"
      by blast
    then have du_rf: "d *\<^sub>R u \<in> rel_frontier S" by simp
    have "(d *\<^sub>R u) /\<^sub>R norm (d *\<^sub>R u) = u"
      using \<open>d > 0\<close> \<open>norm u = 1\<close> by (simp add: norm_scaleR)
    then show "u \<in> (\<lambda>x. x /\<^sub>R norm x) ` rel_frontier S"
      using du_rf by force

  qed

  \<comment> \<open>Injectivity from inverse Lipschitz\<close>
  have x_ne: "\<And>x. x \<in> rel_frontier S \<Longrightarrow> x \<noteq> 0"
    using assms(3) by (auto simp: rel_frontier_def)
  have inj: "inj_on (\<lambda>x. x /\<^sub>R norm x) (rel_frontier S)"
  proof (rule inj_onI)
    fix x y assume mem: "x \<in> rel_frontier S" "y \<in> rel_frontier S"
      and eq: "x /\<^sub>R norm x = y /\<^sub>R norm y"
    have "b * dist x y \<le> dist ((1 / norm x) *\<^sub>R x) ((1 / norm y) *\<^sub>R y)"
      using b[OF mem] .
    also have "\<dots> = dist (x /\<^sub>R norm x) (y /\<^sub>R norm y)"
      using x_ne[OF mem(1)] x_ne[OF mem(2)] by (simp add: field_simps)
    also have "\<dots> = 0" using eq by simp
    finally show "x = y" using \<open>b > 0\<close> by (simp add: mult_le_0_iff dist_le_zero_iff)
  qed

  \<comment> \<open>Apply homeomorphism_compact\<close>
  have "compact (rel_frontier S)"
    using compact_rel_frontier_bounded assms(2) by blast
  then obtain g where homeo: "homeomorphism (rel_frontier S)
      (sphere 0 1 \<inter> affine hull S) (\<lambda>x. x /\<^sub>R norm x) g"
    using homeomorphism_compact[OF _ cont image_eq inj] by blast
  \<comment> \<open>Lipschitz bound for the projection (first conjunct)\<close>
  have lip_f: "\<exists>B. \<forall>x y. x \<in> rel_frontier S \<longrightarrow> y \<in> rel_frontier S \<longrightarrow>
        norm (x /\<^sub>R norm x - y /\<^sub>R norm y) \<le> B * norm (x - y)"
  proof (intro exI allI impI)
    fix x y assume "x \<in> rel_frontier S" "y \<in> rel_frontier S"
    then show "norm (x /\<^sub>R norm x - y /\<^sub>R norm y) \<le> B * norm (x - y)"
      using B[of x y] by (simp add: dist_norm)
  qed
  \<comment> \<open>Lipschitz bound for g (from inverse Lipschitz of f)\<close>
  have lip_g: "\<exists>B. \<forall>x y. x \<in> sphere 0 1 \<inter> affine hull S \<longrightarrow>
                          y \<in> sphere 0 1 \<inter> affine hull S \<longrightarrow>
        norm (g x - g y) \<le> B * norm (x - y)"
  proof (intro exI allI impI)
    fix u v assume uv: "u \<in> sphere 0 1 \<inter> affine hull S"
                       "v \<in> sphere 0 1 \<inter> affine hull S"
    have u_img: "u \<in> (\<lambda>x. x /\<^sub>R norm x) ` rel_frontier S"
      and v_img: "v \<in> (\<lambda>x. x /\<^sub>R norm x) ` rel_frontier S"
      using uv image_eq by auto
    have gu: "g u \<in> rel_frontier S" and gv: "g v \<in> rel_frontier S"
      using homeomorphism_image2[OF homeo] uv by auto
    have fu: "(g u) /\<^sub>R norm (g u) = u" and fv: "(g v) /\<^sub>R norm (g v) = v"
      using homeomorphism_apply2[OF homeo uv(1)] homeomorphism_apply2[OF homeo uv(2)] by auto
    have "b * dist (g u) (g v) \<le> dist ((1 / norm (g u)) *\<^sub>R (g u)) ((1 / norm (g v)) *\<^sub>R (g v))"
      using b[OF gu gv] .
    also have "dist ((1 / norm (g u)) *\<^sub>R (g u)) ((1 / norm (g v)) *\<^sub>R (g v)) = dist u v"
      using fu fv by (simp add: field_simps)
    finally have "b * dist (g u) (g v) \<le> dist u v" .
    then have "dist (g u) (g v) \<le> (1/b) * dist u v"
      using \<open>b > 0\<close> by (simp add: field_simps)
    then show "norm (g u - g v) \<le> (1/b) * norm (u - v)"
      by (simp add: dist_norm)
  qed
  show ?thesis
    using homeo lip_f lip_g by blast
qed

\<comment> \<open>HOL Light: lemma1 for (bilipschitz homeomorphism between relative frontiers)\<close>
lemma bilipschitz_homeomorphism_rel_frontiers_aux:
  fixes S t :: "'a::euclidean_space set"
  assumes "convex S" "bounded S" "convex t" "bounded t"
    "0 \<in> rel_interior S" "0 \<in> rel_interior t"
    "affine hull S = affine hull t"
  shows "\<exists>f g. homeomorphism (rel_frontier S) (rel_frontier t) f g \<and>
               (\<exists>B. \<forall>x y. x \<in> rel_frontier S \<longrightarrow> y \<in> rel_frontier S \<longrightarrow>
                     norm (f x - f y) \<le> B * norm (x - y)) \<and>
               (\<exists>B. \<forall>x y. x \<in> rel_frontier t \<longrightarrow> y \<in> rel_frontier t \<longrightarrow>
                     norm (g x - g y) \<le> B * norm (x - y))"
proof -
  let ?n = "\<lambda>x::'a. x /\<^sub>R norm x"
  \<comment> \<open>Get bilipschitz homeomorphisms for S and t\<close>
  obtain gs where homeo_s: "homeomorphism (rel_frontier S) (sphere 0 1 \<inter> affine hull S) ?n gs"
    and lip_ns: "\<exists>B. \<forall>x y. x \<in> rel_frontier S \<longrightarrow> y \<in> rel_frontier S \<longrightarrow>
          norm (?n x - ?n y) \<le> B * norm (x - y)"
    and lip_gs: "\<exists>B. \<forall>x y. x \<in> sphere 0 1 \<inter> affine hull S \<longrightarrow>
                            y \<in> sphere 0 1 \<inter> affine hull S \<longrightarrow>
          norm (gs x - gs y) \<le> B * norm (x - y)"
    using bilipschitz_homeomorphism_spherical_projection[OF assms(1,2,5)] by blast
  obtain gt where homeo_t: "homeomorphism (rel_frontier t) (sphere 0 1 \<inter> affine hull t) ?n gt"
    and lip_nt: "\<exists>B. \<forall>x y. x \<in> rel_frontier t \<longrightarrow> y \<in> rel_frontier t \<longrightarrow>
          norm (?n x - ?n y) \<le> B * norm (x - y)"
    and lip_gt: "\<exists>B. \<forall>x y. x \<in> sphere 0 1 \<inter> affine hull t \<longrightarrow>
                            y \<in> sphere 0 1 \<inter> affine hull t \<longrightarrow>
          norm (gt x - gt y) \<le> B * norm (x - y)"
    using bilipschitz_homeomorphism_spherical_projection[OF assms(3,4,6)] by blast
  \<comment> \<open>Since affine hull S = affine hull t, the intermediate spaces are the same\<close>
  have mid_eq: "sphere 0 1 \<inter> affine hull S = sphere 0 1 \<inter> affine hull t"
    using assms(7) by simp
  \<comment> \<open>Flip the t-homeomorphism: gt maps sphere \<inter> aff to rel_frontier t\<close>
  have homeo_t': "homeomorphism (sphere 0 1 \<inter> affine hull S) (rel_frontier t) gt ?n"
    using homeomorphism_symD[OF homeo_t] mid_eq by simp
  \<comment> \<open>Compose: gt \<circ> n maps rel_frontier S \<rightarrow> rel_frontier t\<close>
  have homeo_comp: "homeomorphism (rel_frontier S) (rel_frontier t) (gt \<circ> ?n) (gs \<circ> ?n)"
    using homeomorphism_compose[OF homeo_s homeo_t'] by simp
  \<comment> \<open>Lipschitz bound for gt \<circ> n on rel_frontier S\<close>
  have lip_f: "\<exists>B. \<forall>x y. x \<in> rel_frontier S \<longrightarrow> y \<in> rel_frontier S \<longrightarrow>
        norm ((gt \<circ> ?n) x - (gt \<circ> ?n) y) \<le> B * norm (x - y)"
  proof -
    obtain Bn where Bn: "\<And>x y. x \<in> rel_frontier S \<Longrightarrow> y \<in> rel_frontier S \<Longrightarrow>
        norm (?n x - ?n y) \<le> Bn * norm (x - y)"
      using lip_ns by blast
    obtain Bg where Bg: "\<And>x y. x \<in> sphere 0 1 \<inter> affine hull S \<Longrightarrow>
        y \<in> sphere 0 1 \<inter> affine hull S \<Longrightarrow>
        norm (gt x - gt y) \<le> Bg * norm (x - y)"
      using lip_gt mid_eq by auto
    have img_s: "?n ` rel_frontier S = sphere 0 1 \<inter> affine hull S"
      using homeomorphism_image1[OF homeo_s] .
    \<comment> \<open>Convert to lipschitz_on form\<close>
    have lip_n: "(max Bn 0)-lipschitz_on (rel_frontier S) ?n"
    proof (rule lipschitz_onI)
      fix x y assume "x \<in> rel_frontier S" "y \<in> rel_frontier S"
      then have "dist (?n x) (?n y) \<le> Bn * dist x y"
        using Bn by (simp add: dist_norm)
      also have "\<dots> \<le> max Bn 0 * dist x y"
        by (intro mult_right_mono) auto
      finally show "dist (?n x) (?n y) \<le> max Bn 0 * dist x y" .
    qed simp
    have lip_g: "(max Bg 0)-lipschitz_on (sphere 0 1 \<inter> affine hull S) gt"
    proof (rule lipschitz_onI)
      fix x y assume "x \<in> sphere 0 1 \<inter> affine hull S" "y \<in> sphere 0 1 \<inter> affine hull S"
      then have "dist (gt x) (gt y) \<le> Bg * dist x y"
        using Bg by (simp add: dist_norm)
      also have "\<dots> \<le> max Bg 0 * dist x y"
        by (intro mult_right_mono) auto
      finally show "dist (gt x) (gt y) \<le> max Bg 0 * dist x y" .
    qed simp
    have "?n ` rel_frontier S = sphere 0 1 \<inter> affine hull S"
      using img_s .
    then have lip_comp: "(max Bg 0 * max Bn 0)-lipschitz_on (rel_frontier S) (gt \<circ> ?n)"
      using lipschitz_on_compose[OF lip_n lip_g[unfolded img_s[symmetric]]]
      by (simp add: img_s)
    show ?thesis
    proof (intro exI allI impI)
      fix x y assume "x \<in> rel_frontier S" "y \<in> rel_frontier S"
      then show "norm ((gt \<circ> ?n) x - (gt \<circ> ?n) y) \<le> (max Bg 0 * max Bn 0) * norm (x - y)"
        using lipschitz_onD[OF lip_comp] by (simp add: dist_norm)
    qed
  qed
  \<comment> \<open>Lipschitz bound for gs \<circ> n on rel_frontier t\<close>
  have lip_g: "\<exists>B. \<forall>x y. x \<in> rel_frontier t \<longrightarrow> y \<in> rel_frontier t \<longrightarrow>
        norm ((gs \<circ> ?n) x - (gs \<circ> ?n) y) \<le> B * norm (x - y)"
  proof -
    obtain Bn where Bn: "\<And>x y. x \<in> rel_frontier t \<Longrightarrow> y \<in> rel_frontier t \<Longrightarrow>
        norm (?n x - ?n y) \<le> Bn * norm (x - y)"
      using lip_nt by blast
    obtain Bg where Bg: "\<And>x y. x \<in> sphere 0 1 \<inter> affine hull S \<Longrightarrow>
        y \<in> sphere 0 1 \<inter> affine hull S \<Longrightarrow>
        norm (gs x - gs y) \<le> Bg * norm (x - y)"
      using lip_gs by blast
    have img_t: "?n ` rel_frontier t = sphere 0 1 \<inter> affine hull t"
      using homeomorphism_image1[OF homeo_t] .
    \<comment> \<open>Convert to lipschitz_on form\<close>
    have lip_n: "(max Bn 0)-lipschitz_on (rel_frontier t) ?n"
    proof (rule lipschitz_onI)
      fix x y assume "x \<in> rel_frontier t" "y \<in> rel_frontier t"
      then have "dist (?n x) (?n y) \<le> Bn * dist x y"
        using Bn by (simp add: dist_norm)
      also have "\<dots> \<le> max Bn 0 * dist x y"
        by (intro mult_right_mono) auto
      finally show "dist (?n x) (?n y) \<le> max Bn 0 * dist x y" .
    qed simp
    have lip_gs': "(max Bg 0)-lipschitz_on (sphere 0 1 \<inter> affine hull S) gs"
    proof (rule lipschitz_onI)
      fix x y assume "x \<in> sphere 0 1 \<inter> affine hull S" "y \<in> sphere 0 1 \<inter> affine hull S"
      then have "dist (gs x) (gs y) \<le> Bg * dist x y"
        using Bg by (simp add: dist_norm)
      also have "\<dots> \<le> max Bg 0 * dist x y"
        by (intro mult_right_mono) auto
      finally show "dist (gs x) (gs y) \<le> max Bg 0 * dist x y" .
    qed simp
    have lip_comp: "(max Bg 0 * max Bn 0)-lipschitz_on (rel_frontier t) (gs \<circ> ?n)"
      using lipschitz_on_compose[OF lip_n lip_gs'[unfolded mid_eq img_t[symmetric]]]
      by simp
    show ?thesis
    proof (intro exI allI impI)
      fix x y assume "x \<in> rel_frontier t" "y \<in> rel_frontier t"
      then show "norm ((gs \<circ> ?n) x - (gs \<circ> ?n) y) \<le> (max Bg 0 * max Bn 0) * norm (x - y)"
        using lipschitz_onD[OF lip_comp] by (simp add: dist_norm)
    qed
  qed
  show ?thesis
    using homeo_comp lip_f lip_g by blast
qed

lemma bilipschitz_homeomorphism_rel_frontiers_aux2:
  fixes S :: "'a::euclidean_space set" and t :: "'b::euclidean_space set"
  assumes "convex S" "bounded S" "convex t" "bounded t"
    and "0 \<in> rel_interior S"
    and "0 \<in> rel_interior t"
    and "dim S = dim t"
  obtains f g where "homeomorphism (rel_frontier S) (rel_frontier t) f g"
               "\<exists>B. \<forall>x\<in>rel_frontier S. \<forall>y\<in>rel_frontier S.
                     norm (f x - f y) \<le> B * norm (x - y)"
               "\<exists>B. \<forall>x\<in>rel_frontier t. \<forall>y\<in>rel_frontier t.
                     norm (g x - g y) \<le> B * norm (x - y)"
proof -
  obtain h k where
    lin_h: "linear h" and lin_k: "linear k"
    and im_h: "h ` span S = span t" and im_k: "k ` span t = span S"
    and norm_h: "\<And>x. x \<in> span S \<Longrightarrow> norm (h x) = norm x"
    and norm_k: "\<And>y. y \<in> span t \<Longrightarrow> norm (k y) = norm y"
    and kh: "\<And>x. x \<in> span S \<Longrightarrow> k (h x) = x"
    and hk: "\<And>y. y \<in> span t \<Longrightarrow> h (k y) = y"
    using isometries_subspaces [of "span S" "span t"] \<open>dim S = dim t\<close> by auto
  have aff_h: "h ` (affine hull S) = affine hull t"
    by (metis \<open>0 \<in> rel_interior S\<close> \<open>0 \<in> rel_interior t\<close> conic_hull_eq_span_affine_hull im_h)
  have rel_frontier_h: "rel_frontier (h ` S) = h ` rel_frontier S"
  proof -
    have inj_h: "inj_on h (span S)"
      using kh by (intro inj_onI) (metis)
    have cls_span: "closure S \<subseteq> span S"
      using closure_minimal [OF span_superset closed_span] by blast
    have "rel_frontier (h ` S) = closure (h ` S) - rel_interior (h ` S)"
      by (simp add: rel_frontier_def)
    also have "closure (h ` S) = h ` closure S"
      using closure_bounded_linear_image [OF lin_h \<open>bounded S\<close>] by simp
    also have "rel_interior (h ` S) = h ` rel_interior S"
      using rel_interior_convex_linear_image [OF lin_h \<open>convex S\<close>] by simp
    also have "h ` closure S - h ` rel_interior S = h ` (closure S - rel_interior S)"
      using inj_on_image_set_diff [OF inj_h]
        cls_span rel_interior_subset [of S] span_superset [of S]
      by (metis Diff_subset order_trans)
    also have "closure S - rel_interior S = rel_frontier S"
      by (simp add: rel_frontier_def)
    finally show ?thesis .
  qed
  have aff_hs: "affine hull (h ` S) = affine hull t"
    by (metis affine_hull_span_0 \<open>0 \<in> rel_interior S\<close> \<open>0 \<in> rel_interior t\<close> hull_inc im_h lin_h
        linear_0 linear_span_image mem_rel_interior_ball rev_image_eqI)
  have bdd_hs: "bounded (h ` S)"
    using bounded_linear_image[OF \<open>bounded S\<close>] lin_h linear_linear by blast
  have ri_hs: "0 \<in> rel_interior (h ` S)"
    using rel_interior_convex_linear_image[OF lin_h \<open>convex S\<close>] \<open>0 \<in> rel_interior S\<close>
      linear_0[OF lin_h] by (metis image_eqI)
  obtain f g where
    homeo_fg: "homeomorphism (rel_frontier (h ` S)) (rel_frontier t) f g"
    and lip_f: "\<exists>B. \<forall>x y. x \<in> rel_frontier (h ` S) \<longrightarrow> y \<in> rel_frontier (h ` S) \<longrightarrow>
                     norm (f x - f y) \<le> B * norm (x - y)"
    and lip_g: "\<exists>B. \<forall>x y. x \<in> rel_frontier t \<longrightarrow> y \<in> rel_frontier t \<longrightarrow>
                     norm (g x - g y) \<le> B * norm (x - y)"
    using bilipschitz_homeomorphism_rel_frontiers_aux
      [OF convex_linear_image[OF lin_h \<open>convex S\<close>] bdd_hs
          \<open>convex t\<close> \<open>bounded t\<close> ri_hs \<open>0 \<in> rel_interior t\<close> aff_hs]
    by blast
  let ?f = "f o h"
  let ?g = "k o g"
  show thesis 
  proof
    show "homeomorphism (rel_frontier S) (rel_frontier t) ?f ?g"
    proof (rule homeomorphism_compose)
      show "homeomorphism (rel_frontier S) (h ` rel_frontier S) h k"
      proof (unfold homeomorphism_def, intro conjI ballI)
        have rfs_span: "rel_frontier S \<subseteq> span S"
          using rel_frontier_affine_hull affine_hull_subset_span order_trans by blast
        show "h ` rel_frontier S = h ` rel_frontier S" by simp
        show "continuous_on (rel_frontier S) h"
          using lin_h linear_continuous_on by (metis linear_linear)
        show "k ` h ` rel_frontier S = rel_frontier S"
          using kh rfs_span by (force simp: image_comp)
        show "continuous_on (h ` rel_frontier S) k"
          using lin_k linear_continuous_on by (metis linear_linear)
      next
        fix x assume "x \<in> rel_frontier S"
        then show "k (h x) = x" using kh rel_frontier_affine_hull affine_hull_subset_span by blast
      next
        fix y assume "y \<in> h ` rel_frontier S"
        then obtain x where "x \<in> rel_frontier S" "y = h x" by auto
        then have "x \<in> span S" using rel_frontier_affine_hull affine_hull_subset_span by blast
        then have "h x \<in> span t" using im_h by blast
        then show "h (k y) = y" using hk \<open>y = h x\<close> by auto
      qed
    next
      show "homeomorphism (h ` rel_frontier S) (rel_frontier t) f g"
        using homeo_fg rel_frontier_h by simp
    qed
    show "\<exists>B. \<forall>x\<in>rel_frontier S. \<forall>y\<in>rel_frontier S. norm ((?f x::'b) - ?f y) \<le> B * norm (x - y)"
    proof -
      obtain B where B: "\<And>x y. x \<in> rel_frontier (h ` S) \<Longrightarrow> y \<in> rel_frontier (h ` S) \<Longrightarrow>
                          norm (f x - f y) \<le> B * norm (x - y)"
        using lip_f by blast
      have "\<forall>x\<in>rel_frontier S. \<forall>y\<in>rel_frontier S. norm ((f \<circ> h) x - (f \<circ> h) y) \<le> B * norm (x - y)"
      proof (intro ballI)
        fix x y assume x: "x \<in> rel_frontier S" and y: "y \<in> rel_frontier S"
        have hx: "h x \<in> rel_frontier (h ` S)" using x rel_frontier_h by auto
        have hy: "h y \<in> rel_frontier (h ` S)" using y rel_frontier_h by auto
        have xs: "x \<in> span S"
          using \<open>0 \<in> rel_interior S\<close> conic_hull_eq_span_affine_hull rel_frontier_affine_hull x by fastforce
        have ys: "y \<in> span S"
          using affine_hull_subset_span closure_affine_hull rel_frontier_def y by fastforce
        show "norm ((f \<circ> h) x - (f \<circ> h) y) \<le> B * norm (x - y)"
          by (smt (verit) B comp_def hx hy lin_h linear_diff norm_h span_diff xs ys)
      qed
      then show ?thesis by auto
    qed
    show "\<exists>B. \<forall>x\<in>rel_frontier t. \<forall>y\<in>rel_frontier t. norm ((?g x::'a) - ?g y) \<le> B * norm (x - y)"
    proof -
      obtain B where B: "\<And>x y. x \<in> rel_frontier t \<Longrightarrow> y \<in> rel_frontier t \<Longrightarrow>
                          norm (g x - g y) \<le> B * norm (x - y)"
        using lip_g by blast
      have g_in_span: "\<And>x. x \<in> rel_frontier t \<Longrightarrow> g x \<in> span t"
        by (metis aff_hs affine_hull_span_0 homeo_fg homeomorphism_def hull_inc imageI
            rel_frontier_affine_hull rel_interior_subset ri_hs subsetD)
      then show ?thesis
        by (metis (no_types, lifting) B comp_def g_in_span lin_k linear_diff norm_k span_diff)
    qed
  qed
qed

\<comment> \<open>HOL Light: BILIPSCHITZ_HOMEOMORPHISM_RELATIVE_FRONTIERS\<close>
lemma bilipschitz_homeomorphism_rel_frontiers:
  fixes S t :: "'a::euclidean_space set"
  assumes "convex S" "bounded S" "convex t" "bounded t" and eq: "aff_dim S = aff_dim t"
  obtains f g where "homeomorphism (rel_frontier S) (rel_frontier t) f g"
               "\<exists>B. \<forall>x y. x \<in> rel_frontier S \<longrightarrow> y \<in> rel_frontier S \<longrightarrow>
                     norm (f x - f y) \<le> B * norm (x - y)"
               "\<exists>B. \<forall>x y. x \<in> rel_frontier t \<longrightarrow> y \<in> rel_frontier t \<longrightarrow>
                     norm (g x - g y) \<le> B * norm (x - y)"
proof (cases "S={} \<or> t={}")
  case True
  then show ?thesis
    by (metis that aff_dim_negative_iff eq empty_iff homeomorphism_empty rel_frontier_empty)
next
  case False
  obtain a b where a: "a \<in> rel_interior S" and b: "b \<in> rel_interior t"
    using False rel_interior_eq_empty[OF \<open>convex S\<close>] rel_interior_eq_empty[OF \<open>convex t\<close>]
    by blast
  have dim_eq: "dim ((+) (-a) ` S) = dim ((+) (-b) ` t)"
    by (metis a aff_dim_eq_dim eq b hull_inc mem_rel_interior_ball of_nat_eq_iff)
  have ri_s: "0 \<in> rel_interior ((+) (-a) ` S)"
    using a rel_interior_translation[of "-a" S] by (auto simp: image_iff)
  have ri_t: "0 \<in> rel_interior ((+) (-b) ` t)"
    using b rel_interior_translation[of "-b" t] by (auto simp: image_iff)
  obtain f g where
    homeo: "homeomorphism (rel_frontier ((+) (-a) ` S)) (rel_frontier ((+) (-b) ` t)) f g"
    and lip_f: "\<exists>B. \<forall>x\<in>rel_frontier ((+) (-a) ` S). \<forall>y\<in>rel_frontier ((+) (-a) ` S).
                     norm (f x - f y) \<le> B * norm (x - y)"
    and lip_g: "\<exists>B. \<forall>x\<in>rel_frontier ((+) (-b) ` t). \<forall>y\<in>rel_frontier ((+) (-b) ` t).
                     norm (g x - g y) \<le> B * norm (x - y)"
    using bilipschitz_homeomorphism_rel_frontiers_aux2
      [OF convex_translation[OF \<open>convex S\<close>] bounded_translation[OF \<open>bounded S\<close>]
          convex_translation[OF \<open>convex t\<close>] bounded_translation[OF \<open>bounded t\<close>]
          ri_s ri_t dim_eq]
    by blast
  have rfs: "rel_frontier ((+) (-a) ` S) = (+) (-a) ` rel_frontier S"
    by (rule rel_frontier_translation)
  have rft: "rel_frontier ((+) (-b) ` t) = (+) (-b) ` rel_frontier t"
    by (rule rel_frontier_translation)
  obtain B B' where
    lip_fs: "\<And>x y. x \<in> rel_frontier S \<Longrightarrow> y \<in> rel_frontier S \<Longrightarrow>
                    norm (f (-a + x) - f (-a + y)) \<le> B * norm (x - y)"
    and lip_gt: "\<And>x y. x \<in> rel_frontier t \<Longrightarrow> y \<in> rel_frontier t \<Longrightarrow>
                    norm (g (-b + x) - g (-b + y)) \<le> B' * norm (x - y)"
  proof -
    obtain B where B: "\<forall>x\<in>rel_frontier ((+) (-a) ` S). \<forall>y\<in>rel_frontier ((+) (-a) ` S).
                        norm (f x - f y) \<le> B * norm (x - y)"
      using lip_f by blast
    obtain B' where B': "\<forall>x\<in>rel_frontier ((+) (-b) ` t). \<forall>y\<in>rel_frontier ((+) (-b) ` t).
                          norm (g x - g y) \<le> B' * norm (x - y)"
      using lip_g by blast
    show thesis
    proof
      fix x y assume "x \<in> rel_frontier S" "y \<in> rel_frontier S"
      then have xy: "-a + x \<in> rel_frontier ((+) (-a) ` S)" "-a + y \<in> rel_frontier ((+) (-a) ` S)"
        unfolding rfs by (auto simp: image_iff)
      then show "norm (f (-a + x) - f (-a + y)) \<le> B * norm (x - y)"
        using bspec[OF bspec[OF B xy(1)] xy(2)] by simp
    next
      fix x y assume "x \<in> rel_frontier t" "y \<in> rel_frontier t"
      then have xy: "-b + x \<in> rel_frontier ((+) (-b) ` t)" "-b + y \<in> rel_frontier ((+) (-b) ` t)"
        unfolding rft by (auto simp: image_iff)
      then show "norm (g (-b + x) - g (-b + y)) \<le> B' * norm (x - y)"
        using bspec[OF bspec[OF B' xy(1)] xy(2)] by simp
    qed
  qed
  let ?f = "\<lambda>x. b + f (-a + x)"
  let ?g = "\<lambda>x. a + g (-b + x)"
  show thesis
  proof
    show "homeomorphism (rel_frontier S) (rel_frontier t) ?f ?g"
    proof -
      note homeo_parts = homeo[unfolded homeomorphism_def rfs rft]
      have cf: "continuous_on ((+) (-a) ` rel_frontier S) f"
        using homeo_parts by blast
      have cg: "continuous_on ((+) (-b) ` rel_frontier t) g"
        using homeo_parts by blast
      have gf0: "\<And>x. x \<in> (+) (-a) ` rel_frontier S \<Longrightarrow> g (f x) = x"
        using homeo_parts by blast
      have fg0: "\<And>y. y \<in> (+) (-b) ` rel_frontier t \<Longrightarrow> f (g y) = y"
        using homeo_parts by blast
      have gf: "\<And>x. x \<in> rel_frontier S \<Longrightarrow> ?g (?f x) = x"
        using gf0[of "-a + _"] by (auto simp: algebra_simps image_iff)
      have fg: "\<And>y. y \<in> rel_frontier t \<Longrightarrow> ?f (?g y) = y"
        using fg0[of "-b + _"] by (auto simp: algebra_simps image_iff)
      have im_f: "?f ` rel_frontier S = rel_frontier t"
        by (metis homeo_parts image_image translation_galois)
      have im_g: "?g ` rel_frontier t = rel_frontier S"
        by (metis homeo_parts image_image translation_galois)
      have cont_f: "continuous_on (rel_frontier S) ?f"
        using continuous_on_compose[OF _ cf]
          continuous_on_translation_eq[of _ "-a" id] continuous_on_translation_eq[of _ b "f \<circ> (+) (-a)"]
        by (simp add: o_def)
      have cont_g: "continuous_on (rel_frontier t) ?g"
        using continuous_on_compose[OF _ cg]
          continuous_on_translation_eq[of _ "-b" id] continuous_on_translation_eq[of _ a "g \<circ> (+) (-b)"]
        by (simp add: o_def)
      show ?thesis
        unfolding homeomorphism_def
        using gf fg im_f im_g cont_f cont_g by blast
    qed
  next
    show "\<exists>B. \<forall>x y. x \<in> rel_frontier S \<longrightarrow> y \<in> rel_frontier S \<longrightarrow> norm ((?f x::'a) - ?f y) \<le> B * norm (x - y)"
        using lip_fs by (force simp: algebra_simps)
    show "\<exists>B. \<forall>x y. x \<in> rel_frontier t \<longrightarrow> y \<in> rel_frontier t \<longrightarrow> norm ((?g x::'a) - ?g y) \<le> B * norm (x - y)"
        using lip_gt by (force simp: algebra_simps)
  qed
qed


\<comment> \<open>HOL Light: RECTIFIABLE_LOOP_RELATIVE_FRONTIER_CONVEX\<close>
lemma rectifiable_loop_rel_frontier_convex:
  fixes S :: "complex set"
  assumes "bounded S" "convex S" "aff_dim S = 2"
  shows "\<exists>g. simple_path g \<and> rectifiable_path g \<and>
             pathfinish g = pathstart g \<and>
             path_image g = rel_frontier S"
proof -
  \<comment> \<open>The unit disk in \<complex> has aff_dim = 2\<close>
  have int_cball: "interior (cball (0::complex) 1) \<noteq> {}"
    by (auto simp: interior_cball)
  have aff_cball: "aff_dim (cball (0::complex) 1) = 2"
    using aff_dim_nonempty_interior[OF int_cball] DIM_complex by simp
  have fr_cball: "rel_frontier (cball (0::complex) 1) = sphere 0 1"
    using rel_frontier_nonempty_interior[OF int_cball] frontier_cball by simp
  \<comment> \<open>Apply bilipschitz homeomorphism between relative frontiers\<close>
  obtain f g where homeo: "homeomorphism (sphere 0 1) (rel_frontier S) f g"
    and lip_f: "\<exists>B. \<forall>x y. x \<in> sphere (0::complex) 1 \<longrightarrow> y \<in> sphere 0 1 \<longrightarrow>
                    norm (f x - f y) \<le> B * norm (x - y)"
    and lip_g: "\<exists>B. \<forall>x y. x \<in> rel_frontier S \<longrightarrow> y \<in> rel_frontier S \<longrightarrow>
                    norm (g x - g y) \<le> B * norm (x - y)"
  proof -
    have eq: "aff_dim (cball (0::complex) 1) = aff_dim S"
      using aff_cball assms(3) by simp
    obtain f g where h: "homeomorphism (rel_frontier (cball (0::complex) 1)) (rel_frontier S) f g"
      and lf: "\<exists>B. \<forall>x y. x \<in> rel_frontier (cball (0::complex) 1) \<longrightarrow>
                      y \<in> rel_frontier (cball (0::complex) 1) \<longrightarrow>
                      norm (f x - f y) \<le> B * norm (x - y)"
      and lg: "\<exists>B. \<forall>x y. x \<in> rel_frontier S \<longrightarrow> y \<in> rel_frontier S \<longrightarrow>
                      norm (g x - g y) \<le> B * norm (x - y)"
      using bilipschitz_homeomorphism_rel_frontiers
              [OF convex_cball bounded_cball assms(2) assms(1) eq]
      by blast
    show thesis using that[of f g] h lf lg fr_cball by simp
  qed
  \<comment> \<open>Define the unit circle parametrization\<close>
  define \<gamma> :: "real \<Rightarrow> complex" where "\<gamma> \<equiv> \<lambda>t. cis (2 * pi * t)"
  \<comment> \<open>Basic properties of \<gamma>\<close>
  have \<gamma>_img: "\<gamma> ` {0..1} = sphere 0 1"
  proof (intro set_eqI iffI)
    fix z :: complex assume "z \<in> \<gamma> ` {0..1}"
    then show "z \<in> sphere 0 1" unfolding \<gamma>_def by (auto simp: norm_cis)
  next
    fix z :: complex assume z: "z \<in> sphere 0 1"
    then have "z \<noteq> 0" by auto
    define t where "t = (if Arg z \<ge> 0 then Arg z else Arg z + 2*pi) / (2*pi)"
    have "t \<in> {0..1}"
      using Arg_correct [of z] \<open>z \<noteq> 0\<close> by (auto simp: t_def)
    moreover have "\<gamma> t = z"
    proof -
      have nz: "cmod z = 1" using z by simp
      have "sgn z = z" using nz by (simp add: complex_sgn_def)
      moreover have "cis (Arg z) = sgn z" using \<open>z \<noteq> 0\<close> by (rule cis_Arg)
      ultimately have cis_arg: "cis (Arg z) = z" by simp
      show ?thesis
      proof (cases "0 \<le> Arg z")
        case True
        then have "\<gamma> t = cis (2 * pi * (Arg z / (2 * pi)))" by (simp add: t_def \<gamma>_def)
        also have "\<dots> = z" using pi_gt_zero by (simp add: cis_arg)
        finally show ?thesis .
      next
        case False
        then have "\<gamma> t = cis (2 * pi * ((Arg z + 2 * pi) / (2 * pi)))" by (simp add: t_def \<gamma>_def)
        also have "\<dots> = cis (Arg z) * cis (2 * pi)" by (simp add: cis_mult mult.commute)
        also have "\<dots> = z" by (simp add: cis_arg)
        finally show ?thesis .
      qed
    qed
    ultimately show "z \<in> \<gamma> ` {0..1}" by auto
  qed
  have \<gamma>_start: "\<gamma> 0 = 1" unfolding \<gamma>_def by simp
  have \<gamma>_end: "\<gamma> 1 = 1" unfolding \<gamma>_def using cis_2pi by simp
  have \<gamma>_cont: "continuous_on {0..1} \<gamma>"
    unfolding \<gamma>_def by (intro continuous_on_cis continuous_intros)
  have \<gamma>_loop_free: "loop_free \<gamma>"
  proof (unfold loop_free_def, intro ballI impI)
    fix x y assume x: "x \<in> {0..1}" and y: "y \<in> {0..1}" and eq: "\<gamma> x = \<gamma> y"
    have cis_eq: "cis (2 * pi * x) = cis (2 * pi * y)" using eq unfolding \<gamma>_def .
    have cos_eq: "cos (2 * pi * x) = cos (2 * pi * y)"
      using arg_cong[OF cis_eq, of Re] by simp
    have sin_eq: "sin (2 * pi * x) = sin (2 * pi * y)"
      using arg_cong[OF cis_eq, of Im] by simp
    have "cos (2 * pi * x - 2 * pi * y) = 
          cos (2 * pi * x) * cos (2 * pi * y) + sin (2 * pi * x) * sin (2 * pi * y)"
      by (rule cos_diff)
    also have "\<dots> = (cos (2 * pi * x))\<^sup>2 + (sin (2 * pi * x))\<^sup>2"
      using cos_eq sin_eq by (simp add: power2_eq_square)
    also have "\<dots> = 1" by (rule sin_cos_squared_add2)
    finally have "cos (2 * pi * (x - y)) = 1"
      by (simp add: algebra_simps)
    then obtain n :: int where n: "2 * pi * (x - y) = real_of_int n * 2 * pi"
      using cos_one_2pi_int by blast
    then have xy: "x - y = real_of_int n"
      by auto
    have "real_of_int n \<in> {-1..1}" using x y xy by auto
    then have "n \<in> {-1..1}" by auto
    then have "n = 0 \<or> n = 1 \<or> n = -1" by auto
    then show "x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
      using xy x y by auto
  qed
  \<comment> \<open>\<gamma> is Lipschitz on {0..1}\<close>
  have \<gamma>_lip: "\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. norm (\<gamma> x - \<gamma> y) \<le> (2*pi) * norm (x - y)"
  proof (intro ballI)
    fix x y :: real assume x: "x \<in> {0..1}" and y: "y \<in> {0..1}"
    have deriv: "\<forall>t\<in>{0..1}. (\<gamma> has_derivative (\<lambda>h. (2*pi*h) *\<^sub>R (\<i> * cis (2*pi*t)))) (at t within {0..1})"
    proof (intro ballI)
      fix t :: real assume "t \<in> {0..1}"
      have "((\<lambda>t. 2*pi*t) has_derivative (\<lambda>h. 2*pi*h)) (at t within {0..1})"
        by (auto intro!: derivative_eq_intros)
      then show "(\<gamma> has_derivative (\<lambda>h. (2*pi*h) *\<^sub>R (\<i> * cis (2*pi*t)))) (at t within {0..1})"
        unfolding \<gamma>_def using has_derivative_cis by blast
    qed
    have bound: "\<forall>t\<in>{0..1}. onorm (\<lambda>h. (2*pi*h) *\<^sub>R (\<i> * cis (2*pi*t))) \<le> 2*pi"
    proof (intro ballI)
      fix t :: real assume "t \<in> {0..1}"
      show "onorm (\<lambda>h. (2*pi*h) *\<^sub>R (\<i> * cis (2*pi*t))) \<le> 2*pi"
      proof (rule onorm_le)
        fix h :: real
        have "norm ((2*pi*h) *\<^sub>R (\<i> * cis (2*pi*t))) = \<bar>2*pi*h\<bar> * norm (\<i> * cis (2*pi*t))"
          by (simp add: norm_scaleR)
        also have "\<dots> = 2*pi * \<bar>h\<bar>" by (simp add: abs_mult norm_mult norm_cis)
        also have "\<dots> = 2*pi * norm h" by simp
        finally show "norm ((2*pi*h) *\<^sub>R (\<i> * cis (2*pi*t))) \<le> 2*pi * norm h" by simp
      qed
    qed
    show "norm (\<gamma> x - \<gamma> y) \<le> (2*pi) * norm (x - y)"
    proof -
      have d: "\<And>t. t \<in> {0..1} \<Longrightarrow> (\<gamma> has_derivative (\<lambda>h. (2*pi*h) *\<^sub>R (\<i> * cis (2*pi*t)))) (at t within {0..1})"
        using deriv by auto
      have b: "\<And>t. t \<in> {0..1} \<Longrightarrow> onorm (\<lambda>h. (2*pi*h) *\<^sub>R (\<i> * cis (2*pi*t))) \<le> 2*pi"
        using bound by auto
      show ?thesis using differentiable_bound[OF convex_real_interval(5) d b x y] .
    qed
  qed
  \<comment> \<open>\<gamma> is rectifiable\<close>
  have \<gamma>_rect: "has_bounded_variation_on \<gamma> {0..1}"
  proof (rule Lipschitz_imp_has_bounded_variation)
    show "bounded {0::real..1}" using bounded_cbox[of 0 1] by (simp add: cbox_interval)
  next
    fix x y :: real assume "x \<in> {0..1}" "y \<in> {0..1}"
    then show "norm (\<gamma> x - \<gamma> y) \<le> (2*pi) * norm (x - y)" using \<gamma>_lip by auto
  qed
  \<comment> \<open>Compose f with \<gamma>\<close>
  define p where "p \<equiv> f \<circ> \<gamma>"
  \<comment> \<open>p is a path\<close>
  have p_path: "path p"
    unfolding path_def p_def
    using continuous_on_compose[OF \<gamma>_cont] homeo
    unfolding homeomorphism_def using \<gamma>_img by auto
  \<comment> \<open>p is a closed loop\<close>
  have p_loop: "pathfinish p = pathstart p"
    unfolding pathfinish_def pathstart_def p_def comp_def \<gamma>_start \<gamma>_end by simp
  \<comment> \<open>path_image p = rel_frontier S\<close>
  have p_img: "path_image p = rel_frontier S"
    unfolding path_image_def p_def image_comp \<gamma>_img
    using homeo unfolding homeomorphism_def
    by (metis \<gamma>_img image_comp)
  \<comment> \<open>p is loop_free (hence simple_path)\<close>
  have p_loop_free: "loop_free p"
  proof (unfold loop_free_def, intro ballI impI)
    fix x y assume x: "x \<in> {0..1}" and y: "y \<in> {0..1}" and eq: "p x = p y"
    have "f (\<gamma> x) = f (\<gamma> y)" using eq unfolding p_def comp_def .
    moreover have "\<gamma> x \<in> sphere 0 1" "\<gamma> y \<in> sphere 0 1"
      using x y \<gamma>_img by auto
    ultimately have "\<gamma> x = \<gamma> y"
      using homeo unfolding homeomorphism_def by metis
    then show "x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
      using \<gamma>_loop_free x y unfolding loop_free_def by auto
  qed
  have p_simple: "simple_path p"
    unfolding simple_path_def using p_path p_loop_free by auto
  \<comment> \<open>p is rectifiable\<close>
  have p_rect: "rectifiable_path p"
  proof -
    obtain B where B: "\<And>x y. x \<in> sphere (0::complex) 1 \<longrightarrow> y \<in> sphere 0 1 \<longrightarrow>
                         norm (f x - f y) \<le> B * norm (x - y)"
      using lip_f by blast
    have "\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. norm (p x - p y) \<le> (B * (2*pi)) * norm (x - y)"
    proof (intro ballI)
      fix x y :: real assume x: "x \<in> {0..1}" and y: "y \<in> {0..1}"
      have gx: "\<gamma> x \<in> sphere 0 1" and gy: "\<gamma> y \<in> sphere 0 1"
        using x y \<gamma>_img by auto
      have "norm (p x - p y) = norm (f (\<gamma> x) - f (\<gamma> y))"
        unfolding p_def comp_def by simp
      also have "\<dots> \<le> B * norm (\<gamma> x - \<gamma> y)"
        using B gx gy by auto
      also have "\<dots> \<le> B * (2*pi * norm (x - y))"
      proof (intro mult_left_mono)
        show "norm (\<gamma> x - \<gamma> y) \<le> 2*pi * norm (x - y)"
          using \<gamma>_lip x y by auto
        show "0 \<le> B"
          using B[of 1 "-1"] by simp (smt (verit) norm_ge_zero)
      qed
      also have "\<dots> = (B * (2*pi)) * norm (x - y)" by (simp add: algebra_simps)
      finally show "norm (p x - p y) \<le> (B * (2*pi)) * norm (x - y)" .
    qed
    then show ?thesis
      using lipschitz_imp_rectifiable_path by metis
  qed
  show ?thesis
    using p_simple p_rect p_loop p_img by blast
qed

\<comment> \<open>HOL Light: RECTIFIABLE_LOOP_FRONTIER_CONVEX\<close>
lemma rectifiable_loop_frontier_convex:
  fixes S :: "complex set"
  assumes "bounded S" "convex S" "interior S \<noteq> {}"
  shows "\<exists>g. simple_path g \<and> rectifiable_path g \<and>
             pathfinish g = pathstart g \<and>
             path_image g = frontier S"
  using rectifiable_loop_rel_frontier_convex[OF assms(1,2)]
        rel_frontier_nonempty_interior[OF assms(3)]
        aff_dim_nonempty_interior[OF assms(3)]
  by simp

\<comment> \<open>HOL Light: RECTIFIABLE_PATH_FRONTIER_CONVEX\<close>
lemma rectifiable_path_frontier_convex:
  fixes S :: "complex set"
  assumes "bounded S" "convex S" "S \<noteq> {}"
  shows "\<exists>g. rectifiable_path g \<and>
             pathfinish g = pathstart g \<and>
             path_image g = frontier S"
proof -
  have fr_eq: "frontier S = frontier (closure S)"
    using convex_interior_closure[OF assms(2)] closure_closure[of S]
    by (simp add: frontier_def)
  have cS: "bounded (closure S)" "convex (closure S)" "closure S \<noteq> {}"
    using assms by (auto simp: convex_closure compact_closure closure_eq_empty
                         intro: bounded_closure)
  show ?thesis
  proof (cases "interior (closure S) = {}")
    case False
    then obtain g where "simple_path g" "rectifiable_path g"
      "pathfinish g = pathstart g" "path_image g = frontier (closure S)"
      using rectifiable_loop_frontier_convex[OF cS(1,2)] by auto
    then show ?thesis using fr_eq by blast
  next
    case True
    have compact_cS: "compact (closure S)"
      using assms(1) compact_closure by auto
    have "aff_dim (closure S) \<noteq> int DIM(complex)"
    proof
      assume "aff_dim (closure S) = int DIM(complex)"
      then have "interior (closure S) = rel_interior (closure S)"
        using interior_rel_interior[of "closure S"] by simp
      moreover have "rel_interior (closure S) \<noteq> {}"
        using rel_interior_eq_empty cS(2,3) by auto
      ultimately show False using True by auto
    qed
    then have "aff_dim (closure S) \<le> 1"
      using aff_dim_le_DIM[of "closure S"] by (simp add: DIM_complex)
    then have col: "collinear (closure S)"
      by (simp add: collinear_aff_dim)
    obtain a b where ab: "closure S = closed_segment a b"
      using compact_convex_collinear_segment[OF cS(3) compact_cS cS(2) col]
      by auto
    have "frontier (closure S) = closed_segment a b"
      using interior_closed_segment_ge2[of a b]
            closure_closed_segment[of a b]
      by (simp add: frontier_def ab)
    moreover have "rectifiable_path (linepath a b +++ linepath b a)"
      by (simp add: rectifiable_path_join rectifiable_path_linepath)
    moreover have "pathfinish (linepath a b +++ linepath b a) =
                   pathstart (linepath a b +++ linepath b a)"
      by simp
    moreover have "path_image (linepath a b +++ linepath b a) = closed_segment a b"
      by (simp add: path_image_join path_image_linepath closed_segment_commute)
    ultimately show ?thesis using fr_eq by blast
  qed
qed


section \<open>Lebesgue measurability of ordinate sets\<close>

text \<open>Helper: if A is Lebesgue measurable in \<real>, then A \<times> UNIV is Lebesgue measurable in \<real>².\<close>

lemma lebesgue_measurable_Times_UNIV:
  fixes A :: "real set"
  assumes "A \<in> sets lebesgue"
  shows "A \<times> (UNIV :: real set) \<in> sets lebesgue"
proof -
  have UNIV_borel: "(UNIV :: real set) \<in> sets borel"
    using sets.top[of "borel :: real measure"] by (simp add: space_borel)
  have mp_leb: "main_part lborel A \<times> (UNIV :: real set) \<in> sets lebesgue"
    using sets_completionI_sets
    by (metis UNIV_borel assms borel_Times main_part_sets sets_lborel)
  obtain N :: "real set" where N: "N \<in> null_sets lborel" "null_part lborel A \<subseteq> N"
    using null_part[OF assms] by auto
  then have "N \<times> (UNIV :: real set) \<in> null_sets lborel"
    by (metis UNIV_borel lborel.times_in_null_sets1 lborel_prod sets_lborel)
  then have "null_part lborel A \<times> (UNIV :: real set) \<in> sets lebesgue"
    using completion.complete
    by (simp add: N(2) Sigma_mono sets_completionI_sub)
  then show ?thesis  using main_part_null_part_Un[OF assms]
    by (metis Sigma_Un_distrib1 mp_leb sets.Un)
qed

lemma prod_swap_lebesgue_measurable:
  "prod.swap \<in> (lebesgue :: ('a::euclidean_space \<times> 'b::euclidean_space) measure)
    \<rightarrow>\<^sub>M (lebesgue :: ('b \<times> 'a) measure)"
proof -
  have swap_lborel: "prod.swap \<in> (lborel :: ('a \<times> 'b) measure) \<rightarrow>\<^sub>M lborel"
    by (simp add: borel_measurable_continuous_onI continuous_on_swap)
  have swap_compl: "prod.swap \<in> (lebesgue :: ('a \<times> 'b) measure) \<rightarrow>\<^sub>M lborel"
    using measurable_completion[OF swap_lborel] by simp
  have "distr (lebesgue :: ('a \<times> 'b) measure) lborel prod.swap = distr lborel lborel prod.swap"
    using distr_completion[OF swap_lborel] by simp
  also have "\<dots> = lborel"
  proof -
    have "distr lborel lborel prod.swap = distr lborel lborel (\<lambda>(x::'a, y::'b). (y, x))"
      by (intro distr_cong) (auto simp: swap_simp)
    also have "\<dots> = lborel"
      using lborel_pair.distr_pair_swap by (simp add: lborel_prod eq_commute)
    finally show ?thesis .
  qed
  finally have null_eq: "null_sets (lborel :: ('b \<times> 'a) measure)
    \<subseteq> null_sets (distr lebesgue lborel prod.swap)"
    by simp
  show ?thesis
    using completion.measurable_completion2[OF swap_compl null_eq] by simp
qed

lemma lebesgue_measurable_UNIV_Times:
  fixes B :: "real set"
  assumes "B \<in> sets lebesgue"
  shows "(UNIV :: real set) \<times> B \<in> sets lebesgue"
proof -
  have "prod.swap -` (B \<times> UNIV) \<inter> space (lebesgue :: (real \<times> real) measure) \<in> sets lebesgue"
    using measurable_sets[OF prod_swap_lebesgue_measurable lebesgue_measurable_Times_UNIV[OF assms]] .
  moreover have "prod.swap -` (B \<times> (UNIV :: real set)) = (UNIV :: real set) \<times> B" by auto
  ultimately show ?thesis by simp
qed

lemma measure_Complex_image:
  fixes S :: "(real \<times> real) set"
  assumes "S \<in> lmeasurable"
  shows "(\<lambda>(x,y). Complex x y) ` S \<in> lmeasurable" (is "?C ` _ \<in> _")
    and "measure lebesgue ((\<lambda>(x,y). Complex x y) ` S) = measure lebesgue S"
proof -
  let ?inv = "\<lambda>z::complex. (Re z, Im z)"
  \<comment> \<open>Key: ?C is linear from real \<times> real to complex\<close>
  have lin: "linear ?C"
    by (simp add: complex_eq_iff linear_iff)
  \<comment> \<open>?C maps cboxes to cboxes with the same measure\<close>
  have box_eq: "measure lebesgue (?C ` cbox a b) = 1 * measure lebesgue (cbox a b)"
    for a b :: "real \<times> real"
  proof -
    obtain a1 a2 where a: "a = (a1, a2)" by (cases a)
    obtain b1 b2 where b: "b = (b1, b2)" by (cases b)
    have "?C ` cbox (a1,a2) (b1,b2) = cbox (Complex a1 a2) (Complex b1 b2)"
      by (force simp: cbox_complex_eq mem_box Basis_prod_def image_iff split_def)
    moreover have "measure lebesgue (cbox (Complex a1 a2) (Complex b1 b2)) =
          measure lebesgue (cbox (a1,a2) (b1,b2))"
      by (simp add: measure_lborel_cbox_eq Basis_complex_def Basis_prod_def
            complex.sel inner_complex_def inner_Pair_0)
    ultimately show ?thesis unfolding a b by simp
  qed

  have inv_lborel: "?inv \<in> lborel \<rightarrow>\<^sub>M lborel"
    by simp
  \<comment> \<open>Lift source to completion\<close>
  have inv_compl: "?inv \<in> lebesgue \<rightarrow>\<^sub>M lborel"
    using measurable_completion[OF inv_lborel] by simp

  have "distr (lebesgue :: complex measure) lborel ?inv
      = distr lborel lborel ?inv"
    using distr_completion[OF inv_lborel] by simp
  also have "\<dots> = lborel"
    proof -
      have "continuous_on UNIV (\<lambda>p :: real \<times> real. Complex (fst p) (snd p))"
        by (intro continuous_on_Complex continuous_on_fst continuous_on_snd continuous_on_id)
    then have C_meas: "?C \<in> lborel \<rightarrow>\<^sub>M borel"
      by (simp add: borel_measurable_continuous_onI case_prod_beta)
    have inv_borel: "?inv \<in> borel \<rightarrow>\<^sub>M lborel"
      using inv_lborel by (simp add: measurable_def sets_lborel)
    have "distr lborel lborel ?inv =  distr lborel lborel (?inv \<circ> ?C)"
      using lborel_distr_complex_pair distr_distr[OF inv_borel C_meas] by simp
    also have "?inv \<circ> ?C = (\<lambda>x. x)"
      by (auto simp: fun_eq_iff complex.sel split: prod.splits)
    finally show ?thesis
      by simp
  qed
  finally have distr_eq: "distr lebesgue lborel ?inv = lborel"
    by simp
  then have null_eq: "null_sets lborel \<subseteq> null_sets (distr lebesgue lborel ?inv)"
    by simp
  \<comment> \<open>Lift target to completion\<close>
  have inv_lebesgue: "?inv \<in> (lebesgue :: complex measure) \<rightarrow>\<^sub>M (lebesgue :: (real \<times> real) measure)"
    using completion.measurable_completion2[OF inv_compl null_eq] by simp
  have image_eq: "?C ` S = ?inv -` S \<inter> space (lebesgue :: complex measure)"
    by (force simp: complex.sel complex_eq_iff image_iff split: prod.splits)
  have sets_S: "S \<in> sets (lebesgue :: (real \<times> real) measure)"
    using assms by (simp add: fmeasurable_def)
  show "?C ` S \<in> lmeasurable"
  proof -
    have "?C ` S \<in> sets lebesgue"
      using image_eq measurable_sets[OF inv_lebesgue sets_S] by simp
    moreover have "emeasure lebesgue (?C ` S) < \<infinity>"
    proof -
      have "emeasure lebesgue (?C ` S) = emeasure (distr lebesgue lebesgue ?inv) S"
        using image_eq emeasure_distr[OF inv_lebesgue sets_S] by simp
      also have "\<dots> = emeasure (lebesgue :: (real \<times> real) measure) S"
        by (metis (lifting) completion.completion_distr_eq distr_eq inv_compl)
      finally show ?thesis
        using assms by (auto simp: fmeasurable_def)
    qed
    ultimately show ?thesis by (simp add: fmeasurable_def)
  qed

  show "measure lebesgue (?C ` S) = measure lebesgue S"
  proof -
    have "emeasure lebesgue (?C ` S)
        = emeasure lebesgue (?inv -` S \<inter> space lebesgue)"
      using image_eq by simp
    also have "\<dots> = emeasure (distr lebesgue lebesgue ?inv) S"
      using emeasure_distr[OF inv_lebesgue sets_S] by simp
    also have "\<dots> = emeasure (lebesgue :: (real \<times> real) measure) S"
      by (metis (lifting) completion.completion_distr_eq distr_eq inv_compl)
    finally show ?thesis by (simp add: measure_def)
  qed
qed

text \<open>Cavalieri principle: measure of the subgraph of a nonneg continuous function\<close>

lemma has_integral_area_under_curve:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b"
    and "continuous_on {a..b} f"
    and fge0: "\<And>x. x \<in> {a..b} \<Longrightarrow> 0 \<le> f x"
  shows "{z::complex. a \<le> Re z \<and> Re z \<le> b \<and> 0 \<le> Im z \<and> Im z \<le> f (Re z)} \<in> lmeasurable"
    and "measure lebesgue {z::complex. a \<le> Re z \<and> Re z \<le> b \<and> 0 \<le> Im z \<and> Im z \<le> f (Re z)}
       = integral {a..b} f"
proof -
  define S where "S \<equiv> {z::complex. a \<le> Re z \<and> Re z \<le> b \<and> 0 \<le> Im z \<and> Im z \<le> f (Re z)}"
  have cont_g: "continuous_on {a..b} f" by fact
  \<comment> \<open>The subgraph is the continuous image of a compact set, hence compact\<close>
  have S_compact: "compact S"
  proof -
    define \<phi> where "\<phi> \<equiv> \<lambda>(x::real, t::real). Complex x (t * f x)"
    have cont_\<phi>: "continuous_on ({a..b} \<times> {0..1}) \<phi>"
      unfolding \<phi>_def split_def
      by (intro continuous_intros continuous_on_compose2[OF cont_g] continuous_on_fst) auto
    have img: "\<phi> ` ({a..b} \<times> {0..1}) = S"
    proof (rule set_eqI)
      fix z
      show "z \<in> \<phi> ` ({a..b} \<times> {0..1}) \<longleftrightarrow> z \<in> S"
      proof
        assume "z \<in> \<phi> ` ({a..b} \<times> {0..1})"
        then show "z \<in> S"
          unfolding S_def using assms(3)
          by (force simp: \<phi>_def image_iff complex.sel intro: mult_left_le_one_le)
      next
        assume "z \<in> S"
        then have hz: "a \<le> Re z" "Re z \<le> b" "0 \<le> Im z" "Im z \<le> f (Re z)"
          unfolding S_def by auto
        show "z \<in> \<phi> ` ({a..b} \<times> {0..1})"
        proof (cases "f (Re z) = 0")
          case True
          with hz show ?thesis 
            unfolding \<phi>_def by (force simp: complex_eq_iff)
        next
          case False
          then have "Im z / f (Re z) \<in> {0..1}" using hz(3,4) by (auto simp: field_simps)
          moreover have "z = \<phi> (Re z, Im z / f (Re z))"
            unfolding \<phi>_def using False by (simp add: complex_eq_iff)
          ultimately show ?thesis using hz(1,2) by auto
        qed
      qed
    qed
    then show "compact S"
      by (metis img compact_continuous_image[OF cont_\<phi>] compact_Times compact_Icc)      
  qed
  with lmeasurable_compact have S_lmeasurable: "S \<in> lmeasurable" by blast
  \<comment> \<open>Now prove the measure equals the integral using change of variables\<close>
  have S_measure: "measure lebesgue S = integral {a..b} f"
  proof -
    define S' :: "(real \<times> real) set"
      where "S' \<equiv> {(x, y). a \<le> x \<and> x \<le> b \<and> 0 \<le> y \<and> y \<le> f x}"
    \<comment> \<open>Step 1: @{term Complex} is measure-preserving, so $\mu(S) = \mu(S')$\<close>
    have S'_compact: "compact S'"
    proof -
      have "continuous_on ({a..b} \<times> {0..1}) (\<lambda>(x,t). (x, t * f x) :: real \<times> real)"
        unfolding split_def
        by (intro continuous_intros continuous_on_compose2[OF cont_g] continuous_on_fst) auto
      moreover have "(\<lambda>(x,t). (x, t * f x)) ` ({a..b} \<times> {0..1}) = S'"
      proof -
        have "\<exists>y\<in>{0..1}. t = y * f x"
          if "a \<le> x" and "x \<le> b" and t: "0 \<le> t" "t \<le> f x" for x t
        proof (cases "f x = 0")
          case False
          with t show ?thesis 
            by (rule_tac x = "t / f x" in bexI) auto
        qed (use t in auto)
        then show ?thesis
          by (auto simp: mult_left_le_one_le fge0 image_iff S'_def split: prod.splits)
      qed
      ultimately show ?thesis
        using compact_continuous_image compact_Times by blast 
    qed
    with lmeasurable_compact have S'_meas: "S' \<in> lmeasurable" by blast
      have S_eq: "S = (\<lambda>(x,y). Complex x y) ` S'"
      by (force simp: S_def S'_def image_iff)
    then have meas_eq: "measure lebesgue S = measure lebesgue S'"
        using measure_Complex_image(2)[OF S'_meas] by simp
    \<comment> \<open>Step 2: compute measure of S' using Fubini\<close>
    have "measure lebesgue S' = integral {a..b} f"
    proof -
      have integ: "integrable lborel (indicat_real S')"
        using S'_compact fmeasurable_compact fmeasurable_def by blast
      \<comment> \<open>The slice x \<mapsto> integral over y of indicator S' equals f(x) on [a,b] and 0 outside\<close>
      have slice_eq: "\<And>x. integral UNIV (\<lambda>y. indicat_real S' (x, y)) =
                          (if x \<in> {a..b} then f x else 0)"
      proof -
        fix x 
        show "integral UNIV (\<lambda>y. indicat_real S' (x, y)) = (if x \<in> {a..b} then f x else 0)"
        proof (cases "x \<in> {a..b}")
          case True
          then have "{y. (x,y) \<in> S'} = {0..f x}"
            unfolding S'_def by auto
          then have "integral UNIV (\<lambda>y. indicat_real S' (x, y)) = integral {0..f x} (\<lambda>_. 1)"
            by (smt (verit, ccfv_SIG) integral_cong integral_restrict_UNIV indicator_eq_0_iff
                    indicator_eq_1_iff mem_Collect_eq)
          then show ?thesis using True assms(3) by simp
        qed (auto simp: S'_def)
      qed
      \<comment> \<open>Apply Fubini\<close>
      have "measure lebesgue S' = integral UNIV (indicat_real S')"
        using lmeasure_integral_UNIV[OF S'_meas] by simp
      also have "\<dots> = integral UNIV (\<lambda>x. integral UNIV (\<lambda>y. indicat_real S' (x, y)))"
      proof (rule gauge_integral_Fubini_universe_x(1)[OF integ])
        show "(\<lambda>x. integral UNIV (\<lambda>y. indicat_real S' (x, y))) \<in> borel_measurable lborel"
        proof -
          have "(\<lambda>x. integral UNIV (\<lambda>y. indicat_real S' (x, y))) = (\<lambda>x. if x \<in> {a..b} then f x else 0)"
            by (use slice_eq in auto)
          also have "\<dots> \<in> borel_measurable lborel"
          proof -
            have "(\<lambda>x::real. if x \<in> {a..b} then f x else 0) \<in> borel_measurable borel"
              by (intro borel_measurable_continuous_on_if continuous_on_const assms(2)) auto
            then show ?thesis by (simp add: sets_lborel)
          qed
          finally show ?thesis .
        qed
      qed
      also have "\<dots> = integral UNIV (\<lambda>x. if x \<in> {a..b} then f x else 0)"
        by (rule integral_cong) (use slice_eq in auto)
      also have "\<dots> = integral {a..b} f"
        by (rule integral_restrict_UNIV)
      finally show ?thesis .
    qed
    then show ?thesis using meas_eq by simp
  qed

  show "{z::complex. a \<le> Re z \<and> Re z \<le> b \<and> 0 \<le> Im z \<and> Im z \<le> f (Re z)} \<in> lmeasurable"
    using S_lmeasurable unfolding S_def .
  show "measure lebesgue {z::complex. a \<le> Re z \<and> Re z \<le> b \<and> 0 \<le> Im z \<and> Im z \<le> f (Re z)}
       = integral {a..b} f"
    using S_measure unfolding S_def .
qed

lemma lebesgue_measurable_ordinate_set_le:
  fixes f :: "real \<Rightarrow> real"
  assumes "f measurable_on UNIV"
  shows "{(x, y). y \<le> f x} \<in> sets (lebesgue :: (real \<times> real) measure)"
proof -
  have f_meas: "f \<in> borel_measurable lebesgue"
    using assms measurable_on_imp_borel_measurable_lebesgue_UNIV by blast
  \<comment> \<open>Step 1: rewrite as countable intersection\<close>
  have eq: "{(x, y). y \<le> f x} =
    (\<Inter>q \<in> \<rat>. {(x, y). f x < q \<longrightarrow> y < q})"
  proof (intro equalityI subsetI)
    fix p :: "real \<times> real"
    assume "p \<in> {(x, y). y \<le> f x}"
    then obtain x y where p: "p = (x, y)" "y \<le> f x" by auto
    show "p \<in> (\<Inter>q\<in>\<rat>. {(x, y). f x < q \<longrightarrow> y < q})"
      using p by (auto intro: order_le_less_trans)
  next
    fix p :: "real \<times> real"
    assume H: "p \<in> (\<Inter>q\<in>\<rat>. {(x, y). f x < q \<longrightarrow> y < q})"
    then obtain x y where p: "p = (x, y)" by (cases p)
    have *: "\<And>q. q \<in> \<rat> \<Longrightarrow> f x < q \<Longrightarrow> y < q"
      using H p by auto
    have "y \<le> f x"
      using le_iff_forall_rat_less_imp[of y "f x"] * by auto
    then show "p \<in> {(x, y). y \<le> f x}" using p by auto
  qed
  \<comment> \<open>Step 2: each set in the intersection is measurable\<close>
  have meas_q: "\<And>q. q \<in> \<rat> \<Longrightarrow> {(x, y). f x < q \<longrightarrow> y < q}
      \<in> sets (lebesgue :: (real \<times> real) measure)"
  proof -
    fix q :: real assume "q \<in> \<rat>"
    have decomp: "{(x :: real, y :: real). f x < q \<longrightarrow> y < q} =
      {(x, y). q \<le> f x} \<union> {(x, y). y < q}"
      by auto
    \<comment> \<open>Part A: {(x,y). y < q} is Borel measurable\<close>
    have "{(x :: real, y :: real). y < q} = (UNIV :: real set) \<times> {..<q}"
      by auto
    moreover have "{..<q} \<in> sets (borel :: real measure)"
      by (rule lessThan_borel)
    moreover have "(UNIV :: real set) \<in> sets (borel :: real measure)"
      using sets.top[of "borel :: real measure"] by (simp add: space_borel)
    ultimately have A: "{(x :: real, y :: real). y < q}
        \<in> sets (lebesgue :: (real \<times> real) measure)"
      using borel_Times sets_completionI_sets
      by (metis sets_lborel)
    \<comment> \<open>Part B: {(x,y). q \<le> f x} is Lebesgue measurable\<close>
    have "{x :: real. f x \<in> {q..}} \<in> sets lebesgue"
      using lebesgue_measurable_vimage_borel[OF f_meas atLeast_borel] .
    then have "{x :: real. q \<le> f x} \<in> sets lebesgue"
      by (simp add: atLeast_def)
    then have B: "{(x :: real, y :: real). q \<le> f x}
        \<in> sets (lebesgue :: (real \<times> real) measure)"
    proof -
      assume "{x :: real. q \<le> f x} \<in> sets lebesgue"
      moreover have "{(x :: real, y :: real). q \<le> f x} =
        {x. q \<le> f x} \<times> (UNIV :: real set)"
        by auto
      ultimately show ?thesis
        using lebesgue_measurable_Times_UNIV by simp
    qed
    show "{(x, y). f x < q \<longrightarrow> y < q} \<in> sets (lebesgue :: (real \<times> real) measure)"
      using decomp A B sets.Un by metis
  qed

  show ?thesis
    unfolding eq
  proof (rule sets.countable_INT'[OF countable_rat])
    show "\<rat> \<noteq> ({}::real set)" using Rats_0 by blast
    show "(\<lambda>q. {(x, y). f x < q \<longrightarrow> y < q}) ` \<rat>
        \<subseteq> sets (lebesgue :: (real \<times> real) measure)"
      using meas_q by auto
  qed
qed

lemma lebesgue_measurable_ordinate_set_lt:
  fixes f :: "real \<Rightarrow> real"
  assumes "f measurable_on UNIV"
  shows "{(x, y). y < f x} \<in> sets (lebesgue :: (real \<times> real) measure)"
proof -
  have f_meas: "f \<in> borel_measurable lebesgue"
    using assms measurable_on_imp_borel_measurable_lebesgue_UNIV by blast
  \<comment> \<open>Express as countable union using density of rationals\<close>
  have "\<And>a b. b < f a \<Longrightarrow> \<exists>x\<in>\<rat>. x \<le> f a \<and> b < x"
    by (meson Rats_dense_in_real less_le)
  then have eq: "{(x, y). y < f x} = (\<Union>q \<in> \<rat>. {x. q \<le> f x} \<times> {y. y < q})"
    by auto
  \<comment> \<open>Each set in the union is measurable\<close>
  have meas_q: "\<And>q. q \<in> \<rat> \<Longrightarrow> {x. q \<le> f x} \<times> {y :: real. y < q}
      \<in> sets (lebesgue :: (real \<times> real) measure)"
  proof -
    fix q :: real assume "q \<in> \<rat>"
    have A: "{y :: real. y < q} \<in> sets lebesgue"
      using sets_completionI_sets[OF lessThan_borel] sets_lborel by fastforce
    have "{x :: real. f x \<in> {q..}} \<in> sets lebesgue"
      using lebesgue_measurable_vimage_borel[OF f_meas atLeast_borel] .
    then have B: "{x :: real. q \<le> f x} \<in> sets lebesgue"
      by (simp add: atLeast_def)
    show "{x. q \<le> f x} \<times> {y :: real. y < q} \<in> sets (lebesgue :: (real \<times> real) measure)"
      using lebesgue_measurable_Times_UNIV[OF B] lebesgue_measurable_UNIV_Times[OF A]
        sets.Int[of "_ \<times> UNIV" _ "UNIV \<times> {y. y < q}"]
      by (simp add: Times_Int_Times)
  qed

  show ?thesis
    unfolding eq
    by (intro sets.countable_UN''[OF countable_rat]) (use meas_q in auto)
qed

lemma lebesgue_measurable_ordinate_set_le_eq:
  fixes f :: "real \<Rightarrow> real"
  shows "f measurable_on UNIV \<longleftrightarrow>
    {(x, y). y \<le> f x} \<in> sets (lebesgue :: (real \<times> real) measure)"
proof
  assume "f measurable_on UNIV"
  then show "{(x, y). y \<le> f x} \<in> sets (lebesgue :: (real \<times> real) measure)"
    by (rule lebesgue_measurable_ordinate_set_le)
next
  \<comment> \<open>Backward direction requires Fubini-type section argument\<close>
  assume "{(x, y). y \<le> f x} \<in> sets (lebesgue :: (real \<times> real) measure)"
  then show "f measurable_on UNIV"
    sorry
qed

lemma lebesgue_measurable_ordinate_set_lt_eq:
  fixes f :: "real \<Rightarrow> real"
  shows "f measurable_on UNIV \<longleftrightarrow>
    {(x, y). y < f x} \<in> sets (lebesgue :: (real \<times> real) measure)"
proof
  assume "f measurable_on UNIV"
  then show "{(x, y). y < f x} \<in> sets (lebesgue :: (real \<times> real) measure)"
    by (rule lebesgue_measurable_ordinate_set_lt)
next
  \<comment> \<open>Backward direction requires Fubini-type section argument\<close>
  assume "{(x, y). y < f x} \<in> sets (lebesgue :: (real \<times> real) measure)"
  then show "f measurable_on UNIV"
    sorry
qed

lemma negligible_measurable_function_graph:
  fixes f :: "real \<Rightarrow> real"
  assumes "f measurable_on UNIV"
  shows "negligible {(x, y). f x = y}"
proof -
  \<comment> \<open>Extract continuous approximants from measurable_on\<close>
  obtain N g where neg_N: "negligible N" "N \<in> sets lebesgue"
    and g_cont: "\<And>n. continuous_on UNIV (g n)"
    and g_conv: "\<And>x. x \<notin> N \<Longrightarrow> (\<lambda>n. g n x) \<longlonglongrightarrow> f x"
    using assms[unfolded measurable_on_def]
    using negligible_imp_sets by auto
  \<comment> \<open>Define the Borel-measurable pointwise limit\<close>
  define h where "h x = lim (\<lambda>n. g n x)" for x
  have g_borel: "\<And>n. g n \<in> borel_measurable (borel :: real measure)"
    using g_cont borel_measurable_continuous_onI by blast
  have h_borel: "h \<in> borel_measurable (borel :: real measure)"
    unfolding h_def by (simp add: borel_measurable_lim_metric g_borel)
  have h_eq: "\<And>x. x \<notin> N \<Longrightarrow> h x = f x"
    unfolding h_def using g_conv limI by blast

  have graph_sub: "{(x, y). f x = y} \<subseteq> {(x, y). h x = y} \<union> N \<times> UNIV"
    by (force simp: h_eq)
  \<comment> \<open>The graph of h is in @{term \<open>sets (lborel \<Otimes>\<^sub>M lborel)\<close>} and null by Fubini\<close>
  have h_meas_lborel: "h \<in> borel_measurable lborel"
    using h_borel by (simp add: sets_lborel)
  have diff_meas: "(\<lambda>p. h (fst p) - snd p) \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  proof -
    have "(\<lambda>p. h (fst p)) \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
      using measurable_comp[OF measurable_fst, of h lborel borel] h_meas_lborel
      by (simp add: comp_def)
    moreover have "(\<lambda>p. snd p :: real) \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
      using measurable_snd measurable_lborel1 by blast
    ultimately show ?thesis by (rule borel_measurable_diff)
  qed
  have graph_h_borel: "{(x, y). h x = y} \<in> sets (lborel \<Otimes>\<^sub>M lborel)"
  proof -
    have "{(x, y). h x = y} =
      (\<lambda>p. h (fst p) - snd p) -` {0} \<inter> space (lborel \<Otimes>\<^sub>M lborel)"
      by (auto simp: space_pair_measure)
    then show ?thesis using borel_measurable_vimage[OF diff_meas, of 0] by simp
  qed
  have "emeasure (lborel \<Otimes>\<^sub>M lborel) {(x, y). h x = y} = 0"
    using lborel.emeasure_pair_measure_alt[OF graph_h_borel] by simp
  then have graph_h_null: "{(x, y). h x = y} \<in> null_sets (lborel :: (real \<times> real) measure)"
    by (metis graph_h_borel lborel_prod null_setsI)
  \<comment> \<open>N \<times> UNIV is contained in a null set in lborel\<close>
  obtain N' where N': "N' \<in> null_sets lborel" "N \<subseteq> N'"
    by (metis null_sets_completion_iff2 neg_N(1) negligible_iff_null_sets)
  have "N' \<times> (UNIV :: real set) \<in> null_sets (lborel \<Otimes>\<^sub>M lborel)"
    using lborel.times_in_null_sets1[OF N'(1) sets.top] by force
  then have N'_cross_null: "N' \<times> (UNIV :: real set) \<in> null_sets (lborel :: (real \<times> real) measure)"
    using lborel_prod by metis
  have N_cross_sub: "N \<times> (UNIV :: real set) \<subseteq> N' \<times> (UNIV :: real set)"
    using N'(2) by auto
  \<comment> \<open>Combine: graph(f) \<subseteq> null set\<close>
  have "{(x, y). h x = y} \<union> N' \<times> UNIV \<in> null_sets (lborel :: (real \<times> real) measure)"
    using graph_h_null N'_cross_null by blast
  moreover have "{(x, y). f x = y} \<subseteq> {(x, y). h x = y} \<union> N' \<times> UNIV"
    using graph_sub N_cross_sub
    by (meson Un_mono dual_order.refl dual_order.trans)
  ultimately have "{(x, y). f x = y} \<in> null_sets (lebesgue :: (real \<times> real) measure)"
    by (meson completion.complete2 null_sets_completionI)
  then show ?thesis
    by (simp add: negligible_iff_null_sets)
qed

section \<open>Start of the actual isoperimetric inequality\<close>

text \<open>
  Formalisation of the isoperimetric inequality, following John Harrison's
  HOL Light proof in @{text "100/isoperimetric.ml"}.

  The proof has five parts:
  \<^enum> Convex curve lemmas (switching between views of a convex simple closed curve)
  \<^enum> The Wirtinger inequality
  \<^enum> A special case of Green's theorem for convex area
  \<^enum> The isoperimetric theorem for convex curves
  \<^enum> Convexification of an arbitrary rectifiable simple closed curve
  \<^enum> The full isoperimetric theorem

  Infrastructure is provided by the prerequisite theories:
  \<^item> @{text Bounded_Variation}: bounded variation and vector variation
  \<^item> @{text Absolute_Continuity}: absolute continuity and FTC
  \<^item> @{text Rectifiable_Path}: rectifiable paths and path length
  \<^item> @{text Arc_Length_Reparametrization}: arc length reparametrization

  AFP dependencies:
  \<^item> @{text Fourier}: trigonometric orthonormal system, Bessel inequality,
    L2 Fourier convergence (useful for Wirtinger inequality)
  \<^item> @{text Lp} (via Fourier): Hölder inequality, Minkowski inequality
  \<^item> @{text Green}: Green's theorem for type I/II regions, line integrals
\<close>

subsection \<open>Convex curve lemmas\<close>

text \<open>Switching between views of a convex simple closed curve.\<close>

lemma convex_hull_eq_closure_inside:
  fixes g :: "real \<Rightarrow> complex"
  assumes g: "simple_path g" "pathfinish g = pathstart g"
    and conv: "convex (inside (path_image g))"
  shows "convex hull (path_image g) = closure (inside (path_image g))"
proof (rule equalityI)
  have compact_pi: "compact (path_image g)"
    using compact_simple_path_image[OF assms(1)] .
  have bounded_inside: "bounded (inside (path_image g))"
    using Jordan_inside_outside g by blast
  have frontier_inside: "frontier (inside (path_image g)) = path_image g"
    using Jordan_inside_outside g by blast
  show "convex hull (path_image g) \<subseteq> closure (inside (path_image g))"
    by (metis Diff_subset conv convex_closure convex_hull_subset frontier_def
        frontier_inside hull_same)
  have "compact (closure (inside (path_image g)))"
    using compact_closure local.bounded_inside by blast
  then show "closure (inside (path_image g)) \<subseteq> convex hull (path_image g)"
    by (metis (no_types, lifting) Krein_Milman_frontier conv closure_closure convex_closure
        convex_interior_closure frontier_def frontier_inside order.refl)
qed


lemma frontier_convex_hull_eq_path_image:
  fixes g :: "real \<Rightarrow> complex"
  assumes g: "simple_path g" "pathfinish g = pathstart g"
    and conv: "convex (inside (path_image g))"
  shows "frontier (convex hull (path_image g)) = path_image g"
proof -
  have eq: "convex hull (path_image g) = closure (inside (path_image g))"
    by (rule convex_hull_eq_closure_inside[OF assms])
  have open_inside: "open (inside (path_image g))"
    and frontier_inside: "frontier (inside (path_image g)) = path_image g"
    using Jordan_inside_outside g by blast+
  have "frontier (convex hull (path_image g)) =
    closure (inside (path_image g)) - interior (closure (inside (path_image g)))"
    by (simp add: eq frontier_def)
  also have "\<dots> = closure (inside (path_image g)) - inside (path_image g)"
    using convex_interior_closure[OF assms(3)] interior_open[OF open_inside] by simp
  also have "\<dots> = frontier (inside (path_image g))"
    using interior_open[OF open_inside] by (simp add: frontier_def)
  also have "\<dots> = path_image g"
    by (rule frontier_inside)
  finally show ?thesis .
qed

lemma frontier_convex_hull_subset_path_image:
  fixes g :: "real \<Rightarrow> complex"
  assumes "simple_path g" "pathfinish g = pathstart g"
    "path_image g \<subseteq> frontier (convex hull (path_image g))"
  shows "frontier (convex hull path_image g) \<subseteq> path_image g"
proof -
  have bounded_hull: "bounded (convex hull (path_image g))"
    by (simp add: assms(1) bounded_convex_hull bounded_simple_path_image)
      \<comment> \<open>The interior of the convex hull is connected, bounded, and disjoint from path_image g\<close>
  have int_sub: "interior (convex hull (path_image g)) \<inter> path_image g = {}"
    using assms(3) frontier_def by auto
  have "connected (interior (convex hull (path_image g)))"
    by (simp add: convex_connected)
  moreover have "bounded (interior (convex hull (path_image g)))"
    using bounded_hull bounded_interior by blast
  moreover have "interior (convex hull (path_image g)) \<subseteq> - path_image g"
    using int_sub by blast
  ultimately have int_inside: "interior (convex hull (path_image g)) \<subseteq> inside (path_image g)"
    using Jordan_inside_outside[of g] assms 
    by (smt (verit, ccfv_threshold) Diff_eq_empty_iff compl_le_compl_iff connected_Int_frontier
        convex_convex_hull double_compl hull_antimono inf.absorb_iff2 inside_outside int_sub interior_Int
        interior_eq outside_subset_convex subset_hull sup.coboundedI2)
      \<comment> \<open>Also inside \<subseteq> convex hull (since outside contains complement of hull)\<close>
  have "- (convex hull (path_image g)) \<subseteq> outside (path_image g)"
    by (simp add: hull_subset outside_subset_convex)
  hence inside_sub: "inside (path_image g) \<subseteq> convex hull (path_image g)"
    by (metis Un_subset_iff compl_le_swap2 union_with_inside)
      \<comment> \<open>Since inside is open and \<subseteq> convex hull, inside \<subseteq> interior (convex hull)\<close>
  have "inside (path_image g) \<subseteq> interior (convex hull (path_image g))"
    by (simp add: Jordan_inside_outside assms inside_sub interior_maximal)
  with assms show ?thesis
    using frontier_convex_hull_eq_path_image int_inside by auto
qed

section \<open>Part 1: The Wirtinger inequality\<close>

text \<open>The Hölder bound for @{text "p = q = 2"} follows from @{thm Holder_inequality} in the
  AFP @{text Lp} entry.\<close>

lemma real_hoelder_bound_2:
  fixes f :: "real \<Rightarrow> real" and S :: "real set"
  assumes "S \<in> sets lebesgue" "S \<in> lmeasurable"
    "f \<in> borel_measurable lebesgue"
    "integrable lebesgue (\<lambda>x. indicator S x * (f x)\<^sup>2)"
  shows "(LINT x|lebesgue. indicator S x * f x)\<^sup>2 \<le>
    measure lebesgue S * (LINT x|lebesgue. indicator S x * (f x)\<^sup>2)"
proof -
  have ind_if: "\<And>g x. indicator S x * g x = (if x \<in> S then g x else (0::real))"
    by (simp add: indicator_def)
  have to_lebesgue_on: "\<And>g::real\<Rightarrow>real. (LINT x|lebesgue. indicator S x * g x) = integral\<^sup>L (lebesgue_on S) g"
    using assms(1) by (simp add: ind_if Lebesgue_Measure.integral_restrict_UNIV)

  have f_meas_on: "f \<in> borel_measurable (lebesgue_on S)"
    using assms(3) measurable_restrict_space1 by blast
  have f_sq_integ: "integrable (lebesgue_on S) (\<lambda>x. (f x)\<^sup>2)"
    using Lebesgue_Measure.integrable_restrict_UNIV[OF assms(1), of "\<lambda>x. (f x)\<^sup>2"]
    by (simp add: assms(1,4) integrable_restrict_space)
  have f_sq_int: "f square_integrable S"
    unfolding square_integrable_def using assms(1) f_meas_on f_sq_integ by blast

  have one_sq_int: "(\<lambda>x. 1::real) square_integrable S"
    unfolding square_integrable_def 
    using finite_measure_lebesgue_on assms finite_measure.integrable_const by blast

  have schwartz: "\<bar>l2product S f (\<lambda>x. 1)\<bar> \<le> l2norm S f * l2norm S (\<lambda>x. 1)"
    by (rule Schwartz_inequality_abs[OF f_sq_int one_sq_int])

  have "(l2norm S (\<lambda>x. 1))\<^sup>2 = l2product S (\<lambda>x. 1) (\<lambda>x. 1)"
    by (rule l2norm_pow_2[OF one_sq_int])
  also have "\<dots> = measure lebesgue S"
    using finite_measure_lebesgue_on[OF assms(2)]
    by (simp add: l2product_def assms(1) measure_restrict_space)
  finally have "(l2norm S (\<lambda>x. 1))\<^sup>2 = measure lebesgue S" .
  moreover have "(l2product S f (\<lambda>x. 1))\<^sup>2 \<le> (l2norm S f)\<^sup>2 * (l2norm S (\<lambda>x. 1))\<^sup>2"
    by (metis power_mult_distrib real_sqrt_abs schwartz sqrt_le_D)
  moreover
  have "LINT x|lebesgue. indicator S x * f x = l2product S f (\<lambda>x. 1)" 
       "LINT x|lebesgue. indicator S x * (f x)\<^sup>2 = l2product S f f"
    by (simp_all add: to_lebesgue_on l2product_def power2_eq_square)
  ultimately show ?thesis
    by (metis f_sq_int l2norm_pow_2 mult.commute)
qed

locale W =
  fixes f f' :: "real \<Rightarrow> real" and a::real
  assumes f'hsd: "\<And>x. x \<in> {0..2*pi} \<Longrightarrow> (f' has_integral (f x - f 0)) {0..x}"
    and feq: "f (2*pi) = f 0"
    and f0: "(f has_integral 0) {0..2*pi}"
    and f'2: "(\<lambda>x. (f' x)\<^sup>2) integrable_on {0..2*pi}"
    and a: "0 \<le> a" "a < pi" "f (a + pi) = f a"

begin

definition g where "g \<equiv> \<lambda>x. (f x - f a)\<^sup>2 / tan (x - a)"
definition g' where "g' \<equiv> \<lambda>x. (f' x)\<^sup>2 - (f x - f a)\<^sup>2 - (f' x - (f x - f a) / tan (x - a))\<^sup>2"

lemma f': \<open>f' integrable_on {0..2*pi}\<close>
  using f'hsd [of \<open>2*pi\<close>] by fastforce

lemma f'abs: \<open>f' absolutely_integrable_on {0..2*pi}\<close>
proof (rule absolutely_integrable_integrable_bound)
  show \<open>norm (f' x) \<le> 1 + (f' x)\<^sup>2\<close> for x
  proof -
    have \<open>0 \<le> (1 - f' x)\<^sup>2\<close> and \<open>0 \<le> (1 + f' x)\<^sup>2\<close>
      by (auto simp: power2_eq_square)
    then show \<open>norm (f' x) \<le> 1 + (f' x)\<^sup>2\<close>
      by (auto simp: power2_eq_square abs_le_iff algebra_simps)
  qed
  show \<open>f' integrable_on {0..2*pi}\<close> by (rule f')
  show \<open>(\<lambda>x. 1 + (f' x)\<^sup>2) integrable_on {0..2*pi}\<close>
    using integrable_add [OF integrable_const_ivl f'2] by simp
qed

lemma contf: \<open>continuous_on {0..2*pi} f\<close>
proof (rule continuous_on_eq)
  show \<open>continuous_on {0..2*pi} (\<lambda>x. integral {0..x} f' + f 0)\<close>
    by (intro continuous_on_add indefinite_integral_continuous_1 [OF f'] continuous_on_const)
  show \<open>\<And>x. x \<in> {0..2*pi} \<Longrightarrow> integral {0..x} f' + f 0 = f x\<close>
    using f'hsd by (auto simp: has_integral_integrable_integral)
qed

text \<open>The integral over completely trouble-free intervals.\<close>
lemma trouble_free: "(g' has_integral g d - g c) {c..d}"
  if cd: "c \<le> d"
    and sub_cd: "{c..d} \<subseteq> {0..2*pi}"
    and sin_nz: "\<And>x. x \<in> {c..d} \<Longrightarrow> sin (x - a) \<noteq> 0"
  for c d
proof -
  have f'_int: "((\<lambda>t. 2 * (f t - f a) * f' t) has_integral
                   ((f x - f a)\<^sup>2 - (f c - f a)\<^sup>2)) {c..x}"
    if xcd: "x \<in> {c..d}" for x
  proof -
    have cx: "c \<le> x" and xd: "x \<le> d" using xcd cd by auto
    have sub_cx: "{c..x} \<subseteq> {0..2*pi}" using sub_cd xd by auto
    have ac_f: "absolutely_continuous_on {0..2*pi} f"
      using absolute_integral_absolutely_continuous_derivative_eq f'abs f'hsd by blast
    have ac_sq: "absolutely_continuous_on {c..x} (\<lambda>t. (f t - f a)\<^sup>2)"
      unfolding power2_eq_square using absolutely_continuous_on_subset ac_f sub_cx 
      by(intro continuous_intros) fastforce+
    obtain k where negk: "negligible k"
      and derivf: "\<And>t. t \<in> {0..2*pi} - k \<Longrightarrow>
          ((\<lambda>u. integral {0..u} f') has_vector_derivative f' t) (at t within {0..2*pi})"
      using f' has_vector_derivative_indefinite_integral by blast
        \<comment> \<open>Hence (f t - f a)^2 has the right derivative a.e.\<close>
    have deriv_sq: "((\<lambda>t. (f t - f a)\<^sup>2) has_vector_derivative 2 * (f t - f a) * f' t) (at t within {c..x})"
      if "t \<in> {c..x} - k" for t
    proof -
      have hvd_int: "((\<lambda>u. integral {0..u} f') has_vector_derivative f' t) (at t within {0..2*pi})"
        using derivf that sub_cx by auto
      have "((\<lambda>u. f u - f 0) has_vector_derivative f' t) (at t within {0..2*pi})"
      proof (rule has_vector_derivative_transform_within[OF hvd_int])
        fix u assume "u \<in> {0..2*pi}" "dist u t < 1"
        then show "integral {0..u} f' = f u - f 0"
          using f'hsd by blast
      qed (use that sub_cx in auto)
      then have fderiv: "(f has_vector_derivative f' t) (at t within {c..x})"
        using has_vector_derivative_diff_const has_vector_derivative_within_subset sub_cx by blast
      then show ?thesis
        unfolding power2_eq_square has_vector_derivative_def
        by - (rule derivative_eq_intros | simp add: algebra_simps)+
    qed
    show ?thesis
      using fundamental_theorem_of_calculus_absolutely_continuous [OF negk cx ac_sq deriv_sq] by simp
  qed
  text \<open>Apply integration by parts with
      \<^item> \<open>\<lambda>x. (f x - f a)²\<close> and its derivative \<open>\<lambda>x. 2 * (f x - f a) * f' x\<close>
      \<^item> \<open>\<lambda>x. inverse (tan (x - a))\<close> and its derivative \<open>\<lambda>x. - inverse (sin (x - a))²\<close>\<close>
  have ibp_int: "((\<lambda>x. (f x - f a)\<^sup>2 * (- inverse ((sin (x - a))\<^sup>2)) +
      2 * (f x - f a) * f' x * inverse (tan (x - a)))
      has_integral ((f y - f a)\<^sup>2 * inverse (tan (y - a)) -
                    (f c - f a)\<^sup>2 * inverse (tan (c - a)))) {c..y}"
    if "y \<in> {c..d}" for y
  proof (rule absolute_real_integration_by_parts_sum(2))
    show "c \<le> d" using cd .
    show "(\<lambda>x. 2 * (f x - f a) * f' x) absolutely_integrable_on {c..d}"
    proof -
      have f'_abs_cd: "f' absolutely_integrable_on {c..d}"
        using absolutely_integrable_on_subinterval[OF f'abs sub_cd] .
      have cont_ffa: "continuous_on {c..d} (\<lambda>x. 2 * (f x - f a))"
        using sub_cd by (intro continuous_intros continuous_on_subset [OF contf]) auto
      have meas: "(\<lambda>x. 2 * (f x - f a)) \<in> borel_measurable (lebesgue_on {c..d})"
        using cont_ffa by (intro continuous_imp_measurable_on_sets_lebesgue) auto
      have bdd: "bounded ((\<lambda>x. 2 * (f x - f a)) ` {c..d})"
        using cont_ffa compact_Icc compact_continuous_image compact_imp_bounded by blast
      show ?thesis
        using absolutely_integrable_bounded_measurable_product_real
          [OF meas _ bdd f'_abs_cd] by auto
    qed
    show "(\<lambda>x. - inverse ((sin (x - a))\<^sup>2)) absolutely_integrable_on {c..d}"
      by (intro absolutely_integrable_continuous_real continuous_intros) (use sin_nz in auto)
    show "((\<lambda>t. 2 * (f t - f a) * f' t) has_integral
            ((f x - f a)\<^sup>2 - (f c - f a)\<^sup>2)) {c..x}"
      if "x \<in> {c..d}" for x using f'_int[OF that] .
    show "((\<lambda>t. - inverse ((sin (t-a))\<^sup>2)) has_integral
            (inverse (tan (x - a)) - inverse (tan (c - a)))) {c..x}"
      if "x \<in> {c..d}" for x 
    proof -
      have cx: "c \<le> x" and sub_cx: "{c..x} \<subseteq> {c..d}"
        using that by auto
      have inv_tan_eq: "inverse (tan (t-a)) = cos (t-a) / sin (t-a)"
        if "t \<in> {c..x}" for t
        by (simp add: Multiseries_Expansion.tan_conv_sin_cos)
          \<comment> \<open>cos(t-a)/sin(t-a) has the right derivative\<close>
      have deriv: "((\<lambda>t. cos (t-a) / sin (t-a)) has_vector_derivative
                    - inverse ((sin (t-a))\<^sup>2)) (at t within {c..x})"
        if "t \<in> {c..x}" for t
      proof -
        have sin_nz_t: "sin (t-a) \<noteq> 0" using sin_nz that sub_cx by auto
        have "((\<lambda>t. cos (t-a) / sin (t-a)) has_real_derivative
              (- sin (t-a) * sin (t-a) - cos (t-a) * cos (t-a)) / (sin (t-a) * sin (t-a)))
              (at t within {c..x})"
          by (intro derivative_eq_intros | simp add: sin_nz_t)+
        also have "(- sin (t-a) * sin (t-a) - cos (t-a) * cos (t-a)) / (sin (t-a) * sin (t-a))
                 = - inverse ((sin (t-a))\<^sup>2)"
          using sin_cos_squared_add3 [of "t-a"]
          by (simp (no_asm_simp) add: divide_simps power2_eq_square)
        finally show ?thesis
          by (simp add: has_real_derivative_iff_has_vector_derivative)
      qed
        \<comment> \<open>Apply FTC\<close>
      show ?thesis
        using fundamental_theorem_of_calculus[OF cx deriv] inv_tan_eq inv_tan_eq cx
        by simp
    qed
    show "y \<in> {c..d}" using that .
  qed
    \<comment> \<open>The IBP integrand equals g' pointwise on {c..d}\<close>
  have integrand_eq: "(f x - f a)\<^sup>2 * (- inverse ((sin (x - a))\<^sup>2)) +
      2 * (f x - f a) * f' x * inverse (tan (x - a)) = g' x"
    if "x \<in> {c..d}" for x
  proof -
    have snz: "sin (x - a) \<noteq> 0" using sin_nz[OF that] .
    have snz2: "(sin (x - a))\<^sup>2 \<noteq> 0" using snz by auto
    let ?F = "f x - f a"
    let ?s = "sin (x - a)"
    let ?c = "cos (x - a)"
    have inv_tan: "inverse (tan (x - a)) = ?c / ?s"
      unfolding tan_def using snz by (simp add: field_simps)
    have sc1: "?s\<^sup>2 + ?c\<^sup>2 = 1"
      using sin_cos_squared_add[of "x - a"] by simp
    have "((f x - f a)\<^sup>2 * (- inverse (?s\<^sup>2)) + 2 * (f x - f a) * f' x * inverse (tan (x - a))) * ?s\<^sup>2
          = - ?F\<^sup>2 + 2 * ?F * f' x * ?c * ?s"
      using snz snz2 by (simp add: tan_def field_simps power2_eq_square)
    moreover have "g' x * ?s\<^sup>2 = ((f' x)\<^sup>2 - ?F\<^sup>2) * ?s\<^sup>2 - (f' x * ?s - ?F * ?c)\<^sup>2"
      using snz by (simp add: g'_def tan_def field_simps)
    moreover have "\<dots>  = - ?F\<^sup>2 + 2 * ?F * f' x * ?c * ?s"
      using sc1 by algebra 
    ultimately show ?thesis using snz2
      by (metis mult_right_cancel)
  qed
    \<comment> \<open>Combine using has_integral_eq\<close>
  show ?thesis
    using has_integral_eq ibp_int integrand_eq unfolding g_def divide_inverse
    by (metis (no_types, lifting) atLeastAtMost_iff order.refl that(1))
qed

text \<open>Continuity of g.\<close>
lemma g_cont: "continuous_on {0..2*pi} g"
  unfolding continuous_on_eq_continuous_within
proof
  fix c assume c_in: "c \<in> {0..2*pi}"
  show "continuous (at c within {0..2*pi}) g"
  proof (cases "sin (c - a) = 0")
    case False
      \<comment> \<open>When sin(c - a) \<noteq> 0, g is a quotient of continuous functions.\<close>
    have g_eq: "g x = (f x - f a)\<^sup>2 * cos (x - a) / sin (x - a)" for x
      unfolding g_def tan_def by (simp add: field_simps)
    have "continuous (at c within {0..2*pi}) f"
      using contf c_in continuous_on_eq_continuous_within by blast
    then show ?thesis unfolding g_eq
      using False by (auto simp: continuous_intros)
  next
    case True
      \<comment> \<open>When sin(c - a) = 0, g(c) = 0 and we need to show g(x) \<rightarrow> 0.\<close>
    have fca: "f c = f a"
    proof -
      from True obtain n :: int where npi: "c - a = of_int n * pi"
        using sin_zero_iff_int2 by auto
      have "of_int n \<ge> -a / pi" "of_int n \<le> (2 * pi - a) / pi"
        using a npi c_in pi_gt_zero by (simp_all add: field_simps)
      moreover have "-a / pi > -1" using a pi_gt_zero by (simp add: field_simps)
      moreover have "(2 * pi - a) / pi < 3"
        using a pi_gt_zero by (auto simp: divide_simps)
      ultimately have "of_int n > (-1 :: real)" "of_int n < (3 :: real)" by linarith+
      then have "n = 0 \<or> n = 1 \<or> n = 2"
        by auto
      thus ?thesis
      proof (elim disjE)
        assume "n = 2"
        then have "c = a + 2 * pi" using npi by (simp add: algebra_simps)
        with c_in a pi_gt_zero have "a = 0" by auto
        thus "f c = f a" using \<open>c = a + 2 * pi\<close> feq by simp
      qed (use npi a in \<open>auto simp: algebra_simps\<close>)
    qed
    have gc0: "g c = 0"
      unfolding g_def using fca by simp
    show ?thesis unfolding continuous_within gc0
    proof -
      \<comment> \<open>Derive tan(x - a) = tan(x - c) from sin(c - a) = 0.\<close>
      from True obtain n :: int where npi: "c - a = of_int n * pi"
        using sin_zero_iff_int2 by auto
      have tan_eq: "tan (x - a) = tan (x - c)" for x
        by (metis npi diff_add_cancel diff_diff_eq2 tan_periodic_int)
      have g_eq2: "g x = (f x - f c)\<^sup>2 * cos (x - c) / sin (x - c)" for x
        unfolding g_def by (metis fca divide_divide_eq_right local.tan_eq tan_def)
          \<comment> \<open>Show (g \<longlongrightarrow> 0) using the cos/sin form.\<close>
      show "(g \<longlongrightarrow> 0) (at c within {0..2*pi})"
      proof -
        \<comment> \<open>Cauchy-Schwarz bound: (f x - f c)² \<le> |x - c| * \<integral>_c^x (f')².\<close>
        have cs_bound: "(f x - f c)\<^sup>2 \<le> \<bar>x - c\<bar> * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
          if xin: "x \<in> {0..2*pi}" for x
        proof -
          have f'_int_sub: "f' integrable_on {a..b}" if "{a..b} \<subseteq> {0..2*pi}" for a b
            using integrable_subinterval_real[OF set_lebesgue_integral_eq_integral(1)[OF f'abs] that] .
          have f'2_int_sub: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {a..b}" if "{a..b} \<subseteq> {0..2*pi}" for a b
            using integrable_subinterval_real[OF f'2 that] .
              \<comment> \<open>Helper: FTC gives f(b) - f(a) = \<integral>_a^b f' for a,b \<in> {0..2\<pi>}\<close>
          have ftc_sub: "f b - f a = integral {a..b} f'"
            if "a \<in> {0..2*pi}" "b \<in> {0..2*pi}" "a \<le> b" for a b
          proof -
            have "integral {0..a} f' + integral {a..b} f' = integral {0..b} f'"
              by (meson Henstock_Kurzweil_Integration.integral_combine atLeastAtMost_iff f'hsd
                  has_integral_integrable that)
            moreover have "integral {0..a} f' = f a - f 0" and "integral {0..b} f' = f b - f 0"
              using f'hsd that by (auto simp: has_integral_integrable_integral)
            ultimately show ?thesis by linarith
          qed
            \<comment> \<open>Helper: Cauchy-Schwarz (\<integral>_I f')² \<le> (b-a) * \<integral>_I (f')² for I = {a..b} \<subseteq> {0..2\<pi>}\<close>
          have cs_sub: "(integral {a..b} f')\<^sup>2 \<le> (b-a) * integral {a..b} (\<lambda>t. (f' t)\<^sup>2)"
            if sub: "{a..b} \<subseteq> {0..2*pi}" and ab: "a < b" for a b
          proof -
            define \<mu> where "\<mu> \<equiv> integral {a..b} f' / (b-a)"
            have f'I: "f' integrable_on {a..b}" by (rule f'_int_sub[OF sub])
            have f'2I: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {a..b}" by (rule f'2_int_sub[OF sub])
            have int1: "(\<lambda>t. - (2 * \<mu>) * f' t) integrable_on {a..b}"
              using integrable_cmul[OF f'I, of "- (2 * \<mu>)"] by (simp add: scaleR_conv_of_real)
            have sub_int: "(\<lambda>t. (f' t - \<mu>)\<^sup>2) integrable_on {a..b}"
              using integrable_add[OF f'2I integrable_add[OF int1 integrable_const_ivl]]
              by (simp add: power2_eq_square algebra_simps)
            have "0 \<le> integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2)"
              by (rule integral_nonneg[OF sub_int]) (simp add: zero_le_power2)
            also have "integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2) =
                integral {a..b} (\<lambda>t. (f' t)\<^sup>2) + (- (2 * \<mu>) * integral {a..b} f' + \<mu>\<^sup>2 * (b-a))"
            proof -
              have "integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2) =
                  integral {a..b} (\<lambda>t. (f' t)\<^sup>2 + (- (2 * \<mu>) * f' t + \<mu>\<^sup>2))"
                by (rule integral_cong) (simp add: power2_eq_square algebra_simps)
              also have "\<dots> = integral {a..b} (\<lambda>t. (f' t)\<^sup>2) +
                  integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t + \<mu>\<^sup>2)"
                by (rule integral_add[OF f'2I integrable_add[OF int1 integrable_const_ivl]])
              also have "integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t + \<mu>\<^sup>2) =
                  integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t) + integral {a..b} (\<lambda>t. \<mu>\<^sup>2)"
                by (rule integral_add[OF int1 integrable_const_ivl])
              finally show ?thesis using ab by simp
            qed
            also have "- (2 * \<mu>) * integral {a..b} f' + \<mu>\<^sup>2 * (b-a) = - (integral {a..b} f')\<^sup>2 / (b-a)"
              using ab unfolding \<mu>_def by (simp add: power2_eq_square divide_simps)
            finally show ?thesis using ab by (simp add: pos_divide_le_eq mult.commute)
          qed
          show ?thesis
          proof (cases "c \<le> x")
            case True
            show ?thesis using cs_sub \<open>c \<le> x\<close> c_in xin ftc_sub by fastforce
          next
            case False
            hence \<section>: "x < c" "{x..c} \<subseteq> {0..2*pi}" using c_in xin by auto
            then show ?thesis
              by (simp add: cs_sub ftc_sub power2_commute)
          qed
        qed
          \<comment> \<open>The integral of f'² over a shrinking interval tends to 0.\<close>
        have f'2_int_tends_0:
          "((\<lambda>x. integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)) \<longlongrightarrow> 0) (at c within {0..2*pi})"
        proof -
          define F where "F \<equiv> \<lambda>x. integral {0..x} (\<lambda>t. (f' t)\<^sup>2)"
          have F_cont: "continuous_on {0..2*pi} F"
            unfolding F_def by (rule indefinite_integral_continuous_1[OF f'2])
          have F_eq: "integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2) = \<bar>F x - F c\<bar>"
            if "x \<in> {0..2*pi}" for x
          proof (cases "c \<le> x")
            case True
            have sub: "{c..x} \<subseteq> {0..2*pi}" using c_in that True by auto
            have "integral {0..c} (\<lambda>t. (f' t)\<^sup>2) + integral {c..x} (\<lambda>t. (f' t)\<^sup>2) =
                integral {0..x} (\<lambda>t. (f' t)\<^sup>2)"
              by (metis Henstock_Kurzweil_Integration.integral_combine True atLeastatMost_subset_iff f'2
                  integrable_on_subinterval order_refl sub)
            hence "integral {c..x} (\<lambda>t. (f' t)\<^sup>2) = F x - F c"
              unfolding F_def by linarith
            moreover have "0 \<le> integral {c..x} (\<lambda>t. (f' t)\<^sup>2)"
              by (metis integral_nonneg not_integrable_integral order.refl zero_le_power2)
            ultimately show ?thesis using True by (simp add: min_def max_def)
          next
            case False
            hence xc: "x \<le> c" by simp
            have sub: "{x..c} \<subseteq> {0..2*pi}" using c_in that xc by auto
            have "integral {0..x} (\<lambda>t. (f' t)\<^sup>2) + integral {x..c} (\<lambda>t. (f' t)\<^sup>2) 
                  = integral {0..c} (\<lambda>t. (f' t)\<^sup>2)"
              by (metis Henstock_Kurzweil_Integration.integral_combine atLeastatMost_subset_iff f'2
                  integrable_subinterval_real order.refl sub xc)
            moreover have "0 \<le> integral {x..c} (\<lambda>t. (f' t)\<^sup>2)"
              by (metis integral_nonneg not_integrable_integral order.refl zero_le_power2)
            ultimately show ?thesis using xc by (simp add: F_def min_def max_def)
          qed
          have "((\<lambda>x. \<bar>F x - F c\<bar>) \<longlongrightarrow> 0) (at c within {0..2*pi})"
            by (metis F_cont LIM_zero_iff c_in continuous_on_def tendsto_rabs_zero)
          thus ?thesis
            by (smt (verit, best) F_eq Lim_cong_within)
        qed
        have "\<forall>\<^sub>F x in at c. \<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> < 2"
          by real_asymp
        then have sinc_ratio_bounded:
          "\<forall>\<^sub>F x in at c within {0..2*pi}. \<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> \<le> 2"
          by (metis (no_types, lifting) UNIV_I eventually_at_topological less_imp_le)
            \<comment> \<open>Now combine everything.\<close>
        show ?thesis
        proof (rule Lim_null_comparison[where g = "\<lambda>x. 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"])
          \<comment> \<open>g(x) is eventually bounded by 2 * \<integral>(f')².\<close>
          show "\<forall>\<^sub>F x in at c within {0..2*pi}. norm (g x) \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
          proof -
            have mem: "\<forall>\<^sub>F x in at c within {0..2*pi}. x \<in> {0..2*pi}"
              unfolding at_within_def eventually_inf_principal by simp
            show ?thesis
            proof (rule eventually_mono[OF eventually_conj[OF sinc_ratio_bounded mem]])
              fix x assume H: "\<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> \<le> 2 \<and> x \<in> {0..2*pi}"
              have "\<bar>g x\<bar> = (f x - f c)\<^sup>2 * \<bar>cos (x - c)\<bar> / \<bar>sin (x - c)\<bar>"
                using g_eq2 by (simp add: abs_mult)
              also have "\<dots> \<le> (f x - f c)\<^sup>2 * 1 / \<bar>sin (x - c)\<bar>"
                by (meson abs_cos_le_one abs_ge_zero divide_right_mono
                    ordered_comm_semiring_class.comm_mult_left_mono zero_le_power2)
              also have "\<dots> = (f x - f c)\<^sup>2 / \<bar>sin (x - c)\<bar>" by simp
              also have "\<dots> \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
              proof -
                have sub: "{min c x..max c x} \<subseteq> {0..2*pi}" using c_in H by auto
                have f'2I: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {min c x..max c x}"
                  by (rule integrable_subinterval_real[OF f'2 sub])
                show ?thesis
                proof (cases "sin (x - c) = 0")
                  case False
                  define I where "I = integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
                  have Ige: "I \<ge> 0"
                    unfolding I_def by (rule integral_nonneg[OF f'2I]) auto
                  have "(f x - f c)\<^sup>2 / \<bar>sin (x - c)\<bar> \<le> \<bar>x - c\<bar> * I / \<bar>sin (x - c)\<bar>"
                    using H by (simp add: I_def cs_bound divide_right_mono)
                  also have "\<dots> = (\<bar>x - c\<bar> / \<bar>sin (x - c)\<bar>) * I"
                    by (simp add: field_simps)
                  also have "\<dots> \<le> 2 * I"
                    by (meson H Ige mult_mono order.refl zero_le_numeral)
                  finally show ?thesis unfolding I_def .
                qed (use integral_nonneg[OF f'2I] in auto)
              qed
              finally show "norm (g x) \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)" by simp
            qed
          qed
          show "((\<lambda>x. 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)) \<longlongrightarrow> 0) (at c within {0..2*pi})"
            using tendsto_mult_right_zero[OF f'2_int_tends_0] by simp
        qed
      qed
    qed
  qed
qed

text \<open>The integral over mainly trouble-free intervals:
    we only need \<open>sin(x - a) \<noteq> 0\<close> on the open interior, allowing zeros at the endpoints.\<close>
lemma mainly_trouble_free: "(g' has_integral g d - g c) {c..d}"
  if "c \<le> d" and "{c..d} \<subseteq> {0..2*pi}" and "\<And>x. x \<in> {c<..<d} \<Longrightarrow> sin (x - a) \<noteq> 0"
  for c d
proof -
  have "g' absolutely_integrable_on {c..d}"
  proof -
    have f'2_abs: "(\<lambda>x. (f' x)\<^sup>2) absolutely_integrable_on {0..2*pi}"
      by (rule abs_absolutely_integrableI_1[OF f'2]) (simp add: integrable_eq[OF f'2])
    have ffa_abs: "(\<lambda>x. (f x - f a)\<^sup>2) absolutely_integrable_on {0..2*pi}"
      by (rule absolutely_integrable_continuous_real)
        (intro continuous_intros contf)
    note cd_le = \<open>c \<le> d\<close> and cd_sub = \<open>{c..d} \<subseteq> {0..2*pi}\<close>
      and sin_nz = \<open>\<And>x. x \<in> {c<..<d} \<Longrightarrow> sin (x - a) \<noteq> 0\<close>
    have g'_int_sub: "g' integrable_on {u..v}" if uv_sub: "{u..v} \<subseteq> {c<..<d}" for u v
    proof (cases "u \<le> v")
      case True
      then have uv_mem: "u \<in> {c<..<d}" "v \<in> {c<..<d}" and  uv_2pi: "{u..v} \<subseteq> {0..2*pi}"
        using uv_sub cd_sub by auto
      have sin_nz': "sin (x - a) \<noteq> 0" if "x \<in> {u..v}" for x
        using sin_nz that uv_sub by blast
      show ?thesis
        using has_integral_integrable[OF trouble_free[OF True uv_2pi sin_nz']] by auto
    qed (simp add: not_le integrable_on_empty)
    have g'_int: "g' integrable_on {c'..d'}" if "{c'..d'} \<subseteq> {c<..<d}" for c' d'
      using \<open>{c'..d'} \<subseteq> {c<..<d}\<close> g'_int_sub by blast
    have abs_g_cont: \<open>continuous_on {0..2 * pi} (\<lambda>x. \<bar>g x\<bar>)\<close>
      by (intro continuous_intros g_cont)
    obtain h where h_abs: "h absolutely_integrable_on {c..d}" 
      and h_bounded: "(\<forall>x\<in>{c..d}. g' x \<le> h x) \<or> (\<forall>x\<in>{c..d}. h x \<le> g' x)"
      using absolutely_integrable_on_subinterval[OF f'2_abs cd_sub]
      by (simp add: g'_def) 
    show ?thesis
    proof (intro g'_int absolutely_integrable_improper [of c d , unfolded box_real])
      obtain w where "0 \<le> w" "w \<le> 2*pi" and w: "\<forall>y. 0\<le>y \<longrightarrow> y \<le> 2*pi \<longrightarrow> \<bar>g y\<bar> \<le> \<bar>g w\<bar>"
        using continuous_attains_sup [of \<open>{0..2*pi}\<close> \<open>\<lambda>x. \<bar>g x\<bar>\<close>]
        by (metis Arg2pi abs_g_cont atLeastAtMost_iff compact_Icc empty_iff less_eq_real_def)
      show "bounded {integral {c'..d'} g' |c' d'. {c'..d'} \<subseteq> {c<..<d}}"
      proof (rule boundedI)
        fix x assume "x \<in> {integral {c'..d'} g' |c' d'. {c'..d'} \<subseteq> {c<..<d}}"
        then obtain c' d' where cd': "{c'..d'} \<subseteq> {c<..<d}" and xeq: "x = integral {c'..d'} g'"
          by auto
        show "norm x \<le> 2 * \<bar>g w\<bar>"
        proof (cases "c' \<le> d'")
          case True
          have sub_2pi: "{c'..d'} \<subseteq> {0..2*pi}"
            using cd' cd_sub greaterThanLessThan_subseteq_atLeastAtMost_iff by blast
          have "sin (t-a) \<noteq> 0" if "t \<in> {c'..d'}" for t
            using that cd' sin_nz by (meson greaterThanLessThan_subseteq_atLeastAtMost_iff subsetD)
          then have "integral {c'..d'} g' = g d' - g c'"
            using True sub_2pi trouble_free by blast
          then have "\<bar>x\<bar> \<le> \<bar>g d'\<bar> + \<bar>g c'\<bar>"
            using xeq by linarith
          also have "\<dots> \<le> \<bar>g w\<bar> + \<bar>g w\<bar>"
            by (metis True w add_mono atLeastatMost_subset_iff order_trans sub_2pi)
          also have "\<dots> = 2 * \<bar>g w\<bar>" by algebra
          finally show ?thesis by (simp add: xeq)
        qed (simp add: xeq)
      qed
    qed (use h_abs h_bounded in auto)
  qed
  show ?thesis
  proof -
    note cd_le = \<open>c \<le> d\<close> and cd_sub = \<open>{c..d} \<subseteq> {0..2*pi}\<close>
      and sin_nz = \<open>\<And>x. x \<in> {c<..<d} \<Longrightarrow> sin (x - a) \<noteq> 0\<close>
    have g'_int: "g' integrable_on {c..d}"
      using \<open>g' absolutely_integrable_on {c..d}\<close> set_lebesgue_integral_eq_integral by blast
    have g_cont_cd: "continuous_on {c..d} g"
      using continuous_on_subset[OF g_cont cd_sub] .
    have goal: "integral {c..d} g' = g d - g c"
    proof (cases "c < d")
      case False with cd_le show ?thesis by simp
    next
      case True
        \<comment> \<open>Pick sequences c_n \<rightarrow> c and d_n \<rightarrow> d from inside (c,d)\<close>
      define c_n where "c_n \<equiv> \<lambda>n. c + (d - c) / (real n + 2)"
      define d_n where "d_n \<equiv> \<lambda>n. d - (d - c) / (real n + 2)"
      have pos: "0 < (d - c) / (real n + 2)" for n
        using True by auto
      have lt_dc: "(d - c) / (real n + 2) < d - c" for n
        using True by (simp add: divide_less_eq)
      have c_n_le_d_n: "c_n n \<le> d_n n" for n
      proof -
        have "c * real n \<le> d * real n"
          using True by (intro mult_right_mono) auto
        then have "2 * ((d - c) / (real n + 2)) \<le> d - c"
          using True by (simp add: field_simps)
        then show ?thesis unfolding c_n_def d_n_def by linarith
      qed
      have frac_lim: "(\<lambda>n. (d - c) / (real n + 2)) \<longlonglongrightarrow> 0"
      proof (rule real_tendsto_sandwich)
        show "\<forall>\<^sub>F n in sequentially. 0 \<le> (d - c) / (real n + 2)"
          using True by (intro always_eventually allI) (auto simp: field_simps)
        show "\<forall>\<^sub>F n in sequentially. (d - c) / (real n + 2) \<le> (d - c) * (1 / real n)"
          using True by (intro eventually_sequentiallyI[of 1]) (auto simp: field_simps)
        show "(\<lambda>_. (0::real)) \<longlonglongrightarrow> 0" by simp
        show "(\<lambda>n. (d - c) * (1 / real n)) \<longlonglongrightarrow> 0"
          using tendsto_mult_right_zero[OF lim_inverse_n'] by simp
      qed
      have c_n_lim: "c_n \<longlonglongrightarrow> c"
        unfolding c_n_def using tendsto_add[OF tendsto_const frac_lim] by simp
      have d_n_lim: "d_n \<longlonglongrightarrow> d"
        unfolding d_n_def using tendsto_diff[OF tendsto_const frac_lim] by simp
          \<comment> \<open>On each [c_n, d_n], trouble_free applies\<close>
      have c_n_in: "c_n n \<in> {c<..<d}" and d_n_in: "d_n n \<in> {c<..<d}" for n
        using pos[of n] lt_dc[of n] unfolding c_n_def d_n_def by auto
      have sub_n: "{c_n n..d_n n} \<subseteq> {c<..<d}" for n
        using c_n_in[of n] d_n_in[of n] c_n_le_d_n[of n] by auto
      have sub_2pi_n: "{c_n n..d_n n} \<subseteq> {0..2*pi}" for n
        using sub_n[of n] cd_sub greaterThanLessThan_subseteq_atLeastAtMost_iff by blast
      have sin_nz_n: "sin (x - a) \<noteq> 0" if "x \<in> {c_n n..d_n n}" for n x
        using that sub_n[of n] sin_nz
        by (meson greaterThanLessThan_subseteq_atLeastAtMost_iff subsetD)
      have tf_n: "(g' has_integral g (d_n n) - g (c_n n)) {c_n n..d_n n}" for n
        using trouble_free[OF c_n_le_d_n sub_2pi_n sin_nz_n] .
      have int_n: "integral {c_n n..d_n n} g' = g (d_n n) - g (c_n n)" for n
        using tf_n[of n] by (rule integral_unique)
      have int_lim: "(\<lambda>n. integral {c_n n..d_n n} g') \<longlonglongrightarrow> integral {c..d} g'"
      proof -
        have indef_cont: "continuous_on {c..d} (\<lambda>x. integral {c..x} g')"
          by (rule indefinite_integral_continuous_1[OF g'_int])
        have c_n_cd: "c_n n \<in> {c..d}" for n
          using c_n_in[of n] by (meson atLeastAtMost_iff greaterThanLessThan_iff less_imp_le)
        have d_n_cd: "d_n n \<in> {c..d}" for n
          using d_n_in[of n] by (meson atLeastAtMost_iff greaterThanLessThan_iff less_imp_le)
        have split: "integral {c_n n..d_n n} g' = integral {c..d_n n} g' - integral {c..c_n n} g'" for n
        proof -
          have cn_le: "c \<le> c_n n" using c_n_in[of n] by auto
          have int_cdn: "g' integrable_on {c..d_n n}"
            by (rule integrable_subinterval_real[OF g'_int]) (use d_n_cd[of n] cd_le in auto)
          have "integral {c..c_n n} g' + integral {c_n n..d_n n} g' = integral {c..d_n n} g'"
            by (rule Henstock_Kurzweil_Integration.integral_combine[OF cn_le c_n_le_d_n int_cdn])
          then show ?thesis by linarith
        qed
        have "(\<lambda>n. integral {c..d_n n} g') \<longlonglongrightarrow> integral {c..d} g'"
          by (rule continuous_on_tendsto_compose[OF indef_cont d_n_lim])
            (use d_n_cd cd_le in \<open>auto intro: always_eventually\<close>)
        moreover have "(\<lambda>n. integral {c..c_n n} g') \<longlonglongrightarrow> integral {c..c} g'"
          by (rule continuous_on_tendsto_compose[OF indef_cont c_n_lim])
            (use c_n_cd cd_le in \<open>auto intro: always_eventually\<close>)
        moreover have "integral {c..c} g' = 0" by simp
        ultimately have "(\<lambda>n. integral {c..d_n n} g' - integral {c..c_n n} g') \<longlonglongrightarrow> integral {c..d} g' - 0"
          by (intro tendsto_diff) simp_all
        then show ?thesis using split by simp
      qed
      moreover have "(\<lambda>n. g (d_n n) - g (c_n n)) \<longlonglongrightarrow> g d - g c"
      proof (intro tendsto_diff)
        obtain d_n_cd: "d_n n \<in> {c..d}" and c_n_cd: "c_n n \<in> {c..d}" for n
          using c_n_in d_n_in less_eq_real_def by force
        show "(\<lambda>n. g (d_n n)) \<longlonglongrightarrow> g d"
          by (rule continuous_on_tendsto_compose[OF g_cont_cd d_n_lim])
             (use d_n_cd cd_le in \<open>auto intro: always_eventually\<close>)
        show "(\<lambda>n. g (c_n n)) \<longlonglongrightarrow> g c"
          by (rule continuous_on_tendsto_compose[OF g_cont_cd c_n_lim])
             (use c_n_cd cd_le in \<open>auto intro: always_eventually\<close>)
      qed
      ultimately show ?thesis
        using int_n LIMSEQ_unique by auto
    qed
    show ?thesis
      using integrable_integral[OF g'_int] goal by auto
  qed
qed

end

theorem Wirtinger_inequality:
  fixes f f' :: "real \<Rightarrow> real"
  assumes f'hsd: "\<And>x. x \<in> {0..2*pi} \<Longrightarrow> (f' has_integral (f x - f 0)) {0..x}"
    and feq: "f (2*pi) = f 0"
    and f0: "(f has_integral 0) {0..2*pi}"
    and f'2: "(\<lambda>x. (f' x)\<^sup>2) integrable_on {0..2*pi}"
  shows "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
    and "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    and "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2) \<Longrightarrow>
         \<exists>c a. \<forall>x \<in> {0..2*pi}. f x = c * sin (x - a)"
proof -
  obtain a where a: "0 \<le> a" "a < pi" "f (a + pi) = f a"
  proof -
    have contf: \<open>continuous_on {0..2*pi} f\<close>
    proof (rule continuous_on_eq)
      show \<open>continuous_on {0..2*pi} (\<lambda>x. integral {0..x} f' + f 0)\<close>
        using f'hsd [of \<open>2*pi\<close>] 
        by (intro continuous_on_add indefinite_integral_continuous_1  continuous_on_const) auto
      show \<open>\<And>x. x \<in> {0..2*pi} \<Longrightarrow> integral {0..x} f' + f 0 = f x\<close>
        using f'hsd by (auto simp: has_integral_integrable_integral)
    qed
    define h where "h \<equiv> \<lambda>x. f (x + pi) - f x"
    have hcont: "continuous_on {0..pi} h"
      unfolding h_def
      by (intro continuous_intros continuous_on_compose2 [OF contf]) auto
    have heq: "h 0 + h pi = 0"
      unfolding h_def using feq by simp
    have iv: "is_interval (h ` {0..pi})"
      using is_interval_connected_1 connected_continuous_image [OF hcont connected_Icc]
      by blast
    have"h 0 \<in> h ` {0..pi}"  "h pi \<in> h ` {0..pi}"
      using pi_gt_zero by auto
    with heq obtain a where "a \<in> {0..pi}" "h a = 0"
      by (smt (verit, best) imageE is_interval_1 iv)
    show thesis
    proof (cases "a = pi")
      case True
      then have "h 0 = 0" using heq \<open>h a = 0\<close> by auto
      then show thesis using that [of 0] pi_gt_zero by (auto simp: h_def)
    next
      case False
      then show thesis using that [of a] \<open>a \<in> {0..pi}\<close> \<open>h a = 0\<close>
        by (auto simp: h_def)
    qed
  qed

  interpret W f f' a
    using W.intro a assms by blast

  show "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
    by (intro integrable_continuous_interval continuous_on_power contf)

  show "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
  proof -
    \<comment> \<open>Zeros of sin(x - a) in [0, 2\<pi>] are exactly at x = a and x = a + \<pi>.\<close>
    have sin_nz_1: "sin (x - a) \<noteq> 0" if "a + pi < x" "x < 2*pi" for x
      by (smt (verit) \<open>0 \<le> a\<close> sin_lt_zero that)
    have sin_nz_2: "sin (x - a) \<noteq> 0" if "a < x" "x < a + pi" for x
      by (smt (verit, ccfv_threshold) sin_gt_zero that)
    have sin_nz_3: "sin (x - a) \<noteq> 0" if "0 < x" "x < a" for x
      using \<open>a < pi\<close> sin_zero_pi_iff that by auto
    \<comment> \<open>Apply mainly_trouble_free on three intervals.\<close>
    have int1: "(g' has_integral g (2*pi) - g (a + pi)) {a + pi..2*pi}"
      by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_1 in auto)
    have int2: "(g' has_integral g (a + pi) - g a) {a..a + pi}"
      by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_2 in auto)
    have int3: "(g' has_integral g a - g 0) {0..a}"
      by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_3 in auto)
    \<comment> \<open>Combine the three integrals using has_integral_combine.\<close>
    have api_le: "a \<le> a + pi" and api_le2: "a + pi \<le> 2*pi"
      using \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
    have a_le_2pi: "a \<le> 2*pi" using \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
    have int12: "(g' has_integral (g (a + pi) - g a) + (g (2*pi) - g (a + pi))) {a..2*pi}"
      by (rule has_integral_combine[OF api_le api_le2 int2 int1])
    have int_all: "(g' has_integral (g a - g 0) + ((g (a + pi) - g a) + (g (2*pi) - g (a + pi)))) {0..2*pi}"
      by (rule has_integral_combine[OF \<open>0 \<le> a\<close> a_le_2pi int3 int12])
    \<comment> \<open>Simplify: the telescoping sum gives g(2\<pi>) - g(0).\<close>
    have int_all': "(g' has_integral g (2*pi) - g 0) {0..2*pi}"
      using int_all by (simp add: algebra_simps)
    \<comment> \<open>Show g(2\<pi>) = g(0), so the integral of g' is 0.\<close>
    have "g (2*pi) = g 0"
      unfolding g_def using feq by (simp add: tan_def)
    hence g'_zero: "(g' has_integral 0) {0..2*pi}"
      using int_all' by simp
    \<comment> \<open>Extract the inequality from \<integral>g' = 0.\<close>
    \<comment> \<open>g'(x) = (f'(x))² − (f(x)−f(a))² − rest(x)², so (f'(x))² − g'(x) = (f(x)−f(a))² + rest(x)² \<ge> (f(x)−f(a))².\<close>
    have ffa_int: "(\<lambda>x. (f x - f a)\<^sup>2) integrable_on {0..2*pi}"
      by (intro integrable_continuous_interval continuous_intros contf)
    have g'_int: "g' integrable_on {0..2*pi}"
      using g'_zero by (auto simp: has_integral_integrable_integral)
    \<comment> \<open>(f')² − g' is integrable and its integral = \<integral>(f')² − 0 = \<integral>(f')².\<close>
    have diff_int: "((\<lambda>x. (f' x)\<^sup>2 - g' x) has_integral integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2) - 0) {0..2*pi}"
      by (rule has_integral_diff[OF integrable_integral[OF f'2] g'_zero])
    \<comment> \<open>(f')²(x) − g'(x) = (f(x)−f(a))² + rest(x)² \<ge> (f(x)−f(a))².\<close>
    have diff_eq: "(f' x)\<^sup>2 - g' x = (f x - f a)\<^sup>2 + (f' x - (f x - f a) / tan (x - a))\<^sup>2" for x
      unfolding g'_def by (simp add: algebra_simps)
    have diff_ge: "(f' x)\<^sup>2 - g' x \<ge> (f x - f a)\<^sup>2" for x
      unfolding diff_eq by (simp add: zero_le_power2)
    \<comment> \<open>Therefore \<integral>(f')² \<ge> \<integral>(f(x)−f(a))².\<close>
    have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2 - g' x)"
      by (rule integral_le[OF ffa_int]) (use diff_int has_integral_integrable_integral in \<open>auto intro: diff_ge\<close>)
    also have "\<dots> = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
      using diff_int has_integral_integrable_integral by auto
    finally have ineq_ffa: "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)" .
    \<comment> \<open>Show \<integral>(f(x))² \<le> \<integral>(f(x)−f(a))² using \<integral>f = 0.\<close>
    have "(f x)\<^sup>2 \<le> (f x - f a)\<^sup>2 + 2 * f a * f x - (f a)\<^sup>2" for x
      by (simp add: power2_eq_square algebra_simps)
    \<comment> \<open>Actually: (f(x)−f(a))² = (f(x))² − 2\<sqdot>f(a)\<sqdot>f(x) + (f(a))², so (f(x))² = (f(x)−f(a))² + 2\<sqdot>f(a)\<sqdot>f(x) − (f(a))².\<close>
    have fx_eq: "(f x)\<^sup>2 = (f x - f a)\<^sup>2 + 2 * f a * f x - (f a)\<^sup>2" for x
      by (simp add: power2_eq_square algebra_simps)
    have f_int: "f integrable_on {0..2*pi}"
      by (rule integrable_continuous_interval[OF contf])
    \<comment> \<open>\<integral>f = 0 by assumption.\<close>
    have f_integral_0: "integral {0..2*pi} f = 0"
      using f0 by (auto simp: has_integral_integrable_integral)
    \<comment> \<open>\<integral>(f(x)−f(a))² = \<integral>(f(x))² + (f(a))²\<sqdot>2\<pi>  (using \<integral>f = 0).\<close>
    have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) 
        = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) - 2 * f a * integral {0..2*pi} f + (f a)\<^sup>2 * (2*pi)"
    proof -
      have eq: "(f x - f a)\<^sup>2 = (f x)\<^sup>2 - 2 * f a * f x + (f a)\<^sup>2" for x
        by (simp add: power2_eq_square algebra_simps)
      have fx2_int: "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
        by (intro integrable_continuous_interval continuous_intros contf)
      have ffa_2fa_int: "(\<lambda>x. 2 * f a * f x) integrable_on {0..2*pi}"
        using f_int integrable_on_mult_right by blast
      \<comment> \<open>Split: (f−fa)² = f² − 2\<sqdot>fa\<sqdot>f + fa²\<close>
      have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x + (f a)\<^sup>2)"
        by (simp add: eq)
      also have "\<dots> = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x) + integral {0..2*pi} (\<lambda>x. (f a)\<^sup>2)"
        by (rule Henstock_Kurzweil_Integration.integral_add)
          (auto intro: integrable_diff fx2_int ffa_2fa_int)
      also have "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x) =
        integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) - integral {0..2*pi} (\<lambda>x. 2 * f a * f x)"
        by (rule Henstock_Kurzweil_Integration.integral_diff[OF fx2_int ffa_2fa_int])
      also have "integral {0..2*pi} (\<lambda>x. 2 * f a * f x) = 2 * f a * integral {0..2*pi} f"
        using integral_cmul by simp
      also have "integral {0..2*pi} (\<lambda>x. (f a)\<^sup>2) = (f a)\<^sup>2 * (2*pi)"
        by simp
      finally show ?thesis by linarith
    qed
    with f_integral_0 have "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2)"
      by auto
    thus ?thesis using ineq_ffa by linarith
  qed
  show "\<exists>c a. \<forall>x \<in> {0..2*pi}. f x = c * sin (x - a)"
    if "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
  proof -
    \<comment> \<open>From the equality, all intermediate inequalities are equalities.\<close>
    note eq_hyp = that
    \<comment> \<open>Re-derive key intermediate facts.\<close>
    have ffa_2fa_int: "(\<lambda>x. 2 * f a * f x) integrable_on {0..2*pi}"
      using assms(3) integrable_on_mult_right by blast
    have fx2_int: "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
      by (intro integrable_continuous_interval continuous_intros contf)
    have ffa_int: "(\<lambda>x. (f x - f a)\<^sup>2) integrable_on {0..2*pi}"
      by (intro integrable_continuous_interval continuous_intros contf)
    have ffa_eq: "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) + (f a)\<^sup>2 * (2*pi)"
    proof -
      have eq: "(f x - f a)\<^sup>2 = (f x)\<^sup>2 - 2 * f a * f x + (f a)\<^sup>2" for x
        by (simp add: power2_eq_square algebra_simps)
      have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) =
        integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x + (f a)\<^sup>2)"
        by (rule integral_cong) (simp add: eq)
      also have "\<dots> = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x) +
        integral {0..2*pi} (\<lambda>x. (f a)\<^sup>2)"
        by (rule Henstock_Kurzweil_Integration.integral_add)
          (auto intro: integrable_diff fx2_int ffa_2fa_int)
      also have "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x) =
        integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) - integral {0..2*pi} (\<lambda>x. 2 * f a * f x)"
        by (rule Henstock_Kurzweil_Integration.integral_diff[OF fx2_int ffa_2fa_int])
      also have "integral {0..2*pi} (\<lambda>x. 2 * f a * f x) = 2 * f a * integral {0..2*pi} f"
        using integral_cmul by simp
      also have "integral {0..2*pi} (\<lambda>x. (f a)\<^sup>2) = (f a)\<^sup>2 * (2*pi)"
        by simp
      finally show ?thesis using f0 by (auto simp: has_integral_integrable_integral)
    qed
    \<comment> \<open>Re-derive g'_zero: (g' has_integral 0) {0..2\<pi>}.\<close>
    have sin_nz_1: "sin (x - a) \<noteq> 0" if "a + pi < x" "x < 2*pi" for x
      by (smt (verit) \<open>0 \<le> a\<close> sin_lt_zero that)
    have sin_nz_2: "sin (x - a) \<noteq> 0" if "a < x" "x < a + pi" for x
      by (smt (verit, ccfv_threshold) sin_gt_zero that)
    have sin_nz_3: "sin (x - a) \<noteq> 0" if "0 < x" "x < a" for x
      using \<open>a < pi\<close> sin_zero_pi_iff that by auto
    have int1: "(g' has_integral g (2*pi) - g (a + pi)) {a + pi..2*pi}"
      by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_1 in auto)
    have int2: "(g' has_integral g (a + pi) - g a) {a..a + pi}"
      by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_2 in auto)
    have int3: "(g' has_integral g a - g 0) {0..a}"
      by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_3 in auto)
    have api_le: "a \<le> a + pi" and api_le2: "a + pi \<le> 2*pi"
      using \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
    have a_le_2pi: "a \<le> 2*pi" using \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
    have int12: "(g' has_integral (g (a + pi) - g a) + (g (2*pi) - g (a + pi))) {a..2*pi}"
      by (rule has_integral_combine[OF api_le api_le2 int2 int1])
    have int_all: "(g' has_integral (g a - g 0) + ((g (a + pi) - g a) + (g (2*pi) - g (a + pi)))) {0..2*pi}"
      by (rule has_integral_combine[OF \<open>0 \<le> a\<close> a_le_2pi int3 int12])
    have int_all': "(g' has_integral g (2*pi) - g 0) {0..2*pi}"
      using int_all by (simp add: algebra_simps)
    have "g (2*pi) = g 0"
      unfolding g_def using feq by (simp add: tan_def)
    hence g'_zero: "(g' has_integral 0) {0..2*pi}"
      using int_all' by simp
    have ineq_ffa: "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) \<le>
      integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    proof -
      have diff_ge: "(f' x)\<^sup>2 - g' x \<ge> (f x - f a)\<^sup>2" for x
        unfolding g'_def by (simp add: zero_le_power2)
      have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) \<le>
        integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2 - g' x)"
        by (rule integral_le[OF ffa_int])
          (use has_integral_diff[OF integrable_integral[OF f'2] g'_zero]
               has_integral_integrable_integral diff_ge in auto)
      also have "\<dots> = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
        using has_integral_diff[OF integrable_integral[OF f'2] g'_zero]
              has_integral_integrable_integral by auto
      finally show ?thesis .
    qed
    \<comment> \<open>Step 1: f(a) = 0.\<close>
    have fa0: "f a = 0"
      by (smt (verit) eq_hyp ffa_eq ineq_ffa mult_eq_0_iff mult_nonneg_nonneg pi_gt_zero power_eq_0_iff
          zero_le_power2)
    \<comment> \<open>Step 2: The "rest" term integrates to 0.\<close>
    define rest where "rest \<equiv> \<lambda>x. f' x - (f x - f a) / tan (x - a)"
    have diff_eq: "(f' x)\<^sup>2 - g' x = (f x - f a)\<^sup>2 + (rest x)\<^sup>2" for x
      unfolding g'_def rest_def by (simp add: algebra_simps)
    have rest_sq_int: "(\<lambda>x. (rest x)\<^sup>2) integrable_on {0..2*pi}"
    proof -
      have diff_int: "(\<lambda>x. (f' x)\<^sup>2 - g' x) integrable_on {0..2*pi}"
        using has_integral_diff[OF integrable_integral[OF f'2] g'_zero]
              has_integral_integrable by blast
      have eq: "(\<lambda>x. (rest x)\<^sup>2) = (\<lambda>x. (f' x)\<^sup>2 - g' x - (f x - f a)\<^sup>2)"
        by (rule ext) (use diff_eq in \<open>simp add: algebra_simps\<close>)
      show ?thesis unfolding eq
        by (rule integrable_diff[OF diff_int ffa_int])
    qed
    have rest_sq_zero: "integral {0..2*pi} (\<lambda>x. (rest x)\<^sup>2) = 0"
    proof -
      have "integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2 - g' x) =
        integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
        using has_integral_diff[OF integrable_integral[OF f'2] g'_zero]
              has_integral_integrable_integral by auto
      moreover have "integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2 - g' x) =
        integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) + integral {0..2*pi} (\<lambda>x. (rest x)\<^sup>2)"
      proof -
        have eq: "(f' x)\<^sup>2 - g' x = (f x - f a)\<^sup>2 + (rest x)\<^sup>2" for x
          using diff_eq by auto
        have "integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2 - g' x) =
          integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2 + (rest x)\<^sup>2)"
          by (rule integral_cong) (use eq in auto)
        also have "\<dots> = integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) +
          integral {0..2*pi} (\<lambda>x. (rest x)\<^sup>2)"
          by (rule Henstock_Kurzweil_Integration.integral_add[OF ffa_int rest_sq_int])
        finally show ?thesis .
      qed
      moreover have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2)"
        using ffa_eq fa0 by simp
      ultimately show ?thesis using eq_hyp by linarith
    qed
    \<comment> \<open>Integral of c * sin(x - a) via the fundamental theorem of calculus.\<close>
    have csin_integral: "integral {u..v} (\<lambda>x. c * sin (x - a)) =
        c * (cos (u - a) - cos (v - a))" if "u \<le> v" for u v c
    proof -
      have "((\<lambda>x. - (c * cos (x - a))) has_real_derivative c * sin (x - a)) (at x)" for x
        by (auto intro!: derivative_eq_intros simp: algebra_simps)
      hence hvd: "((\<lambda>x. - (c * cos (x - a))) has_vector_derivative c * sin (x - a))
        (at x within {u..v})" for x
        by (meson has_real_derivative_iff_has_vector_derivative has_vector_derivative_at_within)
      hence "((\<lambda>x. c * sin (x - a)) has_integral
        (- (c * cos (v - a)) - (- (c * cos (u - a))))) {u..v}"
        using that by (intro fundamental_theorem_of_calculus) auto
      thus ?thesis
        by (simp add: has_integral_integrable_integral algebra_simps)
    qed
    \<comment> \<open>Key fact: on intervals where sin(x−a) \<noteq> 0, f equals c * sin(x−a).\<close>
    have key_fact: "\<exists>c. \<forall>x\<in>{u..v}. f x = c * sin (x - a)"
      if huv: "0 \<le> u" "u < v" "v \<le> 2*pi"
        and hsin: "\<And>x. x \<in> {u<..<v} \<Longrightarrow> sin (x - a) \<noteq> 0"
      for u v
    proof -
      \<comment> \<open>Open-interval version (to be proved later).\<close>
      have open_ver: "\<exists>c. \<forall>x\<in>{u<..<v}. f x = c * sin (x - a)"
      proof -
        \<comment> \<open>Step 1: \<integral>ᵤᵥ rest² = 0 from \<integral>₀²\<pi> rest² = 0 and nonnegativity.\<close>
        have rest_sq_sub: "(\<lambda>x. (rest x)\<^sup>2) integrable_on {u..v}"
          by (rule integrable_subinterval_real[OF rest_sq_int])
             (use huv in auto)
        have rest_sq_nonneg: "0 \<le> (rest x)\<^sup>2" for x
          by (rule zero_le_power2)
        have "integral {u..v} (\<lambda>x. (rest x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (rest x)\<^sup>2)"
          by (rule integral_subset_le[OF _ rest_sq_sub rest_sq_int])
             (use huv rest_sq_nonneg in auto)
        moreover have "0 \<le> integral {u..v} (\<lambda>x. (rest x)\<^sup>2)"
          by (rule integral_nonneg[OF rest_sq_sub]) (use rest_sq_nonneg in auto)
        ultimately have rest_sq_sub_zero: "integral {u..v} (\<lambda>x. (rest x)\<^sup>2) = 0"
          using rest_sq_zero by linarith
        \<comment> \<open>Step 2: rest = 0 a.e. on {u..v} via Lebesgue theory.\<close>
        have rest_ae_zero: "AE x in lebesgue_on {u..v}. rest x = 0"
        proof -
          have uv_meas: "{u..v} \<in> sets lebesgue" by simp
          have rest_sq_abs: "(\<lambda>x. (rest x)\<^sup>2) absolutely_integrable_on {u..v}"
            by (rule nonnegative_absolutely_integrable_1[OF rest_sq_sub])
               (use rest_sq_nonneg in auto)
          have rest_sq_leb: "integrable (lebesgue_on {u..v}) (\<lambda>x. (rest x)\<^sup>2)"
            by (rule absolutely_integrable_imp_integrable[OF rest_sq_abs uv_meas])
          have "integral\<^sup>L (lebesgue_on {u..v}) (\<lambda>x. (rest x)\<^sup>2) = integral {u..v} (\<lambda>x. (rest x)\<^sup>2)"
            by (rule lebesgue_integral_eq_integral[OF rest_sq_leb uv_meas])
          hence leb_zero: "integral\<^sup>L (lebesgue_on {u..v}) (\<lambda>x. (rest x)\<^sup>2) = 0"
            using rest_sq_sub_zero by simp
          have "AE x in lebesgue_on {u..v}. (rest x)\<^sup>2 = 0"
            using integral_nonneg_eq_0_iff_AE[OF rest_sq_leb] leb_zero
            by (simp add: zero_le_power2)
          thus ?thesis
            by (rule AE_mp) (auto simp: power2_eq_square)
        qed
        \<comment> \<open>Step 3: h(x) = f(x)/sin(x-a) is constant on (u,v).\<close>
        \<comment> \<open>For any [s,t] \<subseteq> (u,v), h is absolutely continuous and h' = rest/sin a.e.,\<close>
        \<comment> \<open>so h(t) - h(s) = \<integral>ₛₜ rest/sin = 0.\<close>
        have h_const: "f s / sin (s - a) = f t / sin (t-a)"
          if hst: "s \<in> {u<..<v}" "t \<in> {u<..<v}" for s t
        proof (cases "s = t")
          case True thus ?thesis by simp
        next
          case False
          \<comment> \<open>WLOG s < t\<close>
          define s' where "s' = min s t"
          define t' where "t' = max s t"
          have st': "u < s'" "t' < v" "s' < t'"
            using hst False unfolding s'_def t'_def by auto
          have st'_sub: "{s'..t'} \<subseteq> {u<..<v}"
            using st' by auto
          have st'_sub2: "{s'..t'} \<subseteq> {0..2*pi}"
            using st' huv by auto
          \<comment> \<open>sin(x - a) \<noteq> 0 on [s', t']\<close>
          have sin_nz_st: "sin (x - a) \<noteq> 0" if "x \<in> {s'..t'}" for x
            using hsin st'_sub that by auto
          \<comment> \<open>h = f/sin is absolutely continuous on [s', t']\<close>
          define h where "h \<equiv> \<lambda>x. f x / sin (x - a)"
          have ac_f: "absolutely_continuous_on {0..2*pi} f"
            using absolute_integral_absolutely_continuous_derivative_eq f'abs f'hsd by blast
          have ac_f_st: "absolutely_continuous_on {s'..t'} f"
            using absolutely_continuous_on_subset[OF ac_f st'_sub2] .
          \<comment> \<open>1/sin(x-a) is absolutely continuous on [s', t'] via Lipschitz bound\<close>
          have ac_inv_sin: "absolutely_continuous_on {s'..t'} (\<lambda>x. inverse (sin (x - a)))"
          proof -
            \<comment> \<open>The derivative -cos/sin² is bounded on [s',t'] since sin is bounded away from 0\<close>
            define deriv where "deriv \<equiv> \<lambda>x::real. - cos (x - a) / (sin (x - a))\<^sup>2"
            have cont_deriv: "continuous_on {s'..t'} deriv"
              unfolding deriv_def
              by (intro continuous_intros) (use sin_nz_st in auto)
            have bdd: "bounded (deriv ` {s'..t'})"
              using compact_continuous_image compact_imp_bounded cont_deriv by blast
            then obtain B where B: "\<And>x. x \<in> {s'..t'} \<Longrightarrow> \<bar>deriv x\<bar> \<le> B"
              by (meson bounded_real imageI)
            have lipschitz: "\<bar>inverse (sin (x - a)) - inverse (sin (y - a))\<bar> \<le> B * \<bar>x - y\<bar>"
              if hx: "s' \<le> x" "x \<le> t'" and hy: "s' \<le> y" "y \<le> t'" for x y
            proof -
              have deriv_at: "((\<lambda>x. inverse (sin (x - a))) has_real_derivative deriv z)
                              (at z within {s'..t'})"
                if hz: "z \<in> {s'..t'}" for z
              proof -
                have snz: "sin (z - a) \<noteq> 0" using sin_nz_st[OF hz] .
                have "((\<lambda>x. sin (x - a)) has_real_derivative cos (z - a))
                       (at z within {s'..t'})"
                  by (intro derivative_eq_intros | simp)+
                moreover have "- (cos (z - a) * inverse (sin (z - a) ^ Suc (Suc 0)))
                              = deriv z"
                  unfolding deriv_def power2_eq_square
                  by (simp add: field_simps)
                ultimately show ?thesis
                  by (metis DERIV_inverse_fun snz)
              qed
              have "norm (inverse (sin (x - a)) - inverse (sin (y - a)))
                    \<le> B * norm (x - y)"
              proof (rule field_differentiable_bound[OF convex_real_interval(5)])
                fix z assume "z \<in> {s'..t'}"
                then show "((\<lambda>x. inverse (sin (x - a))) has_field_derivative deriv z)
                           (at z within {s'..t'})"
                  using deriv_at by auto
              next
                fix z assume "z \<in> {s'..t'}"
                then show "norm (deriv z) \<le> B" using B by (auto simp: abs_le_iff)
              next
                show "x \<in> {s'..t'}" using hx by auto
              next
                show "y \<in> {s'..t'}" using hy by auto
              qed
              then show ?thesis by (simp add: real_norm_def)
            qed
            then show ?thesis
              by (intro Lipschitz_imp_absolutely_continuous strip; auto)
          qed
          \<comment> \<open>h = f \<sqdot> (1/sin) is AC on [s', t']\<close>
          have ac_h: "absolutely_continuous_on {s'..t'} h"
            using absolutely_continuous_on_mul[OF ac_f_st ac_inv_sin]
            by (simp add: divide_real_def h_def)
          \<comment> \<open>h has derivative rest/sin a.e. on [s', t']\<close>
          obtain k where negk: "negligible k"
            and derivf: "\<And>t. t \<in> {0..2*pi} - k \<Longrightarrow>
              ((\<lambda>u. integral {0..u} f') has_vector_derivative f' t)
              (at t within {0..2*pi})"
            using f' has_vector_derivative_indefinite_integral by blast
          have f_eq: "f t = f 0 + integral {0..t} f'" if "t \<in> {0..2*pi}" for t
            using f'hsd[OF that] by (auto simp: has_integral_integrable_integral)
          have fderiv: "(f has_vector_derivative f' t) (at t within {s'..t'})"
            if "t \<in> {s'..t'} - k" for t
          proof -
            have t02: "t \<in> {0..2*pi}" using that st'_sub2 by auto
            have "t \<in> {0..2*pi} - k" using that st'_sub2 by auto
            then have "((\<lambda>u. integral {0..u} f') has_vector_derivative f' t)
                       (at t within {0..2*pi})"
              using derivf by auto
            then have "((\<lambda>u. f u - f 0) has_vector_derivative f' t)
                       (at t within {0..2*pi})"
              using has_vector_derivative_transform_within t02
              by (smt (verit, best) f_eq has_vector_derivative_transform)
            then have "(f has_vector_derivative f' t) (at t within {0..2*pi})"
              using has_vector_derivative_diff_const by blast
            then show ?thesis
              by (rule has_vector_derivative_within_subset) (use st'_sub2 in auto)
          qed
          \<comment> \<open>Derivative of h = f/sin via quotient rule\<close>
          have hderiv: "(h has_vector_derivative (f' t * sin (t-a) - f t * cos (t-a)) / (sin (t-a))\<^sup>2)
              (at t within {s'..t'})"
            if "t \<in> {s'..t'} - k" for t
          proof -
            have fd: "(f has_real_derivative f' t) (at t within {s'..t'})"
              using fderiv that by (simp add: has_real_derivative_iff_has_vector_derivative)
            have sd: "((\<lambda>x. sin (x - a)) has_real_derivative cos (t-a))
                      (at t within {s'..t'})"
              by (auto intro!: derivative_eq_intros)
            have "((\<lambda>x. f x / sin (x - a)) has_real_derivative
                   (f' t * sin (t-a) - f t * cos (t-a)) / (sin (t-a))\<^sup>2)
                  (at t within {s'..t'})"
              using DERIV_quotient[OF fd sd] sin_nz_st that
              by (simp add: power2_eq_square algebra_simps)
            then show ?thesis unfolding h_def
              by (simp add: has_real_derivative_iff_has_vector_derivative)
          qed
          \<comment> \<open>The derivative of h equals rest/sin\<close>
          have hderiv_eq: "(f' t * sin (t-a) - f t * cos (t-a)) / (sin (t-a))\<^sup>2
                          = rest t / sin (t-a)"
            if "t \<in> {s'..t'}" for t
            using that unfolding rest_def fa0
            by (simp add: power2_eq_square divide_simps Multiseries_Expansion.tan_conv_sin_cos)
          have hderiv': "(h has_vector_derivative rest t / sin (t-a))
              (at t within {s'..t'})"
            if "t \<in> {s'..t'} - k" for t
            using hderiv[OF that] hderiv_eq[of t] that by auto
          \<comment> \<open>rest = 0 a.e. on {u..v}, so get a negligible set N\<close>
          obtain N where negN: "negligible N" and restN: "\<And>x. x \<in> {u..v} - N \<Longrightarrow> rest x = 0"
          proof -
            from rest_ae_zero[unfolded eventually_ae_filter[of _ "lebesgue_on {u..v}"]]
            obtain N0 where N0: "N0 \<in> null_sets (lebesgue_on {u..v})"
              and sub: "{x \<in> space (lebesgue_on {u..v}). rest x \<noteq> 0} \<subseteq> N0"
              by auto
            have "negligible N0"
              using null_sets_restrict_space[of "{u..v}"] N0 negligible_iff_null_sets 
              by auto
            moreover have "rest x = 0" if "x \<in> {u..v} - N0" for x
              using sub that by (auto simp: space_lebesgue_on)
            ultimately show ?thesis using that by blast
          qed
          \<comment> \<open>h has derivative 0 a.e. on {s'..t'}\<close>
          have hderiv_zero: "(h has_vector_derivative 0) (at t within {s'..t'})"
            if "t \<in> {s'..t'} - (k \<union> N)" for t
            using restN[of t] that st'_sub hderiv' using st'(2) by fastforce
          have neg_kN: "negligible (k \<union> N)"
            using negk negN by (rule negligible_Un)
          \<comment> \<open>By FTC for AC: h(t') - h(s') = \<integral> 0 = 0\<close>
          have "h t' - h s' = integral {s'..t'} (\<lambda>x. 0::real)"
            using fundamental_theorem_of_calculus_absolutely_continuous [OF neg_kN _ ac_h hderiv_zero]
            using st' by auto
          then have "h s' = h t'" by simp
          \<comment> \<open>Translate back to f/sin\<close>
          then show ?thesis
            unfolding h_def s'_def t'_def by (auto split: if_splits)
        qed
        obtain x where "x \<in> {u<..<v}"
          using huv(2) dense by (metis greaterThanLessThan_iff)
        with eq_divide_eq hsin h_const that show ?thesis
          by metis
      qed
      then obtain c where hc: "\<forall>x\<in>{u<..<v}. f x = c * sin (x - a)"
        by auto
      \<comment> \<open>Extend to the closed interval by continuity.\<close>
      have "f x = c * sin (x - a)" if "x \<in> {u..v}" for x
      proof -
        have "f x - c * sin (x - a) = 0"
        proof (rule continuous_constant_on_closure[of "{u<..<v}" "\<lambda>x. f x - c * sin (x - a)" 0])
          show "continuous_on (closure {u<..<v}) (\<lambda>x. f x - c * sin (x - a))"
            unfolding closure_greaterThanLessThan[OF huv(2)]
            by (intro continuous_intros continuous_on_subset[OF contf])
               (use huv in auto)
          show "\<And>y. y \<in> {u<..<v} \<Longrightarrow> f y - c * sin (y - a) = 0"
            using hc by simp
          show "x \<in> closure {u<..<v}"
            unfolding closure_greaterThanLessThan[OF huv(2)] using that by auto
        qed
        thus ?thesis by simp
      qed
      thus ?thesis by auto
    qed
    show ?thesis
    proof (cases "a=0")
      case True
      then show ?thesis
      proof -
        obtain c1 where c1: "\<forall>x\<in>{0..pi}. f x = c1 * sin (x - a)"
          using key_fact[of 0 pi] sin_nz_2 True pi_gt_zero by auto
        obtain c2 where c2: "\<forall>x\<in>{pi..2*pi}. f x = c2 * sin (x - a)"
          using key_fact[of pi "2*pi"] sin_nz_1 True pi_gt_zero by auto
        \<comment> \<open>Use \<integral>f = 0 and csin_integral to show c1 = c2.\<close>
        have eq1: "integral {0..pi} f = c1 * (cos (0 - a) - cos (pi - a))"
          by (metis (lifting) integral_cong True add_0 api_le c1 csin_integral)
        have eq2: "integral {pi..2*pi} f = c2 * (cos (pi - a) - cos (2*pi - a))"
          by (metis (lifting) integral_cong True add_0 api_le2 c2 csin_integral)
        have int_split: "integral {0..2*pi} f = integral {0..pi} f + integral {pi..2*pi} f"
            using Henstock_Kurzweil_Integration.integral_combine[OF pi_ge_zero]
            by (metis True add_cancel_left_left api_le2 assms(3) integrable_on_def)
        have "integral {0..2*pi} f = 0"
          using f0 by (simp add: has_integral_integrable_integral)
        hence "c1 * (cos (0 - a) - cos (pi - a)) + c2 * (cos (pi - a) - cos (2*pi - a)) = 0"
          using int_split eq1 eq2 by linarith
        hence "c1 = c2" using True
          by (simp add: cos_two_pi cos_pi)
        then show ?thesis
          by (metis atLeastAtMost_iff c1 c2 nle_le)
      qed
    next
      case False
      then show ?thesis
      proof -
        have a_pos: "0 < a" using \<open>0 \<le> a\<close> False by auto
        \<comment> \<open>Three intervals where sin(x-a) \<noteq> 0\<close>
        obtain c1 where c1: "\<forall>x\<in>{0..a}. f x = c1 * sin (x - a)"
          using key_fact[of 0 a] sin_nz_3 a_pos \<open>a < pi\<close> by auto
        obtain c2 where c2: "\<forall>x\<in>{a..a+pi}. f x = c2 * sin (x - a)"
          using key_fact[of a "a+pi"] sin_nz_2 a_pos \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
        obtain c3 where c3: "\<forall>x\<in>{a+pi..2*pi}. f x = c3 * sin (x - a)"
          using key_fact[of "a+pi" "2*pi"] sin_nz_1 \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
        \<comment> \<open>Show c1 = c3 using f(2\<pi>) = f(0)\<close>
        have sin_a_nz: "sin a \<noteq> 0"
          using sin_gt_zero[OF a_pos \<open>a < pi\<close>] by (simp add: less_imp_le)
        have f0_eq: "f 0 = c1 * sin (0 - a)"
          using c1 \<open>0 \<le> a\<close> by auto
        have f2pi_eq: "f (2*pi) = c3 * sin (2*pi - a)"
          using c3 \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
        \<comment> \<open>Compute integrals on each interval\<close>
        have eq1: "integral {0..a} f = c1 * (cos (0 - a) - cos (a - a))"
          by (metis (no_types, lifting) integral_cong \<open>0 \<le> a\<close> c1 csin_integral)
        have eq2: "integral {a..a+pi} f = c2 * (cos (a - a) - cos ((a+pi) - a))"
          by (metis (no_types, lifting) api_le integral_cong c2 csin_integral)
        have eq3: "integral {a+pi..2*pi} f = c3 * (cos ((a+pi) - a) - cos (2*pi - a))"
          by (metis (mono_tags, lifting) integral_cong api_le2 c3 csin_integral)
        \<comment> \<open>Split the integral into three parts\<close>
        have f_int: "f integrable_on {0..2*pi}"
          using f0 has_integral_integrable by blast
        have a_le: "a \<le> a + pi" using pi_gt_zero by linarith
        have api_le: "a + pi \<le> 2 * pi" using \<open>a < pi\<close> by linarith
        have a_le_2pi: "a \<le> 2 * pi" using a_pos \<open>a < pi\<close> by linarith
        have int_split: "integral {0..2*pi} f =
          integral {0..a} f + integral {a..a+pi} f + integral {a+pi..2*pi} f"
        proof -
          have "integral {0..2*pi} f = integral {0..a+pi} f + integral {a+pi..2*pi} f"
            using Henstock_Kurzweil_Integration.integral_combine [OF _ api_le f_int] 
                  a_pos pi_gt_zero by auto
          moreover have "f integrable_on {0..a+pi}"
            using integrable_subinterval_real[OF f_int] a_pos api_le by auto
          ultimately show ?thesis
            by (metis Henstock_Kurzweil_Integration.integral_combine \<open>0 \<le> a\<close> a_le)
        qed
        \<comment> \<open>Use \<integral>f = 0 to show c1 = c2\<close>
        have "integral {0..2*pi} f = 0"
          using f0 by (simp add: has_integral_integrable_integral)
        hence sum_eq: "c1 * (cos (0 - a) - cos (a - a)) + c2 * (cos (a - a) - cos ((a+pi) - a)) +
          c3 * (cos ((a+pi) - a) - cos (2*pi - a)) = 0"
          using int_split eq1 eq2 eq3 by linarith
        have "c1 * (cos a - 1) + 2 * c2 + c1 * (- 1 - cos a) = 0"
          using f0_eq f2pi_eq feq sin_a_nz sum_eq by fastforce
        hence c12_eq: "c1 = c2"
          by (simp add: algebra_simps)
        show "\<exists>c a. \<forall>x\<in>{0..2 * pi}. f x = c * sin (x - a)"
          using f0_eq feq sin_a_nz c1 c2 c3 c12_eq by fastforce
      qed
    qed
  qed
qed

theorem scaled_Wirtinger_inequality:
  fixes f f' :: "real \<Rightarrow> real"
  assumes f': "\<And>x. x \<in> {0..1} \<Longrightarrow> (f' has_integral (f x - f 0)) {0..x}"
    and "f 1 = f 0"
    and f_int: "(f has_integral 0) {0..1}"
    and f'_int: "(\<lambda>x. (f' x)\<^sup>2) integrable_on {0..1}"
  shows "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..1}"
    and "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) \<le> integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    and "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2) \<Longrightarrow>
      \<exists>c a. \<forall>x \<in> {0..1}. f x = c * sin (2*pi*x - a)"
proof -
  define g where "g \<equiv> \<lambda>x. f (x / (2*pi))"
  define g' where "g' \<equiv> \<lambda>x. (1/(2*pi)) * f' (x / (2*pi))"
  have twopi_pos: "2 * pi > 0" and twopi_nz: "2 * pi \<noteq> 0"
    and inv_twopi_pos: "1/(2*pi) > 0" and inv_twopi_nz: "1/(2*pi) \<noteq> (0::real)"
    using pi_gt_zero by auto
  have img: "(\<lambda>x. x / (1/(2*pi))) ` {0..1} = {0..2*pi}"
    using image_divide_atLeastAtMost[OF inv_twopi_pos] by simp
  have prec1: "\<And>x. x \<in> {0..2*pi} \<Longrightarrow> (g' has_integral (g x - g 0)) {0..x}"
  proof -
    fix x :: real assume x: "x \<in> {0..2*pi}"
    have *: "((\<lambda>s. f' (1/(2*pi) * s)) has_integral (2*pi) *\<^sub>R (f (x/(2*pi)) - f 0))
                 ((\<lambda>s. s / (1/(2*pi))) ` {0..x/(2*pi)})"
      using x has_integral_stretch_real[OF f' inv_twopi_nz] inv_twopi_pos by simp
    have **: "((\<lambda>s. f' (s/(2*pi))) has_integral (2*pi) * (f (x/(2*pi)) - f 0)) {0..x}"
      using * image_divide_atLeastAtMost[OF inv_twopi_pos, of 0 "x/(2*pi)"]
      using twopi_pos by (simp add: field_simps)
    have val: "1/(2*pi) * ((2*pi) * (f (x/(2*pi)) - f 0)) = f (x/(2*pi)) - f 0"
      using twopi_nz by simp
    show "(g' has_integral (g x - g 0)) {0..x}"
      using has_integral_mult_right[OF **, of "1/(2*pi)"] twopi_nz 
      unfolding g'_def g_def val by (simp add: field_simps)
  qed
  have prec2: "g (2*pi) = g 0"
    unfolding g_def using assms(2) by simp
  have prec3: "(g has_integral 0) {0..2*pi}"
    using has_integral_stretch_real_iff[OF inv_twopi_nz, of f 0 0 1]  f_int g_def img by auto
  have int: "(\<lambda>x. (f' (x/(2*pi)))\<^sup>2) integrable_on {0..2*pi}"
    using f'_int integrable_stretch_real[OF _ inv_twopi_nz, of "\<lambda>x. (f' x)\<^sup>2" 0 1] img 
    by (simp add: field_simps)
  then have prec4: "(\<lambda>x. (g' x)\<^sup>2) integrable_on {0..2*pi}"
    unfolding g'_def power_mult_distrib
    using integrable_on_cmult_left[OF int, of "(1/(2*pi))\<^sup>2"] by (simp add: algebra_simps)
  text \<open>Apply unscaled Wirtinger inequality\<close>
  have W1: "(\<lambda>x. (g x)\<^sup>2) integrable_on {0..2*pi}"
    and W2: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2)"
    and W3: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) \<Longrightarrow>
         \<exists>c a. \<forall>x \<in> {0..2*pi}. g x = c * sin (x - a)"
    using Wirtinger_inequality[OF prec1 prec2 prec3 prec4] by auto
  text \<open>Transfer conclusions back to scaled domain\<close>
  have g_unfold: "\<And>x. (g x)\<^sup>2 = (f (1/(2*pi) * x))\<^sup>2"
    unfolding g_def by (simp add: field_simps)
  have g'_unfold: "\<And>x. (g' x)\<^sup>2 = (1/(2*pi))\<^sup>2 * (f' (1/(2*pi) * x))\<^sup>2"
    unfolding g'_def by (simp add: power_mult_distrib field_simps)
  text \<open>Show 1: integrability of (f x)² on {0..1}\<close>
  show int_f2: "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..1}"
    using integrable_stretch_real_iff[OF inv_twopi_nz, of "\<lambda>x. (f x)\<^sup>2" 0 1] W1 g_def img by force 
  text \<open>Show 2: the scaled inequality\<close>
  show "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) \<le> integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
  proof -
    have lhs_stretch: "integral ((\<lambda>x. x / (1/(2*pi))) ` {0..1}) (\<lambda>x. (f (1/(2*pi) * x))\<^sup>2)
             = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
      using integral_stretch_real[OF inv_twopi_nz, of 0 1 "\<lambda>x. (f x)\<^sup>2"] by simp
    have lhs_val: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = 2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
      using lhs_stretch img inv_twopi_pos by (simp add: g_unfold)
    have rhs_stretch: "integral ((\<lambda>x. x / (1/(2*pi))) ` {0..1}) (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' (1/(2*pi) * x))\<^sup>2)
             = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2)"
      using integral_stretch_real[OF inv_twopi_nz, of 0 1 "\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2"] by simp
    have factor_out: "integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2) = (1/(2*pi))\<^sup>2 * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      by (simp add: integral_mult_right)
    have "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2)"
      using img rhs_stretch by (simp add: g'_unfold)
    also have "\<dots> = 2*pi * ((1/(2*pi))\<^sup>2 * integral {0..1} (\<lambda>x. (f' x)\<^sup>2))"
      using inv_twopi_pos factor_out by simp
    finally have rhs_val: "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) 
                 = 2*pi * ((1/(2*pi))\<^sup>2 * integral {0..1} (\<lambda>x. (f' x)\<^sup>2))" .
    have rhs_simp: "2*pi * ((1/(2*pi))\<^sup>2 * integral {0..1} (\<lambda>x. (f' x)\<^sup>2))
                  = (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      using twopi_pos by (simp add: power2_eq_square field_simps)
    from W2 lhs_val rhs_val rhs_simp
    have ineq: "2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2) \<le> (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      by linarith
    then have "(2*pi)\<^sup>2 * integral {0..1} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      using twopi_pos by (simp add: power2_eq_square field_simps)
    then show ?thesis
      by (simp add: power_mult_distrib)
  qed
  text \<open>Show 3: the equality case\<close>
  show "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2) \<Longrightarrow>
      \<exists>c a. \<forall>x \<in> {0..1}. f x = c * sin (2*pi*x - a)"
  proof -
    assume eq: "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    have "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
      using img integral_stretch_real[OF inv_twopi_nz, of 0 1 "\<lambda>x. (f x)\<^sup>2"] by (simp add: g_unfold)
    also have "\<dots> = 2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
      using inv_twopi_pos by simp
    finally have lhs: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = 2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2)" .
    have rhs: "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) 
             = (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    proof -
      have "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) 
          = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2)"
        using integral_stretch_real[OF inv_twopi_nz, of 0 1 "\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2"] img 
        by (simp add: g'_unfold)
      also have "\<dots> = (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
        using twopi_pos by (simp add: power2_eq_square field_simps)
      finally show ?thesis .
    qed
    have "(2*pi)\<^sup>2 * integral {0..1} (\<lambda>x. (f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      using eq by (simp add: power_mult_distrib)
    then have "2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2) = (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      using twopi_pos by (simp add: power2_eq_square field_simps)
    then have weq: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2)"
      using lhs rhs by linarith
    from W3[OF weq] obtain c a where ca: "\<forall>x \<in> {0..2*pi}. g x = c * sin (x - a)" by auto
    have "f x = c * sin (2*pi*x - a)" if "x \<in> {0..1}" for x
    proof  -
      have "2*pi*x \<in> {0..2*pi}" using twopi_pos
        using that by auto
      with ca show "f x = c * sin (2*pi*x - a)"
        by (metis g_def nonzero_mult_div_cancel_left twopi_nz)
    qed
    then show "\<exists>c a. \<forall>x \<in> {0..1}. f x = c * sin (2*pi*x - a)" by auto
  qed
qed

section \<open>Part 2: a very special case of Green's theorem for a convex area\<close>

subsection \<open>Area under an arc.\<close>

locale Area =
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex" and u v S
  assumes uv: "u \<le> v"
    and Re_g_le: "Re (g u) \<le> Re (g v)"
    and acont_g: "absolutely_continuous_on {u..v} g"
    and gim: "g ` {u..v} \<subseteq> {z. Im z \<ge> 0}"
    and inj_g: "inj_on g {u..v}"
    and inj_Re: "inj_on Re (g ` {u..v})"
    and negS: "negligible S"
    and gder: "\<And>t. t \<in> {u..v} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"

begin

lemma below_arclet:
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
    and "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
proof -
  obtain h where h: "\<And>x. x \<in> {u..v} \<Longrightarrow> h (Re (g x)) = x"
    by (metis inj_g inj_Re comp_def comp_inj_on inv_into_f_f)
  define ax where "ax \<equiv> (\<lambda>t. Re (g t)) ` {u..v}"
  have cont_h: "continuous_on ax h"
    unfolding ax_def
    by (simp add: absolutely_continuous_on_imp_continuous acont_g continuous_on_Re continuous_on_inv h)
  show "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
  proof -
    have cont_g: "continuous_on {u..v} g"
      by (simp add: absolutely_continuous_on_imp_continuous acont_g)
    have gp_ai: "g' absolutely_integrable_on {u..v}"
      by (meson absolutely_integrable_absolutely_continuous_derivative acont_g gder
          has_vector_derivative_at_within negS)
    have Re_gp_ai: "(\<lambda>t. Re (g' t)) absolutely_integrable_on {u..v}"
      using Re_absolutely_integrable_on gp_ai by blast
    have Im_g_cont: "continuous_on {u..v} (\<lambda>t. Im (g t))"
      by (intro continuous_intros cont_g)
    have Im_g_bdd: "bounded ((\<lambda>t. Im (g t)) ` {u..v})"
      by (intro compact_imp_bounded compact_continuous_image[OF Im_g_cont compact_Icc])
    have Im_g_meas: "(\<lambda>t. Im (g t)) \<in> borel_measurable (lebesgue_on {u..v})"
      using continuous_imp_measurable_on_sets_lebesgue[OF Im_g_cont] atLeastAtMost_borel lborelD
      by (metis sets_completionI_sets)
    show ?thesis
      using absolutely_integrable_bounded_measurable_product_real [OF Im_g_meas _ Im_g_bdd Re_gp_ai]
      by (simp add: mult.commute)
  qed
  have cont_g: "continuous_on {u..v} g"
    using acont_g absolutely_continuous_on_imp_continuous is_interval_cc by blast
  have cont_Reg: "continuous_on {u..v} (\<lambda>t. Re (g t))"
    by (intro continuous_intros cont_g)
  have inj_Reg: "inj_on (\<lambda>t. Re (g t)) {u..v}"
    using comp_inj_on[OF inj_g inj_Re] by (simp add: o_def)
  have ax: "ax = {Re (g u)..Re (g v)}"
  proof (rule antisym)
    show "ax \<subseteq> {Re (g u)..Re (g v)}"
    proof (cases "u = v")
      case False
      with uv 
      have "strict_mono_on {u..v} (\<lambda>t. Re (g t)) \<or> strict_antimono_on {u..v} (\<lambda>t. Re (g t))"
        using injective_eq_monotone_map[OF is_interval_cc cont_Reg] inj_Reg by auto
      with False \<open>u \<le> v\<close> have mono: "strict_mono_on {u..v} (\<lambda>t. Re (g t))"
        by (smt (verit, ccfv_threshold) Re_g_le atLeastAtMost_iff monotone_onD)
      show ?thesis
        using mono by (auto simp: monotone_on_def ax_def less_eq_real_def)
    qed (auto simp: ax_def)
  next
    show "{Re (g u)..Re (g v)} \<subseteq> ax"
      using ivt_increasing_component_on_1[OF uv cont_g, of 1] by (force simp: ax_def)
  qed
  show "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
  proof -
    define f where "f \<equiv> (\<lambda>x. Im (g (h x)))"
    have h_range: "h ` ax \<subseteq> {u..v}"
      using h by (force simp: ax_def)
    have cont_f: "continuous_on ax f"
      using cont_g cont_h continuous_on_Im continuous_on_compose2 f_def h_range by blast
    have f_nonneg: "\<And>x. x \<in> ax \<Longrightarrow> f x \<ge> 0"
      unfolding f_def using gim h_range by blast
    have mono_Reg: "Re (g x) \<le> Re (g y)" if "x \<in> {u..v}" "y \<in> {u..v}" "x \<le> y" for x y
    proof -
      have "strict_mono_on {u..v} (\<lambda>t. Re (g t)) \<or>
            strict_antimono_on {u..v} (\<lambda>t. Re (g t))"
        using injective_eq_monotone_map[OF is_interval_cc cont_Reg] inj_Reg by auto
      with Re_g_le atLeastAtMost_iff leD  order_le_less uv 
      have "mono_on {u..v} (\<lambda>t. Re (g t))"
        unfolding monotone_on_def by metis
      with that show "Re (g x) \<le> Re (g y)" by (auto simp: mono_on_def)
    qed
    have acont_Reg: "absolutely_continuous_on {u..v} (\<lambda>t. Re (g t))"
      using absolutely_continuous_on_compose_linear[OF acont_g bounded_linear_Re[THEN bounded_linear.linear]]
      by (simp add: o_def)
    have deriv_Reg: "\<And>t. t \<in> {u..v} - S \<Longrightarrow> ((\<lambda>t. Re (g t)) has_vector_derivative Re (g' t)) (at t)"
      using bounded_linear_Re[THEN bounded_linear.has_vector_derivative] gder by blast
    \<comment> \<open>Apply substitution: \<integral>_{Re(g u)}^{Re(g v)} f = \<integral>_u^v Re(g') * f(Re(g)) = \<integral>_u^v Re(g') * Im(g)\<close>
    have subst: "((\<lambda>t. Re (g' t) * f (Re (g t))) has_integral (integral {Re (g u)..Re (g v)} f)) {u..v}"
      using has_integral_substitution_ac[OF uv Re_g_le acont_Reg negS deriv_Reg _ mono_Reg] cont_f ax
      using negS by blast
    \<comment> \<open>Since f(Re(g t)) = Im(g t), the LHS simplifies\<close>
    have "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) = integral {Re (g u)..Re (g v)} f"
      using h has_integral_spike[OF negligible_empty _ subst] integral_unique
      by (fastforce simp: f_def)
    \<comment> \<open>Apply area-under-curve: measure of subgraph = \<integral> f\<close>
    also have "\<dots> = measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
    proof -
      \<comment> \<open>First show the subgraph set equals {z. Re(g u) \<le> Re z \<and> Re z \<le> Re(g v) \<and> 0 \<le> Im z \<and> Im z \<le> f(Re z)}\<close>
      have set_eq: "{z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w} =
                    {z. Re (g u) \<le> Re z \<and> Re z \<le> Re (g v) \<and> 0 \<le> Im z \<and> Im z \<le> f (Re z)}" (is "?L=?R")
      proof (intro antisym subsetI)
        fix z assume "z \<in> ?L"
        then obtain w t where wt: "t \<in> {u..v}" "w = g t" "Re w = Re z" "0 \<le> Im z" "Im z \<le> Im w"
          by auto
        have "Re z \<in> ax" unfolding ax_def using wt by force
        then show "z \<in> ?R"
          using f_def h wt ax by fastforce
      next
        fix z assume z: "z \<in> ?R"
        then have Rez: "Re z \<in> ax" using ax by auto
        then show "z \<in> ?L"
          unfolding ax_def using h z by (fastforce simp: f_def)
      qed
      \<comment> \<open>Then apply area-under-curve (Fubini/Cavalieri)\<close>
      show ?thesis unfolding set_eq
        using has_integral_area_under_curve[OF Re_g_le _ _] cont_f f_nonneg ax
        by (metis (no_types, lifting))
    qed
    finally show ?thesis .
  qed
qed

end

subsection \<open>Area above an arc.\<close>

lemma area_above_arclet:
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
  assumes "u \<le> v"
    and Re_g_ge: "Re (g v) \<le> Re (g u)"
    and ac_g: "absolutely_continuous_on {u..v} g"
    and gim: "g ` {u..v} \<subseteq> {z. Im z \<le> 0}"
    and injg: "inj_on g {u..v}"
    and injRe: "inj_on Re (g ` {u..v})"
    and "negligible S"
    and vder_g: "\<And>t. t \<in> {u..v} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
    and "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
proof -
  \<comment> \<open>Symmetry: define h(t) = cnj(g(u+v-t)) and apply area_below_arclet\<close>
  define \<phi> where "\<phi> \<equiv> \<lambda>t. u + v - t"
  define h where "h \<equiv> cnj \<circ> g \<circ> \<phi>"
  define h' where "h' \<equiv> \<lambda>t. - cnj (g' (\<phi> t))"
  interpret Area h h' u v "\<phi> ` S"
  proof
    show "u \<le> v"
      by fact
    show "Re (h u) \<le> Re (h v)"
      by (simp add: \<phi>_def Re_g_ge h_def)
    show "absolutely_continuous_on {u..v} h"
      by (simp add: \<phi>_def absolutely_continuous_on_compose_linear absolutely_continuous_on_reflect assms(3)
          h_def linear_cnj)
    show "h ` {u..v} \<subseteq> {z. 0 \<le> Im z}"
      using gim by (auto simp: h_def \<phi>_def image_subset_iff)
    show "inj_on h {u..v}"
      using injg by (fastforce simp: inj_on_def h_def \<phi>_def)
    show "inj_on Re (h ` {u..v})"
      using injRe by (fastforce simp: inj_on_def h_def \<phi>_def)
    have "\<phi> ` S = (+) (u + v) ` (uminus ` S)"
      unfolding \<phi>_def image_image by (simp add: algebra_simps)
    then show "negligible (\<phi> ` S)"
      by (simp add: \<open>negligible S\<close> linear_uminus negligible_linear_image negligible_translation)
    show "\<And>t. t \<in> {u..v} - (\<phi>`S) \<Longrightarrow> (h has_vector_derivative h' t) (at t)"
      unfolding has_vector_derivative_def h_def h'_def \<phi>_def 
      by (rule vder_g [unfolded has_vector_derivative_def] derivative_eq_intros | force)+
  qed
  have integrand_eq: "\<And>t. Re (h' t) * Im (h t) = Re (g' (\<phi> t)) * Im (g (\<phi> t))"
    unfolding h_def h'_def by (simp add: o_def cnj.sel)
  have integral_eq: "integral {u..v} (\<lambda>t. Re (g' (\<phi> t)) * Im (g (\<phi> t))) =
                     integral {u..v} (\<lambda>t. Re (g' t) * Im (g t))"
  proof -
    define f where "f \<equiv> \<lambda>t. Re (g' t) * Im (g t)"
    have comp_eq: "(f \<circ> (+) (u + v)) \<circ> uminus = f \<circ> \<phi>"
      unfolding \<phi>_def comp_def by (simp add: algebra_simps)
    have "(f \<circ> \<phi>) absolutely_integrable_on {u..v}"
      using below_arclet(1) f_def integrand_eq set_integrable_cong by fastforce
    then have "integral {u..v} (f \<circ> \<phi>) = integral (uminus ` {u..v}) (f \<circ> (+) (u + v))"
      by (subst integral_change_of_variables_linear[OF linear_uminus]) (auto simp: comp_eq)
    also have "\<dots> = integral {u..v} f"
      using integral_shift_Icc_real[of "-v" "-u" f "u+v"] by (simp add: algebra_simps)
    finally show ?thesis 
      by (simp add: f_def comp_def)
  qed
  show "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
  proof -
    have Re_gp_ai: "(\<lambda>t. Re (g' t)) absolutely_integrable_on {u..v}"
      using Re_absolutely_integrable_on has_vector_derivative_at_within assms
      by (metis vder_g absolutely_integrable_absolutely_continuous_derivative)
    have Im_g_cont: "continuous_on {u..v} (\<lambda>t. Im (g t))"
      by (simp add: absolutely_continuous_on_imp_continuous assms(3) continuous_on_Im)
    have Im_g_bdd: "bounded ((\<lambda>t. Im (g t)) ` {u..v})"
      by (intro compact_imp_bounded compact_continuous_image[OF Im_g_cont compact_Icc])
    have Im_g_meas: "(\<lambda>t. Im (g t)) \<in> borel_measurable (lebesgue_on {u..v})"
      using Im_g_cont integrable_continuous_real integrable_imp_measurable by blast
    show ?thesis
      using absolutely_integrable_bounded_measurable_product_real [OF Im_g_meas _ Im_g_bdd Re_gp_ai]
      by (simp add: mult.commute)
  qed
  have measure_eq: "measure lebesgue {z. \<exists>w \<in> h ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w} =
                    measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
  proof -
    have \<phi>_image: "\<phi> ` {u..v} = {u..v}"
      using assms(1) unfolding \<phi>_def by (auto simp: image_iff)
    have h_image: "h ` {u..v} = cnj ` (g ` {u..v})"
      by (metis \<phi>_image h_def image_comp)
    define A where "A \<equiv> {z. \<exists>w \<in> h ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
    define B where "B \<equiv> {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
    have AB: "A = cnj ` B"
      unfolding A_def h_image B_def by (force simp: in_image_cnj_iff)
    have cont_g_uv: "continuous_on {u..v} g"
      using assms(3) absolutely_continuous_on_imp_continuous is_interval_cc by blast
    have "compact B"
    proof -
      \<comment> \<open>B is the continuous image of the compact set {u..v} \<times> {0..1}\<close>
      define \<psi> where "\<psi> \<equiv> \<lambda>(t,s). Complex (Re (g t)) ((1 - s) * Im (g t))"
      have cont_\<psi>: "continuous_on ({u..v} \<times> {0..1}) \<psi>"
        unfolding \<psi>_def split_def
        by (intro continuous_intros continuous_on_compose2[OF continuous_on_Re[OF cont_g_uv]]
            continuous_on_compose2[OF continuous_on_Im[OF cont_g_uv]] continuous_on_fst) auto
      have img: "\<psi> ` ({u..v} \<times> {0..1}) = B"
      proof (rule set_eqI)
        fix z :: complex
        show "z \<in> \<psi> ` ({u..v} \<times> {0..1}) \<longleftrightarrow> z \<in> B"
        proof
          assume "z \<in> \<psi> ` ({u..v} \<times> {0..1})"
          then obtain t s where ts: "t \<in> {u..v}" "s \<in> {0..1}" 
            "z = Complex (Re (g t)) ((1 - s) * Im (g t))"
            unfolding \<psi>_def by auto
          have Im_le: "Im (g t) \<le> 0"
            using assms(4) ts(1) by (auto simp: image_subset_iff)
          have "g t \<in> g ` {u..v}" using ts(1) by auto
          moreover have "Im (g t) \<le> Im z"
            using ts Im_le mult_right_mono_neg by (simp add: mult_le_cancel_right1)
          moreover have "Im z \<le> 0"
            using ts Im_le mult_nonneg_nonpos[of "1-s" "Im (g t)"] by auto
          ultimately show "z \<in> B" unfolding B_def using ts by auto
        next
          assume "z \<in> B"
          then obtain w t where wt: "t \<in> {u..v}" "w = g t" "Re w = Re z" "Im w \<le> Im z" "Im z \<le> 0"
            unfolding B_def by auto
          show "z \<in> \<psi> ` ({u..v} \<times> {0..1})"
          proof (cases "Im (g t) = 0")
            case True
            then show ?thesis 
              using wt by (force simp: image_iff \<psi>_def complex_eq_iff)
          next
            case False
            then have neg: "Im (g t) < 0"
              using wt by force
            define s where "s \<equiv> 1 - Im z / Im (g t)"
            have "0 \<le> Im z / Im (g t)" 
              using wt(5) neg by (simp add: field_simps)
            then have "s \<in> {0..1}" 
              using neg s_def wt(2,4) by force
            moreover have "z = \<psi> (t, s)" unfolding \<psi>_def s_def
              using wt(2,3) False by (simp add: complex_eq_iff field_simps)
            ultimately show ?thesis using wt(1) by auto
          qed
        qed
      qed
      then show ?thesis
        using img compact_continuous_image[OF cont_\<psi>] by (simp add: compact_Times)
    qed
    then have B_meas: "B \<in> lmeasurable" using lmeasurable_compact by blast    
    show ?thesis
      using AB Euclidean_Space_Transfer.measure_linear_image[OF linear_cnj B_meas] det_complex
      by (simp add: A_def B_def)
  qed
  show "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
    using below_arclet(2) integrand_eq integral_eq measure_eq by (simp add: o_def)
qed

subsection \<open>Lemmas for Green's theorem\<close>

definition Green_concl :: "(real \<Rightarrow> complex) \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> bool" where
  "Green_concl g g' \<equiv> (\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {0..1}
    \<and> \<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> = measure lebesgue (inside (path_image g))"

\<comment> \<open>At most 2 points on the frontier of a 2D convex body can share the same
   inner product with a non-zero vector.  Consequence: if three distinct points
   on the frontier have the same Re (or Im), the body must lie on one side.\<close>
lemma frontier_vertical_at_most_two:
  fixes S :: "complex set" and c :: real
  assumes "convex S" "compact S" "interior S \<noteq> {}"
    and sides: "\<exists>p \<in> S. Re p < c" "\<exists>q \<in> S. c < Re q"
    and xyz: "x \<in> frontier S" "y \<in> frontier S" "z \<in> frontier S"
      "Re x = c" "Re y = c" "Re z = c"
  shows "\<not> (x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z)"
proof -
  define T where "T \<equiv> {w :: complex. 1 \<bullet> w = c}"
  have aff_T: "affine T" unfolding T_def by (rule affine_hyperplane)
  have T_eq: "T = {w. Re w = c}" unfolding T_def by (simp add: complex_inner_1)
  have xT: "x \<in> T" "y \<in> T" "z \<in> T"
    using xyz unfolding T_eq by auto
  \<comment> \<open>The interior of S intersects T\<close>
  have int_T: "interior S \<inter> T \<noteq> {}"
  proof -
    have cl: "closed S" using assms(2) compact_imp_closed by blast
    have cl_int: "closure (interior S) = S"
      using convex_closure_interior[OF assms(1) assms(3)] cl
      by (simp add: closure_closed)
    \<comment> \<open>Find interior points on each side of Re = c\<close>
    obtain p where p: "p \<in> interior S" "Re p < c"
    proof -
      obtain p0 where p0: "p0 \<in> S" "Re p0 < c" using sides(1) by auto
      then have "p0 \<in> closure (interior S)" using cl_int by simp
      then obtain ps where ps: "\<forall>n. ps n \<in> interior S" "ps \<longlonglongrightarrow> p0"
        by (meson closure_sequential)
      have "(\<lambda>n. Re (ps n)) \<longlonglongrightarrow> Re p0" by (rule tendsto_Re[OF ps(2)])
      from order_tendstoD(2)[OF this p0(2)]
      obtain n where "Re (ps n) < c" using eventually_sequentially by auto
      then show thesis using that ps(1) by auto
    qed
    obtain q where q: "q \<in> interior S" "c < Re q"
    proof -
      obtain q0 where q0: "q0 \<in> S" "c < Re q0" using sides(2) by auto
      then have "q0 \<in> closure (interior S)" using cl_int by simp
      then obtain qs where qs: "\<forall>n. qs n \<in> interior S" "qs \<longlonglongrightarrow> q0"
        by (meson closure_sequential)
      have "(\<lambda>n. Re (qs n)) \<longlonglongrightarrow> Re q0" by (rule tendsto_Re[OF qs(2)])
      from order_tendstoD(1)[OF this q0(2)]
      obtain n where "c < Re (qs n)" using eventually_sequentially by auto
      then show thesis using that qs(1) by auto
    qed
    \<comment> \<open>IVT on the segment [p,q] \<subseteq> interior S\<close>
    have conv_int: "convex (interior S)" using convex_interior assms(1) by auto
    then have seg_sub: "closed_segment p q \<subseteq> interior S"
      using closed_segment_subset p(1) q(1) by auto
    obtain r where "r \<in> closed_segment p q" "Re r = c"
    proof -
      have "1 \<bullet> p \<le> c" using p(2) by (simp add: complex_inner_1)
      moreover have "c \<le> 1 \<bullet> q" using q(2) by (simp add: complex_inner_1)
      moreover have "p \<in> closed_segment p q" "q \<in> closed_segment p q"
        by (auto simp: ends_in_segment)
      ultimately obtain r where "r \<in> closed_segment p q" "1 \<bullet> r = c"
        using connected_ivt_hyperplane[OF connected_segment] by blast
      then show thesis using that by (simp add: complex_inner_1)
    qed
    then have "r \<in> interior S \<inter> T" using seg_sub T_eq by auto
    then show ?thesis by auto
  qed

  \<comment> \<open>Apply convex_affine_rel_frontier_Int\<close>
  have rf_eq: "rel_frontier (S \<inter> T) = frontier S \<inter> T"
    using convex_affine_rel_frontier_Int[OF assms(1) aff_T int_T] .
  \<comment> \<open>S \<inter> T is a compact convex collinear set, hence a closed segment\<close>
  have ST_ne: "S \<inter> T \<noteq> {}"
    using int_T interior_subset by blast
  have ST_compact: "compact (S \<inter> T)"
  proof -
    have "closed T" unfolding T_def by (rule closed_hyperplane)
    then show ?thesis using assms(2) compact_Int_closed by auto
  qed
  have ST_convex: "convex (S \<inter> T)"
    using assms(1) convex_Int aff_T affine_imp_convex by auto
  have ST_collinear: "collinear (S \<inter> T)"
  proof -
    have "aff_dim T = int (DIM(complex) - 1)"
      unfolding T_def by (rule aff_dim_hyperplane) simp
    then have "aff_dim T = 1" by simp
    moreover have "aff_dim (S \<inter> T) \<le> aff_dim T"
      by (rule aff_dim_subset) auto
    ultimately have "aff_dim (S \<inter> T) \<le> 1" by linarith
    then show ?thesis using collinear_aff_dim by auto
  qed
  obtain p q where pq: "S \<inter> T = closed_segment p q"
    using compact_convex_collinear_segment[OF ST_ne ST_compact ST_convex ST_collinear] by auto
  \<comment> \<open>The rel_frontier of a closed segment has at most 2 elements\<close>
  have rf_sub: "rel_frontier (S \<inter> T) \<subseteq> {p, q}"
  proof (cases "p = q")
    case True
    then show ?thesis unfolding pq by (simp add: rel_frontier_sing)
  next
    case False
    have "rel_frontier (closed_segment p q) = closed_segment p q - rel_interior (closed_segment p q)"
      unfolding rel_frontier_def by (simp add: closure_closed_segment)
    also have "\<dots> = closed_segment p q - open_segment p q"
      using rel_interior_closed_segment[of p q] False by simp
    also have "\<dots> = {p, q}"
    proof -
      have "closed_segment p q = open_segment p q \<union> {p, q}"
        by (rule closed_segment_eq_open)
      moreover have "p \<notin> open_segment p q" "q \<notin> open_segment p q"
        by (simp_all add: open_segment_def)
      ultimately show ?thesis by auto
    qed
    finally show ?thesis using pq by simp
  qed
  \<comment> \<open>x, y, z are all in rel_frontier (S \<inter> T) = frontier S \<inter> T \<subseteq> {p, q}\<close>
  have "x \<in> {p, q}" "y \<in> {p, q}" "z \<in> {p, q}"
    using xyz(1,2,3) xT rf_eq rf_sub by auto
  then show ?thesis by auto
qed


locale Green =
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
    and U :: "real set"
    and a b :: "complex"
  assumes g: "simple_path g" "pathstart g = a" "pathfinish g = a"
    and b: "b \<in> path_image g" "Re a < Re b" "Im a = Im b"
    and dab: "dist a b = diameter (path_image g)"
    and conv: "convex (inside (path_image g))"
    and cont: "absolutely_continuous_on {0..1} g"
    and U: "negligible U"
    and vder: "\<And>t. t \<in> {0..1} - U \<Longrightarrow> (g has_vector_derivative g' t) (at t)"

begin

definition "gop \<equiv> cnj \<circ> reversepath g"
definition "gop' \<equiv> uminus \<circ> cnj \<circ> reversepath g'"

lemma cnj_rev: "Green gop gop' ((\<lambda>t. 1-t) ` U) (cnj a) (cnj b)"
proof
  show "simple_path gop"
    using g by (simp add: simple_path_def gop_def loop_free_reversepath loop_free_cnj)
  show "pathstart gop = cnj a"
    using g by (simp add: gop_def pathstart_compose)
  show "pathfinish gop = cnj a"
    using g by (simp add: gop_def pathfinish_compose)
  show "cnj b \<in> path_image gop"
    using b by (simp add: gop_def path_image_compose)
  show "Re (cnj a) < Re (cnj b)" "Im (cnj a) = Im (cnj b)"
    using b by auto
  show "dist (cnj a) (cnj b) = diameter (path_image gop)"
    by (simp add: gop_def dab diameter_image_cnj path_image_compose flip: dab)
  show "convex (inside (path_image gop))"
    unfolding gop_def
    by (metis conv convex_linear_vimage image_cnj_conv_vimage_cnj 
        inside_cnj_image linear_cnj path_image_compose path_image_reversepath)
  show "absolutely_continuous_on {0..1} gop"
    using cont unfolding gop_def
    by (simp add: absolutely_continuous_on_compose_linear absolutely_continuous_on_reflect linear_cnj
        reversepath_o)
  have "negligible (uminus ` U)"
    by (simp add: U linear_uminus negligible_linear_image_eq)
  then have "negligible (((+)1) ` uminus ` U)"
    using negligible_translation by blast
  then show "negligible ((-) 1 ` U)"
    by (smt (verit, best) image_cong image_image)
next
  fix t :: real
  note vder [unfolded has_vector_derivative_def, derivative_intros]
  assume "t \<in> {0..1} - (-) 1 ` U"
  then have "0 \<le> t" "t \<le> 1" "1-t \<notin> U"
    by (auto simp: image_iff)
  then show "(gop has_vector_derivative gop' t) (at t)"
    unfolding gop_def gop'_def has_vector_derivative_def reversepath_o
    by - (rule derivative_eq_intros | simp add: o_def | assumption)+
qed

lemma rev: "Green (reversepath g) (uminus \<circ> reversepath g') ((\<lambda>t. 1-t) ` U) a b"
proof
  show "simple_path (reversepath g)"
    using g by (simp add: simple_path_def loop_free_reversepath)
  show "pathstart (reversepath g) = a"
    using g by (simp add: pathstart_compose)
  show "pathfinish (reversepath g) = a"
    using g by (simp add: pathfinish_compose)
  show "b \<in> path_image (reversepath g)"
    using b by (simp add: path_image_compose)
  show "Re a < Re b" "Im a = Im b"
    using b by auto
  show "dist a b = diameter (path_image (reversepath g))"
    by (simp add: gop_def dab path_image_compose flip: dab)
  show "convex (inside (path_image (reversepath g)))"
    unfolding gop_def
    by (metis conv convex_linear_vimage image_cnj_conv_vimage_cnj 
        inside_cnj_image linear_cnj path_image_compose path_image_reversepath)
  show "absolutely_continuous_on {0..1} (reversepath g)"
    using cont unfolding gop_def
    by (simp add: absolutely_continuous_on_compose_linear absolutely_continuous_on_reflect linear_cnj
        reversepath_o)
  have "negligible (uminus ` U)"
    by (simp add: U linear_uminus negligible_linear_image_eq)
  then have "negligible (((+)1) ` uminus ` U)"
    using negligible_translation by blast
  then show "negligible ((-) 1 ` U)"
    by (smt (verit, best) image_cong image_image)
next
  fix t :: real
  note vder [unfolded has_vector_derivative_def, derivative_intros]
  assume "t \<in> {0..1} - (-) 1 ` U"
  then have "0 \<le> t" "t \<le> 1" "1-t \<notin> U"
    by (auto simp: image_iff)
  then show "((reversepath g) has_vector_derivative (uminus \<circ> reversepath g') t) (at t)"
    unfolding gop_def gop'_def has_vector_derivative_def reversepath_o
    by - (rule derivative_eq_intros | simp add: o_def | assumption)+
qed


lemma f_abs_int: "(\<lambda>s. Re (g' s) * Im (g s)) absolutely_integrable_on {0..1}"
proof -
  have cont_g: "continuous_on {0..1} g"
    using simple_path_imp_path[OF g(1)] by (simp add: path_def)
  have Im_g_cont: "continuous_on {0..1} (\<lambda>t. Im (g t))"
    by (intro continuous_intros cont_g)
  have Im_g_bdd: "bounded ((\<lambda>t. Im (g t)) ` {0..1})"
    by (intro compact_imp_bounded compact_continuous_image[OF Im_g_cont compact_Icc])
  have Im_g_meas: "(\<lambda>t. Im (g t)) \<in> borel_measurable (lebesgue_on {0..1})"
    using continuous_imp_measurable_on_sets_lebesgue[OF Im_g_cont]
      atLeastAtMost_borel lborelD
    by (metis sets_completionI_sets)
  have gp_ai: "g' absolutely_integrable_on {0..1}"
    using absolutely_integrable_absolutely_continuous_derivative[OF cont U]
      vder has_vector_derivative_at_within by blast
  then show ?thesis
    using absolutely_integrable_bounded_measurable_product_real[OF Im_g_meas _ Im_g_bdd Re_absolutely_integrable_on]
    by (simp add: mult.commute)
qed

lemma arc_inj_on: "inj_on g {u..v}"
  if huv: "0 \<le> u" "v \<le> 1" "u < v" and hne: "u > 0 \<or> v < 1" 
proof (rule inj_onI)
  fix s1 s2 assume s1: "s1 \<in> {u..v}" and s2: "s2 \<in> {u..v}" and eq: "g s1 = g s2"
  have s1_01: "s1 \<in> {0..1}" using s1 huv by auto
  have s2_01: "s2 \<in> {0..1}" using s2 huv by auto
  show "s1 = s2"
  proof (rule ccontr)
    assume neq: "s1 \<noteq> s2"
    from g(1) have lf: "loop_free g" by (simp add: simple_path_def)
    have "s1 = s2 \<or> s1 = 0 \<and> s2 = 1 \<or> s1 = 1 \<and> s2 = 0"
      using eq lf loop_free_def s1_01 s2_01 by blast
    with neq show False using s1 s2 huv hne by auto
  qed
qed

lemma arc_Re_inj_on: "inj_on Re (g ` {u..v})"
  if hinj: "inj_on g {u..v}"
    and hRe: "\<And>s1 s2. \<lbrakk>s1 \<in> {u..v}; s2 \<in> {u..v}; Re (g s1) = Re (g s2); s1 \<noteq> s2\<rbrakk>
               \<Longrightarrow> Re (g u) = Re (g v)"
    and hne: "Re (g u) \<noteq> Re (g v)"
proof (rule inj_onI)
  fix x y assume "x \<in> g ` {u..v}" "y \<in> g ` {u..v}" "Re x = Re y"
  then obtain s1 s2 where s1: "s1 \<in> {u..v}" "x = g s1"
    and s2: "s2 \<in> {u..v}" "y = g s2" by auto
  then have Re_eq: "Re (g s1) = Re (g s2)" using \<open>Re x = Re y\<close> by simp
  show "x = y"
  proof (cases "s1 = s2")
    case True then show ?thesis using s1 s2 by simp
  next
    case False
    then have "Re (g u) = Re (g v)" using hRe[OF s1(1) s2(1) Re_eq] by auto
    then show ?thesis using hne by simp
  qed
qed

lemma Re_inj_upper_gen: 
  assumes s1t: "s1 \<in> {0..t}" and s2t: "s2 \<in> {0..t}"
    and Re_eq: "Re (g s1) = Re (g s2)" and neq: "s1 \<noteq> s2"
    and geq0: "g 0 = 0" "g 1 = 0"
    and ht: "0 < t" "t < 1" "g t = b"
  shows "(s1 = 0 \<and> s2 = t) \<or> (s1 = t \<and> s2 = 0)"
proof (rule ccontr)
  assume not_endpts: "\<not> ((s1 = 0 \<and> s2 = t) \<or> (s1 = t \<and> s2 = 0))"
    \<comment> \<open>Define S = convex hull (path_image g). This is the right set for
       frontier_vertical_at_most_two.\<close>
  define S where "S \<equiv> convex hull (path_image g)"
  have S_convex: "convex S" unfolding S_def by (rule convex_convex_hull)
  have S_compact: "compact S" unfolding S_def
    using compact_simple_path_image[OF g(1)] compact_convex_hull by auto
  have frontier_S: "frontier S = path_image g"
    unfolding S_def using frontier_convex_hull_eq_path_image[OF g(1) _ conv] g(2,3) by auto
  have S_int_ne: "interior S \<noteq> {}"
  proof -
    have "inside (path_image g) \<noteq> {}"
      using Jordan_inside_outside[OF g(1)] g(2,3) by auto
    moreover have "closure (inside (path_image g)) = S"
      unfolding S_def using convex_hull_eq_closure_inside[OF g(1) _ conv] g(2,3) by auto
    moreover have "interior (closure (inside (path_image g))) = inside (path_image g)"
      using convex_interior_closure[OF conv] interior_open
      using Jordan_inside_outside[OF g(1)] g(2,3) by auto
    ultimately show ?thesis by auto
  qed
    \<comment> \<open>Step 1: At least one of s1, s2 is in the open interval (0,t).\<close>
  have interior_param: "s1 \<in> {0<..<t} \<or> s2 \<in> {0<..<t}"
    using s1t s2t neq not_endpts by auto
      \<comment> \<open>Step 2: g s1 \<noteq> g s2 (from injectivity of g on {0..t}, which is a proper sub-arc).\<close>
  have inj_sub: "inj_on g {0..t}"
    using arc_inj_on[of 0 t] ht by auto
  have g_neq: "g s1 \<noteq> g s2"
    by (meson neq inj_on_def inj_sub s1t s2t)
    \<comment> \<open>Step 3: Both g s1 and g s2 are on frontier S = path_image g.\<close>
  have s1_01: "s1 \<in> {0..1}" using s1t ht(2) by auto
  have s2_01: "s2 \<in> {0..1}" using s2t ht(2) by auto
  have gs1_frontier: "g s1 \<in> frontier S"
    using frontier_S s1_01 by (auto simp: path_image_def)
  have gs2_frontier: "g s2 \<in> frontier S"
    using frontier_S s2_01 by (auto simp: path_image_def)
      \<comment> \<open>Step 4: Find a third distinct point on frontier S with the same Re-value.
       Key insight: one of g(0)=0 or g(t)=b has a DIFFERENT parameter from s1 and s2,
       and since g is injective on {0..t}, it gives a distinct POINT.
       But we need it to have the SAME Re-value — that's only possible if Re(g s1) \<in> {0, Re b}.
       If Re(g s1) = 0 then g s1 = g 0 (since Re(g 0) = 0) — but then s1 = 0 by injectivity.
       Similarly if Re(g s1) = Re b then s1 = t.
       So in fact, we need a different approach: the third point comes from the OTHER arc [t,1].
       On the other arc, g goes from b back to 0, so Re goes from Re b back to 0.
       By IVT (since g is continuous), for any c \<in> (0, Re b), there exists s3 \<in> [t,1] with
       Re(g s3) = c. This s3 gives a third point on frontier S.\<close>
  define c where "c \<equiv> Re (g s1)"
    \<comment> \<open>Step 4a: Show c \<in> {0, Re b} forces s1 or s2 to an endpoint, contradicting not_endpts.\<close>
  have c_strict: "0 < c \<and> c < Re b"
  proof -
    have a0: "a = 0" using geq0(1) g(2) by (simp add: pathstart_def)
    have Imb: "Im b = 0" using b(3) a0 by simp
    have Reb: "Re b > 0" using b(2) a0 by simp
    have bdd: "bounded (path_image g)"
      using compact_simple_path_image[OF g(1)] compact_imp_bounded by blast
    have gs1_pi: "g s1 \<in> path_image g" using s1_01 by (auto simp: path_image_def)
    have gs2_pi: "g s2 \<in> path_image g" using s2_01 by (auto simp: path_image_def)
    have g0_pi: "0 \<in> path_image g" using geq0(1) by (metis pathstart_def pathstart_in_path_image)
    have diam_eq: "dist 0 b = diameter (path_image g)" using dab a0 by simp
    have dist_0b: "dist 0 b = Re b"
      using Imb Reb cmod_eq_Re by auto
    \<comment> \<open>Every point on the curve is within distance Re b of both 0 and b\<close>
    have d1: "dist (g s1) b \<le> Re b"
      using diameter_bounded_bound[OF bdd gs1_pi b(1)] diam_eq dist_0b by simp
    have d2: "dist 0 (g s1) \<le> Re b"
      using diameter_bounded_bound[OF bdd g0_pi gs1_pi] diam_eq dist_0b by simp
    \<comment> \<open>Helper: from cmod z \<le> Re b, derive (Re z)² + (Im z)² \<le> (Re b)²\<close>
    have cmod_sq: "(Re z)\<^sup>2 + (Im z)\<^sup>2 \<le> (Re b)\<^sup>2" if "cmod z \<le> Re b" for z
      by (metis cmod_power2 norm_ge_zero power_mono that)
    \<comment> \<open>Helper: from cmod (z - b) \<le> Re b, derive (Re z - Re b)² + (Im z)² \<le> (Re b)²\<close>
    have cmod_sq_b: "(Re z - Re b)\<^sup>2 + (Im z)\<^sup>2 \<le> (Re b)\<^sup>2" if "cmod (z - b) \<le> Re b" for z
      using Imb cmod_sq that by force
    \<comment> \<open>Helper: injectivity gives s = 0 from g s = 0, and s = t from g s = b\<close>
    have eq_0: "s = 0" if "g s = 0" "s \<in> {0..t}" for s
      using geq0(1) inj_onD inj_sub that by fastforce
    have eq_t: "s = t" if "g s = b" "s \<in> {0..t}" for s
      using ht(3) inj_on_contraD inj_sub that by fastforce
    \<comment> \<open>Case c = 0: Re(g s1) = 0, dist(g s1, b) \<le> Re b forces Im(g s1) = 0, so g s1 = 0\<close>
    have "c \<noteq> 0"
    proof
      assume "c = 0"
      then have Re0: "Re (g s1) = 0" unfolding c_def by simp
      have "(Re (g s1) - Re b)\<^sup>2 + (Im (g s1))\<^sup>2 \<le> (Re b)\<^sup>2"
        using cmod_sq_b d1 by (simp add: dist_norm)
      then have "(Im (g s1))\<^sup>2 \<le> 0" using Re0 by (simp add: power2_eq_square)
      then have "g s1 = 0" using Re0 by (auto simp: complex_eq_iff)
      then have "s1 = 0" using eq_0 s1t by simp
      moreover have "Re (g s2) = 0" using Re_eq \<open>c = 0\<close> c_def by simp
      then have "(Re (g s2) - Re b)\<^sup>2 + (Im (g s2))\<^sup>2 \<le> (Re b)\<^sup>2"
        using cmod_sq_b[of "g s2"] diameter_bounded_bound[OF bdd gs2_pi b(1)]
          diam_eq dist_0b by (simp add: dist_norm)
      then have "(Im (g s2))\<^sup>2 \<le> 0" using \<open>Re (g s2) = 0\<close> by (simp add: power2_eq_square)
      then have "g s2 = 0" using \<open>Re (g s2) = 0\<close> by (auto simp: complex_eq_iff)
      then have "s2 = 0" using eq_0 s2t by simp
      ultimately show False using neq by simp
    qed
    \<comment> \<open>Case c = Re b: dist(0, g s1) \<le> Re b forces Im(g s1) = 0, so g s1 = b\<close>
    moreover have "c \<noteq> Re b"
    proof
      assume "c = Re b"
      then have ReB: "Re (g s1) = Re b" unfolding c_def by simp
      have "(Re (g s1))\<^sup>2 + (Im (g s1))\<^sup>2 \<le> (Re b)\<^sup>2"
        using cmod_sq d2 by (simp add: dist_norm)
      then have "(Im (g s1))\<^sup>2 \<le> 0" using ReB by (simp add: power2_eq_square)
      then have "g s1 = b" using ReB Imb by (auto simp: complex_eq_iff)
      then have "s1 = t" using eq_t s1t by simp
      moreover have "Re (g s2) = Re b" using Re_eq \<open>c = Re b\<close> c_def by simp
      then have "(Re (g s2))\<^sup>2 + (Im (g s2))\<^sup>2 \<le> (Re b)\<^sup>2"
        using cmod_sq[of "g s2"] diameter_bounded_bound[OF bdd g0_pi gs2_pi]
          diam_eq dist_0b by (simp add: dist_norm)
      then have "(Im (g s2))\<^sup>2 \<le> 0" using \<open>Re (g s2) = Re b\<close> by (simp add: power2_eq_square)
      then have "g s2 = b" using \<open>Re (g s2) = Re b\<close> Imb by (auto simp: complex_eq_iff)
      then have "s2 = t" using eq_t s2t by simp
      ultimately show False using neq by simp
    qed
    \<comment> \<open>c is bounded: 0 \<le> c \<le> Re b from diameter bound\<close>
    moreover have "0 \<le> c"
    proof -
      \<comment> \<open>From dist(g s1, b) \<le> Re b: |Re(g s1) - Re b| \<le> cmod(g s1 - b) \<le> Re b\<close>
      have "\<bar>Re (g s1) - Re b\<bar> \<le> cmod (g s1 - b)"
        using abs_Re_le_cmod[of "g s1 - b"] by simp
      also have "\<dots> \<le> Re b" using d1 by (simp add: dist_norm)
      finally show ?thesis unfolding c_def by linarith
    qed
    moreover have "c \<le> Re b"
      by (smt (verit) c_def complex_Re_le_cmod d2 dist_0_norm)
    ultimately show ?thesis by linarith
  qed
      \<comment> \<open>Step 4b: By IVT on [t,1], find s3 with Re(g s3) = c.\<close>
  have cont_Re_g: "continuous_on {t..1} (Re \<circ> g)"
    using absolutely_continuous_on_imp_continuous assms(2) cont continuous_on_Re
      continuous_on_eq continuous_on_subset by fastforce
  obtain s3 where s3: "s3 \<in> {t..1}" "Re (g s3) = c"
  proof -
    have img_conn: "connected ((Re \<circ> g) ` {t..1})"
      by (intro connected_continuous_image cont_Re_g connected_Icc)
    then have img_iv: "is_interval ((Re \<circ> g) ` {t..1})"
      using is_interval_connected_1 by auto
    have "Re (g t) \<in> (Re \<circ> g) ` {t..1}" using ht(1,2) by (auto simp: image_def)
    then have Regt_in: "Re b \<in> (Re \<circ> g) ` {t..1}" using ht(3) by simp
    have "Re (g 1) \<in> (Re \<circ> g) ` {t..1}" using ht(2) by (auto simp: image_def)
    then have Re0_in: "0 \<in> (Re \<circ> g) ` {t..1}" using geq0 by simp
    have "c \<in> (Re \<circ> g) ` {t..1}"
      using img_iv[unfolded is_interval_1] Regt_in Re0_in c_strict by auto
    then show ?thesis using that by (auto simp: image_def)
  qed
    \<comment> \<open>Step 4c: g s3 is on frontier S and distinct from g s1 and g s2.\<close>
  have s3_01: "s3 \<in> {0..1}" using s3(1) ht(1) by auto
  have loopfr_g: "loop_free g" using g by (simp add: simple_path_def)
  have gs3_frontier: "g s3 \<in> frontier S"
    using frontier_S s3_01 by (auto simp: path_image_def)
  have gs3_ne_gs1: "g s3 \<noteq> g s1"
  proof
    assume eq: "g s3 = g s1"
    with loopfr_g have "s3 = s1 \<or> s3 = 0 \<and> s1 = 1 \<or> s3 = 1 \<and> s1 = 0"
      using eq loop_free_def s1_01 s3_01 by blast
    then show False
      using assms(1) c_def c_strict eq geq0(2) ht(3) s3(1) by auto
  qed
  have gs3_ne_gs2: "g s3 \<noteq> g s2"
  proof
    assume eq: "g s3 = g s2"
    with loopfr_g have "s3 = s2 \<or> s3 = 0 \<and> s2 = 1 \<or> s3 = 1 \<and> s2 = 0"
      using eq loop_free_def s2_01 s3_01 by blast
    then show False
      using assms(2) c_strict geq0(2) ht(3) s3(1,2) by fastforce
  qed
    \<comment> \<open>Step 5: The "sides" condition for frontier_vertical_at_most_two.\<close>
  have side_left: "\<exists>p \<in> S. Re p < c"
    by (metis S_def assms(5) c_strict hull_inc pathstart_def pathstart_in_path_image
        zero_complex.sel(1))
  have side_right: "\<exists>q \<in> S. c < Re q"
    by (metis S_def b(1) c_strict hull_inc)
    \<comment> \<open>Step 6: Apply frontier_vertical_at_most_two for the contradiction.\<close>
  have three_distinct: "g s1 \<noteq> g s2 \<and> g s1 \<noteq> g s3 \<and> g s2 \<noteq> g s3"
    using g_neq gs3_ne_gs1 gs3_ne_gs2 by auto
  have Re_all_c: "Re (g s1) = c" "Re (g s2) = c" "Re (g s3) = c"
    unfolding c_def using Re_eq s3(2) c_def by auto
  have "\<not> (g s1 \<noteq> g s2 \<and> g s1 \<noteq> g s3 \<and> g s2 \<noteq> g s3)"
    using frontier_vertical_at_most_two[OF S_convex S_compact S_int_ne side_left side_right
        gs1_frontier gs2_frontier gs3_frontier Re_all_c] .
  then show False using three_distinct by auto
qed

lemma not_all_above:
  assumes Reb: "Re b > 0"
  assumes "a = 0"
  assumes real_on_curve: "\<And>z. z \<in> path_image g \<Longrightarrow> Im z = 0 \<Longrightarrow> z = 0 \<or> z = b"
  shows "\<not> (path_image g \<subseteq> {z. 0 \<le> Im z})"
proof -
  have seg_infinite: "\<not> finite (open_segment a b)"
    using Reb assms by force
  have Im_b: "Im b = 0" using b(3) assms by simp
  have seg_Im0: "open_segment a b \<subseteq> {z. Im z = 0}"
    using assms Im_b by (auto simp: in_segment complex_eq_iff)
  have seg_in_closure: "open_segment a b \<subseteq> closure (inside (path_image g))"
    by (metis b(1) conv convex_contains_open_segment convex_convex_hull convex_hull_eq_closure_inside
        g hull_inc pathfinish_in_path_image)
  have frontier_eq: "frontier (inside (path_image g)) = path_image g"
    using Jordan_inside_outside g by blast

  show ?thesis
  proof
    assume above: "path_image g \<subseteq> {z. 0 \<le> Im z}"
    then have hull_above: "convex hull (path_image g) \<subseteq> {z. 0 \<le> Im z}"
      by (intro hull_minimal convex_halfspace_Im_ge)
    then have inside_above: "inside (path_image g) \<subseteq> {z. 0 < Im z}"
    proof -
      have sub: "inside (path_image g) \<subseteq> {z. (0::real) \<le> \<i> \<bullet> z}"
        using hull_above  closure_subset
        using conv convex_hull_eq_closure_inside g by auto
      then have "inside (path_image g) \<subseteq> interior {z. (0::real) \<le> \<i> \<bullet> z}"
        using interior_maximal open_inside Jordan_inside_outside g by blast
      also have "\<dots> = {z. 0 < \<i> \<bullet> z}"
        by (rule interior_halfspace_ge) simp
      finally show ?thesis by (simp add: complex_inner_i_right)
    qed
    have "open_segment a b \<subseteq> path_image g"
      using frontier_def frontier_eq inside_above interior_open open_inside seg_Im0 seg_in_closure
      by (smt (verit, best) DiffI Jordan_inside_outside g mem_Collect_eq subset_eq)
    then have "open_segment a b \<subseteq> {z \<in> path_image g. Im z = 0}"
      using seg_Im0 by auto
    also have "\<dots> \<subseteq> {0, b}"
      using real_on_curve by blast
    finally show False using seg_infinite finite_subset by blast
  qed
qed

end


context Green
begin

interpretation CR: Green gop gop' "(\<lambda>t. 1-t) ` U" "cnj a" "cnj b"
  by (rule cnj_rev)

lemma Green_area_zero_A:
  assumes "a = 0" 
    and t: "0 < t" "t < 1"
    and hgt: "g t = b"
    and above: "g ` {0..t} \<subseteq> {z. 0 \<le> Im z}"
    and below: "g ` {t..1} \<subseteq> {z. Im z \<le> 0}"
  shows "Green_concl g g'"
proof -
  \<comment> \<open>Common facts used by both split_case and split_case'\<close>
  have g0: "g 0 = 0" using assms g(2) by (simp add: pathstart_def)
  have g1: "g 1 = 0" using assms g(3) by (simp add: pathfinish_def)
  have lfg: "loop_free g" using g by (simp add: simple_path_def)
  have Reb: "Re b > 0" using b(2) assms by simp
  have Imb: "Im b = 0" using b(3) assms by simp
    \<comment> \<open>Re-injectivity: on each arc, Re \<circ> g is injective (except at endpoints).
       Otherwise frontier_vertical_at_most_two gives a contradiction via 3 points
       on frontier(closure(inside)) with the same Re-value.\<close>
  have Re_inj_upper: "\<lbrakk>s1 \<in> {0..t}; s2 \<in> {0..t}; Re (g s1) = Re (g s2); s1 \<noteq> s2\<rbrakk>
        \<Longrightarrow> (s1 = 0 \<and> s2 = t) \<or> (s1 = t \<and> s2 = 0)" for s1 s2
    using Re_inj_upper_gen g0 g1 using hgt t by presburger
  have Re_inj_lower: "\<lbrakk>s1 \<in> {t..1}; s2 \<in> {t..1}; Re (g s1) = Re (g s2); s1 \<noteq> s2\<rbrakk>
        \<Longrightarrow> (s1 = t \<and> s2 = 1) \<or> (s1 = 1 \<and> s2 = t)" for s1 s2
    using CR.Re_inj_upper_gen[of "1-s1" "1-t" "1-s2"] hgt t using g g0 g1 assms
    by (auto simp add: gop_def reversepath_def)
      \<comment> \<open>Step 0: Absolute integrability (needed for integral splitting)\<close>
  define f where "f \<equiv> \<lambda>s. Re (g' s) * Im (g s)"
  have f_int: "f integrable_on {0..1}"
    using set_lebesgue_integral_eq_integral(1)[OF f_abs_int] f_def by argo
      \<comment> \<open>Step 1: The integral splits over [0,t] and [t,1]\<close>
  have split_int: "integral {0..1} f = integral {0..t} f + integral {t..1} f"
    using Henstock_Kurzweil_Integration.integral_combine[of 0 t 1 f] t f_int by auto
      \<comment> \<open>Step 2: Upper arc integral \<ge> 0.
       By change of variables x = Re(g(s)) and Re-injectivity, the integral
       \<integral>₀ᵗ Re(g') \<sqdot> Im(g) ds = \<integral>₀^{Re b} f_upper(x) dx \<ge> 0
       since f_upper = Im \<circ> g \<circ> Re⁻¹ \<ge> 0 on the upper arc.\<close>
  have upper_int: "integral {0..t} f \<ge> 0"
  proof -
    interpret Area g g' 0 t U
    proof
      show "Re (g 0) \<le> Re (g t)" 
        using g0 hgt Reb by simp
      show "absolutely_continuous_on {0..t} g"
        using absolutely_continuous_on_subset[OF cont] t by auto
      show "inj_on g {0..t}"
        using arc_inj_on t less_eq_real_def by presburger
      then show "inj_on Re (g ` {0..t})"
        using Reb Re_inj_upper g0 t
        by (intro arc_Re_inj_on; fastforce simp: assms b(2))
    qed (use above U vder t in auto)
    show ?thesis
      unfolding f_def using below_arclet(2) by auto
  qed
    \<comment> \<open>Step 3: Lower arc integral \<ge> 0 as well.
       On [t,1], g goes from b back to 0 (Re decreasing) with Im(g) \<le> 0.
       By change of variables x = Re(g(s)):
       \<integral>ₜ¹ Re(g')\<sqdot>Im(g) ds = \<integral>_{Re b}^0 f_lower(x) dx = -\<integral>₀^{Re b} f_lower(x) dx \<ge> 0
       since f_lower \<le> 0.\<close>
  have lower_int: "integral {t..1} f \<ge> 0"
  proof -
    have t_le1: "t \<le> 1" using t(2) by linarith
    have Re_le': "Re (g 1) \<le> Re (g t)" using g1 hgt Reb by simp
    have ac_sub': "absolutely_continuous_on {t..1} g"
      using absolutely_continuous_on_subset[OF cont] t by auto
    have inj_g_lower: "inj_on g {t..1}"
      using arc_inj_on t(2) less_eq_real_def t by presburger
    then have inj_Re_lower: "inj_on Re (g ` {t..1})"
      using Reb Re_inj_lower g1 t
      by (intro arc_Re_inj_on; fastforce simp: assms b(2))
    have vder_sub': "\<And>s. s \<in> {t..1} - U \<Longrightarrow> (g has_vector_derivative g' s) (at s)"
      using vder t(1) by auto
    show ?thesis
      unfolding f_def
      using area_above_arclet(2)[OF t_le1 Re_le' ac_sub' below inj_g_lower inj_Re_lower U vder_sub']
      by auto
  qed
    \<comment> \<open>Step 4: total integral = area of inside.
       The inside decomposes as the region between the two arcs:
       inside(path_image g) = {z | Re z \<in> (0, Re b) \<and> f_lower(Re z) < Im z < f_upper(Re z)}
       By Fubini, its area = \<integral>₀^{Re b} (f_upper(x) - f_lower(x)) dx
       and by the change-of-variables computations above, this equals
       integral {0..t} f + integral {t..1} f = integral {0..1} f.\<close>
  have area_decomp: "measure lebesgue (inside (path_image g)) = integral {0..t} f + integral {t..1} f"
  proof -
    \<comment> \<open>Re-derive the integral = measure identities (proved locally in upper_int/lower_int)\<close>
    have t_le: "0 \<le> t" using t(1) by linarith
    have t_le1: "t \<le> 1" using t(2) by linarith
    have Re_le: "Re (g 0) \<le> Re (g t)" using g0 hgt Reb by simp
    have Re_le': "Re (g 1) \<le> Re (g t)" using g1 hgt Reb by simp
    have ac_sub: "absolutely_continuous_on {0..t} g"
      using absolutely_continuous_on_subset[OF cont] t by auto
    have ac_sub': "absolutely_continuous_on {t..1} g"
      using absolutely_continuous_on_subset[OF cont] t by auto
    have inj_g_upper: "inj_on g {0..t}"
      using arc_inj_on[of 0 t] t by auto
    then have inj_Re_upper: "inj_on Re (g ` {0..t})"
      using Reb Re_inj_upper g0 t
      by (intro arc_Re_inj_on; fastforce simp: assms b(2))
    have inj_g_lower: "inj_on g {t..1}"
      using arc_inj_on[of t 1] t by auto
    then have inj_Re_lower: "inj_on Re (g ` {t..1})"
      using Reb Re_inj_lower g1 t
      by (intro arc_Re_inj_on; fastforce simp: assms b(2))
    have vder_sub: "\<And>s. s \<in> {0..t} - U \<Longrightarrow> (g has_vector_derivative g' s) (at s)"
      using vder t(2) by auto
    have vder_sub': "\<And>s. s \<in> {t..1} - U \<Longrightarrow> (g has_vector_derivative g' s) (at s)"
      using vder t(1) by auto
        \<comment> \<open>The integral = measure identities\<close>
    interpret Area g g' 0 t U
    proof
      show "Re (g 0) \<le> Re (g t)" 
        using g0 hgt Reb by simp
      show "absolutely_continuous_on {0..t} g"
        using absolutely_continuous_on_subset[OF cont] t by auto
      show "inj_on g {0..t}"
        using arc_inj_on t less_eq_real_def by presburger
      then show "inj_on Re (g ` {0..t})"
        using Reb Re_inj_upper g0 t
        by (intro arc_Re_inj_on; fastforce simp: assms b(2))
    qed (use above U vder t in auto)
    define Au where "Au \<equiv> {z. \<exists>w \<in> g ` {0..t}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
    define Al where "Al \<equiv> {z. \<exists>w \<in> g ` {t..1}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
    have int_upper: "integral {0..t} f = measure lebesgue Au"
      using below_arclet(2) unfolding f_def Au_def by auto
    have int_lower: "integral {t..1} f = measure lebesgue Al"
      using area_above_arclet(2)[OF t_le1 Re_le' ac_sub' below inj_g_lower inj_Re_lower U vder_sub']
      unfolding f_def Al_def by blast
        \<comment> \<open>Step A: Au and Al are measurable (compact, hence lmeasurable)\<close>
    have Au_meas: "Au \<in> lmeasurable"
    proof -
      have cont_g_upper: "continuous_on {0..t} g"
        using absolutely_continuous_on_imp_continuous[OF ac_sub] is_interval_cc by blast
      define \<phi> where "\<phi> \<equiv> \<lambda>(s,r). Complex (Re (g s)) (r * Im (g s))"
      have cont_\<phi>: "continuous_on ({0..t} \<times> {0..1}) \<phi>"
        unfolding \<phi>_def split_def
        by (intro continuous_intros continuous_on_compose2[OF cont_g_upper] continuous_on_fst) auto
      have img: "\<phi> ` ({0..t} \<times> {0..1}) = Au"
      proof (rule set_eqI)
        fix z :: complex
        show "z \<in> \<phi> ` ({0..t} \<times> {0..1}) \<longleftrightarrow> z \<in> Au"
        proof
          assume "z \<in> \<phi> ` ({0..t} \<times> {0..1})"
          then obtain s r where sr: "s \<in> {0..t}" "r \<in> {0..1}" "z = Complex (Re (g s)) (r * Im (g s))"
            unfolding \<phi>_def by auto
          have "g s \<in> g ` {0..t}" using sr(1) by auto
          moreover have Im_ge: "Im (g s) \<ge> 0"
            using subsetD[OF above imageI[OF sr(1)]] by simp
          moreover have "Re (g s) = Re z" using sr(3) by simp
          moreover have "0 \<le> Im z" using sr(3) sr(2) Im_ge
            by (auto intro: mult_nonneg_nonneg)
          moreover have "Im z \<le> Im (g s)" using sr(3) sr(2) Im_ge
            by (auto simp: mult_left_le_one_le)
          ultimately show "z \<in> Au" unfolding Au_def by auto
        next
          assume "z \<in> Au"
          then obtain w where w: "w \<in> g ` {0..t}" "Re w = Re z" "0 \<le> Im z" "Im z \<le> Im w"
            unfolding Au_def by auto
          then obtain s where s: "s \<in> {0..t}" "w = g s" by auto
          show "z \<in> \<phi> ` ({0..t} \<times> {0..1})"
          proof (cases "Im w = 0")
            case True 
            then have "Im z = 0" using w(3,4) by linarith
            then have "z = \<phi> (s, 0)" unfolding \<phi>_def using w(2) s(2) by (simp add: complex_eq_iff)
            then show ?thesis using s(1) by auto
          next
            case False
            define r where "r \<equiv> Im z / Im w"
            have "Im w > 0" using False w(3,4) by linarith
            then have "r \<in> {0..1}" unfolding r_def using w(3,4) by (auto simp: field_simps)
            moreover have "z = \<phi> (s, r)"
              unfolding \<phi>_def r_def using False w(2) s(2) by (simp add: complex_eq_iff)
            ultimately show ?thesis using s(1) by auto
          qed
        qed
      qed
      with compact_Times compact_Icc img compact_continuous_image[OF cont_\<phi>]
      have "compact Au" by metis
      then show ?thesis using lmeasurable_compact by blast
    qed
    have Al_meas: "Al \<in> lmeasurable" \<comment> \<open>duality\<close>
    proof -
      have cont_g_lower: "continuous_on {t..1} g"
        using absolutely_continuous_on_imp_continuous[OF ac_sub'] is_interval_cc by blast
      define \<psi> where "\<psi> \<equiv> \<lambda>(s::real, r::real). Complex (Re (g s)) (r * Im (g s))"
      have cont_\<psi>: "continuous_on ({t..1} \<times> {0..1}) \<psi>"
        unfolding \<psi>_def split_def
        by (intro continuous_intros continuous_on_compose2[OF cont_g_lower] continuous_on_fst) auto
      have img: "\<psi> ` ({t..1} \<times> {0..1}) = Al"
      proof (rule set_eqI)
        fix z :: complex
        show "z \<in> \<psi> ` ({t..1} \<times> {0..1}) \<longleftrightarrow> z \<in> Al"
        proof
          assume "z \<in> \<psi> ` ({t..1} \<times> {0..1})"
          then obtain s r where sr: "s \<in> {t..1}" "r \<in> {0..1}" "z = Complex (Re (g s)) (r * Im (g s))"
            unfolding \<psi>_def by auto
          have "g s \<in> g ` {t..1}" using sr(1) by auto
          moreover have Im_le: "Im (g s) \<le> 0"
            using subsetD[OF below imageI[OF sr(1)]] by simp
          moreover have "Re (g s) = Re z" using sr(3) by simp
          moreover have "Im (g s) \<le> Im z"
            by (metis atLeastAtMost_iff calculation(2) complex.sel(2) linorder_not_le mult_less_cancel_right2
                sr(2,3))
          moreover have "Im z \<le> 0"
            using sr(3) sr(2) Im_le mult_nonneg_nonpos[of r "Im (g s)"] by simp
          ultimately show "z \<in> Al" unfolding Al_def
            by blast
        next
          assume "z \<in> Al"
          then obtain w where w: "w \<in> g ` {t..1}" "Re w = Re z" "Im w \<le> Im z" "Im z \<le> 0"
            unfolding Al_def by auto
          then obtain s where s: "s \<in> {t..1}" "w = g s" by auto
          show "z \<in> \<psi> ` ({t..1} \<times> {0..1})"
          proof (cases "Im w = 0")
            case True
            then have "Im z = 0" using w(3,4) by linarith
            then have "z = \<psi> (s, 0)" unfolding \<psi>_def using w(2) s(2) by (simp add: complex_eq_iff)
            then show ?thesis using s(1) by auto
          next
            case False
            define r where "r \<equiv> Im z / Im w"
            have "Im w < 0" using False w(3,4) by linarith
            then have "r \<in> {0..1}" unfolding r_def using w(3,4)
              by (auto simp: field_simps divide_le_eq_1_neg divide_nonneg_neg)
            moreover have "z = \<psi> (s, r)"
              unfolding \<psi>_def r_def using False w(2) s(2) by (simp add: complex_eq_iff)
            ultimately show ?thesis using s(1) by auto
          qed
        qed
      qed
      have "compact ({t..1} \<times> {0..1::real})" by (intro compact_Times compact_Icc)
      then have "compact Al" using img compact_continuous_image[OF cont_\<psi>] by simp
      then show ?thesis using lmeasurable_compact by blast
    qed
      \<comment> \<open>Step B+C: inside(path_image g) \<subseteq> Au \<union> Al \<subseteq> closure(inside(path_image g)),
         and the gap closure(inside) \<setminus> inside = path_image g is negligible,
         so measure(inside) = measure(Au \<union> Al).\<close>
    have Au_Al_sub_closure: "Au \<union> Al \<subseteq> closure (inside (path_image g))"
    proof -
      have ch_eq: "convex hull (path_image g) = closure (inside (path_image g))"
        using convex_hull_eq_closure_inside[OF g(1) _ conv] g(2,3) by auto
      have zero_in_ch: "0 \<in> convex hull (path_image g)"
        using hull_subset[of "path_image g" convex] g0
        by (auto simp: path_image_def intro!: imageI[of 0])
      have b_in_ch: "b \<in> convex hull (path_image g)"
        using hull_subset[of "path_image g" convex] b(1) by auto
      have real_seg: "closed_segment 0 b \<subseteq> convex hull (path_image g)"
        using closed_segment_subset_convex_hull[OF zero_in_ch b_in_ch] .
      have bdd_pi: "bounded (path_image g)"
        using compact_simple_path_image[OF g(1)] compact_imp_bounded by blast
          \<comment> \<open>Key fact: every point on the path has Re \<in> [0, Re b]\<close>
      have zero_in_pi: "(0::complex) \<in> path_image g"
        using g0 by (auto simp: path_image_def intro!: imageI[of 0])
      have Re_bounds: "0 \<le> Re w \<and> Re w \<le> Re b" if "w \<in> path_image g" for w
      proof -
        have d0: "dist w 0 \<le> diameter (path_image g)"
          using diameter_bounded_bound[OF bdd_pi that zero_in_pi] .
        have db: "dist w b \<le> diameter (path_image g)"
          using diameter_bounded_bound[OF bdd_pi that b(1)] .
        have "diameter (path_image g) = dist 0 b" using dab g0 g1 assms by simp
        then have diam_eq: "diameter (path_image g) = Re b"
          using Imb Re_le cmod_eq_Re g0 hgt by auto
        from d0 have ub: "cmod w \<le> Re b" using diam_eq by (simp add: dist_norm)
        then have "Re w \<le> Re b"
          using abs_Re_le_cmod[of w] by linarith
        from db have "cmod (w - b) \<le> Re b" using diam_eq by (simp add: dist_norm)
        then have "\<bar>Re w - Re b\<bar> \<le> cmod (w - b)"
          using abs_Re_le_cmod[of "w - b"] by simp
        then have "\<bar>Re w - Re b\<bar> \<le> Re b"
          using \<open>cmod (w - b) \<le> Re b\<close> by linarith
        then have "Re w \<ge> 0" by linarith
        show ?thesis using \<open>Re w \<le> Re b\<close> \<open>Re w \<ge> 0\<close> by auto
      qed
        \<comment> \<open>Sublemma: Complex (Re w) 0 \<in> closed_segment 0 b for any w on the path\<close>
      have real_point_in_seg: "Complex (Re w) 0 \<in> closed_segment 0 b"
        if "w \<in> path_image g" for w
      proof -
        have bds: "0 \<le> Re w" "Re w \<le> Re b" using Re_bounds[OF that] by auto
        define u where "u \<equiv> Re w / Re b"
        have "0 \<le> u" "u \<le> 1" unfolding u_def using bds Reb by auto
        have "Complex (Re w) 0 = (1 - u) *\<^sub>R 0 + u *\<^sub>R b"
          unfolding u_def using Reb Imb
          by (simp add: complex_eq_iff scaleR_complex.ctr)
        then show ?thesis using \<open>0 \<le> u\<close> \<open>u \<le> 1\<close>
          unfolding closed_segment_def by auto
      qed
        \<comment> \<open>Sublemma: z between p = Complex(Re w)(0) and w is in the convex hull\<close>
      have in_ch_via_seg: "z \<in> convex hull (path_image g)"
        if w_pi: "w \<in> path_image g"
          and Re_eq: "Re w = Re z"
          and Im_between: "(0 \<le> Im z \<and> Im z \<le> Im w) \<or> (Im w \<le> Im z \<and> Im z \<le> 0)"
        for z w
      proof -
        define p where "p \<equiv> Complex (Re w) 0"
        have p_in_ch: "p \<in> convex hull (path_image g)"
          using real_point_in_seg[OF w_pi] real_seg
          using p_def by blast
        have w_in_ch: "w \<in> convex hull (path_image g)"
          using hull_subset[of "path_image g" convex] w_pi by auto
        show "z \<in> convex hull (path_image g)"
        proof (cases "Im w = 0")
          case True
          then have "Im z = 0" using Im_between by linarith
          then have "z = p" unfolding p_def using Re_eq by (simp add: complex_eq_iff)
          then show ?thesis using p_in_ch by auto
        next
          case False
          define u where "u \<equiv> Im z / Im w"
          have "0 \<le> u" "u \<le> 1" unfolding u_def using Im_between False
            by (auto simp: field_simps split: if_splits)
          have "z = (1 - u) *\<^sub>R p + u *\<^sub>R w"
            unfolding p_def u_def using False Re_eq
            apply (simp add: complex_eq_iff scaleR_complex.ctr)
            by argo
          then have "z \<in> closed_segment p w" using \<open>0 \<le> u\<close> \<open>u \<le> 1\<close>
            unfolding closed_segment_def by auto
          then show ?thesis
            using closed_segment_subset_convex_hull[OF p_in_ch w_in_ch] by auto
        qed
      qed
      have Au_sub: "Au \<subseteq> convex hull (path_image g)"
      proof (rule subsetI)
        fix z assume "z \<in> Au"
        then obtain w where w: "w \<in> g ` {0..t}" "Re w = Re z" "0 \<le> Im z" "Im z \<le> Im w"
          unfolding Au_def by auto
        have "w \<in> path_image g" using w(1) t by (auto simp: path_image_def)
        then show "z \<in> convex hull (path_image g)"
          using in_ch_via_seg[of w z] w(2,3,4) by auto
      qed
      have Al_sub: "Al \<subseteq> convex hull (path_image g)"
      proof (rule subsetI)
        fix z assume "z \<in> Al"
        then obtain w where w: "w \<in> g ` {t..1}" "Re w = Re z" "Im w \<le> Im z" "Im z \<le> 0"
          unfolding Al_def by auto
        have "w \<in> path_image g" using w(1) t by (auto simp: path_image_def)
        then show "z \<in> convex hull (path_image g)"
          using in_ch_via_seg[of w z] w(2,3,4) by auto
      qed
      show ?thesis using Au_sub Al_sub ch_eq by auto
    qed

    have inside_sub_Au_Al: "inside (path_image g) \<subseteq> Au \<union> Al"
    proof (rule subsetI)
      fix z assume z_in: "z \<in> inside (path_image g)"
        \<comment> \<open>Set up the convex hull S and its key properties\<close>
      define S where "S \<equiv> convex hull (path_image g)"
      have S_convex: "convex S" unfolding S_def by (rule convex_convex_hull)
      have S_compact: "compact S" unfolding S_def
        using compact_simple_path_image[OF g(1)] compact_convex_hull by auto
      have S_bounded: "bounded S" using S_compact compact_imp_bounded by auto
      have ch_eq: "S = closure (inside (path_image g))"
        unfolding S_def using convex_hull_eq_closure_inside[OF g(1) _ conv] g(2,3) by auto
      have frontier_S: "frontier S = path_image g"
        unfolding S_def using frontier_convex_hull_eq_path_image[OF g(1) _ conv] g(2,3) by auto
      have inside_eq_int: "inside (path_image g) = interior S"
        by (metis S_bounded S_convex frontier_S inside_frontier_eq_interior)
      have S_int_ne: "interior S \<noteq> {}"
        using z_in inside_eq_int by auto
      have rel_int_eq: "rel_interior S = interior S"
        using rel_interior_nonempty_interior[OF S_int_ne] .
      have rel_fr_eq: "rel_frontier S = frontier S"
        using rel_frontier_nonempty_interior[OF S_int_ne] .
      have z_int: "z \<in> interior S" using z_in inside_eq_int by auto
      have z_rel_int: "z \<in> rel_interior S" using z_int rel_int_eq by simp
          \<comment> \<open>S is full-dimensional, so affine hull S = UNIV\<close>
      have aff_S: "affine hull S = UNIV"
        by (simp add: S_int_ne affine_hull_nonempty_interior)
          \<comment> \<open>Case split on the sign of Im z\<close>
      show "z \<in> Au \<union> Al"
      proof (cases "Im z \<ge> 0")
        case True
          \<comment> \<open>Shoot a ray upward from z in direction \<i>.
             By ray_to_rel_frontier, we hit a point on frontier S = path_image g.\<close>
        obtain d where d: "d > 0" "z + d *\<^sub>R \<i> \<in> rel_frontier S"
          by (metis S_bounded complex_i_not_zero ray_to_frontier rel_fr_eq z_int)
        define w where "w \<equiv> z + d *\<^sub>R \<i>"
        have w_on_path: "w \<in> path_image g"
          using d(2) rel_fr_eq frontier_S w_def by auto
        have Re_w: "Re w = Re z" unfolding w_def by simp
        have Im_w: "Im w = Im z + d" unfolding w_def by simp
        have Im_w_pos: "Im w > 0" using True d(1) Im_w by linarith
            \<comment> \<open>Since Im w > 0 and lower arc has Im \<le> 0, w must be on the upper arc\<close>
        have w_upper: "w \<in> g ` {0..t}"
        proof -
          have "{0..1} = {0..t} \<union> {t..1}" using t_le t_le1 by (auto simp: ivl_disj_un_two_touch)
          then have "path_image g = g ` {0..t} \<union> g ` {t..1}"
            unfolding path_image_def by (simp add: image_Un)
          then have "w \<in> g ` {0..t} \<union> g ` {t..1}" using w_on_path by simp
          moreover have "w \<notin> g ` {t..1}"
            using below Im_w_pos by (auto simp: subset_iff)
          ultimately show ?thesis by blast
        qed
        have "z \<in> Au"
          using Au_def Im_w Re_w True d(1) w_upper by auto
        then show "z \<in> Au \<union> Al" ..
      next
        case False
        then have Im_z_neg: "Im z \<le> 0" by simp
            \<comment> \<open>Shoot a ray downward from z in direction -\<i>\<close>
        obtain d where d: "d > 0" "z + d *\<^sub>R (-\<i>) \<in> frontier S"
          by (metis S_bounded complex_i_not_zero neg_equal_0_iff_equal ray_to_frontier z_int)
        have d2: "z - d *\<^sub>R \<i> \<in> rel_frontier S"
          using d(2) rel_fr_eq by (simp add: real_vector.scale_minus_right)
        define w where "w \<equiv> z - d *\<^sub>R \<i>"
        have w_on_path: "w \<in> path_image g"
          using d2 rel_fr_eq frontier_S w_def by auto
        have Re_w: "Re w = Re z" unfolding w_def by simp
        have Im_w: "Im w = Im z - d" unfolding w_def by simp
        have Im_w_neg: "Im w < 0" using Im_z_neg d(1) Im_w by linarith
            \<comment> \<open>Since Im w < 0, w must be on the lower arc\<close>
        have w_lower: "w \<in> g ` {t..1}"
        proof -
          have "{0..1} = {0..t} \<union> {t..1}" using t_le t_le1 by (auto simp: ivl_disj_un_two_touch)
          then have "path_image g = g ` {0..t} \<union> g ` {t..1}"
            unfolding path_image_def by (simp add: image_Un)
          then have "w \<in> g ` {0..t} \<union> g ` {t..1}" using w_on_path by simp
          moreover have "w \<notin> g ` {0..t}"
            using above Im_w_neg by (auto simp: subset_iff)
          ultimately show ?thesis by blast
        qed
        have "z \<in> Al"
          using Al_def Im_w Im_z_neg Re_w d(1) w_lower by auto
        then show "z \<in> Au \<union> Al" ..
      qed
    qed

    have inside_eq: "measure lebesgue (inside (path_image g)) = measure lebesgue (Au \<union> Al)"
    proof -
      have bdd_inside: "bounded (inside (path_image g))"
        using Jordan_inside_outside[OF g(1)] g(2,3) by auto
      have frontier_inside: "frontier (inside (path_image g)) = path_image g"
        using Jordan_inside_outside[OF g(1)] g(2,3) by auto
      have neg_frontier: "negligible (frontier (inside (path_image g)))"
        using negligible_convex_frontier[OF conv] .
      have inside_meas: "inside (path_image g) \<in> lmeasurable"
        using measurable_Jordan[OF bdd_inside neg_frontier] .
      have AuAl_meas: "Au \<union> Al \<in> lmeasurable"
        using fmeasurable.Un[OF Au_meas Al_meas] .
          \<comment> \<open>Symmetric difference \<subseteq> path_image g, which is negligible\<close>
      have "inside (path_image g) \<Delta> (Au \<union> Al) \<subseteq> path_image g"
        by (metis Au_Al_sub_closure Diff_mono Diff_subset_conv closure_Un_frontier frontier_inside inside_sub_Au_Al
            le_iff_sup)
      then have "negligible (inside (path_image g) \<Delta> (Au \<union> Al))"
        using negligible_subset neg_frontier frontier_inside by auto
      then show ?thesis
        using measure_negligible_symdiff[OF inside_meas]
        by presburger
    qed
      \<comment> \<open>Step D: Au \<inter> Al \<subseteq> {z. Im z = 0}, which is negligible in \<real>².
         Therefore measure(Au \<union> Al) = measure(Au) + measure(Al).\<close>
    have inter_null: "Au \<inter> Al \<subseteq> {z. Im z = 0}"
      unfolding Au_def Al_def by auto
    have "measure lebesgue (Au \<union> Al) = measure lebesgue Au + measure lebesgue Al"
    proof -
      have "negligible {z :: complex. Im z = 0}"
        using negligible_hyperplane[of \<i> 0]
        by (simp add: complex_inner_i_left)
      then have "negligible (Au \<inter> Al)"
        using negligible_subset inter_null by blast
      then have "measure lebesgue (Au \<inter> Al) = 0"
        by (rule negligible_imp_measure0)
      moreover have "measure lebesgue (Au \<union> Al) = measure lebesgue Au + measure lebesgue Al - measure lebesgue (Au \<inter> Al)"
        using measure_Un3[of Au lebesgue Al] Au_meas Al_meas by auto
      ultimately show ?thesis by simp
    qed
      \<comment> \<open>Combine\<close>
    show ?thesis
      using inside_eq \<open>measure lebesgue (Au \<union> Al) = measure lebesgue Au + measure lebesgue Al\<close>
        int_upper int_lower by simp
  qed
    \<comment> \<open>Step 5: Combine\<close>
  have int_eq: "\<bar>integral {0..1} f\<bar> = measure lebesgue (inside (path_image g))"
    using split_int area_decomp upper_int lower_int by linarith

  show ?thesis unfolding Green_concl_def f_def
    using int_eq f_abs_int unfolding f_def by auto
qed

end

subsection \<open>Green's theorem special case at zero\<close>

context Green
begin

interpretation CR: Green gop gop' "(\<lambda>t. 1-t) ` U" "cnj a" "cnj b"
  by (rule cnj_rev)

interpretation R: Green "reversepath g" "uminus \<circ> reversepath g'" "(\<lambda>t. 1-t) ` U" a b
  by (rule rev)

lemma Green_area_zero:
  assumes "a = 0"
  shows "Green_concl g g'"
proof -
  have g0: "g 0 = 0" using assms g(2) by (simp add: pathstart_def)
  have g1: "g 1 = 0" using assms g(3) by (simp add: pathfinish_def)
  define f where "f \<equiv> \<lambda>s. Re (g' s) * Im (g s)"
  have split_case: "Green_concl g g'"
    if assms: "a = 0"
      and t: "0 < t" "t < 1"
      and hgt: "g t = b"
      and above: "g ` {0..t} \<subseteq> {z. 0 \<le> Im z}"
      and below: "g ` {t..1} \<subseteq> {z. Im z \<le> 0}"
    for t :: real
    using Green_area_zero_A[OF assms t hgt above below] .
  have split_case': "Green_concl g g'"
    if assms: "a = 0"
      and t: "0 < t" "t < 1"
      and hgt: "g t = b"
      and below: "g ` {0..t} \<subseteq> {z. Im z \<le> 0}"
      and above: "g ` {t..1} \<subseteq> {z. 0 \<le> Im z}"
    for t :: real
  proof -
    have "Green_concl (reversepath g) (uminus \<circ> reversepath g')"
    proof (intro R.Green_area_zero_A)
      show "a=0" "0 < 1-t" "1-t < 1"
        using assms t by auto
      show "reversepath g (1-t) = b"
        by (simp add: hgt reversepath_def)
      show "reversepath g ` {0..1-t} \<subseteq> {z. 0 \<le> Im z}"
        using above by (force simp: reversepath_def image_subset_iff)
      show "reversepath g ` {1-t..1} \<subseteq> {z. Im z \<le> 0}"
        using below by (force simp: reversepath_def image_subset_iff)
    qed
    moreover have "integral {0..1} (\<lambda>t. Re (reversepath g' t) * Im (reversepath g t)) 
                 = integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))"
      using has_integral_affinity [of f _ 0 1 "-1" 1] f_abs_int
      by (fastforce simp add: reversepath_def f_def absolutely_integrable_on_def)
    ultimately show ?thesis
      using f_abs_int by (auto simp: Green_concl_def)
  qed

  have Reb: "Re b > 0" using b(2) assms by simp
  have Im_a: "Im a = 0" using assms by simp
  have Im_b: "Im b = 0" using b(3) Im_a by simp
  have path_g: "path g" using g(1) simple_path_imp_path by blast
  have cont_g: "continuous_on {0..1} g"
    using path_g by (simp add: path_def)
  obtain t where t: "g t = b" "0 < t" "t < 1"
  proof -
    obtain t where t0: "g t = b" "t \<in> {0..1}"
      using b by (auto simp: path_image_def)
    have "0 < t"
      by (metis atLeastAtMost_iff b(2) g(2) not_le order_eq_iff pathstart_def t0)
    moreover have "t < 1"
      by (smt (verit, best) b(2) box_real(2) g(3) mem_box_real(2) pathfinish_def t0)
    ultimately show thesis using t0 that by blast
  qed
  have Re_inj_upper: "\<lbrakk>s1 \<in> {0..t}; s2 \<in> {0..t}; Re (g s1) = Re (g s2); s1 \<noteq> s2\<rbrakk>
        \<Longrightarrow> (s1 = 0 \<and> s2 = t) \<or> (s1 = t \<and> s2 = 0)" for s1 s2
    using Re_inj_upper_gen g0 g1 t by presburger
  have Re_inj_lower: "\<lbrakk>s1 \<in> {t..1}; s2 \<in> {t..1}; Re (g s1) = Re (g s2); s1 \<noteq> s2\<rbrakk>
        \<Longrightarrow> (s1 = t \<and> s2 = 1) \<or> (s1 = 1 \<and> s2 = t)" for s1 s2
    using CR.Re_inj_upper_gen[of "1-s1" "1-t" "1-s2"] t g g0 g1 assms
    by (auto simp add: gop_def reversepath_def)
  have "g ` {0..t} \<subseteq> {z. 0 \<le> Im z} \<and> g ` {t..1} \<subseteq> {z. Im z \<le> 0} \<or>
        g ` {0..t} \<subseteq> {z. Im z \<le> 0} \<and> g ` {t..1} \<subseteq> {z. 0 \<le> Im z}"
  proof -
    have "open_segment 0 b \<subseteq> frontier (inside (path_image g)) \<or>
          open_segment 0 b \<subseteq> interior (inside (path_image g))"
    proof (rule convex_open_segment_cases_alt)
      show "convex (inside (path_image g))"
        by (simp add: conv)
      show "0 \<in> closure (inside (path_image g))"
        using hull_inc convex_hull_eq_closure_inside
        by (metis assms conv g pathfinish_in_path_image)
      show "b \<in> closure (inside (path_image g))"
        using hull_inc convex_hull_eq_closure_inside
        using R.g(2) b(1) conv g(1,2) by fastforce
    qed
    then consider "open_segment 0 b \<subseteq> path_image g" 
                | "open_segment 0 b \<subseteq> inside (path_image g)"
      by (metis Jordan_inside_outside g interior_subset subset_trans)
    then show ?thesis
    proof cases
      case 1
      have *: "connectedin euclidean (open_segment 0 b)"
        by (simp add: convex_connected)
      with 1 have conn: "connectedin (subtopology euclidean (path_image g))
                         (open_segment 0 b)"
        by (simp add: connectedin_subtopology)
      have pi1: "g ` {0<..<t} \<subseteq> path_image g" and pi2: "g ` {t<..<1} \<subseteq> path_image g"
        using t by (auto simp: path_image_def image_iff)
      have cl1: "g ` {0<..<t} \<inter> path_image g \<inter> closure (path_image g \<inter> g ` {t<..<1}) = {}"
      proof -
        have lf: "loop_free g" using g(1) by (simp add: simple_path_def)
        have inj: "inj_on g {0<..<1}" using lf loop_free_inj_on by blast
        have disj: "g ` {0<..<t} \<inter> g ` {t..1} = {}"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          then obtain x y where xy: "x \<in> {0<..<t}" "y \<in> {t..1}" "g x = g y"
            by blast
          have x01: "x \<in> {0..1}" using xy(1) t(3) by auto
          have y01: "y \<in> {0..1}" using xy(2)
            using t(2) by auto
          have "x \<noteq> y" using xy(1,2) by auto
          then have "x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
            using lf xy(3) x01 y01 unfolding loop_free_def by blast
          then show False using xy(1,2) by auto
        qed
        have closed_img: "closed (g ` {t..1})"
          using compact_continuous_image[OF continuous_on_subset[OF cont_g]]
          by (simp add: compact_imp_closed less_eq_real_def t(2))
        have "closure (g ` {t<..<1}) \<subseteq> g ` {t..1}"
          using closed_img closure_minimal by (meson closure_minimal image_mono greaterThanLessThan_subseteq_atLeastAtMost_iff order.refl less_imp_le)
        then have "closure (path_image g \<inter> g ` {t<..<1}) \<subseteq> g ` {t..1}"
          by (meson Int_lower2 closure_mono dual_order.trans)
        then show ?thesis using disj by auto
      qed
      have cl2: "g ` {t<..<1} \<inter> path_image g \<inter> closure (path_image g \<inter> g ` {0<..<t}) = {}"
      proof -
        have lf: "loop_free g" using g(1) by (simp add: simple_path_def)
        have disj: "g ` {t<..<1} \<inter> g ` {0..t} = {}"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          then obtain x y where xy: "x \<in> {t<..<1}" "y \<in> {0..t}" "g x = g y"
            by blast
          have x01: "x \<in> {0..1}" using xy(1) using t(2) by force
          have y01: "y \<in> {0..1}" using xy(2) t(3) by auto
          have "x \<noteq> y" using xy(1,2) by auto
          then have "x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
            using lf xy(3) x01 y01 unfolding loop_free_def by blast
          then show False using xy(1,2) by auto
        qed
        have closed_img: "closed (g ` {0..t})"
          using compact_continuous_image[OF continuous_on_subset[OF cont_g] _]
          by (meson atLeastatMost_subset_iff compact_imp_closed compact_interval
              eucl_less_le_not_le order.refl t(3))
        have "closure (g ` {0<..<t}) \<subseteq> g ` {0..t}"
          using closed_img closure_minimal by (meson closure_minimal image_mono greaterThanLessThan_subseteq_atLeastAtMost_iff order.refl less_imp_le)
        then have "closure (path_image g \<inter> g ` {0<..<t}) \<subseteq> g ` {0..t}"
          by (meson Int_lower2 closure_mono dual_order.trans)
        then show ?thesis using disj by auto
      qed
      have sub: "open_segment 0 b \<subseteq> g ` {0<..<t} \<union> g ` {t<..<1}"
      proof -
        have decomp: "path_image g \<subseteq> g ` {0<..<t} \<union> g ` {t<..<1} \<union> {0, b}"
        proof
          fix z assume "z \<in> path_image g"
          then obtain s where s: "s \<in> {0..1}" "g s = z" by (auto simp: path_image_def)
          then consider "s = 0" | "s \<in> {0<..<t}" | "s = t" | "s \<in> {t<..<1}" | "s = 1"
            using t by force
          then show "z \<in> g ` {0<..<t} \<union> g ` {t<..<1} \<union> {0, b}"
            using \<open>g s = z\<close> t g0 g1 by blast 
        qed
        have "open_segment 0 b \<inter> {0, b} = {}"
          unfolding open_segment_def by auto
        then show ?thesis using 1 decomp by auto
      qed
      have sep: "separatedin (subtopology euclidean (path_image g))
                              (g ` {0<..<t}) (g ` {t<..<1})"
      proof -
        have eq1: "path_image g \<inter> g ` {t<..<1} = g ` {t<..<1}" using pi2 by auto
        have eq2: "path_image g \<inter> g ` {0<..<t} = g ` {0<..<t}" using pi1 by auto
        have d1: "g ` {0<..<t} \<inter> closure (g ` {t<..<1}) = {}"
          using cl1 pi1 eq1 by auto
        have d2: "g ` {t<..<1} \<inter> closure (g ` {0<..<t}) = {}"
          using cl2 pi2 eq2 by auto
        have "separatedin euclidean (g ` {0<..<t}) (g ` {t<..<1})"
          unfolding separatedin_def using d1 d2
          by (simp add: euclidean_closure_of topspace_euclidean)
        then show ?thesis
          using pi1 pi2 by (simp add: separatedin_subtopology)
      qed
      have "open_segment 0 b \<subseteq> g ` {0<..<t} \<or> open_segment 0 b \<subseteq> g ` {t<..<1}"
        using connectedin_subset_separated_union[OF conn sep sub] .
      then have "closed_segment 0 b \<subseteq> g ` {0..t} \<or> closed_segment 0 b \<subseteq> g ` {t..1}"
        unfolding closed_segment_eq_open
        by (elim disj_forward) (use g0 g1 t in auto)
      then have seg_eq: "g ` {0..t} = closed_segment 0 b \<or> g ` {t..1} = closed_segment 0 b"
      proof (elim disjE)
        assume sub: "closed_segment 0 b \<subseteq> g ` {0..t}"
        have inj: "inj_on g {0..t}" using arc_inj_on[of 0 t] t by auto
        have "continuous_on {0..t} g"
          using continuous_on_subset[OF cont_g] t by auto
        then have cont_inv: "continuous_on (g ` {0..t}) (the_inv_into {0..t} g)"
          using continuous_on_inv_into[OF _ compact_Icc inj] by metis
        have inv_mem: "the_inv_into {0..t} g z \<in> {0..t}" if "z \<in> closed_segment 0 b" for z
          using the_inv_into_into[OF inj _ order_refl] sub that by blast
        have eq0: "the_inv_into {0..t} g 0 = 0"
          using the_inv_into_f_f[OF inj, of 0] g0 t by auto
        have eqt: "the_inv_into {0..t} g b = t"
          using the_inv_into_f_f[OF inj, of t] t by auto
        have conn: "connected (the_inv_into {0..t} g ` closed_segment 0 b)"
          by (intro connected_continuous_image continuous_on_subset[OF cont_inv sub]
                   connected_segment)
        have "0 \<in> the_inv_into {0..t} g ` closed_segment 0 b"
          using eq0 by (auto intro: rev_image_eqI ends_in_segment)
        moreover have "t \<in> the_inv_into {0..t} g ` closed_segment 0 b"
          using eqt by (auto intro: rev_image_eqI ends_in_segment)
        ultimately have "{0..t} \<subseteq> the_inv_into {0..t} g ` closed_segment 0 b"
          using connected_contains_Icc[OF conn] by auto
        then have "g ` {0..t} \<subseteq> g ` (the_inv_into {0..t} g ` closed_segment 0 b)"
          by (rule image_mono)
        also have "\<dots> \<subseteq> closed_segment 0 b"
          using f_the_inv_into_f[OF inj] sub by (auto simp: image_image)
        finally show ?thesis using sub by auto
      next
        assume sub: "closed_segment 0 b \<subseteq> g ` {t..1}"
        have inj: "inj_on g {t..1}" using arc_inj_on[of t 1] t by auto
        have cont_sub: "continuous_on {t..1} g"
          using continuous_on_subset[OF cont_g] t by auto
        have cont_inv: "continuous_on (g ` {t..1}) (the_inv_into {t..1} g)"
          using continuous_on_inv_into[OF cont_sub compact_Icc inj] .
        have inv_mem: "the_inv_into {t..1} g z \<in> {t..1}" if "z \<in> closed_segment 0 b" for z
          using the_inv_into_into[OF inj _ order_refl] sub that by blast
        have eqt: "the_inv_into {t..1} g b = t"
          using the_inv_into_f_f[OF inj, of t] t by auto
        have eq1: "the_inv_into {t..1} g 0 = 1"
          using the_inv_into_f_f[OF inj, of 1] g1 t by auto
        have conn: "connected (the_inv_into {t..1} g ` closed_segment 0 b)"
          by (intro connected_continuous_image continuous_on_subset[OF cont_inv sub]
                   connected_segment)
        have "t \<in> the_inv_into {t..1} g ` closed_segment 0 b"
          using eqt by (auto intro: rev_image_eqI ends_in_segment)
        moreover have "1 \<in> the_inv_into {t..1} g ` closed_segment 0 b"
          using eq1 by (auto intro: rev_image_eqI ends_in_segment)
        ultimately have "{t..1} \<subseteq> the_inv_into {t..1} g ` closed_segment 0 b"
          using connected_contains_Icc[OF conn] by auto
        then have "g ` {t..1} \<subseteq> g ` (the_inv_into {t..1} g ` closed_segment 0 b)"
          by (rule image_mono)
        also have "\<dots> \<subseteq> closed_segment 0 b"
          using f_the_inv_into_f[OF inj] sub by (auto simp: image_image)
        finally show ?thesis using sub by auto
      qed
      \<comment> \<open>Use convex_triple_rel_frontier to show inside is on one side of Im = 0\<close>
      have inside_side: "inside (path_image g) \<subseteq> {z. Im z \<le> 0} \<or>
                         inside (path_image g) \<subseteq> {z. 0 \<le> Im z}"
      proof -
        have J: "inside (path_image g) \<noteq> {}" "open (inside (path_image g))"
          "frontier (inside (path_image g)) = path_image g"
          using Jordan_inside_outside g by blast+
        have intne: "interior (inside (path_image g)) \<noteq> {}"
          using J(1,2) interior_eq by auto
        have rf_eq: "rel_frontier (inside (path_image g)) = frontier (inside (path_image g))"
          using rel_frontier_nonempty_interior intne by blast
        have mid_on: "midpoint 0 b \<in> path_image g"
          using "1" Reb by force
        have rf0: "(0::complex) \<in> rel_frontier (inside (path_image g))"
          using rf_eq J(3) g0 by (auto simp: path_image_def intro!: image_eqI[of _ _ 0])
        have rfb: "b \<in> rel_frontier (inside (path_image g))"
          using rf_eq J(3) b(1) by auto
        have rfm: "midpoint 0 b \<in> rel_frontier (inside (path_image g))"
          using rf_eq J(3) mid_on by auto
        have ne1: "(0::complex) \<noteq> b" using b(2) assms by (auto simp: complex_eq_iff)
        have ne2: "(0::complex) \<noteq> midpoint 0 b"
          using ne1 by (simp add: midpoint_def complex_eq_iff)
        have ne3: "b \<noteq> midpoint 0 b"
          using ne1 by (simp add: midpoint_def complex_eq_iff)
        have ip1: "\<i> \<bullet> (0::complex) = 0" by (simp add: complex_inner_i_left)
        have ip2: "\<i> \<bullet> b = 0" using Im_b by (simp add: complex_inner_i_left)
        have ip3: "\<i> \<bullet> midpoint 0 b = 0"
          using Im_b by (simp add: midpoint_def complex_inner_i_left)
        have "inside (path_image g) \<subseteq> {x. \<i> \<bullet> x \<le> 0} \<or>
              inside (path_image g) \<subseteq> {x. \<i> \<bullet> x \<ge> 0}"
          using convex_triple_rel_frontier[OF conv rf0 rfb rfm ne1 ne2 ne3 ip1 ip2 ip3] .
        then show ?thesis by (auto simp: complex_inner_i_left)
      qed
      have pi_sub: "path_image g \<subseteq> closure (inside (path_image g))"
        using hull_subset[of "path_image g" convex] convex_hull_eq_closure_inside[OF g(1)] g(2,3) conv by force
      \<comment> \<open>The closed segment from 0 to b has Im = 0, so lies in both half-planes.\<close>
      have seg_both: "closed_segment 0 b \<subseteq> {z. Im z \<le> 0}" "closed_segment 0 b \<subseteq> {z. 0 \<le> Im z}"
        using Im_b by (auto simp: closed_segment_def)
      \<comment> \<open>If inside \<subseteq> half-plane, then so is path_image (by closure).\<close>
      have side_le: "inside (path_image g) \<subseteq> {z. Im z \<le> 0} \<Longrightarrow> path_image g \<subseteq> {z. Im z \<le> 0}"
        using pi_sub closure_minimal[OF _ closed_halfspace_le[of \<i> 0, simplified complex_inner_i_left]]
        by auto
      have side_ge: "inside (path_image g) \<subseteq> {z. 0 \<le> Im z} \<Longrightarrow> path_image g \<subseteq> {z. 0 \<le> Im z}"
        using pi_sub closure_minimal[OF _ closed_halfspace_ge[of 0 \<i>, simplified complex_inner_i_left]]
        by auto
      from seg_eq inside_side show ?thesis
      proof (elim disjE)
        assume eq: "g ` {0..t} = closed_segment 0 b"
        assume "inside (path_image g) \<subseteq> {z. Im z \<le> 0}"
        then show ?thesis using side_le seg_both eq t
          by (auto simp: path_image_def image_subset_iff dest!: subsetD)
      next
        assume eq: "g ` {0..t} = closed_segment 0 b"
        assume "inside (path_image g) \<subseteq> {z. 0 \<le> Im z}"
        then show ?thesis using side_ge seg_both eq t
          by (auto simp: path_image_def image_subset_iff dest!: subsetD)
      next
        assume eq: "g ` {t..1} = closed_segment 0 b"
        assume "inside (path_image g) \<subseteq> {z. Im z \<le> 0}"
        then show ?thesis using side_le seg_both eq t
          by (auto simp: path_image_def image_subset_iff dest!: subsetD)
      next
        assume eq: "g ` {t..1} = closed_segment 0 b"
        assume "inside (path_image g) \<subseteq> {z. 0 \<le> Im z}"
        then show ?thesis using side_ge seg_both eq t
          by (auto simp: path_image_def image_subset_iff dest!: subsetD)
      qed
    next
      case seg_inside:2
      have real_on_curve: "z = 0 \<or> z = b" 
        if z_on: "z \<in> path_image g" and z_real: "Im z = 0" for z
      proof (rule ccontr)
        assume non: "\<not> ?thesis"
          \<comment> \<open>Step 1: Basic setup\<close>
            \<comment> \<open>Step 2: Diameter bounds force z into closed_segment 0 b.
       dist 0 z \<le> diam = Re b gives |Re z| \<le> Re b.
       dist z b \<le> diam = Re b gives |Re z − Re b| \<le> Re b, hence Re z \<ge> 0.
       So z is real with 0 \<le> Re z \<le> Re b, i.e. z \<in> closed_segment 0 b.\<close>

        have z_in_seg: "z \<in> closed_segment 0 b"
        proof -
          have bdd: "bounded (path_image g)"
            using g(1) bounded_simple_path_image by blast
          have z0_on: "0 \<in> path_image g"
            using pathstart_in_path_image[of g] g(2) \<open>a=0\<close> by simp
          have diam_eq: "diameter (path_image g) = Re b"
            using dab \<open>a=0\<close> Im_b Reb by (simp add: dist_complex_def cmod_eq_Re)
          have d1: "dist 0 z \<le> Re b"
            using diameter_bounded_bound[OF bdd z0_on z_on] diam_eq by simp
          have d2: "dist z b \<le> Re b"
            using diameter_bounded_bound[OF bdd z_on b(1)] diam_eq by simp
          have Re_le: "Re z \<le> Re b"
            using d1 z_real by (simp add: dist_complex_def cmod_eq_Re)
          have Re_ge: "Re z \<ge> 0"
            using d2 z_real Im_b by (simp add: dist_complex_def cmod_eq_Re minus_complex.sel)
          have z_eq: "z = of_real (Re z)"
            using z_real complex_is_Real_iff of_real_Re by metis
          have b_eq: "b = of_real (Re b)"
            using Im_b complex_is_Real_iff of_real_Re by metis
          show ?thesis
            by (metis Re_ge Re_le Reb atLeastAtMost_iff b_eq closed_segment_eq_real_ivl1
                less_eq_real_def of_real_0 of_real_closed_segment z_eq)
        qed
          \<comment> \<open>Step 4: z is on the curve, so z \<notin> inside. Hence z \<notin> open_segment 0 b.
       Combined with z \<in> closed_segment 0 b, we get z = 0 \<or> z = b.\<close>
        have "z \<notin> inside (path_image g)"
          using inside_no_overlap z_on by blast
        then have "z \<notin> open_segment 0 b"
          using seg_inside by blast
        then show False
          using non z_in_seg by (auto simp: closed_segment_eq_open)
      qed
      have Re_inj_upper: "\<lbrakk>s1 \<in> {0..t}; s2 \<in> {0..t}; Re (g s1) = Re (g s2); s1 \<noteq> s2\<rbrakk>
        \<Longrightarrow> (s1 = 0 \<and> s2 = t) \<or> (s1 = t \<and> s2 = 0)" for s1 s2
        using Re_inj_upper_gen g0 g1 t by presburger
      have Re_inj_lower: "\<lbrakk>s1 \<in> {t..1}; s2 \<in> {t..1}; Re (g s1) = Re (g s2); s1 \<noteq> s2\<rbrakk>
        \<Longrightarrow> (s1 = t \<and> s2 = 1) \<or> (s1 = 1 \<and> s2 = t)" for s1 s2
        using CR.Re_inj_upper_gen[of "1-s1" "1-t" "1-s2"] t g g0 g1 assms
        by (auto simp add: gop_def reversepath_def)

        \<comment> \<open>Im \<circ> g doesn't change sign on either arc: if it did, IVT gives a real point
     in the interior of the arc, contradicting real_on_curve and injectivity.\<close>
      have no_cross: "(\<forall>s \<in> {u..v}. Im (g s) \<ge> 0) \<or> (\<forall>s \<in> {u..v}. Im (g s) \<le> 0)"
        if huv: "u < v" "{u..v} \<subseteq> {0..1}" and hinj: "inj_on g {u..v}"
          and hend: "Im (g u) = 0" "Im (g v) = 0" for u v
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then obtain s\<^sub>1 s\<^sub>2 where s1: "s\<^sub>1 \<in> {u..v}" "Im (g s\<^sub>1) > 0"
          and s2: "s\<^sub>2 \<in> {u..v}" "Im (g s\<^sub>2) < 0"
          by (meson linorder_not_le)
        have cont_uv: "continuous_on {u..v} g"
          using cont_g continuous_on_subset huv(2) by blast
        \<comment> \<open>IVT gives s \<in> (u,v) with Im(g s) = 0\<close>
        obtain s where s: "s \<in> {u..v}" "Im (g s) = 0" "s \<noteq> u" "s \<noteq> v"
        proof (cases "s\<^sub>1 \<le> s\<^sub>2")
          case True
          obtain s where hs: "s \<in> {s\<^sub>1..s\<^sub>2}" "Im (g s) = 0"
            using ivt_decreasing_component_on_1[OF True, of g \<i> 0]
              continuous_on_subset[OF cont_uv] s1 s2
            by (force simp: complex_inner_i_right)
          have "s \<in> {u..v}" using hs(1) s1(1) s2(1) by auto
          moreover have "s \<noteq> u" using hs s1 hend(1) by force
          moreover have "s \<noteq> v" using hs s2 hend(2) by force
          ultimately show thesis using that hs(2) by blast
        next
          case False
          then have le: "s\<^sub>2 \<le> s\<^sub>1" by linarith
          obtain s where hs: "s \<in> {s\<^sub>2..s\<^sub>1}" "Im (g s) = 0"
            using ivt_increasing_component_on_1[OF le, of g \<i> 0]
              continuous_on_subset[OF cont_uv] s1 s2
            by (force simp: complex_inner_i_right)
          have "s \<in> {u..v}" using hs(1) s1(1) s2(1) by auto
          moreover have "s \<noteq> u" using hs s2 hend(1) by force
          moreover have "s \<noteq> v" using hs s1 hend(2) by force
          ultimately show thesis using that hs(2) by blast
        qed

        \<comment> \<open>g s is on the path, so g s \<in> {0, b} by real_on_curve\<close>
        have "g s \<in> path_image g"
          using s(1) huv(2) by (auto simp: path_image_def subset_iff)
        then have "g s = 0 \<or> g s = b" using real_on_curve s(2) by blast
        \<comment> \<open>But g is injective on [u,v] and s \<in> (u,v), so g s \<noteq> g u and g s \<noteq> g v\<close>
        moreover have "g s \<noteq> g u" "g s \<noteq> g v"
          using inj_onD[OF hinj] s(1,3,4) by auto
        \<comment> \<open>Since {g u, g v} \<subseteq> {0, b}, this gives the contradiction\<close>
        moreover have "g u \<in> {0, b}" "g v \<in> {0, b}"
          using real_on_curve hend huv by (auto simp: path_image_def subset_iff)
        ultimately show False
          using \<open>u < v\<close> inj_onD [OF hinj] by (auto simp: order_class.less_le)
      qed
      have no_cross_1: "(\<forall>s \<in> {0..t}. Im (g s) \<ge> 0) \<or> (\<forall>s \<in> {0..t}. Im (g s) \<le> 0)"
        using no_cross[of 0 t] arc_inj_on[of 0 t] t g0 Im_b by auto
      have no_cross_2: "(\<forall>s \<in> {t..1}. Im (g s) \<ge> 0) \<or> (\<forall>s \<in> {t..1}. Im (g s) \<le> 0)"
        using no_cross[of t 1] arc_inj_on[of t 1] t g1 Im_b by auto
      \<comment> \<open>Now case-split on the orientation and dispatch to split_case or split_case'\<close>
    show ?thesis
    proof -
      \<comment> \<open>Eliminate the case where both arcs are on the same side of the real axis.
       Key idea: if path_image g \<subseteq> {Im z \<ge> 0}, then closure(inside) = convex hull \<subseteq> {Im z \<ge> 0},
       so inside \<subseteq> {Im z > 0} (since inside is open). But open_segment 0 b \<subseteq> closure(inside)
       has Im = 0, so it must be in frontier(inside) = path_image g.
       This contradicts real_on_curve since open_segment 0 b is infinite.\<close>
      have inside_ne: "inside (path_image g) \<noteq> {}"
        using Jordan_inside_outside g by blast
      have frontier_eq: "frontier (inside (path_image g)) = path_image g"
        using Jordan_inside_outside g by blast
      have open_inside: "open (inside (path_image g))"
        using Jordan_inside_outside g by blast
      have bounded_inside: "bounded (inside (path_image g))"
        using Jordan_inside_outside g by blast
      have closure_eq: "closure (inside (path_image g)) = convex hull (path_image g)"
        using convex_hull_eq_closure_inside g conv by auto
      have ab_hull: "a \<in> convex hull (path_image g)" "b \<in> convex hull (path_image g)"
        using b(1) g(2) pathstart_in_path_image hull_inc by fastforce+
      have seg_in_closure: "open_segment a b \<subseteq> closure (inside (path_image g))"
        by (metis ab_hull convex_contains_open_segment convex_convex_hull local.closure_eq)
      have seg_Im0: "open_segment a b \<subseteq> {z. Im z = 0}"
        using assms Im_b by (auto simp: in_segment complex_eq_iff)
      have seg_infinite: "\<not> finite (open_segment a b)"
        using Reb assms by force

      have not_all_above: "\<not> (path_image g \<subseteq> {z. 0 \<le> Im z})"
        using Reb assms not_all_above real_on_curve t Im_b by blast

      have not_all_below: "\<not> (path_image g \<subseteq> {z. Im z \<le> 0})"
        using CR.not_all_above using g g0 g1 assms Reb real_on_curve
        by (force simp add: gop_def  path_image_compose)
          \<comment> \<open>With the elimination, the 4-way case split from no_cross_1/no_cross_2 reduces to 2\<close>
      have pi1: "path_image g = g ` {0..t} \<union> g ` {t..1}"
        unfolding path_image_def using t(2,3)
        by (metis image_Un ivl_disj_un_two_touch(4) less_eq_real_def)
      from no_cross_1 no_cross_2 not_all_above not_all_below pi1
      show ?thesis by (auto simp: image_subset_iff)
    qed
    qed
  qed
  then show ?thesis
    using assms split_case split_case' t by blast
qed


subsection \<open>Conclusion of Green's theorem and the signed area formula for a convex closed curve.\<close>

lemma Green_invariant:
  assumes "\<And>g g' U b. Green g g' U 0 b \<Longrightarrow> Green_concl g g'"
  shows "Green_concl g g'"
proof -
  have *: "Green_concl ((\<lambda>x. -a+x) \<circ> g) g'"
  proof (intro assms)
    show "Green ((+) (- a) \<circ> g) g' U 0 (-a+b)"
    proof
      show "simple_path ((+) (- a) \<circ> g)"
        by (simp add: g simple_path_translation_eq)
      show "pathstart ((+) (- a) \<circ> g) = 0"
        by (simp add: g pathstart_compose)
      show "pathfinish ((+) (- a) \<circ> g) = 0"
        by (simp add: g pathfinish_compose)
      show "- a + b \<in> path_image ((+) (- a) \<circ> g)"
        by (simp add: b path_image_translation)
       show "dist 0 (- a + b) = diameter (path_image ((+) (- a) \<circ> g))"
         by (metis add.commute dab diameter_translation dist_0_norm dist_commute dist_norm path_image_compose pth_2)
      show "convex (inside (path_image ((+) (- a) \<circ> g)))"
        by (metis path_image_translation inside_translation convex_translation_eq conv)
      show "absolutely_continuous_on {0..1} ((+) (- a) \<circ> g)"
        by (metis (no_types, lifting) ext absolutely_continuous_on_add absolutely_continuous_on_const cont o_apply)
    next
      fix t
      assume "t \<in> {0..1} - U"
      then show "((+) (- a) \<circ> g has_vector_derivative g' t) (at t)"
        using has_vector_derivative_shift vder by blast
    qed (use b U in auto)
  qed
  show ?thesis
    unfolding Green_concl_def
  proof (intro conjI)
    show "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {0..1}"
    proof -
      have ai_translated: "(\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t)) absolutely_integrable_on {0..1}"
        using * unfolding Green_concl_def by auto
      have gp_ai: "g' absolutely_integrable_on {0..1}"
        using absolutely_integrable_absolutely_continuous_derivative[OF cont U]
          vder has_vector_derivative_at_within by blast
      have Re_gp_ai: "(\<lambda>t. Re (g' t)) absolutely_integrable_on {0..1}"
        using Re_absolutely_integrable_on gp_ai by blast
      have Ima_ai: "(\<lambda>t. Im a * Re (g' t)) absolutely_integrable_on {0..1}"
        using absolutely_integrable_scaleR_left[OF Re_gp_ai, of "Im a"]
        by (simp add: scaleR_conv_of_real)
      show ?thesis
      proof (rule absolutely_integrable_integrable_bound)
        fix t :: real assume "t \<in> {0..1}"
        show "norm (Re (g' t) * Im (g t)) \<le> \<bar>Re (g' t) * Im (((+) (- a) \<circ> g) t)\<bar> + \<bar>Im a * Re (g' t)\<bar>"
          by (simp add: o_def plus_complex.sel uminus_complex.sel real_norm_def algebra_simps)
      next
        show "(\<lambda>t. Re (g' t) * Im (g t)) integrable_on {0..1}"
          using absolutely_integrable_on_def f_abs_int by blast
        show "(\<lambda>t. \<bar>Re (g' t) * Im (((+) (- a) \<circ> g) t)\<bar> + \<bar>Im a * Re (g' t)\<bar>) integrable_on {0..1}"
          using ai_translated Ima_ai unfolding absolutely_integrable_on_def
          by (metis (no_types, lifting)  integrable_cong real_norm_def integrable_add)
      qed
    qed
  next
    show "\<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> = Sigma_Algebra.measure lebesgue (inside (path_image g))"
    proof -
      have meas_eq: "measure lebesgue (inside (path_image ((+) (- a) \<circ> g)))
                   = measure lebesgue (inside (path_image g))"
        by (metis path_image_translation inside_translation measure_translation)
      have int_g': "(g' has_integral 0) {0..1}"
      proof -
        have "(g' has_integral (g 1 - g 0)) {0..1}"
          using fundamental_theorem_of_calculus_absolutely_continuous[OF U _ cont, of g']
          by (metis le_numeral_extra(1) vder has_vector_derivative_at_within)
        then show ?thesis using g by (simp add: pathstart_def pathfinish_def)
      qed
      have Re_has_int: "((\<lambda>t. Re (g' t)) has_integral 0) {0..1}"
        using has_integral_Re[OF int_g'] by simp
      have Ima_has_int: "((\<lambda>t. Im a * Re (g' t)) has_integral 0) {0..1}"
        using has_integral_mult_right[OF Re_has_int] by simp
      have int_extra: "integral {0..1} (\<lambda>t. Im a * Re (g' t)) = 0"
        using integral_unique[OF Ima_has_int] .
      have translated_eq: "\<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t))\<bar>
                         = measure lebesgue (inside (path_image g))"
        using * unfolding Green_concl_def using meas_eq by auto
      have ai_translated: "(\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t)) integrable_on {0..1}"
        using * unfolding Green_concl_def absolutely_integrable_on_def by auto
      have Ima_integrable: "(\<lambda>t. Im a * Re (g' t)) integrable_on {0..1}"
        using Ima_has_int by (rule has_integral_integrable)
      have "integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))
          = integral {0..1} (\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t) + Im a * Re (g' t))"
        by (simp add: o_def plus_complex.sel uminus_complex.sel algebra_simps)
      also have "\<dots> = integral {0..1} (\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t))
                    + integral {0..1} (\<lambda>t. Im a * Re (g' t))"
        using integral_add[OF ai_translated Ima_integrable] .
      also have "\<dots> = integral {0..1} (\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t))"
        unfolding int_extra by simp
      finally show ?thesis
        using translated_eq by simp
    qed
  qed
qed

theorem area_theorem:
  obtains "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {0..1}"
    and "\<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> =
      measure lebesgue (inside (path_image g))"
  using Green.Green_area_zero Green_concl_def Green_invariant by blast

end

section \<open>Part 3: Isoperimetric theorem for convex curves\<close>

text \<open>The kernel lemma: the isoperimetric inequality for a convex curve that has been
  normalized to arc-length parametrization with zero-mean imaginary part and
  diameter along the real axis starting at a point with Re = 0.
  This is where the Wirtinger inequality is applied.\<close>

lemma isoperimetric_kernel:
  fixes g :: "real \<Rightarrow> complex" and L :: real and a b :: complex
  assumes "0 < L"
    and conv_in: "convex (inside (path_image g))"
    and ab: "a \<in> path_image g" "b \<in> path_image g"
    and dist_ab: "dist a b = diameter (path_image g)"
    and bma: "b - a = of_real (dist a b)"
    and ga: "pathstart g = a" "pathfinish g = a"
    and g: "rectifiable_path g" "simple_path g"
    and L: "path_length g = L"
    and arc_length: "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t g) = L * t"
    and lipschitz: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g x) (g y) \<le> L * dist x y"
    and "Re a = 0"
    and "(Im \<circ> g has_integral 0) {0..1}"
  shows "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
      \<exists>c r. path_image g = sphere c r"
proof -
  have acont_g: "absolutely_continuous_on {0..1} g"
    by (rule Lipschitz_imp_absolutely_continuous)
       (use lipschitz in \<open>auto simp: dist_norm dist_real_def\<close>)
  define S where "S = {x \<in> {0..1}. \<not> g differentiable (at x)}"
  have negS: "negligible S"
    unfolding S_def using Lebesgue_differentiation_theorem_compact
    by (metis (full_types) absolutely_continuous_on_imp_has_bounded_variation_on
        acont_g cbox_interval compact_Icc compact_imp_bounded)
  define g' where "g' = (\<lambda>x. vector_derivative g (at x))"
  have g'_deriv: "\<And>x. x \<in> {0..1} - S \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
    by (simp add: S_def g'_def vector_derivative_works)
  have g'_int: "g' absolutely_integrable_on {0..t} \<and> integral {0..t} g' = g t - a" 
    if "t \<in> {0..1::real}" for t
  proof -
    have lhs: "g' absolutely_integrable_on {0..1} \<and> (\<forall>x\<in>{0..1}. (g' has_integral g x - g 0) {0..x})"
      unfolding absolute_integral_absolutely_continuous_derivative_eq
      by (metis has_vector_derivative_at_within acont_g negS g'_deriv)
    have "0 \<le> t" "t \<le> 1" using that by auto
    have abs_int_t: "g' absolutely_integrable_on {0..t}"
      using absolutely_integrable_on_subinterval[OF conjunct1[OF lhs]] \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> by auto
    moreover have "integral {0..t} g' = g t - a"
      using ga by (metis integral_unique lhs pathstart_def that)
    ultimately show "g' absolutely_integrable_on {0..t} \<and> integral {0..t} g' = g t - a"
      by auto
  qed
  have norm_g'_int: "(\<lambda>x. norm (g' x)) absolutely_integrable_on {0..t} \<and> integral {0..t} (\<lambda>x. norm (g' x)) = L * t"
    if "t \<in> {0..1}" for t
  proof -
    have acont_gt: "absolutely_continuous_on {0..t} g"
      using absolutely_continuous_on_subset[OF acont_g] that by auto
    have g'_deriv_t: "\<And>x. x \<in> {0..t} - S \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
      using g'_deriv that by auto
    have "vector_variation {0..t} g = integral {0..t} (\<lambda>u. norm (g' u))"
      using vector_variation_integral_norm_derivative[OF negS _ acont_gt g'_deriv_t] that
      by presburger
    moreover have "vector_variation {0..t} g = L * t"
      using that \<open>rectifiable_path g\<close> path_length_subpath_eq [of 0 t, symmetric] arc_length
      by (fastforce simp: closed_segment_eq_real_ivl1)
    moreover have "(\<lambda>x. norm (g' x)) absolutely_integrable_on {0..t}"
      using g'_int set_integrable_norm that by blast
    ultimately show ?thesis
      using that by auto
  qed
  have norm_g'_le: "norm (g' x) \<le> L" if "x \<in> {0..1} - S" for x
  proof -
    from that have x01: "x \<in> {0..1}" and "x \<notin> S" by auto
    have gd: "(g has_vector_derivative g' x) (at x)" using g'_deriv that by auto
    have xlimpt: "x islimpt {0..1::real}"
      using limpt_of_convex[of "{0..1::real}" x] x01 by auto
    have gd_within: "(g has_vector_derivative g' x) (at x within {0..1})"
      using gd has_vector_derivative_at_within by blast
    have Ld: "((\<lambda>t. L * t) has_vector_derivative L) (at x within {0..1})"
      using has_vector_derivative_mult_right[OF has_vector_derivative_id] by simp
    have ev: "\<forall>\<^sub>F y in at x within {0..1}. norm (g y - g x) \<le> norm (L * y - L * x)"
      unfolding eventually_at_filter
    proof (intro always_eventually allI impI)
      fix y assume "y \<noteq> x" "y \<in> {0..1}"
      have "dist (g y) (g x) \<le> L * dist y x"
        using lipschitz \<open>y \<in> {0..1}\<close> x01 by auto
      then have "norm (g y - g x) \<le> L * \<bar>y - x\<bar>"
        by (simp add: dist_norm dist_real_def)
      also have "\<dots> = \<bar>L * (y - x)\<bar>"
        using \<open>0 < L\<close> by (simp add: abs_mult)
      also have "\<dots> = norm (L * y - L * x)"
        by (simp add: real_norm_def right_diff_distrib)
      finally show "norm (g y - g x) \<le> norm (L * y - L * x)" .
    qed
    from norm_vector_derivatives_le_within[OF xlimpt gd_within Ld ev]
    show "norm (g' x) \<le> L"
      using \<open>0 < L\<close> by simp
  qed

  have norm_g'_sq_int: "(\<lambda>x. (norm (g' x))\<^sup>2) absolutely_integrable_on {0..1}"
  proof (rule measurable_bounded_by_integrable_imp_absolutely_integrable_ae)
    show "(\<lambda>x. (norm (g' x))\<^sup>2) \<in> borel_measurable (lebesgue_on {0..1})"
    proof -
      have "g' \<in> borel_measurable (lebesgue_on {0..1})"
        using absolutely_integrable_imp_borel_measurable[OF conjunct1[OF g'_int[of 1]]]
        by auto
      then have "(\<lambda>x. norm (g' x)) \<in> borel_measurable (lebesgue_on {0..1})"
        using measurable_comp[OF _ borel_measurable_norm] by (simp add: comp_def)
      then show ?thesis
        by (rule borel_measurable_power)
    qed
    show "negligible S" by (rule negS)
    fix x assume "x \<in> {0..1} - S"
    then have "norm (g' x) \<le> L" using norm_g'_le by auto
    then have "(norm (g' x))\<^sup>2 \<le> L\<^sup>2"
      using \<open>0 < L\<close> by (intro power_mono) auto
    then show "norm ((norm (g' x))\<^sup>2) \<le> L\<^sup>2"
      by simp
  qed auto

  have integral_norm_g'_sq: "integral\<^sup>L (lebesgue_on {0..1}) (\<lambda>x. (norm (g' x))\<^sup>2) = L\<^sup>2"
  proof -
    let ?int01 = "{0..1::real}"
    have meas01: "?int01 \<in> sets lebesgue" by simp
    \<comment> \<open>norm(g') is integrable on lebesgue_on {0..1}\<close>
    have norm_g'_abs: "(\<lambda>x. norm (g' x)) absolutely_integrable_on {0..1}"
      using norm_g'_int[of 1] by auto
    have norm_g'_leb: "integrable (lebesgue_on {0..1}) (\<lambda>x. norm (g' x))"
      by (rule absolutely_integrable_imp_integrable[OF norm_g'_abs meas01])
    \<comment> \<open>Its Lebesgue integral equals L\<close>
    have int_norm_g': "integral\<^sup>L (lebesgue_on {0..1}) (\<lambda>x. norm (g' x)) = L"
      by (simp add: lebesgue_integral_eq_integral norm_g'_int norm_g'_leb)
    \<comment> \<open>The constant L is integrable with integral L\<close>
    have const_leb: "integrable (lebesgue_on {0..1}) (\<lambda>x::real. L)"
      by (simp add: integrable_const_ivl)
    have int_const: "integral\<^sup>L (lebesgue_on {0..1}) (\<lambda>x::real. L) = L"
      using lebesgue_integral_const[of "lebesgue_on {0..1}" L]
      by (simp add: measure_restrict_space)
    \<comment> \<open>norm(g' x) \<le> L a.e.\<close>
    have ae_le: "AE x in lebesgue_on {0..1}. norm (g' x) \<le> L"
    proof -
      have "S \<inter> {0..1} \<in> null_sets (lebesgue_on {0..1})"
        using negS negligible_iff_null_sets null_sets_restrict_space
        by (metis inf_le2 meas01 null_set_Int2)
      then have "AE x in lebesgue_on {0..1}. x \<notin> S"
        by (metis AE_not_in Collect_subset S_def inf.orderE)
      then show ?thesis
        using norm_g'_le by (auto elim: eventually_mono)
    qed
    \<comment> \<open>Therefore norm(g' x) = L a.e.\<close>
    have ae_eq: "AE x in lebesgue_on {0..1}. norm (g' x) = L"
      using integral_ineq_eq_0_then_AE[OF ae_le norm_g'_leb const_leb] int_norm_g' int_const
      by simp
    \<comment> \<open>Therefore (norm(g' x))² = L² a.e.\<close>
    have ae_sq: "AE x in lebesgue_on {0..1}. (norm (g' x))\<^sup>2 = L\<^sup>2"
      using ae_eq by (rule AE_mp) auto
    \<comment> \<open>Conclude by integral_cong_AE\<close>
    have meas_sq: "(\<lambda>x. (norm (g' x))\<^sup>2) \<in> borel_measurable (lebesgue_on {0..1})"
    proof -
      have "g' \<in> borel_measurable (lebesgue_on {0..1})"
        using absolutely_integrable_imp_borel_measurable[OF conjunct1[OF g'_int[of 1]]]
        by auto
      then have "(\<lambda>x. norm (g' x)) \<in> borel_measurable (lebesgue_on {0..1})"
        using measurable_comp[OF _ borel_measurable_norm] by (simp add: comp_def)
      then show ?thesis by (rule borel_measurable_power)
    qed
    have "integral\<^sup>L (lebesgue_on ?int01) (\<lambda>x. (norm (g' x))\<^sup>2) =
          integral\<^sup>L (lebesgue_on ?int01) (\<lambda>x. L\<^sup>2)"
      by (rule integral_cong_AE[OF meas_sq _ ae_sq]) simp
    also have "\<dots> = L\<^sup>2"
      using lebesgue_integral_const[of "lebesgue_on ?int01" "L\<^sup>2"]
      by (simp add: measure_restrict_space)
    finally show ?thesis .
  qed

  text \<open>Use the Green formula for the area inside the curve.\<close>
  have green_ai: "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {0..1}"
    and green_area: "\<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> =
      measure lebesgue (inside (path_image g))"
  proof -
    have "Re a < Re b"
    proof -
      have "dist a b > 0"
        using \<open>0 < L\<close> L dist_ab diameter_ge_0 g(1) order_less_le \<comment> \<open>TODO: simplify\<close>
        by (metis path_image_nonempty Diff_cancel ab(1) assms(7,8) bounded_simple_path_image diameter_eq_0
            g(2) insert_absorb nonempty_simple_path_endless singletonD)
      then show ?thesis
        by (metis Re_complex_of_real assms(14,6) diff_0_right minus_complex.sel(1))
    qed
    moreover have "Im a = Im b"
      using bma by (simp add: complex_of_real_def complex_eq_iff)
    ultimately interpret G: Green g g' S a b
    proof unfold_locales
      show "simple_path g" using g by auto
      show "pathstart g = a" "pathfinish g = a" using ga by auto
      show "b \<in> path_image g" using ab by auto
      show "dist a b = diameter (path_image g)" using dist_ab .
      show "convex (inside (path_image g))" using conv_in .
      show "absolutely_continuous_on {0..1} g" using acont_g .
      show "negligible S" using negS .
      show "\<And>t. t \<in> {0..1} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
        using g'_deriv by auto
    qed auto
    from G.area_theorem show "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {0..1}"
      and "\<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> =
        measure lebesgue (inside (path_image g))"
      by (metis (full_types))+
  qed

  obtain sgn :: real where sgn2: "sgn\<^sup>2 = 1"
    and has_int_green: "((\<lambda>t. Re (g' t) * Im (g t)) has_integral
      (sgn * measure lebesgue (inside (path_image g)))) {0..1}"
  proof -
    have integrable: "(\<lambda>t. Re (g' t) * Im (g t)) integrable_on {0..1}"
      using green_ai absolutely_integrable_on_def by blast
    show thesis
    proof (cases "integral {0..1} (\<lambda>t. Re (g' t) * Im (g t)) \<ge> 0")
      case True
      then have eq: "integral {0..1} (\<lambda>t. Re (g' t) * Im (g t)) =
        measure lebesgue (inside (path_image g))"
        using green_area by (simp add: abs_if split: if_splits)
      have "((\<lambda>t. Re (g' t) * Im (g t)) has_integral
        (1 * measure lebesgue (inside (path_image g)))) {0..1}"
        using integrable eq by (simp add: has_integral_integrable_integral)
      then show thesis using that[of 1] by simp
    next
      case False
      then have eq: "integral {0..1} (\<lambda>t. Re (g' t) * Im (g t)) =
        - measure lebesgue (inside (path_image g))"
        using green_area by (simp add: abs_if split: if_splits)
      have "((\<lambda>t. Re (g' t) * Im (g t)) has_integral
        ((-1) * measure lebesgue (inside (path_image g)))) {0..1}"
        using integrable eq by (simp add: has_integral_integrable_integral)
      then show thesis using that[of "-1"] by simp
    qed
  qed

  have has_int_norm_sq: "((\<lambda>x. (norm (g' x))\<^sup>2) has_integral L\<^sup>2) {0..1}"
  proof -
    have int_on: "(\<lambda>x. (norm (g' x))\<^sup>2) integrable_on {0..1}"
      using norm_g'_sq_int absolutely_integrable_on_def by blast
    have "integral {0..1} (\<lambda>x. (norm (g' x))\<^sup>2) = L\<^sup>2"
      using integral_norm_g'_sq norm_g'_sq_int
        lebesgue_integral_eq_integral[of "{0..1}" "\<lambda>x. (norm (g' x))\<^sup>2"]
        absolutely_integrable_imp_integrable[OF norm_g'_sq_int]
      by auto
    then show ?thesis
      using int_on by (simp add: has_integral_integrable_integral)
  qed

  have has_int_key: "((\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2 +
    (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2) has_integral
    (L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi)) {0..1}"
  proof -
    have sgn_sq: "sgn * sgn = 1" using sgn2 by (metis power2_eq_square)
    have integrand_eq: "\<And>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2 +
      (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2 =
      (norm (g' x))\<^sup>2 - 4 * pi * sgn * Re (g' x) * Im (g x)"
    proof -
      fix x
      have "(Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2 +
        (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2 =
        (Re (g' x))\<^sup>2 + (Im (g' x))\<^sup>2 - 4 * pi * sgn * Re (g' x) * Im (g x)"
        using sgn_sq by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> = (norm (g' x))\<^sup>2 - 4 * pi * sgn * Re (g' x) * Im (g x)"
        by (simp add: cmod_power2)
      finally show "(Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2 +
        (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2 =
        (norm (g' x))\<^sup>2 - 4 * pi * sgn * Re (g' x) * Im (g x)" .
    qed
    have scaled_green: "((\<lambda>t. 4 * pi * sgn * (Re (g' t) * Im (g t))) has_integral
      (4 * pi * sgn * (sgn * measure lebesgue (inside (path_image g))))) {0..1}"
      using has_integral_mult_right[OF has_int_green, of "4 * pi * sgn"] .
    have val: "4 * pi * sgn * (sgn * measure lebesgue (inside (path_image g))) =
      measure lebesgue (inside (path_image g)) * 4 * pi"
      using sgn_sq by (simp add: algebra_simps)
    have scaled_green': "((\<lambda>t. 4 * pi * sgn * Re (g' t) * Im (g t)) has_integral
      (measure lebesgue (inside (path_image g)) * 4 * pi)) {0..1}"
      using scaled_green unfolding val by (simp add: algebra_simps)
    have "((\<lambda>x. (norm (g' x))\<^sup>2 - 4 * pi * sgn * Re (g' x) * Im (g x)) has_integral
      (L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi)) {0..1}"
      using has_integral_diff[OF has_int_norm_sq scaled_green'] by (simp add: algebra_simps)
    then show ?thesis
      by (simp add: integrand_eq)
  qed

  have key: "0 \<le> L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi \<and>
             (L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi = 0 \<longrightarrow>
             (\<exists>c r. path_image g = sphere c r))"
  proof (cases "inside(path_image g) = {}")
    case False
    have Im_g'_has_int: "((\<lambda>t. Im (g' t)) has_integral (Im (g x) - Im (g 0))) {0..x}"
      if "x \<in> {0..1}" for x
    proof -
      have "(g' has_integral (g x - a)) {0..x}"
        by (metis g'_int has_integral_iff set_lebesgue_integral_eq_integral(1)
            that)
      then have "((\<lambda>t. Im (g' t)) has_integral Im (g x - a)) {0..x}"
        by (rule has_integral_Im)
      then show ?thesis
        using ga by (simp add: pathstart_def)
    qed
    have Im_g_periodic: "Im (g 1) = Im (g 0)"
      using ga by (simp add: pathstart_def pathfinish_def)
    have Im_g_zero_mean: "((\<lambda>x. Im (g x)) has_integral 0) {0..1}"
      using assms by (simp add: o_def)
    have Im_g'_sq_int: "(\<lambda>x. (Im (g' x))\<^sup>2) integrable_on {0..1}"
    proof -
      have "(\<lambda>x. (Im (g' x))\<^sup>2) absolutely_integrable_on {0..1}"
      proof (rule measurable_bounded_by_integrable_imp_absolutely_integrable_ae)
        show "(\<lambda>x. (Im (g' x))\<^sup>2) \<in> borel_measurable (lebesgue_on {0..1})"
        proof -
          have "g' \<in> borel_measurable (lebesgue_on {0..1})"
            using absolutely_integrable_imp_borel_measurable[OF conjunct1[OF g'_int[of 1]]]
            by auto
          then show ?thesis
            using borel_measurable_complex_iff borel_measurable_power by blast
        qed
        show "negligible S" by (rule negS)
        fix x assume "x \<in> {0..1} - S"
        then have "norm (g' x) \<le> L" using norm_g'_le by auto
        then show "norm ((Im (g' x))\<^sup>2) \<le> L\<^sup>2"
          by (metis abs_Im_le_cmod landau_omega.R_trans norm_ge_zero norm_power power_mono real_norm_def)
      qed auto
      then show ?thesis
        using absolutely_integrable_on_def by blast
    qed
    have wirt1: "(\<lambda>x. (Im (g x))\<^sup>2) integrable_on {0..1}"
      and wirt2: "integral {0..1} (\<lambda>x. (2*pi * Im (g x))\<^sup>2) \<le> integral {0..1} (\<lambda>x. (Im (g' x))\<^sup>2)"
      and wirt3: "integral {0..1} (\<lambda>x. (2*pi * Im (g x))\<^sup>2) = integral {0..1} (\<lambda>x. (Im (g' x))\<^sup>2) \<Longrightarrow>
        \<exists>c a. \<forall>x \<in> {0..1}. Im (g x) = c * sin (2*pi*x - a)"
      using scaled_Wirtinger_inequality[OF Im_g'_has_int Im_g_periodic Im_g_zero_mean Im_g'_sq_int]
      by auto
    obtain w where "((\<lambda>x. (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2) has_integral w) {0..1}"
    proof -
      have sq: "(\<lambda>x. (2 * pi * Im (g x))\<^sup>2) integrable_on {0..1}"
        using integrable_cmul[OF wirt1, of "(2*pi)\<^sup>2"]
        by (simp add: power_mult_distrib mult.commute)
      with that show ?thesis
        using integrable_diff[OF Im_g'_sq_int sq] by force
    qed
    have w_nonneg: "0 \<le> w"
      and w_zero: "w = 0 \<Longrightarrow> \<exists>c a. \<forall>x \<in> {0..1}. Im (g x) = c * sin (2*pi*x - a)"
    proof -
      have "((\<lambda>x. (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2) has_integral w) {0..1}"
        using \<open>((\<lambda>x. (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2) has_integral w) {0..1}\<close> .
      then have w_eq: "w = integral {0..1} (\<lambda>x. (Im (g' x))\<^sup>2) - integral {0..1} (\<lambda>x. (2 * pi * Im (g x))\<^sup>2)"
      proof -
        have "w = integral {0..1} (\<lambda>x. (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2)"
          using \<open>((\<lambda>x. (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2) has_integral w) {0..1}\<close>
          by (simp add: integral_unique)
        also have "\<dots> = integral {0..1} (\<lambda>x. (Im (g' x))\<^sup>2) - integral {0..1} (\<lambda>x. (2 * pi * Im (g x))\<^sup>2)"
        proof -
          have sq: "(\<lambda>x. (2 * pi * Im (g x))\<^sup>2) integrable_on {0..1}"
            using integrable_cmul[OF wirt1, of "(2*pi)\<^sup>2"]
            by (simp add: power_mult_distrib mult.commute)
          show ?thesis
            using integral_diff[OF Im_g'_sq_int sq] by simp
        qed
        finally show ?thesis .
      qed
      show "0 \<le> w"
        using w_eq wirt2 by linarith
      show "w = 0 \<Longrightarrow> \<exists>c a. \<forall>x \<in> {0..1}. Im (g x) = c * sin (2*pi*x - a)"
      proof -
        assume "w = 0"
        then have "integral {0..1} (\<lambda>x. (2*pi * Im (g x))\<^sup>2) = integral {0..1} (\<lambda>x. (Im (g' x))\<^sup>2)"
          using w_eq by linarith
        then show "\<exists>c a. \<forall>x \<in> {0..1}. Im (g x) = c * sin (2*pi*x - a)"
          using wirt3 by blast
      qed
    qed
    define d where "d = L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi - w"
    have key_eq: "L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi = d + w"
      unfolding d_def by linarith

    have sq_has_int: "((\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2) has_integral d) {0..1}"
    proof -
      have "((\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2 + ((Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2)
        - ((Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2)) has_integral
        (L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi - w)) {0..1}"
        using has_integral_diff[OF has_int_key
          \<open>((\<lambda>x. (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2) has_integral w) {0..1}\<close>]
        by simp
      then show ?thesis
        unfolding d_def by simp
    qed
    have d_nonneg: "0 \<le> d"
    proof -
      have sq_int: "(\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2) integrable_on {0..1}"
        using has_integral_integrable[OF sq_has_int] .
      have "0 \<le> integral {0..1} (\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2)"
        by (rule integral_nonneg[OF sq_int]) (simp add: zero_le_power2)
      then show "0 \<le> d"
        using integral_unique[OF sq_has_int] by linarith
    qed
    have dw_nonneg: "0 \<le> d + w"
      using d_nonneg w_nonneg by linarith
    moreover have "\<exists>c r. path_image g = sphere c r" 
      if "d + w = 0"
    proof -
      have d0: "d = 0" and w0: "w = 0"
        using that d_nonneg w_nonneg by linarith+
      obtain C A where CA: "\<And>x. x \<in> {0..1} \<Longrightarrow> Im (g x) = C * sin (2*pi*x - A)"
        using w_zero[OF w0] by blast
      have sq_zero: "((\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2) has_integral 0) {0..1}"
        using sq_has_int d0 by simp
      have neg_Re: "negligible {x \<in> {0..1}. Re (g' x) - 2 * pi * sgn * Im (g x) \<noteq> 0}"
      proof -
        have sq_abs: "(\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2) absolutely_integrable_on {0..1}"
          using nonnegative_absolutely_integrable_1[OF has_integral_integrable[OF sq_zero]]
          by (simp add: zero_le_power2)
        have sq_leb: "integrable (lebesgue_on {0..1}) (\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2)"
          by (rule absolutely_integrable_imp_integrable[OF sq_abs]) simp
        have leb_zero: "integral\<^sup>L (lebesgue_on {0..1}) (\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2) = 0"
          using lebesgue_integral_eq_integral[OF sq_leb] integral_unique[OF sq_zero] by simp
        have "AE x in lebesgue_on {0..1}. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2 = 0"
          using integral_nonneg_eq_0_iff_AE[OF sq_leb] leb_zero
          by (simp add: zero_le_power2)
        then have "AE x in lebesgue_on {0..1}. Re (g' x) - 2 * pi * sgn * Im (g x) = 0"
          by (rule AE_mp) (auto simp: power2_eq_square)
        then show ?thesis
        proof -
          assume ae: "AE x in lebesgue_on {0..1}. Re (g' x) - 2 * pi * sgn * Im (g x) = 0"
          from ae[unfolded eventually_ae_filter[of _ "lebesgue_on {0..1}"]]
          obtain N0 where N0: "N0 \<in> null_sets (lebesgue_on {0..1})"
            and sub: "{x \<in> space (lebesgue_on {0..1}). Re (g' x) - 2 * pi * sgn * Im (g x) \<noteq> 0} \<subseteq> N0"
            by auto
          have "negligible N0"
          proof -
            have "{0..1::real} \<in> sets lebesgue" by simp
            then have "(N0 \<in> null_sets (lebesgue_on {0..1})) = (N0 \<subseteq> {0..1} \<and> N0 \<in> null_sets lebesgue)"
              using null_sets_restrict_space[of "{0..1}" lebesgue N0] by simp
            then show ?thesis
              using N0 negligible_iff_null_sets by auto
          qed

          moreover have "{x \<in> {0..1}. Re (g' x) - 2 * pi * sgn * Im (g x) \<noteq> 0} \<subseteq> N0"
            using sub by (auto simp: space_lebesgue_on)
          ultimately show ?thesis
            by (meson negligible_subset)
        qed
      qed
      have neg_Re': "negligible {x \<in> {0..1}. Re (g' x) - 2 * pi * sgn * C * sin (2*pi*x - A) \<noteq> 0}"
      proof -
        have "{x \<in> {0..1}. Re (g' x) - 2 * pi * sgn * C * sin (2*pi*x - A) \<noteq> 0}
            = {x \<in> {0..1}. Re (g' x) - 2 * pi * sgn * Im (g x) \<noteq> 0}"
          using CA by auto
        then show ?thesis using neg_Re by simp
      qed

      have Re_g: "Re (g x) = - sgn * C * (cos (2*pi*x - A) - cos A)"
        if "x \<in> {0..1}" for x
      proof -
        have x01: "0 \<le> x" "x \<le> 1" using that by auto
        \<comment> \<open>Step 1: integral of Re(g') over {0..x} = Re(g x)\<close>
        have Re_g'_int: "((\<lambda>t. Re (g' t)) has_integral Re (g x)) {0..x}"
        proof -
          have "(g' has_integral (g x - a)) {0..x}"
          proof -
            have "g' absolutely_integrable_on {0..x}"
              using g'_int[OF that] by auto
            moreover have "integral {0..x} g' = g x - a"
              using g'_int[OF that] by auto
            ultimately show ?thesis
              by (metis absolutely_integrable_on_def has_integral_integrable_integral)
          qed
          then have "((\<lambda>t. Re (g' t)) has_integral Re (g x - a)) {0..x}"
            by (rule has_integral_Re)
          then show ?thesis using \<open>Re a = 0\<close> by simp
        qed
        \<comment> \<open>Step 2: integral of 2*pi*sgn*C*sin(2*pi*t - A) over {0..x}\<close>
        have sin_int: "((\<lambda>t. 2 * pi * sgn * C * sin (2 * pi * t - A)) has_integral
          (- sgn * C * (cos (2 * pi * x - A) - cos A))) {0..x}"
        proof -
          have hvd: "((\<lambda>t. - sgn * C * cos (2 * pi * t - A)) has_vector_derivative
            2 * pi * sgn * C * sin (2 * pi * t - A)) (at t within {0..x})" for t
          proof -
            have "((\<lambda>t. - sgn * C * cos (2 * pi * t - A)) has_real_derivative
              - sgn * C * (- sin (2 * pi * t - A)) * (2 * pi)) (at t)"
              by (auto intro!: derivative_eq_intros simp: algebra_simps)
            then have "((\<lambda>t. - sgn * C * cos (2 * pi * t - A)) has_real_derivative
              2 * pi * sgn * C * sin (2 * pi * t - A)) (at t)"
              by (simp add: algebra_simps)
            then show ?thesis
              by (simp add: has_real_derivative_iff_has_vector_derivative
                has_vector_derivative_at_within)
          qed
          have "((\<lambda>t. 2 * pi * sgn * C * sin (2 * pi * t - A)) has_integral
            ((- sgn * C * cos (2 * pi * x - A)) - (- sgn * C * cos (2 * pi * 0 - A)))) {0..x}"
            using fundamental_theorem_of_calculus[OF \<open>0 \<le> x\<close> hvd] by simp
          then show ?thesis by (simp add: algebra_simps)
        qed
        \<comment> \<open>Step 3: integral of the difference = Re(g x) - (-sgn*C*(cos(\<dots>) - cos A))\<close>
        have diff_int: "((\<lambda>t. Re (g' t) - 2 * pi * sgn * C * sin (2 * pi * t - A)) has_integral
          (Re (g x) - (- sgn * C * (cos (2 * pi * x - A) - cos A)))) {0..x}"
          using has_integral_diff[OF Re_g'_int sin_int] by simp
        \<comment> \<open>Step 4: the integrand is 0 a.e. (from neg_Re'), so integral = 0\<close>
        have zero_int: "((\<lambda>t. Re (g' t) - 2 * pi * sgn * C * sin (2 * pi * t - A)) has_integral 0) {0..x}"
        proof -
          have neg_sub: "negligible {t \<in> {0..x}. Re (g' t) - 2 * pi * sgn * C * sin (2 * pi * t - A) \<noteq> 0}"
          proof (rule negligible_subset[OF neg_Re'])
            show "{t \<in> {0..x}. Re (g' t) - 2 * pi * sgn * C * sin (2 * pi * t - A) \<noteq> 0}
              \<subseteq> {x \<in> {0..1}. Re (g' x) - 2 * pi * sgn * C * sin (2 * pi * x - A) \<noteq> 0}"
              using x01 by auto
          qed
          show ?thesis
          proof (rule has_integral_spike[OF neg_sub _ has_integral_0])
            fix t assume "t \<in> {0..x} - {t \<in> {0..x}. Re (g' t) - 2 * pi * sgn * C * sin (2 * pi * t - A) \<noteq> 0}"
            then show "Re (g' t) - 2 * pi * sgn * C * sin (2 * pi * t - A) = (0::real)"
              by auto
          qed
        qed
        \<comment> \<open>Step 5: by uniqueness of integrals\<close>
        show ?thesis
          using has_integral_unique[OF diff_int zero_int] by linarith
      qed
      \<comment> \<open>Final step: path_image g = sphere c |C|\<close>
      define c where "c = Complex (sgn * C * cos A) 0"
      have subset: "path_image g \<subseteq> sphere c \<bar>C\<bar>"
      proof -
        have "cmod (g t - c) = \<bar>C\<bar>" if "t \<in> {0..1}" for t
        proof -
          have re: "Re (g t) = - sgn * C * (cos (2*pi*t - A) - cos A)"
            using Re_g[OF that] .
          have im: "Im (g t) = C * sin (2*pi*t - A)"
            using CA[OF that] .
          have eq_gt: "g t - c = Complex (- sgn * C * cos (2*pi*t - A)) (C * sin (2*pi*t - A))"
          proof (rule complex_eqI)
            show "Re (g t - c) = Re (Complex (- sgn * C * cos (2*pi*t - A)) (C * sin (2*pi*t - A)))"
              unfolding c_def using re by (simp add: algebra_simps)
            show "Im (g t - c) = Im (Complex (- sgn * C * cos (2*pi*t - A)) (C * sin (2*pi*t - A)))"
              unfolding c_def using im by simp
          qed
          have "(cmod (g t - c))\<^sup>2 = (sgn * C * cos (2*pi*t - A))\<^sup>2 + (C * sin (2*pi*t - A))\<^sup>2"
            using eq_gt by (simp add: complex_norm power2_eq_square)
          also have "\<dots> = C\<^sup>2 * (sgn\<^sup>2 * (cos (2*pi*t - A))\<^sup>2 + (sin (2*pi*t - A))\<^sup>2)"
            by (simp add: algebra_simps power2_eq_square)
          also have "\<dots> = C\<^sup>2 * ((cos (2*pi*t - A))\<^sup>2 + (sin (2*pi*t - A))\<^sup>2)"
            using sgn2 by simp
          also have "\<dots> = C\<^sup>2"
            by (simp add: sin_cos_squared_add3)
          also have "\<dots> = \<bar>C\<bar>\<^sup>2"
            by (simp add: power2_abs)
          finally show "cmod (g t - c) = \<bar>C\<bar>"
            by (rule power2_eq_imp_eq) auto
        qed
        then show ?thesis
          by (auto simp: path_image_def sphere_def dist_norm norm_minus_commute)
      qed
      have supset: "sphere c \<bar>C\<bar> \<subseteq> path_image g"
      proof (cases "C = 0")
        case True
        then have "sphere c \<bar>C\<bar> = {c}" by (simp add: sphere_def dist_self)
        moreover have "g 0 = c"
        proof (rule complex_eqI)
          show "Re (g 0) = Re c"
            using Re_g[of 0] by (simp add: c_def True)
          show "Im (g 0) = Im c"
            using CA[of 0] by (simp add: c_def True)
        qed
        moreover have "g 0 \<in> path_image g"
          by (simp add: path_image_def)
        ultimately show ?thesis by auto
      next
        case Cne: False
        show ?thesis
        proof (rule subsetI)
          fix z assume z: "z \<in> sphere c \<bar>C\<bar>"
          then have zc_norm: "cmod (z - c) = \<bar>C\<bar>"
            by (simp add: sphere_def dist_norm norm_minus_commute)
          \<comment> \<open>Find angle for (z-c) scaled to unit circle\<close>
          have unit: "cmod (Complex (- Re (z - c) / (sgn * C)) (Im (z - c) / C)) = 1"
          proof -
            have "(cmod (Complex (- Re (z - c) / (sgn * C)) (Im (z - c) / C)))\<^sup>2
                = (Re (z - c))\<^sup>2 / (sgn\<^sup>2 * C\<^sup>2) + (Im (z - c))\<^sup>2 / C\<^sup>2"
              by (metis (no_types, opaque_lifting) cmod_power2 complex.sel(1,2) power2_minus
                  power_divide power_mult_distrib)
            also have "\<dots> = ((Re (z - c))\<^sup>2 + (Im (z - c))\<^sup>2) / C\<^sup>2"
              using sgn2 by (simp add: add_divide_distrib)
            also have "\<dots> = (cmod (z - c))\<^sup>2 / C\<^sup>2"
              by (simp add: cmod_power2)
            also have "\<dots> = \<bar>C\<bar>\<^sup>2 / C\<^sup>2"
              using zc_norm by simp
            also have "\<dots> = 1"
              using Cne by (simp add: power2_abs)
            finally show ?thesis
              using norm_ge_zero
              by (simp add: abs_square_eq_1)
          qed
          \<comment> \<open>Get angle \<theta>\<close>
          obtain \<theta> where \<theta>_bounds: "0 \<le> \<theta>" "\<theta> < 2*pi"
            and \<theta>_eq: "Complex (- Re (z - c) / (sgn * C)) (Im (z - c) / C) = Complex (cos \<theta>) (sin \<theta>)"
            using complex_unimodular_polar[OF unit] by auto
          have \<theta>_Re: "- Re (z - c) / (sgn * C) = cos \<theta>"
            and \<theta>_Im: "Im (z - c) / C = sin \<theta>"
            using \<theta>_eq by (simp_all add: complex.expand)
          \<comment> \<open>Find t \<in> [0,1] with 2\<pi>t - A \<equiv> \<theta> (mod 2\<pi>)\<close>
          define t where "t = frac ((\<theta> + A) / (2 * pi))"
          have t01: "t \<in> {0..1}"
          proof -
            have "0 \<le> frac ((\<theta> + A) / (2 * pi))" by (rule frac_ge_0)
            moreover have "frac ((\<theta> + A) / (2 * pi)) < 1" by (rule frac_lt_1)
            ultimately show ?thesis unfolding t_def by auto
          qed
          have angle_eq: "cos (2*pi*t - A) = cos \<theta>" "sin (2*pi*t - A) = sin \<theta>"
          proof -
            have *: "2*pi*t = (\<theta> + A) - of_int \<lfloor>(\<theta> + A) / (2*pi)\<rfloor> * (2*pi)"
            proof -
              have "t = (\<theta> + A) / (2*pi) - of_int \<lfloor>(\<theta> + A) / (2*pi)\<rfloor>"
                unfolding t_def frac_def by simp
              then have "2*pi*t = 2*pi * ((\<theta> + A) / (2*pi) - of_int \<lfloor>(\<theta> + A) / (2*pi)\<rfloor>)"
                by simp
              also have "\<dots> = (\<theta> + A) - of_int \<lfloor>(\<theta> + A) / (2*pi)\<rfloor> * (2*pi)"
                using pi_gt_zero by (simp add: field_simps)
              finally show ?thesis .
            qed
            have eq: "2*pi*t - A = \<theta> - of_int \<lfloor>(\<theta> + A) / (2*pi)\<rfloor> * (2*pi)"
              using * by linarith
            show "cos (2*pi*t - A) = cos \<theta>"
              unfolding eq
              by (simp add: cos_diff mult_of_int_commute)
            show "sin (2*pi*t - A) = sin \<theta>"
              unfolding eq by (simp add: mult_of_int_commute sin_diff)
        qed
          \<comment> \<open>Show g t = z\<close>
          have "g t = z"
          proof (rule complex_eqI)
            have "Re (g t) = - sgn * C * (cos (2*pi*t - A) - cos A)"
              using Re_g[OF t01] .
            also have "\<dots> = - sgn * C * cos \<theta> + sgn * C * cos A"
              using angle_eq(1) by (simp add: algebra_simps)
            also have "\<dots> = Re (z - c) + Re c"
            proof -
              have "sgn \<noteq> 0" using sgn2 by (metis power2_eq_square mult_zero_left zero_neq_one)
              then have "Re (z - c) = - sgn * C * cos \<theta>"
                using \<theta>_Re Cne by (simp add: field_simps)
              moreover have "Re c = sgn * C * cos A"
                unfolding c_def by simp
              ultimately show ?thesis by (simp add: algebra_simps)
            qed
            also have "\<dots> = Re z"
              by simp
            finally show "Re (g t) = Re z" .
          next
            have "Im (g t) = C * sin (2*pi*t - A)"
              using CA[OF t01] .
            also have "\<dots> = C * sin \<theta>"
              using angle_eq(2) by simp
            also have "\<dots> = Im (z - c)"
              using \<theta>_Im Cne by (simp add: field_simps)
            also have "\<dots> = Im z"
              by (simp add: c_def)
            finally show "Im (g t) = Im z" .
          qed
          moreover have "g t \<in> path_image g"
            using t01 by (auto simp: path_image_def)
          ultimately show "z \<in> path_image g" by simp
        qed
      qed
      show ?thesis
        using subset supset by (auto intro!: exI[of _ c] exI[of _ "\<bar>C\<bar>"])
    qed
    ultimately show ?thesis
      using key_eq by presburger
  qed (use \<open>L>0\<close> in auto)
  show "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    using key by (simp add: field_simps)
  show "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
    \<exists>c r. path_image g = sphere c r"
  proof -
    assume eq: "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi)"
    have "L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi = 0"
      using eq by (simp add: field_simps)
    then show "\<exists>c r. path_image g = sphere c r"
      using key by blast
  qed
qed

text \<open>Reduction lemmas for the reparametrization steps.\<close>


lemma isoperimetric_reduce_shift:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "convex (inside (path_image g))"
    "path_length g = L"
    "a \<in> path_image g"
  obtains h where "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h" "pathstart h = a"
    "convex (inside (path_image h))"
    "path_length h = L"
    "path_image h = path_image g"
proof -
  obtain t where t: "t \<in> {0..1}" "g t = a"
    using assms(6) by (auto simp: path_image_def)
  define h where "h \<equiv> shiftpath t g"
  have "rectifiable_path h"
    unfolding h_def using rectifiable_path_shiftpath[OF assms(1) assms(3) t(1)] .
  moreover have "simple_path h"
    unfolding h_def using simple_path_shiftpath[OF assms(2) assms(3)] t(1) by auto
  moreover have "pathfinish h = pathstart h"
    unfolding h_def using pathfinish_shiftpath[of t g] pathstart_shiftpath[of t g]
      t(1) assms(3) by auto
  moreover have "pathstart h = a"
    unfolding h_def using pathstart_shiftpath[of t g] t by auto
  moreover have "path_image h = path_image g"
    unfolding h_def using path_image_shiftpath[OF t(1) assms(3)] .
  moreover have "convex (inside (path_image h))"
    using assms(4) calculation(5) by simp
  moreover have "path_length h = L"
    unfolding h_def using path_length_shiftpath[OF assms(1) assms(3) t(1)] assms(5) by simp
  ultimately show thesis using that by blast
qed

lemma isoperimetric_reduce_rotate_translate:
  fixes g :: "real \<Rightarrow> complex" and a b :: complex
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g" "pathstart g = a"
    "convex (inside (path_image g))"
    "path_length g = L"
    "b \<in> path_image g" "dist a b = diameter (path_image g)"
    "a \<noteq> b"
  obtains h a' b' where "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h" "pathstart h = a'"
    "convex (inside (path_image h))"
    "path_length h = L"
    "b' \<in> path_image h" "dist a' b' = diameter (path_image h)"
    "b' - a' = of_real (dist a' b')"
    "Re a' = 0"
    "measure lebesgue (inside (path_image h)) = measure lebesgue (inside (path_image g))"
    "\<And>c r. path_image h = sphere c r \<Longrightarrow> \<exists>c' r'. path_image g = sphere c' r'"
proof -
  define r where "r = cis (- Arg (b - a))"
  define h where "h = (*) r \<circ> (+) (-a) \<circ> g"
  define a' where "a' = r * (a - a)"
  define b' where "b' = r * (b - a)"
  have r_norm: "norm r = 1" unfolding r_def by simp
  have r_ne: "r \<noteq> 0" using r_norm by auto
  have lin_r: "linear ((*) r)" by (intro linearI) (auto simp: algebra_simps scaleR_conv_of_real)
  have inj_r: "inj ((*) r)" using r_ne by (simp add: inj_def)
  have norm_r: "\<And>x. norm (r * x) = norm x" using r_norm
    by (simp add: norm_mult)
  have dist_r: "\<And>x y. dist (r * x) (r * y) = dist x y"
    by (simp add: dist_mult_left r_norm)
  \<comment> \<open>Translation step: g₁ = (+) (-a) \<circ> g\<close>
  define g1 where "g1 = (+) (-a) \<circ> g"
  have rect_g1: "rectifiable_path g1"
    unfolding g1_def using assms(1) rectifiable_path_translation_eq by blast
  have sp_g1: "simple_path g1"
    unfolding g1_def using assms(2) simple_path_translation_eq by blast
  have pi_g1: "path_image g1 = (+) (-a) ` path_image g"
    unfolding g1_def by (simp add: path_image_compose image_comp)
  have ps_g1: "pathstart g1 = 0"
    unfolding g1_def using assms(4) by (simp add: pathstart_compose)
  have pf_g1: "pathfinish g1 = 0"
    unfolding g1_def using assms(3,4) by (simp add: pathstart_compose pathfinish_compose)
  have pl_g1: "path_length g1 = L"
    unfolding g1_def using assms(6) path_length_translation by blast
  \<comment> \<open>Rotation step: h = (*) r \<circ> g₁\<close>
  have h_eq: "h = (*) r \<circ> g1" unfolding h_def g1_def by (simp add: comp_assoc)
  have pi_h: "path_image h = (*) r ` path_image g1"
    unfolding h_eq by (simp add: path_image_compose image_comp)
  have a'_eq: "a' = 0" unfolding a'_def by simp
  have b'_eq: "b' = r * (b - a)" unfolding b'_def by simp
  \<comment> \<open>Key: r * (b-a) is a positive real\<close>
  have ba_ne: "b - a \<noteq> 0" using assms(9) by auto
  have "r * (b - a) = cis (- Arg (b-a)) * (b-a)"
    unfolding r_def by simp
  also have "\<dots> = of_real (cmod (b-a))"
    by (subst (2) rcis_cmod_Arg[symmetric, of "b - a"]) (simp add: rcis_def cis_mult)
  finally have rb_real: "b' = of_real (cmod (b-a))" unfolding b'_def by simp
  show ?thesis
  proof (rule that[of h a' b'])
    show "rectifiable_path h"
      unfolding h_eq using rect_g1 rectifiable_path_linear_image_eq[OF lin_r inj_r] by simp
    show "simple_path h"
      unfolding h_eq using sp_g1 simple_path_linear_image_eq[OF lin_r inj_r] by simp
    show "pathfinish h = pathstart h"
      unfolding h_eq using pf_g1 ps_g1 by (simp add: pathstart_compose pathfinish_compose)
    show "pathstart h = a'"
      unfolding h_eq a'_eq using ps_g1 by (simp add: pathstart_compose)
    show "path_length h = L"
      unfolding h_eq using pl_g1 path_length_linear_image[OF lin_r norm_r] by simp
    show "b' \<in> path_image h"
      unfolding pi_h b'_def g1_def using assms(7)
      by (auto simp: path_image_compose image_comp image_iff)
    show "Re a' = 0" unfolding a'_eq by simp
    show "b' - a' = of_real (dist a' b')"
      unfolding a'_eq using rb_real by (simp add: dist_norm)
    show "dist a' b' = diameter (path_image h)"
    proof -
      have "diameter (path_image h) = diameter ((*) r ` path_image g1)"
        unfolding pi_h by simp
      also have "\<dots> = diameter (path_image g1)"
      proof -
        have "(\<lambda>(x,y). dist x y) ` ((*) r ` path_image g1 \<times> (*) r ` path_image g1) =
              (\<lambda>(x,y). dist x y) ` (path_image g1 \<times> path_image g1)"
          by (force simp: image_iff dist_r)
        then show ?thesis by (simp add: diameter_def)
      qed
      also have "\<dots> = diameter ((+) (-a) ` path_image g)"
        unfolding pi_g1 by simp
      also have "\<dots> = diameter (path_image g)"
        by (metis diameter_translation)
      finally have diam_eq: "diameter (path_image h) = diameter (path_image g)" .
      have "dist a' b' = dist a b"
        unfolding a'_eq b'_def by (simp add: dist_norm norm_r norm_minus_commute)
      then show ?thesis using diam_eq assms(8) by simp
    qed
    have inside_h: "inside (path_image h) = (*) r ` (+) (-a) ` inside (path_image g)"
    proof -
      have "inside (path_image h) = (*) r ` inside (path_image g1)"
      proof -
        have "inside ((*) r ` path_image g1) = (*) r ` inside (path_image g1)"
        proof (rule set_eqI)
          fix x
          define y where "y = inverse r * x"
          then have xy: "x = r * y" using r_ne by simp
          have bij_r: "bij ((*) r)"
            unfolding bij_def using lin_r inj_r eucl.linear_inj_imp_surj[OF lin_r inj_r] by blast
          have compl_img: "(*) r ` (- path_image g1) = - ((*) r ` path_image g1)"
            using bij_image_Compl_eq[OF bij_r] .
          have homeo: "homeomorphism (- path_image g1) ((*) r ` (- path_image g1)) ((*) r) ((*) (inverse r))"
          proof (rule homeomorphismI)
            show "continuous_on (- path_image g1) ((*) r)"
              by (intro continuous_intros)
            show "continuous_on ((*) r ` (- path_image g1)) ((*) (inverse r))"
              by (intro continuous_intros)
            show "\<And>x. x \<in> - path_image g1 \<Longrightarrow> (*) (inverse r) (r * x) = x"
              using r_ne by simp
            show "\<And>y. y \<in> (*) r ` (- path_image g1) \<Longrightarrow> (*) r (inverse r * y) = y"
              using r_ne by simp
            show "(*) r ` (- path_image g1) \<subseteq> (*) r ` (- path_image g1)" by simp
            show "(*) (inverse r) ` ((*) r ` (- path_image g1)) \<subseteq> - path_image g1"
              using r_ne apply (auto simp: image_iff)
              by (metis divide_inverse_commute nonzero_mult_div_cancel_left)
          qed
          have cc: "connected_component_set (- ((*) r ` path_image g1)) x =
                    (*) r ` connected_component_set (- path_image g1) y"
          proof (cases "y \<in> path_image g1")
            case True
            then have "x \<in> (*) r ` path_image g1" using xy by auto
            then have "x \<notin> - ((*) r ` path_image g1)" by simp
            moreover have "y \<notin> - path_image g1" using True by simp
            ultimately show ?thesis
              using connected_component_eq_empty by blast
          next
            case False
            then have y_in: "y \<in> - path_image g1" by simp
            have "connected_component_set ((*) r ` (- path_image g1)) (r * y) =
                  (*) r ` connected_component_set (- path_image g1) y"
              using connected_component_set_homeomorphism[OF homeo y_in] .
            then show ?thesis using compl_img xy by simp
          qed
          have bounded_eq: "bounded ((*) r ` connected_component_set (- path_image g1) y) =
                           bounded (connected_component_set (- path_image g1) y)"
            by (simp add: bounded_iff norm_r image_iff)
          have memb: "(x \<in> (*) r ` path_image g1) = (y \<in> path_image g1)"
            using xy inj_r by (auto simp: inj_image_mem_iff)
          show "(x \<in> inside ((*) r ` path_image g1)) = (x \<in> (*) r ` inside (path_image g1))"
            unfolding inside_def mem_Collect_eq
          proof
            assume lhs: "x \<notin> (*) r ` path_image g1 \<and>
                         bounded (connected_component_set (- (*) r ` path_image g1) x)"
            have "y \<notin> path_image g1" using lhs memb by simp
            moreover have "bounded (connected_component_set (- path_image g1) y)"
              using lhs cc bounded_eq by simp
            ultimately show "x \<in> (*) r ` {x. x \<notin> path_image g1 \<and>
                            bounded (connected_component_set (- path_image g1) x)}"
              using xy by blast
          next
            assume rhs: "x \<in> (*) r ` {x. x \<notin> path_image g1 \<and>
                         bounded (connected_component_set (- path_image g1) x)}"
            then obtain z where z: "z \<notin> path_image g1"
              "bounded (connected_component_set (- path_image g1) z)" "x = r * z"
              by auto
            then have "z = y" using xy r_ne by (metis mult_left_cancel)
            then show "x \<notin> (*) r ` path_image g1 \<and>
                       bounded (connected_component_set (- (*) r ` path_image g1) x)"
              using z memb cc bounded_eq by simp
          qed
        qed
        then show ?thesis unfolding pi_h .
      qed
      also have "inside (path_image g1) = (+) (-a) ` inside (path_image g)"
        unfolding pi_g1 using inside_translation[of "-a" "path_image g"] by simp
      finally show ?thesis .
    qed
    show "convex (inside (path_image h))"
      using inside_h assms(5)
      by (metis convex_linear_image convex_translation_eq lin_r)
    show "measure lebesgue (inside (path_image h)) = measure lebesgue (inside (path_image g))"
    proof -
      have meas_g: "inside (path_image g) \<in> lmeasurable"
      proof -
        have "bounded (inside (path_image g))"
          using Jordan_inside_outside[OF assms(2) assms(3)] by blast
        then show ?thesis using measurable_convex assms(5) by blast
      qed
      have "measure lebesgue ((*) r ` (+) (-a) ` inside (path_image g)) =
            measure lebesgue ((+) (-a) ` inside (path_image g))"
      proof -
        have meas_t: "(+) (-a) ` inside (path_image g) \<in> lmeasurable"
          using meas_g measurable_translation by blast
        have "\<bar>eucl.det ((*) r)\<bar> = 1"
          unfolding det_complex r_def by simp
        then show ?thesis
          using Euclidean_Space_Transfer.measure_linear_image[OF lin_r meas_t] by simp
      qed
      also have "\<dots> = measure lebesgue (inside (path_image g))"
        using measure_translation[of "-a" "inside (path_image g)"] by simp
      finally show ?thesis using inside_h by simp
    qed
    show "\<And>c0 r0. path_image h = sphere c0 r0 \<Longrightarrow> \<exists>c' r'. path_image g = sphere c' r'"
    proof -
      fix c0 r0 assume sph: "path_image h = sphere c0 r0"
      then have eq1: "(*) r ` (+) (-a) ` path_image g = sphere c0 r0"
        unfolding pi_h pi_g1 image_image by (simp add: comp_def)
      have eq2: "(+) (-a) ` path_image g = (*) (inverse r) ` sphere c0 r0"
      proof -
        have "(*) (inverse r) ` ((*) r ` (+) (-a) ` path_image g) = (+) (-a) ` path_image g"
        proof -
          have *: "\<And>z. inverse r * (r * z) = z"
            using r_ne by (metis left_inverse mult.assoc mult_1)
          show ?thesis by (auto simp: image_iff *)
        qed
        then show ?thesis using eq1 by simp
      qed
      have eq3: "path_image g = (+) a ` (*) (inverse r) ` sphere c0 r0"
      proof -
        have "(+) a ` (+) (-a) ` path_image g = path_image g"
          by (auto simp: image_comp o_def)
        then show ?thesis using eq2 by simp
      qed
      moreover have "(*) (inverse r) ` sphere c0 r0 = sphere (inverse r * c0) r0"
        by (auto simp: nonzero_norm_inverse r_ne r_norm sphere_cscale)
      moreover have "(+) a ` sphere (inverse r * c0) r0 = sphere (a + inverse r * c0) r0"
        using sphere_translation[of a "inverse r * c0" r0] by simp
      ultimately show "\<exists>c' r'. path_image g = sphere c' r'" by auto
    qed
  qed
qed


lemma isoperimetric_reduce_arc_length:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "convex (inside (path_image g))"
    "path_length g = L" "0 < L"
  obtains h where "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h" "pathstart h = pathstart g"
    "convex (inside (path_image h))"
    "path_length h = L"
    "path_image h = path_image g"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = L * t"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
proof -
  obtain h where h: "rectifiable_path h" "path_image h = path_image g"
    "pathstart h = pathstart g" "pathfinish h = pathfinish g"
    "path_length h = path_length g"
    "arc g \<Longrightarrow> arc h" "simple_path g \<Longrightarrow> simple_path h"
    "\<forall>t\<in>{0..1}. path_length (subpath 0 t h) = path_length g * t"
    "\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. dist (h x) (h y) \<le> path_length g * dist x y"
    using arc_length_reparametrization [OF assms(1)] by metis
  have "simple_path h" using h(7) assms(2) by auto
  moreover have "pathfinish h = pathstart h"
    using h(3,4) assms(3) by simp
  moreover have "pathstart h = pathstart g" using h(3) .
  moreover have "convex (inside (path_image h))"
    using assms(4) h(2) by simp
  moreover have "path_length h = L" using h(5) assms(5) by simp
  moreover have "path_image h = path_image g" using h(2) .
  moreover have "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = L * t"
    using h(8) assms(5) by auto
  moreover have "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
    using h(9) assms(5) by auto
  ultimately show thesis using that h(1) by blast
qed

lemma isoperimetric_reduce_zero_mean:
  fixes g :: "real \<Rightarrow> complex" and b :: complex
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "convex (inside (path_image g))"
    "path_length g = L"
    "b \<in> path_image g"
    "dist (pathstart g) b = diameter (path_image g)"
    "b - pathstart g = of_real (dist (pathstart g) b)"
    "Re (pathstart g) = 0"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t g) = L * t"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g x) (g y) \<le> L * dist x y"
  obtains h a' b' where "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h"
    "convex (inside (path_image h))"
    "path_length h = L"
    "a' \<in> path_image h" "b' \<in> path_image h"
    "dist a' b' = diameter (path_image h)"
    "b' - a' = of_real (dist a' b')"
    "pathstart h = a'" "pathfinish h = a'"
    "Re a' = 0"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = L * t"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
    "(Im \<circ> h has_integral 0) {0..1}"
    "measure lebesgue (inside (path_image h)) = measure lebesgue (inside (path_image g))"
    "\<And>c r. path_image h = sphere c r \<Longrightarrow> \<exists>c' r'. path_image g = sphere c' r'"
proof -
  define c where "c = integral {0..1} (Im \<circ> g)"
  define d where "d = -(\<i> * (of_real c :: complex))"
  define h where "h = (+) d \<circ> g"
  define a' where "a' = pathstart g + d"
  define b' where "b' = b + d"
  have h_eq: "\<And>t. h t = g t + d" unfolding h_def comp_def by simp
  have pi_h: "path_image h = (+) d ` path_image g"
    unfolding h_def image_comp [symmetric] path_image_compose by simp
  show ?thesis
  proof (rule that[of h a' b'])
    show "rectifiable_path h"
      unfolding h_def using assms(1) rectifiable_path_translation_eq[of d g] by simp
    show "simple_path h"
      unfolding h_def using assms(2) simple_path_translation_eq[of d g] by simp
    show "pathfinish h = pathstart h"
      unfolding h_def using assms(3) by (simp add: pathstart_compose pathfinish_compose)
    show "path_length h = L"
      unfolding h_def using assms(5) path_length_translation[of d g] by simp
    show "pathstart h = a'" unfolding h_def a'_def by (simp add: pathstart_compose)
    show "pathfinish h = a'" unfolding h_def a'_def
      using assms(3) by (simp add: pathstart_compose pathfinish_compose)
    show "a' \<in> path_image h"
      unfolding a'_def using pi_h path_image_def pathstart_def by fastforce
    show "b' \<in> path_image h"
      unfolding b'_def using pi_h assms(6) by auto
    show "b' - a' = of_real (dist a' b')"
      unfolding a'_def b'_def using assms(8) by (simp add: dist_norm)
    show "dist a' b' = diameter (path_image h)"
      using pi_h diameter_translation[of d "path_image g"] assms(7)
      unfolding a'_def b'_def by (simp add: dist_norm)
    show "Re a' = 0" unfolding a'_def d_def using assms(9) by simp
    show "convex (inside (path_image h))"
      using pi_h inside_translation[of d "path_image g"]
        convex_translation_eq[of d "inside (path_image g)"] assms(4) by simp
    show "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = L * t"
    proof -
      fix t :: real assume "t \<in> {0..1}"
      have "subpath 0 t h = (+) d \<circ> subpath 0 t g"
        unfolding h_def subpath_def comp_def by (auto simp: algebra_simps)
      then have "path_length (subpath 0 t h) = path_length (subpath 0 t g)"
        using path_length_translation[of d "subpath 0 t g"] by simp
      also have "\<dots> = L * t" using assms(10) \<open>t \<in> {0..1}\<close> by simp
      finally show "path_length (subpath 0 t h) = L * t" .
    qed
    show "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
    proof -
      fix x y :: real assume "x \<in> {0..1}" "y \<in> {0..1}"
      have "dist (h x) (h y) = dist (g x) (g y)"
        unfolding h_eq by (simp add: dist_norm)
      also have "\<dots> \<le> L * dist x y" using assms(11)[OF \<open>x \<in> {0..1}\<close> \<open>y \<in> {0..1}\<close>] .
      finally show "dist (h x) (h y) \<le> L * dist x y" .
    qed
    show "(Im \<circ> h has_integral 0) {0..1}"
    proof -
      have cont_g: "continuous_on {0..1} g"
        using rectifiable_path_imp_path[OF assms(1)] unfolding path_def .
      have int_Im_g: "(\<lambda>t. Im (g t)) integrable_on {0..1}"
        using integrable_continuous_real[OF continuous_on_Im[OF cont_g]] .
      have Im_h: "\<And>t. Im (h t) = Im (g t) - c"
        unfolding h_def comp_def d_def by simp
      have eq: "\<And>t. (Im \<circ> h) t = (\<lambda>t. Im (g t) - c) t"
        using Im_h unfolding comp_def by simp
      have int_sub: "(\<lambda>t. Im (g t) - c) integrable_on {0..1}"
        by (rule integrable_diff[OF int_Im_g integrable_const_ivl])
      have int_h: "(Im \<circ> h) integrable_on {0..1}"
        using integrable_spike_finite[OF finite.emptyI _ int_sub] eq by simp
      have "integral {0..1} (Im \<circ> h) = integral {0..1} (\<lambda>t. Im (g t) - c)"
        using integral_cong[of "{0..1}" "Im \<circ> h" "\<lambda>t. Im (g t) - c"] eq by simp
      also have "\<dots> = integral {0..1} (\<lambda>t. Im (g t)) - integral {0..1} (\<lambda>_::real. c::real)"
        using integral_diff[OF int_Im_g integrable_const_ivl] by simp
      also have "\<dots> = 0" unfolding c_def comp_def by simp
      finally show ?thesis using int_h has_integral_iff by blast
    qed
    show "measure lebesgue (inside (path_image h)) = measure lebesgue (inside (path_image g))"
      using pi_h inside_translation[of d "path_image g"]
        measure_translation[of d "inside (path_image g)"] by simp
    show "\<And>c0 r. path_image h = sphere c0 r \<Longrightarrow> \<exists>c' r'. path_image g = sphere c' r'"
    proof -
      fix c0 r assume "path_image h = sphere c0 r"
      then have "(+) d ` path_image g = sphere c0 r" using pi_h by simp
      then have "(+) (- d) ` (+) d ` path_image g = (+) (- d) ` sphere c0 r" by simp
      then have "path_image g = (+) (- d) ` sphere c0 r"
        using translation_assoc[of "- d" d "path_image g"] by simp
      also have "\<dots> = sphere (c0 + (- d)) r"
        using sphere_translation[of "-d" c0 r] by simp
      finally show "\<exists>c' r'. path_image g = sphere c' r'" by blast
    qed
  qed
qed

theorem isoperimetric_theorem_convex:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "convex (inside (path_image g))"
    "path_length g = L"
  shows "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
      \<exists>a r. path_image g = sphere a r"
proof -
  have Lpos: "0 < L"
    using simple_path_length_pos_lt[OF assms(1,2)] assms(5) by simp
  text \<open>Step 1: obtain diameter endpoints\<close>
  have compact_pi: "compact (path_image g)"
    using compact_simple_path_image[OF assms(2)] .
  have nonempty_pi: "path_image g \<noteq> {}"
    using path_image_nonempty .
  obtain a b where ab: "a \<in> path_image g" "b \<in> path_image g"
    "dist a b = diameter (path_image g)"
    using diameter_compact_attained[OF compact_pi nonempty_pi] by auto
  text \<open>Step 2: shift start to diameter endpoint a\<close>
  obtain g1 where g1: "rectifiable_path g1" "simple_path g1"
    "pathfinish g1 = pathstart g1" "pathstart g1 = a"
    "convex (inside (path_image g1))"
    "path_length g1 = L" "path_image g1 = path_image g"
    using isoperimetric_reduce_shift[OF assms(1,2,3,4,5) ab(1)] by metis
  have ab1: "a \<in> path_image g1" "b \<in> path_image g1"
    "dist a b = diameter (path_image g1)"
    using ab g1(7) by auto
  have a_ne_b: "a \<noteq> b"
  proof
    assume "a = b"
    then have "diameter (path_image g) = 0" using ab(3) by simp
    then have "path_image g = {a}"
      by (metis ab(1) compact_eq_bounded_closed compact_pi diameter_eq_0 equals0D
          insertE)
    then show False using simple_path_image_uncountable[OF assms(2)]
      by (simp add: countable_finite)
  qed
  text \<open>Step 3: rotate and translate to normalize diameter direction\<close>
  obtain g2 a2 b2 where g2: "rectifiable_path g2" "simple_path g2"
    "pathfinish g2 = pathstart g2" "pathstart g2 = a2"
    "convex (inside (path_image g2))"
    "path_length g2 = L"
    "b2 \<in> path_image g2" "dist a2 b2 = diameter (path_image g2)"
    "b2 - a2 = of_real (dist a2 b2)"
    "Re a2 = 0"
    "measure lebesgue (inside (path_image g2)) = measure lebesgue (inside (path_image g))"
    and sphere_back2: "\<And>c r. path_image g2 = sphere c r \<Longrightarrow>
      \<exists>c' r'. path_image g = sphere c' r'"
    using isoperimetric_reduce_rotate_translate[OF g1(1,2,3) g1(4) g1(5,6) ab1(2,3) a_ne_b]
    by (metis g1(7))
  text \<open>Step 4: arc-length reparametrization\<close>
  obtain g3 where g3: "rectifiable_path g3" "simple_path g3"
    "pathfinish g3 = pathstart g3" "pathstart g3 = pathstart g2"
    "convex (inside (path_image g3))"
    "path_length g3 = L"
    "path_image g3 = path_image g2"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t g3) = L * t"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g3 x) (g3 y) \<le> L * dist x y"
    using isoperimetric_reduce_arc_length[OF g2(1,2,3,5,6) Lpos] by metis
  have g3_facts: "b2 \<in> path_image g3" "dist (pathstart g3) b2 = diameter (path_image g3)"
    "b2 - pathstart g3 = of_real (dist (pathstart g3) b2)" "Re (pathstart g3) = 0"
    using g2(7,8,9,10) g3(4,7) g2(4) by auto
  text \<open>Step 5: vertical translation for zero-mean imaginary part\<close>
  obtain h a' b' where h: "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h"
    "convex (inside (path_image h))"
    "path_length h = L"
    "a' \<in> path_image h" "b' \<in> path_image h"
    "dist a' b' = diameter (path_image h)"
    "b' - a' = of_real (dist a' b')"
    "pathstart h = a'" "pathfinish h = a'"
    "Re a' = 0"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = L * t"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
    "(Im \<circ> h has_integral 0) {0..1}"
    and meas_eq5: "measure lebesgue (inside (path_image h)) =
      measure lebesgue (inside (path_image g3))"
    and sphere_back5: "\<And>c r. path_image h = sphere c r \<Longrightarrow>
      \<exists>c' r'. path_image g3 = sphere c' r'"
    using isoperimetric_reduce_zero_mean[OF g3(1,2,3,5,6) g3_facts(1,2,3,4) g3(8,9)]
    by blast
  have meas_eq: "measure lebesgue (inside (path_image h)) =
    measure lebesgue (inside (path_image g))"
    using meas_eq5 g3(5,7) g2(11) by simp
  have sphere_back: "\<And>c r. path_image h = sphere c r \<Longrightarrow>
    \<exists>c' r'. path_image g = sphere c' r'"
  proof -
    fix c r assume "path_image h = sphere c r"
    then obtain c2 r2 where "path_image g2 = sphere c2 r2"
      using sphere_back5 g3(7) by metis
    then show "\<exists>c' r'. path_image g = sphere c' r'"
      using sphere_back2 by auto
  qed
  text \<open>Step 6: apply the kernel lemma\<close>
  have kernel_hyps: "0 < L" "convex (inside (path_image h))"
    "a' \<in> path_image h" "b' \<in> path_image h"
    "dist a' b' = diameter (path_image h)"
    "b' - a' = of_real (dist a' b')"
    "pathstart h = a'" "pathfinish h = a'"
    "rectifiable_path h" "simple_path h"
    "path_length h = L"
    "Re a' = 0"
    "(Im \<circ> h has_integral 0) {0..1}"
    using Lpos h by auto
  have ineq_h: "measure lebesgue (inside (path_image h)) \<le> L\<^sup>2 / (4 * pi)"
    using isoperimetric_kernel(1)[OF kernel_hyps(1-11) h(13,14) kernel_hyps(12,13)] .
  show "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    using ineq_h meas_eq by simp
  show "\<exists>a r. path_image g = sphere a r"
    if "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi)"
  proof -
    have "measure lebesgue (inside (path_image h)) = L\<^sup>2 / (4 * pi)"
      using that meas_eq by simp
    then obtain c r where "path_image h = sphere c r"
      using isoperimetric_kernel(2)[OF kernel_hyps(1-11) h(13,14) kernel_hyps(12,13)] by auto
    then show ?thesis using sphere_back by auto
  qed
qed

section \<open>Part 4: Convexification\<close>

text \<open>A connected subset of a segment that contains both endpoints is the whole segment.
  (HOL Light: CONNECTED\_SUBSET\_SEGMENT.)\<close>

lemma connected_subset_segment:
  fixes a b :: "'a::euclidean_space"
  assumes "connected S" "S \<subseteq> closed_segment a b" "a \<in> S" "b \<in> S"
  shows "S = closed_segment a b"
proof (cases "a = b")
  case True
  then show ?thesis using assms by auto
next
  case False
  define f where "f = (\<lambda>x::'a. (b - a) \<bullet> x)"
  define K where "K = (b - a) \<bullet> (b - a)"
  have contf: "continuous_on S f" by (auto simp: f_def continuous_intros)
  have conn_fS: "connected (f ` S)" using assms(1) contf connected_continuous_image by blast
  have nz: "K > 0" using False by (simp add: K_def inner_gt_zero_iff)
  have fseg: "\<And>u. f ((1-u) *\<^sub>R a + u *\<^sub>R b) = (b - a) \<bullet> a + u * K"
    by (simp add: f_def K_def inner_diff_right algebra_simps inner_diff_left inner_commute)
  have fa: "f a = (b - a) \<bullet> a" by (simp add: f_def)
  have fb: "f b = (b - a) \<bullet> a + K" using fseg[of 1] by simp
  show ?thesis
  proof (rule subset_antisym[OF assms(2)])
    show "closed_segment a b \<subseteq> S"
    proof
      fix x assume "x \<in> closed_segment a b"
      then obtain u where u: "x = (1 - u) *\<^sub>R a + u *\<^sub>R b" "0 \<le> u" "u \<le> 1"
        by (auto simp: in_segment)
      have fx: "f x = (b - a) \<bullet> a + u * K" using u(1) fseg by simp
      have mem: "f x \<in> closed_segment (f a) (f b)"
        unfolding closed_segment_eq_real_ivl using nz u(2,3) fa fb fx
        by (auto simp: mult_left_le_one_le)
      have "closed_segment (f a) (f b) \<subseteq> f ` S"
        using conn_fS assms(3,4) connected_contains_Icc
        by (metis closed_segment_eq_real_ivl image_eqI)
      then have "f x \<in> f ` S" using mem by blast
      then obtain s where s: "s \<in> S" "f s = f x" by auto
      have "s \<in> closed_segment a b" using s(1) assms(2) by blast
      then obtain v where v: "s = (1 - v) *\<^sub>R a + v *\<^sub>R b" "0 \<le> v" "v \<le> 1"
        by (auto simp: in_segment)
      have "(b - a) \<bullet> a + v * K = (b - a) \<bullet> a + u * K"
        using s(2) v(1) fseg fx by simp
      then have "v = u" using nz by simp
      then show "x \<in> S" using s(1) v(1) u(1) by simp
    qed
  qed
qed

text \<open>A connected subset of two arcs joined only at their common endpoints, containing both
  endpoints, must contain one of the two arcs in full. (HOL Light: CONNECTED\_SUBSET\_ARC\_PAIR.)\<close>

lemma connected_subset_arc_pair:
  fixes g h :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "arc g" "arc h"
    "pathstart g = pathstart h" "pathfinish g = pathfinish h"
    "path_image g \<inter> path_image h = {pathstart g, pathfinish g}"
    "connected S" "S \<subseteq> path_image g \<union> path_image h"
    "pathstart g \<in> S" "pathfinish g \<in> S"
  shows "path_image g \<subseteq> S \<or> path_image h \<subseteq> S"
proof (rule ccontr)
  assume "\<not> (path_image g \<subseteq> S \<or> path_image h \<subseteq> S)"
  then have ng: "\<not> path_image g \<subseteq> S" and nh: "\<not> path_image h \<subseteq> S" by auto
  from ng obtain pg where pg: "pg \<in> path_image g" "pg \<notin> S" by blast
  then obtain p where p: "p \<in> {0..1}" "g p = pg" by (auto simp: path_image_def)
  from nh obtain ph where ph: "ph \<in> path_image h" "ph \<notin> S" by blast
  then obtain q where q: "q \<in> {0..1}" "h q = ph" by (auto simp: path_image_def)
  have gp: "g p \<notin> S" using p(2) pg(2) by simp
  have hq: "h q \<notin> S" using q(2) ph(2) by simp
  have pathg: "path g" and pathh: "path h" using assms(1,2) arc_imp_path by auto
  have img_g0p: "path_image (subpath 0 p g) = g ` {0..p}" using p(1) by (simp add: path_image_subpath)
  have img_gp1: "path_image (subpath p 1 g) = g ` {p..1}" using p(1) by (simp add: path_image_subpath)
  have img_h0q: "path_image (subpath 0 q h) = h ` {0..q}" using q(1) by (simp add: path_image_subpath)
  have img_hq1: "path_image (subpath q 1 h) = h ` {q..1}" using q(1) by (simp add: path_image_subpath)
  have comb_g: "g ` {0..p} \<union> g ` {p..1} = path_image g"
    using p(1) by (simp add: path_image_def image_Un [symmetric]) (metis ivl_disj_un_two_touch(4))
  have comb_h: "h ` {0..q} \<union> h ` {q..1} = path_image h"
    using q(1) by (simp add: path_image_def image_Un [symmetric]) (metis ivl_disj_un_two_touch(4))
  define E1 where "E1 = S - (path_image (subpath p 1 g) \<union> path_image (subpath q 1 h))"
  define E2 where "E2 = S - (path_image (subpath 0 p g) \<union> path_image (subpath 0 q h))"
  have cl_gp1: "closed (path_image (subpath p 1 g))"
    using pathg p(1) by (simp add: closed_path_image path_subpath)
  have cl_hq1: "closed (path_image (subpath q 1 h))"
    using pathh q(1) by (simp add: closed_path_image path_subpath)
  have cl_g0p: "closed (path_image (subpath 0 p g))"
    using pathg p(1) by (simp add: closed_path_image path_subpath)
  have cl_h0q: "closed (path_image (subpath 0 q h))"
    using pathh q(1) by (simp add: closed_path_image path_subpath)
  have openE1: "openin (top_of_set S) E1"
  proof -
    have "E1 = S \<inter> (- (path_image (subpath p 1 g) \<union> path_image (subpath q 1 h)))"
      unfolding E1_def by blast
    moreover have "open (- (path_image (subpath p 1 g) \<union> path_image (subpath q 1 h)))"
      using cl_gp1 cl_hq1 by blast
    ultimately show ?thesis by (simp add: openin_open_Int)
  qed
  have openE2: "openin (top_of_set S) E2"
  proof -
    have "E2 = S \<inter> (- (path_image (subpath 0 p g) \<union> path_image (subpath 0 q h)))"
      unfolding E2_def by blast
    moreover have "open (- (path_image (subpath 0 p g) \<union> path_image (subpath 0 q h)))"
      using cl_g0p cl_h0q by blast
    ultimately show ?thesis by (simp add: openin_open_Int)
  qed
  have injg: "inj_on g {0..1}" using assms(1) by (simp add: arc_def)
  have injh: "inj_on h {0..1}" using assms(2) by (simp add: arc_def)
  have p_pos: "p > 0"
  proof (rule ccontr)
    assume "\<not> p > 0" then have "p = 0" using p(1) by simp
    then have "g p = pathstart g" by (simp add: pathstart_def)
    then show False using gp assms(8) by simp
  qed
  have q_pos: "q > 0"
  proof (rule ccontr)
    assume "\<not> q > 0" then have "q = 0" using q(1) by simp
    then have "h q = pathstart h" by (simp add: pathstart_def)
    then show False using hq assms(8) assms(3) by simp
  qed
  have p_lt1: "p < 1"
  proof (rule ccontr)
    assume "\<not> p < 1" then have "p = 1" using p(1) by simp
    then have "g p = pathfinish g" by (simp add: pathfinish_def)
    then show False using gp assms(9) by simp
  qed
  have q_lt1: "q < 1"
  proof (rule ccontr)
    assume "\<not> q < 1" then have "q = 1" using q(1) by simp
    then have "h q = pathfinish h" by (simp add: pathfinish_def)
    then show False using hq assms(9) assms(4) by simp
  qed
  have ne_E1: "pathstart g \<in> E1"
  proof -
    have "g 0 \<notin> g ` {p..1}"
    proof
      assume "g 0 \<in> g ` {p..1}"
      then obtain t where t: "t \<in> {p..1}" "g 0 = g t" by auto
      have "0 = t" using injg t p(1) p_pos by (force simp: inj_on_def)
      then show False using t(1) p_pos by simp
    qed
    moreover have "g 0 \<notin> h ` {q..1}"
    proof
      assume "g 0 \<in> h ` {q..1}"
      then have "h 0 \<in> h ` {q..1}" using assms(3) by (simp add: pathstart_def)
      then obtain t where t: "t \<in> {q..1}" "h 0 = h t" by auto
      have "0 = t" using injh t q(1) q_pos by (force simp: inj_on_def)
      then show False using t(1) q_pos by simp
    qed
    ultimately show ?thesis
      unfolding E1_def using assms(8) img_gp1 img_hq1 by (simp add: pathstart_def)
  qed
  have ne_E2: "pathfinish g \<in> E2"
  proof -
    have "g 1 \<notin> g ` {0..p}"
    proof
      assume "g 1 \<in> g ` {0..p}"
      then obtain t where t: "t \<in> {0..p}" "g 1 = g t" by auto
      have "1 = t" using injg t p(1) by (force simp: inj_on_def)
      then show False using t(1) p_lt1 by simp
    qed
    moreover have "g 1 \<notin> h ` {0..q}"
    proof
      assume "g 1 \<in> h ` {0..q}"
      then have "h 1 \<in> h ` {0..q}" using assms(4) by (simp add: pathfinish_def)
      then obtain t where t: "t \<in> {0..q}" "h 1 = h t" by auto
      have "1 = t" using injh t q(1) by (force simp: inj_on_def)
      then show False using t(1) q_lt1 by simp
    qed
    moreover have "pathfinish g \<in> S" using assms(9) .
    ultimately show ?thesis
      unfolding E2_def using img_g0p img_h0q by (simp add: pathfinish_def)
  qed
  have ps_g: "pathstart g = g 0" by (simp add: pathstart_def)
  have pf_g: "pathfinish g = g 1" by (simp add: pathfinish_def)
  have cross_gh: "\<And>s t. s \<in> {0..1} \<Longrightarrow> t \<in> {0..1} \<Longrightarrow> g s = h t \<Longrightarrow> g s = g 0 \<or> g s = g 1"
  proof -
    fix s t assume s: "s \<in> {0..1}" and t: "t \<in> {0..1}" and eq: "g s = h t"
    have "g s \<in> path_image g" using s by (auto simp: path_image_def)
    moreover have "g s \<in> path_image h" using t eq by (auto simp: path_image_def)
    ultimately have "g s \<in> {pathstart g, pathfinish g}" using assms(5) by blast
    then show "g s = g 0 \<or> g s = g 1" using ps_g pf_g by auto
  qed
  have sub_p1: "{p..1} \<subseteq> {0..1}" using p(1) by auto
  have sub_0p: "{0..p} \<subseteq> {0..1}" using p(1) by auto
  have sub_q1: "{q..1} \<subseteq> {0..1}" using q(1) by auto
  have sub_0q: "{0..q} \<subseteq> {0..1}" using q(1) by auto
  have gh11: "g 1 = h 1" using assms(4) by (simp add: pathfinish_def)
  have gh00: "g 0 = h 0" using assms(3) by (simp add: pathstart_def)
  have cover_False: "\<And>x. x \<in> S \<Longrightarrow> x \<in> g ` {p..1} \<union> h ` {q..1} \<Longrightarrow> x \<in> g ` {0..p} \<union> h ` {0..q} \<Longrightarrow> False"
  proof -
    fix x assume xS: "x \<in> S" and inR1: "x \<in> g ` {p..1} \<union> h ` {q..1}" and inR2: "x \<in> g ` {0..p} \<union> h ` {0..q}"
    from inR1 consider (g1) "x \<in> g ` {p..1}" | (h1) "x \<in> h ` {q..1}" by auto
    then show False
    proof cases
      case g1
      then obtain s where s: "s \<in> {p..1}" "x = g s" by auto
      from inR2 consider (a) "x \<in> g ` {0..p}" | (b) "x \<in> h ` {0..q}" by auto
      then show False
      proof cases
        case a
        then obtain t where t: "t \<in> {0..p}" "x = g t" by auto
        have "s = t" using injg s t sub_p1 sub_0p s(2) t(2) by (force simp: inj_on_def)
        then have "s = p" using s(1) t(1) by simp
        then show False using gp xS s(2) by simp
      next
        case b
        then obtain t where t: "t \<in> {0..q}" "x = h t" by auto
        have eq: "g s = h t" using s(2) t(2) by simp
        have "g s = g 0 \<or> g s = g 1" using cross_gh s(1) sub_p1 t(1) sub_0q eq by blast
        then show False
        proof
          assume "g s = g 0"
          then have "s = 0" using injg s(1) sub_p1 by (force simp: inj_on_def)
          then show False using s(1) p_pos by simp
        next
          assume "g s = g 1"
          then have "h t = h 1" using eq gh11 by simp
          then have "t = 1" using injh t(1) sub_0q by (force simp: inj_on_def)
          then show False using t(1) q_lt1 by simp
        qed
      qed
    next
      case h1
      then obtain s where s: "s \<in> {q..1}" "x = h s" by auto
      from inR2 consider (a) "x \<in> g ` {0..p}" | (b) "x \<in> h ` {0..q}" by auto
      then show False
      proof cases
        case a
        then obtain t where t: "t \<in> {0..p}" "x = g t" by auto
        have eq: "g t = h s" using s(2) t(2) by simp
        have "g t = g 0 \<or> g t = g 1" using cross_gh t(1) sub_0p s(1) sub_q1 eq by blast
        then show False
        proof
          assume "g t = g 1"
          then have "t = 1" using injg t(1) sub_0p by (force simp: inj_on_def)
          then show False using t(1) p_lt1 by simp
        next
          assume "g t = g 0"
          then have "h s = h 0" using eq gh00 by simp
          then have "s = 0" using injh s(1) sub_q1 by (force simp: inj_on_def)
          then show False using s(1) q_pos by simp
        qed
      next
        case b
        then obtain t where t: "t \<in> {0..q}" "x = h t" by auto
        have "s = t" using injh s t sub_q1 sub_0q s(2) t(2) by (force simp: inj_on_def)
        then have "s = q" using s(1) t(1) by simp
        then show False using hq xS s(2) by simp
      qed
    qed
  qed
  have cover: "S \<subseteq> E1 \<union> E2"
  proof
    fix x assume xS: "x \<in> S"
    show "x \<in> E1 \<union> E2"
    proof (rule ccontr)
      assume "x \<notin> E1 \<union> E2"
      then have "x \<in> g ` {p..1} \<union> h ` {q..1}" and "x \<in> g ` {0..p} \<union> h ` {0..q}"
        using xS unfolding E1_def E2_def img_gp1 img_hq1 img_g0p img_h0q by auto
      then show False using cover_False xS by blast
    qed
  qed
  have disjoint: "E1 \<inter> E2 = {}"
  proof -
    have "(g ` {p..1} \<union> h ` {q..1}) \<union> (g ` {0..p} \<union> h ` {0..q}) = path_image g \<union> path_image h"
      using comb_g comb_h by blast
    moreover have "S \<subseteq> path_image g \<union> path_image h" using assms(7) .
    ultimately show ?thesis unfolding E1_def E2_def img_gp1 img_hq1 img_g0p img_h0q by blast
  qed
  from assms(6) have "\<not> (\<exists>E1 E2. openin (top_of_set S) E1 \<and> openin (top_of_set S) E2 \<and> S \<subseteq> E1 \<union> E2 \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {})"
    by (simp add: connected_openin)
  moreover have "openin (top_of_set S) E1 \<and> openin (top_of_set S) E2 \<and> S \<subseteq> E1 \<union> E2 \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {}"
    using openE1 openE2 cover disjoint ne_E1 ne_E2 by auto
  ultimately show False by blast
qed

text \<open>If two frontier points of a bounded convex 2D set are joined by a frontier arc whose
  interior (the arc minus the two points) stays connected and whose convex hull is the whole set,
  then the straight segment between the two points also lies on the frontier. The connectedness of
  the arc-minus-endpoints is what rules out the spurious ``chord through the interior'' case.\<close>

lemma seg_frontier_aux:
  fixes S :: "complex set"
  assumes cvx: "convex S" and cpt: "compact S" and intne: "interior S \<noteq> {}"
    and ga_fr: "ga \<in> frontier S" and gb_fr: "gb \<in> frontier S" and ne: "ga \<noteq> gb"
    and D1fr: "path_image D1 \<subseteq> frontier S"
    and D1con: "connected (path_image D1 - {ga, gb})"
    and gaD1: "ga \<in> path_image D1" and gbD1: "gb \<in> path_image D1"
    and hullD1: "convex hull (path_image D1) = S"
  shows "closed_segment ga gb \<subseteq> frontier S"
proof -
  have clSh: "closed S" using cpt by (rule compact_imp_closed)
  have relfr: "rel_frontier S = frontier S" using intne by (rule rel_frontier_nonempty_interior)
  have ga_cl: "ga \<in> closure S" and gb_cl: "gb \<in> closure S"
    using ga_fr gb_fr by (auto simp: frontier_def)
  have dich: "open_segment ga gb \<subseteq> frontier S \<or> open_segment ga gb \<subseteq> interior S"
    using convex_open_segment_cases_alt[OF cvx ga_cl gb_cl] .
  define A where "A = \<i> * (gb - ga)"
  have A_nz: "A \<noteq> 0" using ne by (simp add: A_def)
  define e where "e = inner A ga"
  have eb: "inner A gb = e"
  proof -
    have "inner A (gb - ga) = 0" unfolding A_def inner_complex_def by (simp add: algebra_simps)
    then show ?thesis using e_def by (simp add: inner_diff_right)
  qed
  have opfr: "open_segment ga gb \<subseteq> frontier S"
  proof (rule ccontr)
    assume "\<not> open_segment ga gb \<subseteq> frontier S"
    then have segint: "open_segment ga gb \<subseteq> interior S" using dich by blast
    have mid_int: "midpoint ga gb \<in> interior S"
      using segint ne by (simp add: midpoint_in_open_segment subsetD)
    have mid_e: "inner A (midpoint ga gb) = e"
      using e_def eb by (simp add: midpoint_def inner_add_right inner_diff_right field_simps)
    have not_le: "\<not> (path_image D1 \<subseteq> {x. inner A x \<le> e})"
    proof
      assume "path_image D1 \<subseteq> {x. inner A x \<le> e}"
      then have "convex hull (path_image D1) \<subseteq> {x. inner A x \<le> e}"
        by (simp add: convex_halfspace_le hull_minimal)
      then have "S \<subseteq> {x. inner A x \<le> e}" using hullD1 by simp
      then have "interior S \<subseteq> interior {x. inner A x \<le> e}" by (rule interior_mono)
      also have "interior {x. inner A x \<le> e} = {x. inner A x < e}"
        using A_nz by (simp add: interior_halfspace_le)
      finally have "inner A (midpoint ga gb) < e" using mid_int by blast
      then show False using mid_e by simp
    qed
    have not_ge: "\<not> (path_image D1 \<subseteq> {x. e \<le> inner A x})"
    proof
      assume "path_image D1 \<subseteq> {x. e \<le> inner A x}"
      then have "convex hull (path_image D1) \<subseteq> {x. e \<le> inner A x}"
        by (simp add: convex_halfspace_ge hull_minimal)
      then have "S \<subseteq> {x. e \<le> inner A x}" using hullD1 by simp
      then have "interior S \<subseteq> interior {x. e \<le> inner A x}" by (rule interior_mono)
      also have "interior {x. e \<le> inner A x} = {x. e < inner A x}"
        using A_nz by (simp add: interior_halfspace_ge)
      finally have "e < inner A (midpoint ga gb)" using mid_int by blast
      then show False using mid_e by simp
    qed
    from not_le obtain x1 where x1: "x1 \<in> path_image D1" "inner A x1 > e" by force
    from not_ge obtain x2 where x2: "x2 \<in> path_image D1" "inner A x2 < e" by force
    have x1ne: "x1 \<notin> {ga, gb}" using x1(2) e_def eb by auto
    have x2ne: "x2 \<notin> {ga, gb}" using x2(2) e_def eb by auto
    have x1D: "x1 \<in> path_image D1 - {ga,gb}" using x1(1) x1ne by simp
    have x2D: "x2 \<in> path_image D1 - {ga,gb}" using x2(1) x2ne by simp
    obtain w where w: "w \<in> path_image D1 - {ga,gb}" "inner A w = e"
      using connected_ivt_hyperplane[OF D1con x2D x1D, where a=A and b=e] x1(2) x2(2) by force
    have w_fr: "w \<in> rel_frontier S" using w(1) D1fr relfr by auto
    have ga_rf: "ga \<in> rel_frontier S" using ga_fr relfr by simp
    have gb_rf: "gb \<in> rel_frontier S" using gb_fr relfr by simp
    have wne: "w \<noteq> ga" "w \<noteq> gb" using w(1) by auto
    have triple: "S \<subseteq> {x. inner A x \<le> e} \<or> S \<subseteq> {x. e \<le> inner A x}"
    proof (rule convex_triple_rel_frontier[OF cvx ga_rf gb_rf w_fr ne])
      show "ga \<noteq> w" using wne(1) by simp
      show "gb \<noteq> w" using wne(2) by simp
      show "inner A ga = e" using e_def by simp
      show "inner A gb = e" using eb by simp
      show "inner A w = e" using w(2) by simp
    qed
    have D1S: "path_image D1 \<subseteq> S" using D1fr relfr hullD1 hull_subset by (metis frontier_def Diff_subset dual_order.trans)
    from triple show False
    proof
      assume "S \<subseteq> {x. inner A x \<le> e}"
      then have "path_image D1 \<subseteq> {x. inner A x \<le> e}" using D1S by blast
      then show False using not_le by simp
    next
      assume "S \<subseteq> {x. e \<le> inner A x}"
      then have "path_image D1 \<subseteq> {x. e \<le> inner A x}" using D1S by blast
      then show False using not_ge by simp
    qed
  qed
  have "{ga, gb} \<subseteq> frontier S" using ga_fr gb_fr by simp
  then show ?thesis using opfr by (simp add: closed_segment_eq_open)
qed

text \<open>The step lemma: replacing an arc that deviates from the convex hull frontier
  with a straight segment shortens the path while preserving the convex hull.\<close>

lemma step_lemma:
  fixes g :: "real \<Rightarrow> complex"
  assumes "simple_path g" "pathfinish g = pathstart g"
    and "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g x) (g y) \<le> L * dist x y"
    and "a < b"
    and ab01: "a \<in> {0..1}" "b \<in> {0..1}"
    and "g a \<in> frontier (convex hull (path_image g))"
    and "g b \<in> frontier (convex hull (path_image g))"
    and "g ` {a<..<b} \<inter> frontier (convex hull (path_image g)) = {}"
  obtains h where "simple_path h"
    and "pathstart h = pathstart g" and "pathfinish h = pathstart g"
    and "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
    and "path_length h < path_length g"
    and "convex hull (path_image h) = convex hull (path_image g)"
    and "\<And>x. x \<notin> {a<..<b} \<Longrightarrow> h x = g x"
    and "h ` {a..b} \<subseteq> frontier (convex hull (path_image g))"
proof (cases "box a b = {}")
  case True
  with \<open>a<b\<close> show ?thesis by auto
next
  case False
  have interior_subset: "g ` {a<..<b} \<subseteq> interior (convex hull (path_image g))"
  proof -
    have "g ` {a<..<b} \<subseteq> path_image g"
      using ab01 unfolding path_image_def
      by (intro image_mono) (auto simp: greaterThanLessThan_subseteq_atLeastAtMost_iff)
    also have "\<dots> \<subseteq> convex hull (path_image g)"
      by (rule hull_subset)
    finally have sub: "g ` {a<..<b} \<subseteq> convex hull (path_image g)" .
    have closed: "closed (convex hull (path_image g))"
      using compact_convex_hull[OF compact_simple_path_image[OF \<open>simple_path g\<close>]]
      by (rule compact_imp_closed)
    with sub have "g ` {a<..<b} \<subseteq> frontier (convex hull (path_image g)) \<union> interior (convex hull (path_image g))"
      unfolding frontier_def by auto
    with assms(9) show ?thesis by auto
  qed
  have interior_ne: "interior (convex hull (path_image g)) \<noteq> {}"
    using interior_subset \<open>a<b\<close> by fastforce
  show ?thesis
  proof (cases "g a = g b")
    case True
    then show ?thesis
    proof -
      have ab_eq: "a = 0" "b = 1"
      proof -
        from True have "g a = g b" .
        with \<open>simple_path g\<close> ab01 have "a = b \<or> a = 0 \<and> b = 1 \<or> a = 1 \<and> b = 0"
          unfolding simple_path_def loop_free_def by auto
        with \<open>a < b\<close> show "a = 0" "b = 1" by auto
      qed
      have g01: "g 0 = g 1"
        using assms(2) by (simp add: pathfinish_def pathstart_def)
      have pi_eq: "path_image g = {g 0} \<union> g ` {0<..<1}"
        using g01 by (fastforce simp: path_image_def image_iff)
      have int_sub: "g ` {0<..<1} \<subseteq> interior (convex hull (path_image g))"
        using interior_subset ab_eq by simp
      \<comment> \<open>Every extreme point of the convex hull lies in path_image g but not in the interior\<close>
      have ext_sub: "{x. x extreme_point_of (convex hull (path_image g))} \<subseteq> {g 0}"
      proof (rule subsetI, clarsimp)
        fix x assume ext: "x extreme_point_of convex hull (path_image g)"
        then have "x \<in> path_image g"
          using extreme_point_of_convex_hull by blast
        moreover have "x \<notin> interior (convex hull (path_image g))"
          using extreme_point_not_in_interior[OF ext] .
        ultimately show "x = g 0"
          using int_sub pi_eq by auto
      qed
      \<comment> \<open>By Krein-Milman, the convex hull collapses to a single point\<close>
      have compact_hull: "compact (convex hull (path_image g))"
        by (rule compact_convex_hull[OF compact_simple_path_image[OF \<open>simple_path g\<close>]])
      have "convex hull (path_image g) = convex hull {x. x extreme_point_of (convex hull (path_image g))}"
        using Krein_Milman_Minkowski[OF compact_hull convex_convex_hull] by simp
      also have "\<dots> \<subseteq> convex hull {g 0}"
        using ext_sub by (intro hull_mono)
      also have "\<dots> = {g 0}" by (simp add: convex_hull_singleton)
      finally have "convex hull (path_image g) \<subseteq> {g 0}" .
      then have "interior (convex hull (path_image g)) \<subseteq> interior {g 0}"
        by (rule interior_mono)
      then have "interior (convex hull (path_image g)) = {}"
        by (simp add: interior_singleton)
      with interior_ne show ?thesis by contradiction
    qed
  next
    case False
    have hull_eq: "convex hull (g ` ({0..1} - {a<..<b})) = convex hull (path_image g)"
    proof
      show "convex hull (g ` ({0..1} - {a<..<b})) \<subseteq> convex hull (path_image g)"
        by (intro hull_mono image_mono) (auto simp: path_image_def)
          \<comment> \<open>For \<supseteq>, use extreme points: they lie in path_image g but not in interior\<close>
      have compact_hull: "compact (convex hull (path_image g))"
        by (rule compact_convex_hull[OF compact_simple_path_image[OF \<open>simple_path g\<close>]])
      have ext_in_rest: "{x. x extreme_point_of (convex hull (path_image g))} \<subseteq> g ` ({0..1} - {a<..<b})"
      proof (rule subsetI, clarsimp)
        fix x assume ext: "x extreme_point_of convex hull (path_image g)"
        then have "x \<in> path_image g"
          using extreme_point_of_convex_hull by blast
        moreover have "x \<notin> interior (convex hull (path_image g))"
          using extreme_point_not_in_interior[OF ext] .
        moreover have "g ` {a<..<b} \<subseteq> interior (convex hull (path_image g))"
          using interior_subset .
        ultimately have "x \<in> path_image g" "x \<notin> g ` {a<..<b}"
          by blast+
        then show "x \<in> g ` ({0..1} - {a<..<b})"
          unfolding path_image_def by blast
      qed
      show "convex hull (path_image g) \<subseteq> convex hull (g ` ({0..1} - {a<..<b}))"
        using Krein_Milman_Minkowski[OF compact_hull convex_convex_hull]
        using ext_in_rest hull_mono by blast
    qed
    have hull_seg_eq: "convex hull (closed_segment (g a) (g b) \<union> g ` ({0..1} - {a<..<b})) = convex hull (path_image g)"
    proof
      have "g a \<in> g ` ({0..1} - {a<..<b})" "g b \<in> g ` ({0..1} - {a<..<b})"
        using ab01 \<open>a < b\<close> by auto
      then have seg_sub: "closed_segment (g a) (g b) \<subseteq> convex hull (g ` ({0..1} - {a<..<b}))"
        by (meson closed_segment_subset convex_convex_hull hull_inc)
      show "convex hull (closed_segment (g a) (g b) \<union> g ` ({0..1} - {a<..<b})) \<subseteq> convex hull (path_image g)"
        by (metis hull_eq convex_convex_hull hull_subset le_supI seg_sub subset_hull)
      show "convex hull (path_image g) \<subseteq> convex hull (closed_segment (g a) (g b) \<union> g ` ({0..1} - {a<..<b}))"
        by (metis Un_commute Un_upper1 hull_eq hull_mono)
    qed
  \<comment> \<open>Step 1: Double arc decomposition of g\<close>
    obtain g0 g1 where arcs:
      "arc g0" "arc g1"
      "pathstart g0 = g a" "pathfinish g0 = g b"
      "pathstart g1 = g b" "pathfinish g1 = g a"
      "path_image g0 = g ` {a..b}"
      "path_image g1 = g ` ({0..1} - {a<..<b})"
      "(path_image g0) \<inter> (path_image g1) = {g a, g b}"
      "(path_image g0) \<union> (path_image g1) = path_image g"
      using exists_double_arc_explicit[OF \<open>simple_path g\<close> \<open>pathfinish g = pathstart g\<close>
          ab01(1) ab01(2) less_imp_le[OF \<open>a < b\<close>] False] by blast

    \<comment> \<open>Step 2: The frontier of the convex hull admits a rectifiable simple loop parametrization\<close>
    \<comment> \<open>(This corresponds to HOL Light's RECTIFIABLE_LOOP_RELATIVE_FRONTIER_CONVEX)\<close>
    have frontier_eq_rel: "rel_frontier (convex hull (path_image g)) = frontier (convex hull (path_image g))"
      using rel_frontier_nonempty_interior[OF interior_ne] by simp
    obtain d where d_props:
      "simple_path d" "pathfinish d = pathstart d" "rectifiable_path d"
      "path_image d = frontier (convex hull (path_image g))"
    proof -
      have "convex (convex hull (path_image g))" by (rule convex_convex_hull)
      moreover have "bounded (convex hull (path_image g))"
        by (intro bounded_convex_hull compact_imp_bounded compact_simple_path_image \<open>simple_path g\<close>)
      moreover have "interior (convex hull (path_image g)) \<noteq> {}"
        by (rule interior_ne)
      moreover note frontier_eq_rel
      ultimately show ?thesis 
        using rectifiable_loop_frontier_convex that by blast
    qed

\<comment> \<open>Step 4: Double arc decomposition of the frontier loop d, with inside decomposition\<close>
    have ga_ne_gb: "g a \<noteq> g b" using False .
    obtain d0 d1 where d_split:
      "arc d0" "arc d1"
      "pathstart d0 = g a" "pathfinish d0 = g b"
      "pathstart d1 = g b" "pathfinish d1 = g a"
      "path_image d0 \<inter> path_image d1 = {g a, g b}"
      "path_image d0 \<union> path_image d1 = path_image d"
      "inside (path_image d0 \<union> path_image g0) \<inter>
       inside (path_image d1 \<union> path_image g0) = {}"
      "inside (path_image d0 \<union> path_image g0) \<union>
       inside (path_image d1 \<union> path_image g0) \<union>
       (path_image g0 - {g a, g b}) =
       interior (convex hull (path_image g))"
      "(path_image g1 - {g b, g a}) \<inter> path_image d0 = {}"
    proof -
      have ga_d: "g a \<in> path_image d" and gb_d: "g b \<in> path_image d"
        using d_props(4) assms(7,8) by simp_all
      obtain d0 d1 where da:
        "arc d0" "arc d1"
        "pathstart d0 = g a" "pathfinish d0 = g b"
        "pathstart d1 = g b" "pathfinish d1 = g a"
        "path_image d0 \<inter> path_image d1 = {g a, g b}"
        "path_image d0 \<union> path_image d1 = path_image d"
        using exists_double_arc[OF d_props(1) d_props(2) ga_d gb_d ga_ne_gb] by metis
      \<comment> \<open>Endpoints and basic simple-path facts for the frontier arcs d0, d1\<close>
      have sp_d0: "simple_path d0" and sp_d1: "simple_path d1"
        using da(1,2) arc_imp_simple_path by blast+
      have rev_ends: "pathstart (reversepath d1) = g a" "pathfinish (reversepath d1) = g b"
        using da(5,6) by (simp_all add: pathstart_reversepath pathfinish_reversepath)
      have rev_pi: "path_image (reversepath d1) = path_image d1"
        by (simp add: path_image_reversepath)
      have sp_rev_d1: "simple_path (reversepath d1)"
        using sp_d1 by (simp add: simple_path_reversepath)
      have sp_g0: "simple_path g0" using arcs(1) arc_imp_simple_path by blast
      note g0_ends = arcs(3,4)
      have gab_g0: "g a \<in> path_image g0" "g b \<in> path_image g0"
        using g0_ends by (metis pathstart_in_path_image pathfinish_in_path_image)+
      have gab_d0: "g a \<in> path_image d0" "g b \<in> path_image d0"
        using da(3,4) by (metis pathstart_in_path_image pathfinish_in_path_image)+
      have gab_d1: "g a \<in> path_image d1" "g b \<in> path_image d1"
        using da(5,6) by (metis pathstart_in_path_image pathfinish_in_path_image)+
      have d0_sub: "path_image d0 \<subseteq> path_image d" and d1_sub: "path_image d1 \<subseteq> path_image d"
        using da(8) by blast+
      \<comment> \<open>The open part of g0 lies in the interior, hence g0 meets the frontier only at g a, g b\<close>
      have g0_decomp: "path_image g0 = g ` {a<..<b} \<union> {g a, g b}"
      proof -
        have "{a..b} = {a<..<b} \<union> {a, b}"
          using \<open>a < b\<close> by auto
        then have "g ` {a..b} = g ` {a<..<b} \<union> {g a, g b}"
          by (simp add: image_Un)
        then show ?thesis using arcs(7) by simp
      qed
      have g0_d_int: "path_image g0 \<inter> path_image d = {g a, g b}"
      proof -
        have "g ` {a<..<b} \<inter> path_image d = {}"
          using assms(9) d_props(4) by simp
        moreover have "{g a, g b} \<subseteq> path_image d"
          using ga_d gb_d by simp
        ultimately show ?thesis
          using g0_decomp by blast
      qed
      have d0_g0_int: "path_image d0 \<inter> path_image g0 = {g a, g b}"
      proof
        show "path_image d0 \<inter> path_image g0 \<subseteq> {g a, g b}"
          using d0_sub g0_d_int by blast
        show "{g a, g b} \<subseteq> path_image d0 \<inter> path_image g0"
          using gab_d0 gab_g0 by blast
      qed
      have d1_g0_int: "path_image d1 \<inter> path_image g0 = {g a, g b}"
      proof
        show "path_image d1 \<inter> path_image g0 \<subseteq> {g a, g b}"
          using d1_sub g0_d_int by blast
        show "{g a, g b} \<subseteq> path_image d1 \<inter> path_image g0"
          using gab_d1 gab_g0 by blast
      qed
      \<comment> \<open>Split the inside via SPLIT_INSIDE_SIMPLE_CLOSED_CURVE on d0, reversepath d1, g0\<close>
      have d_union: "path_image d0 \<union> path_image (reversepath d1) = path_image d"
        using da(8) rev_pi by simp
      have inside_eq: "inside (path_image d0 \<union> path_image (reversepath d1)) = interior (convex hull path_image g)"
      proof -
        have "bounded (convex hull path_image g)"
          by (intro bounded_convex_hull compact_imp_bounded compact_simple_path_image \<open>simple_path g\<close>)
        then have "inside (frontier (convex hull path_image g)) = interior (convex hull path_image g)"
          using inside_frontier_eq_interior convex_convex_hull by blast
        then show ?thesis
          using d_union d_props(4) by simp
      qed
      have g0_inside_ne: "path_image g0 \<inter> inside (path_image d0 \<union> path_image (reversepath d1)) \<noteq> {}"
      proof -
        have "g ` {a<..<b} \<noteq> {}"
          using \<open>a < b\<close> by auto
        moreover have "g ` {a<..<b} \<subseteq> path_image g0"
          using g0_decomp by blast
        moreover have "g ` {a<..<b} \<subseteq> interior (convex hull path_image g)"
          using interior_subset by blast
        ultimately show ?thesis
          using inside_eq by blast
      qed
      have d0_rev_int: "path_image d0 \<inter> path_image (reversepath d1) = {g a, g b}"
        using da(7) rev_pi by simp
      have split:
        "inside (path_image d0 \<union> path_image g0) \<inter> inside (path_image (reversepath d1) \<union> path_image g0) = {}"
        "inside (path_image d0 \<union> path_image g0) \<union> inside (path_image (reversepath d1) \<union> path_image g0) \<union> (path_image g0 - {g a, g b}) = inside (path_image d0 \<union> path_image (reversepath d1))"
        using split_inside_simple_closed_curve[OF sp_d0 da(3,4) sp_rev_d1 rev_ends sp_g0 g0_ends ga_ne_gb
            d0_rev_int d0_g0_int _ g0_inside_ne]
        by (simp_all add: rev_pi d1_g0_int)
      have split1: "inside (path_image d0 \<union> path_image g0) \<inter> inside (path_image d1 \<union> path_image g0) = {}"
        using split(1) rev_pi by simp
      have split2: "inside (path_image d0 \<union> path_image g0) \<union> inside (path_image d1 \<union> path_image g0) \<union> (path_image g0 - {g a, g b}) = interior (convex hull path_image g)"
        using split(2) rev_pi inside_eq by simp
      \<comment> \<open>Step 4 (cont.): orient the split so that g1's interior avoids d0.
          This is a connectedness argument on path_image g1 - {g a, g b}.\<close>
      have arc_rev_g0: "arc (reversepath g0)" using arcs(1) by (simp add: arc_reversepath)
      have J0_loop: "simple_path (d0 +++ reversepath g0)"
      proof (rule simple_path_join_loop)
        show "arc d0" by (rule da(1))
        show "arc (reversepath g0)" by (rule arc_rev_g0)
        show "pathfinish d0 = pathstart (reversepath g0)"
          using da(4) g0_ends by (simp add: pathstart_reversepath)
        show "pathfinish (reversepath g0) = pathstart d0"
          using da(3) g0_ends by (simp add: pathfinish_reversepath)
        show "path_image d0 \<inter> path_image (reversepath g0) \<subseteq> {pathstart d0, pathstart (reversepath g0)}"
          using d0_g0_int da(3) g0_ends by (simp add: path_image_reversepath pathstart_reversepath)
      qed
      have J0_close: "pathfinish (d0 +++ reversepath g0) = pathstart (d0 +++ reversepath g0)"
        using da(3) g0_ends by (simp add: pathstart_reversepath pathfinish_reversepath)
      have J0_pi: "path_image (d0 +++ reversepath g0) = path_image d0 \<union> path_image g0"
        using da(4) g0_ends by (simp add: path_image_join pathstart_reversepath path_image_reversepath)
      have J1_loop: "simple_path (reversepath d1 +++ reversepath g0)"
      proof (rule simple_path_join_loop)
        show "arc (reversepath d1)" using da(2) by (simp add: arc_reversepath)
        show "arc (reversepath g0)" by (rule arc_rev_g0)
        show "pathfinish (reversepath d1) = pathstart (reversepath g0)"
          using da(5) g0_ends by (simp add: pathstart_reversepath pathfinish_reversepath)
        show "pathfinish (reversepath g0) = pathstart (reversepath d1)"
          using da(6) g0_ends by (simp add: pathstart_reversepath pathfinish_reversepath)
        show "path_image (reversepath d1) \<inter> path_image (reversepath g0) \<subseteq> {pathstart (reversepath d1), pathstart (reversepath g0)}"
          using d1_g0_int da(6) g0_ends by (simp add: path_image_reversepath pathstart_reversepath pathfinish_reversepath)
      qed
      have J1_close: "pathfinish (reversepath d1 +++ reversepath g0) = pathstart (reversepath d1 +++ reversepath g0)"
        using da(6) g0_ends by (simp add: pathstart_reversepath pathfinish_reversepath)
      have J1_pi: "path_image (reversepath d1 +++ reversepath g0) = path_image d1 \<union> path_image g0"
        using da(5) g0_ends by (simp add: path_image_join pathstart_reversepath pathfinish_reversepath path_image_reversepath)
      have J0_jio: "frontier (inside (path_image d0 \<union> path_image g0)) = path_image d0 \<union> path_image g0"
        using Jordan_inside_outside[OF J0_loop J0_close] J0_pi by simp
      have J1_jio: "frontier (inside (path_image d1 \<union> path_image g0)) = path_image d1 \<union> path_image g0"
        using Jordan_inside_outside[OF J1_loop J1_close] J1_pi by simp
      have cl_J0: "closure (inside (path_image d0 \<union> path_image g0)) = inside (path_image d0 \<union> path_image g0) \<union> path_image d0 \<union> path_image g0"
        using closure_Un_frontier[of "inside (path_image d0 \<union> path_image g0)"] J0_jio by (simp add: Un_assoc)
      have cl_J1: "closure (inside (path_image d1 \<union> path_image g0)) = inside (path_image d1 \<union> path_image g0) \<union> path_image d1 \<union> path_image g0"
        using closure_Un_frontier[of "inside (path_image d1 \<union> path_image g0)"] J1_jio by (simp add: Un_assoc)
      have sp_g1: "simple_path g1" using arcs(2) arc_imp_simple_path by blast
      define S where "S = path_image g1 - {g b, g a}"
      have S_conn: "connected S"
        using connected_simple_path_endless[OF sp_g1] arcs(5,6) unfolding S_def
        by (simp add: insert_commute)
      have g1_g0_int: "path_image g1 \<inter> path_image g0 = {g a, g b}"
        using arcs(9) by (simp add: Int_commute)
      have S_g0: "S \<inter> path_image g0 = {}"
        using g1_g0_int unfolding S_def by blast
      have d0d1_front: "path_image d0 \<union> path_image d1 = frontier (convex hull path_image g)"
        using da(8) d_props(4) by simp
      have cldd0: "closed (path_image d0 \<union> path_image g0)"
        using da(1) arcs(1) by (simp add: closed_path_image arc_imp_path closed_Un)
      have cldd1: "closed (path_image d1 \<union> path_image g0)"
        using da(2) arcs(1) by (simp add: closed_path_image arc_imp_path closed_Un)
      have op_in0: "open (inside (path_image d0 \<union> path_image g0))" using cldd0 by (rule open_inside)
      have op_in1: "open (inside (path_image d1 \<union> path_image g0))" using cldd1 by (rule open_inside)
      have g1_in_hull: "path_image g1 \<subseteq> convex hull path_image g"
      proof -
        have "path_image g1 \<subseteq> path_image g" using arcs(10) by blast
        also have "\<dots> \<subseteq> convex hull path_image g" by (rule hull_subset)
        finally show ?thesis .
      qed
      have hull_closed: "closed (convex hull path_image g)"
        by (simp add: compact_imp_closed compact_convex_hull compact_simple_path_image \<open>simple_path g\<close>)
      have g1_cover: "path_image g1 \<subseteq> interior (convex hull path_image g) \<union> frontier (convex hull path_image g)"
        using g1_in_hull hull_closed by (simp add: frontier_def closure_closed) blast
      \<comment> \<open>S = g1 minus its endpoints is covered by the two \<open>inside\<close>-plus-arc regions ...\<close>
      have cover: "\<And>z. z \<in> S \<Longrightarrow> z \<in> (inside (path_image d1 \<union> path_image g0) \<union> path_image d1) \<union> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0))"
      proof -
        fix z assume zS: "z \<in> S"
        have zg1: "z \<in> path_image g1" and zng0: "z \<notin> path_image g0"
          using zS S_def g1_g0_int by auto
        consider "z \<in> interior (convex hull path_image g)" | "z \<in> frontier (convex hull path_image g)"
          using g1_cover zg1 by blast
        then show "z \<in> (inside (path_image d1 \<union> path_image g0) \<union> path_image d1) \<union> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0))"
        proof cases
          case 1
          then have "z \<in> inside (path_image d0 \<union> path_image g0) \<union> inside (path_image d1 \<union> path_image g0) \<union> (path_image g0 - {g a, g b})"
            using split2 by simp
          then show ?thesis using zng0 by blast
        next
          case 2
          then have "z \<in> path_image d0 \<union> path_image d1" using d0d1_front by simp
          then show ?thesis by blast
        qed
      qed
      have ic0: "inside (path_image d1 \<union> path_image g0) \<inter> closure (inside (path_image d0 \<union> path_image g0)) = {}"
      proof -
        have "inside (path_image d1 \<union> path_image g0) \<inter> inside (path_image d0 \<union> path_image g0) = {}"
          using split1 by (simp add: Int_commute)
        then show ?thesis using open_Int_closure_eq_empty[OF op_in1, of "inside (path_image d0 \<union> path_image g0)"] by simp
      qed
      have ic1: "inside (path_image d0 \<union> path_image g0) \<inter> closure (inside (path_image d1 \<union> path_image g0)) = {}"
      proof -
        have "inside (path_image d0 \<union> path_image g0) \<inter> inside (path_image d1 \<union> path_image g0) = {}"
          using split1 by simp
        then show ?thesis using open_Int_closure_eq_empty[OF op_in0, of "inside (path_image d1 \<union> path_image g0)"] by simp
      qed
      have d0_cl: "path_image d0 \<subseteq> closure (inside (path_image d0 \<union> path_image g0))"
        using cl_J0 by blast
      have d1_cl: "path_image d1 \<subseteq> closure (inside (path_image d1 \<union> path_image g0))"
        using cl_J1 by blast
      have in1_d0: "inside (path_image d1 \<union> path_image g0) \<inter> path_image d0 = {}"
        using ic0 d0_cl by blast
      have d1_in0: "path_image d1 \<inter> inside (path_image d0 \<union> path_image g0) = {}"
        using ic1 d1_cl by blast
      have in1_in0: "inside (path_image d1 \<union> path_image g0) \<inter> inside (path_image d0 \<union> path_image g0) = {}"
        using split1 by (simp add: Int_commute)
      have d1_d0_S: "\<And>z. z \<in> S \<Longrightarrow> \<not>(z \<in> path_image d1 \<and> z \<in> path_image d0)"
        using da(7) unfolding S_def by blast
      \<comment> \<open>... and the two regions are disjoint on S, so S splits into two relatively clopen pieces\<close>
      have disj: "\<And>z. z \<in> S \<Longrightarrow> \<not>(z \<in> (inside (path_image d1 \<union> path_image g0) \<union> path_image d1) \<and> z \<in> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0)))"
      proof -
        fix z assume zS: "z \<in> S"
        show "\<not>(z \<in> (inside (path_image d1 \<union> path_image g0) \<union> path_image d1) \<and> z \<in> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0)))"
          using in1_d0 in1_in0 d1_in0 d1_d0_S[OF zS] by blast
      qed
      have eqA: "S - closure (inside (path_image d1 \<union> path_image g0)) = S \<inter> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0))"
      proof -
        have "S - closure (inside (path_image d1 \<union> path_image g0)) = S - (inside (path_image d1 \<union> path_image g0) \<union> path_image d1)"
          using cl_J1 S_g0 by blast
        also have "\<dots> = S \<inter> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0))"
          using cover disj by blast
        finally show ?thesis .
      qed
      have eqB: "S - closure (inside (path_image d0 \<union> path_image g0)) = S \<inter> (path_image d1 \<union> inside (path_image d1 \<union> path_image g0))"
      proof -
        have "S - closure (inside (path_image d0 \<union> path_image g0)) = S - (inside (path_image d0 \<union> path_image g0) \<union> path_image d0)"
          using cl_J0 S_g0 by blast
        also have "\<dots> = S \<inter> (path_image d1 \<union> inside (path_image d1 \<union> path_image g0))"
          using cover disj by blast
        finally show ?thesis .
      qed
      have opA: "openin (top_of_set S) (S - closure (inside (path_image d1 \<union> path_image g0)))"
      proof -
        have "S - closure (inside (path_image d1 \<union> path_image g0)) = S \<inter> (- closure (inside (path_image d1 \<union> path_image g0)))"
          by blast
        moreover have "open (- closure (inside (path_image d1 \<union> path_image g0)))"
          by (simp add: open_Compl)
        ultimately show ?thesis
          by (simp add: openin_open_Int)
      qed
      have opB: "openin (top_of_set S) (S - closure (inside (path_image d0 \<union> path_image g0)))"
      proof -
        have "S - closure (inside (path_image d0 \<union> path_image g0)) = S \<inter> (- closure (inside (path_image d0 \<union> path_image g0)))"
          by blast
        moreover have "open (- closure (inside (path_image d0 \<union> path_image g0)))"
          by (simp add: open_Compl)
        ultimately show ?thesis
          by (simp add: openin_open_Int)
      qed
      have AB_cover: "(S - closure (inside (path_image d1 \<union> path_image g0))) \<union> (S - closure (inside (path_image d0 \<union> path_image g0))) = S"
        using eqA eqB cover by blast
      have AB_disj: "(S - closure (inside (path_image d1 \<union> path_image g0))) \<inter> (S - closure (inside (path_image d0 \<union> path_image g0))) = {}"
        using eqA eqB in1_d0 in1_in0 d1_in0 d1_d0_S split1 by auto
      have one_empty: "(S - closure (inside (path_image d1 \<union> path_image g0))) = {} \<or> (S - closure (inside (path_image d0 \<union> path_image g0))) = {}"
        using S_conn opA opB AB_cover AB_disj connected_openin by blast
      have disjunction: "S \<inter> path_image d0 = {} \<or> S \<inter> path_image d1 = {}"
      proof -
        consider "S - closure (inside (path_image d1 \<union> path_image g0)) = {}" | "S - closure (inside (path_image d0 \<union> path_image g0)) = {}"
          using one_empty by blast
        then show ?thesis
        proof cases
          case 1
          then have "S \<inter> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0)) = {}" using eqA by simp
          then show ?thesis by blast
        next
          case 2
          then have "S \<inter> (path_image d1 \<union> inside (path_image d1 \<union> path_image g0)) = {}" using eqB by simp
          then show ?thesis by blast
        qed
      qed
      \<comment> \<open>Whichever arc S avoids becomes d0 (reversing the pair in the second case)\<close>
      show thesis
      proof (cases "S \<inter> path_image d0 = {}")
        case True
        then have c11: "(path_image g1 - {g b, g a}) \<inter> path_image d0 = {}" unfolding S_def by simp
        show thesis
          by (rule that[OF da(1) da(2) da(3) da(4) da(5) da(6) da(7) da(8) split1 split2 c11])
      next
        case False
        then have d1e: "(path_image g1 - {g b, g a}) \<inter> path_image d1 = {}"
          using disjunction unfolding S_def by blast
        have r1: "arc (reversepath d1)" using da(2) by (simp add: arc_reversepath)
        have r2: "arc (reversepath d0)" using da(1) by (simp add: arc_reversepath)
        have r3: "pathstart (reversepath d1) = g a" using da(6) by (simp add: pathstart_reversepath)
        have r4: "pathfinish (reversepath d1) = g b" using da(5) by (simp add: pathfinish_reversepath)
        have r5: "pathstart (reversepath d0) = g b" using da(4) by (simp add: pathstart_reversepath)
        have r6: "pathfinish (reversepath d0) = g a" using da(3) by (simp add: pathfinish_reversepath)
        have r7: "path_image (reversepath d1) \<inter> path_image (reversepath d0) = {g a, g b}"
          using da(7) by (simp add: path_image_reversepath Int_commute)
        have r8: "path_image (reversepath d1) \<union> path_image (reversepath d0) = path_image d"
          using da(8) by (simp add: path_image_reversepath Un_commute)
        have r9: "inside (path_image (reversepath d1) \<union> path_image g0) \<inter> inside (path_image (reversepath d0) \<union> path_image g0) = {}"
          using split1 by (simp add: path_image_reversepath Int_commute)
        have r10: "inside (path_image (reversepath d1) \<union> path_image g0) \<union> inside (path_image (reversepath d0) \<union> path_image g0) \<union> (path_image g0 - {g a, g b}) = interior (convex hull path_image g)"
          using split2 by (simp add: path_image_reversepath Un_commute Un_left_commute)
        have r11: "(path_image g1 - {g b, g a}) \<inter> path_image (reversepath d1) = {}"
          using d1e by (simp add: path_image_reversepath)
        show thesis
          by (rule that[OF r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11])
      qed
    qed
    \<comment> \<open>Step 3: g(a) and g(b) are on the path_image of d\<close>
    have ga_in_d: "g a \<in> path_image d" and gb_in_d: "g b \<in> path_image d"
      using d_props(4) assms(7,8) by auto
    \<comment> \<open>Step 4: build h as the straight segment from g(a) to g(b) on (a,b), unchanged elsewhere.
       (front_arc is no longer used; see step_lemma_proof_body.thy in memory for derivation notes.)\<close>
    show ?thesis
    proof -
      have hull_closed: "closed (convex hull path_image g)"
        by (simp add: compact_imp_closed compact_convex_hull compact_simple_path_image \<open>simple_path g\<close>)
      have compact_hull: "compact (convex hull path_image g)"
        by (simp add: compact_convex_hull compact_simple_path_image \<open>simple_path g\<close>)
      have d1_sub_hull: "convex hull (path_image d1) \<subseteq> convex hull (path_image g)"
      proof -
        have "path_image d1 \<subseteq> path_image d" using d_split(8) by blast
        also have "\<dots> = frontier (convex hull path_image g)" using d_props(4) .
        also have "\<dots> \<subseteq> convex hull path_image g"
          using hull_closed by (simp add: frontier_def closure_closed)
        finally have "path_image d1 \<subseteq> convex hull path_image g" .
        then show ?thesis by (simp add: hull_minimal)
      qed
      have km_ext: "convex hull path_image g = convex hull {x. x extreme_point_of (convex hull path_image g)}"
        using Krein_Milman_Minkowski[OF compact_hull convex_convex_hull] by simp
      have test_cl: "\<And>x. x \<in> path_image g \<Longrightarrow> x \<in> closure (convex hull path_image g)"
        using closure_subset hull_subset by (meson subset_iff)
      have test_front: "\<And>x. x \<in> closure (convex hull path_image g) \<Longrightarrow> x \<notin> interior (convex hull path_image g) \<Longrightarrow> x \<in> frontier (convex hull path_image g)"
        by (simp add: frontier_def)
      have ext_in_g_front: "\<And>x. x extreme_point_of (convex hull path_image g) \<Longrightarrow> x \<in> path_image g \<inter> path_image d"
      proof -
        fix x assume e: "x extreme_point_of (convex hull path_image g)"
        have xg: "x \<in> path_image g" using extreme_point_of_convex_hull[OF e] .
        then have "x \<in> closure (convex hull path_image g)" using test_cl by blast
        moreover have "x \<notin> interior (convex hull path_image g)"
          using extreme_point_not_in_interior[OF e] .
        ultimately have "x \<in> frontier (convex hull path_image g)" using test_front by blast
        then have "x \<in> path_image d" using d_props(4) by simp
        with xg show "x \<in> path_image g \<inter> path_image d" by simp
      qed
      have gab_d1: "g a \<in> path_image d1" "g b \<in> path_image d1"
        using d_split(5,6) by (metis pathstart_in_path_image pathfinish_in_path_image)+
      have g0_int_d: "path_image g0 \<inter> path_image d = {g a, g b}"
      proof -
        have "g ` {a<..<b} \<inter> path_image d = {}" using assms(9) d_props(4) by simp
        moreover have "path_image g0 = g ` {a<..<b} \<union> {g a, g b}"
        proof -
          have "{a..b} = {a<..<b} \<union> {a, b}" using \<open>a < b\<close> by auto
          then have "g ` {a..b} = g ` {a<..<b} \<union> {g a, g b}" by (simp add: image_Un)
          then show ?thesis using arcs(7) by simp
        qed
        moreover have "{g a, g b} \<subseteq> path_image d" using ga_in_d gb_in_d by simp
        ultimately show ?thesis by blast
      qed
      have g1_int_d: "path_image g1 \<inter> path_image d \<subseteq> path_image d1"
      proof -
        have "path_image g1 \<inter> path_image d0 \<subseteq> {g a, g b}" using d_split(11) by blast
        then have "path_image g1 \<inter> path_image d0 \<subseteq> path_image d1" using gab_d1 by blast
        moreover have "path_image g1 \<inter> path_image d1 \<subseteq> path_image d1" by blast
        moreover have "path_image d = path_image d0 \<union> path_image d1" using d_split(8) by simp
        ultimately show ?thesis by blast
      qed
      have hull_d1_eq: "convex hull (path_image d1) = convex hull (path_image g)"
      proof (rule subset_antisym)
        show "convex hull (path_image d1) \<subseteq> convex hull (path_image g)" by (rule d1_sub_hull)
      next
        have "path_image g \<inter> path_image d \<subseteq> path_image d1"
        proof -
          have "path_image g = path_image g0 \<union> path_image g1" using arcs(10) by simp
          then have "path_image g \<inter> path_image d = (path_image g0 \<inter> path_image d) \<union> (path_image g1 \<inter> path_image d)" by blast
          also have "\<dots> \<subseteq> {g a, g b} \<union> path_image d1" using g0_int_d g1_int_d by blast
          also have "\<dots> \<subseteq> path_image d1" using gab_d1 by blast
          finally show ?thesis .
        qed
        then have "{x. x extreme_point_of (convex hull path_image g)} \<subseteq> path_image d1"
          using ext_in_g_front by blast
        then have "convex hull {x. x extreme_point_of (convex hull path_image g)} \<subseteq> convex hull (path_image d1)"
          by (rule hull_mono)
        then show "convex hull (path_image g) \<subseteq> convex hull (path_image d1)" using km_ext by simp
      qed
      \<comment> \<open>The straight segment between g(a) and g(b) lies on the frontier, via seg_frontier_aux
         applied to the arc d1 (whose hull is the whole convex hull by hull_d1_eq).\<close>
      have seg_in_frontier: "closed_segment (g a) (g b) \<subseteq> frontier (convex hull path_image g)"
      proof (rule seg_frontier_aux[of _ _ _ d1])
        show "convex (convex hull path_image g)" by (rule convex_convex_hull)
        show "compact (convex hull path_image g)" by (rule compact_hull)
        show "interior (convex hull path_image g) \<noteq> {}" by (rule interior_ne)
        show "g a \<in> frontier (convex hull path_image g)" by (rule assms(7))
        show "g b \<in> frontier (convex hull path_image g)" by (rule assms(8))
        show "g a \<noteq> g b" by (rule ga_ne_gb)
        show "path_image d1 \<subseteq> frontier (convex hull path_image g)"
          using d_split(8) d_props(4) by blast
        show "connected (path_image d1 - {g a, g b})"
          using connected_simple_path_endless[OF arc_imp_simple_path[OF d_split(2)]] d_split(5,6)
          by (simp add: insert_commute)
        show "g a \<in> path_image d1" by (rule gab_d1(1))
        show "g b \<in> path_image d1" by (rule gab_d1(2))
        show "convex hull path_image d1 = convex hull path_image g" by (rule hull_d1_eq)
      qed
      have rev_d1_arc: "arc (reversepath d1)" using d_split(2) by (simp add: arc_reversepath)
      have rev_d1_start: "pathstart (reversepath d1) = g a" using d_split(6) by (simp add: pathstart_reversepath)
      have rev_d1_finish: "pathfinish (reversepath d1) = g b" using d_split(5) by (simp add: pathfinish_reversepath)
      have rev_d1_pi: "path_image (reversepath d1) = path_image d1" by (simp add: path_image_reversepath)
      have d0d1_pi: "path_image d0 \<union> path_image (reversepath d1) = frontier (convex hull path_image g)"
        using rev_d1_pi d_split(8) d_props(4) by simp
      have int_ends: "path_image d0 \<inter> path_image (reversepath d1) = {pathstart d0, pathfinish d0}"
        using d_split(7) rev_d1_pi d_split(3,4) by simp
      have seg_sub_union: "closed_segment (g a) (g b) \<subseteq> path_image d0 \<union> path_image (reversepath d1)"
        using seg_in_frontier d0d1_pi by simp
      have dich: "path_image d0 \<subseteq> closed_segment (g a) (g b) \<or> path_image (reversepath d1) \<subseteq> closed_segment (g a) (g b)"
      proof (rule connected_subset_arc_pair[where g=d0 and h="reversepath d1"])
        show "arc d0" by (rule d_split(1))
        show "arc (reversepath d1)" by (rule rev_d1_arc)
        show "pathstart d0 = pathstart (reversepath d1)" using d_split(3) rev_d1_start by simp
        show "pathfinish d0 = pathfinish (reversepath d1)" using d_split(4) rev_d1_finish by simp
        show "path_image d0 \<inter> path_image (reversepath d1) = {pathstart d0, pathfinish d0}" by (rule int_ends)
        show "connected (closed_segment (g a) (g b))" by simp
        show "closed_segment (g a) (g b) \<subseteq> path_image d0 \<union> path_image (reversepath d1)" by (rule seg_sub_union)
        show "pathstart d0 \<in> closed_segment (g a) (g b)" using d_split(3) by simp
        show "pathfinish d0 \<in> closed_segment (g a) (g b)" using d_split(4) by simp
      qed
      have not_d1: "\<not> (path_image (reversepath d1) \<subseteq> closed_segment (g a) (g b))"
      proof
        assume "path_image (reversepath d1) \<subseteq> closed_segment (g a) (g b)"
        then have "path_image d1 \<subseteq> closed_segment (g a) (g b)" using rev_d1_pi by simp
        then have "convex hull (path_image d1) \<subseteq> convex hull (closed_segment (g a) (g b))"
          by (rule hull_mono)
        also have "convex hull (closed_segment (g a) (g b)) = closed_segment (g a) (g b)"
          by (simp add: hull_same convex_closed_segment)
        finally have "convex hull (path_image g) \<subseteq> closed_segment (g a) (g b)"
          using hull_d1_eq by simp
        then have "interior (convex hull (path_image g)) \<subseteq> interior (closed_segment (g a) (g b))"
          by (rule interior_mono)
        also have "interior (closed_segment (g a) (g b)) = {}"
          by (rule interior_closed_segment_ge2) simp
        finally show False using interior_ne by simp
      qed
      have d0_sub_seg: "path_image d0 \<subseteq> closed_segment (g a) (g b)"
        using dich not_d1 by blast
      have d0_eq_seg: "path_image d0 = closed_segment (g a) (g b)"
      proof (rule connected_subset_segment)
        show "connected (path_image d0)" using d_split(1) by (simp add: connected_arc_image)
        show "path_image d0 \<subseteq> closed_segment (g a) (g b)" by (rule d0_sub_seg)
        show "g a \<in> path_image d0" using gab_d1 d_split(3) by (metis pathstart_in_path_image)
        show "g b \<in> path_image d0" using d_split(4) by (metis pathfinish_in_path_image)
      qed
      define h where "h \<equiv> \<lambda>t. if t \<in> {a<..<b} then g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a) else g t"
      have interval_img: "(\<lambda>t. (t - a)/(b - a)) ` {a..b} = {0..1}"
      proof -
        have nz: "b - a > 0" using \<open>a < b\<close> by simp
        have "(\<lambda>t. (t - a)/(b - a)) ` {a..b} = (\<lambda>t. t/(b-a) - a/(b-a)) ` {a..b}"
          by (simp add: diff_divide_distrib)
        also have "\<dots> = {a/(b-a) - a/(b-a) .. b/(b-a) - a/(b-a)}"
          using nz by (subst image_affinity_atLeastAtMost_div_diff) auto
        also have "\<dots> = {0..1}" using nz by (simp add: diff_divide_distrib [symmetric] divide_self_if)
        finally show ?thesis .
      qed
      have lin: "(\<lambda>t. g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a)) ` {a..b} = closed_segment (g a) (g b)"
      proof -
        have "(\<lambda>t. g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a)) ` {a..b}
            = (\<lambda>u. g a + u *\<^sub>R (g b - g a)) ` ((\<lambda>t. (t-a)/(b-a)) ` {a..b})"
          by (simp add: image_image)
        also have "\<dots> = (\<lambda>u. g a + u *\<^sub>R (g b - g a)) ` {0..1}"
          using interval_img by simp
        also have "\<dots> = closed_segment (g a) (g b)"
          by (simp add: closed_segment_image_interval algebra_simps cong: image_cong)
        finally show ?thesis .
      qed
      have hh_eq_lin: "\<And>t. t \<in> {a..b} \<Longrightarrow> h t = g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a)"
      proof -
        fix t assume t: "t \<in> {a..b}"
        show "h t = g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a)"
        proof (cases "t \<in> {a<..<b}")
          case True then show ?thesis by (simp add: h_def)
        next
          case False
          with t have "t = a \<or> t = b" by auto
          then show ?thesis using \<open>a < b\<close> by (auto simp: h_def)
        qed
      qed
      have hh_seg: "h ` {a..b} = closed_segment (g a) (g b)"
      proof -
        have "h ` {a..b} = (\<lambda>t. g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a)) ` {a..b}"
          by (rule image_cong[OF refl hh_eq_lin])
        with lin show ?thesis by simp
      qed
      have a_ge0: "0 \<le> a" and b_le1: "b \<le> 1" using ab01 by auto
      have hh_0: "h 0 = g 0" using a_ge0 by (simp add: h_def)
      have hh_1: "h 1 = g 1" using b_le1 by (simp add: h_def)
      have hh_start: "pathstart h = pathstart g" by (simp add: pathstart_def hh_0)
      have hh_finish: "pathfinish h = pathstart g"
        using assms(2) by (simp add: pathstart_def pathfinish_def hh_1)
      have hh_frontier: "h ` {a..b} \<subseteq> frontier (convex hull path_image g)"
        using hh_seg seg_in_frontier by simp
      have hh_out_img: "h ` ({0..1} - {a<..<b}) = g ` ({0..1} - {a<..<b})"
      proof (rule image_cong[OF refl])
        fix x assume x: "x \<in> {0..1} - {a<..<b}"
        have "x \<notin> {a<..<b}" using x by simp
        then show "h x = g x" unfolding h_def by presburger
      qed
      have univ: "{0..1} = {a..b} \<union> ({0..1} - {a<..<b})"
        using ab01 \<open>a < b\<close> by auto
      have pi_h: "path_image h = closed_segment (g a) (g b) \<union> g ` ({0..1} - {a<..<b})"
      proof -
        have "path_image h = h ` {0..1}" by (simp add: path_image_def)
        also have "\<dots> = h ` {a..b} \<union> h ` ({0..1} - {a<..<b})"
          by (subst univ) (simp add: image_Un)
        also have "\<dots> = closed_segment (g a) (g b) \<union> g ` ({0..1} - {a<..<b})"
          using hh_seg hh_out_img by simp
        finally show ?thesis .
      qed
      have front_in_hull: "frontier (convex hull path_image g) \<subseteq> convex hull path_image g"
        using hull_closed by (simp add: frontier_def closure_closed)
      have seg_in: "closed_segment (g a) (g b) \<subseteq> convex hull path_image g"
        using seg_in_frontier front_in_hull by (rule subset_trans)
      have out_in: "g ` ({0..1} - {a<..<b}) \<subseteq> convex hull path_image g"
      proof -
        have "g ` ({0..1} - {a<..<b}) \<subseteq> path_image g" by (auto simp: path_image_def)
        also have "path_image g \<subseteq> convex hull path_image g" by (rule hull_subset)
        finally show ?thesis .
      qed
      have hull_hh: "convex hull (path_image h) = convex hull (path_image g)"
      proof (rule subset_antisym)
        show "convex hull (path_image h) \<subseteq> convex hull (path_image g)"
          using pi_h seg_in out_in by (simp add: hull_minimal)
      next
        have "convex hull (path_image g) = convex hull (g ` ({0..1} - {a<..<b}))"
          using hull_eq by simp
        also have "\<dots> \<subseteq> convex hull (path_image h)"
          using pi_h by (simp add: hull_mono)
        finally show "convex hull (path_image g) \<subseteq> convex hull (path_image h)" .
      qed
      have L_nonneg: "0 \<le> L"
      proof -
        have le: "dist (g a) (g b) \<le> L * dist a b" using assms(3) ab01 by blast
        have pos: "0 < dist a b" using \<open>a < b\<close> by simp
        have "0 \<le> dist (g a) (g b)" by simp
        with le have "0 \<le> L * dist a b" by linarith
        with pos show ?thesis by (simp add: zero_le_mult_iff)
      qed
      have dab: "dist (g a) (g b) \<le> L * (b - a)"
      proof -
        have "dist (g a) (g b) \<le> L * dist a b" using assms(3) ab01 by blast
        also have "dist a b = b - a" using \<open>a < b\<close> by (simp add: dist_real_def)
        finally show ?thesis .
      qed
      have lip_mid: "L-lipschitz_on {a..b} h"
      proof (rule lipschitz_onI)
        show "0 \<le> L" by (rule L_nonneg)
        fix x y assume xy: "x \<in> {a..b}" "y \<in> {a..b}"
        have hx: "h x = g a + ((x - a)/(b - a)) *\<^sub>R (g b - g a)" using hh_eq_lin xy(1) .
        have hy: "h y = g a + ((y - a)/(b - a)) *\<^sub>R (g b - g a)" using hh_eq_lin xy(2) .
        have factor: "h x - h y = ((x - a)/(b - a) - (y - a)/(b - a)) *\<^sub>R (g b - g a)"
          by (simp add: hx hy scaleR_left_diff_distrib)
        have e1: "dist (h x) (h y) = \<bar>(x - a)/(b - a) - (y - a)/(b - a)\<bar> * norm (g b - g a)"
          by (simp add: dist_norm factor)
        have diff_eq: "(x - a)/(b - a) - (y - a)/(b - a) = (x - y)/(b - a)"
          by (simp add: diff_divide_distrib)
        have e2: "\<bar>(x - a)/(b - a) - (y - a)/(b - a)\<bar> = \<bar>x - y\<bar> / (b - a)"
          using \<open>a < b\<close> by (simp add: diff_eq abs_divide)
        have e3: "norm (g b - g a) / (b - a) \<le> L"
        proof -
          have "norm (g b - g a) = dist (g a) (g b)" by (simp add: dist_norm norm_minus_commute)
          then show ?thesis using dab \<open>a < b\<close> by (simp add: divide_le_eq)
        qed
        have "dist (h x) (h y) = (norm (g b - g a) / (b - a)) * \<bar>x - y\<bar>"
          using e1 e2 by simp
        also have "\<dots> \<le> L * \<bar>x - y\<bar>"
          using mult_right_mono[OF e3 abs_ge_zero] by simp
        finally show "dist (h x) (h y) \<le> L * dist x y" by (simp add: dist_real_def)
      qed
      have lip_g: "L-lipschitz_on {0..1} g"
        by (rule lipschitz_onI[OF _ L_nonneg]) (rule assms(3))
      have hh_lo: "\<And>x. x \<in> {0..a} \<Longrightarrow> h x = g x"
        by (auto simp: h_def)
      have hh_hi: "\<And>x. x \<in> {b..1} \<Longrightarrow> h x = g x"
        using \<open>a < b\<close> by (auto simp: h_def)
      have lip_lo: "L-lipschitz_on {0..a} h"
      proof -
        have "{0..a} \<subseteq> {0..1}" using a_ge0 b_le1 \<open>a<b\<close> by auto
        then have "L-lipschitz_on {0..a} g" using lip_g lipschitz_on_subset by blast
        then show ?thesis by (rule lipschitz_on_transform) (simp add: hh_lo)
      qed
      have lip_hi: "L-lipschitz_on {b..1} h"
      proof -
        have "{b..1} \<subseteq> {0..1}" using a_ge0 b_le1 \<open>a<b\<close> by auto
        then have "L-lipschitz_on {b..1} g" using lip_g lipschitz_on_subset by blast
        then show ?thesis by (rule lipschitz_on_transform) (simp add: hh_hi)
      qed
      have lip_lomid: "L-lipschitz_on {0..b} h"
      proof -
        have "L-lipschitz_on {0..b} (\<lambda>x. if x \<le> a then h x else h x)"
          using lip_lo lip_mid by (rule lipschitz_on_concat) simp
        then show ?thesis by simp
      qed
      have lip_hh: "L-lipschitz_on {0..1} h"
      proof -
        have "L-lipschitz_on {0..1} (\<lambda>x. if x \<le> b then h x else h x)"
          using lip_lomid lip_hi by (rule lipschitz_on_concat) simp
        then show ?thesis by simp
      qed
      have path_hh: "path h"
        using lip_hh by (simp add: path_def lipschitz_on_continuous_on)
      have g1_img: "g ` ({0..1} - {a<..<b}) = path_image g1" using arcs(8) by simp
      have opse_in_d0: "open_segment (g a) (g b) \<subseteq> path_image d0"
        using d0_eq_seg by (simp add: open_segment_def)
      have opse_g1_disj: "open_segment (g a) (g b) \<inter> path_image g1 = {}"
      proof -
        have "open_segment (g a) (g b) \<inter> {g b, g a} = {}"
          by (simp add: open_segment_def)
        moreover have "(path_image g1 - {g b, g a}) \<inter> path_image d0 = {}" using d_split(11) .
        ultimately show ?thesis using opse_in_d0 by blast
      qed
      have hh_in_opse: "\<And>x. x \<in> {a<..<b} \<Longrightarrow> h x \<in> open_segment (g a) (g b)"
      proof -
        fix x assume x: "x \<in> {a<..<b}"
        have "(x - a)/(b - a) \<in> {0<..<1}"
          using x \<open>a < b\<close> by (auto simp: divide_simps)
        then have "g a + ((x-a)/(b-a)) *\<^sub>R (g b - g a) \<in> open_segment (g a) (g b)"
          using ga_ne_gb by (auto simp: in_segment algebra_simps)
        then show "h x \<in> open_segment (g a) (g b)" using x by (simp add: h_def)
      qed
      have hh_inj_mid: "\<And>x y. x \<in> {a<..<b} \<Longrightarrow> y \<in> {a<..<b} \<Longrightarrow> h x = h y \<Longrightarrow> x = y"
      proof -
        fix x y assume x: "x \<in> {a<..<b}" and y: "y \<in> {a<..<b}" and eq: "h x = h y"
        have "g a + ((x-a)/(b-a)) *\<^sub>R (g b - g a) = g a + ((y-a)/(b-a)) *\<^sub>R (g b - g a)"
          using eq x y by (simp add: h_def)
        then have "((x-a)/(b-a)) *\<^sub>R (g b - g a) = ((y-a)/(b-a)) *\<^sub>R (g b - g a)" by simp
        then have eqfrac: "(x-a)/(b-a) = (y-a)/(b-a)"
          using ga_ne_gb by (simp add: real_vector.scale_right_imp_eq)
        show "x = y" using eqfrac \<open>a < b\<close> by (simp add: divide_cancel_right)
      qed
      have g_loop_free: "loop_free g" using assms(1) by (simp add: simple_path_def)
      have hh_out_g: "\<And>x. x \<notin> {a<..<b} \<Longrightarrow> h x = g x" unfolding h_def by presburger
      have hh_out_in_g1: "\<And>x. x \<in> {0..1} \<Longrightarrow> x \<notin> {a<..<b} \<Longrightarrow> h x \<in> path_image g1"
        using hh_out_g g1_img by blast
      have gloopD: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> g x = g y \<Longrightarrow> x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
        using g_loop_free unfolding loop_free_def by blast
      have testM1: "\<And>x y. x \<in> {a<..<b} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> y \<notin> {a<..<b} \<Longrightarrow> h x = h y \<Longrightarrow> False"
      proof -
        fix x y assume xb: "x \<in> {a<..<b}" and y01: "y \<in> {0..1}" and yo: "y \<notin> {a<..<b}" and eq: "h x = h y"
        have "h x \<in> open_segment (g a) (g b)" using hh_in_opse xb .
        then have "h y \<in> open_segment (g a) (g b)" using eq by simp
        moreover have "h y \<in> path_image g1" using hh_out_in_g1 y01 yo .
        ultimately have "h y \<in> open_segment (g a) (g b) \<inter> path_image g1" by simp
        then show False using opse_g1_disj by simp
      qed
      have loopfree_hh: "loop_free h"
        unfolding loop_free_def
      proof (intro ballI impI)
        fix x y assume x: "x \<in> {0..1}" and y: "y \<in> {0..1}" and eq: "h x = h y"
        consider (II) "x \<in> {a<..<b}" "y \<in> {a<..<b}"
          | (OO) "x \<notin> {a<..<b}" "y \<notin> {a<..<b}"
          | (M1) "x \<in> {a<..<b}" "y \<notin> {a<..<b}"
          | (M2) "x \<notin> {a<..<b}" "y \<in> {a<..<b}"
          by blast
        then show "x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
        proof cases
          case II
          then show ?thesis using hh_inj_mid eq by blast
        next
          case OO
          then have "g x = g y" using eq hh_out_g by simp
          then show ?thesis using gloopD x y by blast
        next
          case M1
          then have False using testM1 x y eq by blast
          then show ?thesis ..
        next
          case M2
          then have False using testM1[of y x] x y eq by simp
          then show ?thesis ..
        qed
      qed
      have simple_hh: "simple_path h"
        using path_hh loopfree_hh by (simp add: simple_path_def)
      have lip_imp_bv: "\<And>(f::real\<Rightarrow>complex) M c d. M-lipschitz_on {c..d} f \<Longrightarrow> has_bounded_variation_on f {c..d}"
      proof -
        fix f :: "real \<Rightarrow> complex" and M c d assume lip: "M-lipschitz_on {c..d} f"
        show "has_bounded_variation_on f {c..d}"
          unfolding has_bounded_variation_on_interval
        proof (intro exI[where x="max 0 (M * (d - c))"] allI impI)
          fix D assume D: "D division_of {c..d}"
          have Mnn: "0 \<le> M" using lip by (simp add: lipschitz_on_nonneg)
          have elem: "\<And>k. k \<in> D \<Longrightarrow> norm (f (Sup k) - f (Inf k)) \<le> M * content k"
          proof -
            fix k assume k: "k \<in> D"
            obtain a' b' where ab': "k = cbox a' b'" using division_ofD(4)[OF D k] by blast
            have ksub: "k \<subseteq> {c..d}" using division_ofD(2)[OF D k] by simp
            have kne: "k \<noteq> {}" using division_ofD(3)[OF D k] by simp
            then have leab: "a' \<le> b'" using ab' by (simp add: box_ne_empty)
            have infk: "Inf k = a'" and supk: "Sup k = b'" using ab' leab by auto
            have mem: "a' \<in> {c..d}" "b' \<in> {c..d}" using ksub ab' leab by auto
            have "norm (f b' - f a') = dist (f b') (f a')" by (simp add: dist_norm)
            also have "\<dots> \<le> M * dist b' a'" using lipschitz_onD[OF lip] mem by simp
            also have "dist b' a' = b' - a'" using leab by (simp add: dist_real_def)
            also have "M * (b' - a') = M * content k" using ab' leab by (simp add: content_real)
            finally show "norm (f (Sup k) - f (Inf k)) \<le> M * content k" using infk supk by simp
          qed
          have "(\<Sum>k\<in>D. norm (f (Sup k) - f (Inf k))) \<le> (\<Sum>k\<in>D. M * content k)"
            by (rule sum_mono) (rule elem)
          also have "\<dots> = M * (\<Sum>k\<in>D. content k)" by (simp add: sum_distrib_left)
          also have "(\<Sum>k\<in>D. content k) = content {c..d}"
            using additive_content_division[OF D[unfolded box_real(2)[symmetric]]] by (simp add: box_real(2))
          also have "M * content {c..d} \<le> max 0 (M * (d - c))"
            using Mnn by (simp add: content_real_if)
          finally show "(\<Sum>k\<in>D. norm (f (Sup k) - f (Inf k))) \<le> max 0 (M * (d - c))" .
        qed
      qed
      have bv_hh: "has_bounded_variation_on h {0..1}" using lip_imp_bv[OF lip_hh] .
      have bv_g: "has_bounded_variation_on g {0..1}" using lip_imp_bv[OF lip_g] .
      have bv_hh_ab: "has_bounded_variation_on h {a..b}"
        using bv_hh has_bounded_variation_on_subset a_ge0 b_le1 \<open>a<b\<close> by (meson atLeastatMost_subset_iff dual_order.refl)
      have bv_g_ab: "has_bounded_variation_on g {a..b}"
        using bv_g has_bounded_variation_on_subset a_ge0 b_le1 \<open>a<b\<close> by (meson atLeastatMost_subset_iff dual_order.refl)
      have a01: "a \<in> {0..1}" and b01: "b \<in> {0..1}" using ab01 by auto
      have bv_hh_a1: "has_bounded_variation_on h {a..1}"
        using bv_hh has_bounded_variation_on_subset a_ge0 b_le1 \<open>a<b\<close> by (meson atLeastatMost_subset_iff order_refl)
      have bv_g_a1: "has_bounded_variation_on g {a..1}"
        using bv_g has_bounded_variation_on_subset a_ge0 b_le1 \<open>a<b\<close> by (meson atLeastatMost_subset_iff order_refl)
      have split_hh: "vector_variation {0..1} h = vector_variation {0..a} h + vector_variation {a..b} h + vector_variation {b..1} h"
      proof -
        have "vector_variation {0..1} h = vector_variation {0..a} h + vector_variation {a..1} h"
          using vector_variation_combine[OF bv_hh a01] .
        moreover have "vector_variation {a..1} h = vector_variation {a..b} h + vector_variation {b..1} h"
          using vector_variation_combine[OF bv_hh_a1, of b] \<open>a<b\<close> b_le1 by simp
        ultimately show ?thesis by simp
      qed
      have split_g: "vector_variation {0..1} g = vector_variation {0..a} g + vector_variation {a..b} g + vector_variation {b..1} g"
      proof -
        have "vector_variation {0..1} g = vector_variation {0..a} g + vector_variation {a..1} g"
          using vector_variation_combine[OF bv_g a01] .
        moreover have "vector_variation {a..1} g = vector_variation {a..b} g + vector_variation {b..1} g"
          using vector_variation_combine[OF bv_g_a1, of b] \<open>a<b\<close> b_le1 by simp
        ultimately show ?thesis by simp
      qed
      have lo_eq: "vector_variation {0..a} h = vector_variation {0..a} g"
        by (rule vector_variation_cong) (simp add: hh_lo)
      have hi_eq: "vector_variation {b..1} h = vector_variation {b..1} g"
        by (rule vector_variation_cong) (simp add: hh_hi)
      have hh_a: "h a = g a" using \<open>a<b\<close> by (simp add: h_def)
      have hh_b: "h b = g b" using \<open>a<b\<close> by (simp add: h_def)
      have mid_hh_ge: "vector_variation {a..b} h \<ge> norm (g b - g a)"
      proof -
        have "norm (h b - h a) \<le> vector_variation {a..b} h"
          using vector_variation_ge_norm_function[OF bv_hh_ab, of b a] \<open>a<b\<close> by simp
        then show ?thesis using hh_a hh_b by (simp add: norm_minus_commute)
      qed
      have mid_hh_le: "vector_variation {a..b} h \<le> norm (g b - g a)"
      proof -
        have key: "\<And>D. D division_of {a..b} \<Longrightarrow> (\<Sum>k\<in>D. norm (h (Sup k) - h (Inf k))) \<le> norm (g b - g a)"
        proof -
          fix D assume D: "D division_of {a..b}"
          have elem: "\<And>k. k \<in> D \<Longrightarrow> norm (h (Sup k) - h (Inf k)) = ((Sup k - Inf k)/(b-a)) * norm (g b - g a)"
          proof -
            fix k assume k: "k \<in> D"
            obtain a' b' where ab': "k = cbox a' b'" using division_ofD(4)[OF D k] by blast
            have ksub: "k \<subseteq> {a..b}" using division_ofD(2)[OF D k] by simp
            have kne: "k \<noteq> {}" using division_ofD(3)[OF D k] by simp
            then have leab: "a' \<le> b'" using ab' by (simp add: box_ne_empty)
            have infk: "Inf k = a'" and supk: "Sup k = b'" using ab' leab by auto
            have mem: "a' \<in> {a..b}" "b' \<in> {a..b}" using ksub ab' leab by auto
            have ha: "h a' = g a + ((a'-a)/(b-a)) *\<^sub>R (g b - g a)" using hh_eq_lin mem(1) .
            have hb: "h b' = g a + ((b'-a)/(b-a)) *\<^sub>R (g b - g a)" using hh_eq_lin mem(2) .
            have "h b' - h a' = (((b'-a)/(b-a)) - ((a'-a)/(b-a))) *\<^sub>R (g b - g a)"
              by (simp add: ha hb scaleR_left_diff_distrib)
            also have "((b'-a)/(b-a)) - ((a'-a)/(b-a)) = (b'-a')/(b-a)"
              by (simp add: diff_divide_distrib)
            finally have "h b' - h a' = ((b'-a')/(b-a)) *\<^sub>R (g b - g a)" by simp
            then have "norm (h b' - h a') = \<bar>(b'-a')/(b-a)\<bar> * norm (g b - g a)" by simp
            also have "\<bar>(b'-a')/(b-a)\<bar> = (b'-a')/(b-a)" using leab \<open>a<b\<close> by simp
            finally show "norm (h (Sup k) - h (Inf k)) = ((Sup k - Inf k)/(b-a)) * norm (g b - g a)"
              using infk supk by simp
          qed
          have content_elem: "\<And>k. k \<in> D \<Longrightarrow> (Sup k - Inf k) = content k"
          proof -
            fix k assume k: "k \<in> D"
            obtain a' b' where ab': "k = cbox a' b'" using division_ofD(4)[OF D k] by blast
            have kne: "k \<noteq> {}" using division_ofD(3)[OF D k] by simp
            then have leab: "a' \<le> b'" using ab' by (simp add: box_ne_empty)
            then show "(Sup k - Inf k) = content k" using ab' by (simp add: content_real)
          qed
          have "(\<Sum>k\<in>D. norm (h (Sup k) - h (Inf k))) = (\<Sum>k\<in>D. ((Sup k - Inf k)/(b-a)) * norm (g b - g a))"
            by (rule sum.cong[OF refl]) (rule elem)
          also have "\<dots> = ((\<Sum>k\<in>D. (Sup k - Inf k))/(b-a)) * norm (g b - g a)"
            by (simp add: sum_distrib_right sum_divide_distrib)
          also have "(\<Sum>k\<in>D. (Sup k - Inf k)) = (\<Sum>k\<in>D. content k)"
            by (rule sum.cong[OF refl]) (rule content_elem)
          also have "(\<Sum>k\<in>D. content k) = content {a..b}"
            using additive_content_division[OF D[unfolded box_real(2)[symmetric]]] by (simp add: box_real(2))
          also have "content {a..b} = b - a" using \<open>a<b\<close> by (simp add: content_real)
          also have "((b-a)/(b-a)) * norm (g b - g a) = norm (g b - g a)" using \<open>a<b\<close> by simp
          finally show "(\<Sum>k\<in>D. norm (h (Sup k) - h (Inf k))) \<le> norm (g b - g a)" by simp
        qed
        show ?thesis
          using bv_hh_ab key has_bounded_vector_variation_on_interval by blast
      qed
      have mid_hh_eq: "vector_variation {a..b} h = norm (g b - g a)"
        using mid_hh_ge mid_hh_le by simp
      define c where "c = (a + b)/2"
      have c_mem: "c \<in> {a<..<b}" using \<open>a<b\<close> by (simp add: c_def)
      have ac: "a < c" and cb: "c < b" using c_mem by auto
      have gc_not_seg: "g c \<notin> closed_segment (g a) (g b)"
      proof
        assume "g c \<in> closed_segment (g a) (g b)"
        then have "g c \<in> frontier (convex hull path_image g)" using seg_in_frontier by blast
        moreover have "g c \<in> g ` {a<..<b}" using c_mem by blast
        ultimately show False using assms(9) by blast
      qed
      have strict_tri: "dist (g a) (g b) < dist (g a) (g c) + dist (g c) (g b)"
      proof -
        have "\<not> between (g a, g b) (g c)" using gc_not_seg by (simp add: between_mem_segment)
        then have "dist (g a) (g c) + dist (g c) (g b) \<noteq> dist (g a) (g b)"
          by (simp add: between)
        moreover have "dist (g a) (g b) \<le> dist (g a) (g c) + dist (g c) (g b)"
          by (rule dist_triangle)
        ultimately show ?thesis by linarith
      qed
      have c_in_ab: "c \<in> {a..b}" using ac cb by simp
      have bv_g_ac: "has_bounded_variation_on g {a..c}"
        using bv_g_ab has_bounded_variation_on_subset ac cb by (meson atLeastatMost_subset_iff order_refl less_imp_le)
      have bv_g_cb: "has_bounded_variation_on g {c..b}"
        using bv_g_ab has_bounded_variation_on_subset ac cb by (meson atLeastatMost_subset_iff order_refl less_imp_le)
      have mid_g_gt: "vector_variation {a..b} g > norm (g b - g a)"
      proof -
        have split: "vector_variation {a..b} g = vector_variation {a..c} g + vector_variation {c..b} g"
          using vector_variation_combine[OF bv_g_ab c_in_ab] .
        have ge1: "norm (g c - g a) \<le> vector_variation {a..c} g"
          using vector_variation_ge_norm_function[OF bv_g_ac, of c a] ac cb by (simp add: norm_minus_commute)
        have ge2: "norm (g b - g c) \<le> vector_variation {c..b} g"
          using vector_variation_ge_norm_function[OF bv_g_cb, of b c] ac cb by (simp add: norm_minus_commute)
        have "norm (g b - g a) < norm (g c - g a) + norm (g b - g c)"
          using strict_tri by (simp add: dist_norm norm_minus_commute)
        also have "\<dots> \<le> vector_variation {a..c} g + vector_variation {c..b} g"
          using ge1 ge2 by simp
        also have "\<dots> = vector_variation {a..b} g" using split by simp
        finally show ?thesis .
      qed
      have path_length_lt: "path_length h < path_length g"
      proof -
        have "path_length h = vector_variation {0..a} g + vector_variation {a..b} h + vector_variation {b..1} g"
          using split_hh lo_eq hi_eq by (simp add: path_length_def)
        also have "vector_variation {a..b} h = norm (g b - g a)" using mid_hh_eq .
        finally have hh_val: "path_length h = vector_variation {0..a} g + norm (g b - g a) + vector_variation {b..1} g" .
        have "path_length g = vector_variation {0..a} g + vector_variation {a..b} g + vector_variation {b..1} g"
          using split_g by (simp add: path_length_def)
        with hh_val mid_g_gt show ?thesis by simp
      qed
      have lip_show: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
        using lipschitz_onD[OF lip_hh] .
      have hh_agree: "\<And>x. x \<notin> {a<..<b} \<Longrightarrow> h x = g x" using hh_out_g .
      show thesis
        using that[OF simple_hh hh_start hh_finish lip_show path_length_lt hull_hh hh_agree hh_frontier] .
    qed
  qed
qed

text \<open>A nonempty bounded open connected subset of the reals is an open interval.\<close>

lemma open_bounded_connected_real_is_interval:
  fixes c :: "real set"
  assumes "open c" "connected c" "c \<noteq> {}" "bounded c"
  shows "c = {Inf c<..<Sup c}"
proof -
  have isiv: "is_interval c" using assms(2) by (simp add: is_interval_connected_1)
  have bb: "bdd_below c" and ba: "bdd_above c" using assms(4) bounded_imp_bdd_below bounded_imp_bdd_above by auto
  have InfnotIn: "Inf c \<notin> c"
  proof
    assume "Inf c \<in> c"
    then obtain b where "b < Inf c" "{b<..Inf c} \<subseteq> c" using open_left[OF assms(1) \<open>Inf c \<in> c\<close>, of "Inf c - 1"] by auto
    then have "(Inf c + b)/2 \<in> c" by auto
    moreover have "(Inf c + b)/2 < Inf c" using \<open>b < Inf c\<close> by simp
    ultimately show False using bb cInf_lower leD by blast
  qed
  have SupnotIn: "Sup c \<notin> c"
  proof
    assume "Sup c \<in> c"
    then obtain b where "Sup c < b" "{Sup c..<b} \<subseteq> c" using open_right[OF assms(1) \<open>Sup c \<in> c\<close>, of "Sup c + 1"] by auto
    then have "(Sup c + b)/2 \<in> c" by auto
    moreover have "Sup c < (Sup c + b)/2" using \<open>Sup c < b\<close> by simp
    ultimately show False using ba cSup_upper leD by blast
  qed
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> c"
    then have "Inf c \<le> x" "x \<le> Sup c" using bb ba cInf_lower cSup_upper by auto
    moreover have "x \<noteq> Inf c" using \<open>x \<in> c\<close> InfnotIn by auto
    moreover have "x \<noteq> Sup c" using \<open>x \<in> c\<close> SupnotIn by auto
    ultimately show "x \<in> {Inf c<..<Sup c}" by auto
  next
    fix x assume x: "x \<in> {Inf c<..<Sup c}"
    obtain u where u: "u \<in> c" "u < x" using x assms(3) bb
      by (metis cInf_lessD greaterThanLessThan_iff)
    obtain v where v: "v \<in> c" "x < v" using x assms(3) ba
      by (metis less_cSupD greaterThanLessThan_iff)
    show "x \<in> c" using isiv u v by (meson is_interval_1 less_imp_le)
  qed
qed

text \<open>The reduced convexification subgoal: a unit-speed (Lipschitz) simple closed rectifiable loop
  starting on the frontier of its convex hull can be replaced by a no-longer loop with the same
  convex hull whose image IS that frontier. The components of the part of the parameter interval
  whose image avoids the frontier are countably many open intervals; this is captured by
  @{text decomp} (still to be proved), and the deviating arcs are then straightened via
  @{text step_lemma}.\<close>

lemma convexification_unit_speed:
  fixes \<gamma> :: "real \<Rightarrow> complex"
  assumes rect: "rectifiable_path \<gamma>" and simp: "simple_path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
    and frstart: "pathstart \<gamma> \<in> frontier (convex hull (path_image \<gamma>))"
    and lip: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (\<gamma> x) (\<gamma> y) \<le> path_length \<gamma> * dist x y"
  shows "\<exists>h. rectifiable_path h \<and> simple_path h \<and> pathfinish h = pathstart h \<and> path_length h \<le> path_length \<gamma> \<and> convex hull (path_image h) = convex hull (path_image \<gamma>) \<and> path_image h = frontier (convex hull (path_image \<gamma>))"
proof (cases "path_image \<gamma> \<subseteq> frontier (convex hull (path_image \<gamma>))")
  case True
  \<comment> \<open>Already on the frontier: \<gamma> itself works (its image equals the frontier).\<close>
  have "path_image \<gamma> = frontier (convex hull (path_image \<gamma>))"
    using frontier_convex_hull_subset_path_image[OF simp loop True] True by blast
  then show ?thesis using rect simp loop by (intro exI[of _ \<gamma>]) auto
next
  case False
  have path\<gamma>: "path \<gamma>" using simp by (rule simple_path_imp_path)
  define F where "F = frontier (convex hull (path_image \<gamma>))"
  define s where "s = {t \<in> {0..1}. \<gamma> t \<notin> F}"
  have clF: "closed F" unfolding F_def by simp
  have cont\<gamma>: "continuous_on {0..1} \<gamma>" using path\<gamma> by (simp add: path_def)
  have g0F: "\<gamma> 0 \<in> F" using frstart F_def by (simp add: pathstart_def)
  have g1F: "\<gamma> 1 \<in> F" using frstart loop F_def by (simp add: pathstart_def pathfinish_def)
  \<comment> \<open>Since both endpoints map into F, the deviating set s avoids 0 and 1, hence is open in \<real>.\<close>
  have s_sub: "s \<subseteq> {0<..<1}"
  proof
    fix t assume "t \<in> s"
    then have t01: "t \<in> {0..1}" and tnF: "\<gamma> t \<notin> F" unfolding s_def by auto
    have "t \<noteq> 0" using tnF g0F by auto
    moreover have "t \<noteq> 1" using tnF g1F by auto
    ultimately show "t \<in> {0<..<1}" using t01 by auto
  qed
  have s_openin: "openin (top_of_set {0..1}) s"
  proof -
    have "openin (top_of_set {0..1}) ({0..1} \<inter> \<gamma> -` (- F))"
      using cont\<gamma> clF by (intro continuous_openin_preimage_gen) auto
    moreover have "{0..1} \<inter> \<gamma> -` (- F) = s" unfolding s_def by auto
    ultimately show ?thesis by simp
  qed
  have opens: "open s"
  proof -
    have "openin (top_of_set {0<..<1}) s"
      using s_openin s_sub by (metis greaterThanLessThan_subseteq_atLeastAtMost_iff openin_subset_trans order_refl zero_le_one)
    then show ?thesis by (metis open_greaterThanLessThan openin_open_trans)
  qed
  have s_ne: "s \<noteq> {}"
  proof -
    from False obtain z where "z \<in> path_image \<gamma>" "z \<notin> F" unfolding F_def by blast
    then obtain t where "t \<in> {0..1}" "\<gamma> t = z" by (auto simp: path_image_def)
    then have "t \<in> s" using \<open>z \<notin> F\<close> unfolding s_def by auto
    then show ?thesis by auto
  qed
  \<comment> \<open>Component decomposition: the components of s are countably many open intervals
     \<open>{a n<..<b n}\<close>, each with both endpoints mapped by \<gamma> onto the frontier F.\<close>
  have decomp: "\<exists>a b::nat\<Rightarrow>real. (\<forall>n. a n \<in> {0..1}) \<and> (\<forall>n. b n \<in> {0..1}) \<and> (\<forall>n. a n \<le> b n) \<and> (\<forall>n. \<gamma> (a n) \<in> F) \<and> (\<forall>n. \<gamma> (b n) \<in> F) \<and> components s = {{a n<..<b n} | n. n \<in> (UNIV::nat set)}"
  proof -
    have comp_open: "\<And>c. c \<in> components s \<Longrightarrow> open c" using opens by (rule open_components)
    have comp_disj: "disjoint (components s)"
      using pairwise_disjoint_components by (simp add: disjoint_def pairwise_def disjnt_def)
    have comp_count: "countable (components s)"
      using comp_open comp_disj by (rule countable_disjoint_open_subsets)
    have comp_ne: "components s \<noteq> {}" using s_ne by (simp add: components_eq_empty)
    define q where "q = from_nat_into (components s)"
    have q_range: "range q = components s"
      unfolding q_def using comp_ne comp_count by (rule range_from_nat_into)
    have q_comp: "\<And>n. q n \<in> components s" using q_range by auto
    have s_sub01: "s \<subseteq> {0..1}" using s_sub by auto
    have s_bdd: "bounded s" using s_sub01 bounded_closed_interval bounded_subset by blast
    have qsub: "\<And>n. q n \<subseteq> s" using q_comp in_components_subset by blast
    have q_interval: "\<And>n. q n = {Inf (q n)<..<Sup (q n)}"
    proof -
      fix n
      have o: "open (q n)" using q_comp comp_open by blast
      have c: "connected (q n)" using q_comp in_components_connected by blast
      have nem: "q n \<noteq> {}" using q_comp in_components_nonempty by blast
      have bd: "bounded (q n)" using qsub s_bdd bounded_subset by blast
      show "q n = {Inf (q n)<..<Sup (q n)}" using o c nem bd by (rule open_bounded_connected_real_is_interval)
    qed
    define a where "a = (\<lambda>n. Inf (q n))"
    define b where "b = (\<lambda>n. Sup (q n))"
    have qab: "\<And>n. q n = {a n<..<b n}" using q_interval by (simp add: a_def b_def)
    have ablt: "\<And>n. a n < b n"
    proof -
      fix n
      have "q n \<noteq> {}" using q_comp in_components_nonempty by blast
      then show "a n < b n" using qab by (metis greaterThanLessThan_empty_iff not_less)
    qed
    have clq: "\<And>n. closure (q n) = {a n..b n}" using qab ablt by (simp add: closure_greaterThanLessThan)
    have cls01: "closure s \<subseteq> {0..1}"
      using s_sub closure_mono[of s "{0<..<1}"] closure_greaterThanLessThan[of "0::real" 1] by simp
    have ab01: "\<And>n. a n \<in> {0..1} \<and> b n \<in> {0..1}"
    proof -
      fix n
      have "{a n..b n} = closure (q n)" using clq by simp
      also have "closure (q n) \<subseteq> closure s" using qsub by (simp add: closure_mono)
      also have "closure s \<subseteq> {0..1}" using cls01 by simp
      finally have sub: "{a n..b n} \<subseteq> {0..1}" .
      have "a n \<in> {a n..b n}" "b n \<in> {a n..b n}" using ablt[of n] by auto
      then show "a n \<in> {0..1} \<and> b n \<in> {0..1}" using sub by blast
    qed
    have a_notin: "\<And>n. a n \<notin> s"
    proof (rule ccontr)
      fix n assume "\<not> a n \<notin> s"
      then have ains: "a n \<in> s" by simp
      have qns: "q n \<subseteq> s" by (rule qsub)
      have sub: "{a n..<b n} \<subseteq> s"
      proof
        fix x assume "x \<in> {a n..<b n}"
        then have "x = a n \<or> x \<in> {a n<..<b n}" by auto
        then show "x \<in> s" using ains qns qab by auto
      qed
      moreover have "connected {a n..<b n}" by (rule connected_Ico)
      moreover have "{a n..<b n} \<noteq> {}" using ablt[of n] by auto
      moreover have "q n \<subseteq> {a n..<b n}" using qab by auto
      ultimately have "{a n..<b n} = q n"
        using q_comp[of n] in_components_maximal by blast
      then show False using ablt[of n] qab by (metis atLeastLessThan_iff greaterThanLessThan_iff less_irrefl order_refl)
    qed
    have b_notin: "\<And>n. b n \<notin> s"
    proof (rule ccontr)
      fix n assume "\<not> b n \<notin> s"
      then have bins: "b n \<in> s" by simp
      have qns: "q n \<subseteq> s" by (rule qsub)
      have sub: "{a n<..b n} \<subseteq> s"
      proof
        fix x assume "x \<in> {a n<..b n}"
        then have "x = b n \<or> x \<in> {a n<..<b n}" by auto
        then show "x \<in> s" using bins qns qab by auto
      qed
      moreover have "connected {a n<..b n}" by (rule connected_Ioc)
      moreover have "{a n<..b n} \<noteq> {}" using ablt[of n] by auto
      moreover have "q n \<subseteq> {a n<..b n}" using qab by auto
      ultimately have "{a n<..b n} = q n"
        using q_comp[of n] in_components_maximal by blast
      then show False using ablt[of n] qab by (metis greaterThanAtMost_iff greaterThanLessThan_iff less_irrefl order_refl)
    qed
    have gaF: "\<And>n. \<gamma> (a n) \<in> F"
    proof -
      fix n
      have "a n \<in> {0..1}" using ab01 by simp
      moreover have "a n \<notin> s" by (rule a_notin)
      ultimately show "\<gamma> (a n) \<in> F" unfolding s_def by auto
    qed
    have gbF: "\<And>n. \<gamma> (b n) \<in> F"
    proof -
      fix n
      have "b n \<in> {0..1}" using ab01 by simp
      moreover have "b n \<notin> s" by (rule b_notin)
      ultimately show "\<gamma> (b n) \<in> F" unfolding s_def by auto
    qed
    have comp_eq: "components s = {{a n<..<b n} | n. n \<in> (UNIV::nat set)}"
    proof -
      have "components s = range q" using q_range by simp
      also have "\<dots> = {{a n<..<b n} | n. n \<in> (UNIV::nat set)}" using qab by auto
      finally show ?thesis .
    qed
    show "\<exists>a b::nat\<Rightarrow>real. (\<forall>n. a n \<in> {0..1}) \<and> (\<forall>n. b n \<in> {0..1}) \<and> (\<forall>n. a n \<le> b n) \<and> (\<forall>n. \<gamma> (a n) \<in> F) \<and> (\<forall>n. \<gamma> (b n) \<in> F) \<and> components s = {{a n<..<b n} | n. n \<in> (UNIV::nat set)}"
      using ab01 ablt gaF gbF comp_eq by (intro exI[of _ a] exI[of _ b]) (auto simp: less_imp_le)
  qed
  note [[quick_and_dirty]]
  \<comment> \<open>Extract the deviating arcs from the decomposition.\<close>
  from decomp obtain a b :: "nat \<Rightarrow> real" where
    ab01: "\<And>n. a n \<in> {0..1}" "\<And>n. b n \<in> {0..1}" and
    able: "\<And>n. a n \<le> b n" and
    gaF: "\<And>n. \<gamma> (a n) \<in> F" and gbF: "\<And>n. \<gamma> (b n) \<in> F" and
    comps: "components s = {{a n<..<b n} | n. n \<in> (UNIV::nat set)}" by auto
  \<comment> \<open>U n collects the first n deviating arcs; P n h is the invariant for the n-th
     approximation: a Lipschitz simple closed loop with the same convex hull, mapping the
     first n arcs onto the frontier and equal to \<gamma> elsewhere.\<close>
  define U where "U = (\<lambda>n::nat. \<Union> {{a m<..<b m} | m. m < n})"
  define P where "P = (\<lambda>n h. simple_path h \<and> rectifiable_path h \<and> pathstart h = pathstart \<gamma> \<and> pathfinish h = pathfinish \<gamma> \<and> convex hull (path_image h) = convex hull (path_image \<gamma>) \<and> (\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. dist (h x) (h y) \<le> path_length \<gamma> * dist x y) \<and> (\<forall>x\<in>U n. h x \<in> F) \<and> (\<forall>x. x \<notin> U n \<longrightarrow> h x = \<gamma> x))"
  have U0: "U 0 = {}" by (simp add: U_def)
  have base: "P 0 \<gamma>"
    unfolding P_def using simp rect lip by (simp add: U0)
  have arc_comp: "\<And>n. {a n<..<b n} \<in> components s" using comps by auto
  have arc_in_s: "\<And>n. {a n<..<b n} \<subseteq> s" using arc_comp in_components_subset by blast
  have arc_off_F: "\<And>n x. x \<in> {a n<..<b n} \<Longrightarrow> \<gamma> x \<notin> F"
    using arc_in_s s_def by blast
  have USuc: "\<And>n. U (Suc n) = U n \<union> {a n<..<b n}"
    by (auto simp: U_def less_Suc_eq)
  have U_sub_s: "\<And>n. U n \<subseteq> s"
  proof -
    fix n
    show "U n \<subseteq> s"
    proof
      fix x assume "x \<in> U n"
      then obtain m where "m < n" "x \<in> {a m<..<b m}" by (auto simp: U_def)
      then show "x \<in> s" using arc_in_s by blast
    qed
  qed
  have an_notin_s: "\<And>n. a n \<notin> s" using gaF s_def by blast
  have bn_notin_s: "\<And>n. b n \<notin> s" using gbF s_def by blast
  have an_notin_U: "\<And>n. a n \<notin> U n" using an_notin_s U_sub_s by blast
  have bn_notin_U: "\<And>n. b n \<notin> U n" using bn_notin_s U_sub_s by blast
  have arc_sub_U: "\<And>i j::nat. i < j \<Longrightarrow> {a i<..<b i} \<subseteq> U j"
  proof -
    fix i j :: nat assume "i < j"
    then have "{a i<..<b i} \<in> {{a k<..<b k} | k. k < j}" by auto
    then show "{a i<..<b i} \<subseteq> U j" by (auto simp: U_def)
  qed
  have U_mem: "\<And>x n. x \<in> U n \<Longrightarrow> \<exists>i<n. x \<in> {a i<..<b i}"
  proof -
    fix x n assume "x \<in> U n"
    then show "\<exists>i<n. x \<in> {a i<..<b i}" unfolding U_def by blast
  qed
  have arc_disj: "\<And>i j. {a i<..<b i} \<noteq> {a j<..<b j} \<Longrightarrow> {a i<..<b i} \<inter> {a j<..<b j} = {}"
    using arc_comp components_nonoverlap by blast
  have arc_disj_U: "\<And>n. \<not> {a n<..<b n} \<subseteq> U n \<Longrightarrow> {a n<..<b n} \<inter> U n = {}"
  proof -
    fix n assume nsub: "\<not> {a n<..<b n} \<subseteq> U n"
    show "{a n<..<b n} \<inter> U n = {}"
    proof (rule ccontr)
      assume "{a n<..<b n} \<inter> U n \<noteq> {}"
      then obtain x where x: "x \<in> {a n<..<b n} \<inter> U n" by blast
      then have x1: "x \<in> {a n<..<b n}" and x2: "x \<in> U n" by auto
      from x2 obtain i where i: "i < n" "x \<in> {a i<..<b i}" using U_mem by blast
      have eq: "{a n<..<b n} = {a i<..<b i}" using x1 i(2) arc_disj by blast
      have "{a i<..<b i} \<subseteq> U n" using i(1) arc_sub_U by blast
      then show False using nsub eq by simp
    qed
  qed
  have F_eq: "F = frontier (convex hull (path_image \<gamma>))" by (simp add: F_def)
  \<comment> \<open>Inductive step: straighten the n-th arc with step\_lemma (unless it is empty or already
     handled), preserving the invariant.\<close>
  have step: "\<And>n h. P n h \<Longrightarrow> \<exists>h'. P (Suc n) h' \<and> (\<forall>x. \<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n) \<longrightarrow> h' x = h x)"
  proof -
    fix n h assume Ph: "P n h"
    have hsimple: "simple_path h" and hrect: "rectifiable_path h"
      and hps: "pathstart h = pathstart \<gamma>" and hpf: "pathfinish h = pathfinish \<gamma>"
      and hhull: "convex hull (path_image h) = convex hull (path_image \<gamma>)"
      and hlip: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> path_length \<gamma> * dist x y"
      and hUF: "\<And>x. x \<in> U n \<Longrightarrow> h x \<in> F"
      and hoff: "\<And>x. x \<notin> U n \<Longrightarrow> h x = \<gamma> x"
      using Ph unfolding P_def by auto
    have hloop: "pathfinish h = pathstart h" using hps hpf loop by simp
    have hF: "frontier (convex hull (path_image h)) = F" using hhull F_eq by simp
    show "\<exists>h'. P (Suc n) h' \<and> (\<forall>x. \<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n) \<longrightarrow> h' x = h x)"
    proof (cases "{a n<..<b n} = {} \<or> {a n<..<b n} \<subseteq> U n")
      case True
      then have "U (Suc n) = U n" using USuc by auto
      then have "P (Suc n) h" using Ph by (simp add: P_def)
      then show ?thesis by (intro exI[of _ h]) auto
    next
      case False
      then have ne: "{a n<..<b n} \<noteq> {}" and nsub: "\<not> {a n<..<b n} \<subseteq> U n" by auto
      have ablt_n: "a n < b n" using ne by simp
      have arc_disj_Un: "{a n<..<b n} \<inter> U n = {}" using nsub arc_disj_U by blast
      have ha: "h (a n) = \<gamma> (a n)" using hoff an_notin_U by simp
      have hb: "h (b n) = \<gamma> (b n)" using hoff bn_notin_U by simp
      have harc: "\<And>x. x \<in> {a n<..<b n} \<Longrightarrow> h x = \<gamma> x" using hoff arc_disj_Un by blast
      have haF: "h (a n) \<in> frontier (convex hull (path_image h))" using ha gaF hF by simp
      have hbF: "h (b n) \<in> frontier (convex hull (path_image h))" using hb gbF hF by simp
      have harc_offF: "h ` {a n<..<b n} \<inter> frontier (convex hull (path_image h)) = {}"
      proof -
        have "h ` {a n<..<b n} \<subseteq> {y. y \<notin> F}" using harc arc_off_F by auto
        then show ?thesis using hF by auto
      qed
      obtain h' where h'simple: "simple_path h'"
        and h'ps: "pathstart h' = pathstart h" and h'pf: "pathfinish h' = pathstart h"
        and h'lip: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h' x) (h' y) \<le> path_length \<gamma> * dist x y"
        and h'len: "path_length h' < path_length h"
        and h'hull: "convex hull (path_image h') = convex hull (path_image h)"
        and h'off: "\<And>x. x \<notin> {a n<..<b n} \<Longrightarrow> h' x = h x"
        and h'arcF: "h' ` {a n..b n} \<subseteq> frontier (convex hull (path_image h))"
        using step_lemma[OF hsimple hloop hlip ablt_n ab01(1)[of n] ab01(2)[of n] haF hbF harc_offF]
        by metis
      have h'rect: "rectifiable_path h'"
        by (rule lipschitz_imp_rectifiable_path[where B="path_length \<gamma>"])
           (use h'lip in \<open>simp add: dist_norm\<close>)
      have h'agree: "\<And>x. \<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n) \<Longrightarrow> h' x = h x"
      proof -
        fix x assume "\<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n)"
        then have "x \<notin> {a n<..<b n}" using arc_disj_Un by blast
        then show "h' x = h x" using h'off by simp
      qed
      have h'UF: "\<And>x. x \<in> U (Suc n) \<Longrightarrow> h' x \<in> F"
      proof -
        fix x assume "x \<in> U (Suc n)"
        then have "x \<in> U n \<or> x \<in> {a n<..<b n}" using USuc by auto
        then show "h' x \<in> F"
        proof
          assume xUn: "x \<in> U n"
          then have "x \<notin> {a n<..<b n}" using arc_disj_Un by blast
          then have "h' x = h x" using h'off by simp
          then show "h' x \<in> F" using xUn hUF by simp
        next
          assume "x \<in> {a n<..<b n}"
          then have "x \<in> {a n..b n}" by auto
          then have "h' x \<in> frontier (convex hull (path_image h))" using h'arcF by auto
          then show "h' x \<in> F" using hF by simp
        qed
      qed
      have h'offSuc: "\<And>x. x \<notin> U (Suc n) \<Longrightarrow> h' x = \<gamma> x"
      proof -
        fix x assume "x \<notin> U (Suc n)"
        then have xn: "x \<notin> U n" and xarc: "x \<notin> {a n<..<b n}" using USuc by auto
        have "h' x = h x" using xarc h'off by simp
        also have "h x = \<gamma> x" using xn hoff by simp
        finally show "h' x = \<gamma> x" .
      qed
      have PSuc: "P (Suc n) h'"
        unfolding P_def
        using h'simple h'rect h'ps hps h'pf loop h'hull hhull h'lip h'UF h'offSuc
        by simp
      show ?thesis using PSuc h'agree by blast
    qed
  qed
  \<comment> \<open>Dependent choice yields the sequence of approximations f.\<close>
  obtain f where f: "\<And>n. P n (f n)"
    and fstep: "\<And>n x. \<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n) \<Longrightarrow> f (Suc n) x = f n x"
    using dependent_nat_choice[where P=P and Q="\<lambda>n h h'. \<forall>x. \<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n) \<longrightarrow> h' x = h x"]
      base step by metis
  \<comment> \<open>For each parameter x the sequence f n x is eventually constant: either x lies in no arc
     (so f n x = \<gamma> x throughout), or it lies in the arc with least index N, after which f is fixed.\<close>
  have evconst: "\<forall>x\<in>{0..1}. \<exists>y. eventually (\<lambda>n. f n x = y) sequentially"
  proof
    fix x :: real assume x01: "x \<in> {0..1}"
    show "\<exists>y. eventually (\<lambda>n. f n x = y) sequentially"
    proof (cases "\<exists>n. x \<in> {a n<..<b n}")
      case False
      have stab: "f n x = f 0 x" for n
      proof (induct n)
        case 0 show ?case by simp
      next
        case (Suc n)
        have "f (Suc n) x = f n x" using fstep False by blast
        then show ?case using Suc by simp
      qed
      then have "eventually (\<lambda>n. f n x = f 0 x) sequentially" by simp
      then show ?thesis by blast
    next
      case True
      define N where "N = (LEAST n. x \<in> {a n<..<b n})"
      have xN: "x \<in> {a N<..<b N}" using True LeastI_ex N_def by (metis (mono_tags, lifting))
      have stab2: "\<And>m. N < m \<Longrightarrow> f (Suc m) x = f m x"
      proof -
        fix m assume Nm: "N < m"
        have "x \<in> U m" using Nm xN arc_sub_U by blast
        then have "\<not>(x \<in> {a m<..<b m} \<and> x \<notin> U m)" by simp
        then show "f (Suc m) x = f m x" using fstep by blast
      qed
      have stab3: "\<And>d. f (Suc N + d) x = f (Suc N) x"
      proof -
        fix d show "f (Suc N + d) x = f (Suc N) x"
        proof (induct d)
          case 0 show ?case by simp
        next
          case (Suc d)
          have "f (Suc (Suc N + d)) x = f (Suc N + d) x" using stab2 by simp
          then show ?case using Suc by simp
        qed
      qed
      have "eventually (\<lambda>n. f n x = f (Suc N) x) sequentially"
      proof (rule eventually_sequentiallyI[where c="Suc N"])
        fix n assume "Suc N \<le> n"
        then obtain d where "n = Suc N + d" using le_Suc_ex by blast
        then show "f n x = f (Suc N) x" using stab3 by simp
      qed
      then show ?thesis by blast
    qed
  qed
  \<comment> \<open>Skolemize to obtain the limit path h: f n x = h x eventually, for each x.\<close>
  obtain h where h: "\<And>x. x \<in> {0..1} \<Longrightarrow> eventually (\<lambda>n. f n x = h x) sequentially"
    using evconst by (metis (mono_tags))
  \<comment> \<open>Properties of the approximants f n, extracted from the invariant P.\<close>
  have fsimple: "\<And>n. simple_path (f n)" using f unfolding P_def by blast
  have fps: "\<And>n. pathstart (f n) = pathstart \<gamma>" using f unfolding P_def by blast
  have fpf: "\<And>n. pathfinish (f n) = pathfinish \<gamma>" using f unfolding P_def by blast
  have fhull: "\<And>n. convex hull (path_image (f n)) = convex hull (path_image \<gamma>)" using f unfolding P_def by blast
  have flip: "\<And>n x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (f n x) (f n y) \<le> path_length \<gamma> * dist x y"
    using f unfolding P_def by blast
  have fUF: "\<And>n x. x \<in> U n \<Longrightarrow> f n x \<in> F" using f unfolding P_def by blast
  have foff: "\<And>n x. x \<notin> U n \<Longrightarrow> f n x = \<gamma> x" using f unfolding P_def by blast
  \<comment> \<open>The limit path h inherits the L-Lipschitz bound (pointwise limit of L-Lipschitz maps).\<close>
  have hlip: "\<And>x y::real. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> path_length \<gamma> * dist x y"
  proof -
    fix x y :: real assume xy: "x \<in> {0..1}" "y \<in> {0..1}"
    have ev: "eventually (\<lambda>n. f n x = h x \<and> f n y = h y) sequentially"
      using h[OF xy(1)] h[OF xy(2)] by eventually_elim simp
    then obtain n where n: "f n x = h x" "f n y = h y"
      unfolding eventually_sequentially by auto
    have "dist (f n x) (f n y) \<le> path_length \<gamma> * dist x y" using flip[OF xy] by blast
    then show "dist (h x) (h y) \<le> path_length \<gamma> * dist x y" using n by simp
  qed
  have hrect: "rectifiable_path h"
    by (rule lipschitz_imp_rectifiable_path[where B="path_length \<gamma>"])
       (use hlip in \<open>simp add: dist_norm\<close>)
  have hpath: "path h" using hrect by (rule rectifiable_path_imp_path)
  have hsimple: "simple_path h"
    unfolding simple_path_def
  proof (intro conjI)
    show "path h" by (rule hpath)
    show "loop_free h"
      unfolding loop_free_def
    proof (intro ballI impI)
      fix x y :: real assume xy: "x \<in> {0..1}" "y \<in> {0..1}" and eq: "h x = h y"
      have ev: "eventually (\<lambda>n. f n x = h x \<and> f n y = h y) sequentially"
        using h[OF xy(1)] h[OF xy(2)] by eventually_elim simp
      then obtain n where n: "f n x = h x" "f n y = h y"
        unfolding eventually_sequentially by auto
      have "f n x = f n y" using n eq by simp
      then show "x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
        using fsimple[of n] xy unfolding simple_path_def loop_free_def by blast
    qed
  qed
  have hloop: "pathfinish h = pathstart h"
  proof -
    have z01: "(0::real) \<in> {0..1}" and o01: "(1::real) \<in> {0..1}" by auto
    have ev: "eventually (\<lambda>n. f n 0 = h 0 \<and> f n 1 = h 1) sequentially"
      using h[OF z01] h[OF o01] by eventually_elim simp
    then obtain n where n: "f n 0 = h 0" "f n 1 = h 1"
      unfolding eventually_sequentially by auto
    have "f n 1 = f n 0" using fps[of n] fpf[of n] loop by (simp add: pathstart_def pathfinish_def)
    then have "h 1 = h 0" using n by simp
    then show ?thesis by (simp add: pathstart_def pathfinish_def)
  qed
  have hlen: "path_length h \<le> path_length \<gamma>"
    by (rule path_length_lipschitz[where B="path_length \<gamma>"])
       (use hlip in \<open>simp add: dist_norm\<close>)
  \<comment> \<open>The image of h lies on the frontier: each parameter either lands in an arc (so eventually
     in F) or maps via \<gamma> to a point already on the frontier.\<close>
  have notarc_notin_s: "\<And>x. (\<nexists>n. x \<in> {a n<..<b n}) \<Longrightarrow> x \<notin> s"
  proof -
    fix x assume noarc: "\<nexists>n. x \<in> {a n<..<b n}"
    show "x \<notin> s"
    proof
      assume "x \<in> s"
      then have "x \<in> \<Union>(components s)" by (simp add: Union_components)
      then obtain c where "c \<in> components s" "x \<in> c" by blast
      then obtain n where "c = {a n<..<b n}" using comps by auto
      then show False using noarc \<open>x \<in> c\<close> by blast
    qed
  qed
  have hx_in_F: "\<And>x. x \<in> {0..1} \<Longrightarrow> h x \<in> F"
  proof -
    fix x :: real assume x01: "x \<in> {0..1}"
    show "h x \<in> F"
    proof (cases "\<exists>n. x \<in> {a n<..<b n}")
      case True
      then obtain n where xn: "x \<in> {a n<..<b n}" by blast
      obtain N where N: "\<And>m. N \<le> m \<Longrightarrow> f m x = h x" using h[OF x01] unfolding eventually_sequentially by blast
      define m where "m = max N (Suc n)"
      have "N \<le> m" "n < m" by (auto simp: m_def)
      have "x \<in> U m" using xn arc_sub_U \<open>n < m\<close> by blast
      then have "f m x \<in> F" using fUF by blast
      then show "h x \<in> F" using N \<open>N \<le> m\<close> by simp
    next
      case False
      obtain n where n: "f n x = h x" using h[OF x01] unfolding eventually_sequentially by blast
      have "x \<notin> U n" using False U_mem by blast
      then have "f n x = \<gamma> x" using foff by blast
      moreover have "x \<notin> s" using False notarc_notin_s by blast
      then have "\<gamma> x \<in> F" using x01 s_def by blast
      ultimately show "h x \<in> F" using n by simp
    qed
  qed
  have hsub_F: "path_image h \<subseteq> F" using hx_in_F by (auto simp: path_image_def)
  \<comment> \<open>Off the arcs, h still agrees with \<gamma>; so \<gamma>'s image outside the deviating set s is part of
     the image of h.\<close>
  have arcs_eq_s: "\<Union> {{a n<..<b n} | n. n \<in> (UNIV::nat set)} = s"
    using comps Union_components by metis
  have hoff_s: "\<And>x. x \<in> {0..1} \<Longrightarrow> x \<notin> s \<Longrightarrow> h x = \<gamma> x"
  proof -
    fix x :: real assume x01: "x \<in> {0..1}" and xs: "x \<notin> s"
    have noarc: "\<nexists>n. x \<in> {a n<..<b n}" using xs arcs_eq_s by blast
    obtain n where n: "f n x = h x" using h[OF x01] unfolding eventually_sequentially by blast
    have "x \<notin> U n" using noarc U_mem by blast
    then have "f n x = \<gamma> x" using foff by blast
    then show "h x = \<gamma> x" using n by simp
  qed
  have gout_sub_h: "\<gamma> ` ({0..1} - s) \<subseteq> path_image h"
  proof
    fix z assume "z \<in> \<gamma> ` ({0..1} - s)"
    then obtain x where x: "x \<in> {0..1}" "x \<notin> s" "z = \<gamma> x" by auto
    then have "z = h x" using hoff_s by simp
    then show "z \<in> path_image h" using x(1) by (auto simp: path_image_def)
  qed
  \<comment> \<open>The convex hulls agree.\<close>
  have hhull: "convex hull (path_image h) = convex hull (path_image \<gamma>)"
  proof (rule subset_antisym)
    \<comment> \<open>\<subseteq>: every point h x = f n x for some n lies in convex hull (f n) = convex hull \<gamma>.\<close>
    have ph_sub: "path_image h \<subseteq> convex hull (path_image \<gamma>)"
    proof
      fix z assume "z \<in> path_image h"
      then obtain x where x: "x \<in> {0..1}" "z = h x" by (auto simp: path_image_def)
      obtain n where n: "f n x = h x" using h[OF x(1)] unfolding eventually_sequentially by blast
      have "h x = f n x" using n by simp
      then have "h x \<in> path_image (f n)" using x(1) by (auto simp: path_image_def)
      then have "h x \<in> convex hull (path_image (f n))" using hull_subset by (meson subsetD)
      then have "h x \<in> convex hull (path_image \<gamma>)" using fhull by simp
      then show "z \<in> convex hull (path_image \<gamma>)" using x(2) by simp
    qed
    show "convex hull (path_image h) \<subseteq> convex hull (path_image \<gamma>)"
      using ph_sub convex_convex_hull by (rule hull_minimal)
  next
    \<comment> \<open>\<supseteq>: the extreme points of the hull are frontier points, hence images of parameters
       outside s, which lie in path_image h. (Krein-Milman + redundancy of interior points.)\<close>
    have cpt_g: "compact (convex hull path_image \<gamma>)"
      by (simp add: compact_convex_hull compact_path_image path\<gamma>)
    have km_g: "convex hull path_image \<gamma> = convex hull {x. x extreme_point_of (convex hull path_image \<gamma>)}"
      using Krein_Milman_Minkowski[OF cpt_g convex_convex_hull] by simp
    have ext_in_out: "\<And>z. z extreme_point_of (convex hull path_image \<gamma>) \<Longrightarrow> z \<in> \<gamma> ` ({0..1} - s)"
    proof -
      fix z assume e: "z extreme_point_of (convex hull path_image \<gamma>)"
      have zpig: "z \<in> path_image \<gamma>" using extreme_point_of_convex_hull[OF e] .
      then obtain x where x: "x \<in> {0..1}" "z = \<gamma> x" by (auto simp: path_image_def)
      have znotint: "z \<notin> interior (convex hull path_image \<gamma>)" using extreme_point_not_in_interior[OF e] .
      have "z \<in> F"
      proof -
        have "z \<in> convex hull path_image \<gamma>" using zpig hull_subset by (meson subsetD)
        then have "z \<in> closure (convex hull path_image \<gamma>)" using closure_subset by (meson subsetD)
        then show "z \<in> F" using znotint F_def by (simp add: frontier_def)
      qed
      then have "x \<notin> s" using x(2) s_def x(1) by auto
      then show "z \<in> \<gamma> ` ({0..1} - s)" using x by auto
    qed
    have "{x. x extreme_point_of (convex hull path_image \<gamma>)} \<subseteq> \<gamma> ` ({0..1} - s)"
      using ext_in_out by blast
    then have "convex hull {x. x extreme_point_of (convex hull path_image \<gamma>)} \<subseteq> convex hull (\<gamma> ` ({0..1} - s))"
      by (rule hull_mono)
    then have "convex hull (path_image \<gamma>) \<subseteq> convex hull (\<gamma> ` ({0..1} - s))" using km_g by simp
    also have "convex hull (\<gamma> ` ({0..1} - s)) \<subseteq> convex hull (path_image h)"
      using gout_sub_h by (rule hull_mono)
    finally show "convex hull (path_image \<gamma>) \<subseteq> convex hull (path_image h)" .
  qed
  \<comment> \<open>The image of h is exactly the frontier: \<subseteq> is hsub_F; \<supseteq> because h is a simple closed
     curve whose image lies on the frontier of its (now equal) convex hull.\<close>
  have hF: "frontier (convex hull (path_image h)) = F" using hhull F_eq by simp
  have h_image_F: "path_image h = F"
  proof
    show "path_image h \<subseteq> F" by (rule hsub_F)
    show "F \<subseteq> path_image h"
    proof -
      have "path_image h \<subseteq> frontier (convex hull (path_image h))" using hsub_F hF by simp
      then have "frontier (convex hull (path_image h)) \<subseteq> path_image h"
        using frontier_convex_hull_subset_path_image[OF hsimple hloop] by simp
      then show "F \<subseteq> path_image h" using hF by simp
    qed
  qed
  show ?thesis
  proof (intro exI[of _ h] conjI)
    show "rectifiable_path h" by (rule hrect)
    show "simple_path h" by (rule hsimple)
    show "pathfinish h = pathstart h" by (rule hloop)
    show "path_length h \<le> path_length \<gamma>" by (rule hlen)
    show "convex hull (path_image h) = convex hull (path_image \<gamma>)" by (rule hhull)
    show "path_image h = frontier (convex hull (path_image \<gamma>))" using h_image_F F_def by simp
  qed
qed

theorem isoperimetric_convexification:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
  obtains h where "rectifiable_path h" and "simple_path h"
    and "pathfinish h = pathstart h"
    and "path_length h \<le> path_length g"
    and "convex hull (path_image h) = convex hull (path_image g)"
    and "path_image h = frontier (convex hull (path_image g))"
proof -
  note [[quick_and_dirty]]
  \<comment> \<open>Strengthened version, assuming the loop starts on the frontier of its convex hull.
     (Proved later; here used to derive the general statement by shifting the basepoint.)\<close>
  have *: "\<And>G::real\<Rightarrow>complex. rectifiable_path G \<Longrightarrow> simple_path G \<Longrightarrow> pathfinish G = pathstart G \<Longrightarrow> pathstart G \<in> frontier (convex hull (path_image G)) \<Longrightarrow> (\<exists>h. rectifiable_path h \<and> simple_path h \<and> pathfinish h = pathstart h \<and> path_length h \<le> path_length G \<and> convex hull (path_image h) = convex hull (path_image G) \<and> path_image h = frontier (convex hull (path_image G)))"
  proof -
    fix G :: "real \<Rightarrow> complex"
    assume Grect: "rectifiable_path G" and Gsimple: "simple_path G"
      and Gloop: "pathfinish G = pathstart G"
      and Gfr: "pathstart G \<in> frontier (convex hull (path_image G))"
    \<comment> \<open>WLOG reparametrize G by arc length, so it becomes (path_length G)-Lipschitz (unit speed).
       All relevant quantities (path_image, path_length, endpoints, frontier) are preserved.\<close>
    obtain g' where g': "rectifiable_path g'" "path_image g' = path_image G"
        "pathstart g' = pathstart G" "pathfinish g' = pathfinish G"
        "path_length g' = path_length G" "arc G \<Longrightarrow> arc g'" "simple_path G \<Longrightarrow> simple_path g'"
        "\<forall>t\<in>{0..1}. path_length (subpath 0 t g') = path_length G * t"
        "\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. dist (g' x) (g' y) \<le> path_length G * dist x y"
      using arc_length_reparametrization[OF Grect] by metis
    have g'simple: "simple_path g'" using g'(7) Gsimple by simp
    have g'rect: "rectifiable_path g'" by (rule g'(1))
    have g'loop: "pathfinish g' = pathstart g'" using g'(3,4) Gloop by simp
    have g'fr: "pathstart g' \<in> frontier (convex hull (path_image g'))"
      using g'(3) g'(2) Gfr by simp
    have g'lip: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g' x) (g' y) \<le> path_length G * dist x y"
      using g'(9) by blast
    have g'lip': "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g' x) (g' y) \<le> path_length g' * dist x y"
      using g'lip g'(5) by simp
    \<comment> \<open>Reduced subgoal, now also assuming the unit-speed (Lipschitz) bound. This is where the
       iterated application of step_lemma will go.\<close>
    have **: "\<And>\<gamma>::real\<Rightarrow>complex. rectifiable_path \<gamma> \<Longrightarrow> simple_path \<gamma> \<Longrightarrow> pathfinish \<gamma> = pathstart \<gamma> \<Longrightarrow> pathstart \<gamma> \<in> frontier (convex hull (path_image \<gamma>)) \<Longrightarrow> (\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (\<gamma> x) (\<gamma> y) \<le> path_length \<gamma> * dist x y) \<Longrightarrow> (\<exists>h. rectifiable_path h \<and> simple_path h \<and> pathfinish h = pathstart h \<and> path_length h \<le> path_length \<gamma> \<and> convex hull (path_image h) = convex hull (path_image \<gamma>) \<and> path_image h = frontier (convex hull (path_image \<gamma>)))"
      using convexification_unit_speed by blast
    have inst: "\<exists>h. rectifiable_path h \<and> simple_path h \<and> pathfinish h = pathstart h \<and> path_length h \<le> path_length g' \<and> convex hull (path_image h) = convex hull (path_image g') \<and> path_image h = frontier (convex hull (path_image g'))"
      using **[OF g'rect g'simple g'loop g'fr g'lip'] .
    show "\<exists>h. rectifiable_path h \<and> simple_path h \<and> pathfinish h = pathstart h \<and> path_length h \<le> path_length G \<and> convex hull (path_image h) = convex hull (path_image G) \<and> path_image h = frontier (convex hull (path_image G))"
      using inst g'(5) g'(2) by simp
  qed
  \<comment> \<open>Some point of the loop lies on the frontier (an extreme point of the convex hull).\<close>
  have pathg: "path g" using assms(2) by (rule simple_path_imp_path)
  have cpt: "compact (convex hull path_image g)"
    by (simp add: compact_convex_hull compact_path_image pathg)
  have ne: "convex hull path_image g \<noteq> {}"
    by (simp add: path_image_nonempty)
  obtain x where x_ext: "x extreme_point_of (convex hull path_image g)"
    using extreme_point_exists_convex[OF cpt convex_convex_hull ne] by blast
  have x_pig: "x \<in> path_image g" using extreme_point_of_convex_hull[OF x_ext] .
  have x_in: "x \<in> convex hull path_image g" using hull_subset x_pig by (meson subsetD)
  have x_notint: "x \<notin> interior (convex hull path_image g)" using extreme_point_not_in_interior[OF x_ext] .
  have x_clo: "x \<in> closure (convex hull path_image g)" using x_in closure_subset by (meson subsetD)
  have x_fr: "x \<in> frontier (convex hull path_image g)"
    using x_clo x_notint by (simp add: frontier_def)
  obtain t where t: "t \<in> {0..1}" "g t = x" using x_pig by (auto simp: path_image_def)
  \<comment> \<open>Shift g so that it starts at the frontier point g t; properties are preserved.\<close>
  have sp_rect: "rectifiable_path (shiftpath t g)" using assms(1,3) t(1) by (rule rectifiable_path_shiftpath)
  have sp_simple: "simple_path (shiftpath t g)" using assms(2,3) t(1) by (simp add: simple_path_shiftpath)
  have sp_loop: "pathfinish (shiftpath t g) = pathstart (shiftpath t g)" using assms(3) t(1) by (rule closed_shiftpath)
  have sp_pi: "path_image (shiftpath t g) = path_image g" using t(1) assms(3) by (rule path_image_shiftpath)
  have sp_start: "pathstart (shiftpath t g) = g t" using t(1) by (simp add: pathstart_shiftpath)
  have sp_len: "path_length (shiftpath t g) = path_length g" using assms(1,3) t(1) by (rule path_length_shiftpath)
  have sp_startfr: "pathstart (shiftpath t g) \<in> frontier (convex hull (path_image (shiftpath t g)))"
    using sp_start sp_pi x_fr t(2) by simp
  have inst: "\<exists>h. rectifiable_path h \<and> simple_path h \<and> pathfinish h = pathstart h \<and> path_length h \<le> path_length (shiftpath t g) \<and> convex hull (path_image h) = convex hull (path_image (shiftpath t g)) \<and> path_image h = frontier (convex hull (path_image (shiftpath t g)))"
    using *[OF sp_rect sp_simple sp_loop sp_startfr] .
  from inst obtain h where h: "rectifiable_path h" "simple_path h" "pathfinish h = pathstart h"
      "path_length h \<le> path_length (shiftpath t g)"
      "convex hull (path_image h) = convex hull (path_image (shiftpath t g))"
      "path_image h = frontier (convex hull (path_image (shiftpath t g)))" by blast
  show ?thesis
    using inst sp_len sp_pi that by force
qed

theorem isoperimetric_convexification_strict:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "\<not> convex (inside (path_image g))"
  obtains h where "rectifiable_path h" and "simple_path h"
    and "pathfinish h = pathstart h"
    and "path_length h \<le> path_length g"
    and "convex hull (path_image h) = convex hull (path_image g)"
    and "path_image h = frontier (convex hull (path_image g))"
    and "measure lebesgue (inside (path_image g)) < measure lebesgue (inside (path_image h))"
proof -
  show ?thesis
    sorry
qed

section \<open>Part 5: The isoperimetric theorem\<close>

theorem isoperimetric_theorem:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "path_length g = L"
  shows "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
      \<exists>a r. path_image g = sphere a r"
proof -
  show ineq: "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
  proof (cases "convex (inside (path_image g))")
    case True
    show ?thesis
      using isoperimetric_theorem_convex(1)[OF assms(1-3) True assms(4)] .
  next
    case False
    obtain h where h: "rectifiable_path h" "simple_path h"
      "pathfinish h = pathstart h"
      "path_length h \<le> path_length g"
      "convex hull (path_image h) = convex hull (path_image g)"
      "path_image h = frontier (convex hull (path_image g))"
      "measure lebesgue (inside (path_image g)) < measure lebesgue (inside (path_image h))"
      by (rule isoperimetric_convexification_strict[OF assms(1-3) False])
    have bounded_hull: "bounded (convex hull (path_image g))"
      by (intro bounded_convex_hull compact_imp_bounded compact_simple_path_image assms(2))
    have eq_int: "inside (path_image h) = interior (convex hull (path_image g))"
      using inside_frontier_eq_interior[OF bounded_hull convex_convex_hull] h(6) by simp
    have convex_h: "convex (inside (path_image h))"
      using eq_int convex_interior[OF convex_convex_hull] by simp
    have ineq_h: "measure lebesgue (inside (path_image h)) \<le> (path_length h)\<^sup>2 / (4 * pi)"
      using isoperimetric_theorem_convex(1)[OF h(1-3) convex_h refl] .
    have mono: "(path_length h)\<^sup>2 / (4 * pi) \<le> L\<^sup>2 / (4 * pi)"
      by (intro divide_right_mono power_mono)
        (use h(4) assms(4) path_length_pos_le[OF h(1)] pi_gt_zero in simp_all)
    show ?thesis using h(7) ineq_h mono by linarith
  qed
  show "\<exists>a r. path_image g = sphere a r"
    if eq: "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi)"
  proof (cases "convex (inside (path_image g))")
    case True
    show ?thesis
      using isoperimetric_theorem_convex(2)[OF assms(1-3) True assms(4)] eq .
  next
    case False
    obtain h where h: "rectifiable_path h" "simple_path h"
      "pathfinish h = pathstart h"
      "path_length h \<le> path_length g"
      "convex hull (path_image h) = convex hull (path_image g)"
      "path_image h = frontier (convex hull (path_image g))"
      "measure lebesgue (inside (path_image g)) < measure lebesgue (inside (path_image h))"
      by (rule isoperimetric_convexification_strict[OF assms(1-3) False])
    have bounded_hull: "bounded (convex hull (path_image g))"
      by (intro bounded_convex_hull compact_imp_bounded compact_simple_path_image assms(2))
    have eq_int: "inside (path_image h) = interior (convex hull (path_image g))"
      using inside_frontier_eq_interior[OF bounded_hull convex_convex_hull] h(6) by simp
    have convex_h: "convex (inside (path_image h))"
      using eq_int convex_interior[OF convex_convex_hull] by simp
    have ineq_h: "measure lebesgue (inside (path_image h)) \<le> (path_length h)\<^sup>2 / (4 * pi)"
      using isoperimetric_theorem_convex(1)[OF h(1-3) convex_h refl] .
    have mono: "(path_length h)\<^sup>2 / (4 * pi) \<le> L\<^sup>2 / (4 * pi)"
      by (intro divide_right_mono power_mono)
        (use h(4) assms(4) path_length_pos_le[OF h(1)] pi_gt_zero in simp_all)
    have "measure lebesgue (inside (path_image g)) < L\<^sup>2 / (4 * pi)"
      using h(7) ineq_h mono by linarith
    with eq show ?thesis by simp
  qed
qed

end

