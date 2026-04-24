theory Isoperimetric
  imports Arc_Length_Reparametrization "Fourier.Fourier" "Green.Green" "../Euclidean_Space_Transfer"
    "HOL-ex.Sketch_and_Explore" Isar_Explore
begin

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

  \<comment> \<open>Left inverse of \<sigma> on T\<close>
  define n where "n \<equiv> the_inv_into T \<sigma>"

  \<comment> \<open>For each x, obtain d(x) > 0 with the continuity bound\<close>
  have "\<exists>d. d > 0 \<and>
    (x \<in> {a..b} \<and> x \<in> \<sigma> ` T \<longrightarrow>
      (\<forall>y. \<bar>y - x\<bar> < d \<and> y \<in> {a..b} \<longrightarrow>
        norm (f y - f x) \<le> \<epsilon> / 2 ^ (4 + n x)))" for x
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
      have eps_pos: "\<epsilon> / 2 ^ (4 + n x) > 0"
        using \<open>0 < \<epsilon>\<close> by simp
      from cont[unfolded continuous_on_iff] x_ab eps_pos
      obtain \<delta> where "\<delta> > 0"
        and \<delta>: "\<And>y. y \<in> {a..b} \<Longrightarrow> dist y x < \<delta> \<Longrightarrow> dist (f y) (f x) < \<epsilon> / 2 ^ (4 + n x)"
        by blast
      show ?thesis
      proof (intro exI conjI impI allI)
        show "\<delta> > 0" by fact
      next
        fix y assume "\<bar>y - x\<bar> < \<delta> \<and> y \<in> {a..b}"
        then have "y \<in> {a..b}" "dist y x < \<delta>" by (auto simp: dist_real_def)
        then have "dist (f y) (f x) < \<epsilon> / 2 ^ (4 + n x)"
          using \<delta> by auto
        then show "norm (f y - f x) \<le> \<epsilon> / 2 ^ (4 + n x)"
          by (simp add: dist_norm less_imp_le)
      qed
    qed
  qed
  then have d_exists: "\<forall>x. \<exists>d>0. (x \<in> {a..b} \<and> x \<in> \<sigma> ` T \<longrightarrow>
      (\<forall>y. \<bar>y - x\<bar> < d \<and> y \<in> {a..b} \<longrightarrow>
        norm (f y - f x) \<le> \<epsilon> / 2 ^ (4 + n x)))"
    by blast
  have d_choice: "\<exists>dd. \<forall>x. dd x > 0 \<and> (x \<in> {a..b} \<and> x \<in> \<sigma> ` T \<longrightarrow>
      (\<forall>y. \<bar>y - x\<bar> < dd x \<and> y \<in> {a..b} \<longrightarrow> norm (f y - f x) \<le> \<epsilon> / 2 ^ (4 + n x)))"
  proof -
    have "\<forall>x. \<exists>d. d > 0 \<and> (x \<in> {a..b} \<and> x \<in> \<sigma> ` T \<longrightarrow>
        (\<forall>y. \<bar>y - x\<bar> < d \<and> y \<in> {a..b} \<longrightarrow> norm (f y - f x) \<le> \<epsilon> / 2 ^ (4 + n x)))"
      using d_exists by (simp add: Bex_def)
    then show ?thesis
      by (rule choice)
  qed
  obtain d :: "real \<Rightarrow> real" where d_pos: "\<And>x. d x > 0"
    and d_bound: "\<And>x. x \<in> {a..b} \<Longrightarrow> x \<in> \<sigma> ` T \<Longrightarrow>
      (\<forall>y. \<bar>y - x\<bar> < d x \<and> y \<in> {a..b} \<longrightarrow> norm (f y - f x) \<le> \<epsilon> / 2 ^ (4 + n x))"
    using d_choice by auto

  show "\<exists>g. gauge g \<and> (\<forall>p. p tagged_partial_division_of cbox a b \<and> g fine p \<and> fst ` p \<subseteq> S \<longrightarrow> norm (\<Sum>(x, k)\<in>p. f (\<Squnion> k) - f (\<Sqinter> k)) < \<epsilon>)"
  proof (intro exI conjI allI impI)
    show "gauge (\<lambda>x. ball x (d x))"
      using d_pos by (intro gauge_ball_dependent) auto
  next
    fix p assume p_hyp: "p tagged_partial_division_of cbox a b \<and>
      (\<lambda>x. ball x (d x)) fine p \<and> fst ` p \<subseteq> S"
    then have p_div: "p tagged_partial_division_of cbox a b"
      and p_fine: "(\<lambda>x. ball x (d x)) fine p"
      and p_tags: "fst ` p \<subseteq> S"
      by auto
    have p_finite: "finite p"
      using tagged_partial_division_ofD(1)[OF p_div] .

    have finite_sub: "finite {(x,k). (x,k) \<in> p \<and> P x k}" for P
      by (rule finite_subset[OF _ p_finite]) auto
    have finite_snd: "finite {k. (x,k) \<in> p \<and> P x k}" for P x
    proof -
      have "{k. (x,k) \<in> p \<and> P x k} \<subseteq> snd ` p"
        by (force intro: image_eqI)
      then show ?thesis
        using finite_subset finite_imageI[OF p_finite] by blast
    qed

    show "norm (\<Sum>(x, k)\<in>p. f (\<Squnion> k) - f (\<Sqinter> k)) < \<epsilon>"
    proof -
      let ?S' = "{(x,k). (x,k) \<in> p \<and> x \<in> \<sigma> ` T \<and> Henstock_Kurzweil_Integration.content k \<noteq> 0}"
      let ?t = "norm (\<Sum>(x,k)\<in>?S'. - (f (\<Squnion> k) - f (\<Sqinter> k)))"
      \<comment> \<open>Show that zero-content terms vanish, so the sum over @{term p} equals the sum over @{term "?S'"}\<close>
      have zero_content: "f (\<Squnion> k) - f (\<Sqinter> k) = 0"
        if "(x, k) \<in> p" "Henstock_Kurzweil_Integration.content k = 0" for x k
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
          and extra: "x \<notin> \<sigma> ` T \<or> Henstock_Kurzweil_Integration.content k = 0"
          by (cases b) auto
        have "x \<in> \<sigma> ` T"
          using p_tags bxk Seq by (force simp: image_iff)
        with extra have "Henstock_Kurzweil_Integration.content k = 0" by blast
        then show "(case b of (x, k) \<Rightarrow> f (\<Squnion> k) - f (\<Sqinter> k)) = 0"
          using zero_content[OF bxk(2)] bxk(1) by simp
      qed
      have neg_eq: "- (\<Sum>(x,k)\<in>p. f (\<Squnion> k) - f (\<Sqinter> k)) =
                    (\<Sum>(x,k)\<in>?S'. - (f (\<Squnion> k) - f (\<Sqinter> k)))"
        unfolding sum_eq sum_negf[symmetric] by (simp add: case_prod_unfold)
      have "norm (\<Sum>(x,k)\<in>p. f (\<Squnion> k) - f (\<Sqinter> k)) = ?t"
        by (subst neg_eq[symmetric], subst norm_minus_cancel[symmetric]) (rule refl)
      also have "\<dots> \<le> (\<Sum>(x,k)\<in>?S'. \<epsilon> / 2 ^ (3 + n x))"
      proof (rule sum_norm_le)
        fix z assume z_in: "z \<in> ?S'"
        obtain x k where z_eq: "z = (x, k)" and xk_in: "(x, k) \<in> p"
          and x_img: "x \<in> \<sigma> ` T" and k_nz: "Henstock_Kurzweil_Integration.content k \<noteq> 0"
          using z_in by (cases z) auto
        from tagged_partial_division_ofD(4)[OF p_div xk_in]
        obtain u v where k_eq: "k = cbox u v" by auto
        from tagged_partial_division_ofD(2)[OF p_div xk_in]
        have x_in_k: "x \<in> k" .
        then have uv: "u \<le> v" using k_eq by (auto simp: mem_box)
        from k_nz have "u < v"
          using k_eq uv by (auto simp: content_cbox_if Basis_real_def)
        have sup_k: "\<Squnion> k = v" and inf_k: "\<Sqinter> k = u"
          using k_eq uv by (simp_all add: Sup_atLeastAtMost Inf_atLeastAtMost)
        \<comment> \<open>x is in {a..b} and in \<sigma> ` T\<close>
        have k_sub: "k \<subseteq> cbox a b"
          using tagged_partial_division_ofD(3)[OF p_div xk_in] .
        have x_ab: "x \<in> {a..b}" using x_in_k k_sub by auto
        \<comment> \<open>u and v are in {a..b}\<close>
        have u_ab: "u \<in> {a..b}" and v_ab: "v \<in> {a..b}"
          using k_sub k_eq \<open>u \<le> v\<close> by auto
        \<comment> \<open>From fineness: k \<subseteq> ball x (d x), so u and v are within d x of x\<close>
        have k_ball: "k \<subseteq> ball x (d x)"
          using fineD[OF p_fine xk_in] .
        have "u \<in> ball x (d x)" and "v \<in> ball x (d x)"
          using k_ball k_eq \<open>u \<le> v\<close> by auto
        then have du: "\<bar>u - x\<bar> < d x" and dv: "\<bar>v - x\<bar> < d x"
          by (auto simp: mem_ball dist_real_def)
        \<comment> \<open>Apply the continuity bound d_bound\<close>
        have bnd_v: "norm (f v - f x) \<le> \<epsilon> / 2 ^ (4 + n x)"
          using d_bound[OF x_ab x_img, rule_format, of v] dv v_ab by auto
        have bnd_u: "norm (f u - f x) \<le> \<epsilon> / 2 ^ (4 + n x)"
          using d_bound[OF x_ab x_img, rule_format, of u] du u_ab by auto
        \<comment> \<open>Triangle inequality and arithmetic\<close>
        have bnd_xu: "norm (f x - f u) \<le> \<epsilon> / 2 ^ (4 + n x)"
          using bnd_u by (subst norm_minus_commute) 
        have bound: "norm (-(f (\<Squnion> k) - f (\<Sqinter> k))) \<le> \<epsilon> / 2 ^ (3 + n x)"
        proof -
          have "norm (-(f (\<Squnion> k) - f (\<Sqinter> k))) = norm (f (\<Squnion> k) - f (\<Sqinter> k))"
            by (rule norm_minus_cancel)
          also have "\<dots> = norm (f v - f u)"
            by (simp add: sup_k inf_k)
          also have "\<dots> = norm ((f v - f x) + (f x - f u))" by simp
          also have "\<dots> \<le> norm (f v - f x) + norm (f x - f u)"
            by (rule norm_triangle_ineq)
          also have "\<dots> \<le> \<epsilon> / 2 ^ (4 + n x) + \<epsilon> / 2 ^ (4 + n x)"
            by (intro add_mono bnd_v bnd_xu)
          also have "\<dots> = \<epsilon> / 2 ^ (3 + n x)"
          proof -
            have "(2::real) ^ (4 + n x) = 2 * 2 ^ (3 + n x)" by (simp add: power_add)
            then show ?thesis by (simp add: field_simps)
          qed
          finally show ?thesis .
        qed
        show "norm (case z of (x, k) \<Rightarrow> - (f (\<Squnion> k) - f (\<Sqinter> k))) \<le>
                      (case z of (x, k) \<Rightarrow> \<epsilon> / 2 ^ (3 + n x))"
          using bound z_eq by simp
      qed
      also have "\<dots> < \<epsilon>"
        sorry
      finally show ?thesis .
    qed
  qed
qed

lemma fundamental_theorem_of_calculus_interior_strong:
  fixes f :: "real \<Rightarrow> 'a::banach" and f' :: "real \<Rightarrow> 'a"
  assumes "countable S"
    and "a \<le> b"
    and "continuous_on {a..b} f"
    and "\<And>x. x \<in> {a<..<b} - S \<Longrightarrow>
      (f has_vector_derivative f' x) (at x)"
  shows "(f' has_integral (f b - f a)) {a..b}"
proof -
  have "(f' has_integral (f b - f a)) {a..b}"
  proof (rule fundamental_theorem_of_calculus_strong[where S = "insert a (insert b S)"])
    show "countable (insert a (insert b S))"
      using assms(1) by auto
    show "a \<le> b" by fact
    show "continuous_on {a..b} f" by fact
    fix x assume "x \<in> {a..b} - insert a (insert b S)"
    then have x: "x \<in> {a<..<b} - S"
      by auto
    then have "(f has_vector_derivative f' x) (at x)"
      using assms(4) by auto
    then show "(f has_vector_derivative f' x) (at x within {a..b})"
      using has_vector_derivative_at_within by blast
  qed
  then show ?thesis .
qed

lemma integral_has_vector_derivative_pointwise:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a..b}"
    and "x \<in> {a..b}"
    and "continuous (at x within {a..b}) f"
  shows "((\<lambda>u. integral {a..u} f) has_vector_derivative f x) (at x within {a..b})"
  sorry

lemma has_integral_substitution_strong:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and g g' :: "real \<Rightarrow> real"
  assumes "countable k"
    and "f integrable_on {c..d}"
    and "continuous_on {a..b} g"
    and "g ` {a..b} \<subseteq> {c..d}"
    and "\<And>x. x \<in> {a..b} - k \<Longrightarrow>
      (g has_vector_derivative g' x) (at x within {a..b}) \<and>
      continuous (at (g x) within {c..d}) f"
    and "a \<le> b" and "c \<le> d" and "g a \<le> g b"
  shows "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral integral {g a..g b} f) {a..b}"
proof -
  \<comment> \<open>Define the indefinite integral ff\<close>
  define ff where "ff \<equiv> \<lambda>x. integral {c..x} f"
  \<comment> \<open>ff is continuous on {c..d}\<close>
  have ff_cont: "continuous_on {c..d} ff"
    unfolding ff_def using indefinite_integral_continuous_1[OF assms(2)] .
  \<comment> \<open>ff \<circ> g is continuous on {a..b}\<close>
  have fg_cont: "continuous_on {a..b} (ff \<circ> g)"
    using continuous_on_compose2[OF ff_cont assms(3) assms(4)] unfolding comp_def .
  \<comment> \<open>g maps {a..b} into {c..d}\<close>
  have g_in: "g x \<in> {c..d}" if "x \<in> {a..b}" for x
    using assms(4) that by blast
  \<comment> \<open>Apply FTC interior strong to ff \<circ> g\<close>
  have ftc: "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral ((ff \<circ> g) b - (ff \<circ> g) a)) {a..b}"
  proof (rule fundamental_theorem_of_calculus_interior_strong[where S = k])
    show "countable k" by fact
    show "a \<le> b" by fact
    show "continuous_on {a..b} (ff \<circ> g)" by fact
    fix x assume xk: "x \<in> {a<..<b} - k"
    then have x_ab: "x \<in> {a..b}" and x_nk: "x \<notin> k" by auto
    have x_ab_k: "x \<in> {a..b} - k" using x_ab x_nk by auto
    have gx_cd: "g x \<in> {c..d}" using g_in[OF x_ab] .
    \<comment> \<open>Get derivative of g and continuity of f at g(x)\<close>
    have g_deriv: "(g has_vector_derivative g' x) (at x within {a..b})"
      and f_cont: "continuous (at (g x) within {c..d}) f"
      using assms(5)[OF x_ab_k] by auto
    \<comment> \<open>Get derivative of ff at g(x) within {c..d}\<close>
    have ff_deriv: "(ff has_vector_derivative f (g x)) (at (g x) within {c..d})"
      unfolding ff_def
      using integral_has_vector_derivative_pointwise[OF assms(2) gx_cd f_cont] .
    \<comment> \<open>Weaken to derivative within g ` {a..b}\<close>
    have ff_deriv': "(ff has_vector_derivative f (g x)) (at (g x) within g ` {a..b})"
      using has_vector_derivative_within_subset[OF ff_deriv assms(4)] .
    \<comment> \<open>Apply chain rule\<close>
    have chain: "((ff \<circ> g) has_vector_derivative g' x *\<^sub>R f (g x)) (at x within {a..b})"
      using vector_diff_chain_within[OF g_deriv ff_deriv'] .
    \<comment> \<open>x is in the interior, so at x within {a..b} = at x\<close>
    have "x \<in> interior {a..b}"
      using xk by (simp add: interior_atLeastAtMost_real)
    then have "at x within {a..b} = at x"
      by (rule at_within_interior)
    with chain show "((ff \<circ> g) has_vector_derivative g' x *\<^sub>R f (g x)) (at x)"
      by simp
  qed
  \<comment> \<open>Now show (ff \<circ> g) b - (ff \<circ> g) a = integral {g a..g b} f\<close>
  have "(ff \<circ> g) b - (ff \<circ> g) a = integral {g a..g b} f"
  proof -
    have ga_cd: "g a \<in> {c..d}" using g_in[OF _] assms(6) by auto
    have gb_cd: "g b \<in> {c..d}" using g_in[OF _] assms(6) by auto
    have c_ga: "c \<le> g a" and ga_d: "g a \<le> d"
      using ga_cd by auto
    have c_gb: "c \<le> g b" and gb_d: "g b \<le> d"
      using gb_cd by auto
    have "f integrable_on {c..g b}"
      using integrable_on_subinterval[OF assms(2), of c "g b"] c_gb gb_d by auto
    then have combine: "integral {c..g a} f + integral {g a..g b} f = integral {c..g b} f"
      using Henstock_Kurzweil_Integration.integral_combine[OF c_ga assms(8)] by auto
    have "(ff \<circ> g) b - (ff \<circ> g) a = ff (g b) - ff (g a)"
      by (simp add: comp_def)
    also have "\<dots> = integral {c..g b} f - integral {c..g a} f"
      by (simp add: ff_def)
    also have "\<dots> = integral {g a..g b} f"
      using combine by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  with ftc show ?thesis by simp
qed

text \<open>Composition of Lipschitz with absolutely continuous is absolutely continuous.\<close>
lemma absolutely_continuous_on_Lipschitz_compose:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space" and \<phi> :: "real \<Rightarrow> real"
  assumes ac: "absolutely_continuous_on {a..b} \<phi>"
    and lip: "\<And>x y. x \<in> \<phi> ` {a..b} \<Longrightarrow> y \<in> \<phi> ` {a..b} \<Longrightarrow> norm (g x - g y) \<le> L * \<bar>x - y\<bar>"
    and "0 \<le> L"
  shows "absolutely_continuous_on {a..b} (g \<circ> \<phi>)"
  sorry

text \<open>1D substitution for absolutely continuous monotone functions.\<close>
lemma has_integral_substitution_ac:
  fixes \<phi> :: "real \<Rightarrow> real" and \<phi>' :: "real \<Rightarrow> real" and f :: "real \<Rightarrow> real"
  assumes "a \<le> b" "\<phi> a \<le> \<phi> b"
    and "absolutely_continuous_on {a..b} \<phi>"
    and "negligible S"
    and "\<And>t. t \<in> {a..b} - S \<Longrightarrow> (\<phi> has_vector_derivative \<phi>' t) (at t)"
    and "continuous_on {\<phi> a..\<phi> b} f"
    and mono: "\<And>x y. x \<in> {a..b} \<Longrightarrow> y \<in> {a..b} \<Longrightarrow> x \<le> y \<Longrightarrow> \<phi> x \<le> \<phi> y"
  shows "((\<lambda>t. \<phi>' t * f (\<phi> t)) has_integral (integral {\<phi> a..\<phi> b} f)) {a..b}"
  sorry

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
    have "continuous_on UNIV (\<lambda>p :: real \<times> real. Complex (fst p) (snd p))"
      by (intro continuous_on_Complex continuous_on_fst continuous_on_snd continuous_on_id)
    then have "continuous_on UNIV ?C"
      by (simp add: case_prod_unfold)
    then have "?C \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI)
    then show ?thesis by (simp add: measurable_lborel1)
  qed
  have "emeasure (distr lborel borel ?C) (box l u) = emeasure lborel (?C -` box l u)"
    using emeasure_distr[OF meas_C] by simp
  also have "?C -` box l u = box (Re l, Im l) (Re u, Im u)"
    by (auto simp: mem_box Basis_complex_def Basis_prod_def inner_complex_def
          inner_Pair_0 complex.sel split: prod.splits)
  also have "emeasure lborel (box (Re l, Im l) (Re u, Im u)) =
             ennreal (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
  proof -
    have "emeasure lborel (box (Re l, Im l) (Re u, Im u)) =
          ennreal (\<Prod>b\<in>(Basis :: (real \<times> real) set). ((Re u, Im u) - (Re l, Im l)) \<bullet> b)"
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



section \<open>Lebesgue measurability of ordinate sets\<close>

lemma le_iff_forall_rat_less_imp:
  fixes x y :: real
  shows "x \<le> y \<longleftrightarrow> (\<forall>q \<in> \<rat>. y < q \<longrightarrow> x < q)"
proof (intro iffI)
  assume "x \<le> y"
  then show "\<forall>q\<in>\<rat>. y < q \<longrightarrow> x < q"
    by (meson order_le_less_trans)
next
  assume *: "\<forall>q\<in>\<rat>. y < q \<longrightarrow> x < q"
  show "x \<le> y"
  proof (rule ccontr)
    assume "\<not> x \<le> y"
    then have "y < x" by simp
    then obtain q where "q \<in> \<rat>" "y < q" "q < x"
      using Rats_dense_in_real by blast
    with * show False by auto
  qed
qed

text \<open>Helper: if A is Lebesgue measurable in \<real>, then A \<times> UNIV is Lebesgue measurable in \<real>².\<close>

lemma lebesgue_measurable_Times_UNIV:
  fixes A :: "real set"
  assumes "A \<in> sets lebesgue"
  shows "A \<times> (UNIV :: real set) \<in> sets lebesgue"
proof -
  have A_eq: "A = main_part lborel A \<union> null_part lborel A"
    using main_part_null_part_Un[OF assms] by simp
  have mp: "main_part lborel A \<in> sets lborel"
    using main_part_sets[OF assms] .
  obtain N :: "real set" where N: "N \<in> null_sets lborel" "null_part lborel A \<subseteq> N"
    using null_part[OF assms] by auto
  have mp_borel: "main_part lborel A \<in> sets (borel :: real measure)"
    using mp by (simp add: sets_lborel)
  have UNIV_borel: "(UNIV :: real set) \<in> sets (borel :: real measure)"
    using sets.top[of "borel :: real measure"] by (simp add: space_borel)
  have "main_part lborel A \<times> (UNIV :: real set) \<in> sets (borel :: (real \<times> real) measure)"
    using borel_Times[OF mp_borel UNIV_borel] .
  then have mp_leb: "main_part lborel A \<times> (UNIV :: real set)
      \<in> sets (lebesgue :: (real \<times> real) measure)"
    using sets_completionI_sets by (simp add: sets_lborel)
  have UNIV_lborel: "(UNIV :: real set) \<in> sets (lborel :: real measure)"
    using sets.top[of "lborel :: real measure"] by (simp add: space_lborel space_borel)
  have "N \<times> (UNIV :: real set) \<in> null_sets (lborel \<Otimes>\<^sub>M (lborel :: real measure))"
    using lborel.times_in_null_sets1[OF N(1) UNIV_lborel] .
  then have N_null: "N \<times> (UNIV :: real set) \<in> null_sets (lborel :: (real \<times> real) measure)"
    by (simp add: lborel_prod)
  have "null_part lborel A \<times> (UNIV :: real set) \<subseteq> N \<times> (UNIV :: real set)"
    using N(2) by auto
  moreover have "N \<times> (UNIV :: real set) \<in> null_sets (lebesgue :: (real \<times> real) measure)"
    using N_null null_sets_completionI by blast
  ultimately have np_leb: "null_part lborel A \<times> (UNIV :: real set)
      \<in> sets (lebesgue :: (real \<times> real) measure)"
    using completion.complete by blast
  have "A \<times> (UNIV :: real set) = (main_part lborel A \<times> UNIV) \<union> (null_part lborel A \<times> UNIV)"
    using A_eq by auto
  then show ?thesis using mp_leb np_leb sets.Un by metis
qed

lemma prod_swap_lebesgue_measurable:
  "prod.swap \<in> (lebesgue :: ('a::euclidean_space \<times> 'b::euclidean_space) measure)
    \<rightarrow>\<^sub>M (lebesgue :: ('b \<times> 'a) measure)"
proof -
  \<comment> \<open>Step 1: prod.swap is Borel-measurable\<close>
  have swap_lborel: "prod.swap \<in> (lborel :: ('a \<times> 'b) measure)
    \<rightarrow>\<^sub>M (lborel :: ('b \<times> 'a) measure)"
    by (simp add: borel_measurable_continuous_onI continuous_on_swap)
  \<comment> \<open>Step 2: lift source to completion\<close>
  have swap_compl: "prod.swap \<in> (lebesgue :: ('a \<times> 'b) measure)
    \<rightarrow>\<^sub>M (lborel :: ('b \<times> 'a) measure)"
    using measurable_completion[OF swap_lborel] by simp
  \<comment> \<open>Step 3: null sets are preserved\<close>
  have "distr (lebesgue :: ('a \<times> 'b) measure) lborel prod.swap
    = distr lborel lborel prod.swap"
    using distr_completion[OF swap_lborel] by simp
  also have "... = (lborel :: ('b \<times> 'a) measure)"
  proof -
    have "distr lborel lborel prod.swap
      = distr lborel lborel (\<lambda>(x::'a, y::'b). (y, x))"
      by (intro distr_cong) (auto simp: swap_simp)
    also have "... = (lborel :: ('b \<times> 'a) measure)"
      using lborel_pair.distr_pair_swap by (simp add: lborel_prod eq_commute)
    finally show ?thesis .
  qed
  finally have null_eq: "null_sets (lborel :: ('b \<times> 'a) measure)
    \<subseteq> null_sets (distr (lebesgue :: ('a \<times> 'b) measure) lborel prod.swap)"
    by simp
  \<comment> \<open>Step 4: lift target to completion\<close>
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
  proof (rule linearI)
    fix x y :: "real \<times> real" and c :: real
    show "?C (x + y) = ?C x + ?C y"
      by (cases x; cases y) (simp add: complex_eq_iff)
    show "?C (c *\<^sub>R x) = c *\<^sub>R ?C x"
      by (cases x) (simp add: complex_eq_iff)
  qed
  \<comment> \<open>?C maps cboxes to cboxes with the same measure\<close>
  have box_eq: "measure lebesgue (?C ` cbox a b) = 1 * measure lebesgue (cbox a b)"
    for a b :: "real \<times> real"
  proof -
    obtain a1 a2 where a: "a = (a1, a2)" by (cases a)
    obtain b1 b2 where b: "b = (b1, b2)" by (cases b)
    have "?C ` cbox (a1,a2) (b1,b2) = cbox (Complex a1 a2) (Complex b1 b2)"
    proof (intro set_eqI iffI)
      fix z :: complex
      assume "z \<in> ?C ` cbox (a1,a2) (b1,b2)"
      then show "z \<in> cbox (Complex a1 a2) (Complex b1 b2)"
        by (auto simp: cbox_complex_eq complex.sel mem_box Basis_prod_def)
    next
      fix z :: complex
      assume "z \<in> cbox (Complex a1 a2) (Complex b1 b2)"
      then show "z \<in> ?C ` cbox (a1,a2) (b1,b2)"
        by (simp add: cbox_Complex_eq cbox_Pair_eq split_def)
    qed
    moreover have "measure lebesgue (cbox (Complex a1 a2) (Complex b1 b2)) =
          measure lebesgue (cbox (a1,a2) (b1,b2))"
      by (simp add: measure_lborel_cbox_eq Basis_complex_def Basis_prod_def
            complex.sel inner_complex_def inner_Pair_0)
    ultimately show ?thesis unfolding a b by simp
  qed
  \<comment> \<open>?inv is measurable from complex lborel to (real \<times> real) lborel\<close>
  have inv_lborel: "?inv \<in> (lborel :: complex measure) \<rightarrow>\<^sub>M (lborel :: (real \<times> real) measure)"
  proof -
    have "?inv \<in> (borel :: complex measure) \<rightarrow>\<^sub>M (borel :: (real \<times> real) measure)"
      by (intro borel_measurable_Pair borel_measurable_Re borel_measurable_Im)
    then show ?thesis by (simp add: measurable_def sets_lborel)
  qed
  \<comment> \<open>Lift source to completion\<close>
  have inv_compl: "?inv \<in> (lebesgue :: complex measure) \<rightarrow>\<^sub>M (lborel :: (real \<times> real) measure)"
    using measurable_completion[OF inv_lborel] by simp
  \<comment> \<open>Compute distr lebesgue lborel ?inv = lborel\<close>
  have "distr (lebesgue :: complex measure) lborel ?inv
      = distr (lborel :: complex measure) lborel ?inv"
    using distr_completion[OF inv_lborel] by simp
  also have "\<dots> = (lborel :: (real \<times> real) measure)"
  proof -
    \<comment> \<open>Use distr_distr with ?C and ?inv: ?inv \<circ> ?C = id\<close>
    have C_meas: "?C \<in> (lborel :: (real \<times> real) measure) \<rightarrow>\<^sub>M (borel :: complex measure)"
    proof -
      have "continuous_on UNIV (\<lambda>p :: real \<times> real. Complex (fst p) (snd p))"
        by (intro continuous_on_Complex continuous_on_fst continuous_on_snd continuous_on_id)
      then have "continuous_on UNIV ?C"
        by (simp add: case_prod_unfold)
      then have "?C \<in> borel_measurable borel"
        by (rule borel_measurable_continuous_onI)
      then show ?thesis by (simp add: measurable_lborel1)
    qed
    have inv_borel: "?inv \<in> (borel :: complex measure) \<rightarrow>\<^sub>M (lborel :: (real \<times> real) measure)"
      using inv_lborel by (simp add: measurable_def sets_lborel)
    have "distr (lborel :: complex measure) lborel ?inv
        = distr (distr lborel borel ?C) lborel ?inv"
      using lborel_distr_complex_pair by simp
    also have "\<dots> = distr lborel lborel (?inv \<circ> ?C)"
      using distr_distr[OF inv_borel C_meas] by simp
    also have "?inv \<circ> ?C = (\<lambda>x. x)"
      by (auto simp: fun_eq_iff complex.sel split: prod.splits)
    also have "distr lborel lborel \<dots> = lborel"
      by (rule distr_id)
    finally show ?thesis .
  qed
  finally have distr_eq: "distr (lebesgue :: complex measure) lborel ?inv
      = (lborel :: (real \<times> real) measure)"
    by simp
  then have null_eq: "null_sets (lborel :: (real \<times> real) measure)
      \<subseteq> null_sets (distr (lebesgue :: complex measure) lborel ?inv)"
    by simp
  \<comment> \<open>Lift target to completion\<close>
  have inv_lebesgue: "?inv \<in> (lebesgue :: complex measure) \<rightarrow>\<^sub>M (lebesgue :: (real \<times> real) measure)"
    using completion.measurable_completion2[OF inv_compl null_eq] by simp
  \<comment> \<open>distr lebesgue lebesgue ?inv = lebesgue, via completion_distr_eq\<close>
  have distr_lebesgue_eq:
    "distr (lebesgue :: complex measure) (lebesgue :: (real \<times> real) measure) ?inv
     = (lebesgue :: (real \<times> real) measure)"
  proof -
    have "null_sets (distr (lebesgue :: complex measure) lborel ?inv) = null_sets lborel"
      using distr_eq by simp
    then have "completion (distr (lebesgue :: complex measure) lborel ?inv)
        = distr (lebesgue :: complex measure) lebesgue ?inv"
      using completion.completion_distr_eq[OF inv_compl] by simp
    then show ?thesis using distr_eq by simp
  qed
  \<comment> \<open>?C ` S = ?inv⁻¹(S) since ?C is a bijection\<close>
  have image_eq: "?C ` S = ?inv -` S \<inter> space (lebesgue :: complex measure)"
  proof (intro set_eqI iffI)
    fix z :: complex
    assume "z \<in> ?C ` S"
    then obtain p where "p \<in> S" "z = ?C p" by auto
    then show "z \<in> ?inv -` S \<inter> space lebesgue"
      by (auto simp: complex.sel split: prod.splits)
  next
    fix z :: complex
    assume "z \<in> ?inv -` S \<inter> space lebesgue"
    then have "?inv z \<in> S" by auto
    moreover have "?C (?inv z) = z"
      by (simp add: complex_eq_iff)
    ultimately show "z \<in> ?C ` S" by (metis image_eqI)
  qed
  \<comment> \<open>Measurability of ?C ` S\<close>
  have sets_S: "S \<in> sets (lebesgue :: (real \<times> real) measure)"
    using assms by (simp add: fmeasurable_def)
  show "?C ` S \<in> lmeasurable"
  proof -
    have "?C ` S \<in> sets (lebesgue :: complex measure)"
      using image_eq measurable_sets[OF inv_lebesgue sets_S] by simp
    moreover have "emeasure (lebesgue :: complex measure) (?C ` S) < \<infinity>"
    proof -
      have "emeasure (lebesgue :: complex measure) (?C ` S)
          = emeasure (lebesgue :: complex measure) (?inv -` S \<inter> space lebesgue)"
        using image_eq by simp
      also have "\<dots> = emeasure (distr (lebesgue :: complex measure) lebesgue ?inv) S"
        using emeasure_distr[OF inv_lebesgue sets_S] by simp
      also have "\<dots> = emeasure (lebesgue :: (real \<times> real) measure) S"
        using distr_lebesgue_eq by simp
      finally show ?thesis
        using assms by (auto simp: fmeasurable_def)
    qed
    ultimately show ?thesis by (simp add: fmeasurable_def)
  qed
  \<comment> \<open>Measure equality\<close>
  show "measure lebesgue (?C ` S) = measure lebesgue S"
  proof -
    have "emeasure (lebesgue :: complex measure) (?C ` S)
        = emeasure (lebesgue :: complex measure) (?inv -` S \<inter> space lebesgue)"
      using image_eq by simp
    also have "\<dots> = emeasure (distr (lebesgue :: complex measure) lebesgue ?inv) S"
      using emeasure_distr[OF inv_lebesgue sets_S] by simp
    also have "\<dots> = emeasure (lebesgue :: (real \<times> real) measure) S"
      using distr_lebesgue_eq by simp
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
      fix z :: complex
      show "z \<in> \<phi> ` ({a..b} \<times> {0..1}) \<longleftrightarrow> z \<in> S"
      proof
        assume "z \<in> \<phi> ` ({a..b} \<times> {0..1})"
        then obtain x t where xt: "x \<in> {a..b}" "t \<in> {0..1}" "z = Complex x (t * f x)"
          unfolding \<phi>_def by auto
        then show "z \<in> S"
          unfolding S_def using assms(3)[OF xt(1)]
          by (auto simp: complex.sel intro: mult_left_le_one_le mult_nonneg_nonneg)
      next
        assume "z \<in> S"
        then have hz: "a \<le> Re z" "Re z \<le> b" "0 \<le> Im z" "Im z \<le> f (Re z)"
          unfolding S_def by auto
        show "z \<in> \<phi> ` ({a..b} \<times> {0..1})"
        proof (cases "f (Re z) = 0")
          case True
          then have "Im z = 0" using hz(3,4) by linarith
          then have "z = \<phi> (Re z, 0)"
            unfolding \<phi>_def by (simp add: complex_eq_iff)
          then show ?thesis using hz(1,2) by auto
        next
          case False
          define t where "t \<equiv> Im z / f (Re z)"
          have "0 < f (Re z)" using False hz(3,4) assms(3) hz(1,2) by linarith
          then have "t \<in> {0..1}" unfolding t_def using hz(3,4) by (auto simp: field_simps)
          moreover have "z = \<phi> (Re z, t)"
            unfolding \<phi>_def t_def using False by (simp add: complex_eq_iff)
          ultimately show ?thesis using hz(1,2) by auto
        qed
      qed
    qed
    have "compact ({a..b} \<times> {0..1::real})"
      by (intro compact_Times compact_Icc)
    then show "compact S"
      using img compact_continuous_image[OF cont_\<phi>] by simp
  qed
  have S_meas: "S \<in> lmeasurable"
    using S_compact lmeasurable_compact by blast
  \<comment> \<open>Now prove the measure equals the integral using change of variables\<close>
  have S_measure: "measure lebesgue S = integral {a..b} f"
  proof -
    \<comment> \<open>Define the pair version of S and work in \<real>² = real \<times> real\<close>
    define S' :: "(real \<times> real) set"
      where "S' \<equiv> {(x, y). a \<le> x \<and> x \<le> b \<and> 0 \<le> y \<and> y \<le> f x}"
    \<comment> \<open>Step 1: measure of complex S = measure of pair S'\<close>
    \<comment> \<open>We use the fact that Complex is a measure-preserving bijection\<close>
    have S'_compact: "compact S'"
    proof -
      have "continuous_on ({a..b} \<times> {0..1}) (\<lambda>(x,t). (x, t * f x) :: real \<times> real)"
        unfolding split_def
        by (intro continuous_intros continuous_on_compose2[OF cont_g] continuous_on_fst) auto
      moreover have "(\<lambda>(x,t). (x, t * f x)) ` ({a..b} \<times> {0..1}) = S'"
      proof -
        have "\<exists>y\<in>{0..1}. t = y * f x"
          if "a \<le> x" and "x \<le> b" and t: "0 \<le> t" "t \<le> f x"
          for x :: real and t :: real
        proof (cases "f x = 0")
          case True
          then show ?thesis
            using t by fastforce
        next
          case False
          with t show ?thesis 
            by (rule_tac x = "t / f x" in bexI) auto
        qed
        then show ?thesis
          by (auto simp: mult_left_le_one_le fge0 image_iff S'_def split: prod.splits)
      qed
      moreover have "compact ({a..b} \<times> {0..1::real})"
        by (intro compact_Times compact_Icc)
      ultimately show ?thesis
        using compact_continuous_image by blast
    qed
    have S'_meas: "S' \<in> lmeasurable"
      using S'_compact lmeasurable_compact by blast
    have meas_eq: "measure lebesgue S = measure lebesgue S'"
    proof -
      have S_eq: "S = (\<lambda>(x,y). Complex x y) ` S'"
      proof (rule set_eqI)
        fix z :: complex
        show "z \<in> S \<longleftrightarrow> z \<in> (\<lambda>(x,y). Complex x y) ` S'"
          unfolding S_def S'_def image_iff
          by (auto simp: complex.sel complex_eq_iff intro!: exI[of _ "Re z"] exI[of _ "Im z"])
      qed
      then show ?thesis
        using measure_Complex_image(2)[OF S'_meas] by simp
    qed
    \<comment> \<open>Step 2: compute measure of S' using Fubini\<close>
    have "measure lebesgue S' = integral {a..b} f"
    proof -
      have integ: "integrable lborel (indicat_real S')"
      proof -
        have "integrable lborel (\<lambda>x. indicat_real S' x *\<^sub>R (1::real))"
          by (rule borel_integrable_compact[OF S'_compact continuous_on_const])
        then show ?thesis by simp
      qed
      \<comment> \<open>The slice x \<mapsto> integral over y of indicator S' equals f(x) on [a,b] and 0 outside\<close>
      have slice_eq: "\<And>x. integral UNIV (\<lambda>y. indicat_real S' (x, y)) =
                          (if x \<in> {a..b} then f x else 0)"
      proof -
        fix x :: real
        show "integral UNIV (\<lambda>y. indicat_real S' (x, y)) = (if x \<in> {a..b} then f x else 0)"
        proof (cases "x \<in> {a..b}")
          case True
          have "{y. (x,y) \<in> S'} = {0..f x}"
            unfolding S'_def using True by auto
          then have "integral UNIV (\<lambda>y. indicat_real S' (x, y)) = integral {0..f x} (\<lambda>_. 1)"
            by (smt (verit, ccfv_SIG) Henstock_Kurzweil_Integration.integral_cong Henstock_Kurzweil_Integration.integral_restrict_UNIV indicator_eq_0_iff indicator_eq_1_iff
                mem_Collect_eq)
          also have "... = f x"
            using assms(3)[OF True] by simp
          finally show ?thesis using True by simp
        next
          case False
          have "{y. (x,y) \<in> S'} = {}"
            unfolding S'_def using False by auto
          then show ?thesis using False
            by auto
        qed
      qed
      \<comment> \<open>Apply Fubini\<close>
      have "measure lebesgue S' = integral UNIV (indicat_real S')"
        using lmeasure_integral_UNIV[OF S'_meas] by simp
      also have "... = integral UNIV (\<lambda>x. integral UNIV (\<lambda>y. indicat_real S' (x, y)))"
      proof (rule gauge_integral_Fubini_universe_x(1)[OF integ])
        show "(\<lambda>x. integral UNIV (\<lambda>y. indicat_real S' (x, y))) \<in> borel_measurable lborel"
        proof -
          have "(\<lambda>x. integral UNIV (\<lambda>y. indicat_real S' (x, y))) =
                (\<lambda>x. if x \<in> {a..b} then f x else 0)"
            by (rule ext) (use slice_eq in auto)
          also have "... \<in> borel_measurable lborel"
          proof -
            have "(\<lambda>x::real. if x \<in> {a..b} then f x else 0) \<in> borel_measurable borel"
              by (intro borel_measurable_continuous_on_if continuous_on_const assms(2)) auto
            then show ?thesis by (simp add: sets_lborel)
          qed
          finally show ?thesis .
        qed
      qed
      also have "... = integral UNIV (\<lambda>x. if x \<in> {a..b} then f x else 0)"
        by (rule integral_cong) (use slice_eq in auto)
      also have "... = integral {a..b} f"
        by (rule integral_restrict_UNIV)
      finally show ?thesis .
    qed
    then show ?thesis using meas_eq by simp
  qed

  show "{z::complex. a \<le> Re z \<and> Re z \<le> b \<and> 0 \<le> Im z \<and> Im z \<le> f (Re z)} \<in> lmeasurable"
    using S_meas unfolding S_def .
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
  \<comment> \<open>Step 3: countable intersection\<close>
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
  have eq: "{(x, y). y < f x} = (\<Union>q \<in> \<rat>. {x. q \<le> f x} \<times> {y. y < q})"
  proof (intro equalityI subsetI)
    fix p :: "real \<times> real"
    assume "p \<in> {(x, y). y < f x}"
    then obtain x y where p: "p = (x, y)" "y < f x" by auto
    then obtain q where "q \<in> \<rat>" "y < q" "q < f x"
      using Rats_dense_in_real by blast
    then show "p \<in> (\<Union>q \<in> \<rat>. {x. q \<le> f x} \<times> {y. y < q})"
      using p by (auto intro: less_imp_le)
  next
    fix p :: "real \<times> real"
    assume "p \<in> (\<Union>q \<in> \<rat>. {x. q \<le> f x} \<times> {y. y < q})"
    then show "p \<in> {(x, y). y < f x}" by auto
  qed
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
    show "{x. q \<le> f x} \<times> {y :: real. y < q}
        \<in> sets (lebesgue :: (real \<times> real) measure)"
      using lebesgue_measurable_Times_UNIV[OF B] lebesgue_measurable_UNIV_Times[OF A]
        sets.Int[of "{x. q \<le> f x} \<times> UNIV" "lebesgue :: (real \<times> real) measure"
                   "UNIV \<times> {y. y < q}"]
      by (simp add: Times_Int_Times)
  qed
  \<comment> \<open>Countable union\<close>
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
  \<comment> \<open>The graph of f is contained in graph(h) \<union> (N \<times> UNIV)\<close>
  have graph_sub: "{(x, y). f x = y} \<subseteq> {(x, y). h x = y} \<union> N \<times> UNIV"
  proof clarsimp
    fix a assume "a \<notin> N"
    then show "h a = f a" using h_eq by simp
  qed
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
  proof -
    have "emeasure (lborel \<Otimes>\<^sub>M lborel) {(x, y). h x = y} =
      (\<integral>\<^sup>+ x. emeasure lborel (Pair x -` {(x, y). h x = y}) \<partial>lborel)"
      by (rule lborel.emeasure_pair_measure_alt[OF graph_h_borel])
    then show ?thesis by simp
  qed
  then have graph_h_null: "{(x, y). h x = y} \<in> null_sets (lborel :: (real \<times> real) measure)"
    by (metis graph_h_borel lborel_prod null_setsI)
  \<comment> \<open>N \<times> UNIV is contained in a null set in lborel\<close>
  have "N \<in> null_sets (lebesgue :: real measure)"
    using neg_N negligible_iff_null_sets by auto
  then obtain N' where N': "N' \<in> null_sets lborel" "N \<subseteq> N'"
    using null_sets_completion_iff2 by metis
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

section \<open>Convex curve lemmas\<close>

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

lemma frontier_convex_hull_eq_path_image':
  fixes g :: "real \<Rightarrow> complex"
  assumes "simple_path g" "pathfinish g = pathstart g"
          "path_image g \<subseteq> frontier (convex hull (path_image g))"
  shows "frontier (convex hull (path_image g)) = path_image g"
proof (rule equalityI)
  show "frontier (convex hull path_image g) \<subseteq> path_image g"
  proof -
    have compact_pi: "compact (path_image g)"
      using compact_simple_path_image[OF assms(1)] .
    have closed_hull: "closed (convex hull (path_image g))"
      using compact_convex_hull[OF compact_pi] compact_imp_closed by blast
    have bounded_hull: "bounded (convex hull (path_image g))"
      using bounded_convex_hull compact_imp_bounded[OF compact_pi] by blast
    have convex_hull: "convex (convex hull (path_image g))"
      by (rule convex_convex_hull)
    \<comment> \<open>The interior of the convex hull is connected, bounded, and disjoint from path_image g\<close>
    have int_sub: "interior (convex hull (path_image g)) \<inter> path_image g = {}"
      using assms(3) frontier_def by auto
    have "connected (interior (convex hull (path_image g)))"
      using convex_connected convex_interior convex_hull by blast
    moreover have "bounded (interior (convex hull (path_image g)))"
      using bounded_hull bounded_interior by blast
    moreover have "interior (convex hull (path_image g)) \<subseteq> - path_image g"
      using int_sub by blast
    ultimately have int_inside: "interior (convex hull (path_image g)) \<subseteq> inside (path_image g)"
      using Jordan_inside_outside[of g] assms(1,2) 
      by (smt (verit, ccfv_threshold) Diff_eq_empty_iff compl_le_compl_iff connected_Int_frontier
          convex_hull double_compl hull_antimono inf.absorb_iff2 inside_outside int_sub interior_Int
          interior_eq outside_subset_convex subset_hull sup.coboundedI2)
    \<comment> \<open>Also inside \<subseteq> convex hull (since outside contains complement of hull)\<close>
    have "- (convex hull (path_image g)) \<subseteq> outside (path_image g)"
      by (simp add: hull_subset outside_subset_convex)
    hence inside_sub: "inside (path_image g) \<subseteq> convex hull (path_image g)"
      by (metis Un_subset_iff compl_le_swap2 union_with_inside)
    \<comment> \<open>Since inside is open and \<subseteq> convex hull, inside \<subseteq> interior (convex hull)\<close>
    have "open (inside (path_image g))"
      using Jordan_inside_outside assms(1,2) by blast
    hence "inside (path_image g) \<subseteq> interior (convex hull (path_image g))"
      using inside_sub open_subset_interior by blast
    \<comment> \<open>So interior (convex hull) = inside\<close>
    hence "interior (convex hull (path_image g)) = inside (path_image g)"
      using int_inside by blast
    \<comment> \<open>frontier (convex hull) = convex hull - interior (convex hull) = convex hull - inside\<close>
    with assms show ?thesis
      by (metis Diff_cancel  convex_convex_hull convex_interior diff_shunt
          frontier_convex_hull_eq_path_image)
  qed
  show "path_image g \<subseteq> frontier (convex hull path_image g)"
    by (rule assms(3))
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
  \<comment> \<open>Convert to lebesgue_on S integrals\<close>
  have f_meas_on: "f \<in> borel_measurable (lebesgue_on S)"
    using assms(3) measurable_restrict_space1 by blast
  have f_sq_integ: "integrable (lebesgue_on S) (\<lambda>x. (f x)\<^sup>2)"
  proof -
    have "(\<lambda>x. indicator S x * (f x)\<^sup>2) = (\<lambda>x. if x \<in> S then (f x)\<^sup>2 else 0)"
      by (auto simp: indicator_times_eq_if)
    hence "integrable lebesgue (\<lambda>x. if x \<in> S then (f x)\<^sup>2 else 0)"
      using assms(4) by simp
    then show ?thesis
      by (simp add: Lebesgue_Measure.integrable_restrict_UNIV[OF assms(1), of "\<lambda>x. (f x)\<^sup>2"])
  qed
  have f_sq_int: "f square_integrable S"
    unfolding square_integrable_def using assms(1) f_meas_on f_sq_integ by blast

  \<comment> \<open>(\<lambda>x. 1) is square integrable since S has finite measure\<close>
  have one_sq_int: "(\<lambda>x. 1::real) square_integrable S"
    unfolding square_integrable_def
  proof (intro conjI)
    show "S \<in> sets lebesgue" by (rule assms(1))
    show "(\<lambda>x. 1::real) \<in> borel_measurable (lebesgue_on S)" by simp
    have "finite_measure (lebesgue_on S)"
      by (rule finite_measure_lebesgue_on[OF assms(2)])
    then show "integrable (lebesgue_on S) (\<lambda>x. (1::real)\<^sup>2)"
      by (simp add: finite_measure.integrable_const)
  qed
  \<comment> \<open>Schwartz inequality: |l2product S f 1| \<le> l2norm S f * l2norm S 1\<close>
  have schwartz: "\<bar>l2product S f (\<lambda>x. 1)\<bar> \<le> l2norm S f * l2norm S (\<lambda>x. 1)"
    by (rule Schwartz_inequality_abs[OF f_sq_int one_sq_int])
  \<comment> \<open>Rewrite goal in terms of l2product\<close>
  have If_eq: "LINT x|lebesgue. indicator S x * f x = l2product S f (\<lambda>x. 1)"
    by (simp add: to_lebesgue_on l2product_def)
  have If2_eq: "LINT x|lebesgue. indicator S x * (f x)\<^sup>2 = l2product S f f"
    by (simp add: to_lebesgue_on l2product_def power2_eq_square)
  have norm1_sq: "(l2norm S (\<lambda>x. 1))\<^sup>2 = measure lebesgue S"
  proof -
    have "(l2norm S (\<lambda>x. 1))\<^sup>2 = l2product S (\<lambda>x. 1) (\<lambda>x. 1)"
      by (rule l2norm_pow_2[OF one_sq_int])
    also have "\<dots> = LINT x|lebesgue_on S. 1"
      by (simp add: l2product_def)
    also have "\<dots> = measure (lebesgue_on S) S"
      using finite_measure_lebesgue_on[OF assms(2)]
      by simp
    also have "\<dots> = measure lebesgue S"
      by (metis assms(1) order.refl measure_restrict_space sets.Int_space_eq2)
    finally show ?thesis .
  qed
  have schwartz_sq: "(l2product S f (\<lambda>x. 1))\<^sup>2 \<le> (l2norm S f)\<^sup>2 * (l2norm S (\<lambda>x. 1))\<^sup>2"
  proof -
    have "\<bar>l2product S f (\<lambda>x. 1)\<bar> \<le> l2norm S f * l2norm S (\<lambda>x. 1)"
      by (rule schwartz)
    hence "(l2product S f (\<lambda>x. 1))\<^sup>2 \<le> (l2norm S f * l2norm S (\<lambda>x. 1))\<^sup>2"
      using real_sqrt_abs sqrt_le_D by presburger
    thus ?thesis by (simp add: power_mult_distrib)
  qed
  show ?thesis
    by (simp only: If_eq If2_eq norm1_sq l2norm_pow_2[OF f_sq_int])
      (use schwartz_sq norm1_sq l2norm_pow_2[OF f_sq_int] in \<open>simp add: mult.commute\<close>)
qed

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
  have f': \<open>f' integrable_on {0..2*pi}\<close>
    using f'hsd [of \<open>2*pi\<close>] by fastforce

  have f'abs: \<open>f' absolutely_integrable_on {0..2*pi}\<close>
  proof (rule absolutely_integrable_integrable_bound [where g = \<open>\<lambda>x. 1 + (f' x)\<^sup>2\<close>])
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

  have contf: \<open>continuous_on {0..2*pi} f\<close>
  proof (rule continuous_on_eq [of _ \<open>\<lambda>x. integral {0..x} f' + f 0\<close>])
    show \<open>continuous_on {0..2*pi} (\<lambda>x. integral {0..x} f' + f 0)\<close>
      by (intro continuous_on_add indefinite_integral_continuous_1 [OF f'] continuous_on_const)
    show \<open>\<And>x. x \<in> {0..2*pi} \<Longrightarrow> integral {0..x} f' + f 0 = f x\<close>
      using f'hsd by (auto simp: has_integral_integrable_integral)
  qed
  show "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
    by (intro integrable_continuous_interval continuous_on_power contf)

  obtain a where "0 \<le> a" "a < pi" "f (a + pi) = f a"
  proof -
    define g where "g \<equiv> \<lambda>x. f (x + pi) - f x"
    have gcont: "continuous_on {0..pi} g"
      unfolding g_def
    proof (intro continuous_on_diff)
      show "continuous_on {0..pi} (\<lambda>x. f (x + pi))"
      proof (rule continuous_on_compose2 [OF contf continuous_on_add [OF continuous_on_id continuous_on_const]])
        show "(\<lambda>x. x + pi) ` {0..pi} \<subseteq> {0..2*pi}"
          using pi_gt_zero by auto
      qed
      show "continuous_on {0..pi} f"
        using continuous_on_subset [OF contf] pi_gt_zero by auto
    qed
    have geq: "g 0 + g pi = 0"
      unfolding g_def using feq by simp
    have "0 \<in> g ` {0..pi}"
    proof -
      have iv: "is_interval (g ` {0..pi})"
        using is_interval_connected_1 connected_continuous_image [OF gcont connected_Icc]
        by blast
      have g0: "g 0 \<in> g ` {0..pi}" and gpi: "g pi \<in> g ` {0..pi}"
        using pi_gt_zero by auto
      consider "g 0 \<le> 0" | "g pi \<le> 0"
        using geq by linarith
      then show ?thesis
        by (metis add_le_same_cancel1 add_le_same_cancel2 g0 geq gpi iv mem_is_interval_1_I)
    qed
    then obtain a where "a \<in> {0..pi}" "g a = 0"
      by auto
    show thesis
    proof (cases "a = pi")
      case True
      then have "g 0 = 0" using geq \<open>g a = 0\<close> by auto
      then show thesis using that [of 0] pi_gt_zero by (auto simp: g_def)
    next
      case False
      then show thesis using that [of a] \<open>a \<in> {0..pi}\<close> \<open>g a = 0\<close>
        by (auto simp: g_def)
    qed
  qed

  define g where "g \<equiv> \<lambda>x. (f x - f a)\<^sup>2 / tan (x - a)"
  define g' where "g' \<equiv> \<lambda>x. (f' x)\<^sup>2 - (f x - f a)\<^sup>2 - (f' x - (f x - f a) / tan (x - a))\<^sup>2"

  text \<open>The integral over completely trouble-free intervals.\<close>
  have trouble_free:
    "(g' has_integral g d - g c) {c..d}"
    if cd: "c \<le> d"
      and sub_cd: "{c..d} \<subseteq> {0..2*pi}"
      and sin_nz: "\<And>x. x \<in> {c..d} \<Longrightarrow> sin (x - a) \<noteq> 0"
    for c d
  proof -
    text \<open>Apply integration by parts with
      \<^item> \<open>\<lambda>x. (f x - f a)²\<close> and its derivative \<open>\<lambda>x. 2 * (f x - f a) * f' x\<close>
      \<^item> \<open>\<lambda>x. inverse (tan (x - a))\<close> and its derivative \<open>\<lambda>x. - inverse (sin (x - a))²\<close>\<close>
    have f'_abs: "(\<lambda>x. 2 * (f x - f a) * f' x) absolutely_integrable_on {c..d}"
    proof -
      have f'_abs_cd: "f' absolutely_integrable_on {c..d}"
        using absolutely_integrable_on_subinterval[OF f'abs sub_cd] .
      have contf_cd: "continuous_on {c..d} f"
        using continuous_on_subset[OF contf sub_cd] .
      have cont_ffa: "continuous_on {c..d} (\<lambda>x. 2 * (f x - f a))"
        by (intro continuous_intros contf_cd)
      have meas: "(\<lambda>x. 2 * (f x - f a)) \<in> borel_measurable (lebesgue_on {c..d})"
        using cont_ffa by (intro continuous_imp_measurable_on_sets_lebesgue) auto
      have bdd: "bounded ((\<lambda>x. 2 * (f x - f a)) ` {c..d})"
        using cont_ffa compact_Icc compact_continuous_image compact_imp_bounded by blast
      show ?thesis
        using absolutely_integrable_bounded_measurable_product_real
          [OF meas _ bdd f'_abs_cd] by auto
    qed
    have g'_abs: "(\<lambda>x. - inverse ((sin (x - a))\<^sup>2)) absolutely_integrable_on {c..d}"
    proof (rule absolutely_integrable_continuous_real)
      show "continuous_on {c..d} (\<lambda>x. - inverse ((sin (x - a))\<^sup>2))"
        by (intro continuous_intros) (use sin_nz in auto)
    qed
    have f'_int: "((\<lambda>t. 2 * (f t - f a) * f' t) has_integral
                   ((f x - f a)\<^sup>2 - (f c - f a)\<^sup>2)) {c..x}"
      if xcd: "x \<in> {c..d}" for x
    proof -
      have cx: "c \<le> x" using xcd cd by auto
      have xd: "x \<le> d" using xcd by auto
      have sub_cx: "{c..x} \<subseteq> {0..2*pi}" using sub_cd xd by auto
          \<comment> \<open>f agrees with f 0 + integral {0..\<sqdot>} f' on {0..2*pi}\<close>
      have f_eq: "f t = f 0 + integral {0..t} f'" if "t \<in> {0..2*pi}" for t
        using f'hsd[OF that] by (auto simp: has_integral_integrable_integral)
          \<comment> \<open>f is absolutely continuous on {0..2*pi}\<close>
      have ac_f: "absolutely_continuous_on {0..2*pi} f"
        using absolute_integral_absolutely_continuous_derivative_eq f'abs f'hsd by blast
        \<comment> \<open>f - f a is absolutely continuous on {c..x}\<close>
      have ac_ffa: "absolutely_continuous_on {c..x} (\<lambda>t. f t - f a)"
        using absolutely_continuous_on_sub
          [OF absolutely_continuous_on_subset[OF ac_f sub_cx]
            absolutely_continuous_on_const] .
          \<comment> \<open>(f t - f a)^2 is absolutely continuous on {c..x}\<close>
      have ac_sq: "absolutely_continuous_on {c..x} (\<lambda>t. (f t - f a)\<^sup>2)"
        unfolding power2_eq_square
        using absolutely_continuous_on_mul[OF ac_ffa ac_ffa]
        by (simp add: scaleR_conv_of_real)
          \<comment> \<open>f has derivative f' a.e. on {0..2*pi}\<close>
      obtain k where negk: "negligible k"
        and derivf: "\<And>t. t \<in> {0..2*pi} - k \<Longrightarrow>
          ((\<lambda>u. integral {0..u} f') has_vector_derivative f' t) (at t within {0..2*pi})"
        using f' has_vector_derivative_indefinite_integral by blast
          \<comment> \<open>Hence (f t - f a)^2 has the right derivative a.e.\<close>
      have deriv_sq: "((\<lambda>t. (f t - f a)\<^sup>2) has_vector_derivative 2 * (f t - f a) * f' t)
          (at t within {c..x})"
        if "t \<in> {c..x} - k" for t
      proof -
        have t02pi: "t \<in> {0..2*pi}" using that sub_cx by auto
        have "t \<in> {0..2*pi} - k" using that sub_cx by auto
        then have hvd_int: "((\<lambda>u. integral {0..u} f') has_vector_derivative f' t)
            (at t within {0..2*pi})"
          using derivf by auto
            \<comment> \<open>Convert to has_vector_derivative of f\<close>
        have "((\<lambda>u. f u - f 0) has_vector_derivative f' t) (at t within {0..2*pi})"
        proof (rule has_vector_derivative_transform_within[OF hvd_int])
          show "0 < (1::real)" by simp
          show "t \<in> {0..2*pi}" using t02pi .
          fix u assume "u \<in> {0..2*pi}" "dist u t < 1"
          then show "integral {0..u} f' = f u - f 0"
            using f_eq f'hsd by blast
        qed
        then have "(f has_vector_derivative f' t) (at t within {0..2*pi})"
          using has_vector_derivative_diff_const by blast
        then have fderiv: "(f has_vector_derivative f' t) (at t within {c..x})"
          by (rule has_vector_derivative_within_subset) (use sub_cx in auto)
        have ffa_deriv: "((\<lambda>t. f t - f a) has_vector_derivative f' t) (at t within {c..x})"
          using has_vector_derivative_diff[OF fderiv has_vector_derivative_const] by simp
        show ?thesis
          unfolding power2_eq_square
          using has_vector_derivative_mult[OF ffa_deriv ffa_deriv]
          by (simp add: algebra_simps scaleR_conv_of_real)
      qed
      show ?thesis
        using fundamental_theorem_of_calculus_absolutely_continuous
          [OF negk cx ac_sq deriv_sq] by simp
    qed
    have g'_int: "((\<lambda>t. - inverse ((sin (t - a))\<^sup>2)) has_integral
                   (inverse (tan (x - a)) - inverse (tan (c - a)))) {c..x}"
      if xcd: "x \<in> {c..d}" for x
    proof -
      have cx: "c \<le> x" using xcd cd by auto
      have sub_cx: "{c..x} \<subseteq> {c..d}" using xcd by auto
          \<comment> \<open>inverse(tan(t-a)) = cos(t-a)/sin(t-a) when sin(t-a) \<noteq> 0\<close>
      have inv_tan_eq: "inverse (tan (t - a)) = cos (t - a) / sin (t - a)"
        if "t \<in> {c..x}" for t
        by (simp add: Multiseries_Expansion.tan_conv_sin_cos)
        \<comment> \<open>cos(t-a)/sin(t-a) has the right derivative\<close>
      have deriv: "((\<lambda>t. cos (t - a) / sin (t - a)) has_vector_derivative
                    - inverse ((sin (t - a))\<^sup>2)) (at t within {c..x})"
        if "t \<in> {c..x}" for t
      proof -
        have sin_nz_t: "sin (t - a) \<noteq> 0" using sin_nz that sub_cx by auto
        have "((\<lambda>t. cos (t - a) / sin (t - a)) has_real_derivative
              (- sin (t - a) * sin (t - a) - cos (t - a) * cos (t - a)) / (sin (t - a) * sin (t - a)))
              (at t within {c..x})"
          by (intro derivative_eq_intros | simp add: sin_nz_t)+
        also have "(- sin (t - a) * sin (t - a) - cos (t - a) * cos (t - a)) / (sin (t - a) * sin (t - a))
                 = - inverse ((sin (t - a))\<^sup>2)"
          by (smt (verit, ccfv_threshold) divide_real_def inverse_eq_divide more_arith_simps(10,7)
              power2_eq_square sin_cos_squared_add)
        finally show ?thesis
          by (simp add: has_real_derivative_iff_has_vector_derivative)
      qed
        \<comment> \<open>Apply FTC\<close>
      have "((\<lambda>t. - inverse ((sin (t - a))\<^sup>2)) has_integral
             (cos (x - a) / sin (x - a) - cos (c - a) / sin (c - a))) {c..x}"
        using fundamental_theorem_of_calculus[OF cx deriv] .
      then show ?thesis
        using inv_tan_eq[of x] inv_tan_eq[of c] cx by simp
    qed
    text \<open>The IBP conclusion gives us \<open>has_integral\<close> for the sum
      \<open>(f x - f a)² * (- inverse (sin (x - a)²)) + 2 * (f x - f a) * f' x * inverse (tan (x - a))\<close>,
      which after algebra equals \<open>g'\<close>, with value \<open>g d - g c\<close>.\<close>
    have ibp_int: "((\<lambda>x. (f x - f a)\<^sup>2 * (- inverse ((sin (x - a))\<^sup>2)) +
      2 * (f x - f a) * f' x * inverse (tan (x - a)))
      has_integral ((f y - f a)\<^sup>2 * inverse (tan (y - a)) -
                    (f c - f a)\<^sup>2 * inverse (tan (c - a)))) {c..y}"
      if "y \<in> {c..d}" for y
    proof (rule absolute_real_integration_by_parts_sum(2))
      show "c \<le> d" using cd .
      show "(\<lambda>x. 2 * (f x - f a) * f' x) absolutely_integrable_on {c..d}"
        using f'_abs .
      show "(\<lambda>x. - inverse ((sin (x - a))\<^sup>2)) absolutely_integrable_on {c..d}"
        using g'_abs .
      show "((\<lambda>t. 2 * (f t - f a) * f' t) has_integral
            ((f x - f a)\<^sup>2 - (f c - f a)\<^sup>2)) {c..x}"
        if "x \<in> {c..d}" for x using f'_int[OF that] .
      show "((\<lambda>t. - inverse ((sin (t - a))\<^sup>2)) has_integral
            (inverse (tan (x - a)) - inverse (tan (c - a)))) {c..x}"
        if "x \<in> {c..d}" for x using g'_int[OF that] .
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
          \<comment> \<open>Multiply both sides by s² and show equality\<close>
      have "((f x - f a)\<^sup>2 * (- inverse ((sin (x - a))\<^sup>2)) +
        2 * (f x - f a) * f' x * inverse (tan (x - a))) * ?s\<^sup>2 =
        - ?F\<^sup>2 + 2 * ?F * f' x * ?c * ?s"
        using snz snz2 unfolding tan_def
        by (simp add: field_simps power2_eq_square)

      moreover have "g' x * ?s\<^sup>2 = - ?F\<^sup>2 + 2 * ?F * f' x * ?c * ?s"
      proof -
        have expand: "g' x = (f' x)\<^sup>2 - ?F\<^sup>2 - (f' x - ?F * ?c / ?s)\<^sup>2"
          unfolding g'_def tan_def using snz by (simp add: field_simps)
        have "g' x * ?s\<^sup>2 =
          ((f' x)\<^sup>2 - ?F\<^sup>2) * ?s\<^sup>2 - (f' x * ?s - ?F * ?c)\<^sup>2"
          unfolding expand using snz
          by (simp add: field_simps power2_eq_square)
        also have "\<dots> = - ?F\<^sup>2 * ?s\<^sup>2 - ?F\<^sup>2 * ?c\<^sup>2 + 2 * ?F * f' x * ?c * ?s"
          by (simp add: power2_eq_square algebra_simps)
        also have "\<dots> = - ?F\<^sup>2 + 2 * ?F * f' x * ?c * ?s"
          using sc1 by algebra 
        finally show ?thesis .
      qed
      ultimately show ?thesis using snz2
        by (metis mult_right_cancel)
    qed
      \<comment> \<open>The IBP value equals g d - g c\<close>
    have value_eq: "(f d - f a)\<^sup>2 * inverse (tan (d - a)) -
      (f c - f a)\<^sup>2 * inverse (tan (c - a)) = g d - g c"
      unfolding g_def divide_inverse by (rule refl)
        \<comment> \<open>Combine using has_integral_eq\<close>
    show ?thesis
      using has_integral_eq ibp_int integrand_eq value_eq
      by (metis (no_types, lifting) atLeastAtMost_iff order.refl that(1))
  qed

  text \<open>Continuity of g.\<close>
  have g_cont: "continuous_on {0..2*pi} g"
    unfolding continuous_on_eq_continuous_within
  proof
    fix c assume c_in: "c \<in> {0..2*pi}"
    show "continuous (at c within {0..2*pi}) g"
    proof (cases "sin (c - a) = 0")
      case False
        \<comment> \<open>When sin(c - a) \<noteq> 0, g is a quotient of continuous functions.\<close>
      have g_eq: "g x = (f x - f a)\<^sup>2 * cos (x - a) / sin (x - a)" for x
        unfolding g_def tan_def by (simp add: field_simps)
      show ?thesis unfolding g_eq
      proof (intro continuous_intros)
        show "continuous (at c within {0..2*pi}) f"
          using contf c_in continuous_on_eq_continuous_within by blast
        show "sin (c - a) \<noteq> 0" by (rule False)
      qed
    next
      case True
        \<comment> \<open>When sin(c - a) = 0, g(c) = 0 and we need to show g(x) \<rightarrow> 0.\<close>
        \<comment> \<open>First establish that f(c) = f(a).\<close>
      have fca: "f c = f a"
      proof -
        from True obtain n :: int where npi: "c - a = of_int n * pi"
          using sin_zero_iff_int2 by auto
        have "n = 0 \<or> n = 1 \<or> n = 2"
        proof -
          from npi have "c = a + of_int n * pi" by simp
          with c_in \<open>0 \<le> a\<close> \<open>a < pi\<close> have "0 \<le> a + of_int n * pi" "a + of_int n * pi \<le> 2 * pi"
            by auto
          hence "of_int n * pi \<ge> -a" "of_int n * pi \<le> 2 * pi - a"
            by linarith+
          hence "of_int n \<ge> -a / pi" "of_int n \<le> (2 * pi - a) / pi"
            using pi_gt_zero by (simp_all add: field_simps)
          moreover have "-a / pi > -1" using \<open>0 \<le> a\<close> \<open>a < pi\<close> pi_gt_zero by (simp add: field_simps)
          moreover have "(2 * pi - a) / pi < 3"
            using \<open>0 \<le> a\<close> \<open>a < pi\<close> pi_gt_zero by (auto simp: divide_simps)
          ultimately have "of_int n > (-1 :: real)" "of_int n < (3 :: real)" by linarith+
          hence "n \<ge> 0" "n \<le> 2" by linarith+
          thus ?thesis by auto
        qed
        thus ?thesis
        proof (elim disjE)
          assume "n = 0" then show "f c = f a" using npi by simp
        next
          assume "n = 1" then show "f c = f a"
            using npi \<open>f (a + pi) = f a\<close> by (simp add: algebra_simps)
        next
          assume "n = 2"
          then have "c = a + 2 * pi" using npi by (simp add: algebra_simps)
          with c_in \<open>0 \<le> a\<close> \<open>a < pi\<close> pi_gt_zero have "a = 0" by auto
          thus "f c = f a" using \<open>c = a + 2 * pi\<close> feq by simp
        qed
      qed
        \<comment> \<open>Now g(c) = 0.\<close>
      have gc0: "g c = 0"
        unfolding g_def using fca by simp
          \<comment> \<open>The continuity reduces to showing g(x) \<rightarrow> 0.\<close>
      show ?thesis unfolding continuous_within gc0
      proof -
        \<comment> \<open>Derive tan(x - a) = tan(x - c) from sin(c - a) = 0.\<close>
        from True obtain n :: int where npi: "c - a = of_int n * pi"
          using sin_zero_iff_int2 by auto
        have tan_eq: "tan (x - a) = tan (x - c)" for x
          by (metis npi diff_add_cancel diff_diff_eq2 tan_periodic_int)
          \<comment> \<open>So g(x) = (f(x) - f(c))² / tan(x - c).\<close>
        have g_eq: "g x = (f x - f c)\<^sup>2 / tan (x - c)" for x
          unfolding g_def tan_eq using fca by simp
            \<comment> \<open>Rewrite as cos/sin form.\<close>
        have g_eq2: "g x = (f x - f c)\<^sup>2 * cos (x - c) / sin (x - c)" for x
          unfolding g_eq tan_def by (simp add: field_simps)
            \<comment> \<open>Show (g \<longlongrightarrow> 0) using the cos/sin form.\<close>
        show "(g \<longlongrightarrow> 0) (at c within {0..2*pi})"
        proof -
          \<comment> \<open>Cauchy-Schwarz bound: (f x - f c)² \<le> |x - c| * \<integral>_c^x (f')².\<close>
          have cs_bound: "(f x - f c)\<^sup>2 \<le> \<bar>x - c\<bar> * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
            if xin: "x \<in> {0..2*pi}" for x
          proof -
            \<comment> \<open>Helper: f' integrable on any subinterval of {0..2\<pi>}\<close>
            have f'_int_sub: "f' integrable_on {a..b}" if "{a..b} \<subseteq> {0..2*pi}" for a b
              using integrable_subinterval_real[OF set_lebesgue_integral_eq_integral(1)[OF f'abs] that] .
                \<comment> \<open>Helper: (f')² integrable on any subinterval of {0..2\<pi>}\<close>
            have f'2_int_sub: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {a..b}" if "{a..b} \<subseteq> {0..2*pi}" for a b
              using integrable_subinterval_real[OF f'2 that] .
                \<comment> \<open>Helper: FTC gives f(b) - f(a) = \<integral>_a^b f' for a,b \<in> {0..2\<pi>}\<close>
            have ftc_sub: "f b - f a = integral {a..b} f'"
              if "a \<in> {0..2*pi}" "b \<in> {0..2*pi}" "a \<le> b" for a b
            proof -
              have "integral {0..a} f' + integral {a..b} f' = integral {0..b} f'"
                by (meson Henstock_Kurzweil_Integration.integral_combine atLeastAtMost_iff f'hsd
                    has_integral_integrable that)
              moreover have "integral {0..a} f' = f a - f 0"
                using f'hsd that by (auto simp: has_integral_integrable_integral)
              moreover have "integral {0..b} f' = f b - f 0"
                using f'hsd that by (auto simp: has_integral_integrable_integral)
              ultimately show ?thesis by linarith
            qed
              \<comment> \<open>Helper: Cauchy-Schwarz (\<integral>_I f')² \<le> (b-a) * \<integral>_I (f')² for I = {a..b} \<subseteq> {0..2\<pi>}\<close>
            have cs_sub: "(integral {a..b} f')\<^sup>2 \<le> (b - a) * integral {a..b} (\<lambda>t. (f' t)\<^sup>2)"
              if sub: "{a..b} \<subseteq> {0..2*pi}" and ab: "a < b" for a b
            proof -
              define \<mu> where "\<mu> \<equiv> integral {a..b} f' / (b - a)"
              have f'I: "f' integrable_on {a..b}" by (rule f'_int_sub[OF sub])
              have f'2I: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {a..b}" by (rule f'2_int_sub[OF sub])
                  \<comment> \<open>(f' - \<mu>)² = (f')² - 2\<mu>f' + \<mu>², each integrable\<close>
              have int1: "(\<lambda>t. - (2 * \<mu>) * f' t) integrable_on {a..b}"
                using integrable_cmul[OF f'I, of "- (2 * \<mu>)"] by (simp add: scaleR_conv_of_real)
              have int2: "(\<lambda>t. \<mu>\<^sup>2) integrable_on {a..b}"
                by (rule integrable_const_ivl)
              have sub_int: "(\<lambda>t. (f' t - \<mu>)\<^sup>2) integrable_on {a..b}"
              proof -
                have "(\<lambda>t. (f' t)\<^sup>2 + (- (2 * \<mu>) * f' t + \<mu>\<^sup>2)) integrable_on {a..b}"
                  by (rule integrable_add[OF f'2I integrable_add[OF int1 int2]])
                moreover have "(f' t - \<mu>)\<^sup>2 = (f' t)\<^sup>2 + (- (2 * \<mu>) * f' t + \<mu>\<^sup>2)" for t
                  by (simp add: power2_eq_square algebra_simps)
                ultimately show ?thesis by (simp add: o_def)
              qed
              have "0 \<le> integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2)"
                by (rule integral_nonneg[OF sub_int]) (simp add: zero_le_power2)
              also have "integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2) =
                integral {a..b} (\<lambda>t. (f' t)\<^sup>2) + (- (2 * \<mu>) * integral {a..b} f' + \<mu>\<^sup>2 * (b - a))"
              proof -
                have "integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2) =
                  integral {a..b} (\<lambda>t. (f' t)\<^sup>2 + (- (2 * \<mu>) * f' t + \<mu>\<^sup>2))"
                  by (rule integral_cong) (simp add: power2_eq_square algebra_simps)
                also have "\<dots> = integral {a..b} (\<lambda>t. (f' t)\<^sup>2) +
                  integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t + \<mu>\<^sup>2)"
                  by (rule integral_add[OF f'2I integrable_add[OF int1 int2]])
                also have "integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t + \<mu>\<^sup>2) =
                  integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t) + integral {a..b} (\<lambda>t. \<mu>\<^sup>2)"
                  by (rule integral_add[OF int1 int2])
                also have "integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t) = - (2 * \<mu>) * integral {a..b} f'"
                  by simp
                also have "integral {a..b} (\<lambda>t. \<mu>\<^sup>2) = \<mu>\<^sup>2 * (b - a)"
                  using ab by simp
                finally show ?thesis by linarith
              qed
              also have "- (2 * \<mu>) * integral {a..b} f' + \<mu>\<^sup>2 * (b - a) =
                - (integral {a..b} f')\<^sup>2 / (b - a)"
              proof -
                have D: "b - a > 0" using ab by simp
                define I where "I \<equiv> integral {a..b} f'"
                have "- (2 * \<mu>) * I + \<mu>\<^sup>2 * (b - a) = - 2 * (I / (b - a)) * I + (I / (b - a))\<^sup>2 * (b - a)"
                  unfolding \<mu>_def I_def by simp
                also have "\<dots> = - 2 * I\<^sup>2 / (b - a) + I\<^sup>2 / (b - a)"
                  using D by (simp add: power2_eq_square divide_simps)
                also have "\<dots> = - I\<^sup>2 / (b - a)" by algebra
                finally show ?thesis unfolding I_def .
              qed
              finally have "(integral {a..b} f')\<^sup>2 / (b - a) \<le> integral {a..b} (\<lambda>t. (f' t)\<^sup>2)"
                by linarith
              thus ?thesis using ab by (simp add: pos_divide_le_eq mult.commute)
            qed
              \<comment> \<open>Main proof by cases\<close>
            show ?thesis
            proof (cases "c \<le> x")
              case True
              show ?thesis
              proof (cases "x = c")
                case True then show ?thesis by simp
              next
                case False
                with \<open>c \<le> x\<close> have cx: "c < x" by linarith
                have sub: "{c..x} \<subseteq> {0..2*pi}" using c_in xin \<open>c \<le> x\<close> by auto
                have "f x - f c = integral {c..x} f'"
                  by (rule ftc_sub) (use c_in xin \<open>c \<le> x\<close> in auto)
                hence "(f x - f c)\<^sup>2 = (integral {c..x} f')\<^sup>2" by simp
                also have "\<dots> \<le> (x - c) * integral {c..x} (\<lambda>t. (f' t)\<^sup>2)"
                  by (rule cs_sub[OF sub cx])
                also have "\<dots> = \<bar>x - c\<bar> * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
                  using \<open>c \<le> x\<close> by (simp add: min_absorb1 max_absorb2)
                finally show ?thesis .
              qed
            next
              case False
              hence xc: "x < c" by linarith
              have sub: "{x..c} \<subseteq> {0..2*pi}" using c_in xin xc by auto
              have "f c - f x = integral {x..c} f'"
                by (rule ftc_sub) (use c_in xin xc in auto)
              hence "(f x - f c)\<^sup>2 = (integral {x..c} f')\<^sup>2"
                by (simp add: power2_eq_square algebra_simps)
              also have "\<dots> \<le> (c - x) * integral {x..c} (\<lambda>t. (f' t)\<^sup>2)"
                by (rule cs_sub[OF sub xc])
              also have "\<dots> = \<bar>x - c\<bar> * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
                using xc by (simp add: min_absorb2 max_absorb1)
              finally show ?thesis .
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
                    integrable_on_subinterval le_numeral_extra(3) sub)
              hence "integral {c..x} (\<lambda>t. (f' t)\<^sup>2) = F x - F c"
                unfolding F_def by linarith
              moreover have "0 \<le> integral {c..x} (\<lambda>t. (f' t)\<^sup>2)"
                by (rule integral_nonneg[OF integrable_subinterval_real[OF f'2 sub]])
                  (simp add: zero_le_power2)
              ultimately show ?thesis using True by (simp add: min_def max_def)
            next
              case False
              hence xc: "x \<le> c" by simp
              have sub: "{x..c} \<subseteq> {0..2*pi}" using c_in that xc by auto
              have "integral {0..x} (\<lambda>t. (f' t)\<^sup>2) + integral {x..c} (\<lambda>t. (f' t)\<^sup>2) =
                integral {0..c} (\<lambda>t. (f' t)\<^sup>2)"
                by (metis Henstock_Kurzweil_Integration.integral_combine atLeastAtMost_iff
                    atLeastatMost_subset_iff c_in f'2 integrable_on_subinterval le_numeral_extra(3) that
                    xc)
              hence "integral {x..c} (\<lambda>t. (f' t)\<^sup>2) = F c - F x"
                unfolding F_def by linarith
              moreover have "0 \<le> integral {x..c} (\<lambda>t. (f' t)\<^sup>2)"
                by (rule integral_nonneg[OF integrable_subinterval_real[OF f'2 sub]])
                  (simp add: zero_le_power2)
              ultimately show ?thesis using xc by (simp add: min_def max_def)
            qed
            have "((\<lambda>x. \<bar>F x - F c\<bar>) \<longlongrightarrow> 0) (at c within {0..2*pi})"
              by (metis F_cont LIM_zero_iff c_in continuous_on_def tendsto_rabs_zero)
            thus ?thesis
              by (smt (verit, best) F_eq Lim_cong_within)
          qed
          
          \<comment> \<open>Combine: g(x) = (f(x)-f(c))² * cos(x-c) / sin(x-c) \<rightarrow> 0.\<close>
          \<comment> \<open>Show (x-c)/sin(x-c) \<rightarrow> 1 as x \<rightarrow> c, hence bounded near c.\<close>
          have sinc_ratio_bounded:
            "\<forall>\<^sub>F x in at c within {0..2*pi}. \<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> \<le> 2"
          proof -
            \<comment> \<open>sin(x)/x \<rightarrow> 1 at 0, so (x-c)/sin(x-c) \<rightarrow> 1 at c.\<close>
            have inv_lim: "(\<lambda>x. (x - c) / sin (x - c)) \<midarrow>c\<rightarrow> 1"
              by real_asymp
                \<comment> \<open>Extract: eventually |ratio| < 2.\<close>
            from tendstoD[OF inv_lim, of 1]
            have "\<forall>\<^sub>F x in at c. dist ((x - c) / sin (x - c)) 1 < 1"
              by simp
            hence "\<forall>\<^sub>F x in at c. \<bar>(x - c) / sin (x - c)\<bar> < 2"
              by (elim eventually_mono) (auto simp: dist_real_def abs_if split: if_splits)
            hence "\<forall>\<^sub>F x in at c. \<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> < 2"
              by (elim eventually_mono) (simp add: abs_divide)
            thus ?thesis
              by (metis (no_types, lifting) UNIV_I eventually_at_topological less_imp_le)
          qed

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
                hence ratio_bd: "\<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> \<le> 2" and xin: "x \<in> {0..2*pi}" by auto
                have "\<bar>g x\<bar> = \<bar>(f x - f c)\<^sup>2 * cos (x - c) / sin (x - c)\<bar>"
                  using g_eq2 by simp
                also have "\<dots> = (f x - f c)\<^sup>2 * \<bar>cos (x - c)\<bar> / \<bar>sin (x - c)\<bar>"
                  by (simp add: abs_mult abs_divide)
                also have "\<dots> \<le> (f x - f c)\<^sup>2 * 1 / \<bar>sin (x - c)\<bar>"
                  by (meson abs_cos_le_one abs_ge_zero divide_right_mono
                      ordered_comm_semiring_class.comm_mult_left_mono zero_le_power2)
                also have "\<dots> = (f x - f c)\<^sup>2 / \<bar>sin (x - c)\<bar>" by simp
                also have "\<dots> \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
                proof -
                  have sub: "{min c x..max c x} \<subseteq> {0..2*pi}" using c_in xin by auto
                  have f'2I: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {min c x..max c x}"
                    by (rule integrable_subinterval_real[OF f'2 sub])
                  show ?thesis
                  proof (cases "sin (x - c) = 0")
                    case True
                    then show ?thesis
                      using integral_nonneg[OF f'2I] by simp
                  next
                    case False
                    hence sinpos: "\<bar>sin (x - c)\<bar> > 0" by simp
                    define I where "I = integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
                    have Ige: "I \<ge> 0"
                      unfolding I_def by (rule integral_nonneg[OF f'2I]) (simp add: zero_le_power2)
                    have "(f x - f c)\<^sup>2 \<le> \<bar>x - c\<bar> * I"
                      unfolding I_def by (rule cs_bound[OF xin])
                    hence "(f x - f c)\<^sup>2 / \<bar>sin (x - c)\<bar> \<le> \<bar>x - c\<bar> * I / \<bar>sin (x - c)\<bar>"
                      by (intro divide_right_mono) simp_all
                    also have "\<dots> = (\<bar>x - c\<bar> / \<bar>sin (x - c)\<bar>) * I"
                      by (simp add: field_simps)
                    also have "\<dots> \<le> 2 * I"
                      by (rule mult_right_mono[OF ratio_bd Ige])
                    finally show ?thesis unfolding I_def .
                  qed
                qed
                finally show "norm (g x) \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)" by simp
              qed
            qed
              \<comment> \<open>2 * \<integral>(f')² \<rightarrow> 0.\<close>
            show "((\<lambda>x. 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)) \<longlongrightarrow> 0) (at c within {0..2*pi})"
              using tendsto_mult_right_zero[OF f'2_int_tends_0] by simp
          qed
        qed
      qed
    qed
  qed


  text \<open>The integral over mainly trouble-free intervals:
    we only need \<open>sin(x - a) \<noteq> 0\<close> on the open interior, allowing zeros at the endpoints.\<close>
  have mainly_trouble_free:
    "(g' has_integral g d - g c) {c..d}"
    if "c \<le> d" and "{c..d} \<subseteq> {0..2*pi}"
      and "\<And>x. x \<in> {c<..<d} \<Longrightarrow> sin (x - a) \<noteq> 0"
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
        case False
        then show ?thesis by (simp add: not_le integrable_on_empty)
      next
        case True
        then have uv_mem: "u \<in> {c<..<d}" "v \<in> {c<..<d}"
          using uv_sub by auto
        have uv_cd: "{u..v} \<subseteq> {c..d}"
          using uv_sub greaterThanLessThan_subseteq_atLeastAtMost_iff by blast
        then have uv_2pi: "{u..v} \<subseteq> {0..2*pi}" using cd_sub by auto
        have sin_nz': "sin (x - a) \<noteq> 0" if "x \<in> {u..v}" for x
        proof -
          have "x \<in> {c<..<d}" using that uv_sub by blast
          then show ?thesis using sin_nz by auto
        qed
        show ?thesis
          using has_integral_integrable[OF trouble_free[OF True uv_2pi sin_nz']] by auto
      qed
      have g'_int: "g' integrable_on {c'..d'}" if "{c'..d'} \<subseteq> {c<..<d}" for c' d'
        using \<open>{c'..d'} \<subseteq> {c<..<d}\<close> g'_int_sub by blast
      have abs_g_cont: \<open>continuous_on {0..2 * pi} (\<lambda>x. \<bar>g x\<bar>)\<close>
        by (intro continuous_intros g_cont)
      obtain h where h_abs: "h absolutely_integrable_on {c..d}" 
                 and h_bounded: "(\<forall>x\<in>{c..d}. g' x \<le> h x) \<or> (\<forall>x\<in>{c..d}. h x \<le> g' x)"
      proof -
        have abs: \<open>(\<lambda>x. (f' x)\<^sup>2) absolutely_integrable_on {c..d}\<close>
          using absolutely_integrable_on_subinterval[OF f'2_abs cd_sub] .
        have bnd: \<open>\<forall>x\<in>{c..d}. g' x \<le> (f' x)\<^sup>2\<close>
        proof (intro ballI)
          fix x assume \<open>x \<in> {c..d}\<close>
          show \<open>g' x \<le> (f' x)\<^sup>2\<close>
            unfolding g'_def by simp
        qed
        show ?thesis
          using abs bnd by (intro that[of \<open>\<lambda>x. (f' x)\<^sup>2\<close>]) auto
      qed
      show ?thesis
      proof (intro g'_int absolutely_integrable_improper [of c d , unfolded box_real])
        obtain w where "w\<in>{0..2 * pi}" "\<forall>y\<in>{0..2 * pi}. \<bar>g y\<bar> \<le> \<bar>g w\<bar>"
          using continuous_attains_sup [of \<open>{0..2*pi}\<close> \<open>\<lambda>x. \<bar>g x\<bar>\<close>]
          by (metis add_increasing atLeastatMost_empty_iff compact_Icc abs_g_cont mult_2
              pi_ge_zero)        
        show "bounded {integral {c'..d'} g' |c' d'. {c'..d'} \<subseteq> {c<..<d}}"
        proof (rule boundedI[where B = "2 * \<bar>g w\<bar>"])
          fix x assume "x \<in> {integral {c'..d'} g' |c' d'. {c'..d'} \<subseteq> {c<..<d}}"
          then obtain c' d' where cd': "{c'..d'} \<subseteq> {c<..<d}" and xeq: "x = integral {c'..d'} g'"
            by auto
          show "norm x \<le> 2 * \<bar>g w\<bar>"
          proof (cases "c' \<le> d'")
            case False
            then have "{c'..d'} = {}" by auto
            then show ?thesis by (simp add: xeq)
          next
            case True
            then have mem: "c' \<in> {c<..<d}" "d' \<in> {c<..<d}" using cd' by auto
            have sub_2pi: "{c'..d'} \<subseteq> {0..2*pi}"
              using cd' cd_sub greaterThanLessThan_subseteq_atLeastAtMost_iff by blast
            have sin_nz': "sin (t - a) \<noteq> 0" if "t \<in> {c'..d'}" for t
              using that cd' sin_nz by (meson greaterThanLessThan_subseteq_atLeastAtMost_iff subsetD)
            have hi: "(g' has_integral g d' - g c') {c'..d'}"
              using trouble_free[OF True sub_2pi sin_nz'] .
            then have "integral {c'..d'} g' = g d' - g c'"
              using has_integral_integrable_integral g'_int_sub[OF cd'] by auto
            then have "\<bar>x\<bar> = \<bar>g d' - g c'\<bar>" by (simp add: xeq)
            also have "\<dots> \<le> \<bar>g d'\<bar> + \<bar>g c'\<bar>" by linarith
            also have "\<dots> \<le> \<bar>g w\<bar> + \<bar>g w\<bar>"
            proof -
              have "c' \<in> {0..2*pi}" "d' \<in> {0..2*pi}"
                using mem cd_sub greaterThanLessThan_subseteq_atLeastAtMost_iff by blast+
              then show ?thesis
                using \<open>\<forall>y\<in>{0..2 * pi}. \<bar>g y\<bar> \<le> \<bar>g w\<bar>\<close> by (meson add_mono)
            qed
            also have "\<dots> = 2 * \<bar>g w\<bar>" by algebra
            finally show ?thesis by (simp add: xeq)
          qed
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
        case False
        then have "c = d" using cd_le by linarith
        then show ?thesis by simp
      next
        case True
        \<comment> \<open>Pick sequences c_n \<rightarrow> c and d_n \<rightarrow> d from inside (c,d)\<close>
        define c_n where "c_n \<equiv> \<lambda>n. c + (d - c) / (real n + 2)"
        define d_n where "d_n \<equiv> \<lambda>n. d - (d - c) / (real n + 2)"
        have pos: "0 < (d - c) / (real n + 2)" for n
          using True by auto
        have lt_dc: "(d - c) / (real n + 2) < d - c" for n
        proof -
          have "real n + 2 > 1" by auto
          then show ?thesis using True by (simp add: divide_less_eq)
        qed
        have c_n_in: "c_n n \<in> {c<..<d}" for n
          using pos[of n] lt_dc[of n] unfolding c_n_def by auto
        have d_n_in: "d_n n \<in> {c<..<d}" for n
          using pos[of n] lt_dc[of n] unfolding d_n_def by auto
        have c_n_le_d_n: "c_n n \<le> d_n n" for n
        proof -
          have "0 \<le> real n" by simp
          then have "c * real n \<le> d * real n"
            using True by (intro mult_right_mono) linarith+
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
        \<comment> \<open>The integrals converge to integral {c..d} g'\<close>
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
              by (rule integrable_subinterval_real[OF g'_int])
                 (use d_n_cd[of n] cd_le in auto)
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
        \<comment> \<open>The RHS converges to g d - g c by continuity\<close>
        moreover have "(\<lambda>n. g (d_n n) - g (c_n n)) \<longlonglongrightarrow> g d - g c"
        proof (intro tendsto_diff)
          have d_n_cd: "d_n n \<in> {c..d}" for n
            using d_n_in[of n] by (meson atLeastAtMost_iff greaterThanLessThan_iff less_imp_le)
          have c_n_cd: "c_n n \<in> {c..d}" for n
            using c_n_in[of n] by (meson atLeastAtMost_iff greaterThanLessThan_iff less_imp_le)
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
  show "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
  proof -
    \<comment> \<open>Zeros of sin(x - a) in [0, 2\<pi>] are exactly at x = a and x = a + \<pi>.\<close>
    have sin_nz_1: "sin (x - a) \<noteq> 0" if "a + pi < x" "x < 2*pi" for x
      by (smt (verit) \<open>0 \<le> a\<close> sin_lt_zero that)
    have sin_nz_2: "sin (x - a) \<noteq> 0" if "a < x" "x < a + pi" for x
      by (smt (verit, ccfv_threshold) sin_gt_zero that)
    have sin_nz_3: "sin (x - a) \<noteq> 0" if "0 < x" "x < a" for x
    proof -
      have "0 < a - x" "a - x < pi" using that \<open>a < pi\<close> by auto
      hence "0 < sin (a - x)" by (rule sin_gt_zero)
      moreover have "sin (x - a) = - sin (a - x)"
        by (metis sin_minus minus_diff_eq)
      ultimately show ?thesis by simp
    qed
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
    have ffa_2fa_int: "(\<lambda>x. 2 * f a * f x) integrable_on {0..2*pi}"
    proof -
      have "(\<lambda>x. (2 * f a) *\<^sub>R f x) integrable_on {0..2*pi}"
        by (rule integrable_cmul[OF f_int])
      thus ?thesis by simp
    qed
    have ffa_expand: "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) =
      integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) - 2 * f a * integral {0..2*pi} f +
      (f a)\<^sup>2 * (2*pi)"
    proof -
      have eq: "(f x - f a)\<^sup>2 = (f x)\<^sup>2 - 2 * f a * f x + (f a)\<^sup>2" for x
        by (simp add: power2_eq_square algebra_simps)
      have fx2_int: "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
        by (intro integrable_continuous_interval continuous_intros contf)
      have const_int: "(\<lambda>x::real. (f a)\<^sup>2) integrable_on {0..2*pi}"
        by blast
      \<comment> \<open>Split: (f−fa)² = f² − 2\<sqdot>fa\<sqdot>f + fa²\<close>
      have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x + (f a)\<^sup>2)"
        by (rule integral_cong) (simp add: eq)
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
    have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) =
      integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) + (f a)\<^sup>2 * (2*pi)"
      using ffa_expand f_integral_0 by simp
    hence "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) =
      integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) - (f a)\<^sup>2 * (2*pi)"
      by linarith
    moreover have "(f a)\<^sup>2 * (2*pi) \<ge> 0" by (simp add: zero_le_power2)
    ultimately have "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2)"
      by linarith
    thus ?thesis using ineq_ffa by linarith
  qed
  show "\<exists>c a. \<forall>x \<in> {0..2*pi}. f x = c * sin (x - a)"
    if "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
  proof -
    \<comment> \<open>From the equality, all intermediate inequalities are equalities.\<close>
    note eq_hyp = that
    \<comment> \<open>Re-derive key intermediate facts.\<close>
    have ffa_2fa_int: "(\<lambda>x. 2 * f a * f x) integrable_on {0..2*pi}"
    proof -
      have "(\<lambda>x. (2 * f a) *\<^sub>R f x) integrable_on {0..2*pi}"
        by (rule integrable_cmul[OF integrable_continuous_interval[OF contf]])
      thus ?thesis by simp
    qed
    have fx2_int: "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
      by (intro integrable_continuous_interval continuous_intros contf)
    have ffa_int: "(\<lambda>x. (f x - f a)\<^sup>2) integrable_on {0..2*pi}"
      by (intro integrable_continuous_interval continuous_intros contf)
    have ffa_eq: "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) =
      integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) + (f a)\<^sup>2 * (2*pi)"
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
    proof -
      have "0 < a - x" "a - x < pi" using that \<open>a < pi\<close> by auto
      hence "0 < sin (a - x)" by (rule sin_gt_zero)
      moreover have "sin (x - a) = - sin (a - x)"
        by (metis sin_minus minus_diff_eq)
      ultimately show ?thesis by simp
    qed
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
    proof -
      have fa2_nonneg: "(f a)\<^sup>2 * (2*pi) \<ge> 0" by (simp add: zero_le_power2)
      have "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le>
        integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2)"
        using ffa_eq fa2_nonneg by linarith
      hence "(f a)\<^sup>2 * (2*pi) \<le> 0"
        using ineq_ffa eq_hyp ffa_eq by linarith
      hence "(f a)\<^sup>2 * (2*pi) = 0" using fa2_nonneg by linarith
      thus "f a = 0" using pi_gt_zero by (simp add: power2_eq_square)
    qed
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
      moreover have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) =
        integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2)"
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
        have h_const: "f s / sin (s - a) = f t / sin (t - a)"
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
              using compact_continuous_image[OF cont_deriv compact_Icc]
                    compact_imp_bounded by blast
            then obtain B where B: "\<And>x. x \<in> {s'..t'} \<Longrightarrow> \<bar>deriv x\<bar> \<le> B"
              by (meson bounded_real imageI)
            have lipschitz: "\<bar>inverse (sin (x - a)) - inverse (sin (y - a))\<bar> \<le> B * \<bar>x - y\<bar>"
              if hx: "s' \<le> x" "x \<le> t'" and hy: "s' \<le> y" "y \<le> t'"
              for x y
            proof -
              have deriv_at: "((\<lambda>x. inverse (sin (x - a))) has_real_derivative deriv z)
                              (at z within {s'..t'})"
                if hz: "z \<in> {s'..t'}" for z
              proof -
                have snz: "sin (z - a) \<noteq> 0" using sin_nz_st[OF hz] .
                have "((\<lambda>x. sin (x - a)) has_real_derivative cos (z - a))
                       (at z within {s'..t'})"
                  by (intro derivative_eq_intros | simp)+
                then have "((\<lambda>x. inverse (sin (x - a))) has_real_derivative
                            - (cos (z - a) * inverse (sin (z - a) ^ Suc (Suc 0))))
                           (at z within {s'..t'})"
                  using DERIV_inverse_fun snz by blast
                moreover have "- (cos (z - a) * inverse (sin (z - a) ^ Suc (Suc 0)))
                              = deriv z"
                  unfolding deriv_def power2_eq_square
                  by (simp add: field_simps)
                ultimately show ?thesis by simp
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
          proof -
            have "absolutely_continuous_on {s'..t'} (\<lambda>x. f x *\<^sub>R inverse (sin (x - a)))"
              by (rule absolutely_continuous_on_mul[OF ac_f_st ac_inv_sin]) auto
            moreover have "h x = f x *\<^sub>R inverse (sin (x - a))" for x
              unfolding h_def by (simp add: divide_inverse)
            ultimately show ?thesis
              using absolutely_continuous_on_eq by presburger
          qed
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
            proof (rule has_vector_derivative_transform_within)
              show "0 < (1::real)" by simp
              show "t \<in> {0..2*pi}" using t02 .
              fix u assume "u \<in> {0..2*pi}" "dist u t < 1"
              then show "integral {0..u} f' = f u - f 0"
                using f_eq f'hsd by blast
            qed
            then have "(f has_vector_derivative f' t) (at t within {0..2*pi})"
              using has_vector_derivative_diff_const by blast
            then show ?thesis
              by (rule has_vector_derivative_within_subset) (use st'_sub2 in auto)
          qed
          \<comment> \<open>Derivative of h = f/sin via quotient rule\<close>
          have hderiv: "(h has_vector_derivative
              (f' t * sin (t - a) - f t * cos (t - a)) / (sin (t - a))\<^sup>2)
              (at t within {s'..t'})"
            if "t \<in> {s'..t'} - k" for t
          proof -
            have snz: "sin (t - a) \<noteq> 0"
              using sin_nz_st that by auto
            have fd: "(f has_real_derivative f' t) (at t within {s'..t'})"
              using fderiv that
              by (simp add: has_real_derivative_iff_has_vector_derivative)
            have sd: "((\<lambda>x. sin (x - a)) has_real_derivative cos (t - a))
                      (at t within {s'..t'})"
              by (auto intro!: derivative_eq_intros)
            have "((\<lambda>x. f x / sin (x - a)) has_real_derivative
                   (f' t * sin (t - a) - f t * cos (t - a)) / (sin (t - a))\<^sup>2)
                  (at t within {s'..t'})"
              using DERIV_quotient[OF fd sd snz]
              by (simp add: power2_eq_square algebra_simps)
            then show ?thesis unfolding h_def
              by (simp add: has_real_derivative_iff_has_vector_derivative)
          qed
          \<comment> \<open>The derivative of h equals rest/sin\<close>
          have hderiv_eq: "(f' t * sin (t - a) - f t * cos (t - a)) / (sin (t - a))\<^sup>2
                          = rest t / sin (t - a)"
            if "t \<in> {s'..t'}" for t
          proof -
            have snz: "sin (t - a) \<noteq> 0" using sin_nz_st that by auto
            show ?thesis unfolding rest_def fa0
              by (simp add: power2_eq_square field_simps snz
                            Multiseries_Expansion.tan_conv_sin_cos)
          qed
          have hderiv': "(h has_vector_derivative rest t / sin (t - a))
              (at t within {s'..t'})"
            if "t \<in> {s'..t'} - k" for t
            using hderiv[OF that] hderiv_eq[of t] that by auto
          \<comment> \<open>rest = 0 a.e. on {u..v}, so get a negligible set N\<close>
          obtain N where negN: "negligible N"
            and restN: "\<And>x. x \<in> {u..v} - N \<Longrightarrow> rest x = 0"
          proof -
            from rest_ae_zero[unfolded eventually_ae_filter[of _ "lebesgue_on {u..v}"]]
            obtain N0 where N0: "N0 \<in> null_sets (lebesgue_on {u..v})"
              and sub: "{x \<in> space (lebesgue_on {u..v}). rest x \<noteq> 0} \<subseteq> N0"
              by auto
            have "N0 \<in> null_sets lebesgue"
              using null_sets_restrict_space[of "{u..v}" lebesgue] N0 by auto
            then have "negligible N0"
              using negligible_iff_null_sets by auto
            moreover have "rest x = 0" if "x \<in> {u..v} - N0" for x
              using sub that by (auto simp: space_lebesgue_on)
            ultimately show ?thesis using that by blast
          qed
          \<comment> \<open>h has derivative 0 a.e. on {s'..t'}\<close>
          have hderiv_zero: "(h has_vector_derivative 0) (at t within {s'..t'})"
            if "t \<in> {s'..t'} - (k \<union> N)" for t
          proof -
            have "t \<in> {s'..t'} - k" using that by auto
            then have "(h has_vector_derivative rest t / sin (t - a))
                       (at t within {s'..t'})"
              using hderiv' by auto
            moreover have "rest t = 0"
              using restN[of t] that st'_sub by auto
            ultimately show ?thesis by simp
          qed
          have neg_kN: "negligible (k \<union> N)"
            using negk negN by (rule negligible_Un)
          \<comment> \<open>By FTC for AC: h(t') - h(s') = \<integral> 0 = 0\<close>
          have "h t' - h s' = integral {s'..t'} (\<lambda>x. 0::real)"
            using fundamental_theorem_of_calculus_absolutely_continuous
              [OF neg_kN _ ac_h hderiv_zero]
            using st' by auto
          then have "h s' = h t'" by simp
          \<comment> \<open>Translate back to f/sin\<close>
          then show ?thesis
            unfolding h_def s'_def t'_def
            by (auto split: if_splits)

        qed
        \<comment> \<open>Conclude: pick any x₀ \<in> (u,v) and set c = f(x₀)/sin(x₀-a).\<close>
        obtain x0 where x0_in: "x0 \<in> {u<..<v}"
          using huv(2) dense
          by (metis greaterThanLessThan_iff)
        define c where "c = f x0 / sin (x0 - a)"
        have "f x = c * sin (x - a)" if "x \<in> {u<..<v}" for x
        proof -
          have "f x / sin (x - a) = f x0 / sin (x0 - a)"
            using h_const[OF that x0_in] .
          hence "f x / sin (x - a) = c" unfolding c_def .
          thus ?thesis using hsin[OF that]
            by (simp add: field_simps)
        qed
        thus ?thesis by auto
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
        proof -
          have "integral {0..pi} f = integral {0..pi} (\<lambda>x. c1 * sin (x - a))"
            by (rule integral_cong) (use c1 in auto)
          also have "\<dots> = c1 * (cos (0 - a) - cos (pi - a))"
            by (rule csin_integral) (use pi_ge_zero in auto)
          finally show ?thesis .
        qed
        have eq2: "integral {pi..2*pi} f = c2 * (cos (pi - a) - cos (2*pi - a))"
        proof -
          have "integral {pi..2*pi} f = integral {pi..2*pi} (\<lambda>x. c2 * sin (x - a))"
            by (rule integral_cong) (use c2 in auto)
          also have "\<dots> = c2 * (cos (pi - a) - cos (2*pi - a))"
            by (rule csin_integral) (use pi_ge_zero in auto)
          finally show ?thesis .
        qed
        have int_split: "integral {0..2*pi} f = integral {0..pi} f + integral {pi..2*pi} f"
        proof -
          have f_int: "f integrable_on {0..2*pi}"
            using f0 has_integral_integrable by blast
          show ?thesis
            using Henstock_Kurzweil_Integration.integral_combine[OF pi_ge_zero _ f_int]
              pi_ge_zero by linarith
        qed
        have "integral {0..2*pi} f = 0"
          using f0 by (simp add: has_integral_integrable_integral)
        hence "c1 * (cos (0 - a) - cos (pi - a)) + c2 * (cos (pi - a) - cos (2*pi - a)) = 0"
          using int_split eq1 eq2 by linarith
        hence c_eq: "c1 = c2" using True
          by (simp add: cos_two_pi cos_pi)
        show "\<exists>c a. \<forall>x\<in>{0..2 * pi}. f x = c * sin (x - a)"
        proof (intro exI ballI)
          fix x assume "x \<in> {0..2*pi}"
          show "f x = c1 * sin (x - a)"
          proof (cases "x \<le> pi")
            case True
            then show ?thesis using c1 \<open>x \<in> {0..2*pi}\<close> by auto
          next
            case False
            then show ?thesis using c2 c_eq \<open>x \<in> {0..2*pi}\<close> by auto
          qed
        qed
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
        have c13_eq: "c1 = c3"
        proof -
          have "f 0 = f (2*pi)" using feq by simp
          hence "c1 * sin (0 - a) = c3 * sin (2*pi - a)"
            using f0_eq f2pi_eq by simp
          hence "c1 * (- sin a) = c3 * (- sin a)"
            by (simp add: sin_minus sin_2pi_minus)
          thus ?thesis using sin_a_nz by auto
        qed
        \<comment> \<open>Compute integrals on each interval\<close>
        have eq1: "integral {0..a} f = c1 * (cos (0 - a) - cos (a - a))"
        proof -
          have "integral {0..a} f = integral {0..a} (\<lambda>x. c1 * sin (x - a))"
            by (rule integral_cong) (use c1 in auto)
          also have "\<dots> = c1 * (cos (0 - a) - cos (a - a))"
            by (rule csin_integral) (use a_pos in auto)
          finally show ?thesis .
        qed
        have eq2: "integral {a..a+pi} f = c2 * (cos (a - a) - cos ((a+pi) - a))"
        proof -
          have "integral {a..a+pi} f = integral {a..a+pi} (\<lambda>x. c2 * sin (x - a))"
            by (rule integral_cong) (use c2 in auto)
          also have "\<dots> = c2 * (cos (a - a) - cos ((a+pi) - a))"
            by (rule csin_integral) (use pi_ge_zero in auto)
          finally show ?thesis .
        qed
        have eq3: "integral {a+pi..2*pi} f = c3 * (cos ((a+pi) - a) - cos (2*pi - a))"
        proof -
          have "integral {a+pi..2*pi} f = integral {a+pi..2*pi} (\<lambda>x. c3 * sin (x - a))"
            by (rule integral_cong) (use c3 in auto)
          also have "\<dots> = c3 * (cos ((a+pi) - a) - cos (2*pi - a))"
            by (rule csin_integral) (use \<open>a < pi\<close> in linarith)
          finally show ?thesis .
        qed
        \<comment> \<open>Split the integral into three parts\<close>
        have f_int: "f integrable_on {0..2*pi}"
          using f0 has_integral_integrable by blast
        have a_le: "a \<le> a + pi" using pi_gt_zero by linarith
        have api_le: "a + pi \<le> 2 * pi" using \<open>a < pi\<close> by linarith
        have a_le_2pi: "a \<le> 2 * pi" using a_pos \<open>a < pi\<close> by linarith
        have int_split: "integral {0..2*pi} f =
          integral {0..a} f + integral {a..a+pi} f + integral {a+pi..2*pi} f"
        proof -
          have api_ge: "0 \<le> a + pi" using a_pos pi_gt_zero by linarith
          have s2: "integral {0..2*pi} f = integral {0..a+pi} f + integral {a+pi..2*pi} f"
            using Henstock_Kurzweil_Integration.integral_combine
              [OF api_ge api_le f_int] by auto
          have f_int_api: "f integrable_on {0..a+pi}"
            using integrable_subinterval_real[OF f_int] a_pos api_le by auto
          have s1: "integral {0..a+pi} f = integral {0..a} f + integral {a..a+pi} f"
            using Henstock_Kurzweil_Integration.integral_combine
              [OF \<open>0 \<le> a\<close> a_le f_int_api] by auto
          show ?thesis using s1 s2 by linarith
        qed
        \<comment> \<open>Use \<integral>f = 0 to show c1 = c2\<close>
        have "integral {0..2*pi} f = 0"
          using f0 by (simp add: has_integral_integrable_integral)
        hence sum_eq: "c1 * (cos (0 - a) - cos (a - a)) +
          c2 * (cos (a - a) - cos ((a+pi) - a)) +
          c3 * (cos ((a+pi) - a) - cos (2*pi - a)) = 0"
          using int_split eq1 eq2 eq3 by linarith
        \<comment> \<open>Simplify: cos(0-a) = cos(a), cos(a-a) = 1, cos(pi) = -1, cos(2\<pi>-a) = cos(a)\<close>
        have "c1 * (cos a - 1) + c2 * (1 - (-1)) + c3 * ((-1) - cos a) = 0"
          using sum_eq by (simp add: cos_diff cos_two_pi cos_pi)
        hence "c1 * (cos a - 1) + 2 * c2 + c3 * (- 1 - cos a) = 0"
          by (simp add: algebra_simps)
        hence "c1 * (cos a - 1) + 2 * c2 + c1 * (- 1 - cos a) = 0"
          using c13_eq by simp
        hence "- 2 * c1 + 2 * c2 = 0"
          by (simp add: algebra_simps)
        hence c12_eq: "c1 = c2" by linarith
        \<comment> \<open>Now show f x = c1 * sin (x - a) for all x \<in> {0..2\<pi>}\<close>
        show "\<exists>c a. \<forall>x\<in>{0..2 * pi}. f x = c * sin (x - a)"
        proof (intro exI ballI)
          fix x assume hx: "x \<in> {0..2*pi}"
          show "f x = c1 * sin (x - a)"
          proof (cases "x \<le> a")
            case True
            then show ?thesis using c1 hx by auto
          next
            case False
            then show ?thesis
            proof (cases "x \<le> a + pi")
              case True
              then show ?thesis using c2 c12_eq hx \<open>\<not> x \<le> a\<close> by auto
            next
              case False
              then show ?thesis using c3 c13_eq c12_eq hx by auto
            qed
          qed
        qed
      qed
    qed
  qed
qed

theorem scaled_Wirtinger_inequality:
  fixes f f' :: "real \<Rightarrow> real"
  assumes "\<And>x. x \<in> {0..1} \<Longrightarrow>
    (f' has_integral (f x - f 0)) {0..x}"
    and "f 1 = f 0"
    and "(f has_integral 0) {0..1}"
    and "(\<lambda>x. (f' x)\<^sup>2) integrable_on {0..1}"
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
  text \<open>Precondition 1: g' has_integral (g x - g 0) on {0..x}\<close>
  have prec1: "\<And>x. x \<in> {0..2*pi} \<Longrightarrow> (g' has_integral (g x - g 0)) {0..x}"
  proof -
    fix x :: real assume x: "x \<in> {0..2*pi}"
    have y_mem: "x / (2*pi) \<in> {0..1}" using x twopi_pos by (auto simp: field_simps)
    have step1: "(f' has_integral (f (x/(2*pi)) - f 0)) {0..x/(2*pi)}"
      using assms(1)[OF y_mem] by simp
    have step2: "((\<lambda>s. f' (1/(2*pi) * s)) has_integral (2*pi) *\<^sub>R (f (x/(2*pi)) - f 0))
                 ((\<lambda>s. s / (1/(2*pi))) ` {0..x/(2*pi)})"
      using has_integral_stretch_real[OF step1 inv_twopi_nz] inv_twopi_pos by simp
    have img_sub: "(\<lambda>s. s / (1/(2*pi))) ` {0..x/(2*pi)} = {0..x}"
      using image_divide_atLeastAtMost[OF inv_twopi_pos, of 0 "x/(2*pi)"]
      using twopi_pos by (simp add: field_simps)
    have step3: "((\<lambda>s. f' (s/(2*pi))) has_integral (2*pi) * (f (x/(2*pi)) - f 0)) {0..x}"
      using step2 img_sub by (simp add: field_simps)
    have step4: "((\<lambda>s. 1/(2*pi) * f' (s/(2*pi))) has_integral 1/(2*pi) * ((2*pi) * (f (x/(2*pi)) - f 0))) {0..x}"
      using has_integral_mult_right[OF step3, of "1/(2*pi)"] by simp
    have val: "1/(2*pi) * ((2*pi) * (f (x/(2*pi)) - f 0)) = f (x/(2*pi)) - f 0"
      using twopi_nz by simp
    then show "(g' has_integral (g x - g 0)) {0..x}"
      using step4 unfolding g'_def g_def val by (simp add: field_simps)
  qed
  text \<open>Precondition 2: g(2*pi) = g(0)\<close>
  have prec2: "g (2*pi) = g 0"
    unfolding g_def using assms(2) by simp
  text \<open>Precondition 3: (g has_integral 0) on {0..2*pi}\<close>
  have prec3: "(g has_integral 0) {0..2*pi}"
  proof -
    have "(f has_integral \<bar>1/(2*pi)\<bar> *\<^sub>R 0) {0..1}"
      using assms(3) by simp
    then have "((\<lambda>x. f (1/(2*pi) * x)) has_integral 0) ((\<lambda>x. x / (1/(2*pi))) ` {0..1})"
      using has_integral_stretch_real_iff[OF inv_twopi_nz, of f 0 0 1] by simp
    then show ?thesis
      unfolding g_def using img by (simp add: field_simps)
  qed
  text \<open>Precondition 4: (\<lambda>x. (g' x)²) integrable_on {0..2*pi}\<close>
  have prec4: "(\<lambda>x. (g' x)\<^sup>2) integrable_on {0..2*pi}"
  proof -
    have "(\<lambda>x. (f' x)\<^sup>2) integrable_on {0..1}" by (rule assms(4))
    then have "(\<lambda>x. (f' (1/(2*pi) * x))\<^sup>2) integrable_on ((\<lambda>x. x / (1/(2*pi))) ` {0..1})"
      using integrable_stretch_real[OF _ inv_twopi_nz, of "\<lambda>x. (f' x)\<^sup>2" 0 1] by simp
    then have int: "(\<lambda>x. (f' (x/(2*pi)))\<^sup>2) integrable_on {0..2*pi}"
      using img by (simp add: field_simps)
    show ?thesis
      unfolding g'_def power_mult_distrib
      using integrable_on_cmult_left[OF int, of "(1/(2*pi))\<^sup>2"]
      by (simp add: power_mult_distrib algebra_simps)
  qed
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
  proof -
    from W1 have "(\<lambda>x. (f (1/(2*pi) * x))\<^sup>2) integrable_on {0..2*pi}"
      by (simp add: g_unfold)
    then have "(\<lambda>x. (f (1/(2*pi) * x))\<^sup>2) integrable_on ((\<lambda>x. x / (1/(2*pi))) ` {0..1})"
      using img by simp
    then show ?thesis
      using integrable_stretch_real_iff[OF inv_twopi_nz, of "\<lambda>x. (f x)\<^sup>2" 0 1] by simp
  qed
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
    have rhs_val: "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) 
                 = 2*pi * ((1/(2*pi))\<^sup>2 * integral {0..1} (\<lambda>x. (f' x)\<^sup>2))"
    proof -
      have "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) 
          = integral ((\<lambda>x. x / (1/(2*pi))) ` {0..1}) (\<lambda>x. (g' x)\<^sup>2)"
        using img by simp
      also have "\<dots> = integral ((\<lambda>x. x / (1/(2*pi))) ` {0..1}) (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' (1/(2*pi) * x))\<^sup>2)"
        by (simp add: g'_unfold)
      also have "\<dots> = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2)"
        using rhs_stretch by simp
      also have "\<dots> = 2*pi * ((1/(2*pi))\<^sup>2 * integral {0..1} (\<lambda>x. (f' x)\<^sup>2))"
        using inv_twopi_pos factor_out by simp
      finally show ?thesis .
    qed
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
    have lhs: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = 2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
    proof -
      have "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2)
          = integral ((\<lambda>x. x / (1/(2*pi))) ` {0..1}) (\<lambda>x. (f (1/(2*pi) * x))\<^sup>2)"
        using img by (simp add: g_unfold)
      also have "\<dots> = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
        using integral_stretch_real[OF inv_twopi_nz, of 0 1 "\<lambda>x. (f x)\<^sup>2"] by simp
      also have "\<dots> = 2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
        using inv_twopi_pos by simp
      finally show ?thesis .
    qed
    have rhs: "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) 
             = (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    proof -
      have "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) 
          = integral ((\<lambda>x. x / (1/(2*pi))) ` {0..1}) (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' (1/(2*pi) * x))\<^sup>2)"
        using img by (simp add: g'_unfold)
      also have "\<dots> = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2)"
        using integral_stretch_real[OF inv_twopi_nz, of 0 1 "\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2"] by simp
      also have "\<dots> = 2*pi * ((1/(2*pi))\<^sup>2 * integral {0..1} (\<lambda>x. (f' x)\<^sup>2))"
        using inv_twopi_pos by (simp add: integral_mult_right)
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
    have "\<forall>x \<in> {0..1}. f x = c * sin (2*pi*x - a)"
    proof
      fix x :: real assume xmem: "x \<in> {0..1}"
      then have "2*pi*x \<in> {0..2*pi}" using twopi_pos by (auto simp: field_simps)
      from ca[rule_format, OF this]
      show "f x = c * sin (2*pi*x - a)"
        unfolding g_def using twopi_nz by (simp add: field_simps)
    qed
    then show "\<exists>c a. \<forall>x \<in> {0..1}. f x = c * sin (2*pi*x - a)" by auto
  qed
qed

text \<open>Part 2: a very special case of Green's theorem for a convex area\<close>

text \<open>Area under/above an arc, and the signed area formula for a convex closed curve.\<close>

lemma area_below_arclet:
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
  assumes "u \<le> v"
    and Re_g_le: "Re (g u) \<le> Re (g v)"
    and acont_g: "absolutely_continuous_on {u..v} g"
    and "g ` {u..v} \<subseteq> {z. Im z \<ge> 0}"
    and inj_g: "inj_on g {u..v}"
    and inj_Re: "inj_on Re (g ` {u..v})"
    and "negligible S"
    and "\<And>t. t \<in> {u..v} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
    and "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
proof -
  obtain h where h: "\<And>x. x \<in> {u..v} \<Longrightarrow> h (Re (g x)) = x"
    using inj_Re inj_g inv_into_f_f [of "Re o g" "{u..v}"]
    by (metis comp_inj_on inj_Re inj_g o_def)
  define ax where "ax \<equiv> (\<lambda>t. Re (g t)) ` {u..v}"
  have cont_h: "continuous_on ax h"
    unfolding ax_def
    by (simp add: absolutely_continuous_on_imp_continuous assms(3) continuous_on_Re
        continuous_on_inv h)
  show "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
  proof -
    have cont_g: "continuous_on {u..v} g"
      using assms(3) absolutely_continuous_on_imp_continuous is_interval_cc by blast
    have gp_ai: "g' absolutely_integrable_on {u..v}"
      using absolutely_integrable_absolutely_continuous_derivative[OF assms(3) assms(7)]
        assms(8) has_vector_derivative_at_within by blast
    have Re_gp_ai: "(\<lambda>t. Re (g' t)) absolutely_integrable_on {u..v}"
    proof -
      have "(\<lambda>t. g' t \<bullet> 1) absolutely_integrable_on {u..v}"
        by (rule absolutely_integrable_component[OF gp_ai])
      then show ?thesis by (simp add: complex_inner_1_right)
    qed
    have Im_g_cont: "continuous_on {u..v} (\<lambda>t. Im (g t))"
      by (intro continuous_intros cont_g)
    have Im_g_bdd: "bounded ((\<lambda>t. Im (g t)) ` {u..v})"
      by (intro compact_imp_bounded compact_continuous_image[OF Im_g_cont compact_Icc])
    have Im_g_meas: "(\<lambda>t. Im (g t)) \<in> borel_measurable (lebesgue_on {u..v})"
      using continuous_imp_measurable_on_sets_lebesgue[OF Im_g_cont]
        atLeastAtMost_borel lborelD
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
      case True then show ?thesis unfolding ax_def by auto
    next
      case False
      with \<open>u \<le> v\<close> have uv: "u < v" by auto
      have smono: "strict_mono_on {u..v} (\<lambda>t. Re (g t)) \<or>
                   strict_antimono_on {u..v} (\<lambda>t. Re (g t))"
        using injective_eq_monotone_map[OF is_interval_cc cont_Reg] inj_Reg by auto
      have mono: "strict_mono_on {u..v} (\<lambda>t. Re (g t))"
      proof -
        { assume am: "strict_antimono_on {u..v} (\<lambda>t. Re (g t))"
          have "Re (g v) < Re (g u)"
          proof -
            from am have "antimono_on {u..v} (\<lambda>t. Re (g t))"
              and "inj_on (\<lambda>t. Re (g t)) {u..v}"
              using strict_antimono_iff_antimono by blast+
            then have "mono_on {u..v} (\<lambda>t. - Re (g t))"
              by (simp add: monotone_on_def)
            then have "- Re (g u) \<le> - Re (g v)"
              using mono_onD uv by fastforce
            then show ?thesis
              by (metis False assms(1,2) atLeastAtMost_iff h neg_le_iff_le nle_le)
          qed
          with Re_g_le have False by auto }
        with smono show ?thesis by blast
      qed
      show ?thesis
        using mono by (auto simp: monotone_on_def ax_def less_eq_real_def)
    qed
  next
    show "{Re (g u)..Re (g v)} \<subseteq> ax"
    proof
      fix y assume "y \<in> {Re (g u)..Re (g v)}"
      then have y: "Re (g u) \<le> y" "y \<le> Re (g v)" by auto
      obtain t where t: "t \<in> {u..v}" "g t \<bullet> 1 = y"
        using ivt_increasing_component_on_1[OF \<open>u \<le> v\<close> cont_g, of 1 y] y
        by (auto simp: complex_inner_1_right)
      then have "Re (g t) = y" by (simp add: complex_inner_1_right)
      with t(1) show "y \<in> ax"
        unfolding ax_def by force
    qed
  qed
  show "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
  proof -
    define f where "f \<equiv> (\<lambda>x. Im (g (h x)))"
    have h_mem: "\<And>x. x \<in> {u..v} \<Longrightarrow> h (Re (g x)) \<in> {u..v}"
      using h by simp
    have h_inv: "\<And>x. x \<in> ax \<Longrightarrow> Re (g (h x)) = x"
    proof -
      fix x assume "x \<in> ax"
      then obtain t where t: "t \<in> {u..v}" "x = Re (g t)"
        unfolding ax_def by auto
      then have "h x = t" using h by simp
      then show "Re (g (h x)) = x" using t by simp
    qed
    have f_gh: "\<And>t. t \<in> {u..v} \<Longrightarrow> f (Re (g t)) = Im (g t)"
      unfolding f_def using h by simp
    have h_range: "h ` ax \<subseteq> {u..v}"
    proof
      fix y assume "y \<in> h ` ax"
      then obtain x where x: "x \<in> ax" "y = h x" by auto
      then obtain t where t: "t \<in> {u..v}" "x = Re (g t)"
        unfolding ax_def by auto
      then have "h x = t" using h by simp
      with x t show "y \<in> {u..v}" by simp
    qed
    have cont_f: "continuous_on ax f"
    proof -
      have "continuous_on ax (g \<circ> h)"
        using continuous_on_compose[OF cont_h continuous_on_subset[OF cont_g h_range]]
        by auto
      then show ?thesis unfolding f_def
        by (intro continuous_intros) (simp add: o_def)
    qed
    have f_nonneg: "\<And>x. x \<in> ax \<Longrightarrow> f x \<ge> 0"
    proof -
      fix x assume "x \<in> ax"
      then obtain t where t: "t \<in> {u..v}" "x = Re (g t)"
        unfolding ax_def by auto
      have "g t \<in> g ` {u..v}" using t(1) by auto
      then have "Im (g t) \<ge> 0" using assms(4) by auto
      then show "f x \<ge> 0" unfolding f_def using h t by simp
    qed
    \<comment> \<open>Monotonicity of Re \<circ> g\<close>
    have mono_Reg: "\<And>x y. x \<in> {u..v} \<Longrightarrow> y \<in> {u..v} \<Longrightarrow> x \<le> y \<Longrightarrow> Re (g x) \<le> Re (g y)"
    proof -
      have smono: "strict_mono_on {u..v} (\<lambda>t. Re (g t)) \<or>
                   strict_antimono_on {u..v} (\<lambda>t. Re (g t))"
        using injective_eq_monotone_map[OF is_interval_cc cont_Reg] inj_Reg by auto
      have mono: "mono_on {u..v} (\<lambda>t. Re (g t))"
      proof (cases "u = v")
        case True then show ?thesis by (simp add: mono_on_def)
      next
        case False
        with \<open>u \<le> v\<close> have "u < v" by auto
        { assume am: "strict_antimono_on {u..v} (\<lambda>t. Re (g t))"
          then have "Re (g v) < Re (g u)"
            unfolding monotone_on_def using \<open>u < v\<close> \<open>u \<le> v\<close> by auto
          with Re_g_le have False by auto }
        with smono have "strict_mono_on {u..v} (\<lambda>t. Re (g t))" by blast
        then show ?thesis
          by (simp add: monotone_on_def less_eq_real_def)
      qed
      fix x y assume "x \<in> {u..v}" "y \<in> {u..v}" "x \<le> y"
      then show "Re (g x) \<le> Re (g y)" using mono by (auto simp: mono_on_def)
    qed
    \<comment> \<open>Absolute continuity of Re \<circ> g\<close>
    have acont_Reg: "absolutely_continuous_on {u..v} (\<lambda>t. Re (g t))"
      using absolutely_continuous_on_compose_linear[OF acont_g bounded_linear_Re[THEN bounded_linear.linear]]
      by (simp add: o_def)
    \<comment> \<open>Derivative of Re \<circ> g\<close>
    have deriv_Reg: "\<And>t. t \<in> {u..v} - S \<Longrightarrow> ((\<lambda>t. Re (g t)) has_vector_derivative Re (g' t)) (at t)"
    proof -
      fix t assume "t \<in> {u..v} - S"
      then have "(g has_vector_derivative g' t) (at t)" using assms(8) by auto
      then show "((\<lambda>t. Re (g t)) has_vector_derivative Re (g' t)) (at t)"
        using bounded_linear_Re[THEN bounded_linear.has_vector_derivative] by auto
    qed
    \<comment> \<open>Apply substitution: \<integral>_{Re(g u)}^{Re(g v)} f = \<integral>_u^v Re(g') * f(Re(g)) = \<integral>_u^v Re(g') * Im(g)\<close>
    have subst: "((\<lambda>t. Re (g' t) * f (Re (g t))) has_integral (integral {Re (g u)..Re (g v)} f)) {u..v}"
      using has_integral_substitution_ac[OF \<open>u \<le> v\<close> Re_g_le acont_Reg assms(7) deriv_Reg _ mono_Reg]
        cont_f ax by auto
    \<comment> \<open>Since f(Re(g t)) = Im(g t), the LHS simplifies\<close>
    have "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) = integral {Re (g u)..Re (g v)} f"
    proof -
      have "((\<lambda>t. Re (g' t) * Im (g t)) has_integral (integral {Re (g u)..Re (g v)} f)) {u..v}"
      proof -
        have eq: "\<And>t. t \<in> {u..v} - {} \<Longrightarrow> Re (g' t) * Im (g t) = Re (g' t) * f (Re (g t))"
          using f_gh by simp
        show ?thesis
          using has_integral_spike[OF negligible_empty eq subst] by auto
      qed
      then show ?thesis by (rule integral_unique)
    qed
    \<comment> \<open>Apply area-under-curve: measure of subgraph = \<integral> f\<close>
    also have "\<dots> = measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
    proof -
      \<comment> \<open>First show the subgraph set equals {z. Re(g u) \<le> Re z \<and> Re z \<le> Re(g v) \<and> 0 \<le> Im z \<and> Im z \<le> f(Re z)}\<close>
      have set_eq: "{z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w} =
                    {z. Re (g u) \<le> Re z \<and> Re z \<le> Re (g v) \<and> 0 \<le> Im z \<and> Im z \<le> f (Re z)}"
      proof (rule antisym; rule subsetI)
        fix z assume "z \<in> {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
        then obtain w t where wt: "t \<in> {u..v}" "w = g t" "Re w = Re z" "0 \<le> Im z" "Im z \<le> Im w"
          by auto
        have "Re z \<in> ax" unfolding ax_def using wt by force
        then have "Re (g u) \<le> Re z" "Re z \<le> Re (g v)" using ax by auto
        moreover have "f (Re z) = Im w"
        proof -
          have "h (Re z) = t"
            by (metis h wt(1,2,3) atLeastAtMost_iff)
          then show ?thesis unfolding f_def using wt by simp
        qed
        ultimately show "z \<in> {z. Re (g u) \<le> Re z \<and> Re z \<le> Re (g v) \<and> 0 \<le> Im z \<and> Im z \<le> f (Re z)}"
          using wt by auto
      next
        fix z assume z: "z \<in> {z. Re (g u) \<le> Re z \<and> Re z \<le> Re (g v) \<and> 0 \<le> Im z \<and> Im z \<le> f (Re z)}"
        then have Rez: "Re z \<in> ax" using ax by auto
        then obtain t where t: "t \<in> {u..v}" "Re (g t) = Re z"
          unfolding ax_def by auto
        let ?w = "g t"
        have "?w \<in> g ` {u..v}" using t by auto
        moreover have "Re ?w = Re z" using t by auto
        moreover have "Im ?w = f (Re z)"
          using f_gh[OF t(1)] t(2) by simp
        ultimately show "z \<in> {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
          using z by auto
      qed
      \<comment> \<open>Then apply area-under-curve (Fubini/Cavalieri)\<close>
      show ?thesis unfolding set_eq
        using has_integral_area_under_curve[OF Re_g_le _ _] cont_f f_nonneg ax
        by (metis (no_types, lifting))
    qed
    finally show ?thesis .
  qed
qed

lemma area_above_arclet:
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
  assumes "u \<le> v"
    and "Re (g v) \<le> Re (g u)"
    and "absolutely_continuous_on {u..v} g"
    and "g ` {u..v} \<subseteq> {z. Im z \<le> 0}"
    and "inj_on g {u..v}"
    and "\<And>x y. x \<in> g ` {u..v} \<Longrightarrow> y \<in> g ` {u..v} \<Longrightarrow> Re x = Re y \<Longrightarrow> x = y"
    and "negligible S"
    and "\<And>t. t \<in> {u..v} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
    and "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
  sorry

theorem Green_area_theorem:
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
    and a b :: "complex"
  assumes "simple_path g" "pathstart g = a" "pathfinish g = a"
    and "b \<in> path_image g" "Re a < Re b" "Im a = Im b"
    and "dist a b = diameter (path_image g)"
    and "convex (inside (path_image g))"
    and "absolutely_continuous_on {0..1} g"
    and "negligible U"
    and "\<And>t. t \<in> {0..1} - U \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {0..1}"
    and "\<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> =
      measure lebesgue (inside (path_image g))"
  sorry

section \<open>Part 3: Isoperimetric theorem for convex curves\<close>

theorem isoperimetric_theorem_convex:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "convex (inside (path_image g))"
    "path_length g = L"
  shows "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
      \<exists>a r. path_image g = sphere a r"
  sorry

section \<open>Part 4: Convexification\<close>

text \<open>The step lemma: replacing an arc that deviates from the convex hull frontier
  with a straight segment shortens the path while preserving the convex hull.\<close>

lemma step_lemma:
  fixes g :: "real \<Rightarrow> complex"
  assumes "simple_path g" "pathfinish g = pathstart g"
    and "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g x) (g y) \<le> L * dist x y"
    and "a < b"
    and "a \<in> {0..1}" "b \<in> {0..1}"
    and "g a \<in> frontier (convex hull (path_image g))"
    and "g b \<in> frontier (convex hull (path_image g))"
    and "g ` {a<..<b} \<inter> frontier (convex hull (path_image g)) = {}"
  shows "\<exists>h. simple_path h \<and>
    pathstart h = pathstart g \<and> pathfinish h = pathstart g \<and>
    (\<forall>x \<in> {0..1}. \<forall>y \<in> {0..1}. dist (h x) (h y) \<le> L * dist x y) \<and>
    path_length h < path_length g \<and>
    convex hull (path_image h) = convex hull (path_image g) \<and>
    (\<forall>x. x \<notin> {a<..<b} \<longrightarrow> h x = g x) \<and>
    h ` {a..b} \<subseteq> frontier (convex hull (path_image g))"
  sorry

theorem isoperimetric_convexification:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
  shows "\<exists>h. rectifiable_path h \<and> simple_path h \<and>
    pathfinish h = pathstart h \<and>
    path_length h \<le> path_length g \<and>
    convex hull (path_image h) = convex hull (path_image g) \<and>
    path_image h = frontier (convex hull (path_image g))"
  sorry

theorem isoperimetric_convexification_strict:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "\<not> convex (inside (path_image g))"
  shows "\<exists>h. rectifiable_path h \<and> simple_path h \<and>
    pathfinish h = pathstart h \<and>
    path_length h \<le> path_length g \<and>
    convex hull (path_image h) = convex hull (path_image g) \<and>
    path_image h = frontier (convex hull (path_image g)) \<and>
    measure lebesgue (inside (path_image g)) < measure lebesgue (inside (path_image h))"
  sorry

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
      using isoperimetric_convexification_strict[OF assms(1-3) False] by blast
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
      using isoperimetric_convexification_strict[OF assms(1-3) False] by blast
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

