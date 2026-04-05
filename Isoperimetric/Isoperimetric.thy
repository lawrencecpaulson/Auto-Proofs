theory Isoperimetric
  imports Arc_Length_Reparametrization "Fourier.Fourier" "Green.Green"
 "HOL-ex.Sketch_and_Explore"  "Isar_Explore"
begin

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

section "Measure Theory"

lemma absolutely_integrable_approximate_continuous_vector:
  fixes f :: \<open>'a::euclidean_space \<Rightarrow> 'b::euclidean_space\<close>
    and S :: \<open>'a set\<close>
  assumes \<open>S \<in> lmeasurable\<close>
    and \<open>f absolutely_integrable_on S\<close>
    and \<open>e > 0\<close>
  obtains g where \<open>g absolutely_integrable_on S\<close> \<open>continuous_on UNIV g\<close>
    \<open>bounded (range g)\<close> 
    \<open>norm (integral S (\<lambda>x. norm (f x - g x))) < e\<close>
proof -
  obtain h where hint: "h absolutely_integrable_on S" 
    and hbo: "bounded (h ` UNIV)" 
    and he2: "norm (integral S (\<lambda>x. norm (f x - h x))) < e/2"
  proof -
    define trunc where "trunc \<equiv> \<lambda>n x. \<Sum>b\<in>Basis. max (- real n) (min (real n) (f x \<bullet> b)) *\<^sub>R b"
    have trunc_abs_int: \<open>trunc n absolutely_integrable_on S\<close> for n
    proof -
      define c where \<open>c = (\<Sum>b\<in>Basis. real n *\<^sub>R b :: 'b)\<close>
      have c_inner[simp]: \<open>c \<bullet> b = real n\<close> if \<open>b \<in> Basis\<close> for b
        unfolding c_def using inner_sum_left_Basis[OF that] by simp
      have mc_inner[simp]: \<open>(- c) \<bullet> b = - real n\<close> if \<open>b \<in> Basis\<close> for b
        by (simp add: that)
      have const_int: \<open>(\<lambda>_::'a. d) absolutely_integrable_on S\<close> for d :: 'b
        using absolutely_integrable_on_const assms(1) by blast
      have min_int: \<open>(\<lambda>x. \<Sum>b\<in>Basis. min (f x \<bullet> b) (c \<bullet> b) *\<^sub>R b)
                     absolutely_integrable_on S\<close>
        by (rule absolutely_integrable_min[OF assms(2) const_int])
      then have min_int': \<open>(\<lambda>x. \<Sum>b\<in>Basis. min (f x \<bullet> b) (real n) *\<^sub>R b)
                            absolutely_integrable_on S\<close>
        by (simp cong: sum.cong)
      have max_int: \<open>(\<lambda>x. \<Sum>b\<in>Basis. max ((- c) \<bullet> b) ((\<Sum>b\<in>Basis. min (f x \<bullet> b) (real n) *\<^sub>R b) \<bullet> b) *\<^sub>R b)
                     absolutely_integrable_on S\<close>
        by (rule absolutely_integrable_max[OF const_int min_int'])
      then show ?thesis
        by (simp add: trunc_def inner_sum_left_Basis max.commute min.commute cong: sum.cong)
    qed
    have conv: \<open>(\<lambda>k. integral S (\<lambda>x. norm (f x - trunc k x))) \<longlonglongrightarrow> 0\<close>
    proof -
      let ?fn = \<open>\<lambda>k x. norm (f x - trunc k x)\<close>
      have \<open>(\<lambda>k. integral S (?fn k)) \<longlonglongrightarrow> integral S (\<lambda>x. 0 :: real)\<close>
      proof (rule dominated_convergence(2))
        show fn_int: \<open>(\<lambda>x. ?fn k x) integrable_on S\<close> for k
        proof -
          have f_int: \<open>f integrable_on S\<close>
            using assms(2) set_lebesgue_integral_eq_integral(1) by blast
          have t_int: \<open>(\<lambda>x. trunc k x) integrable_on S\<close>
            using trunc_abs_int[of k] set_lebesgue_integral_eq_integral(1) by blast
          have diff_int: \<open>(\<lambda>x. f x - trunc k x) integrable_on S\<close>
            using integrable_diff[OF f_int t_int] .
          have f_norm_int: \<open>(\<lambda>x. norm (f x)) integrable_on S\<close>
            using assms(2) absolutely_integrable_on_def by blast
          have t_norm_int: \<open>(\<lambda>x. norm (trunc k x)) integrable_on S\<close>
            using trunc_abs_int[of k] absolutely_integrable_on_def by force
          have bound_int: \<open>(\<lambda>x. norm (f x) + norm (trunc k x)) integrable_on S\<close>
            using integrable_add[OF f_norm_int t_norm_int] .
          have \<open>(\<lambda>x. f x - trunc k x) absolutely_integrable_on S\<close>
            by (rule absolutely_integrable_integrable_bound[OF _ diff_int bound_int])
              (simp add: norm_triangle_ineq4)
          then show ?thesis
            using absolutely_integrable_on_def absolutely_integrable_norm
              set_lebesgue_integral_eq_integral(1) by (metis (no_types, lifting) ext)
        qed
        show dom_int: \<open>(\<lambda>x. 2 * norm (f x)) integrable_on S\<close>
          using assms(2)[unfolded absolutely_integrable_on_def]
          by (auto intro: integrable_on_mult_right)
        show norm_bound: \<open>norm (?fn k x) \<le> 2 * norm (f x)\<close> if \<open>x \<in> S\<close> for k x
        proof -
          have trunc_inner: \<open>trunc k x \<bullet> b = max (- real k) (min (real k) (f x \<bullet> b))\<close>
            if \<open>b \<in> Basis\<close> for b
            using inner_sum_left_Basis[OF that] by (simp add: trunc_def)
          have clip_le: \<open>\<bar>max (- real k) (min (real k) (c::real))\<bar> \<le> \<bar>c\<bar>\<close> for c
            by auto
          have \<open>trunc k x \<bullet> trunc k x \<le> f x \<bullet> f x\<close>
          proof -
            have \<open>trunc k x \<bullet> trunc k x = (\<Sum>b\<in>Basis. (trunc k x \<bullet> b) * (trunc k x \<bullet> b))\<close>
              by (rule euclidean_inner)
            also have \<open>\<dots> = (\<Sum>b\<in>Basis. (max (- real k) (min (real k) (f x \<bullet> b)))^2)\<close>
              by (simp add: trunc_inner power2_eq_square)
            also have \<open>\<dots> \<le> (\<Sum>b\<in>Basis. (f x \<bullet> b)^2)\<close>
              by (rule sum_mono) (use power2_mono[OF clip_le] in auto)
            also have \<open>\<dots> = (\<Sum>b\<in>Basis. (f x \<bullet> b) * (f x \<bullet> b))\<close>
              by (simp add: power2_eq_square)
            also have \<open>\<dots> = f x \<bullet> f x\<close>
              by (rule euclidean_inner[symmetric])
            finally show ?thesis .
          qed
          then have \<open>norm (trunc k x) \<le> norm (f x)\<close>
            by (simp add: norm_eq_sqrt_inner real_sqrt_le_mono)
          then show ?thesis
            by (simp add: norm_triangle_ineq4 [THEN order_trans])
        qed
        show \<open>(\<lambda>k. ?fn k x) \<longlonglongrightarrow> 0\<close> if \<open>x \<in> S\<close> for x
        proof -
          obtain N where N: \<open>real N \<ge> norm (f x)\<close>
            using real_nat_ceiling_ge by blast
          have \<open>?fn k x = 0\<close> if \<open>k \<ge> N\<close> for k
          proof -
            have \<open>real k \<ge> norm (f x)\<close> using N that by linarith
            then obtain \<open>f x \<bullet> b \<le> real k\<close> \<open>- real k \<le> f x \<bullet> b\<close> if \<open>b \<in> Basis\<close> for b
              using norm_bound_Basis_le by fastforce
            then have \<open>trunc k x = f x\<close>
              by (simp add: trunc_def euclidean_eqI)
            then show ?thesis by simp
          qed
          then have \<open>\<forall>\<^sub>F k in sequentially. ?fn k x = 0\<close>
            unfolding eventually_sequentially by blast
          then show ?thesis
            by (simp add: tendsto_eventually)
        qed
      qed
      then show ?thesis by simp
    qed
    then obtain n where n: "norm (integral S (\<lambda>x. norm (f x - trunc n x))) < e/2"
      by (metis (no_types, lifting) LIMSEQ_iff assms(3) half_gt_zero order.refl diff_0_right)
    show ?thesis
    proof 
      show "bounded (range (trunc n))"
      proof (unfold bounded_iff, intro exI allI ballI)
        fix y assume "y \<in> range (trunc n)"
        then obtain x where y: "y = trunc n x" by auto
        have "norm (max (- real n) (min (real n) (f x \<bullet> b)) *\<^sub>R b) \<le> real n" if "b \<in> Basis" for b
          by (simp add: that)
        then have "norm (trunc n x) \<le> real DIM('b) * real n"
          unfolding trunc_def by (rule sum_norm_bound)
        then show "norm y \<le> real DIM('b) * real n"
          by (simp add: y)
      qed
    qed (use n trunc_abs_int in auto)
  qed
  obtain B where "B > 0" and B: "\<And>z. norm (h z) \<le> B"
    by (meson UNIV_I bounded_pos hbo image_eqI)

  obtain k g where neg_k: \<open>negligible k\<close>
    and g_cont: \<open>\<And>n. continuous_on UNIV (g n)\<close>
    and g_bound: \<open>\<And>n x. norm (g n x) \<le> norm (B *\<^sub>R (\<Sum>b\<in>Basis. b :: 'b))\<close>
    and g_conv: \<open>\<And>x. x \<in> S - k \<Longrightarrow> (\<lambda>n. g n x) \<longlonglongrightarrow> h x\<close>
  proof -
    have \<open>h integrable_on S\<close>
      using hint absolutely_integrable_on_def set_lebesgue_integral_eq_integral(1) by blast
    then have \<open>h \<in> borel_measurable (lebesgue_on S)\<close>
      by (rule integrable_imp_measurable)
    then have h_meas: \<open>h measurable_on S\<close>
      using assms
      by (auto simp: measurable_on_iff_borel_measurable lmeasurable_iff_integrable fmeasurable_def)
    then obtain N g where "negligible N"
      and contg: "\<And>n. continuous_on UNIV (g n)"
      and lim: "\<And>x. x \<notin> N \<Longrightarrow> (\<lambda>n. g n x) \<longlonglongrightarrow> (if x \<in> S then h x else 0)"
      by (auto simp: measurable_on_def)
    define j where "j \<equiv> \<lambda>n x. \<Sum>b\<in>Basis. max (-B) (min B (g n x \<bullet> b)) *\<^sub>R b :: 'b"
    show ?thesis
    proof
      show "continuous_on UNIV (j n)" for n
        unfolding j_def by (intro continuous_intros contg)
      fix n x
      show "norm (j n x::'b) \<le> norm (B *\<^sub>R (\<Sum>b\<in>Basis. b :: 'b))"
      proof (rule norm_le_componentwise)
        fix b :: 'b assume b: "b \<in> Basis"
        have "\<bar>max (- B) (min B (g n x \<bullet> b))\<bar> \<le> B"
          using \<open>B > 0\<close> by (auto simp: abs_le_iff)
        moreover have "(\<Sum>i\<in>Basis. max (- B) (min B (g n x \<bullet> i)) *\<^sub>R i) \<bullet> b
                      = max (- B) (min B (g n x \<bullet> b))"
          using inner_sum_left_Basis[OF b] by simp
        moreover have "(B *\<^sub>R (\<Sum>i\<in>Basis. i::'b)) \<bullet> b = B"
          by (simp add: inner_scaleR_left inner_sum_Basis[OF b])
        ultimately show "\<bar>j n x \<bullet> b\<bar> \<le> \<bar>(B *\<^sub>R (\<Sum>b\<in>Basis. b::'b)) \<bullet> b\<bar>"
          using \<open>B > 0\<close> by (simp add: j_def)
      qed
    next
      fix x :: 'a
      assume xS: "x \<in> S - N"
      show "(\<lambda>n. j n x) \<longlonglongrightarrow> h x"
      proof -
        define clamp where "clamp \<equiv> \<lambda>v::'b. \<Sum>b\<in>Basis. max (-B) (min B (v \<bullet> b)) *\<^sub>R b"
        have j_eq: "j n x = clamp (g n x)" for n
          by (simp add: j_def clamp_def)
        have clamp_cont: "continuous_on UNIV clamp"
          unfolding clamp_def by (intro continuous_intros)
        have clamp_h: "clamp (h x) = h x"
        proof -
          have *: "max (- B) (min B (h x \<bullet> b)) = h x \<bullet> b" if "b \<in> Basis" for b
            using norm_nth_le[OF that, of "h x"] B by (smt (verit) real_norm_def)
          show ?thesis
            unfolding clamp_def using * by (simp cong: sum.cong add: euclidean_representation)
        qed
        have g_lim: "(\<lambda>n. g n x) \<longlonglongrightarrow> h x"
          using lim xS by fastforce
        have "isCont clamp (h x)"
          using clamp_cont continuous_on_eq_continuous_at open_UNIV by fastforce
        then have "(\<lambda>n. clamp (g n x)) \<longlonglongrightarrow> clamp (h x)"
          using continuous_imp_tendsto g_lim by (auto simp: o_def)
        then show ?thesis
          by (simp add: j_eq clamp_h)
      qed
    qed (use \<open>negligible N\<close> contg in auto)
  qed
  have S_sets: "S \<in> sets lebesgue"
    using assms(1) by blast
  have gn_int: "g n absolutely_integrable_on S" for n
  proof -
    have meas: "g n \<in> borel_measurable (lebesgue_on S)"
      using continuous_imp_measurable_on_sets_lebesgue[OF continuous_on_subset[OF g_cont subset_UNIV] S_sets] .
    have "integrable (lebesgue_on S) (norm \<circ> g n)"
    proof (rule finite_measure.integrable_const_bound[OF finite_measure_lebesgue_on[OF assms(1)]])
      show "AE x in lebesgue_on S. norm ((norm \<circ> g n) x) \<le> norm (B *\<^sub>R (\<Sum>b\<in>Basis. b :: 'b))"
        using g_bound by auto
      show "norm \<circ> g n \<in> borel_measurable (lebesgue_on S)"
        using borel_measurable_norm meas measurable_comp by blast
    qed
    then show ?thesis
      using meas S_sets absolutely_integrable_measurable by blast
  qed
  show ?thesis
  proof -
    define fn where "fn \<equiv> \<lambda>n x. norm (f x - g n x)"
    have fn_int: "fn n integrable_on S" for n
      using gn_int absolutely_integrable_on_def assms(2) fn_def
      by fastforce
    have fn_bound: "fn n x \<le> norm (f x) + norm (B *\<^sub>R (\<Sum>b\<in>Basis. b :: 'b))" for n x
    proof -
      have "fn n x \<le> norm (f x) + norm (g n x)"
        unfolding fn_def by (rule norm_triangle_ineq4)
      also have "\<dots> \<le> norm (f x) + norm (B *\<^sub>R (\<Sum>b\<in>Basis. b :: 'b))"
        using g_bound by force
      finally show ?thesis .
    qed
    have dom_int: "(\<lambda>x. norm (f x) + norm (B *\<^sub>R (\<Sum>b\<in>Basis. b :: 'b))) integrable_on S"
    proof -
      have "f integrable_on S"
        using assms(2) set_lebesgue_integral_eq_integral(1) by blast
      then have "(\<lambda>x. norm (f x)) integrable_on S"
        using absolutely_integrable_norm[OF assms(2)] set_lebesgue_integral_eq_integral(1)    
        by (simp add: absolutely_integrable_on_def)
      moreover have "(\<lambda>_::'a. norm (B *\<^sub>R (\<Sum>b\<in>Basis. b :: 'b))) integrable_on S"
        using absolutely_integrable_on_const[OF assms(1)] set_lebesgue_integral_eq_integral(1) by blast
      ultimately show ?thesis
        by (rule integrable_add)
    qed
    have fn_conv: "(\<lambda>n. fn n x) \<longlonglongrightarrow> norm (f x - h x)" if "x \<in> S - k" for x
      using fn_def g_conv tendsto_diff tendsto_norm that by blast
    have conv_Sk: "(\<lambda>n. integral (S - k) (fn n)) \<longlonglongrightarrow> integral (S - k) (\<lambda>x. norm (f x - h x))"
    proof (rule dominated_convergence(2))
      show "fn n integrable_on (S - k)" for n
        using fn_int integrable_spike_set negligible_subset[OF neg_k]
        by (simp add: has_integral_iff integrable_negligible integrable_setdiff)
      show "(\<lambda>x. norm (f x) + norm (B *\<^sub>R (\<Sum>b\<in>Basis. b :: 'b))) integrable_on (S - k)"
        using dom_int negligible_subset[OF neg_k]
        by (metis (lifting) eq_integralD integrable_negligible integrable_setdiff neg_k
            negligible_diff)
      show "norm (fn n x) \<le> norm (f x) + norm (B *\<^sub>R (\<Sum>b\<in>Basis. b :: 'b))"
        if "x \<in> S - k" for n x
        using fn_bound fn_def by fastforce
      show "(\<lambda>n. fn n x) \<longlonglongrightarrow> norm (f x - h x)" if "x \<in> S - k" for x
        using fn_conv that by blast
    qed
    have int_eq: "integral (S - k) (fn n) = integral S (fn n)" for n
      using integral_subset_negligible[of "S - k" S "fn n"] neg_k
      by (simp add: Diff_Diff_Int negligible_Int)
    have int_eq': "integral (S - k) (\<lambda>x. norm (f x - h x)) = integral S (\<lambda>x. norm (f x - h x))"
      using integral_subset_negligible[of "S - k" S "\<lambda>x. norm (f x - h x)"] neg_k
      by (simp add: Diff_Diff_Int negligible_Int)
    have conv_S: "(\<lambda>n. integral S (fn n)) \<longlonglongrightarrow> integral S (\<lambda>x. norm (f x - h x))"
      using conv_Sk int_eq int_eq' by simp
    have limit_small: "integral S (\<lambda>x. norm (f x - h x)) < e"
      using he2 by simp
    then obtain N where N: "\<forall>n\<ge>N. norm (integral S (fn n) - integral S (\<lambda>x. norm (f x - h x))) < e - integral S (\<lambda>x. norm (f x - h x))"
      using conv_S LIMSEQ_iff
      by (smt (verit) assms(3) diff_gt_0_iff_gt)
    have "norm (integral S (fn N)) < e"
    proof -
      have "norm (integral S (fn N) - integral S (\<lambda>x. norm (f x - h x))) < e - integral S (\<lambda>x. norm (f x - h x))"
        using N by simp
      then show ?thesis
        by (smt (verit, best) Henstock_Kurzweil_Integration.integral_nonneg fn_def fn_int
            norm_ge_zero real_norm_def)
    qed
    then have goal: "norm (integral S (\<lambda>x. norm (f x - g N x))) < e"
      by (simp add: fn_def)
    have \<open>bounded (range (g N)) \<close>
      using bounded_iff g_bound by blast
    then show ?thesis
      using that[OF \<open>g N absolutely_integrable_on S\<close> g_cont] goal by blast
  qed
qed

theorem absolutely_integrable_approximate_continuous:
  fixes f :: \<open>'a::euclidean_space \<Rightarrow> 'b::euclidean_space\<close>
    and S :: \<open>'a set\<close>
  assumes S_meas: \<open>S \<in> sets lebesgue\<close>
    and f_int: \<open>f absolutely_integrable_on S\<close>
    and e_pos: \<open>e > 0\<close>
  obtains g where \<open>g absolutely_integrable_on S\<close> \<open>continuous_on UNIV g\<close>
    \<open>bounded (g ` UNIV)\<close>
    \<open>norm (integral S (\<lambda>x. norm (f x - g x))) < e\<close>
proof -
  text \<open>Claim 1: absolute integrability on intersections and differences with boxes.\<close>
  have f_int_inter: \<open>f absolutely_integrable_on (S \<inter> cbox u v)\<close> for u v
    by (meson assms(1,2) fmeasurableD fmeasurable_cbox inf.cobounded1 set_integrable_subset
        sets.Int sets_completionI_sets)
  have f_int_diff: \<open>f absolutely_integrable_on (S - cbox u v)\<close> for u v
    by (meson Diff_subset assms(1,2) fmeasurableD lmeasurable_cbox set_integrable_subset
        sets.Diff)
  text \<open>Claim 2: approximation of the norm integral by boxes.\<close>
  have norm_int: \<open>(\<lambda>x. norm (f x)) integrable_on S\<close>
    using f_int absolutely_integrable_on_def by blast
  obtain a b where approx:
    \<open>norm (integral (S \<inter> cbox a b) (\<lambda>x. norm (f x)) - integral S (\<lambda>x. norm (f x))) < e / 3\<close>
  proof -
    have \<open>((\<lambda>x. norm (f x)) has_integral integral S (\<lambda>x. norm (f x))) S\<close>
      using integrable_integral [OF norm_int] .
    then have alt: \<open>\<forall>\<epsilon>>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
                     norm (integral (cbox a b) (\<lambda>x. if x \<in> S then norm (f x) else 0) -
                           integral S (\<lambda>x. norm (f x))) < \<epsilon>\<close>
      using has_integral_alt' [of \<open>\<lambda>x. norm (f x)\<close> \<open>integral S (\<lambda>x. norm (f x))\<close> S]
      by blast
    have \<open>e / 3 > 0\<close> using e_pos by auto
    then obtain B where \<open>B > 0\<close> and B:
      \<open>\<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
         norm (integral (cbox a b) (\<lambda>x. if x \<in> S then norm (f x) else 0) -
               integral S (\<lambda>x. norm (f x))) < e / 3\<close>
      using alt by blast
    obtain c where \<open>ball (0::'a) B \<subseteq> cbox (- c) c\<close>
      using bounded_subset_cbox_symmetric [OF bounded_ball] by blast
    then have \<open>norm (integral (cbox (- c) c) (\<lambda>x. if x \<in> S then norm (f x) else 0) -
                     integral S (\<lambda>x. norm (f x))) < e / 3\<close>
      using B by blast
    moreover have \<open>integral (cbox (- c) c) (\<lambda>x. if x \<in> S then norm (f x) else 0) =
                   integral (S \<inter> cbox (- c) c) (\<lambda>x. norm (f x))\<close>
      by (rule integral_restrict_Int)
    ultimately show ?thesis
      using that by auto
  qed
  text \<open>Apply the existing lemma to get a continuous bounded approximation on the box.\<close>
  have meas_inter: \<open>S \<inter> cbox a b \<in> lmeasurable\<close>
    by (intro bounded_set_imp_lmeasurable bounded_Int)
       (use S_meas lmeasurable_cbox fmeasurableD sets.Int in auto)
  obtain g where g_int: \<open>g absolutely_integrable_on (S \<inter> cbox a b)\<close>
    and g_cont: \<open>continuous_on UNIV g\<close>
    and g_bdd: \<open>bounded (g ` UNIV)\<close>
    and g_approx: \<open>norm (integral (S \<inter> cbox a b) (\<lambda>x. norm (f x - g x))) < e / 3\<close>
  proof -
    have \<open>e / 3 > 0\<close> using e_pos by auto
    then show ?thesis
      using absolutely_integrable_approximate_continuous_vector [OF meas_inter f_int_inter]
            that
      by metis
  qed
  text \<open>Extract an explicit positive bound on @{term g}.\<close>
  obtain B where B_pos: \<open>B > 0\<close> and B_bound: \<open>\<And>x. norm (g x) \<le> B\<close>
    using g_bdd [unfolded bounded_pos] by (auto simp: image_iff)
  text \<open>Obtain @{term c}, @{term d} with @{term \<open>cbox a b \<subseteq> box c d\<close>} and small measure gap.\<close>
  have eB: \<open>e / 3 / B > 0\<close> using e_pos B_pos by auto
  obtain c d where cd_sub: \<open>cbox a b \<subseteq> box c d\<close>
    and cd_meas: \<open>measure lborel (box c d) - measure lborel (cbox a b) < e / 3 / B\<close>
  proof (cases \<open>cbox a b = {}\<close>)
    case True
    then show ?thesis using eB by (intro that [of 0 0]) auto
  next
    case False
    then have ab: \<open>\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> b \<bullet> i\<close> by (simp add: box_ne_empty)
    define F where \<open>F \<equiv> \<lambda>\<delta>::real. \<Prod>i\<in>Basis. (b \<bullet> i - a \<bullet> i) + 2 * \<delta>\<close>
    have F_cont: \<open>isCont F 0\<close>
      unfolding F_def by (intro continuous_intros)
    have F_0: \<open>F 0 = measure lborel (cbox a b)\<close>
      unfolding F_def using content_cbox' [OF False] by simp
    then obtain \<delta> where \<open>\<delta> > 0\<close> and
      \<delta>_bound: \<open>\<And>\<delta>'. \<bar>\<delta>'\<bar> < \<delta> \<Longrightarrow> \<bar>F \<delta>' - F 0\<bar> < e / 3 / B\<close>
      using F_cont [unfolded continuous_at_real_range] eB by (auto simp: real_norm_def)
    define \<delta>' where \<open>\<delta>' \<equiv> min \<delta> 1 / 2\<close>
    have \<delta>'_pos: \<open>\<delta>' > 0\<close> using \<open>\<delta> > 0\<close> unfolding \<delta>'_def by auto
    have \<delta>'_lt: \<open>\<bar>\<delta>'\<bar> < \<delta>\<close> using \<open>\<delta> > 0\<close> unfolding \<delta>'_def by auto
    define c' d' where \<open>c' \<equiv> a - \<delta>' *\<^sub>R One\<close> and \<open>d' \<equiv> b + \<delta>' *\<^sub>R One\<close>
    have inner_c': \<open>i \<in> Basis \<Longrightarrow> c' \<bullet> i = a \<bullet> i - \<delta>'\<close> for i
      unfolding c'_def by (simp add: inner_diff_left inner_scaleR_left inner_sum_Basis)
    have inner_d': \<open>i \<in> Basis \<Longrightarrow> d' \<bullet> i = b \<bullet> i + \<delta>'\<close> for i
      unfolding d'_def by (simp add: inner_add_left inner_scaleR_left inner_sum_Basis)
    have sub: \<open>cbox a b \<subseteq> box c' d'\<close>
      by (intro subset_box_imp ballI conjI)
         (simp_all add: inner_c' inner_d' \<delta>'_pos)
    have cd_le: \<open>i \<in> Basis \<Longrightarrow> c' \<bullet> i \<le> d' \<bullet> i\<close> for i
      using ab [of i] \<delta>'_pos by (simp add: inner_c' inner_d')
    have cd_ne: \<open>cbox c' d' \<noteq> {}\<close>
      using False sub box_subset_cbox [of c' d'] by auto
    have content_cd: \<open>measure lborel (cbox c' d') = F \<delta>'\<close>
      unfolding F_def using content_cbox' [OF cd_ne]
      by (simp add: inner_c' inner_d' algebra_simps)
    have content_mono: \<open>measure lborel (cbox a b) \<le> measure lborel (cbox c' d')\<close>
      using Henstock_Kurzweil_Integration.content_subset
            [OF subset_trans [OF sub box_subset_cbox]] .
    have \<open>\<bar>F \<delta>' - F 0\<bar> < e / 3 / B\<close>
      using \<delta>_bound \<delta>'_lt by blast
    then have \<open>measure lborel (cbox c' d') - measure lborel (cbox a b) < e / 3 / B\<close>
      using content_cd F_0 content_mono by linarith
    then show ?thesis
      using sub that content_box_cbox [of c' d'] by simp
  qed

  text \<open>Apply Tietze to obtain @{term h} extending @{term \<open>\<lambda>x. if x \<in> cbox a b then g x else 0\<close>}
    from the closed set @{term \<open>cbox a b \<union> (UNIV - box c d)\<close>} to all of @{term UNIV},
    with bound @{term B}.\<close>
  obtain h where h_cont: \<open>continuous_on UNIV h\<close>
    and h_eq: \<open>\<And>x. x \<in> cbox a b \<union> (UNIV - box c d) \<Longrightarrow> h x = (if x \<in> cbox a b then g x else 0)\<close>
    and h_bound: \<open>\<And>x. norm (h x) \<le> B\<close>
  proof (rule Tietze [of \<open>cbox a b \<union> (UNIV - box c d)\<close>
      \<open>\<lambda>x. if x \<in> cbox a b then g x else 0\<close> UNIV B])
    show \<open>continuous_on (cbox a b \<union> (UNIV - box c d))
          (\<lambda>x. if x \<in> cbox a b then g x else 0)\<close>
    proof (rule continuous_on_cases)
      show \<open>closed (cbox a b)\<close> by (rule closed_cbox)
      show \<open>closed (UNIV - box c d)\<close>
        using closed_Compl [OF open_box] by (simp add: Compl_eq_Diff_UNIV)
      show \<open>continuous_on (cbox a b) g\<close>
        using g_cont continuous_on_subset by blast
      show \<open>continuous_on (UNIV - box c d) (\<lambda>x. 0)\<close>
        by (rule continuous_on_const)
      show \<open>\<forall>x. x \<in> cbox a b \<and> x \<notin> cbox a b \<or>
              x \<in> UNIV - box c d \<and> x \<in> cbox a b \<longrightarrow> g x = 0\<close>
        using cd_sub by auto
    qed
    show \<open>closedin (top_of_set UNIV) (cbox a b \<union> (UNIV - box c d))\<close>
      unfolding subtopology_UNIV closed_closedin [symmetric]
      by (intro closed_Un closed_cbox closed_Compl [OF open_box, simplified Compl_eq_Diff_UNIV])
    show \<open>0 \<le> B\<close> using B_pos by linarith
    fix x assume \<open>x \<in> cbox a b \<union> (UNIV - box c d)\<close>
    then show \<open>norm (if x \<in> cbox a b then g x else 0) \<le> B\<close>
      using B_bound B_pos by (auto simp: less_imp_le)
  next
    fix h assume \<open>continuous_on UNIV h\<close>
      and \<open>\<And>x. x \<in> cbox a b \<union> (UNIV - box c d) \<Longrightarrow> h x = (if x \<in> cbox a b then g x else 0)\<close>
      and \<open>\<And>x. x \<in> UNIV \<Longrightarrow> norm (h x) \<le> B\<close>
    then show thesis
      by (intro that [of h]) auto
  qed
  text \<open>Show that h is absolutely integrable on S.\<close>
  have h_zero: \<open>h x = 0\<close> if \<open>x \<notin> cbox c d\<close> for x
    by (metis DiffI Diff_partition UNIV_I UnCI box_subset_cbox cd_sub h_eq that)
  have h_abs_cbox: \<open>h absolutely_integrable_on cbox c d\<close>
    by (rule absolutely_integrable_continuous [OF continuous_on_subset [OF h_cont subset_UNIV]])
  have h_abs_inter: \<open>h absolutely_integrable_on (S \<inter> cbox c d)\<close>
    using h_abs_cbox S_meas
    by (meson fmeasurableD fmeasurable_cbox inf.cobounded2 set_integrable_subset
        sets.Int sets_completionI_sets)
  have h_abs_S: \<open>h absolutely_integrable_on S\<close>
  proof (rule absolutely_integrable_spike_set [OF h_abs_inter])
    show \<open>negligible {x \<in> S \<inter> cbox c d - S. h x \<noteq> 0}\<close>
      by (simp add: Int_Diff)
    show \<open>negligible {x \<in> S - S \<inter> cbox c d. h x \<noteq> 0}\<close>
      by (simp add: h_zero cong: conj_cong)
  qed
  have h_int_inter: \<open>h absolutely_integrable_on (S \<inter> cbox u v)\<close> for u v
    by (meson h_abs_S S_meas fmeasurableD fmeasurable_cbox inf.cobounded1 set_integrable_subset
        sets.Int sets_completionI_sets)
  have h_int_diff: \<open>h absolutely_integrable_on (S - cbox u v)\<close> for u v
    by (meson h_abs_S S_meas Diff_subset fmeasurableD lmeasurable_cbox set_integrable_subset
        sets.Diff)
  show ?thesis
  proof
    show \<open>h absolutely_integrable_on S\<close> by (rule h_abs_S)
  next
    have fh_abs_inter: \<open>(\<lambda>x. f x - h x) absolutely_integrable_on (S \<inter> cbox a b)\<close>
      using f_int_inter h_int_inter by (rule set_integral_diff(1))
    have fh_abs_diff: \<open>(\<lambda>x. f x - h x) absolutely_integrable_on (S - cbox a b)\<close>
      using f_int_diff h_int_diff by (rule set_integral_diff(1))
    have nfh_int_inter: \<open>(\<lambda>x. norm (f x - h x)) integrable_on (S \<inter> cbox a b)\<close>
      using absolutely_integrable_norm [OF fh_abs_inter]
      by (auto intro: set_lebesgue_integral_eq_integral(1) simp: o_def)
    have nfh_int_diff: \<open>(\<lambda>x. norm (f x - h x)) integrable_on (S - cbox a b)\<close>
      using absolutely_integrable_norm [OF fh_abs_diff]
      by (auto intro: set_lebesgue_integral_eq_integral(1) simp: o_def)
    have split_eq: \<open>integral S (\<lambda>x. norm (f x - h x)) =
        integral (S \<inter> cbox a b) (\<lambda>x. norm (f x - h x)) + integral (S - cbox a b) (\<lambda>x. norm (f x - h x))\<close>
      by (metis (lifting) Diff_disjoint Int_Diff_Un Int_assoc integral_Un negligible_Int
          negligible_empty nfh_int_diff nfh_int_inter)
    have h_eq_g_on_ab: \<open>h x = g x\<close> if \<open>x \<in> cbox a b\<close> for x
      using h_eq [of x] that by auto
    have integral_fg_eq: \<open>integral (S \<inter> cbox a b) (\<lambda>x. norm (f x - g x)) =
        integral (S \<inter> cbox a b) (\<lambda>x. norm (f x - h x))\<close>
      by (intro integral_unique has_integral_eq [OF _ integrable_integral [OF nfh_int_inter]])
         (auto simp: h_eq_g_on_ab)
    have nf_int_diff: \<open>(\<lambda>x. norm (f x)) integrable_on (S - cbox a b)\<close>
      using absolutely_integrable_norm [OF f_int_diff]
      by (auto intro: set_lebesgue_integral_eq_integral(1) simp: o_def)
    have nh_int_diff: \<open>(\<lambda>x. norm (h x)) integrable_on (S - cbox a b)\<close>
      using absolutely_integrable_norm [OF h_int_diff]
      by (auto intro: set_lebesgue_integral_eq_integral(1) simp: o_def)
    have nfh_sum_int_diff: \<open>(\<lambda>x. norm (f x) + norm (h x)) integrable_on (S - cbox a b)\<close>
      by (rule integrable_add [OF nf_int_diff nh_int_diff])
    have norm_diff_bound: \<open>norm (integral (S - cbox a b) (\<lambda>x. norm (f x - h x))) \<le>
        integral (S - cbox a b) (\<lambda>x. norm (f x) + norm (h x))\<close>
      by (rule integral_norm_bound_integral [OF nfh_int_diff nfh_sum_int_diff])
        (simp add: norm_triangle_ineq4)
    have nf_int_inter: \<open>(\<lambda>x. norm (f x)) integrable_on (S \<inter> cbox a b)\<close>
      using absolutely_integrable_norm [OF f_int_inter]
      by (auto intro: set_lebesgue_integral_eq_integral(1) simp: o_def)
    have nf_split: \<open>integral (S \<inter> cbox a b) (\<lambda>x. norm (f x)) + integral (S - cbox a b) (\<lambda>x. norm (f x))
        = integral S (\<lambda>x. norm (f x))\<close>
      by (metis Diff_disjoint Int_Diff_Un Int_assoc integral_Un negligible_Int
          negligible_empty nf_int_diff nf_int_inter)

    have nf_diff_bound: \<open>integral (S - cbox a b) (\<lambda>x. norm (f x)) < e / 3\<close>
      using nf_split approx integral_nonneg [OF nf_int_diff]
      by (simp add: abs_le_iff)
    have nh_diff_bound: \<open>integral (S - cbox a b) (\<lambda>x. norm (h x)) < e / 3\<close>
    proof -
      have cd_ab_meas: \<open>box c d - cbox a b \<in> lmeasurable\<close>
        using lmeasurable_box lmeasurable_cbox by (rule fmeasurable.Diff)
      have int1: \<open>(\<lambda>x. if x \<in> S - cbox a b then norm (h x) else 0) integrable_on UNIV\<close>
        using nh_int_diff integrable_restrict_UNIV by fastforce
      have int2: \<open>(\<lambda>x. if x \<in> box c d - cbox a b then B else 0) integrable_on UNIV\<close>
        using integrable_on_const [OF cd_ab_meas] integrable_restrict_UNIV by fastforce
      have pw: \<open>norm (if x \<in> S - cbox a b then norm (h x) else 0) \<le>
              (if x \<in> box c d - cbox a b then B else 0)\<close> for x
        using B_pos h_bound h_eq by force

      have \<open>integral (S - cbox a b) (\<lambda>x. norm (h x)) =
                integral UNIV (\<lambda>x. if x \<in> S - cbox a b then norm (h x) else 0)\<close>
        by (rule integral_restrict_UNIV [symmetric])
      moreover have \<open>integral (box c d - cbox a b) (\<lambda>x. B) =
                integral UNIV (\<lambda>x. if x \<in> box c d - cbox a b then B else 0)\<close>
        by (rule integral_restrict_UNIV [symmetric])
      moreover have \<open>norm (integral UNIV (\<lambda>x. if x \<in> S - cbox a b then norm (h x) else 0)) \<le>
              integral UNIV (\<lambda>x. if x \<in> box c d - cbox a b then B else 0)\<close>
        by (rule integral_norm_bound_integral [OF int1 int2 pw])
      ultimately have nh_le_const:
        \<open>integral (S - cbox a b) (\<lambda>x. norm (h x)) \<le> integral (box c d - cbox a b) (\<lambda>x. B)\<close>
        by simp
      also have \<open>\<dots> = B * (measure lebesgue (box c d) - measure lebesgue (cbox a b))\<close>
        by (metis (no_types, lifting) ext Henstock_Kurzweil_Integration.integral_mult_right
            cd_ab_meas lmeasure_integral mult_1_right
            measurable_measure_Diff [OF lmeasurable_box]
            lmeasurable_cbox fmeasurableD cd_sub)
      also have \<open>\<dots> < B * (e / 3 / B)\<close>
        using cd_meas B_pos by (intro mult_strict_left_mono) auto
      also have \<open>\<dots> = e / 3\<close>
        using B_pos by auto
      finally show ?thesis .
    qed
    have step1: \<open>norm (integral (S \<inter> cbox a b) (\<lambda>x. norm (f x - h x))) < e / 3\<close>
      using g_approx by (simp add: integral_fg_eq)
    have step2: \<open>norm (integral (S - cbox a b) (\<lambda>x. norm (f x - h x))) < 2 / 3 * e\<close>
      using norm_diff_bound integral_add [OF nf_int_diff nh_int_diff]
            nf_diff_bound nh_diff_bound
      by linarith
    have \<open>norm (integral S (\<lambda>x. norm (f x - h x))) \<le>
        norm (integral (S \<inter> cbox a b) (\<lambda>x. norm (f x - h x))) +
        norm (integral (S - cbox a b) (\<lambda>x. norm (f x - h x)))\<close>
      by (simp add: split_eq norm_triangle_ineq)
    also have \<open>\<dots> < e / 3 + 2 / 3 * e\<close>
      using step1 step2 by linarith
    also have \<open>\<dots> = e\<close> by simp
    finally show "norm (integral S (\<lambda>x. norm (f x - h x))) < e" .
  qed (use h_bound h_cont bounded_iff in auto)
qed


text \<open>Integration by parts for absolutely integrable functions.
  The first lemma is a direct specialisation of @{thm integration_by_parts}
  to real-valued multiplication.\<close>

lemma real_integration_by_parts_simple:
  fixes f g f' g' :: "real \<Rightarrow> real" and a b y :: real
  assumes "a \<le> b"
    and "continuous_on {a..b} f" and "continuous_on {a..b} g"
    and "\<And>x. x \<in> {a..b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
    and "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
    and "((\<lambda>x. f x * g' x) has_integral (f b * g b - f a * g a - y)) {a..b}"
  shows "((\<lambda>x. f' x * g x) has_integral y) {a..b}"
  by (rule integration_by_parts [OF bounded_bilinear_mult]) (use assms in auto)


text \<open>Integration by parts for absolutely integrable functions with indefinite integrals.
  This is the bilinear generalisation: HOL Light's @{text ABSOLUTE_INTEGRATION_BY_PARTS}.\<close>

theorem absolute_integration_by_parts:
  fixes bop :: \<open>'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::euclidean_space\<close>
    and f :: \<open>real \<Rightarrow> 'a\<close> and g :: \<open>real \<Rightarrow> 'b\<close>
    and f' :: \<open>real \<Rightarrow> 'a\<close> and g' :: \<open>real \<Rightarrow> 'b\<close>
    and a b :: real
  assumes \<open>bilinear bop\<close>
    and ab: \<open>a \<le> b\<close>
    and f'abs: \<open>f' absolutely_integrable_on {a..b}\<close>
    and g'abs: \<open>g' absolutely_integrable_on {a..b}\<close>
    and f'int: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> (f' has_integral f x) {a..x}\<close>
    and g'int: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> (g' has_integral g x) {a..x}\<close>
  shows \<open>(\<lambda>x. bop (f x) (g' x)) absolutely_integrable_on {a..b}\<close>
    and \<open>(\<lambda>x. bop (f' x) (g x)) absolutely_integrable_on {a..b}\<close>
    and \<open>integral {a..b} (\<lambda>x. bop (f x) (g' x)) + integral {a..b} (\<lambda>x. bop (f' x) (g x)) 
       = bop (f b) (g b) - bop (f a) (g a)\<close>
proof -
  have f'int_eq: "f x = integral {a..x} f'" if "x \<in> {a..b}" for x
    using integral_unique[OF f'int[OF that]] by simp
  have g'int_eq: "g x = integral {a..x} g'" if "x \<in> {a..b}" for x
    using integral_unique[OF g'int[OF that]] by simp
  have f'_int: "f' integrable_on {a..b}"
    using f'abs absolutely_integrable_on_def by blast
  have g'_int: "g' integrable_on {a..b}"
    using g'abs absolutely_integrable_on_def by blast
  have f_cont: "continuous_on {a..b} f"
    by (metis (mono_tags, lifting) continuous_on_cong f'_int f'int_eq indefinite_integral_continuous_1)
  have g_cont: "continuous_on {a..b} g"
    by (metis (mono_tags, lifting) continuous_on_cong g'_int g'int_eq indefinite_integral_continuous_1)
  have ab_sets: "{a..b} \<in> sets lebesgue"
    by simp
  have f_meas: "f \<in> borel_measurable (lebesgue_on {a..b})"
    using integrable_imp_measurable[OF integrable_continuous_real[OF f_cont]] .
  have f_bounded: "bounded (f ` {a..b})"
    using compact_continuous_image[OF f_cont compact_Icc] compact_imp_bounded by blast
  have g_meas: "g \<in> borel_measurable (lebesgue_on {a..b})"
    using integrable_imp_measurable[OF integrable_continuous_real[OF g_cont]] .
  have g_bounded: "bounded (g ` {a..b})"
    using compact_continuous_image[OF g_cont compact_Icc] compact_imp_bounded by blast
  have bop_swap: "bilinear (\<lambda>x y. bop y x)"
    using \<open>bilinear bop\<close> by (simp add: bilinear_def)
  show "(\<lambda>x. bop (f x) (g' x)) absolutely_integrable_on {a..b}"
    using absolutely_integrable_bounded_measurable_product[OF \<open>bilinear bop\<close> f_meas ab_sets f_bounded g'abs] .
  show "(\<lambda>x. bop (f' x) (g x)) absolutely_integrable_on {a..b}"
    using absolutely_integrable_bounded_measurable_product[OF bop_swap g_meas ab_sets g_bounded f'abs] .

  obtain ff' where ff': \<open>\<forall>n. ff' n absolutely_integrable_on {a..b} \<and> continuous_on UNIV (ff' n) \<and>
              bounded (range (ff' n)) \<and>
              norm (integral {a..b} (\<lambda>x. norm (f' x - ff' n x))) < inverse (real n + 1)\<close>
  proof -
    have \<open>\<forall>n. \<exists>h. h absolutely_integrable_on {a..b} \<and> continuous_on UNIV h \<and>
                bounded (range h) \<and>
                norm (integral {a..b} (\<lambda>x. norm (f' x - h x))) < inverse (real n + 1)\<close> (is "All ?P")
    proof
      fix n :: nat
      have e_pos: \<open>inverse (real n + 1) > 0\<close> by simp
      show "?P n"
        using absolutely_integrable_approximate_continuous_vector [OF _ f'abs e_pos]
        by force
    qed
    with that show thesis 
      unfolding choice_iff by blast
  qed
  obtain gg' where gg': \<open>\<forall>n. gg' n absolutely_integrable_on {a..b} \<and> continuous_on UNIV (gg' n) \<and>
              bounded (range (gg' n)) \<and>
              norm (integral {a..b} (\<lambda>x. norm (g' x - gg' n x))) < inverse (real n + 1)\<close>
  proof -
    have \<open>\<forall>n. \<exists>h. h absolutely_integrable_on {a..b} \<and> continuous_on UNIV h \<and>
                bounded (range h) \<and>
                norm (integral {a..b} (\<lambda>x. norm (g' x - h x))) < inverse (real n + 1)\<close> (is "All ?P")
    proof
      fix n :: nat
      have e_pos: \<open>inverse (real n + 1) > 0\<close> by simp
      show "?P n"
        using absolutely_integrable_approximate_continuous_vector [OF _ g'abs e_pos]
        by force
    qed
    with that show thesis 
      unfolding choice_iff by blast
  qed
  \<comment> \<open>ff' n and gg' n are continuous on {a..b} (restriction of continuous_on UNIV).\<close>
  have ff'_cont_ab: \<open>\<And>n. continuous_on {a..b} (ff' n)\<close>
    using ff' continuous_on_subset by blast
  have gg'_cont_ab: \<open>\<And>n. continuous_on {a..b} (gg' n)\<close>
    using gg' continuous_on_subset by blast

  \<comment> \<open>Define the indefinite integrals of ff' and gg'.\<close>
  define ff where \<open>ff \<equiv> \<lambda>n x. integral {a..x} (ff' n)\<close>
  define gg where \<open>gg \<equiv> \<lambda>n x. integral {a..x} (gg' n)\<close>

  \<comment> \<open>ff n and gg n are continuous on {a..b}.\<close>
  have ff_cont: \<open>\<And>n. continuous_on {a..b} (ff n)\<close>
    unfolding ff_def using ff' indefinite_integral_continuous_1 set_lebesgue_integral_eq_integral(1)
    by blast
  have gg_cont: \<open>\<And>n. continuous_on {a..b} (gg n)\<close>
    unfolding gg_def using gg' indefinite_integral_continuous_1 set_lebesgue_integral_eq_integral(1)
    by blast

  \<comment> \<open>f, g, ff n, gg n are all absolutely integrable on {a..b}.\<close>
  have f_absint: \<open>f absolutely_integrable_on {a..b}\<close>
    using f_cont absolutely_integrable_continuous_real by blast
  have g_absint: \<open>g absolutely_integrable_on {a..b}\<close>
    using g_cont absolutely_integrable_continuous_real by blast
  have ff_absint: \<open>\<And>n. ff n absolutely_integrable_on {a..b}\<close>
    using ff_cont absolutely_integrable_continuous_real by blast
  have gg_absint: \<open>\<And>n. gg n absolutely_integrable_on {a..b}\<close>
    using gg_cont absolutely_integrable_continuous_real by blast

  \<comment> \<open>Bilinear product is absolutely integrable when one factor is abs.\ integrable
    and the other is continuous on the compact interval.\<close>
  have bop_absint_cont1: \<open>(\<lambda>x. bop (h x) (k x)) absolutely_integrable_on {a..b}\<close>
    if \<open>h absolutely_integrable_on {a..b}\<close> \<open>continuous_on {a..b} k\<close> for h :: \<open>real \<Rightarrow> 'a\<close> and k :: \<open>real \<Rightarrow> 'b\<close>
  proof -
    have \<open>k \<in> borel_measurable (lebesgue_on {a..b})\<close>
      using continuous_imp_measurable_on_sets_lebesgue[OF that(2) ab_sets] .
    moreover have \<open>bounded (k ` {a..b})\<close>
      using compact_imp_bounded[OF compact_continuous_image[OF that(2) compact_Icc]] .
    ultimately show ?thesis
      using absolutely_integrable_bounded_measurable_product[OF bop_swap _ ab_sets _ that(1)]
      by simp
  qed
  have bop_absint_cont2: \<open>(\<lambda>x. bop (h x) (k x)) absolutely_integrable_on {a..b}\<close>
    if \<open>continuous_on {a..b} h\<close> \<open>k absolutely_integrable_on {a..b}\<close> for h :: \<open>real \<Rightarrow> 'a\<close> and k :: \<open>real \<Rightarrow> 'b\<close>
  proof -
    have \<open>h \<in> borel_measurable (lebesgue_on {a..b})\<close>
      using continuous_imp_measurable_on_sets_lebesgue[OF that(1) ab_sets] .
    moreover have \<open>bounded (h ` {a..b})\<close>
      using compact_imp_bounded[OF compact_continuous_image[OF that(1) compact_Icc]] .
    ultimately show ?thesis
      using absolutely_integrable_bounded_measurable_product[OF \<open>bilinear bop\<close> _ ab_sets _ that(2)]
      by simp
  qed
  define s where \<open>s \<equiv> \<lambda>n.
      (integral {a..b} (\<lambda>x. bop (ff n x) (gg' n x)) +
       integral {a..b} (\<lambda>x. bop (ff' n x) (gg n x))) -
      (bop (ff n b) (gg n b) - bop (ff n a) (gg n a))\<close>
  have lim_zero: \<open>s \<longlonglongrightarrow> 0\<close>
  proof -
    have s_eq: \<open>s n = 0\<close> for n
    proof -
      \<comment> \<open>ff n and gg n have the right derivatives at interior points of {a..b}.\<close>
      have ff_deriv: \<open>(ff n has_vector_derivative ff' n x) (at x)\<close> if \<open>x \<in> {a<..<b}\<close> for x
      proof -
        have \<open>((\<lambda>u. integral {a..u} (ff' n)) has_vector_derivative ff' n x) (at x within {a..b})\<close>
          using integral_has_vector_derivative[OF ff'_cont_ab] that by auto
        then have \<open>((\<lambda>u. integral {a..u} (ff' n)) has_vector_derivative ff' n x) (at x)\<close>
          using at_within_Icc_at that by fastforce
        then show ?thesis unfolding ff_def .
      qed
      have gg_deriv: \<open>(gg n has_vector_derivative gg' n x) (at x)\<close> if \<open>x \<in> {a<..<b}\<close> for x
      proof -
        have \<open>((\<lambda>u. integral {a..u} (gg' n)) has_vector_derivative gg' n x) (at x within {a..b})\<close>
          using integral_has_vector_derivative[OF gg'_cont_ab] that by auto
        then have \<open>((\<lambda>u. integral {a..u} (gg' n)) has_vector_derivative gg' n x) (at x)\<close>
          using at_within_Icc_at that by fastforce
        then show ?thesis unfolding gg_def .
      qed
      \<comment> \<open>Apply integration by parts (interior version) for continuous ff' n, gg' n.\<close>
      have bb: \<open>bounded_bilinear bop\<close>
        using \<open>bilinear bop\<close> bilinear_conv_bounded_bilinear by blast
      have bop_int1: \<open>(\<lambda>x. bop (ff n x) (gg' n x)) integrable_on {a..b}\<close>
        using bop_absint_cont2[OF ff_cont gg'_cont_ab[THEN absolutely_integrable_continuous_real]]
              set_lebesgue_integral_eq_integral(1) by blast
      have ibp: \<open>((\<lambda>x. bop (ff' n x) (gg n x)) has_integral
            (bop (ff n b) (gg n b) - bop (ff n a) (gg n a) -
             integral {a..b} (\<lambda>x. bop (ff n x) (gg' n x)))) {a..b}\<close>
      proof (rule integration_by_parts_interior[OF bb ab ff_cont gg_cont ff_deriv gg_deriv])
        show \<open>((\<lambda>x. bop (ff n x) (gg' n x)) has_integral
              bop (ff n b) (gg n b) - bop (ff n a) (gg n a) -
              (bop (ff n b) (gg n b) - bop (ff n a) (gg n a) -
               integral {a..b} (\<lambda>x. bop (ff n x) (gg' n x)))) {a..b}\<close>
          using integrable_integral[OF bop_int1] by simp
      qed
      show ?thesis
        unfolding s_def
        using integral_unique[OF ibp] by (simp add: algebra_simps)
    qed
    show ?thesis
      using s_eq tendsto_const[of 0 sequentially]
      by (simp add: LIMSEQ_iff)
  qed
  moreover have lim_goal: \<open>s \<longlonglongrightarrow>
      (integral {a..b} (\<lambda>x. bop (f x) (g' x)) +
       integral {a..b} (\<lambda>x. bop (f' x) (g x))) -
      (bop (f b) (g b) - bop (f a) (g a))\<close>
  proof -
    \<comment> \<open>Obtain the bilinear norm bound K.\<close>
    have bb: \<open>bounded_bilinear bop\<close>
      using \<open>bilinear bop\<close> bilinear_conv_bounded_bilinear by blast
    obtain K where \<open>K > 0\<close> and K: \<open>\<And>u v. norm (bop u v) \<le> norm u * norm v * K\<close>
      using bounded_bilinear.pos_bounded[OF bb] by blast
    \<comment> \<open>L1 convergence: \<integral> \<Parallel>f' - ff' n\<Parallel> \<rightarrow> 0 and \<integral> \<Parallel>g' - gg' n\<Parallel> \<rightarrow> 0.\<close>
    have ff'_L1: \<open>(\<lambda>n. integral {a..b} (\<lambda>x. norm (f' x - ff' n x))) \<longlonglongrightarrow> 0\<close>
    proof (rule LIMSEQ_norm_0)
      fix n
      have \<open>norm (integral {a..b} (\<lambda>x. norm (f' x - ff' n x))) < inverse (real n + 1)\<close>
        using ff' by blast
      also have \<open>inverse (real n + 1) = 1 / real (Suc n)\<close>
        by (simp add: inverse_eq_divide)
      finally show \<open>norm (integral {a..b} (\<lambda>x. norm (f' x - ff' n x))) < 1 / real (Suc n)\<close> .
    qed
    have gg'_L1: \<open>(\<lambda>n. integral {a..b} (\<lambda>x. norm (g' x - gg' n x))) \<longlonglongrightarrow> 0\<close>
    proof (rule LIMSEQ_norm_0)
      fix n
      have \<open>norm (integral {a..b} (\<lambda>x. norm (g' x - gg' n x))) < inverse (real n + 1)\<close>
        using gg' by blast
      also have \<open>inverse (real n + 1) = 1 / real (Suc n)\<close>
        by (simp add: inverse_eq_divide)
      finally show \<open>norm (integral {a..b} (\<lambda>x. norm (g' x - gg' n x))) < 1 / real (Suc n)\<close> .
    qed

    \<comment> \<open>FTC identity: f and g are the indefinite integrals of f' and g' on {a..b}.\<close>
    have f_eq: \<open>f x = integral {a..x} f'\<close> if \<open>x \<in> {a..b}\<close> for x
      using f'int_eq[OF that] .
    have g_eq: \<open>g x = integral {a..x} g'\<close> if \<open>x \<in> {a..b}\<close> for x
      using g'int_eq[OF that] .

    \<comment> \<open>Pointwise convergence: ff n c \<rightarrow> f c and gg n c \<rightarrow> g c for any c \<in> {a..b},
      via L1 convergence of ff' n \<rightarrow> f' and gg' n \<rightarrow> g'.\<close>
    have ff_ptwise: \<open>(\<lambda>n. ff n c) \<longlonglongrightarrow> f c\<close> if c_ab: \<open>c \<in> {a..b}\<close> for c
    proof -
      have ac_sub: \<open>{a..c} \<subseteq> {a..b}\<close> using c_ab by auto
      have ff'n_int_c: \<open>ff' n integrable_on {a..c}\<close> for n
        using ff'_cont_ab integrable_continuous_real integrable_on_subinterval ac_sub by blast
      have f'_int_c: \<open>f' integrable_on {a..c}\<close>
        using f'_int integrable_on_subinterval ac_sub by blast
      have diff_int_c: \<open>(\<lambda>x. ff' n x - f' x) integrable_on {a..c}\<close> for n
        using integrable_diff[OF ff'n_int_c f'_int_c] .
      \<comment> \<open>The norm of the difference is integrable on {a..b} (absolute integrability).\<close>
      have ff'n_int: \<open>ff' n integrable_on {a..b}\<close> for n
        using ff'_cont_ab integrable_continuous_real by blast
      have diff_int: \<open>(\<lambda>x. ff' n x - f' x) integrable_on {a..b}\<close> for n
        using integrable_diff[OF ff'n_int f'_int] .
      have norm_f': \<open>(\<lambda>x. norm (f' x)) integrable_on {a..b}\<close>
        using f'abs absolutely_integrable_on_def by blast
      have norm_ff'n: \<open>(\<lambda>x. norm (ff' n x)) integrable_on {a..b}\<close> for n
        using ff' absolutely_integrable_on_def by blast
      have norm_sum: \<open>(\<lambda>x. norm (f' x) + norm (ff' n x)) integrable_on {a..b}\<close> for n
        using integrable_add[OF norm_f' norm_ff'n] .
      have norm_diff_int: \<open>(\<lambda>x. norm (f' x - ff' n x)) integrable_on {a..b}\<close> for n
        by (metis absolutely_integrable_on_def assms(3) ff' set_integral_diff(1))
      \<comment> \<open>Key bound: \<Parallel>ff n c - f c\<Parallel> \<le> \<integral>{a..b} \<Parallel>f' - ff' n\<Parallel>.\<close>
      have bound: \<open>norm (ff n c - f c) \<le> integral {a..b} (\<lambda>x. norm (f' x - ff' n x))\<close> for n
      proof -
        have eq: \<open>ff n c - f c = integral {a..c} (\<lambda>x. ff' n x - f' x)\<close>
          unfolding ff_def using f_eq[OF c_ab] integral_diff[OF ff'n_int_c f'_int_c] by simp
        have norm_diff_int_c: \<open>(\<lambda>x. norm (f' x - ff' n x)) integrable_on {a..c}\<close>
          using integrable_on_subinterval[OF norm_diff_int ac_sub] .
        have \<open>norm (integral {a..c} (\<lambda>x. ff' n x - f' x))
              \<le> integral {a..c} (\<lambda>x. norm (ff' n x - f' x))\<close>
          using integral_norm_bound_integral[OF diff_int_c norm_diff_int_c]
          by (simp add: norm_minus_commute)
        also have \<open>\<dots> = integral {a..c} (\<lambda>x. norm (f' x - ff' n x))\<close>
          by (simp add: norm_minus_commute)
        also have \<open>\<dots> \<le> integral {a..b} (\<lambda>x. norm (f' x - ff' n x))\<close>
          using integral_subset_le[OF ac_sub norm_diff_int_c norm_diff_int] by simp
        finally show ?thesis unfolding eq .
      qed
      have \<open>(\<lambda>n. ff n c - f c) \<longlonglongrightarrow> 0\<close>
      proof (rule Lim_null_comparison[OF _ ff'_L1])
        show \<open>\<forall>\<^sub>F n in sequentially. norm (ff n c - f c) \<le> integral {a..b} (\<lambda>x. norm (f' x - ff' n x))\<close>
          using bound by (simp add: eventually_sequentially)
      qed
      then show ?thesis
        using LIM_zero_iff by blast
    qed
    have gg_ptwise: \<open>(\<lambda>n. gg n c) \<longlonglongrightarrow> g c\<close> if c_ab: \<open>c \<in> {a..b}\<close> for c
    proof -
      have ac_sub: \<open>{a..c} \<subseteq> {a..b}\<close> using c_ab by auto
      have gg'n_int_c: \<open>gg' n integrable_on {a..c}\<close> for n
        using gg'_cont_ab integrable_continuous_real integrable_on_subinterval ac_sub by blast
      have g'_int_c: \<open>g' integrable_on {a..c}\<close>
        using g'_int integrable_on_subinterval ac_sub by blast
      have diff_int_c: \<open>(\<lambda>x. gg' n x - g' x) integrable_on {a..c}\<close> for n
        using integrable_diff[OF gg'n_int_c g'_int_c] .
      have gg'n_int: \<open>gg' n integrable_on {a..b}\<close> for n
        using gg'_cont_ab integrable_continuous_real by blast
      have diff_int: \<open>(\<lambda>x. gg' n x - g' x) integrable_on {a..b}\<close> for n
        using integrable_diff[OF gg'n_int g'_int] .
      have norm_g': \<open>(\<lambda>x. norm (g' x)) integrable_on {a..b}\<close>
        using g'abs absolutely_integrable_on_def by blast
      have norm_gg'n: \<open>(\<lambda>x. norm (gg' n x)) integrable_on {a..b}\<close> for n
        using gg' absolutely_integrable_on_def by blast
      have norm_sum: \<open>(\<lambda>x. norm (g' x) + norm (gg' n x)) integrable_on {a..b}\<close> for n
        using integrable_add[OF norm_g' norm_gg'n] .
      have norm_diff_int: \<open>(\<lambda>x. norm (g' x - gg' n x)) integrable_on {a..b}\<close> for n
        by (metis absolutely_integrable_on_def assms(4) gg' set_integral_diff(1))
      have bound: \<open>norm (gg n c - g c) \<le> integral {a..b} (\<lambda>x. norm (g' x - gg' n x))\<close> for n
      proof -
        have eq: \<open>gg n c - g c = integral {a..c} (\<lambda>x. gg' n x - g' x)\<close>
          unfolding gg_def using g_eq[OF c_ab] integral_diff[OF gg'n_int_c g'_int_c] by simp
        have norm_diff_int_c: \<open>(\<lambda>x. norm (g' x - gg' n x)) integrable_on {a..c}\<close>
          using integrable_on_subinterval[OF norm_diff_int ac_sub] .
        have \<open>norm (integral {a..c} (\<lambda>x. gg' n x - g' x))
              \<le> integral {a..c} (\<lambda>x. norm (gg' n x - g' x))\<close>
          using integral_norm_bound_integral[OF diff_int_c norm_diff_int_c]
          by (simp add: norm_minus_commute)
        also have \<open>\<dots> = integral {a..c} (\<lambda>x. norm (g' x - gg' n x))\<close>
          by (simp add: norm_minus_commute)
        also have \<open>\<dots> \<le> integral {a..b} (\<lambda>x. norm (g' x - gg' n x))\<close>
          using integral_subset_le[OF ac_sub norm_diff_int_c norm_diff_int] by simp
        finally show ?thesis unfolding eq .
      qed
      have \<open>(\<lambda>n. gg n c - g c) \<longlonglongrightarrow> 0\<close>
      proof (rule Lim_null_comparison[OF _ gg'_L1])
        show \<open>\<forall>\<^sub>F n in sequentially. norm (gg n c - g c) \<le> integral {a..b} (\<lambda>x. norm (g' x - gg' n x))\<close>
          using bound by (simp add: eventually_sequentially)
      qed
      then show ?thesis
        by (simp add: LIM_zero_iff)
    qed
    have \<open>(\<lambda>n. bop (ff n c) (gg n c)) \<longlonglongrightarrow> bop (f c) (g c)\<close> if c_ab: \<open>c \<in> {a..b}\<close> for c
      using bb bounded_bilinear.tendsto c_ab ff_ptwise gg_ptwise by blast
    then have *: \<open>(\<lambda>n. bop (ff n b) (gg n b) - bop (ff n a) (gg n a)) 
         \<longlonglongrightarrow> bop (f b) (g b) - bop (f a) (g a)\<close> 



    \<comment> \<open>Uniform convergence: ff n \<rightarrow> f and gg n \<rightarrow> g uniformly on {a..b}.\<close>
      by (simp add: assms(2) tendsto_diff)
    have ff_uniform: \<open>(\<lambda>n. SUP x\<in>{a..b}. norm (ff n x - f x)) \<longlonglongrightarrow> 0\<close>
    proof (rule Lim_null_comparison[OF _ ff'_L1])
      show \<open>\<forall>\<^sub>F n in sequentially. norm (SUP x\<in>{a..b}. norm (ff n x - f x))
            \<le> integral {a..b} (\<lambda>x. norm (f' x - ff' n x))\<close>
      proof (intro always_eventually allI)
        fix n
        have ne: \<open>{a..b} \<noteq> {}\<close> using ab by auto
        have ff'n_int: \<open>ff' n integrable_on {a..b}\<close>
          using ff'_cont_ab integrable_continuous_real by blast
        have diff_int: \<open>(\<lambda>x. ff' n x - f' x) integrable_on {a..b}\<close>
          using integrable_diff[OF ff'n_int f'_int] .
        have norm_diff_int: \<open>(\<lambda>x. norm (f' x - ff' n x)) integrable_on {a..b}\<close>
          by (metis absolutely_integrable_on_def f'abs ff' set_integral_diff(1))
        \<comment> \<open>Pointwise bound for each x \<in> {a..b}.\<close>
        have bound: \<open>norm (ff n x - f x) \<le> integral {a..b} (\<lambda>t. norm (f' t - ff' n t))\<close>
          if \<open>x \<in> {a..b}\<close> for x
        proof -
          have ac_sub: \<open>{a..x} \<subseteq> {a..b}\<close> using that by auto
          have ff'n_int_x: \<open>ff' n integrable_on {a..x}\<close>
            using integrable_on_subinterval[OF ff'n_int ac_sub] .
          have f'_int_x: \<open>f' integrable_on {a..x}\<close>
            using integrable_on_subinterval[OF f'_int ac_sub] .
          have diff_int_x: \<open>(\<lambda>t. ff' n t - f' t) integrable_on {a..x}\<close>
            using integrable_diff[OF ff'n_int_x f'_int_x] .
          have norm_diff_int_x: \<open>(\<lambda>t. norm (f' t - ff' n t)) integrable_on {a..x}\<close>
            using integrable_on_subinterval[OF norm_diff_int ac_sub] .
          have \<open>norm (ff n x - f x) = norm (integral {a..x} (ff' n) - integral {a..x} f')\<close>
            unfolding ff_def using f_eq[OF that] by simp
          also have \<open>\<dots> = norm (integral {a..x} (\<lambda>t. ff' n t - f' t))\<close>
            using integral_diff[OF ff'n_int_x f'_int_x] by simp
          also have \<open>\<dots> \<le> integral {a..x} (\<lambda>t. norm (ff' n t - f' t))\<close>
            using integral_norm_bound_integral[OF diff_int_x norm_diff_int_x]
            by (simp add: norm_minus_commute)
          also have \<open>\<dots> = integral {a..x} (\<lambda>t. norm (f' t - ff' n t))\<close>
            by (simp add: norm_minus_commute)
          also have \<open>\<dots> \<le> integral {a..b} (\<lambda>t. norm (f' t - ff' n t))\<close>
            using integral_subset_le[OF ac_sub norm_diff_int_x norm_diff_int] by simp
          finally show ?thesis .
        qed
        \<comment> \<open>SUP bound via cSup_least.\<close>
        have bdd: \<open>bdd_above ((\<lambda>x. norm (ff n x - f x)) ` {a..b})\<close>
        proof -
          have \<open>continuous_on {a..b} (\<lambda>x. norm (ff n x - f x))\<close>
            by (intro continuous_on_norm continuous_on_diff ff_cont f_cont)
          then have \<open>compact ((\<lambda>x. norm (ff n x - f x)) ` {a..b})\<close>
            using compact_continuous_image compact_Icc by blast
          then have \<open>bounded ((\<lambda>x. norm (ff n x - f x)) ` {a..b})\<close>
            using compact_imp_bounded by blast
          then show ?thesis using bounded_imp_bdd_above by auto
        qed
        have sup_bound: \<open>(SUP x\<in>{a..b}. norm (ff n x - f x))
              \<le> integral {a..b} (\<lambda>t. norm (f' t - ff' n t))\<close>
          using cSup_least[of \<open>(\<lambda>x. norm (ff n x - f x)) ` {a..b}\<close>] ne bound
          by (force simp: image_iff)
        have sup_nonneg: \<open>(SUP x\<in>{a..b}. norm (ff n x - f x)) \<ge> 0\<close>
        proof -
          have \<open>a \<in> {a..b}\<close> using ab by auto
          then have \<open>norm (ff n a - f a) \<le> (SUP x\<in>{a..b}. norm (ff n x - f x))\<close>
            using cSUP_upper[OF _ bdd] by blast
          then show ?thesis using norm_ge_zero[of \<open>ff n a - f a\<close>] by linarith
        qed
        show \<open>norm (SUP x\<in>{a..b}. norm (ff n x - f x))
              \<le> integral {a..b} (\<lambda>x. norm (f' x - ff' n x))\<close>
          using sup_bound sup_nonneg by simp
      qed
    qed
    have gg_uniform: \<open>(\<lambda>n. SUP x\<in>{a..b}. norm (gg n x - g x)) \<longlonglongrightarrow> 0\<close>
    proof (rule Lim_null_comparison[OF _ gg'_L1])
      show \<open>\<forall>\<^sub>F n in sequentially. norm (SUP x\<in>{a..b}. norm (gg n x - g x))
            \<le> integral {a..b} (\<lambda>x. norm (g' x - gg' n x))\<close>
      proof (intro always_eventually allI)
        fix n
        have ne: \<open>{a..b} \<noteq> {}\<close> using ab by auto
        have gg'n_int: \<open>gg' n integrable_on {a..b}\<close>
          using gg'_cont_ab integrable_continuous_real by blast
        have diff_int: \<open>(\<lambda>x. gg' n x - g' x) integrable_on {a..b}\<close>
          using integrable_diff[OF gg'n_int g'_int] .
        have norm_diff_int: \<open>(\<lambda>x. norm (g' x - gg' n x)) integrable_on {a..b}\<close>
          by (metis absolutely_integrable_on_def g'abs gg' set_integral_diff(1))
        have bound: \<open>norm (gg n x - g x) \<le> integral {a..b} (\<lambda>t. norm (g' t - gg' n t))\<close>
          if \<open>x \<in> {a..b}\<close> for x
        proof -
          have ac_sub: \<open>{a..x} \<subseteq> {a..b}\<close> using that by auto
          have gg'n_int_x: \<open>gg' n integrable_on {a..x}\<close>
            using integrable_on_subinterval[OF gg'n_int ac_sub] .
          have g'_int_x: \<open>g' integrable_on {a..x}\<close>
            using integrable_on_subinterval[OF g'_int ac_sub] .
          have diff_int_x: \<open>(\<lambda>t. gg' n t - g' t) integrable_on {a..x}\<close>
            using integrable_diff[OF gg'n_int_x g'_int_x] .
          have norm_diff_int_x: \<open>(\<lambda>t. norm (g' t - gg' n t)) integrable_on {a..x}\<close>
            using integrable_on_subinterval[OF norm_diff_int ac_sub] .
          have \<open>norm (gg n x - g x) = norm (integral {a..x} (gg' n) - integral {a..x} g')\<close>
            unfolding gg_def using g_eq[OF that] by simp
          also have \<open>\<dots> = norm (integral {a..x} (\<lambda>t. gg' n t - g' t))\<close>
            using integral_diff[OF gg'n_int_x g'_int_x] by simp
          also have \<open>\<dots> \<le> integral {a..x} (\<lambda>t. norm (gg' n t - g' t))\<close>
            using integral_norm_bound_integral[OF diff_int_x norm_diff_int_x]
            by (simp add: norm_minus_commute)
          also have \<open>\<dots> = integral {a..x} (\<lambda>t. norm (g' t - gg' n t))\<close>
            by (simp add: norm_minus_commute)
          also have \<open>\<dots> \<le> integral {a..b} (\<lambda>t. norm (g' t - gg' n t))\<close>
            using integral_subset_le[OF ac_sub norm_diff_int_x norm_diff_int] by simp
          finally show ?thesis .
        qed
        have bdd: \<open>bdd_above ((\<lambda>x. norm (gg n x - g x)) ` {a..b})\<close>
        proof -
          have \<open>continuous_on {a..b} (\<lambda>x. norm (gg n x - g x))\<close>
            by (intro continuous_on_norm continuous_on_diff gg_cont g_cont)
          then have \<open>compact ((\<lambda>x. norm (gg n x - g x)) ` {a..b})\<close>
            using compact_continuous_image compact_Icc by blast
          then have \<open>bounded ((\<lambda>x. norm (gg n x - g x)) ` {a..b})\<close>
            using compact_imp_bounded by blast
          then show ?thesis using bounded_imp_bdd_above by auto
        qed
        have sup_bound: \<open>(SUP x\<in>{a..b}. norm (gg n x - g x))
              \<le> integral {a..b} (\<lambda>t. norm (g' t - gg' n t))\<close>
          using cSup_least[of \<open>(\<lambda>x. norm (gg n x - g x)) ` {a..b}\<close>] ne bound
          by (force simp: image_iff)
        have sup_nonneg: \<open>(SUP x\<in>{a..b}. norm (gg n x - g x)) \<ge> 0\<close>
        proof -
          have \<open>a \<in> {a..b}\<close> using ab by auto
          then have \<open>norm (gg n a - g a) \<le> (SUP x\<in>{a..b}. norm (gg n x - g x))\<close>
            using cSUP_upper[OF _ bdd] by blast
          then show ?thesis using norm_ge_zero[of \<open>gg n a - g a\<close>] by linarith
        qed
        show \<open>norm (SUP x\<in>{a..b}. norm (gg n x - g x))
              \<le> integral {a..b} (\<lambda>x. norm (g' x - gg' n x))\<close>
          using sup_bound sup_nonneg by simp
      qed
    qed
    \<comment> \<open>Pointwise convergence at a and b.\<close>
    have ff_b: \<open>(\<lambda>n. ff n b) \<longlonglongrightarrow> f b\<close>
      using ff_ptwise[of b] ab by auto
    have ff_a: \<open>(\<lambda>n. ff n a) \<longlonglongrightarrow> f a\<close>
      using ff_ptwise[of a] ab by auto
    have gg_b: \<open>(\<lambda>n. gg n b) \<longlonglongrightarrow> g b\<close>
      using gg_ptwise[of b] ab by auto
    have gg_a: \<open>(\<lambda>n. gg n a) \<longlonglongrightarrow> g a\<close>
      using gg_ptwise[of a] ab by auto
    \<comment> \<open>Bilinear limit at endpoints.\<close>
    have bop_b: \<open>(\<lambda>n. bop (ff n b) (gg n b)) \<longlonglongrightarrow> bop (f b) (g b)\<close>
      using Lim_bilinear[OF ff_b gg_b bb] .
    have bop_a: \<open>(\<lambda>n. bop (ff n a) (gg n a)) \<longlonglongrightarrow> bop (f a) (g a)\<close>
      using Lim_bilinear[OF ff_a gg_a bb] .
    \<comment> \<open>Integral convergence.\<close>
    have int1: \<open>(\<lambda>n. integral {a..b} (\<lambda>x. bop (ff n x) (gg' n x))) \<longlonglongrightarrow>
               integral {a..b} (\<lambda>x. bop (f x) (g' x))\<close>
      sorry
    have int2: \<open>(\<lambda>n. integral {a..b} (\<lambda>x. bop (ff' n x) (gg n x))) \<longlonglongrightarrow>
               integral {a..b} (\<lambda>x. bop (f' x) (g x))\<close>
      sorry
    \<comment> \<open>Combine via tendsto_add and tendsto_diff.\<close>
    show ?thesis
      unfolding s_def
      using tendsto_diff[OF tendsto_add[OF int1 int2] tendsto_diff[OF bop_b bop_a]] .
  qed
  ultimately show "integral {a..b} (\<lambda>x. bop (f x) (g' x)) + integral {a..b} (\<lambda>x. bop (f' x) (g x))
       = bop (f b) (g b) - bop (f a) (g a)"
      using LIMSEQ_unique eq_iff_diff_eq_0 by blast
qed

text \<open>The real-valued specialisation: HOL Light's @{text ABSOLUTE_REAL_INTEGRATION_BY_PARTS}.\<close>

lemma absolute_real_integration_by_parts:
  fixes f g f' g' :: "real \<Rightarrow> real"
  assumes ab: "a \<le> b"
    and f'abs: "f' absolutely_integrable_on {a..b}"
    and g'abs: "g' absolutely_integrable_on {a..b}"
    and f'int: "\<And>x. x \<in> {a..b} \<Longrightarrow> (f' has_integral f x) {a..x}"
    and g'int: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g' has_integral g x) {a..x}"
  shows fg'_abs: "(\<lambda>x. f x * g' x) absolutely_integrable_on {a..b}"
    and f'g_abs: "(\<lambda>x. f' x * g x) absolutely_integrable_on {a..b}"
    and ibp_eq: "integral {a..b} (\<lambda>x. f x * g' x) +
      integral {a..b} (\<lambda>x. f' x * g x) = f b * g b - f a * g a"
  using absolute_integration_by_parts[OF bilinear_times ab f'abs g'abs f'int g'int]
  by auto

text \<open>Integration by parts for absolutely integrable functions (shifted / sum version).
  Bilinear generalisation: HOL Light's @{text ABSOLUTE_INTEGRATION_BY_PARTS_SUM}.\<close>

theorem absolute_integration_by_parts_sum:
  fixes bop :: \<open>'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::euclidean_space\<close>
    and f :: \<open>real \<Rightarrow> 'a\<close> and g :: \<open>real \<Rightarrow> 'b\<close>
    and f' :: \<open>real \<Rightarrow> 'a\<close> and g' :: \<open>real \<Rightarrow> 'b\<close>
    and a b :: real
  assumes bop: \<open>bilinear bop\<close>
    and ab: \<open>a \<le> b\<close>
    and f'abs: \<open>f' absolutely_integrable_on {a..b}\<close>
    and g'abs: \<open>g' absolutely_integrable_on {a..b}\<close>
    and f'int: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> (f' has_integral (f x - f a)) {a..x}\<close>
    and g'int: \<open>\<And>x. x \<in> {a..b} \<Longrightarrow> (g' has_integral (g x - g a)) {a..x}\<close>
  shows \<open>(\<lambda>x. bop (f x) (g' x) + bop (f' x) (g x)) absolutely_integrable_on {a..b}\<close>
    and \<open>\<And>x. x \<in> {a..b} \<Longrightarrow>
      ((\<lambda>x. bop (f x) (g' x) + bop (f' x) (g x))
        has_integral (bop (f x) (g x) - bop (f a) (g a))) {a..x}\<close>

  sorry


text \<open>Helper: the indefinite integral of an absolutely integrable function
  is absolutely continuous.\<close>

lemma indefinite_integral_absolutely_continuous:
  fixes f' :: "real \<Rightarrow> real"
  assumes ab: "a \<le> b" and f'abs: "f' absolutely_integrable_on {a..b}"
  shows "absolutely_continuous_on {a..b} (\<lambda>x. integral {a..x} f')"
unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
proof (intro allI impI)
  fix \<epsilon> :: real assume "\<epsilon> > 0"
  have nf'_int: "(\<lambda>x. norm (f' x)) integrable_on {a..b}"
    using f'abs unfolding absolutely_integrable_on_def by simp
  have f'_int: "f' integrable_on {a..b}"
    using f'abs absolutely_integrable_on_def by blast
  \<comment> \<open>Truncation approach: split |f'| into bounded and tail parts.\<close>
  define I where "I = integral {a..b} (\<lambda>x. norm (f' x))"
  \<comment> \<open>For any M > 0, the tail integral \<integral> max(|f'| - M, 0) can be made small.\<close>
  \<comment> \<open>Since min(|f'|, M) \<le> M, we have \<integral>_k min(|f'|, M) \<le> M * content(k).\<close>
  \<comment> \<open>And norm(\<integral>_k f') \<le> \<integral>_k |f'| = \<integral>_k min(|f'|, M) + \<integral>_k max(|f'| - M, 0).\<close>
  \<comment> \<open>Choose M so that \<integral>_{a..b} max(|f'| - M, 0) < \<epsilon>/2, then \<delta> = \<epsilon>/(2M).\<close>
  have tail_small: "\<exists>M>0. integral {a..b} (\<lambda>x. max (norm (f' x) - M) 0) < \<epsilon> / 2"
  proof -
    \<comment> \<open>max(|f'(x)| - M, 0) \<le> |f'(x)| and \<rightarrow> 0 pointwise, so integral \<rightarrow> 0 by DCT.\<close>
    sorry
  qed
  then obtain M where "M > 0"
    and tail: "integral {a..b} (\<lambda>x. max (norm (f' x) - M) 0) < \<epsilon> / 2"
    by auto
  define \<delta> where "\<delta> = \<epsilon> / (2 * M)"
  have "\<delta> > 0" using \<open>\<epsilon> > 0\<close> \<open>M > 0\<close> unfolding \<delta>_def by simp
  show "\<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> {a..b} \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
    (\<Sum>k\<in>d. norm (integral {a..Sup k} f' - integral {a..Inf k} f')) < \<epsilon>"
  proof (intro exI conjI allI impI)
    show "\<delta> > 0" by fact
    fix d t assume dt: "d division_of t \<and> t \<subseteq> {a..b} \<and> (\<Sum>k\<in>d. content k) < \<delta>"
    then have div: "d division_of t" and sub: "t \<subseteq> {a..b}"
      and content_bound: "(\<Sum>k\<in>d. content k) < \<delta>" by auto
    \<comment> \<open>Each interval in the division satisfies integral {a..Sup k} - integral {a..Inf k} = integral {Inf k..Sup k}\<close>
    sorry
  qed
qed



text \<open>The real-valued shifted version:
  HOL Light's @{text ABSOLUTE_REAL_INTEGRATION_BY_PARTS_SUM}.\<close>

lemma absolute_real_integration_by_parts_sum:
  fixes f g f' g' :: "real \<Rightarrow> real"
  assumes ab: "a \<le> b"
    and f'abs: "f' absolutely_integrable_on {a..b}"
    and g'abs: "g' absolutely_integrable_on {a..b}"
    and f'int: "\<And>x. x \<in> {a..b} \<Longrightarrow> (f' has_integral (f x - f a)) {a..x}"
    and g'int: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g' has_integral (g x - g a)) {a..x}"
  shows fgsum_abs: "(\<lambda>x. f x * g' x + f' x * g x) absolutely_integrable_on {a..b}"
    and fgsum_int: "\<And>x. x \<in> {a..b} \<Longrightarrow>
      ((\<lambda>x. f x * g' x + f' x * g x) has_integral (f x * g x - f a * g a)) {a..x}"
proof -
  \<comment> \<open>Apply IBP with shifted antiderivatives F x = f x - f a, G x = g x - g a.\<close>
  define F where "F \<equiv> \<lambda>x. f x - f a"
  define G where "G \<equiv> \<lambda>x. g x - g a"
  have F_int: "\<And>x. x \<in> {a..b} \<Longrightarrow> (f' has_integral F x) {a..x}"
    unfolding F_def using f'int by simp
  have G_int: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g' has_integral G x) {a..x}"
    unfolding G_def using g'int by simp
  note ibp = absolute_real_integration_by_parts[OF ab f'abs g'abs F_int G_int]
  \<comment> \<open>IBP gives us three facts about F and G.\<close>
  have Fg'_abs: "(\<lambda>x. F x * g' x) absolutely_integrable_on {a..b}" using ibp(1) .
  have f'G_abs: "(\<lambda>x. f' x * G x) absolutely_integrable_on {a..b}" using ibp(2) .
  have ibp_eq: "integral {a..b} (\<lambda>x. F x * g' x) + integral {a..b} (\<lambda>x. f' x * G x) = F b * G b - F a * G a"
    using ibp(3) .
  \<comment> \<open>Constant-multiple terms are absolutely integrable.\<close>
  have cg'_abs: "(\<lambda>x. f a * g' x) absolutely_integrable_on {a..b}"
    using absolutely_integrable_scaleR_left[OF g'abs, of "f a"]
    by (simp add: scaleR_conv_of_real)
  have f'c_abs: "(\<lambda>x. f' x * g a) absolutely_integrable_on {a..b}"
    using absolutely_integrable_scaleR_right[OF f'abs, of "g a"]
    by (simp add: scaleR_conv_of_real)
  \<comment> \<open>Each component is integrable.\<close>
  have Fg'_int: "(\<lambda>x. F x * g' x) integrable_on {a..b}"
    using Fg'_abs set_lebesgue_integral_eq_integral by blast
  have f'G_int: "(\<lambda>x. f' x * G x) integrable_on {a..b}"
    using f'G_abs set_lebesgue_integral_eq_integral by blast
  have cg'_int: "(\<lambda>x. f a * g' x) integrable_on {a..b}"
    using cg'_abs set_lebesgue_integral_eq_integral by blast
  have f'c_int: "(\<lambda>x. f' x * g a) integrable_on {a..b}"
    using f'c_abs set_lebesgue_integral_eq_integral by blast
  \<comment> \<open>The norm of each component is integrable.\<close>
  have Fg'_norm: "(\<lambda>x. norm (F x * g' x)) integrable_on {a..b}"
    using Fg'_abs absolutely_integrable_on_def by blast
  have f'G_norm: "(\<lambda>x. norm (f' x * G x)) integrable_on {a..b}"
    using f'G_abs absolutely_integrable_on_def by blast
  have cg'_norm: "(\<lambda>x. norm (f a * g' x)) integrable_on {a..b}"
    using cg'_abs absolutely_integrable_on_def by blast
  have f'c_norm: "(\<lambda>x. norm (f' x * g a)) integrable_on {a..b}"
    using f'c_abs absolutely_integrable_on_def by blast
  \<comment> \<open>The decomposition: f x * g' x + f' x * g x = F x * g' x + f a * g' x + f' x * G x + f' x * g a.\<close>
  have decomp: "\<And>x. f x * g' x + f' x * g x = F x * g' x + f a * g' x + (f' x * G x + f' x * g a)"
    unfolding F_def G_def by (simp add: algebra_simps)
  \<comment> \<open>Sum is integrable.\<close>
  have sum_int: "(\<lambda>x. f x * g' x + f' x * g x) integrable_on {a..b}"
    unfolding decomp using integrable_add[OF integrable_add[OF Fg'_int cg'_int] integrable_add[OF f'G_int f'c_int]] .
  \<comment> \<open>Norm bound: |f x * g' x + f' x * g x| \<le> |F x * g' x| + |f a * g' x| + |f' x * G x| + |f' x * g a|.\<close>
  have bound_int: "(\<lambda>x. norm (F x * g' x) + norm (f a * g' x) + (norm (f' x * G x) + norm (f' x * g a))) integrable_on {a..b}"
    using integrable_add[OF integrable_add[OF Fg'_norm cg'_norm] integrable_add[OF f'G_norm f'c_norm]] .
  have norm_bound: "\<And>x. x \<in> {a..b} \<Longrightarrow> norm (f x * g' x + f' x * g x) \<le>
    norm (F x * g' x) + norm (f a * g' x) + (norm (f' x * G x) + norm (f' x * g a))"
    unfolding decomp by (intro order_trans[OF norm_triangle_ineq] add_mono order_trans[OF norm_triangle_ineq] order_refl)+
  show fgsum_abs: "(\<lambda>x. f x * g' x + f' x * g x) absolutely_integrable_on {a..b}"
    by (rule absolutely_integrable_integrable_bound[OF norm_bound sum_int bound_int])
  \<comment> \<open>Goal 2: has_integral on {a..x} for each x \<in> {a..b}.\<close>
  show "\<And>x. x \<in> {a..b} \<Longrightarrow>
    ((\<lambda>x. f x * g' x + f' x * g x) has_integral (f x * g x - f a * g a)) {a..x}"
  proof -
    fix x assume xab: "x \<in> {a..b}"
    hence ax: "a \<le> x" and xb: "x \<le> b" by auto
    have sub: "{a..x} \<subseteq> {a..b}" using xb by auto
    \<comment> \<open>Absolute integrability on the subinterval.\<close>
    have f'abs_sub: "f' absolutely_integrable_on {a..x}"
      using absolutely_integrable_on_subinterval[OF f'abs sub] .
    have g'abs_sub: "g' absolutely_integrable_on {a..x}"
      using absolutely_integrable_on_subinterval[OF g'abs sub] .
    \<comment> \<open>has_integral results on {a..x}.\<close>
    have F_int_sub: "\<And>y. y \<in> {a..x} \<Longrightarrow> (f' has_integral F y) {a..y}"
      using F_int sub by auto
    have G_int_sub: "\<And>y. y \<in> {a..x} \<Longrightarrow> (g' has_integral G y) {a..y}"
      using G_int sub by auto
    \<comment> \<open>Apply IBP on {a..x}.\<close>
    note ibp_sub = absolute_real_integration_by_parts[OF ax f'abs_sub g'abs_sub F_int_sub G_int_sub]
    \<comment> \<open>From IBP: integral of F * g' + f' * G on {a..x} = F x * G x - F a * G a = F x * G x.\<close>
    have Fg'_int_sub: "(\<lambda>t. F t * g' t) integrable_on {a..x}"
      using ibp_sub(1) set_lebesgue_integral_eq_integral by blast
    have f'G_int_sub: "(\<lambda>t. f' t * G t) integrable_on {a..x}"
      using ibp_sub(2) set_lebesgue_integral_eq_integral by blast
    have ibp_eq_sub: "integral {a..x} (\<lambda>t. F t * g' t) + integral {a..x} (\<lambda>t. f' t * G t) = F x * G x - F a * G a"
      using ibp_sub(3) .
    \<comment> \<open>F a = 0 and G a = 0.\<close>
    have Fa: "F a = 0" unfolding F_def by simp
    have Ga: "G a = 0" unfolding G_def by simp
    \<comment> \<open>Combine: has_integral of F * g' + f' * G on {a..x} gives F x * G x.\<close>
    have hi_FG: "((\<lambda>t. F t * g' t + f' t * G t) has_integral (F x * G x)) {a..x}"
      using has_integral_add[OF integrable_integral[OF Fg'_int_sub] integrable_integral[OF f'G_int_sub]]
        ibp_eq_sub Fa Ga by simp
    \<comment> \<open>has_integral for constant-multiple terms.\<close>
    have hi_cg: "((\<lambda>t. f a * g' t) has_integral (f a * (g x - g a))) {a..x}"
      using has_integral_mult_right[OF g'int[OF xab]] unfolding G_def by simp
    have hi_fc: "((\<lambda>t. f' t * g a) has_integral ((f x - f a) * g a)) {a..x}"
      using has_integral_mult_left[OF f'int[OF xab]] unfolding F_def by simp
    \<comment> \<open>Combine all four terms.\<close>
    have hi_const: "((\<lambda>t. f a * g' t + f' t * g a) has_integral (f a * (g x - g a) + (f x - f a) * g a)) {a..x}"
      using has_integral_add[OF hi_cg hi_fc] .
    have hi_sum: "((\<lambda>t. (F t * g' t + f' t * G t) + (f a * g' t + f' t * g a))
      has_integral (F x * G x + (f a * (g x - g a) + (f x - f a) * g a))) {a..x}"
      using has_integral_add[OF hi_FG hi_const] .
    \<comment> \<open>Rewrite to match the goal.\<close>
    have eq_fn: "\<And>t. (F t * g' t + f' t * G t) + (f a * g' t + f' t * g a) = f t * g' t + f' t * g t"
      unfolding F_def G_def by (simp add: algebra_simps)
    have eq_val: "F x * G x + (f a * (g x - g a) + (f x - f a) * g a) = f x * g x - f a * g a"
      unfolding F_def G_def by (simp add: algebra_simps)
    show "((\<lambda>x. f x * g' x + f' x * g x) has_integral (f x * g x - f a * g a)) {a..x}"
      using hi_sum unfolding eq_fn eq_val .
  qed
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
    show \<open>\<And>x. x \<in> {0..2*pi} \<Longrightarrow> norm (f' x) \<le> 1 + (f' x)\<^sup>2\<close>
    proof -
      fix x :: real
      have \<open>0 \<le> (1 - f' x)\<^sup>2\<close> and \<open>0 \<le> (1 + f' x)\<^sup>2\<close>
        by (auto simp: power2_eq_square)
      then show \<open>norm (f' x) \<le> 1 + (f' x)\<^sup>2\<close>
        by (auto simp: power2_eq_square abs_le_iff real_norm_def algebra_simps)
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
      proof cases
        case 1
        then have "0 \<le> g pi" using geq by linarith
        then show ?thesis using mem_is_interval_1_I [OF iv g0 gpi, of 0] 1 by auto
      next
        case 2
        then have "0 \<le> g 0" using geq by linarith
        then show ?thesis using mem_is_interval_1_I [OF iv gpi g0, of 0] 2 by auto
      qed
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

  show "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    sorry
  show "\<exists>c a. \<forall>x \<in> {0..2*pi}. f x = c * sin (x - a)"
    if "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    sorry
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
  sorry 

section \<open>Part 2: Green's theorem for convex area\<close>

text \<open>Area under/above an arc, and the signed area formula for a convex closed curve.\<close>

lemma area_below_arclet:
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
  assumes "u \<le> v"
    and "Re (g u) \<le> Re (g v)"
    and "absolutely_continuous_on {u..v} g"
    and "g ` {u..v} \<subseteq> {z. Im z \<ge> 0}"
    and "inj_on g {u..v}"
    and "\<And>x y. x \<in> g ` {u..v} \<Longrightarrow> y \<in> g ` {u..v} \<Longrightarrow> Re x = Re y \<Longrightarrow> x = y"
    and "negligible S"
    and "\<And>t. t \<in> {u..v} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
    and "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
  sorry 

lemma area_above_arclet:
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
  assumes "u \<le> v"
    and "Re (g v) \<le> Re (g u)"
    and "absolutely_continuous_on g {u..v}"
    and "g ` {u..v} \<subseteq> {z. Im z \<le> 0}"
    and "inj_on g {u..v}"
    and "\<And>x y. x \<in> g ` {u..v} \<Longrightarrow> y \<in> g ` {u..v} \<Longrightarrow> Re x = Re y \<Longrightarrow> x = y"
    and "negligible S"
    and "\<And>t. t \<in> {u..v} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
    and "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
  sorry

theorem green_area_theorem:
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
    and a b :: "complex"
  assumes "simple_path g" "pathstart g = a" "pathfinish g = a"
    and "b \<in> path_image g" "Re a < Re b" "Im a = Im b"
    and "dist a b = diameter (path_image g)"
    and "convex (inside (path_image g))"
    and "absolutely_continuous_on g {0..1}"
    and "negligible U"
    and "\<And>t. t \<in> {0..1} - U \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {0..1}"
    and "\<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> =
      measure (inside (path_image g))"
  sorry

section \<open>Part 3: Isoperimetric theorem for convex curves\<close>

theorem isoperimetric_theorem_convex:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "convex (inside (path_image g))"
    "path_length g = L"
  shows "measure (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
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
    measure (inside (path_image g)) < measure (inside (path_image h))"
  sorry

section \<open>Part 5: The isoperimetric theorem\<close>

theorem isoperimetric_theorem:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "path_length g = L"
  shows "measure (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
      \<exists>a r. path_image g = sphere a r"
  sorry

end
