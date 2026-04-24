(*  Title:      HOL/Analysis/Change_Of_Vars.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section\<open>Change of Variables Theorems\<close>

theory Change_Of_Vars_EU
  imports "HOL-Analysis.Vitali_Covering_Theorem" "HOL-Analysis.Determinants" 
          "Determinant_Linear_Function" "Euclidean_Space_Transfer" 
          Isar_Explore "HOL-ex.Sketch_and_Explore" 

begin

hide_const (open) Polynomial.content

lemma 
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "linear f" "S \<in> lmeasurable"
  shows measurable_linear_image_eu: "f ` S \<in> lmeasurable"
    and measure_linear_image_eu: "measure lebesgue (f ` S) = \<bar>eucl.det f\<bar> * measure lebesgue S"
proof -
  have meq: "measure lebesgue (f ` cbox a b) = \<bar>eucl.det f\<bar> * measure lebesgue (cbox a b)" for a b
    using Euclidean_Space_Transfer.measure_linear_image[OF assms(1)] by auto
  show "f ` S \<in> lmeasurable" "measure lebesgue (f ` S) = \<bar>eucl.det f\<bar> * measure lebesgue S"
    using measure_linear_sufficient [OF assms(1) assms(2) meq] by metis+
qed

lemma
 fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes f: "orthogonal_transformation f" and S: "S \<in> lmeasurable"
  shows measurable_orthogonal_image_eu: "f ` S \<in> lmeasurable"
    and measure_orthogonal_image_eu: "measure lebesgue (f ` S) = \<bar>eucl.det f\<bar> * measure lebesgue S"
proof -
  have "linear f"
    by (simp add: f orthogonal_transformation_linear)
  then show "f ` S \<in> lmeasurable"
    by (metis S measurable_linear_image_eu)
  show "measure lebesgue (f ` S) = \<bar>eucl.det f\<bar> * measure lebesgue S"
    using S f \<open>linear f\<close> measure_linear_image_eu by blast
qed

proposition measure_semicontinuous_with_hausdist_explicit:
  assumes "bounded S" and neg: "negligible(frontier S)" and "e > 0"
  obtains d where "d > 0"
                  "\<And>T. \<lbrakk>T \<in> lmeasurable; \<And>y. y \<in> T \<Longrightarrow> \<exists>x. x \<in> S \<and> dist x y < d\<rbrakk>
                        \<Longrightarrow> measure lebesgue T < measure lebesgue S + e"
proof (cases "S = {}")
  case True
  with that \<open>e > 0\<close> show ?thesis by force
next
  case False
  then have frS: "frontier S \<noteq> {}"
    using \<open>bounded S\<close> frontier_eq_empty not_bounded_UNIV by blast
  have "S \<in> lmeasurable"
    by (simp add: \<open>bounded S\<close> measurable_Jordan neg)
  have null: "(frontier S) \<in> null_sets lebesgue"
    by (metis neg negligible_iff_null_sets)
  have "frontier S \<in> lmeasurable" and mS0: "measure lebesgue (frontier S) = 0"
    using neg negligible_imp_measurable negligible_iff_measure by blast+
  with \<open>e > 0\<close> sets_lebesgue_outer_open
  obtain U where "open U"
    and U: "frontier S \<subseteq> U" "U - frontier S \<in> lmeasurable" "emeasure lebesgue (U - frontier S) < e"
    by (metis fmeasurableD)
  with null have "U \<in> lmeasurable"
    by (metis borel_open measurable_Diff_null_set sets_completionI_sets sets_lborel)
  have "measure lebesgue (U - frontier S) = measure lebesgue U"
    using mS0 by (simp add: \<open>U \<in> lmeasurable\<close> fmeasurableD measure_Diff_null_set null)
  with U have mU: "measure lebesgue U < e"
    by (simp add: emeasure_eq_measure2 ennreal_less_iff)
  show ?thesis
  proof
    have "U \<noteq> UNIV"
      using \<open>U \<in> lmeasurable\<close> by auto
    then have "- U \<noteq> {}"
      by blast
    with \<open>open U\<close> \<open>frontier S \<subseteq> U\<close> show "setdist (frontier S) (- U) > 0"
      by (auto simp: \<open>bounded S\<close> open_closed compact_frontier_bounded setdist_gt_0_compact_closed frS)
    fix T
    assume "T \<in> lmeasurable"
      and T: "\<And>t. t \<in> T \<Longrightarrow> \<exists>y. y \<in> S \<and> dist y t < setdist (frontier S) (- U)"
    then have "measure lebesgue T - measure lebesgue S \<le> measure lebesgue (T - S)"
      by (simp add: \<open>S \<in> lmeasurable\<close> measure_diff_le_measure_setdiff)
    also have "\<dots>  \<le> measure lebesgue U"
    proof -
      have "T - S \<subseteq> U"
      proof clarify
        fix x
        assume "x \<in> T" and "x \<notin> S"
        then obtain y where "y \<in> S" and y: "dist y x < setdist (frontier S) (- U)"
          using T by blast
        have "closed_segment x y \<inter> frontier S \<noteq> {}"
          using connected_Int_frontier \<open>x \<notin> S\<close> \<open>y \<in> S\<close> by blast
        then obtain z where z: "z \<in> closed_segment x y" "z \<in> frontier S"
          by auto
        with y have "dist z x < setdist(frontier S) (- U)"
          by (auto simp: dist_commute dest!: dist_in_closed_segment)
        with z have False if "x \<in> -U"
          using setdist_le_dist [OF \<open>z \<in> frontier S\<close> that] by auto
        then show "x \<in> U"
          by blast
      qed
      then show ?thesis
        by (simp add: \<open>S \<in> lmeasurable\<close> \<open>T \<in> lmeasurable\<close> \<open>U \<in> lmeasurable\<close> fmeasurableD measure_mono_fmeasurable sets.Diff)
    qed
    finally have "measure lebesgue T - measure lebesgue S \<le> measure lebesgue U" .
    with mU show "measure lebesgue T < measure lebesgue S + e"
      by linarith
  qed
qed

proposition
 fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes S: "S \<in> lmeasurable"
  and deriv: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  and int: "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) integrable_on S"
  and bounded: "\<And>x. x \<in> S \<Longrightarrow> \<bar>eucl.det (f' x)\<bar> \<le> B"
  shows measurable_bounded_differentiable_image_eu:
       "f ` S \<in> lmeasurable"
    and measure_bounded_differentiable_image_eu:
       "measure lebesgue (f ` S) \<le> B * measure lebesgue S" (is "?M")
proof -
  have "f ` S \<in> lmeasurable \<and> measure lebesgue (f ` S) \<le> B * measure lebesgue S"
  proof (cases "B < 0")
    case True
    then have "S = {}"
      by (meson abs_ge_zero bounded empty_iff equalityI less_le_trans linorder_not_less subsetI)
    then show ?thesis
      by auto
  next
    case False
    then have "B \<ge> 0"
      by arith
    let ?\<mu> = "measure lebesgue"
    have f_diff: "f differentiable_on S"
      using deriv by (auto simp: differentiable_on_def differentiable_def)
    have eps: "f ` S \<in> lmeasurable" "?\<mu> (f ` S) \<le> (B+e) * ?\<mu> S" (is "?ME")
              if "e > 0" for e
    proof -
      have eps_d: "f ` S \<in> lmeasurable"  "?\<mu> (f ` S) \<le> (B+e) * (?\<mu> S + d)" (is "?MD")
                  if "d > 0" for d
      proof -
        obtain T where T: "open T" "S \<subseteq> T" and TS: "(T-S) \<in> lmeasurable" and "emeasure lebesgue (T-S) < ennreal d"
          using S \<open>d > 0\<close> sets_lebesgue_outer_open by blast
        then have "?\<mu> (T-S) < d"
          by (metis emeasure_eq_measure2 ennreal_leI not_less)
        with S T TS have "T \<in> lmeasurable" and Tless: "?\<mu> T < ?\<mu> S + d"
          by (auto simp: measurable_measure_Diff dest!: fmeasurable_Diff_D)
        have "\<exists>r. 0 < r \<and> r < d \<and> ball x r \<subseteq> T \<and> f ` (S \<inter> ball x r) \<in> lmeasurable \<and>
                  ?\<mu> (f ` (S \<inter> ball x r)) \<le> (B + e) * ?\<mu> (ball x r)"
          if "x \<in> S" "d > 0" for x d
        proof -
          have lin: "linear (f' x)"
            and lim0: "((\<lambda>y. (f y - (f x + f' x (y - x))) /\<^sub>R norm(y - x)) \<longlongrightarrow> 0) (at x within S)"
            using deriv \<open>x \<in> S\<close> by (auto simp: has_derivative_within bounded_linear.linear field_simps)
          have bo: "bounded (f' x ` ball 0 1)"
            by (simp add: bounded_linear_image linear_linear lin)
          have neg: "negligible (frontier (f' x ` ball 0 1))"
            using deriv has_derivative_linear \<open>x \<in> S\<close>
            by (auto intro!: negligible_convex_frontier [OF convex_linear_image])
          let ?unit_vol = "Henstock_Kurzweil_Integration.content (ball (0 :: 'a) 1)"
          have 0: "0 < e * ?unit_vol"
            using \<open>e > 0\<close> by (simp add: content_ball_pos)
          obtain k where "k > 0" and k:
                  "\<And>U. \<lbrakk>U \<in> lmeasurable; \<And>y. y \<in> U \<Longrightarrow> \<exists>z. z \<in> f' x ` ball 0 1 \<and> dist z y < k\<rbrakk>
                        \<Longrightarrow> ?\<mu> U < ?\<mu> (f' x ` ball 0 1) + e * ?unit_vol"
            using measure_semicontinuous_with_hausdist_explicit [OF bo neg 0] by blast
          obtain l where "l > 0" and l: "ball x l \<subseteq> T"
            using \<open>x \<in> S\<close> \<open>open T\<close> \<open>S \<subseteq> T\<close> openE by blast
          obtain \<zeta> where "0 < \<zeta>"
            and \<zeta>: "\<And>y. \<lbrakk>y \<in> S; y \<noteq> x; dist y x < \<zeta>\<rbrakk>
                        \<Longrightarrow> norm (f y - (f x + f' x (y - x))) / norm (y - x) < k"
            using lim0 \<open>k > 0\<close> by (simp add: Lim_within) (auto simp add: field_simps)
          define r where "r \<equiv> min (min l (\<zeta>/2)) (min 1 (d/2))"
          show ?thesis
          proof (intro exI conjI)
            show "r > 0" "r < d"
              using \<open>l > 0\<close> \<open>\<zeta> > 0\<close> \<open>d > 0\<close> by (auto simp: r_def)
            have "r \<le> l"
              by (auto simp: r_def)
            with l show "ball x r \<subseteq> T"
              by auto
            have ex_lessK: "\<exists>x' \<in> ball 0 1. dist (f' x x') ((f y - f x) /\<^sub>R r) < k"
              if "y \<in> S" and "dist x y < r" for y
            proof (cases "y = x")
              case True
              with lin linear_0 \<open>k > 0\<close> that show ?thesis
                by (rule_tac x=0 in bexI) (auto simp: linear_0)
            next
              case False
              then show ?thesis
              proof (rule_tac x="(y - x) /\<^sub>R r" in bexI)
                have "f' x ((y - x) /\<^sub>R r) = f' x (y - x) /\<^sub>R r"
                  by (simp add: lin linear_scale)
                then have "dist (f' x ((y - x) /\<^sub>R r)) ((f y - f x) /\<^sub>R r) = norm (f' x (y - x) /\<^sub>R r - (f y - f x) /\<^sub>R r)"
                  by (simp add: dist_norm)
                also have "\<dots> = norm (f' x (y - x) - (f y - f x)) / r"
                  using \<open>r > 0\<close> by (simp add: divide_simps scale_right_diff_distrib [symmetric])
                also have "\<dots> \<le> norm (f y - (f x + f' x (y - x))) / norm (y - x)"
                  using that \<open>r > 0\<close> False by (simp add: field_split_simps dist_norm norm_minus_commute mult_right_mono)
                also have "\<dots> < k"
                  using that \<open>0 < \<zeta>\<close> by (simp add: dist_commute r_def  \<zeta> [OF \<open>y \<in> S\<close> False])
                finally show "dist (f' x ((y - x) /\<^sub>R r)) ((f y - f x) /\<^sub>R r) < k" .
                show "(y - x) /\<^sub>R r \<in> ball 0 1"
                  using that \<open>r > 0\<close> by (simp add: dist_norm divide_simps norm_minus_commute)
              qed
            qed
            let ?rfs = "(\<lambda>x. x /\<^sub>R r) ` (+) (- f x) ` f ` (S \<inter> ball x r)"
            have rfs_mble: "?rfs \<in> lmeasurable"
            proof (rule bounded_set_imp_lmeasurable)
              have "f differentiable_on S \<inter> ball x r"
                using f_diff by (auto simp: fmeasurableD differentiable_on_subset)
              with S show "?rfs \<in> sets lebesgue"
                by (auto simp: sets.Int intro!: lebesgue_sets_translation differentiable_image_in_sets_lebesgue)
              let ?B = "(\<lambda>(x, y). x + y) ` (f' x ` ball 0 1 \<times> ball 0 k)"
              have "bounded ?B"
                by (simp add: bounded_plus [OF bo])
              moreover have "?rfs \<subseteq> ?B"
                apply (auto simp: dist_norm image_iff dest!: ex_lessK)
                by (metis (no_types, opaque_lifting) add.commute diff_add_cancel dist_0_norm dist_commute dist_norm mem_ball)
              ultimately show "bounded (?rfs)"
                by (rule bounded_subset)
            qed
            then have "(\<lambda>x. r *\<^sub>R x) ` ?rfs \<in> lmeasurable"
              by (simp add: measurable_linear_image_eu)
            with \<open>r > 0\<close> have "(+) (- f x) ` f ` (S \<inter> ball x r) \<in> lmeasurable"
              by (simp add: image_comp o_def)
            then have "(+) (f x) ` (+) (- f x) ` f ` (S \<inter> ball x r) \<in> lmeasurable"
              using  measurable_translation by blast
            then show fsb: "f ` (S \<inter> ball x r) \<in> lmeasurable"
              by (simp add: image_comp o_def)
            have "?\<mu> (f ` (S \<inter> ball x r)) = ?\<mu> (?rfs) * r ^ DIM('a)"
              using \<open>r > 0\<close> fsb
              by (simp add: measure_linear_image_eu measure_translation_subtract measurable_translation_subtract eucl.det_scale' field_simps cong: image_cong_simp)
            also have "\<dots> \<le> (\<bar>eucl.det (f' x)\<bar> * ?unit_vol + e * ?unit_vol) * r ^ DIM('a)"
            proof -
              have "?\<mu> (?rfs) < ?\<mu> (f' x ` ball 0 1) + e * ?unit_vol"
                using rfs_mble by (force intro: k dest!: ex_lessK)
              then have "?\<mu> (?rfs) < \<bar>eucl.det (f' x)\<bar> * ?unit_vol + e * ?unit_vol"
                by (simp add: lin measure_linear_image_eu [of "f' x"])
              with \<open>r > 0\<close> show ?thesis
                by auto
            qed
            also have "\<dots> \<le> (B + e) * ?\<mu> (ball x r)"
              using bounded [OF \<open>x \<in> S\<close>] \<open>r > 0\<close>
              by (simp add: algebra_simps content_ball_conv_unit_ball[of r] content_ball_pos)
            finally show "?\<mu> (f ` (S \<inter> ball x r)) \<le> (B + e) * ?\<mu> (ball x r)" .
          qed
        qed
        then obtain r where
          r0d: "\<And>x d. \<lbrakk>x \<in> S; d > 0\<rbrakk> \<Longrightarrow> 0 < r x d \<and> r x d < d"
          and rT: "\<And>x d. \<lbrakk>x \<in> S; d > 0\<rbrakk> \<Longrightarrow> ball x (r x d) \<subseteq> T"
          and r: "\<And>x d. \<lbrakk>x \<in> S; d > 0\<rbrakk> \<Longrightarrow>
                  (f ` (S \<inter> ball x (r x d))) \<in> lmeasurable \<and>
                  ?\<mu> (f ` (S \<inter> ball x (r x d))) \<le> (B + e) * ?\<mu> (ball x (r x d))"
          by metis
        obtain C where "countable C" and Csub: "C \<subseteq> {(x,r x t) |x t. x \<in> S \<and> 0 < t}"
          and pwC: "pairwise (\<lambda>i j. disjnt (ball (fst i) (snd i)) (ball (fst j) (snd j))) C"
          and negC: "negligible(S - (\<Union>i \<in> C. ball (fst i) (snd i)))"
          apply (rule Vitali_covering_theorem_balls [of S "{(x,r x t) |x t. x \<in> S \<and> 0 < t}" fst snd])
           apply auto
          by (metis dist_eq_0_iff r0d)
        let ?UB = "(\<Union>(x,s) \<in> C. ball x s)"
        have eq: "f ` (S \<inter> ?UB) = (\<Union>(x,s) \<in> C. f ` (S \<inter> ball x s))"
          by auto
        have mle: "?\<mu> (\<Union>(x,s) \<in> K. f ` (S \<inter> ball x s)) \<le> (B + e) * (?\<mu> S + d)"  (is "?l \<le> ?r")
          if "K \<subseteq> C" and "finite K" for K
        proof -
          have gt0: "b > 0" if "(a, b) \<in> K" for a b
            using Csub that \<open>K \<subseteq> C\<close> r0d by auto
          have inj: "inj_on (\<lambda>(x, y). ball x y) K"
            by (force simp: inj_on_def ball_eq_ball_iff dest: gt0)
          have disjnt: "disjoint ((\<lambda>(x, y). ball x y) ` K)"
            using pwC that pairwise_image pairwise_mono by fastforce
          have "?l \<le> (\<Sum>i\<in>K. ?\<mu> (case i of (x, s) \<Rightarrow> f ` (S \<inter> ball x s)))"
          proof (rule measure_UNION_le [OF \<open>finite K\<close>], clarify)
            fix x r
            assume "(x,r) \<in> K"
            then have "x \<in> S"
              using Csub \<open>K \<subseteq> C\<close> by auto
            show "f ` (S \<inter> ball x r) \<in> sets lebesgue"
              by (meson Int_lower1 S differentiable_on_subset f_diff fmeasurableD lmeasurable_ball order_refl sets.Int differentiable_image_in_sets_lebesgue)
          qed
          also have "\<dots> \<le> (\<Sum>(x,s) \<in> K. (B + e) * ?\<mu> (ball x s))"
            using Csub r \<open>K \<subseteq> C\<close>  by (intro sum_mono) auto
          also have "\<dots> = (B + e) * (\<Sum>(x,s) \<in> K. ?\<mu> (ball x s))"
            by (simp add: prod.case_distrib sum_distrib_left)
          also have "\<dots> = (B + e) * sum ?\<mu> ((\<lambda>(x, y). ball x y) ` K)"
            using \<open>B \<ge> 0\<close> \<open>e > 0\<close> by (simp add: inj sum.reindex prod.case_distrib)
          also have "\<dots> = (B + e) * ?\<mu> (\<Union>(x,s) \<in> K. ball x s)"
            using \<open>B \<ge> 0\<close> \<open>e > 0\<close> that
            by (subst measure_Union') (auto simp: disjnt measure_Union')
          also have "\<dots> \<le> (B + e) * ?\<mu> T"
            using \<open>B \<ge> 0\<close> \<open>e > 0\<close> that apply simp
            using measure_mono_fmeasurable [OF _ _ \<open>T \<in> lmeasurable\<close>] Csub rT
            by (smt (verit) SUP_least measure_nonneg measure_notin_sets mem_Collect_eq old.prod.case subset_iff)
          also have "\<dots> \<le> (B + e) * (?\<mu> S + d)"
            using \<open>B \<ge> 0\<close> \<open>e > 0\<close> Tless by simp
          finally show ?thesis .
        qed
        have fSUB_mble: "(f ` (S \<inter> ?UB)) \<in> lmeasurable"
          unfolding eq using Csub r False \<open>e > 0\<close> that
          by (auto simp: intro!: fmeasurable_UN_bound [OF \<open>countable C\<close> _ mle])
        have fSUB_meas: "?\<mu> (f ` (S \<inter> ?UB)) \<le> (B + e) * (?\<mu> S + d)"  (is "?MUB")
          unfolding eq using Csub r False \<open>e > 0\<close> that
          by (auto simp: intro!: measure_UN_bound [OF \<open>countable C\<close> _ mle])
        have neg: "negligible ((f ` (S \<inter> ?UB) - f ` S) \<union> (f ` S - f ` (S \<inter> ?UB)))"
        proof (rule negligible_subset [OF negligible_differentiable_image_negligible [OF order_refl negC, where f=f]])
          show "f differentiable_on S - (\<Union>i\<in>C. ball (fst i) (snd i))"
            by (meson DiffE differentiable_on_subset subsetI f_diff)
        qed force
        show "f ` S \<in> lmeasurable"
          by (rule lmeasurable_negligible_symdiff [OF fSUB_mble neg])
        show ?MD
          using fSUB_meas measure_negligible_symdiff [OF fSUB_mble neg] by simp
      qed
      show "f ` S \<in> lmeasurable"
        using eps_d [of 1] by simp
      show ?ME
      proof (rule field_le_epsilon)
        fix \<delta> :: real
        assume "0 < \<delta>"
        then show "?\<mu> (f ` S) \<le> (B + e) * ?\<mu> S + \<delta>"
          using eps_d [of "\<delta> / (B+e)"] \<open>e > 0\<close> \<open>B \<ge> 0\<close> by (auto simp: divide_simps mult_ac)
      qed
    qed
    show ?thesis
    proof (cases "?\<mu> S = 0")
      case True
      with eps have "?\<mu> (f ` S) = 0"
        by (metis mult_zero_right not_le zero_less_measure_iff)
      then show ?thesis
        using eps [of 1] by (simp add: True)
    next
      case False
      have "?\<mu> (f ` S) \<le> B * ?\<mu> S"
      proof (rule field_le_epsilon)
        fix e :: real
        assume "e > 0"
        then show "?\<mu> (f ` S) \<le> B * ?\<mu> S + e"
          using eps [of "e / ?\<mu> S"] False by (auto simp: algebra_simps zero_less_measure_iff)
      qed
      with eps [of 1] show ?thesis by auto
    qed
  qed
  then show "f ` S \<in> lmeasurable" ?M by blast+
qed

lemma m_diff_image_weak_eu:
 fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes S: "S \<in> lmeasurable"
    and deriv: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and int: "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) integrable_on S"
  shows "f ` S \<in> lmeasurable \<and> measure lebesgue (f ` S) \<le> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
proof -
  let ?\<mu> = "measure lebesgue"
  have aint_S: "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) absolutely_integrable_on S"
    using int unfolding absolutely_integrable_on_def by auto
  define m where "m \<equiv> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
  have *: "f ` S \<in> lmeasurable" "?\<mu> (f ` S) \<le> m + e * ?\<mu> S"
    if "e > 0" for e
  proof -
    define Sn where "Sn \<equiv> \<lambda>n. {x \<in> S. real n * e \<le> \<bar>eucl.det (f' x)\<bar> \<and> \<bar>eucl.det (f' x)\<bar> < real (Suc n) * e}"
    have Sn_sub: "Sn n \<subseteq> S" for n
      by (auto simp: Sn_def)
    have S_eq: "S = (\<Union>n. Sn n)"
    proof (intro equalityI subsetI)
      fix x assume "x \<in> S"
      define n where "n = nat \<lfloor>\<bar>eucl.det (f' x)\<bar> / e\<rfloor>"
      have "real_of_int \<lfloor>\<bar>eucl.det (f' x)\<bar> / e\<rfloor> * e \<le> \<bar>eucl.det (f' x)\<bar>"
        using floor_divide_lower \<open>e > 0\<close> by blast
      moreover have "\<bar>eucl.det (f' x)\<bar> < (real_of_int \<lfloor>\<bar>eucl.det (f' x)\<bar> / e\<rfloor> + 1) * e"
        using floor_divide_upper \<open>e > 0\<close> by blast
      moreover have "\<lfloor>\<bar>eucl.det (f' x)\<bar> / e\<rfloor> \<ge> 0"
        using \<open>e > 0\<close> by (simp add: floor_divide_lower)
      ultimately have "x \<in> Sn n"
        using \<open>x \<in> S\<close> by (auto simp: Sn_def n_def of_nat_nat nat_add_distrib algebra_simps)
      then show "x \<in> (\<Union>n. Sn n)" by auto
    qed (auto simp: Sn_def)
    have Sn_mble: "Sn n \<in> lmeasurable" for n
    proof -
      have meas: "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) \<in> borel_measurable (lebesgue_on S)"
        using integrable_imp_measurable[OF int] .
      have 1: "{x \<in> S. real n * e \<le> \<bar>eucl.det (f' x)\<bar>} \<in> sets (lebesgue_on S)"
        using borel_measurable_le[OF _ meas] by (simp add: space_lebesgue_on)
      have 2: "{x \<in> S. \<bar>eucl.det (f' x)\<bar> < real (Suc n) * e} \<in> sets (lebesgue_on S)"
        using borel_measurable_less[OF meas] by (simp add: space_lebesgue_on)
      have "{x \<in> S. real n * e \<le> \<bar>eucl.det (f' x)\<bar> \<and> \<bar>eucl.det (f' x)\<bar> < real (Suc n) * e} \<in> sets (lebesgue_on S)"
        using Int_Collect sets.Int[OF 1 2] by (metis Collect_conj_eq2)
      then have "Sn n \<in> sets (lebesgue_on S)"
        by (simp add: Sn_def)
      then have "Sn n \<in> sets lebesgue"
        using S sets_restrict_space_iff[of S lebesgue] by blast
      then show ?thesis
        using fmeasurableI2[OF S Sn_sub] by blast
    qed
    have Sn_deriv: "(f has_derivative f' x) (at x within Sn n)" if "x \<in> Sn n" for x n
      by (meson Sn_sub deriv has_derivative_subset subsetD that)
    have Sn_int: "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) integrable_on Sn n" for n
    proof -
      have "Sn n \<in> sets (lebesgue_on S)"
        using Sn_mble Sn_sub S
        by (simp add: sets_restrict_space_iff)
      then have "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) absolutely_integrable_on Sn n"
        using set_integrable_restrict_space[OF aint_S] by auto
      then show ?thesis
        using set_lebesgue_integral_eq_integral by blast
    qed
    have Sn_bdd: "\<bar>eucl.det (f' x)\<bar> \<le> real (Suc n) * e" if "x \<in> Sn n" for x n
      using that by (auto simp: Sn_def less_imp_le)
    have fSn_mble: "f ` Sn n \<in> lmeasurable" for n
      using measurable_bounded_differentiable_image_eu [OF Sn_mble Sn_deriv Sn_int Sn_bdd] .
    have fSn_meas: "?\<mu> (f ` Sn n) \<le> real (Suc n) * e * ?\<mu> (Sn n)" for n
      using measure_bounded_differentiable_image_eu [OF Sn_mble Sn_deriv Sn_int Sn_bdd] .
    have fSn_meas2: "?\<mu> (f ` Sn n) \<le> integral (Sn n) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>) + e * ?\<mu> (Sn n)" for n
    proof -
      have "real (Suc n) * e * ?\<mu> (Sn n) = real n * e * ?\<mu> (Sn n) + e * ?\<mu> (Sn n)"
        by (simp add: algebra_simps)
      also have "real n * e * ?\<mu> (Sn n) \<le> integral (Sn n) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
      proof -
        have "real n * e * ?\<mu> (Sn n) = integral (Sn n) (\<lambda>x. real n * e)"
          using lmeasure_integral[OF Sn_mble] integral_mult_right[of "Sn n" "real n * e"]
          by (metis (no_types, lifting) Henstock_Kurzweil_Integration.integral_cong lambda_one mult_commute_abs)
        also have "\<dots> \<le> integral (Sn n) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
          using integral_le[OF integrable_on_const[OF Sn_mble] Sn_int]
          using Sn_def by blast
        finally show ?thesis .
      qed
      finally show ?thesis using fSn_meas [of n] by linarith
    qed
    have "f ` S = (\<Union>n. f ` Sn n)"
      using S_eq by auto
    have bound: "?\<mu> (\<Union> ((\<lambda>k. f ` Sn k) ` {..n})) \<le> m + e * ?\<mu> S" for n
    proof -
      have "?\<mu> (\<Union> ((\<lambda>k. f ` Sn k) ` {..n})) \<le> (\<Sum>k\<le>n. ?\<mu> (f ` Sn k))"
        by (intro measure_UNION_le) (auto intro: fSn_mble fmeasurableD)
      also have "\<dots> \<le> (\<Sum>k\<le>n. integral (Sn k) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>) + e * ?\<mu> (Sn k))"
        by (intro sum_mono) (use fSn_meas2 in auto)
      also have "\<dots> = (\<Sum>k\<le>n. integral (Sn k) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)) + e * (\<Sum>k\<le>n. ?\<mu> (Sn k))"
        by (simp add: sum.distrib sum_distrib_left)
      also have "\<dots> \<le> m + e * ?\<mu> S"
      proof (intro add_mono mult_left_mono)
        show "(\<Sum>k\<le>n. integral (Sn k) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)) \<le> m"
        proof -
          have disj: "disjoint_family_on Sn {..n}"
            unfolding disjoint_family_on_def Sn_def 
            using mult_strict_right_mono[OF _ \<open>e > 0\<close>]
            apply auto
            by (smt (verit) le_antisym nat_le_real_less)
          have pw: "pairwise (\<lambda>i i'. negligible (Sn i \<inter> Sn i')) {..n}"
            using disj unfolding disjoint_family_on_def pairwise_def
            by auto
          have hi: "((\<lambda>x. \<bar>eucl.det (f' x)\<bar>) has_integral (\<Sum>k\<le>n. integral (Sn k) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>))) (\<Union>k\<le>n. Sn k)"
            by (intro has_integral_UN[OF _ _ pw]) (auto intro: integrable_integral Sn_int)
          have sum_eq: "(\<Sum>k\<le>n. integral (Sn k) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)) = integral (\<Union>k\<le>n. Sn k) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
            using integral_unique[OF hi] by simp
          also have "\<dots> \<le> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
          proof (rule integral_subset_le)
            show "(\<Union>k\<le>n. Sn k) \<subseteq> S" using Sn_sub by auto
            show "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) integrable_on (\<Union>k\<le>n. Sn k)"
              using hi by (auto simp: integrable_on_def)
            show "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) integrable_on S" using int .
            show "\<forall>x\<in>S. 0 \<le> \<bar>eucl.det (f' x)\<bar>" by auto
          qed
          finally show ?thesis by (simp add: m_def)
        qed
        show "(\<Sum>k\<le>n. ?\<mu> (Sn k)) \<le> ?\<mu> S"
        proof -
          have disj: "disjoint_family_on Sn {..n}"
            unfolding disjoint_family_on_def Sn_def
            using mult_strict_right_mono[OF _ \<open>e > 0\<close>]
            apply auto
            by (smt (verit, ccfv_threshold) nat_le_real_less order_antisym)
          have "(\<Sum>k\<le>n. ?\<mu> (Sn k)) = ?\<mu> (\<Union>k\<le>n. Sn k)"
            by (intro measure_finite_Union[symmetric])
               (auto intro: disj fmeasurableD[OF Sn_mble]
                     simp: emeasure_eq_measure2[OF Sn_mble])
          also have "\<dots> \<le> ?\<mu> S"
          proof (rule measure_mono_fmeasurable)
            show "(\<Union>k\<le>n. Sn k) \<subseteq> S" using Sn_sub by auto
            show "(\<Union>k\<le>n. Sn k) \<in> sets lebesgue"
              by (intro sets.finite_Union) (auto intro: fmeasurableD[OF Sn_mble])
            show "S \<in> lmeasurable" using S .
          qed
          finally show ?thesis .
        qed
        show "0 \<le> e" using \<open>e > 0\<close> by linarith
      qed
      finally show ?thesis .
    qed
    have fS_mble: "f ` S \<in> lmeasurable"
      using fmeasurable_countable_Union[OF fSn_mble bound] \<open>f ` S = (\<Union>n. f ` Sn n)\<close>
      by (metis (no_types) atMost_atLeast0 image_comp)
    have fS_meas: "?\<mu> (f ` S) \<le> m + e * ?\<mu> S"
      using measure_countable_Union_le[OF fSn_mble bound] \<open>f ` S = (\<Union>n. f ` Sn n)\<close>
      by (metis (no_types) atMost_atLeast0 image_comp)
    show "f ` S \<in> lmeasurable" "?\<mu> (f ` S) \<le> m + e * ?\<mu> S"
      using fS_mble fS_meas by auto
  qed
  show ?thesis
  proof
    show "f ` S \<in> lmeasurable"
      using * linordered_field_no_ub by blast
    let ?x = "m - ?\<mu> (f ` S)"
    have False if "?\<mu> (f ` S) > integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
    proof -
      have ml: "m < ?\<mu> (f ` S)"
        using m_def that by blast
      then have "?\<mu> S \<noteq> 0"
        using "*"(2) bgauge_existence_lemma by fastforce
      with ml have 0: "0 < - (m - ?\<mu> (f ` S))/2 / ?\<mu> S"
        using that zero_less_measure_iff by force
      then show ?thesis
        using * [OF 0] that by (auto simp: field_split_simps m_def split: if_split_asm)
    qed
    then show "?\<mu> (f ` S) \<le> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
      by fastforce
  qed
qed


theorem
 fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes S: "S \<in> sets lebesgue"
    and deriv: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and int: "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) integrable_on S"
  shows measurable_differentiable_image_eu: "f ` S \<in> lmeasurable"
    and measure_differentiable_image_eu:
       "measure lebesgue (f ` S) \<le> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)" (is "?M")
proof -
  let ?One = "\<Sum>i\<in>Basis. i :: 'a"
  let ?I = "\<lambda>n::nat. cbox (- real n *\<^sub>R ?One) (real n *\<^sub>R ?One) \<inter> S"
  let ?\<mu> = "measure lebesgue"
  have "\<And>x. x \<in> S \<Longrightarrow> \<exists>xa. \<forall>i\<in>Basis. - real xa \<le> x \<bullet> i \<and> x \<bullet> i \<le> real xa"
    by (meson abs_le_iff minus_le_iff norm_bound_Basis_le real_arch_simple)
  then have Seq: "S = (\<Union>n. ?I n)"
    by (auto simp: mem_box)
  have fIn: "f ` ?I n \<in> lmeasurable"
       and mfIn: "?\<mu> (f ` ?I n) \<le> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)" (is ?MN) for n
  proof -
    have In_mble: "?I n \<in> lmeasurable"
      by (simp add: S fmeasurable_Int_fmeasurable)
    have In_deriv: "(f has_derivative f' x) (at x within ?I n)" if "x \<in> ?I n" for x
      by (meson IntD2 deriv has_derivative_subset inf_le2 that)
    have In_int: "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) integrable_on ?I n"
      using int integrable_on_subcbox
      by (metis (no_types, lifting) inf.orderI inf_sup_aci(1) inf_top.right_neutral
          integrable_restrict_Int)
    have res: "f ` ?I n \<in> lmeasurable \<and> ?\<mu> (f ` ?I n) \<le> integral (?I n) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
      by (rule m_diff_image_weak_eu [OF In_mble In_deriv In_int])
    then show "f ` ?I n \<in> lmeasurable" by blast
    have "integral (?I n) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>) \<le> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
      by (rule integral_subset_le [OF _ In_int int]) auto
    with res show ?MN by linarith
  qed
  have "?I k \<subseteq> ?I n" if "k \<le> n" for k n
    using that by (force simp: mem_box)
  then have "(\<Union>k\<le>n. f ` ?I k) = f ` ?I n" for n
    by (fastforce simp add:)
  with mfIn have "?\<mu> (\<Union>k\<le>n. f ` ?I k) \<le> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)" for n
    by simp
  then have "(\<Union>n. f ` ?I n) \<in> lmeasurable" "?\<mu> (\<Union>n. f ` ?I n) \<le> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
    by (rule fmeasurable_countable_Union [OF fIn] measure_countable_Union_le [OF fIn])+
  then show "f ` S \<in> lmeasurable" ?M
    by (metis Seq image_UN)+
qed

subsection\<open>Borel measurable Jacobian determinant\<close>

proposition borel_measurable_partial_derivatives_eu:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes S: "S \<in> sets lebesgue"
    and f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  shows "(\<lambda>x. f' x u \<bullet> v) \<in> borel_measurable (lebesgue_on S)"
proof -
  have lin: "linear (f' x)" if "x \<in> S" for x
    using f[OF that] has_derivative_linear by blast
  have contf: "continuous_on S f"
    using continuous_on_eq_continuous_within f has_derivative_continuous by blast
  have "{x \<in> S.  f' x u \<bullet> v \<le> b} \<in> sets lebesgue" for b
  proof (rule sets_negligible_symdiff)
    let ?C = "\<lambda>e A d y. {x \<in> S. norm(y - x) < d \<longrightarrow> norm(f y - f x - A (y - x)) \<le> e * norm(y - x)}"
    let ?L = "{A. linear A \<and> A u \<bullet> v < b \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>)}"
    let ?E = "{e \<in> \<rat>. (0::real) < e}"
    let ?D = "{d \<in> \<rat>. (0::real) < d}"
    let ?T = "{x \<in> S. \<forall>e>0. \<exists>d>0. \<exists>A. linear A \<and> A u \<bullet> v < b \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>) \<and>
                       (\<forall>y \<in> S. x \<in> ?C e A d y)}"
    let ?U = "S \<inter> (\<Inter>e \<in> ?E. \<Union>A \<in> ?L. \<Union>d \<in> ?D. S \<inter> (\<Inter>y \<in> S. ?C e A d y))"
    have "?T = ?U"
    proof (intro set_eqI iffI ; clarsimp)
      fix s :: 'a and q :: real and r :: real
      assume "s \<in> S"
        and "\<forall>e>0. \<exists>d>0. \<exists>A. linear A \<and> A u \<bullet> v < b \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>) \<and> (\<forall>y\<in>S. norm (y - s) < d \<longrightarrow> norm (f y - f s - A (y - s)) \<le> e * norm (y - s))"
        and q: "q \<in> \<rat>" "0 < q" and r: "r \<in> \<rat>" "0 < r"
      show "\<exists>xa. linear xa \<and> xa u \<bullet> v < b \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. xa i \<bullet> j \<in> \<rat>) \<and> (\<exists>xc. xc \<in> \<rat> \<and> 0 < xc \<and> (\<forall>xd\<in>S. norm (xd - s) < xc \<longrightarrow> norm (f xd - f s - xa (xd - s)) \<le> r * norm (xd - s)))"
      proof -
        obtain d A where linA: "linear A" and dpos: "d > 0" and Ab: "A u \<bullet> v < b" and AQ: "\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>"
          and norm: "\<forall>y\<in>S. norm (y - s) < d \<longrightarrow> norm (f y - f s - A (y - s)) \<le> r * norm (y - s)"
          using \<open>\<forall>e>0. _\<close> \<open>0 < r\<close> by blast
        obtain xc where xcQ: "xc \<in> \<rat>" and xc_close: "\<bar>xc - d/2\<bar> < d/2"
          using rational_approximation [of "d/2"] dpos by auto
        have "0 < xc" "xc < d"
          using xc_close dpos by linarith+
        then show ?thesis
          using linA Ab AQ norm xcQ by (meson order.strict_trans)
      qed
    next
      fix x :: 'a
        and e :: real
      assume "x \<in> S"
        and xif: "x \<in> (if \<forall>x. (x::real) \<in> \<rat> \<longrightarrow> \<not> 0 < x then UNIV else S \<inter> (\<Inter>x\<in>?E. \<Union>xa\<in>?L. \<Union>xb\<in>?D. \<Inter>y\<in>S. ?C x xa xb y))"
        and "0 < e"
      show "\<exists>d>0. \<exists>A. linear A \<and> A u \<bullet> v < b \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>) \<and> (\<forall>y\<in>S. norm (y - x) < d \<longrightarrow> norm (f y - f x - A (y - x)) \<le> e * norm (y - x))"
      proof -
        have nif: "\<not> (\<forall>x::real. x \<in> \<rat> \<longrightarrow> \<not> 0 < x)"
          using Rats_1 zero_less_one by blast
        obtain q::real where qQ: "q \<in> \<rat>" and q0: "0 < q" and qe: "q < e"
          using \<open>0 < e\<close> Rats_dense_in_real by blast
        from xif nif
        have xmem: "x \<in> S \<inter> (\<Inter>x\<in>?E. \<Union>xa\<in>?L. \<Union>xb\<in>?D. \<Inter>y\<in>S. ?C x xa xb y)"
          by (auto split: if_splits)
        then have "x \<in> (\<Union>xa\<in>?L. \<Union>xb\<in>?D. \<Inter>y\<in>S. ?C q xa xb y)"
          using qQ q0 by blast
        then obtain A d where linA: "linear A" and Ab: "A u \<bullet> v < b" and AQ: "\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>"
          and dQ: "d \<in> \<rat>" and d0: "0 < d"
          and norm: "\<forall>y\<in>S. x \<in> S \<and> (norm (y - x) < d \<longrightarrow> norm (f y - f x - A (y - x)) \<le> q * norm (y - x))"
          by auto
        moreover have "q * norm (y - x) \<le> e * norm (y - x)" for y
          using qe by (simp add: mult_right_mono)
        ultimately show ?thesis
          by (meson le_less order.trans)
      qed
    qed
    moreover have "?U \<in> sets lebesgue"
    proof -
      have coE: "countable ?E"
        using countable_Collect countable_rat by blast
      have ne: "?E \<noteq> {}"
        using zero_less_one Rats_1 by blast
      have coA: "countable ?L"
      proof (rule countable_subset)
        show "countable {A :: 'a \<Rightarrow> 'b. linear A \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>)}"
        proof -
          \<comment> \<open>A linear function is determined by its values on Basis\<close>
          {             fix A B :: "'a \<Rightarrow> 'b"
            assume "linear A" "linear B" and eq: "\<forall>x\<in>Basis. A x = B x"
            have "A = B"
            proof (rule ext)
              fix x
              have "A x = A (\<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R i)"
                by (simp add: euclidean_representation)
              also have "\<dots> = (\<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R A i)"
                using \<open>linear A\<close> by (simp add: linear_sum linear_scale)
              also have "\<dots> = (\<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R B i)"
                using eq by simp
              also have "\<dots> = B (\<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R i)"
                using \<open>linear B\<close> by (simp add: linear_sum linear_scale)
              also have "\<dots> = B x"
                by (simp add: euclidean_representation)
              finally show "A x = B x" .
            qed
          }
          then have inj: "inj_on (\<lambda>A. restrict A (Basis::'a set))
                            {A :: 'a \<Rightarrow> 'b. linear A \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>)}"
            by (smt (verit, ccfv_SIG) inj_onI mem_Collect_eq restrict_apply')
          \<comment> \<open>The range of this restriction is contained in a countable set\<close>
          have "countable {g :: 'a \<Rightarrow> 'b. (\<forall>i. i \<notin> Basis \<longrightarrow> g i = undefined) \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. g i \<bullet> j \<in> \<rat>)}"
          proof (rule countable_subset)
            let ?V = "{w :: 'b. \<forall>j\<in>Basis. w \<bullet> j \<in> \<rat>}"
            have cV: "countable ?V"
            proof -
              have inj: "inj_on (\<lambda>w. restrict (\<lambda>j. w \<bullet> j) (Basis :: 'b set)) ?V"
                by (metis (mono_tags, lifting) euclidean_eq_iff inj_on_def restrict_apply')
              moreover have "(\<lambda>w. restrict (\<lambda>j. w \<bullet> j) (Basis :: 'b set)) ` ?V \<subseteq> PiE Basis (\<lambda>_. \<rat>)"
                by (auto simp: PiE_def Pi_def extensional_def restrict_def)
              moreover have "countable (PiE (Basis :: 'b set) (\<lambda>_. \<rat>))" 
                by (intro countable_PiE finite_Basis) (auto simp: countable_rat)
              moreover have "countable ((\<lambda>w. restrict (\<lambda>j. w \<bullet> j) (Basis :: 'b set)) ` ?V)"
                using calculation(2,3) countable_subset by blast
              ultimately show ?thesis
                using countable_image_inj_on by blast
            qed
            show "{g :: 'a \<Rightarrow> 'b. (\<forall>i. i \<notin> Basis \<longrightarrow> g i = undefined) \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. g i \<bullet> j \<in> \<rat>)} \<subseteq>
                  PiE (Basis :: 'a set) (\<lambda>_. ?V)"
              by blast
            show "countable (PiE (Basis :: 'a set) (\<lambda>_. ?V))"
              by (intro countable_PiE finite_Basis) (auto simp: cV)
          qed
          moreover have "(\<lambda>A. restrict A (Basis::'a set)) ` 
                         {A :: 'a \<Rightarrow> 'b. linear A \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>)} \<subseteq>
                         {g :: 'a \<Rightarrow> 'b. (\<forall>i. i \<notin> Basis \<longrightarrow> g i = undefined) \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. g i \<bullet> j \<in> \<rat>)}"
            by (auto simp: restrict_def)
          ultimately show ?thesis
            by (metis (no_types, lifting) inj countable_image_inj_on countable_subset)
        qed
      qed blast
      have *: "\<lbrakk>U \<noteq> {} \<Longrightarrow> closedin (top_of_set S) (S \<inter> \<Inter> U)\<rbrakk>
               \<Longrightarrow> closedin (top_of_set S) (S \<inter> \<Inter> U)" for U
        by fastforce
      have sets: "S \<inter> (\<Inter>y\<in>S. ?C e A d y) \<in> sets lebesgue" if "linear A" for e A d
      proof (rule lebesgue_closedin [OF _ S])
        show "closedin (top_of_set S) (S \<inter> (\<Inter>y\<in>S. ?C e A d y))"
        proof (rule *)
          assume ne: "(\<lambda>y. ?C e A d y) ` S \<noteq> {}"
          then have Sne: "S \<noteq> {}" by blast
          have sub: "(\<Inter>y\<in>S. ?C e A d y) \<subseteq> S"
            using Sne by (auto intro: INF_lower2)
          have eq: "S \<inter> (\<Inter>y\<in>S. ?C e A d y) = (\<Inter>y\<in>S. ?C e A d y)"
            using sub by (rule Int_absorb1)
          show "closedin (top_of_set S) (S \<inter> (\<Inter>y\<in>S. ?C e A d y))"
            unfolding eq
          proof (rule closedin_INT [OF Sne])
            fix y assume "y \<in> S"
            have "closedin (top_of_set S)
                    ({x \<in> S. d \<le> norm (y - x)} \<union> {x \<in> S. norm (f y - f x - A (y - x)) \<le> e * norm (y - x)})"
            proof (intro closedin_Un)
              show "closedin (top_of_set S) {x \<in> S. d \<le> norm (y - x)}"
              proof -
                have "continuous_on S (\<lambda>x. norm (y - x))"
                  by (intro continuous_on_norm continuous_on_diff continuous_on_const continuous_on_id)
                then have "closedin (top_of_set S) (S \<inter> (\<lambda>x. norm (y - x)) -` {d..})"
                  by (intro continuous_closedin_preimage closed_atLeast)
                moreover have "{x \<in> S. d \<le> norm (y - x)} = S \<inter> (\<lambda>x. norm (y - x)) -` {d..}"
                  by auto
                ultimately show ?thesis by simp
              qed
              show "closedin (top_of_set S) {x \<in> S. norm (f y - f x - A (y - x)) \<le> e * norm (y - x)}"
              proof -
                have contA: "continuous_on S A"
                  using that linear_continuous_on linear_conv_bounded_linear by blast
                have contAcomp: "continuous_on S (\<lambda>x. A (y - x))"
                proof -
                  have "continuous_on UNIV A"
                    using that linear_continuous_on linear_conv_bounded_linear by blast
                  moreover have "continuous_on S (\<lambda>x. y - x)"
                    by (intro continuous_on_diff continuous_on_const continuous_on_id)
                  ultimately show ?thesis
                    by (rule continuous_on_compose2) auto
                qed
                have "continuous_on S (\<lambda>x. norm (f y - f x - A (y - x)) - e * norm (y - x))"
                  by (intro continuous_on_diff continuous_on_norm continuous_on_mult
                           continuous_on_const contf continuous_on_id contAcomp)
                then have "closedin (top_of_set S) (S \<inter> (\<lambda>x. norm (f y - f x - A (y - x)) - e * norm (y - x)) -` {..0})"
                  by (intro continuous_closedin_preimage closed_atMost)
                moreover have "{x \<in> S. norm (f y - f x - A (y - x)) \<le> e * norm (y - x)}
                              = S \<inter> (\<lambda>x. norm (f y - f x - A (y - x)) - e * norm (y - x)) -` {..0}"
                  by auto
                ultimately show ?thesis by simp
              qed
            qed
            moreover have "?C e A d y
                          = {x \<in> S. d \<le> norm (y - x)} \<union> {x \<in> S. norm (f y - f x - A (y - x)) \<le> e * norm (y - x)}"
              by (auto simp: not_less)
            ultimately show "closedin (top_of_set S) (?C e A d y)"
              by simp
          qed
        qed
      qed

      have coD: "countable ?D"
        using countable_Collect countable_rat by blast
      show ?thesis
      proof (cases "S = {}")
        case True
        then show ?thesis by auto
      next
        case Sne: False
        show ?thesis
          unfolding INT_extend_simps if_not_P [OF ne] if_not_P [OF Sne]
          apply (intro sets.Int sets.countable_INT' [OF coE ne] image_subsetI
                       sets.countable_UN' [OF coA] sets.countable_UN' [OF coD])
          subgoal by (rule S)
          subgoal for e A d
            using sets [of A d e] Sne by auto
          done
      qed
    qed
    ultimately show "?T \<in> sets lebesgue"
      by simp
    define M where "M \<equiv> (?T - {x \<in> S. f' x u \<bullet> v \<le> b} \<union> ({x \<in> S. f' x u \<bullet> v \<le> b} - ?T))"
    define \<Theta> where "\<Theta> \<equiv> \<lambda>x v. \<forall>\<xi>>0. \<exists>e>0. \<forall>y \<in> S-{x}. norm (x - y) < e \<longrightarrow> \<bar>v \<bullet> (y - x)\<bar> < \<xi> * norm (x - y)"
    have nN: "negligible {x \<in> S. \<exists>v\<noteq>0. \<Theta> x v}"
      unfolding negligible_eq_zero_density 
    proof clarsimp
      fix x v and r e :: "real"
      assume "x \<in> S" "v \<noteq> 0" "r > 0" "e > 0"
      and Theta [rule_format]: "\<Theta> x v"
      moreover have "(norm v * e / 2) / DIM('a) ^ DIM('a) > 0"
        using  \<open>v \<noteq> 0\<close> \<open>e > 0\<close>
        by (auto simp add: zero_less_divide_iff zero_less_mult_iff)
      ultimately obtain d where "d > 0"
         and dless: "\<And>y. \<lbrakk>y \<in> S - {x}; norm (x - y) < d\<rbrakk> \<Longrightarrow>
                        \<bar>v \<bullet> (y - x)\<bar> < ((norm v * e / 2) / DIM('a) ^ DIM('a)) * norm (x - y)"
        by (metis \<Theta>_def)
      let ?W = "ball x (min d r) \<inter> {y. \<bar>v \<bullet> (y - x)\<bar> < (norm v * e/2 * min d r) / DIM('a) ^ DIM('a)}"
      have "open {x. \<bar>v \<bullet> (x - a)\<bar> < b}" for a b
        by (intro open_Collect_less continuous_intros)
      show "\<exists>d>0. d \<le> r \<and>
            (\<exists>U. {x' \<in> S. \<exists>v\<noteq>0. \<Theta> x' v} \<inter> ball x d \<subseteq> U \<and>
                 U \<in> lmeasurable \<and> measure lebesgue U < e * content (ball x d))"
      proof (intro exI conjI)
        show "0 < min d r" "min d r \<le> r"
          using \<open>r > 0\<close> \<open>d > 0\<close> by auto
        show "{x' \<in> S. \<exists>v. v \<noteq> 0 \<and> \<Theta> x' v} \<inter> ball x (min d r) \<subseteq> ?W"
          proof (clarsimp simp: dist_norm norm_minus_commute)
            fix y w
            assume "y \<in> S" "w \<noteq> 0"
              and d: "norm (y - x) < d" and r: "norm (y - x) < r"
            show "\<bar>v \<bullet> (y - x)\<bar> < norm v * e * min d r / (2 * real DIM('a) ^ DIM('a))"
            proof (cases "y = x")
              case True
              with \<open>r > 0\<close> \<open>d > 0\<close> \<open>e > 0\<close> \<open>v \<noteq> 0\<close> show ?thesis
                by (auto simp: divide_simps)
            next
              case False
              have "\<bar>v \<bullet> (y - x)\<bar> < norm v * e / 2 / real (DIM('a) ^ DIM('a)) * norm (x - y)"
                by (metis Diff_iff False \<open>y \<in> S\<close> d dless empty_iff insert_iff norm_minus_commute)
              also have "\<dots> \<le> norm v * e * min d r / (2 * real DIM('a) ^ DIM('a))"
                using d r \<open>e > 0\<close> by (simp add: divide_simps norm_minus_commute mult_left_mono)
              finally show ?thesis .
            qed
          qed
          show "?W \<in> lmeasurable"
            by (simp add: fmeasurable_Int_fmeasurable borel_open)
          obtain e_k :: 'a where ek: "e_k \<in> Basis"
            using nonempty_Basis by blast
          obtain T where T: "orthogonal_transformation T" and v: "v = T (norm v *\<^sub>R e_k)"
            sorry
          define b where "b \<equiv> norm v"
          have "b > 0"
            using \<open>v \<noteq> 0\<close> by (auto simp: b_def)
          have eqb: "inv T v = b *\<^sub>R e_k"
            using T v b_def orthogonal_transformation_bij bij_betw_inv_into_left
            by (metis UNIV_I orthogonal_transformation_inj inv_f_f)
          have "inj T" "bij T" and invT: "orthogonal_transformation (inv T)"
            using T orthogonal_transformation_inj orthogonal_transformation_bij orthogonal_transformation_inv
            by auto
          let ?v = "\<Sum>i\<in>Basis. (min d r / DIM('a)) *\<^sub>R i"
          let ?v' = "\<Sum>i\<in>Basis. (if i = e_k then (e/2 * min d r) / DIM('a) ^ DIM('a) else min d r) *\<^sub>R i"
          let ?x' = "inv T x"
          let ?W' = "(ball ?x' (min d r) \<inter> {y. \<bar>(y - ?x') \<bullet> e_k\<bar> < e * min d r / (2 * DIM('a) ^ DIM('a))})"
          have abs: "x - e \<le> y \<and> y \<le> x + e \<longleftrightarrow> abs(y - x) \<le> e" for x y e::real
            by auto
          have "?W = T ` ?W'"
          proof -
            have 1: "T ` (ball (inv T x) (min d r)) = ball x (min d r)"
              by (simp add: T image_orthogonal_transformation_ball orthogonal_transformation_surj surj_f_inv_f)
            have 2: "{y. \<bar>v \<bullet> (y - x)\<bar> < b * e * min d r / (2 * real DIM('a) ^ DIM('a))} =
                      T ` {y. \<bar>(y - ?x') \<bullet> e_k\<bar> < e * min d r / (2 * real DIM('a) ^ DIM('a))}"
            proof -
              have *: "\<bar>T (b *\<^sub>R e_k) \<bullet> (y - x)\<bar> = b * \<bar>(inv T y - ?x') \<bullet> e_k\<bar>" for y
              proof -
                have "\<bar>T (b *\<^sub>R e_k) \<bullet> (y - x)\<bar> = \<bar>(b *\<^sub>R e_k) \<bullet> inv T (y - x)\<bar>"
                  using T invT by (metis orthogonal_transformation_def eqb v b_def)
                also have "\<dots> = b * \<bar>e_k \<bullet> inv T (y - x)\<bar>"
                  using \<open>b > 0\<close> by (simp add: abs_mult)
                also have "\<dots> = b * \<bar>(inv T y - ?x') \<bullet> e_k\<bar>"
                  using orthogonal_transformation_linear [OF invT]
                  by (simp add: linear_diff inner_commute)
                finally show ?thesis
                  by simp
              qed
              show ?thesis
                using v b_def [symmetric]
                using \<open>b > 0\<close> by (simp add: * bij_image_Collect_eq [OF \<open>bij T\<close>] mult_less_cancel_left_pos times_divide_eq_right [symmetric] del: times_divide_eq_right)
            qed
            show ?thesis
              using 1 2 b_def by (simp add: image_Int [OF \<open>inj T\<close>])
          qed
          moreover have "?W' \<in> lmeasurable"
            by (auto intro: fmeasurable_Int_fmeasurable)
          moreover have "\<bar>eucl.det T\<bar> = 1"
          proof -
            note [transfer_rule] = transfer_measure_bij_rules transfer_eucl_bij_rules
            have "orthogonal_transformation f \<Longrightarrow> \<bar>eucl.det f\<bar> = 1" for f :: "'a \<Rightarrow> 'a"
              using orthogonal_transformation_det[unfolded orthogonal_transformation_def,
                where ?'n = "'a basis", untransferred]
              by (simp add: orthogonal_transformation_def)
            then show ?thesis using T by blast
          qed
          ultimately have "measure lebesgue ?W = measure lebesgue ?W'"
            using measure_orthogonal_image_eu [OF T] by simp
          also have "\<dots> \<le> measure lebesgue (cbox (?x' - ?v') (?x' + ?v'))"
          proof (rule measure_mono_fmeasurable)
            show "?W' \<subseteq> cbox (?x' - ?v') (?x' + ?v')"
            proof (intro subsetI)
              fix y assume "y \<in> ?W'"
              then have ball: "dist ?x' y < min d r"
                and ek_bound: "\<bar>(y - ?x') \<bullet> e_k\<bar> < e * min d r / (2 * real DIM('a) ^ DIM('a))"
                by auto
              have dist: "norm (y - ?x') < min d r"
                using ball by (simp add: dist_commute dist_norm)
              show "y \<in> cbox (?x' - ?v') (?x' + ?v')"
                sorry \<comment> \<open>component-wise: e_k direction from ek_bound, others from dist via Basis_le_norm\<close>
            qed
          qed auto
          also have "\<dots> \<le> e/2 * measure lebesgue (cbox (?x' - ?v) (?x' + ?v))"
          proof -
            have "cbox (?x' - ?v) (?x' + ?v) \<noteq> {}"
              using \<open>r > 0\<close> \<open>d > 0\<close>
              by (auto simp: box_ne_empty inner_diff_left inner_add_left inner_sum_left_Basis)
            with \<open>r > 0\<close> \<open>d > 0\<close> \<open>e > 0\<close> show ?thesis
              sorry
          qed
          also have "\<dots> \<le> e/2 * measure lebesgue (cball ?x' (min d r))"
          proof (rule mult_left_mono [OF measure_mono_fmeasurable])
            have *: "norm (?x' - y) \<le> min d r"
              if y: "\<And>i. i \<in> Basis \<Longrightarrow> \<bar>(?x' - y) \<bullet> i\<bar> \<le> min d r / real DIM('a)" for y
            proof -
              have "norm (?x' - y) \<le> (\<Sum>i\<in>Basis. \<bar>(?x' - y) \<bullet> i\<bar>)"
                by (rule norm_le_l1)
              also have "\<dots> \<le> real DIM('a) * (min d r / real DIM('a))"
                by (rule sum_bounded_above) (use y in auto)
              finally show ?thesis
                by simp
            qed
            show "cbox (?x' - ?v) (?x' + ?v) \<subseteq> cball ?x' (min d r)"
              apply (clarsimp simp only: mem_box dist_norm mem_cball intro!: *)
              sorry
          qed (use \<open>e > 0\<close> in auto)
          also have "\<dots> < e * content (cball ?x' (min d r))"
            using \<open>r > 0\<close> \<open>d > 0\<close> \<open>e > 0\<close> by (auto intro: content_cball_pos)
          also have "\<dots> = e * content (ball x (min d r))"
            using \<open>r > 0\<close> \<open>d > 0\<close> content_ball_conv_unit_ball[of "min d r" "inv T x"]
                  content_ball_conv_unit_ball[of "min d r" x]
            by (simp add: content_cball_conv_ball)
          finally show "measure lebesgue ?W < e * content (ball x (min d r))" .
      qed
    qed
    have *: "(\<And>x. (x \<notin> S) \<Longrightarrow> (x \<in> T \<longleftrightarrow> x \<in> U)) \<Longrightarrow> (T - U) \<union> (U - T) \<subseteq> S" for S T U :: "'a set"
      by blast
    have MN: "M \<subseteq> {x \<in> S. \<exists>v\<noteq>0. \<Theta> x v}"
      unfolding M_def
    proof (rule *)
      fix x
      assume x: "x \<notin> {x \<in> S. \<exists>v\<noteq>0. \<Theta> x v}"
      show "(x \<in> ?T) \<longleftrightarrow> (x \<in> {x \<in> S. f' x u \<bullet> v \<le> b})"
        sorry
    qed
    show "negligible M"
      using negligible_subset [OF nN MN] .
  qed
  then show ?thesis
    by (simp add: borel_measurable_vimage_halfspace_component_le sets_restrict_space_iff assms)
qed


theorem borel_measurable_det_Jacobian:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes S: "S \<in> sets lebesgue" and f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  shows "(\<lambda>x. eucl.det (f' x)) \<in> borel_measurable (lebesgue_on S)"
  unfolding eucl_det_def
  by (intro borel_measurable_sum borel_measurable_prod borel_measurable_times
            borel_measurable_const borel_measurable_partial_derivatives_eu [OF S])
     (auto intro: f)

corollary borel_measurable_det_Jacobian_matrix:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes S: "S \<in> sets lebesgue" and f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  shows "(\<lambda>x. matrix_det(matrix(f' x))) \<in> borel_measurable (lebesgue_on S)"
proof -
  have "(\<lambda>x. eucl.det (f' x)) \<in> borel_measurable (lebesgue_on S)"
    by (rule borel_measurable_det_Jacobian [OF S f])
  then show ?thesis
  proof (rule measurable_cong [THEN iffD2, rotated])
    fix w assume "w \<in> space (lebesgue_on S)"
    then have "w \<in> S"
      by (simp add: space_restrict_space)
    then have "linear (f' w)"
      using f has_derivative_linear by blast
    then show "matrix_det (matrix (f' w)) = eucl.det (f' w)"
      by (simp add: eucl_det_conv_matrix_det)
  qed
qed

text\<open>The localisation wrt S uses the same argument for many similar results.\<close>
(*See HOL Light's MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_BOREL, etc.*)
theorem borel_measurable_lebesgue_on_preimage_borel:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "S \<in> sets lebesgue"
  shows "f \<in> borel_measurable (lebesgue_on S) \<longleftrightarrow>
         (\<forall>T. T \<in> sets borel \<longrightarrow> {x \<in> S. f x \<in> T} \<in> sets lebesgue)"
proof -
  have "{x. (if x \<in> S then f x else 0) \<in> T} \<in> sets lebesgue \<longleftrightarrow> {x \<in> S. f x \<in> T} \<in> sets lebesgue"
         if "T \<in> sets borel" for T
    proof (cases "0 \<in> T")
      case True
      then have "{x \<in> S. f x \<in> T} = {x. (if x \<in> S then f x else 0) \<in> T} \<inter> S"
                "{x. (if x \<in> S then f x else 0) \<in> T} = {x \<in> S. f x \<in> T} \<union> -S"
        by auto
      then show ?thesis
        by (metis (no_types, lifting) Compl_in_sets_lebesgue assms sets.Int sets.Un)
    next
      case False
      then have "{x. (if x \<in> S then f x else 0) \<in> T} = {x \<in> S. f x \<in> T}"
        by auto
      then show ?thesis
        by auto
    qed
    then show ?thesis
      unfolding borel_measurable_lebesgue_preimage_borel borel_measurable_if [OF assms, symmetric]
      by blast
qed

lemma sets_lebesgue_almost_borel:
  assumes "S \<in> sets lebesgue"
  obtains B N where "B \<in> sets borel" "negligible N" "B \<union> N = S"
  by (metis assms negligible_iff_null_sets negligible_subset null_sets_completionI sets_completionE sets_lborel)

lemma double_lebesgue_sets:
 assumes S: "S \<in> sets lebesgue" and T: "T \<in> sets lebesgue" and fim: "f ` S \<subseteq> T"
 shows "(\<forall>U. U \<in> sets lebesgue \<and> U \<subseteq> T \<longrightarrow> {x \<in> S. f x \<in> U} \<in> sets lebesgue) \<longleftrightarrow>
          f \<in> borel_measurable (lebesgue_on S) \<and>
          (\<forall>U. negligible U \<and> U \<subseteq> T \<longrightarrow> {x \<in> S. f x \<in> U} \<in> sets lebesgue)"
         (is "?lhs \<longleftrightarrow> _ \<and> ?rhs")
  unfolding borel_measurable_lebesgue_on_preimage_borel [OF S]
proof (intro iffI allI conjI impI, safe)
  fix V :: "'b set"
  assume *: "\<forall>U. U \<in> sets lebesgue \<and> U \<subseteq> T \<longrightarrow> {x \<in> S. f x \<in> U} \<in> sets lebesgue"
    and "V \<in> sets borel"
  then have V: "V \<in> sets lebesgue"
    by simp
  have "{x \<in> S. f x \<in> V} = {x \<in> S. f x \<in> T \<inter> V}"
    using fim by blast
  also have "{x \<in> S. f x \<in> T \<inter> V} \<in> sets lebesgue"
    using T V * le_inf_iff by blast
  finally show "{x \<in> S. f x \<in> V} \<in> sets lebesgue" .
next
  fix U :: "'b set"
  assume "\<forall>U. U \<in> sets lebesgue \<and> U \<subseteq> T \<longrightarrow> {x \<in> S. f x \<in> U} \<in> sets lebesgue"
         "negligible U" "U \<subseteq> T"
  then show "{x \<in> S. f x \<in> U} \<in> sets lebesgue"
    using negligible_imp_sets by blast
next
  fix U :: "'b set"
  assume 1 [rule_format]: "(\<forall>T. T \<in> sets borel \<longrightarrow> {x \<in> S. f x \<in> T} \<in> sets lebesgue)"
     and 2 [rule_format]: "\<forall>U. negligible U \<and> U \<subseteq> T \<longrightarrow> {x \<in> S. f x \<in> U} \<in> sets lebesgue"
     and "U \<in> sets lebesgue" "U \<subseteq> T"
  then obtain C N where C: "C \<in> sets borel \<and> negligible N \<and> C \<union> N = U"
    using sets_lebesgue_almost_borel by metis
  then have "{x \<in> S. f x \<in> C} \<in> sets lebesgue"
    by (blast intro: 1)
  moreover have "{x \<in> S. f x \<in> N} \<in> sets lebesgue"
    using C \<open>U \<subseteq> T\<close> by (blast intro: 2)
  moreover have "{x \<in> S. f x \<in> C \<union> N} = {x \<in> S. f x \<in> C} \<union> {x \<in> S. f x \<in> N}"
    by auto
  ultimately show "{x \<in> S. f x \<in> U} \<in> sets lebesgue"
    using C by auto
qed


subsection\<open>Simplest case of Sard's theorem (we don't need continuity of derivative)\<close>

lemma Sard_lemma00:
  fixes P :: "'b::euclidean_space set"
  assumes "a \<ge> 0" and a: "a *\<^sub>R i \<noteq> 0" and i: "i \<in> Basis"
    and P: "P \<subseteq> {x. a *\<^sub>R i \<bullet> x = 0}"
    and "0 \<le> m" "0 \<le> e"
 obtains S where "S \<in> lmeasurable"
            and "{z. norm z \<le> m \<and> (\<exists>t \<in> P. norm(z - t) \<le> e)} \<subseteq> S"
            and "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (DIM('b) - 1)"
proof -
  have "a > 0"
    using assms by simp
  let ?v = "(\<Sum>j\<in>Basis. (if j = i then e else m) *\<^sub>R j)"
  show thesis
  proof
    have "- e \<le> x \<bullet> i" "x \<bullet> i \<le> e"
      if "t \<in> P" "norm (x - t) \<le> e" for x t
      using \<open>a > 0\<close> that Basis_le_norm [of i "x-t"] P i
      by (auto simp: inner_commute algebra_simps)
    moreover have "- m \<le> x \<bullet> j" "x \<bullet> j \<le> m"
      if "norm x \<le> m" "t \<in> P" "norm (x - t) \<le> e" "j \<in> Basis" and "j \<noteq> i"
      for x t j
      using that Basis_le_norm [of j x] by auto
    ultimately
    show "{z. norm z \<le> m \<and> (\<exists>t\<in>P. norm (z - t) \<le> e)} \<subseteq> cbox (-?v) ?v"
      by (auto simp: mem_box)
    have *: "\<forall>k\<in>Basis. - ?v \<bullet> k \<le> ?v \<bullet> k"
      using \<open>0 \<le> m\<close> \<open>0 \<le> e\<close> by (auto simp: inner_Basis)
    have 2: "2 ^ DIM('b) = 2 * 2 ^ (DIM('b) - Suc 0)"
      by (metis DIM_positive Suc_pred power_Suc)
    show "measure lebesgue (cbox (-?v) ?v) \<le> 2 * e * (2 * m) ^ (DIM('b) - 1)"
      using \<open>i \<in> Basis\<close>
      by (simp add: content_cbox [OF *] prod.distrib prod.If_cases Diff_eq [symmetric] 2)
  qed blast
qed

lemma orthogonal_transformation_exists_eu:
  fixes a b :: "'a::euclidean_space"
  assumes "norm a = norm b"
  obtains T where "orthogonal_transformation T" "T a = b"
proof -
  let ?a' = "eucl_to_vec a :: real ^ 'a basis"
  let ?b' = "eucl_to_vec b :: real ^ 'a basis"
  have norm_eq: "norm ?a' = norm ?b'"
    using assms
    by (metis (mono_tags) eucl_of_vec_to_vec transfer_eucl_norm rel_funD eucl_vec_rel_altdef)
  then obtain T' :: "real ^ 'a basis \<Rightarrow> real ^ 'a basis"
    where T': "orthogonal_transformation T'" "T' ?a' = ?b'"
    using orthogonal_transformation_exists by metis
  define T where "T = eucl_of_vec \<circ> T' \<circ> eucl_to_vec"
  have inner_eq: "T v \<bullet> T w = v \<bullet> w" for v w
  proof -
    have "T v \<bullet> T w = T' (eucl_to_vec v) \<bullet> T' (eucl_to_vec w)"
      unfolding T_def comp_def 
      by (metis (mono_tags) transfer_eucl_vec_inner rel_funD eucl_vec_rel_def)
    also have "\<dots> = eucl_to_vec v \<bullet> eucl_to_vec w"
      using T'(1) by (simp add: orthogonal_transformation_def)
    also have "\<dots> = v \<bullet> w"
      by (metis (mono_tags) eucl_vec_rel_altdef rel_funD transfer_eucl_vec_inner)
    finally show ?thesis .
  qed
  have "linear T"
  proof (rule linearI)
    fix x y :: 'a
    show "T (x + y) = T x + T y"
    proof -
      have "(T (x + y) - (T x + T y)) \<bullet> z = 0" for z
        unfolding inner_diff_left
        by (smt (verit) inner_commute inner_eq inner_right_distrib vector_eq)
      then show ?thesis
        by (metis all_zero_iff eq_iff_diff_eq_0)
    qed
  next
    fix c :: real and x :: 'a
    show "T (c *\<^sub>R x) = c *\<^sub>R T x"
    proof -
      have "(T (c *\<^sub>R x) - c *\<^sub>R T x) \<bullet> z = 0" for z
        unfolding inner_diff_left
        by (smt (verit, best) inner_commute inner_eq inner_right_distrib vector_eq inner_scaleR_left)
      then show ?thesis
        by (metis all_zero_iff eq_iff_diff_eq_0)
    qed
  qed
  then have "orthogonal_transformation T"
    using inner_eq by (simp add: orthogonal_transformation_def)
  moreover have "T a = b"
    unfolding T_def comp_def using T'(2) by simp
  ultimately show thesis
    using that by blast
qed

text\<open>As above, but reorienting the vector (HOL Light's @text{GEOM\_BASIS\_MULTIPLE\_TAC})\<close>
lemma Sard_lemma0:
  fixes P :: "'a::euclidean_space set"
  assumes "a \<noteq> 0"
    and P: "P \<subseteq> {x. a \<bullet> x = 0}" and "0 \<le> m" "0 \<le> e"
  obtains S where "S \<in> lmeasurable"
    and "{z. norm z \<le> m \<and> (\<exists>t \<in> P. norm(z - t) \<le> e)} \<subseteq> S"
    and "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (DIM('a) - 1)"
proof -
  obtain i :: 'a where i: "i \<in> Basis"
    using nonempty_Basis by blast
  have ni: "norm (norm a *\<^sub>R i) = norm a"
    using norm_Basis[OF i] by simp
  then obtain T where T: "orthogonal_transformation T" and a: "T (norm a *\<^sub>R i) = a"
    using orthogonal_transformation_exists_eu by metis
  have Tinv [simp]: "T (inv T x) = x" for x
    by (simp add: T orthogonal_transformation_surj surj_f_inv_f)
  obtain S where S: "S \<in> lmeasurable"
    and subS: "{z. norm z \<le> m \<and> (\<exists>t \<in> T-`P. norm(z - t) \<le> e)} \<subseteq> S"
    and mS: "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (DIM('a) - 1)"
  proof (rule Sard_lemma00 [of "norm a" i "T-`P" m e])
    have "norm a *\<^sub>R i \<bullet> x = 0" if "T x \<in> P" for x
    proof -
      have "norm a *\<^sub>R i \<bullet> x = T (norm a *\<^sub>R i) \<bullet> T x"
        using T by (simp add: orthogonal_transformation_def)
      also have "\<dots> = a \<bullet> T x"
        by (simp add: a)
      also have "\<dots> = 0"
        using P that by auto
      finally show ?thesis .
    qed
    then show "T -` P \<subseteq> {x. norm a *\<^sub>R i \<bullet> x = 0}"
      by auto
  qed (use assms T i in auto)
  show thesis
  proof
    show "T ` S \<in> lmeasurable"
      using S measurable_orthogonal_image_eu T by blast
    have "{z. norm z \<le> m \<and> (\<exists>t\<in>P. norm (z - t) \<le> e)} \<subseteq> T ` {z. norm z \<le> m \<and> (\<exists>t\<in>T -` P. norm (z - t) \<le> e)}"
    proof clarsimp
      fix x t
      assume \<section>: "norm x \<le> m" "t \<in> P" "norm (x - t) \<le> e"
      then have "norm (inv T x) \<le> m"
        using orthogonal_transformation_inv [OF T] by (simp add: orthogonal_transformation_norm)
      moreover have "\<exists>t\<in>T -` P. norm (inv T x - t) \<le> e"
      proof -
        have "inv T t \<in> T -` P"
          using \<open>t \<in> P\<close> by (simp add: vimage_def)
        moreover have "norm (inv T x - inv T t) \<le> e"
        proof -
          have "inv T x - inv T t = inv T (x - t)"
            using orthogonal_transformation_inv [OF T]
            by (simp add: linear_diff orthogonal_transformation_linear)
          also have "norm \<dots> = norm (x - t)"
            using orthogonal_transformation_inv [OF T] by (simp add: orthogonal_transformation_norm)
          finally show ?thesis
            using \<section>(3) by simp
        qed
        ultimately show ?thesis by auto
      qed
      ultimately show "x \<in> T ` {z. norm z \<le> m \<and> (\<exists>t\<in>T -` P. norm (z - t) \<le> e)}"
        by force
    qed
    then show "{z. norm z \<le> m \<and> (\<exists>t\<in>P. norm (z - t) \<le> e)} \<subseteq> T ` S"
      using image_mono [OF subS] by (rule order_trans)
    show "measure lebesgue (T ` S) \<le> 2 * e * (2 * m) ^ (DIM('a) - 1)"
    proof -
      have linT: "linear T" and linTi: "linear (inv T)"
        using T orthogonal_transformation_inv [OF T]
        by (auto simp: orthogonal_transformation_linear)
      have "T \<circ> inv T = id"
        using T orthogonal_transformation_surj surj_f_inv_f by fastforce
      then have "eucl.det T * eucl.det (inv T) = 1"
        using eucl.det_compose [OF linT linTi] by simp
      have "\<bar>eucl.det T\<bar> = 1"
      proof -
        note [transfer_rule] = transfer_measure_bij_rules transfer_eucl_bij_rules
        have "orthogonal_transformation f \<Longrightarrow> \<bar>eucl.det f\<bar> = 1" for f :: "'a \<Rightarrow> 'a"
          using orthogonal_transformation_det[unfolded orthogonal_transformation_def,
            where ?'n = "'a basis", untransferred]
          by (simp add: orthogonal_transformation_def)
        then show ?thesis using T by blast
      qed
      then have "measure lebesgue (T ` S) = measure lebesgue S"
        using measure_orthogonal_image_eu [OF T S] by simp
      then show ?thesis using mS by simp
    qed
  qed
qed


text\<open>As above, but translating the sets (HOL Light's @text{GEN\_GEOM\_ORIGIN\_TAC})\<close>
lemma Sard_lemma1:
  fixes P :: "'a::euclidean_space set"
   assumes P: "dim P < DIM('a)" and "0 \<le> m" "0 \<le> e"
 obtains S where "S \<in> lmeasurable"
            and "{z. norm(z - w) \<le> m \<and> (\<exists>t \<in> P. norm(z - w - t) \<le> e)} \<subseteq> S"
            and "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (DIM('a) - 1)"
proof -
  obtain a where "a \<noteq> 0" "P \<subseteq> {x. a \<bullet> x = 0}"
    using lowdim_subset_hyperplane [of P] P span_base by auto
  then obtain S where S: "S \<in> lmeasurable"
    and subS: "{z. norm z \<le> m \<and> (\<exists>t \<in> P. norm(z - t) \<le> e)} \<subseteq> S"
    and mS: "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (DIM('a) - 1)"
    by (rule Sard_lemma0 [OF _ _ \<open>0 \<le> m\<close> \<open>0 \<le> e\<close>])
  show thesis
  proof
    show "(+)w ` S \<in> lmeasurable"
      by (metis measurable_translation S)
    show "{z. norm (z - w) \<le> m \<and> (\<exists>t\<in>P. norm (z - w - t) \<le> e)} \<subseteq> (+)w ` S"
      using subS by force
    show "measure lebesgue ((+)w ` S) \<le> 2 * e * (2 * m) ^ (DIM('a) - 1)"
      by (metis measure_translation mS)
  qed
qed

theorem baby_Sard_eu:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes mlen: "DIM('a) \<le> DIM('b)"
    and der: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and low_rank: "\<And>x. x \<in> S \<Longrightarrow> dim (f' x ` UNIV) < DIM('b)"
  shows "negligible(f ` S)"
proof -
  let ?etv_a = "eucl_to_vec :: 'a \<Rightarrow> real^('a basis)"
  let ?eov_a = "eucl_of_vec :: real^('a basis) \<Rightarrow> 'a"
  let ?etv_b = "eucl_to_vec :: 'b \<Rightarrow> real^('b basis)"
  let ?eov_b = "eucl_of_vec :: real^('b basis) \<Rightarrow> 'b"
  define fv where "fv \<equiv> ?etv_b \<circ> f \<circ> ?eov_a"
  define Sv where "Sv \<equiv> ?etv_a ` S"
  define fv' where "fv' \<equiv> \<lambda>x. ?etv_b \<circ> f' (?eov_a x) \<circ> ?eov_a"
  have card_eq_a: "CARD('a basis) = DIM('a)"
    using UNIV_basis_eq inj_Abs_basis by (metis card_image)
  have card_eq_b: "CARD('b basis) = DIM('b)"
    using UNIV_basis_eq inj_Abs_basis by (metis card_image)
  have lin_etv_b: "linear ?etv_b"
    unfolding eucl_to_vec_def linear_iff
    by (auto simp: vec_eq_iff inner_left_distrib inner_right_distrib)
  have lin_eov_a: "linear ?eov_a"
    unfolding eucl_of_vec_def linear_iff
    by (auto simp: scaleR_sum_right algebra_simps sum.distrib)
  have Sv_eq: "?eov_a ` Sv = S"
    by (auto simp: Sv_def image_comp)
  have inj_etv_b: "inj ?etv_b"
    by (simp add: inj_def)
  have der_v: "(fv has_derivative fv' x) (at x within Sv)" if "x \<in> Sv" for x
  proof -
    have x_in: "?eov_a x \<in> S"
      using that by (auto simp: Sv_def)
    have step1: "(f \<circ> ?eov_a has_derivative f' (?eov_a x) \<circ> ?eov_a) (at x within Sv)"
      by (rule diff_chain_within [OF linear_imp_has_derivative [OF lin_eov_a]])
         (use der x_in Sv_eq in auto)
    show ?thesis
      unfolding fv_def fv'_def comp_assoc
      by (rule diff_chain_within [OF step1 linear_imp_has_derivative [OF lin_etv_b]])
  qed
  have lin_fv': "linear (fv' x)" if "x \<in> Sv" for x
  proof -
    have x_in: "?eov_a x \<in> S"
      using that by (auto simp: Sv_def)
    show ?thesis
      unfolding fv'_def comp_def
      using lin_etv_b lin_eov_a has_derivative_linear [OF der [OF x_in]]
      by (auto intro!: linearI simp: linear_add linear_cmul)
  qed
  have rank_v: "rank (matrix (fv' x)) < CARD('b basis)" if "x \<in> Sv" for x
  proof -
    have x_in: "?eov_a x \<in> S"
      using that by (auto simp: Sv_def)
    have "rank (matrix (fv' x)) = dim (range (fv' x))"
      using rank_dim_range [of "matrix (fv' x)"] lin_fv' [OF that]
      by (simp add: matrix_works)
    also have "range (fv' x) = ?etv_b ` (f' (?eov_a x) ` range ?eov_a)"
      by (auto simp: fv'_def image_comp)
    also have "range ?eov_a = (UNIV :: 'a set)"
      using surj_def by (auto intro: image_eqI [of _ _ "?etv_a _"])
    also have "dim (?etv_b ` (f' (?eov_a x) ` UNIV)) = dim (f' (?eov_a x) ` UNIV)"
      by (rule eucl.dim_image_eq [OF lin_etv_b])
         (meson inj_etv_b inj_on_subset subset_UNIV)
    also have "\<dots> < DIM('b)"
      using low_rank x_in by auto
    finally show ?thesis
      using card_eq_b by simp
  qed
  have mlen_v: "CARD('a basis) \<le> CARD('b basis)"
    using mlen card_eq_a card_eq_b by simp
  have "negligible (fv ` Sv)"
    by (rule baby_Sard [OF mlen_v der_v rank_v])
  moreover have "fv ` Sv = ?etv_b ` (f ` S)"
    by (auto simp: fv_def Sv_def image_comp)
  ultimately have neg_etv: "negligible (?etv_b ` (f ` S))"
    by simp
  show "negligible (f ` S)"
  proof (rule negligible_subset [OF _ subset_refl])
    have "f ` S = ?eov_b ` (?etv_b ` (f ` S))"
      by (simp add: image_comp)
    also have "negligible \<dots>"
    proof -
      have "linear ?eov_b"
        unfolding eucl_of_vec_def linear_iff
        by (auto simp: scaleR_sum_right algebra_simps sum.distrib)
      then have diff: "?eov_b differentiable_on ?etv_b ` (f ` S)"
        by (rule linear_imp_differentiable_on)
      show ?thesis
        by (rule negligible_differentiable_image_negligible [OF _ neg_etv diff]) (simp add: card_eq_b)
    qed
    finally show "negligible (f ` S)" .
  qed
qed


subsection\<open>A one-way version of change-of-variables not assuming injectivity. \<close>

lemma integral_on_image_ubound_weak_eu:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
      and f: "f \<in> borel_measurable (lebesgue_on (g ` S))"
      and nonneg_fg:  "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f(g x)"
      and der_g:   "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and det_int_fg: "(\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x)) integrable_on S"
      and meas_gim: "\<And>T. \<lbrakk>T \<subseteq> g ` S; T \<in> sets lebesgue\<rbrakk> \<Longrightarrow> {x \<in> S. g x \<in> T} \<in> sets lebesgue"
    shows "f integrable_on (g ` S) \<and>
           integral (g ` S) f \<le> integral S (\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x))"
         (is "_ \<and> _ \<le> ?b")
proof -
  let ?D = "\<lambda>x. \<bar>eucl.det (g' x)\<bar>"
  have cont_g: "continuous_on S g"
    using der_g has_derivative_continuous_on by blast
  have [simp]: "space (lebesgue_on S) = S"
    by (simp add: S)
  have gS_in_sets_leb: "g ` S \<in> sets lebesgue"
    apply (rule differentiable_image_in_sets_lebesgue)
    using der_g by (auto simp: S differentiable_def differentiable_on_def)
  obtain h where nonneg_h: "\<And>n x. 0 \<le> h n x"
    and h_le_f: "\<And>n x. x \<in> S \<Longrightarrow> h n (g x) \<le> f (g x)"
    and h_inc: "\<And>n x. h n x \<le> h (Suc n) x"
    and h_meas: "\<And>n. h n \<in> borel_measurable lebesgue"
    and fin_R: "\<And>n. finite(range (h n))"
    and lim: "\<And>x. x \<in> g ` S \<Longrightarrow> (\<lambda>n. h n x) \<longlonglongrightarrow> f x"
  proof -
    let ?f = "\<lambda>x. if x \<in> g ` S then f x else 0"
    have "?f \<in> borel_measurable lebesgue \<and> (\<forall>x. 0 \<le> ?f x)"
      by (auto simp: gS_in_sets_leb f nonneg_fg measurable_restrict_space_iff [symmetric])
    then show ?thesis
      apply (clarsimp simp add: borel_measurable_simple_function_limit_increasing)
      apply (rename_tac h)
      by (rule_tac h=h in that) (auto split: if_split_asm)
  qed
  have h_lmeas: "{t. h n (g t) = y} \<inter> S \<in> sets lebesgue" for y n
  proof -
    have "space (lebesgue_on (UNIV::'a set)) = UNIV"
      by simp
    then have "((h n) -`{y} \<inter> g ` S) \<in> sets (lebesgue_on (g ` S))"
      by (metis Int_commute borel_measurable_vimage h_meas image_eqI inf_top.right_neutral sets_restrict_space space_borel space_completion space_lborel)
    then have "({u. h n u = y} \<inter> g ` S) \<in> sets lebesgue"
      using gS_in_sets_leb
      by (simp add: integral_indicator fmeasurableI2 sets_restrict_space_iff vimage_def)
    then have "{x \<in> S. g x \<in> ({u. h n u = y} \<inter> g ` S)} \<in> sets lebesgue"
      using meas_gim[of "({u. h n u = y} \<inter> g ` S)"] by force
    moreover have "{t. h n (g t) = y} \<inter> S = {x \<in> S. g x \<in> ({u. h n u = y} \<inter> g ` S)}"
      by blast
    ultimately show ?thesis
      by auto
  qed
  have hint: "h n integrable_on g ` S \<and> integral (g ` S) (h n) \<le> integral S (\<lambda>x. ?D x * h n (g x))"
          (is "?INT \<and> ?lhs \<le> ?rhs")  for n
  proof -
    let ?R = "range (h n)"
    have hn_eq: "h n = (\<lambda>x. \<Sum>y\<in>?R. y * indicat_real {x. h n x = y} x)"
      by (simp add: indicator_def if_distrib fin_R cong: if_cong)
    have yind: "(\<lambda>t. y * indicator{x. h n x = y} t) integrable_on (g ` S) \<and>
                (integral (g ` S) (\<lambda>t. y * indicator {x. h n x = y} t))
                 \<le> integral S (\<lambda>t. \<bar>eucl.det (g' t)\<bar> * y * indicator {x. h n x = y} (g t))"
       if y: "y \<in> ?R" for y::real
    proof (cases "y=0")
      case True
      then show ?thesis using gS_in_sets_leb integrable_0 by force
    next
      case False
      with that have "y > 0"
        using less_eq_real_def nonneg_h by fastforce
      have "(\<lambda>x. if x \<in> {t. h n (g t) = y} then ?D x else 0) integrable_on S"
      proof (rule measurable_bounded_by_integrable_imp_integrable)
        have "(\<lambda>x. ?D x) \<in> borel_measurable (lebesgue_on ({t. h n (g t) = y} \<inter> S))"
        proof -
          have "(\<lambda>v. eucl.det (g' v)) \<in> borel_measurable (lebesgue_on (S \<inter> {v. h n (g v) = y}))"
            by (metis Int_lower1 S assms(4) borel_measurable_det_Jacobian measurable_restrict_mono)
          then show ?thesis
            by (simp add: Int_commute)
        qed
        then have "(\<lambda>x. if x \<in> {t. h n (g t) = y} \<inter> S then ?D x else 0) \<in> borel_measurable lebesgue"
          by (rule borel_measurable_if_I [OF _ h_lmeas])
        then show "(\<lambda>x. if x \<in> {t. h n (g t) = y} then ?D x else 0) \<in> borel_measurable (lebesgue_on S)"
          by (simp add: if_if_eq_conj Int_commute borel_measurable_if [OF S, symmetric])
        show "(\<lambda>x. ?D x *\<^sub>R f (g x) /\<^sub>R y) integrable_on S"
          by (rule integrable_cmul) (use det_int_fg in auto)
        show "norm (if x \<in> {t. h n (g t) = y} then ?D x else 0) \<le> ?D x *\<^sub>R f (g x) /\<^sub>R y"
          if "x \<in> S" for x
          using nonneg_h [of n x] \<open>y > 0\<close> nonneg_fg [of x] h_le_f [of x n] that
          by (auto simp: divide_simps mult_left_mono)
      qed (use S in auto)
      then have int_det: "(\<lambda>t. \<bar>eucl.det (g' t)\<bar>) integrable_on ({t. h n (g t) = y} \<inter> S)"
        using integrable_restrict_Int by force
      have "(g ` ({t. h n (g t) = y} \<inter> S)) \<in> lmeasurable"
        by (blast intro: has_derivative_subset [OF der_g] measurable_differentiable_image_eu [OF h_lmeas] int_det)
      moreover have "g ` ({t. h n (g t) = y} \<inter> S) = {x. h n x = y} \<inter> g ` S"
        by blast
      moreover have "measure lebesgue (g ` ({t. h n (g t) = y} \<inter> S))
                     \<le> integral ({t. h n (g t) = y} \<inter> S) (\<lambda>t. \<bar>eucl.det (g' t)\<bar>)"
        by (blast intro: has_derivative_subset [OF der_g] measure_differentiable_image_eu [OF h_lmeas _ int_det])
      ultimately show ?thesis
        using \<open>y > 0\<close> integral_restrict_Int [of S "{t. h n (g t) = y}" "\<lambda>t. \<bar>eucl.det (g' t)\<bar> * y"]
        apply (simp add: integrable_on_indicator integral_indicator)
        apply (simp add: indicator_def of_bool_def if_distrib cong: if_cong)
        done
    qed
    show ?thesis
    proof
      show "h n integrable_on g ` S"
        apply (subst hn_eq)
        using yind by (force intro: integrable_sum [OF fin_R])
      have "?lhs = integral (g ` S) (\<lambda>x. \<Sum>y\<in>range (h n). y * indicat_real {x. h n x = y} x)"
        by (metis hn_eq)
      also have "\<dots> = (\<Sum>y\<in>range (h n). integral (g ` S) (\<lambda>x. y * indicat_real {x. h n x = y} x))"
        by (rule integral_sum [OF fin_R]) (use yind in blast)
      also have "\<dots> \<le> (\<Sum>y\<in>range (h n). integral S (\<lambda>u. \<bar>eucl.det (g' u)\<bar> * y * indicat_real {x. h n x = y} (g u)))"
        using yind by (force intro: sum_mono)
      also have "\<dots> = integral S (\<lambda>u. \<Sum>y\<in>range (h n). \<bar>eucl.det (g' u)\<bar> * y * indicat_real {x. h n x = y} (g u))"
      proof (rule integral_sum [OF fin_R, symmetric])
        fix y assume y: "y \<in> ?R"
        with nonneg_h have "y \<ge> 0"
          by auto
        show "(\<lambda>u. \<bar>eucl.det (g' u)\<bar> * y * indicat_real {x. h n x = y} (g u)) integrable_on S"
        proof (rule measurable_bounded_by_integrable_imp_integrable)
          have "(\<lambda>x. indicat_real {x. h n x = y} (g x)) \<in> borel_measurable (lebesgue_on S)"
            using h_lmeas S
            by (auto simp: indicator_vimage [symmetric] borel_measurable_indicator_iff sets_restrict_space_iff)
          then show "(\<lambda>u. \<bar>eucl.det (g' u)\<bar> * y * indicat_real {x. h n x = y} (g u)) \<in> borel_measurable (lebesgue_on S)"
            by (intro borel_measurable_times borel_measurable_abs borel_measurable_const borel_measurable_det_Jacobian [OF S der_g])
        next
          fix x
          assume "x \<in> S"
          then have "y * indicat_real {x. h n x = y} (g x) \<le> f (g x)"
            by (metis (full_types) h_le_f indicator_simps mem_Collect_eq mult.right_neutral mult_zero_right nonneg_fg)
          with \<open>y \<ge> 0\<close> show "norm (?D x * y * indicat_real {x. h n x = y} (g x)) \<le> ?D x * f(g x)"
            by (simp add: abs_mult mult.assoc mult_left_mono)
        qed (use S det_int_fg in auto)
      qed
      also have "\<dots> = integral S (\<lambda>T. \<bar>eucl.det (g' T)\<bar> *
                                        (\<Sum>y\<in>range (h n). y * indicat_real {x. h n x = y} (g T)))"
        by (simp add: sum_distrib_left mult.assoc)
      also have "\<dots> = ?rhs"
        by (metis hn_eq)
      finally show "integral (g ` S) (h n) \<le> ?rhs" .
    qed
  qed
  have le: "integral S (\<lambda>T. \<bar>eucl.det (g' T)\<bar> * h n (g T)) \<le> ?b" for n
  proof (rule integral_le)
    show "(\<lambda>T. \<bar>eucl.det (g' T)\<bar> * h n (g T)) integrable_on S"
    proof (rule measurable_bounded_by_integrable_imp_integrable)
      have "(\<lambda>T. \<bar>eucl.det (g' T)\<bar> *\<^sub>R h n (g T)) \<in> borel_measurable (lebesgue_on S)"
      proof (intro borel_measurable_scaleR borel_measurable_abs borel_measurable_det_Jacobian \<open>S \<in> sets lebesgue\<close>)
        have eq: "{x \<in> S. f x \<le> a} = (\<Union>b \<in> (f ` S) \<inter> atMost a. {x. f x = b} \<inter> S)" for f and a::real
          by auto
        have "finite ((\<lambda>x. h n (g x)) ` S \<inter> {..a})" for a
          by (force intro: finite_subset [OF _ fin_R])
        with h_lmeas [of n] show "(\<lambda>x. h n (g x)) \<in> borel_measurable (lebesgue_on S)"
          apply (simp add: borel_measurable_vimage_halfspace_component_le \<open>S \<in> sets lebesgue\<close> sets_restrict_space_iff eq)
          by (metis (mono_tags) SUP_inf sets.finite_UN)
      qed (use der_g in blast)
      then show "(\<lambda>T. \<bar>eucl.det (g' T)\<bar> * h n (g T)) \<in> borel_measurable (lebesgue_on S)"
        by simp
      show "norm (?D x * h n (g x)) \<le> ?D x *\<^sub>R f (g x)"
        if "x \<in> S" for x
        by (simp add: h_le_f mult_left_mono nonneg_h that)
    qed (use S det_int_fg in auto)
    show "?D x * h n (g x) \<le> ?D x * f (g x)" if "x \<in> S" for x
      by (simp add: \<open>x \<in> S\<close> h_le_f mult_left_mono)
    show "(\<lambda>x. ?D x * f (g x)) integrable_on S"
      using det_int_fg by blast
  qed
  have "f integrable_on g ` S \<and> (\<lambda>k. integral (g ` S) (h k)) \<longlonglongrightarrow> integral (g ` S) f"
  proof (rule monotone_convergence_increasing)
    have "\<bar>integral (g ` S) (h n)\<bar> \<le> integral S (\<lambda>x. ?D x * f (g x))" for n
    proof -
      have "\<bar>integral (g ` S) (h n)\<bar> = integral (g ` S) (h n)"
        using hint by (simp add: integral_nonneg nonneg_h)
      also have "\<dots> \<le> integral S (\<lambda>x. ?D x * f (g x))"
        using hint le by (meson order_trans)
      finally show ?thesis .
    qed
    then show "bounded (range (\<lambda>k. integral (g ` S) (h k)))"
      by (force simp: bounded_iff)
  qed (use h_inc lim hint in auto)
  moreover have "integral (g ` S) (h n) \<le> integral S (\<lambda>x. ?D x * f (g x))" for n
    using hint by (blast intro: le order_trans)
  ultimately show ?thesis
    by (auto intro: Lim_bounded)
qed

lemma integral_on_image_ubound_nonneg_eu:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes nonneg_fg: "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f(g x)"
      and der_g:   "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and intS: "(\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x)) integrable_on S"
  shows "f integrable_on (g ` S) \<and> integral (g ` S) f \<le> integral S (\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x))"
         (is "_ \<and> _ \<le> ?b")
proof -
  let ?D = "\<lambda>x. eucl.det (g' x)"
  define S' where "S' \<equiv> {x \<in> S. ?D x * f(g x) \<noteq> 0}"
  then have der_gS': "\<And>x. x \<in> S' \<Longrightarrow> (g has_derivative g' x) (at x within S')"
    by (metis (mono_tags, lifting) der_g has_derivative_subset mem_Collect_eq subset_iff)
  have "(\<lambda>x. if x \<in> S then \<bar>?D x\<bar> * f (g x) else 0) integrable_on UNIV"
    by (simp add: integrable_restrict_UNIV intS)
  then have Df_borel: "(\<lambda>x. if x \<in> S then \<bar>?D x\<bar> * f (g x) else 0) \<in> borel_measurable lebesgue"
    using integrable_imp_measurable lebesgue_on_UNIV_eq by force
  have S': "S' \<in> sets lebesgue"
  proof -
    from Df_borel borel_measurable_vimage_open [of _ UNIV]
    have "{x. (if x \<in> S then \<bar>?D x\<bar> * f (g x) else 0) \<in> T} \<in> sets lebesgue"
      if "open T" for T
      using that unfolding lebesgue_on_UNIV_eq
      by (fastforce simp add: dest!: spec)
    then have "{x. (if x \<in> S then \<bar>?D x\<bar> * f (g x) else 0) \<in> -{0}} \<in> sets lebesgue"
      using open_Compl by blast
    then show ?thesis
      by (simp add: S'_def conj_ac split: if_split_asm cong: conj_cong)
  qed
  then have gS': "g ` S' \<in> sets lebesgue"
  proof (rule differentiable_image_in_sets_lebesgue)
    show "g differentiable_on S'"
      using der_g unfolding S'_def differentiable_def differentiable_on_def
      by (blast intro: has_derivative_subset)
  qed auto
  have f: "f \<in> borel_measurable (lebesgue_on (g ` S'))"
  proof (clarsimp simp add: borel_measurable_vimage_open)
    fix T :: "real set"
    assume "open T"
    have "{x \<in> g ` S'. f x \<in> T} = g ` {x \<in> S'. f(g x) \<in> T}"
      by blast
    moreover have "g ` {x \<in> S'. f(g x) \<in> T} \<in> sets lebesgue"
    proof (rule differentiable_image_in_sets_lebesgue)
      let ?h = "\<lambda>x. \<bar>?D x\<bar> * f (g x) /\<^sub>R \<bar>?D x\<bar>"
      have "(\<lambda>x. if x \<in> S' then \<bar>?D x\<bar> * f (g x) else 0) = (\<lambda>x. if x \<in> S then \<bar>?D x\<bar> * f (g x) else 0)"
        by (auto simp: S'_def)
      also have "\<dots> \<in> borel_measurable lebesgue"
        by (rule Df_borel)
      finally have *: "(\<lambda>x. \<bar>?D x\<bar> * f (g x)) \<in> borel_measurable (lebesgue_on S')"
        by (simp add: borel_measurable_if_D)
      have "(\<lambda>v. eucl.det (g' v)) \<in> borel_measurable (lebesgue_on S')"
        using S' borel_measurable_det_Jacobian der_gS' by blast
      then have "?h \<in> borel_measurable (lebesgue_on S')"
        using "*" borel_measurable_abs borel_measurable_inverse borel_measurable_scaleR by blast
      moreover have "?h x = f(g x)" if "x \<in> S'" for x
        using that by (auto simp: S'_def)
      ultimately have "(\<lambda>x. f(g x)) \<in> borel_measurable (lebesgue_on S')"
        by (metis (no_types, lifting) measurable_lebesgue_cong)
      then show "{x \<in> S'. f (g x) \<in> T} \<in> sets lebesgue"
        by (simp add: \<open>S' \<in> sets lebesgue\<close> \<open>open T\<close> borel_measurable_vimage_open sets_restrict_space_iff)
      show "g differentiable_on {x \<in> S'. f (g x) \<in> T}"
        using der_g unfolding S'_def differentiable_def differentiable_on_def
        by (blast intro: has_derivative_subset)
    qed auto
    ultimately have "{x \<in> g ` S'. f x \<in> T} \<in> sets lebesgue"
      by metis
    then show "{x \<in> g ` S'. f x \<in> T} \<in> sets (lebesgue_on (g ` S'))"
      by (simp add: \<open>g ` S' \<in> sets lebesgue\<close> sets_restrict_space_iff)
  qed
  have intS': "(\<lambda>x. \<bar>?D x\<bar> * f (g x)) integrable_on S'"
    using intS
    by (rule integrable_spike_set) (auto simp: S'_def intro: empty_imp_negligible)
  have lebS': "{x \<in> S'. g x \<in> T} \<in> sets lebesgue" if "T \<subseteq> g ` S'" "T \<in> sets lebesgue" for T
  proof -
    have "g \<in> borel_measurable (lebesgue_on S')"
      using der_gS' has_derivative_continuous_on S'
      by (blast intro: continuous_imp_measurable_on_sets_lebesgue)
    moreover have "{x \<in> S'. g x \<in> U} \<in> sets lebesgue" if "negligible U" "U \<subseteq> g ` S'" for U
    proof (intro negligible_imp_sets negligible_differentiable_vimage that)
      fix x
      assume x: "x \<in> S'"
      then have "linear (g' x)"
        using der_gS' has_derivative_linear by blast
      with x show "inj (g' x)"
        using eucl.det_eq_0_iff by (auto simp: S'_def)
    qed (use der_gS' in auto)
    ultimately show ?thesis
      using double_lebesgue_sets [OF S' gS' order_refl] that by blast
  qed
  have int_gS': "f integrable_on g ` S' \<and> integral (g ` S') f \<le> integral S' (\<lambda>x. \<bar>?D x\<bar> * f(g x))"
    using integral_on_image_ubound_weak_eu [OF S' f nonneg_fg der_gS' intS' lebS'] S'_def by blast
  have neg_det: "negligible (g ` {x \<in> S. eucl.det (g' x) = 0})"
  proof (rule baby_Sard_eu [OF order_refl], simp_all)
    fix x
    assume x: "x \<in> S \<and> eucl.det (g' x) = 0"
    then show "(g has_derivative g' x) (at x within {x \<in> S. eucl.det (g' x) = 0})"
      by (metis (no_types, lifting) der_g has_derivative_subset mem_Collect_eq subsetI)
    have "linear (g' x)"
      using \<open>(g has_derivative g' x) _\<close> has_derivative_linear by blast
    then have "\<not> inj (g' x)"
      using x eucl.det_eq_0_iff by auto
    then have "\<not> surj (g' x)"
      using \<open>linear (g' x)\<close> eucl.linear_surjective_imp_injective by auto
    then have "g' x ` UNIV \<noteq> UNIV"
      by (simp add: surj_def)
    moreover have "subspace (g' x ` UNIV)"
      using \<open>linear (g' x)\<close> linear_subspace_image subspace_UNIV by blast
    ultimately show "dim (g' x ` UNIV) < DIM('a)"
      using eucl.subspace_dim_equal [of "g' x ` UNIV" UNIV] subspace_UNIV eucl.dim_UNIV
      by (metis eucl.dim_subset le_neq_implies_less subset_UNIV)
  qed
  then have negg: "negligible (g ` S - g ` {x \<in> S. ?D x \<noteq> 0})"
    by (rule negligible_subset) (auto simp: S'_def)
  have null: "g ` {x \<in> S. ?D x \<noteq> 0} - g ` S = {}"
    by (auto simp: S'_def)
  let ?F = "{x \<in> S. f (g x) \<noteq> 0}"
  have eq: "g ` S' = g ` ?F \<inter> g ` {x \<in> S. ?D x \<noteq> 0}"
    by (auto simp: S'_def image_iff)
  show ?thesis
  proof
    have "((\<lambda>x. if x \<in> g ` ?F then f x else 0) integrable_on g ` {x \<in> S. ?D x \<noteq> 0})"
      using int_gS' eq integrable_restrict_Int [where f=f]
      by simp
    then have "f integrable_on g ` {x \<in> S. ?D x \<noteq> 0}"
      by (auto simp: image_iff elim!: integrable_eq)
    then show "f integrable_on g ` S"
      using negg null
      by (auto intro: integrable_spike_set [OF _ empty_imp_negligible negligible_subset])
    have "integral (g ` S) f = integral (g ` {x \<in> S. ?D x \<noteq> 0}) f"
      using negg by (auto intro: negligible_subset integral_spike_set)
    also have "\<dots> = integral (g ` {x \<in> S. ?D x \<noteq> 0}) (\<lambda>x. if x \<in> g ` ?F then f x else 0)"
      by (auto simp: image_iff intro!: integral_cong)
    also have "\<dots> = integral (g ` S') f"
      using eq integral_restrict_Int by simp
    also have "\<dots> \<le> integral S' (\<lambda>x. \<bar>?D x\<bar> * f(g x))"
      by (metis int_gS')
    also have "\<dots> \<le> ?b"
      by (rule integral_subset_le [OF _ intS' intS]) (use nonneg_fg S'_def in auto)
    finally show "integral (g ` S) f \<le> ?b" .
  qed
qed

lemma absolutely_integrable_on_image_real_eu:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and g :: "'a \<Rightarrow> 'a"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and intS: "(\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x)) absolutely_integrable_on S"
  shows "f absolutely_integrable_on (g ` S)"
proof -
  let ?D = "\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f (g x)"
  let ?N = "{x \<in> S. f (g x) < 0}" and ?P = "{x \<in> S. f (g x) > 0}"
  have eq: "{x. (if x \<in> S then ?D x else 0) > 0} = {x \<in> S. ?D x > 0}"
           "{x. (if x \<in> S then ?D x else 0) < 0} = {x \<in> S. ?D x < 0}"
    by auto
  have "?D integrable_on S"
    using intS absolutely_integrable_on_def by blast
  then have "(\<lambda>x. if x \<in> S then ?D x else 0) integrable_on UNIV"
    by (simp add: integrable_restrict_UNIV)
  then have D_borel: "(\<lambda>x. if x \<in> S then ?D x else 0) \<in> borel_measurable (lebesgue_on UNIV)"
    using integrable_imp_measurable lebesgue_on_UNIV_eq by blast
  then have Dlt: "{x \<in> S. ?D x < 0} \<in> sets lebesgue"
    unfolding borel_measurable_vimage_halfspace_component_lt
    by (drule_tac x=0 in spec) (auto simp: eq)
  from D_borel have Dgt: "{x \<in> S. ?D x > 0} \<in> sets lebesgue"
    unfolding borel_measurable_vimage_halfspace_component_gt
    by (drule_tac x=0 in spec) (auto simp: eq)

  have dfgbm: "?D \<in> borel_measurable (lebesgue_on S)"
    using intS absolutely_integrable_on_def integrable_imp_measurable by blast
  have der_gN: "(g has_derivative g' x) (at x within ?N)" if "x \<in> ?N" for x
      using der_g has_derivative_subset that by force
  have "(\<lambda>x. - f x) integrable_on g ` ?N \<and>
         integral (g ` ?N) (\<lambda>x. - f x) \<le> integral ?N (\<lambda>x. \<bar>eucl.det (g' x)\<bar> * - f (g x))"
  proof (rule integral_on_image_ubound_nonneg_eu [OF _ der_gN])
    have 1: "?D integrable_on {x \<in> S. ?D x < 0}"
      using Dlt
      by (auto intro: set_lebesgue_integral_eq_integral [OF set_integrable_subset] intS)
    have "uminus \<circ> (\<lambda>x. \<bar>eucl.det (g' x)\<bar> * - f (g x)) integrable_on ?N"
      by (simp add: o_def mult_less_0_iff empty_imp_negligible integrable_spike_set [OF 1])
    then show "(\<lambda>x. \<bar>eucl.det (g' x)\<bar> * - f (g x)) integrable_on ?N"
      by (simp add: integrable_neg_iff o_def)
  qed auto
  then have "f integrable_on g ` ?N"
    by (simp add: integrable_neg_iff)
  moreover have "g ` ?N = {y \<in> g ` S. f y < 0}"
    by auto
  ultimately have "f integrable_on {y \<in> g ` S. f y < 0}"
    by simp
  then have N: "f absolutely_integrable_on {y \<in> g ` S. f y < 0}"
    by (rule absolutely_integrable_absolutely_integrable_ubound) auto

  have der_gP: "(g has_derivative g' x) (at x within ?P)" if "x \<in> ?P" for x
      using der_g has_derivative_subset that by force
    have "f integrable_on g ` ?P \<and> integral (g ` ?P) f \<le> integral ?P ?D"
    proof (rule integral_on_image_ubound_nonneg_eu [OF _ der_gP])
      show "?D integrable_on ?P"
      proof (rule integrable_spike_set)
        show "?D integrable_on {x \<in> S. 0 < ?D x}"
          using Dgt
          by (auto intro: set_lebesgue_integral_eq_integral [OF set_integrable_subset] intS)
      qed (auto simp: zero_less_mult_iff empty_imp_negligible)
    qed auto
  then have "f integrable_on g ` ?P"
    by metis
  moreover have "g ` ?P = {y \<in> g ` S. f y > 0}"
    by auto
  ultimately have "f integrable_on {y \<in> g ` S. f y > 0}"
    by simp
  then have P: "f absolutely_integrable_on {y \<in> g ` S. f y > 0}"
    by (rule absolutely_integrable_absolutely_integrable_lbound) auto
  have "(\<lambda>x. if x \<in> g ` S \<and> f x < 0 \<or> x \<in> g ` S \<and> 0 < f x then f x else 0) = (\<lambda>x. if x \<in> g ` S then f x else 0)"
    by auto
  then show ?thesis
    using absolutely_integrable_Un [OF N P] absolutely_integrable_restrict_UNIV [symmetric, where f=f]
    by simp
qed

proposition absolutely_integrable_on_image_eu:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and intS: "(\<lambda>x. \<bar>eucl.det (g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S"
  shows "f absolutely_integrable_on (g ` S)"
proof (rule absolutely_integrable_componentwise)
  fix b :: 'b assume "b \<in> Basis"
  have "(\<lambda>x. \<bar>eucl.det (g' x)\<bar> * (f (g x) \<bullet> b)) absolutely_integrable_on S"
    using absolutely_integrable_component [OF intS, of b]
    by (simp add: inner_scaleR_left)
  then show "(\<lambda>x. f x \<bullet> b) absolutely_integrable_on g ` S"
    by (auto intro: absolutely_integrable_on_image_real_eu der_g)
qed

proposition integral_on_image_ubound_eu:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and g :: "'a \<Rightarrow> 'a"
  assumes "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f(g x)"
    and "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and "(\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x)) integrable_on S"
  shows "integral (g ` S) f \<le> integral S (\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x))"
  using integral_on_image_ubound_nonneg_eu [OF assms] by simp

subsection\<open>Change-of-variables theorem\<close>

text\<open>The classic change-of-variables theorem. We have two versions with quite general hypotheses,
the first that the transforming function has a continuous inverse, the second that the base set is
Lebesgue measurable.\<close>
lemma cov_invertible_nonneg_le_eu:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and g :: "'a \<Rightarrow> 'a"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and der_h: "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
    and f0: "\<And>y. y \<in> T \<Longrightarrow> 0 \<le> f y"
    and hg: "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
    and gh: "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
    and id: "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "f integrable_on T \<and> (integral T f) \<le> b \<longleftrightarrow>
             (\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x)) integrable_on S \<and>
             integral S (\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x)) \<le> b"
        (is "?lhs = ?rhs")
proof -
  have Teq: "T = g`S" and Seq: "S = h`T"
    using hg gh image_iff by fastforce+
  have gS: "g differentiable_on S"
    by (meson der_g differentiable_def differentiable_on_def)
  let ?D = "\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f (g x)"
  show ?thesis
  proof
    assume ?lhs
    then have fT: "f integrable_on T" and intf: "integral T f \<le> b"
      by blast+
    show ?rhs
    proof
      let ?fgh = "\<lambda>x. \<bar>eucl.det (h' x)\<bar> * (\<bar>eucl.det (g' (h x))\<bar> * f (g (h x)))"
      have ddf: "?fgh x = f x"
        if "x \<in> T" for x
      proof -
        have lin_h: "linear (h' x)" and lin_g: "linear (g' (h x))"
          using der_h that gh der_g has_derivative_linear by blast+
        have "h' x \<circ> g'(h x) = id"
          using id that by blast
        then have "eucl.det (h' x \<circ> g' (h x)) = 1"
          by (simp add: eucl.det_ident)
        then have "eucl.det (h' x) * eucl.det (g' (h x)) = 1"
          by (simp add: eucl.det_compose [OF lin_h lin_g])
        then have "\<bar>eucl.det (h' x)\<bar> * \<bar>eucl.det (g' (h x))\<bar> = 1"
          by (metis abs_1 abs_mult)
        then show ?thesis
          by (simp add: gh that)
      qed
      have "?D integrable_on (h ` T)"
      proof (intro set_lebesgue_integral_eq_integral absolutely_integrable_on_image_real_eu)
        show "(\<lambda>x. ?fgh x) absolutely_integrable_on T"
          by (smt (verit, del_insts) abs_absolutely_integrableI_1 ddf f0 fT integrable_eq)
      qed (use der_h in auto)
      with Seq show "(\<lambda>x. ?D x) integrable_on S"
        by simp
      have "integral S (\<lambda>x. ?D x) \<le> integral T (\<lambda>x. ?fgh x)"
        unfolding Seq
      proof (rule integral_on_image_ubound_eu)
        show "(\<lambda>x. ?fgh x) integrable_on T"
        using ddf fT integrable_eq by force
      qed (use f0 gh der_h in auto)
      also have "\<dots> = integral T f"
        by (force simp: ddf intro: integral_cong)
      finally show "integral S (\<lambda>x. ?D x) \<le> b"
        using intf by linarith
    qed
  next
    assume R: ?rhs
    then have "f integrable_on g ` S"
      using der_g f0 hg integral_on_image_ubound_nonneg_eu by blast
    moreover have "integral (g ` S) f \<le> integral S (\<lambda>x. ?D x)"
      by (rule integral_on_image_ubound_eu [OF f0 der_g]) (use R Teq in auto)
    ultimately show ?lhs
      using R by (simp add: Teq)
  qed
qed

lemma cov_invertible_nonneg_eq_eu:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and g :: "'a \<Rightarrow> 'a"
  assumes "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
      and "\<And>y. y \<in> T \<Longrightarrow> 0 \<le> f y"
      and "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
      and "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
      and "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "((\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x)) has_integral b) S \<longleftrightarrow> (f has_integral b) T"
  using cov_invertible_nonneg_le_eu [OF assms]
  by (simp add: has_integral_iff) (meson eq_iff)

lemma cov_invertible_real_eu:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and g :: "'a \<Rightarrow> 'a"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and der_h: "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
      and hg: "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
      and gh: "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
      and id: "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "(\<lambda>x. \<bar>eucl.det(g' x)\<bar> * f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>eucl.det(g' x)\<bar> * f(g x)) = b \<longleftrightarrow>
         f absolutely_integrable_on T \<and> integral T f = b"
         (is "?lhs = ?rhs")
proof -
  have Teq: "T = g`S" and Seq: "S = h`T"
    using hg gh image_iff by fastforce+
  let ?DP = "\<lambda>x. \<bar>eucl.det(g' x)\<bar> * f(g x)" and ?DN = "\<lambda>x. \<bar>eucl.det(g' x)\<bar> * -f(g x)"
  have "+": "(?DP has_integral b) {x \<in> S. f (g x) > 0} \<longleftrightarrow> (f has_integral b) {y \<in> T. f y > 0}" for b
  proof (rule cov_invertible_nonneg_eq_eu)
    have *: "(\<lambda>x. f (g x)) -` Y \<inter> {x \<in> S. f (g x) > 0}
          = ((\<lambda>x. f (g x)) -` Y \<inter> S) \<inter> {x \<in> S. f (g x) > 0}" for Y
      by auto
    show "(g has_derivative g' x) (at x within {x \<in> S. f (g x) > 0})" if "x \<in> {x \<in> S. f (g x) > 0}" for x
      using that der_g has_derivative_subset by fastforce
    show "(h has_derivative h' y) (at y within {y \<in> T. f y > 0})" if "y \<in> {y \<in> T. f y > 0}" for y
      using that der_h has_derivative_subset by fastforce
  qed (use gh hg id in auto)
  have "-": "(?DN has_integral b) {x \<in> S. f (g x) < 0} \<longleftrightarrow> ((\<lambda>x. - f x) has_integral b) {y \<in> T. f y < 0}" for b
  proof (rule cov_invertible_nonneg_eq_eu)
    have *: "(\<lambda>x. - f (g x)) -` y \<inter> {x \<in> S. f (g x) < 0}
          = ((\<lambda>x. f (g x)) -` uminus ` y \<inter> S) \<inter> {x \<in> S. f (g x) < 0}" for y
      using image_iff by fastforce
    show "(g has_derivative g' x) (at x within {x \<in> S. f (g x) < 0})" if "x \<in> {x \<in> S. f (g x) < 0}" for x
      using that der_g has_derivative_subset by fastforce
    show "(h has_derivative h' y) (at y within {y \<in> T. f y < 0})" if "y \<in> {y \<in> T. f y < 0}" for y
      using that der_h has_derivative_subset by fastforce
  qed (use gh hg id in auto)
  show ?thesis
  proof
    assume LHS: ?lhs
    have eq: "{x. (if x \<in> S then ?DP x else 0) > 0} = {x \<in> S. ?DP x > 0}"
      "{x. (if x \<in> S then ?DP x else 0) < 0} = {x \<in> S. ?DP x < 0}"
      by auto
    have "?DP integrable_on S"
      using LHS absolutely_integrable_on_def by blast
    then have "(\<lambda>x. if x \<in> S then ?DP x else 0) integrable_on UNIV"
      by (simp add: integrable_restrict_UNIV)
    then have D_borel: "(\<lambda>x. if x \<in> S then ?DP x else 0) \<in> borel_measurable (lebesgue_on UNIV)"
      using integrable_imp_measurable lebesgue_on_UNIV_eq by blast
    then have SN: "{x \<in> S. ?DP x < 0} \<in> sets lebesgue"
      unfolding borel_measurable_vimage_halfspace_component_lt
      by (drule_tac x=0 in spec) (auto simp: eq)
    from D_borel have SP: "{x \<in> S. ?DP x > 0} \<in> sets lebesgue"
      unfolding borel_measurable_vimage_halfspace_component_gt
      by (drule_tac x=0 in spec) (auto simp: eq)
    have "?DP absolutely_integrable_on {x \<in> S. ?DP x > 0}"
      using LHS by (fast intro!: set_integrable_subset [OF _, of _ S] SP)
    then have aP: "?DP absolutely_integrable_on {x \<in> S. f (g x) > 0}"
      by (rule absolutely_integrable_spike_set) (auto simp: zero_less_mult_iff empty_imp_negligible)
    have "?DP absolutely_integrable_on {x \<in> S. ?DP x < 0}"
      using LHS by (fast intro!: set_integrable_subset [OF _, of _ S] SN)
    then have aN: "?DP absolutely_integrable_on {x \<in> S. f (g x) < 0}"
      by (rule absolutely_integrable_spike_set) (auto simp: mult_less_0_iff empty_imp_negligible)
    have fN: "f integrable_on {y \<in> T. f y < 0}"
             "integral {y \<in> T. f y < 0} f = integral {x \<in> S. f (g x) < 0} ?DP"
      using "-" [of "integral {x \<in> S. f(g x) < 0} ?DN"] aN
      by (auto simp: set_lebesgue_integral_eq_integral has_integral_iff integrable_neg_iff)
    have faN: "f absolutely_integrable_on {y \<in> T. f y < 0}"
    proof (rule absolutely_integrable_integrable_bound)
      show "(\<lambda>x. - f x) integrable_on {y \<in> T. f y < 0}"
        using fN by (auto simp: integrable_neg_iff)
    qed (use fN in auto)
    have fP: "f integrable_on {y \<in> T. f y > 0}"
             "integral {y \<in> T. f y > 0} f = integral {x \<in> S. f (g x) > 0} ?DP"
      using "+" [of "integral {x \<in> S. f(g x) > 0} ?DP"] aP
      by (auto simp: set_lebesgue_integral_eq_integral has_integral_iff integrable_neg_iff)
    have faP: "f absolutely_integrable_on {y \<in> T. f y > 0}"
      using fP(1) nonnegative_absolutely_integrable_1 by fastforce
    have fa: "f absolutely_integrable_on ({y \<in> T. f y < 0} \<union> {y \<in> T. f y > 0})"
      by (rule absolutely_integrable_Un [OF faN faP])
    show ?rhs
    proof
      have eq: "((if x \<in> T \<and> f x < 0 \<or> x \<in> T \<and> 0 < f x then 1 else 0) * f x)
              = (if x \<in> T then 1 else 0) * f x" for x
        by auto
      show "f absolutely_integrable_on T"
        using fa by (simp add: indicator_def of_bool_def set_integrable_def eq)
      have [simp]: "{y \<in> T. f y < 0} \<inter> {y \<in> T. 0 < f y} = {}" for T and f :: "'a \<Rightarrow> real"
        by auto
      have "integral T f = integral ({y \<in> T. f y < 0} \<union> {y \<in> T. f y > 0}) f"
        by (intro empty_imp_negligible integral_spike_set) (auto simp: eq)
      also have "\<dots> = integral {y \<in> T. f y < 0} f + integral {y \<in> T. f y > 0} f"
        using fN fP by simp
      also have "\<dots> = integral {x \<in> S. f (g x) < 0} ?DP + integral {x \<in> S. 0 < f (g x)} ?DP"
        by (simp add: fN fP)
      also have "\<dots> = integral ({x \<in> S. f (g x) < 0} \<union> {x \<in> S. 0 < f (g x)}) ?DP"
        using aP aN by (simp add: set_lebesgue_integral_eq_integral)
      also have "\<dots> = integral S ?DP"
        by (intro empty_imp_negligible integral_spike_set) auto
      also have "\<dots> = b"
        using LHS by simp
      finally show "integral T f = b" .
    qed
  next
    assume RHS: ?rhs
    have eq: "{x. (if x \<in> T then f x else 0) > 0} = {x \<in> T. f x > 0}"
             "{x. (if x \<in> T then f x else 0) < 0} = {x \<in> T. f x < 0}"
      by auto
    have "f integrable_on T"
      using RHS absolutely_integrable_on_def by blast
    then have "(\<lambda>x. if x \<in> T then f x else 0) integrable_on UNIV"
      by (simp add: integrable_restrict_UNIV)
    then have D_borel: "(\<lambda>x. if x \<in> T then f x else 0) \<in> borel_measurable (lebesgue_on UNIV)"
      using integrable_imp_measurable lebesgue_on_UNIV_eq by blast
    then have TN: "{x \<in> T. f x < 0} \<in> sets lebesgue"
      unfolding borel_measurable_vimage_halfspace_component_lt
      by (drule_tac x=0 in spec) (auto simp: eq)
    from D_borel have TP: "{x \<in> T. f x > 0} \<in> sets lebesgue"
      unfolding borel_measurable_vimage_halfspace_component_gt
      by (drule_tac x=0 in spec) (auto simp: eq)
    have aint: "f absolutely_integrable_on {y. y \<in> T \<and> 0 < (f y)}"
               "f absolutely_integrable_on {y. y \<in> T \<and> (f y) < 0}"
         and intT: "integral T f = b"
      using set_integrable_subset [of _ T] TP TN RHS by blast+
    show ?lhs
    proof
      have fN: "f integrable_on {v \<in> T. f v < 0}"
        using absolutely_integrable_on_def aint by blast
      then have DN: "(?DN has_integral integral {y \<in> T. f y < 0} (\<lambda>x. - f x)) {x \<in> S. f (g x) < 0}"
        using "-" [of "integral {y \<in> T. f y < 0} (\<lambda>x. - f x)"]
        by (simp add: has_integral_neg_iff integrable_integral)
      have aDN: "?DP absolutely_integrable_on {x \<in> S. f (g x) < 0}"
        apply (rule absolutely_integrable_integrable_bound [where g = ?DN])
        using DN hg by (fastforce simp: abs_mult integrable_neg_iff)+
      have fP: "f integrable_on {v \<in> T. f v > 0}"
        using absolutely_integrable_on_def aint by blast
      then have DP: "(?DP has_integral integral {y \<in> T. f y > 0} f) {x \<in> S. f (g x) > 0}"
        using "+" [of "integral {y \<in> T. f y > 0} f"]
        by (simp add: has_integral_neg_iff integrable_integral)
      have aDP: "?DP absolutely_integrable_on {x \<in> S. f (g x) > 0}"
        apply (rule absolutely_integrable_integrable_bound [where g = ?DP])
        using DP hg by (fastforce simp: integrable_neg_iff)+
      have eq: "(if x \<in> S then 1 else 0) * ?DP x = (if x \<in> S \<and> f (g x) < 0 \<or> x \<in> S \<and> f (g x) > 0 then 1 else 0) * ?DP x" for x
        by force
      have "?DP absolutely_integrable_on ({x \<in> S. f (g x) < 0} \<union> {x \<in> S. f (g x) > 0})"
        by (rule absolutely_integrable_Un [OF aDN aDP])
      then show I: "?DP absolutely_integrable_on S"
        by (simp add: indicator_def of_bool_def eq set_integrable_def)
      have [simp]: "{y \<in> S. f y < 0} \<inter> {y \<in> S. 0 < f y} = {}" for S and f :: "'a \<Rightarrow> real"
        by auto
      have "integral S ?DP = integral ({x \<in> S. f (g x) < 0} \<union> {x \<in> S. f (g x) > 0}) ?DP"
        by (intro empty_imp_negligible integral_spike_set) auto
      also have "\<dots> = integral {x \<in> S. f (g x) < 0} ?DP + integral {x \<in> S. 0 < f (g x)} ?DP"
        using aDN aDP by (simp add: set_lebesgue_integral_eq_integral)
      also have "\<dots> = - integral {y \<in> T. f y < 0} (\<lambda>x. - f x) + integral {y \<in> T. f y > 0} f"
        using DN DP by (auto simp: has_integral_iff)
      also have "\<dots> = integral ({x \<in> T. f x < 0} \<union> {x \<in> T. 0 < f x}) f"
        by (simp add: fN fP)
      also have "\<dots> = integral T f"
        by (intro empty_imp_negligible integral_spike_set) auto
      also have "\<dots> = b"
        using intT by simp
      finally show "integral S ?DP = b" .
    qed
  qed
qed


lemma cv_inv_version3:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and der_h: "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
    and hg: "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
    and gh: "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
    and id: "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "(\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
             integral S (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) = b
         \<longleftrightarrow> f absolutely_integrable_on T \<and> integral T f = b"
proof -
  let ?D = "\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)"
  have "((\<lambda>x. \<bar>eucl.det(g' x)\<bar> * (f(g x) \<bullet> i)) absolutely_integrable_on S \<and> integral S (\<lambda>x. \<bar>eucl.det(g' x)\<bar> * (f(g x) \<bullet> i)) = b \<bullet> i) \<longleftrightarrow>
        ((\<lambda>x. f x \<bullet> i) absolutely_integrable_on T \<and> integral T (\<lambda>x. f x \<bullet> i) = b \<bullet> i)" for i
    by (rule cov_invertible_real_eu [OF der_g der_h hg gh id])
  then have "?D absolutely_integrable_on S \<and> (?D has_integral b) S \<longleftrightarrow>
        f absolutely_integrable_on T \<and> (f has_integral b) T"
    unfolding absolutely_integrable_componentwise_iff [where f=f] has_integral_componentwise_iff [of f]
              absolutely_integrable_componentwise_iff [where f="?D"] has_integral_componentwise_iff [of ?D]
    by (auto simp: all_conj_distrib has_integral_iff set_lebesgue_integral_eq_integral dest: absolutely_integrable_on_def [THEN iffD1, THEN conjunct1])
  then show ?thesis
    using absolutely_integrable_on_def by blast
qed


lemma cv_inv_version4:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S) \<and> eucl.det(g' x) \<noteq> 0"
    and hg: "\<And>x. x \<in> S \<Longrightarrow> continuous_on (g ` S) h \<and> h(g x) = x"
  shows "(\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
             integral S (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) = b
         \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  have "\<forall>x. \<exists>h'. x \<in> S
           \<longrightarrow> (g has_derivative g' x) (at x within S) \<and> linear h' \<and> g' x \<circ> h' = id \<and> h' \<circ> g' x = id"
  proof
    fix x show "\<exists>h'. x \<in> S
           \<longrightarrow> (g has_derivative g' x) (at x within S) \<and> linear h' \<and> g' x \<circ> h' = id \<and> h' \<circ> g' x = id"
    proof (cases "x \<in> S")
      case True
      then have "linear (g' x)" "inj (g' x)" "(g has_derivative g' x) (at x within S)"
        using der_g has_derivative_linear eucl.det_eq_0_iff by blast+
      then have "linear (inv (g' x))" "g' x \<circ> inv (g' x) = id" "inv (g' x) \<circ> g' x = id"
        using eucl.inj_linear_imp_inv_linear inv_o_cancel surj_iff eucl.linear_inj_imp_surj
        by blast+
      then show ?thesis
        using \<open>(g has_derivative g' x) (at x within S)\<close> by blast
    qed auto
  qed
  then obtain h' where h':
    "\<And>x. x \<in> S
           \<Longrightarrow> (g has_derivative g' x) (at x within S) \<and>
               linear (h' x) \<and> g' x \<circ> (h' x) = id \<and> (h' x) \<circ> g' x = id"
    by metis
  show ?thesis
  proof (rule cv_inv_version3)
    show "\<And>y. y \<in> g ` S \<Longrightarrow> (h has_derivative h' (h y)) (at y within g ` S)"
      using h' hg
      by (force simp: continuous_on_eq_continuous_within intro!: has_derivative_inverse_within)
  qed (use h' hg in auto)
qed


theorem has_absolute_integral_change_of_variables_invertible:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and hg: "\<And>x. x \<in> S \<Longrightarrow> h(g x) = x"
      and conth: "continuous_on (g ` S) h"
  shows "(\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and> integral S (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) = b \<longleftrightarrow>
         f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
    (is "?lhs = ?rhs")
proof -
  let ?S = "{x \<in> S. eucl.det(g' x) \<noteq> 0}" and ?D = "\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)"
  have *: "?D absolutely_integrable_on ?S \<and> integral ?S ?D = b
           \<longleftrightarrow> f absolutely_integrable_on (g ` ?S) \<and> integral (g ` ?S) f = b"
  proof (rule cv_inv_version4)
    show "(g has_derivative g' x) (at x within ?S) \<and> eucl.det(g' x) \<noteq> 0"
      if "x \<in> ?S" for x
      using der_g that has_derivative_subset that by fastforce
    show "continuous_on (g ` ?S) h \<and> h (g x) = x"
      if "x \<in> ?S" for x
      using that continuous_on_subset [OF conth]  by (simp add: hg image_mono)
  qed
  have "negligible (g ` {x \<in> S. eucl.det(g' x) = 0})"
  proof (rule baby_Sard_eu [OF order_refl], simp_all)
    fix x
    assume x: "x \<in> S \<and> eucl.det (g' x) = 0"
    then show "(g has_derivative g' x) (at x within {x \<in> S. eucl.det (g' x) = 0})"
      by (metis (no_types, lifting) der_g has_derivative_subset mem_Collect_eq subsetI)
    have "linear (g' x)"
      using \<open>(g has_derivative g' x) _\<close> has_derivative_linear by blast
    then have "\<not> inj (g' x)"
      using x eucl.det_eq_0_iff by auto
    then have "\<not> surj (g' x)"
      using \<open>linear (g' x)\<close> eucl.linear_surjective_imp_injective by auto
    then have "g' x ` UNIV \<noteq> UNIV"
      by (simp add: surj_def)
    moreover have "subspace (g' x ` UNIV)"
      using \<open>linear (g' x)\<close> linear_subspace_image subspace_UNIV by blast
    ultimately show "dim (g' x ` UNIV) < DIM('a)"
      using eucl.subspace_dim_equal [of "g' x ` UNIV" UNIV] subspace_UNIV eucl.dim_UNIV
      by (metis eucl.dim_subset le_neq_implies_less subset_UNIV)
  qed
  then have neg: "negligible {x \<in> g ` S. x \<notin> g ` ?S \<and> f x \<noteq> 0}"
    by (auto intro: negligible_subset)
  have [simp]: "{x \<in> g ` ?S. x \<notin> g ` S \<and> f x \<noteq> 0} = {}"
    by auto
  have "?D absolutely_integrable_on ?S \<and> integral ?S ?D = b
    \<longleftrightarrow> ?D absolutely_integrable_on S \<and> integral S ?D = b"
    apply (intro conj_cong absolutely_integrable_spike_set_eq)
      apply(auto simp: integral_spike_set empty_imp_negligible neg)
    done
  moreover
  have "f absolutely_integrable_on (g ` ?S) \<and> integral (g ` ?S) f = b
    \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
    by (auto intro!: conj_cong absolutely_integrable_spike_set_eq integral_spike_set neg)
  ultimately
  show ?thesis
    using "*" by blast
qed



theorem has_absolute_integral_change_of_variables_compact:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes "compact S"
      and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and inj: "inj_on g S"
  shows "((\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
             integral S (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) = b
      \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b)"
proof -
  obtain h where hg: "\<And>x. x \<in> S \<Longrightarrow> h(g x) = x"
    using inj by (metis the_inv_into_f_f)
  have conth: "continuous_on (g ` S) h"
    by (metis \<open>compact S\<close> continuous_on_inv der_g has_derivative_continuous_on hg)
  show ?thesis
    by (rule has_absolute_integral_change_of_variables_invertible [OF der_g hg conth])
qed

lemma integral_countable_UN_eu:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    and s :: "nat \<Rightarrow> 'a set"
  assumes f: "f absolutely_integrable_on (\<Union> (range s))"
    and s: "\<And>m. s m \<in> sets lebesgue"
  shows ai: "f absolutely_integrable_on (\<Union> (s ` {..n}))"
    and "(\<lambda>n. integral (\<Union> (s ` {..n})) f) \<longlonglongrightarrow> integral (\<Union> (range s)) f" (is "?F \<longlonglongrightarrow> ?I")
proof -
  show fU: "f absolutely_integrable_on (\<Union>m\<le>n. s m)" for n
    using assms by (blast intro: set_integrable_subset [OF f])
  have fint: "f integrable_on (\<Union> (range s))"
    using absolutely_integrable_on_def f by blast
  let ?h = "\<lambda>x. if x \<in> \<Union>(s ` UNIV) then norm(f x) else 0"
  have "(\<lambda>n. integral UNIV (\<lambda>x. if x \<in> (\<Union>m\<le>n. s m) then f x else 0))
        \<longlonglongrightarrow> integral UNIV (\<lambda>x. if x \<in> \<Union>(s ` UNIV) then f x else 0)"
  proof (rule dominated_convergence)
    show "(\<lambda>x. if x \<in> (\<Union>m\<le>n. s m) then f x else 0) integrable_on UNIV" for n
      unfolding integrable_restrict_UNIV
      using fU absolutely_integrable_on_def by blast
    show "(\<lambda>x. if x \<in> \<Union>(s ` UNIV) then norm(f x) else 0) integrable_on UNIV"
      by (metis (no_types) absolutely_integrable_on_def f integrable_restrict_UNIV)
    show "\<And>x. (\<lambda>n. if x \<in> (\<Union>m\<le>n. s m) then f x else 0)
         \<longlonglongrightarrow> (if x \<in> \<Union>(s ` UNIV) then f x else 0)"
      by (force intro: tendsto_eventually eventually_sequentiallyI)
  qed auto
  then show "?F \<longlonglongrightarrow> ?I"
    by (simp only: integral_restrict_UNIV)
qed 

lemma has_absolute_integral_change_of_variables_compact_family:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes compact: "\<And>n::nat. compact (F n)"
      and der_g: "\<And>x. x \<in> (\<Union>n. F n) \<Longrightarrow> (g has_derivative g' x) (at x within (\<Union>n. F n))"
      and inj: "inj_on g (\<Union>n. F n)"
  shows "((\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on (\<Union>n. F n) \<and>
             integral (\<Union>n. F n) (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) = b
      \<longleftrightarrow> f absolutely_integrable_on (g ` (\<Union>n. F n)) \<and> integral (g ` (\<Union>n. F n)) f = b)"
proof -
  let ?D = "\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f (g x)"
  let ?U = "\<lambda>n. \<Union>m\<le>n. F m"
  let ?lift = "vec::real\<Rightarrow>real^1"
  have F_leb: "F m \<in> sets lebesgue" for m
    by (simp add: compact borel_compact)
  have iff: "(\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f (g x)) absolutely_integrable_on (?U n) \<and>
             integral (?U n) (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f (g x)) = b
         \<longleftrightarrow> f absolutely_integrable_on (g ` (?U n)) \<and> integral (g ` (?U n)) f = b" for n b and f :: "'a \<Rightarrow> 'c::euclidean_space"
  proof (rule has_absolute_integral_change_of_variables_compact)
    show "compact (?U n)"
      by (simp add: compact compact_UN)
    show "(g has_derivative g' x) (at x within (?U n))"
      if "x \<in> ?U n" for x
      using that by (blast intro!: has_derivative_subset [OF der_g])
    show "inj_on g (?U n)"
      using inj by (auto simp: inj_on_def)
  qed
  show ?thesis
    unfolding image_UN
  proof safe
    assume DS: "?D absolutely_integrable_on (\<Union>n. F n)"
      and b: "b = integral (\<Union>n. F n) ?D"
    have DU: "\<And>n. ?D absolutely_integrable_on (?U n)"
             "(\<lambda>n. integral (?U n) ?D) \<longlonglongrightarrow> integral (\<Union>n. F n) ?D"
      using integral_countable_UN_eu [where s=F and f="?D"] DS F_leb by auto
    with iff have fag: "f absolutely_integrable_on g ` (?U n)"
      and fg_int: "integral (\<Union>m\<le>n. g ` F m) f = integral (?U n) ?D" for n
      by (auto simp: image_UN)
    let ?h = "\<lambda>x. if x \<in> (\<Union>m. g ` F m) then norm(f x) else 0"
    have "(\<lambda>x. if x \<in> (\<Union>m. g ` F m) then f x else 0) absolutely_integrable_on UNIV"
    proof (rule dominated_convergence_absolutely_integrable)
      show "(\<lambda>x. if x \<in> (\<Union>m\<le>k. g ` F m) then f x else 0) absolutely_integrable_on UNIV" for k
        unfolding absolutely_integrable_restrict_UNIV
        using fag by (simp add: image_UN)
      let ?nf = "\<lambda>n x. if x \<in> (\<Union>m\<le>n. g ` F m) then norm(f x) else 0"
      show "?h integrable_on UNIV"
      proof (rule monotone_convergence_increasing [THEN conjunct1])
        show "?nf k integrable_on UNIV" for k
          using fag
          unfolding integrable_restrict_UNIV absolutely_integrable_on_def by (simp add: image_UN)
        { fix n
          have "(norm \<circ> ?D) absolutely_integrable_on ?U n"
            by (intro absolutely_integrable_norm DU)
          then have "integral (g ` ?U n) (norm \<circ> f) = integral (?U n) (norm \<circ> ?D)"
            using iff [of n "norm \<circ> f" "integral (?U n) (\<lambda>x. \<bar>eucl.det(g' x)\<bar> * norm (f (g x)))"]
            by (auto simp: o_def)
        }
        moreover have "bounded (range (\<lambda>k. integral (?U k) (norm \<circ> ?D)))"
          unfolding bounded_iff
        proof (rule exI, clarify)
          fix k
          show "norm (integral (?U k) (norm \<circ> ?D)) \<le> integral (\<Union>n. F n) (norm \<circ> ?D)"
            unfolding integral_restrict_UNIV [of _ "norm \<circ> ?D", symmetric]
          proof (rule integral_norm_bound_integral)
            show "(\<lambda>x. if x \<in> \<Union> (F ` {..k}) then (norm \<circ> ?D) x else 0) integrable_on UNIV"
              "(\<lambda>x. if x \<in> (\<Union>n. F n) then (norm \<circ> ?D) x else 0) integrable_on UNIV"
              using DU(1) DS
              unfolding absolutely_integrable_on_def o_def integrable_restrict_UNIV by auto
          qed auto
        qed
        ultimately show "bounded (range (\<lambda>k. integral UNIV (?nf k)))"
          by (simp add: integral_restrict_UNIV image_UN [symmetric] o_def)
      next
        show "(\<lambda>k. if x \<in> (\<Union>m\<le>k. g ` F m) then norm (f x) else 0)
              \<longlonglongrightarrow> (if x \<in> (\<Union>m. g ` F m) then norm (f x) else 0)" for x
          by (force intro: tendsto_eventually eventually_sequentiallyI)
      qed auto
    next
      show "(\<lambda>k. if x \<in> (\<Union>m\<le>k. g ` F m) then f x else 0)
            \<longlonglongrightarrow> (if x \<in> (\<Union>m. g ` F m) then f x else 0)" for x
      proof clarsimp
        fix m y
        assume "y \<in> F m"
        show "(\<lambda>k. if \<exists>x\<in>{..k}. g y \<in> g ` F x then f (g y) else 0) \<longlonglongrightarrow> f (g y)"
          using \<open>y \<in> F m\<close> by (force intro: tendsto_eventually eventually_sequentiallyI [of m])
      qed
    qed auto
    then show fai: "f absolutely_integrable_on (\<Union>m. g ` F m)"
      using absolutely_integrable_restrict_UNIV by blast
    show "integral ((\<Union>x. g ` F x)) f = integral (\<Union>n. F n) ?D"
    proof (rule LIMSEQ_unique)
      show "(\<lambda>n. integral (?U n) ?D) \<longlonglongrightarrow> integral (\<Union>x. g ` F x) f"
        unfolding fg_int [symmetric]
      proof (rule integral_countable_UN_eu [OF fai])
        show "g ` F m \<in> sets lebesgue" for m
        proof (rule differentiable_image_in_sets_lebesgue [OF F_leb])
          show "g differentiable_on F m"
            by (meson der_g differentiableI UnionI differentiable_on_def differentiable_on_subset rangeI subsetI)
        qed auto
      qed
    qed (use DU in metis)
  next
    assume fs: "f absolutely_integrable_on (\<Union>x. g ` F x)"
      and b: "b = integral ((\<Union>x. g ` F x)) f"
    have gF_leb: "g ` F m \<in> sets lebesgue" for m
    proof (rule differentiable_image_in_sets_lebesgue [OF F_leb])
      show "g differentiable_on F m"
        using der_g unfolding differentiable_def differentiable_on_def
        by (meson Sup_upper UNIV_I UnionI has_derivative_subset image_eqI)
    qed auto
    have fgU: "\<And>n. f absolutely_integrable_on (\<Union>m\<le>n. g ` F m)"
      "(\<lambda>n. integral (\<Union>m\<le>n. g ` F m) f) \<longlonglongrightarrow> integral (\<Union>m. g ` F m) f"
      using integral_countable_UN_eu [OF fs gF_leb] by auto
    with iff have DUn: "?D absolutely_integrable_on ?U n"
      and D_int: "integral (?U n) ?D = integral (\<Union>m\<le>n. g ` F m) f" for n
      by (auto simp: image_UN)
    let ?h = "\<lambda>x. if x \<in> (\<Union>n. F n) then norm(?D x) else 0"
    have "(\<lambda>x. if x \<in> (\<Union>n. F n) then ?D x else 0) absolutely_integrable_on UNIV"
    proof (rule dominated_convergence_absolutely_integrable)
      show "(\<lambda>x. if x \<in> ?U k then ?D x else 0) absolutely_integrable_on UNIV" for k
        unfolding absolutely_integrable_restrict_UNIV using DUn by simp
      let ?nD = "\<lambda>n x. if x \<in> ?U n then norm(?D x) else 0"
      show "?h integrable_on UNIV"
      proof (rule monotone_convergence_increasing [THEN conjunct1])
        show "?nD k integrable_on UNIV" for k
          using DUn
          unfolding integrable_restrict_UNIV absolutely_integrable_on_def by (simp add: image_UN)
        { fix n::nat
          have "(norm \<circ> f) absolutely_integrable_on (\<Union>m\<le>n. g ` F m)"
            using absolutely_integrable_norm fgU by blast
          then have "integral (?U n) (norm \<circ> ?D) = integral (g ` ?U n) (norm \<circ> f)"
            using iff [of n "norm \<circ> f" "integral (g ` ?U n) (norm \<circ> f)"]
            unfolding image_UN by (auto simp: o_def)
        }
        moreover have "bounded (range (\<lambda>k. integral (g ` ?U k) (norm \<circ> f)))"
          unfolding bounded_iff
        proof (rule exI, clarify)
          fix k
          show "norm (integral (g ` ?U k) (norm \<circ> f)) \<le> integral (g ` (\<Union>n. F n)) (norm \<circ> f)"
            unfolding integral_restrict_UNIV [of _ "norm \<circ> f", symmetric]
          proof (rule integral_norm_bound_integral)
            show "(\<lambda>x. if x \<in> g ` ?U k then (norm \<circ> f) x else 0) integrable_on UNIV"
                 "(\<lambda>x. if x \<in> g ` (\<Union>n. F n) then (norm \<circ> f) x else 0) integrable_on UNIV"
              using fgU fs
              unfolding absolutely_integrable_on_def o_def integrable_restrict_UNIV
              by (auto simp: image_UN)
          qed auto
        qed
        ultimately show "bounded (range (\<lambda>k. integral UNIV (?nD k)))"
          unfolding integral_restrict_UNIV image_UN [symmetric] o_def by simp
      next
        show "(\<lambda>k. if x \<in> ?U k then norm (?D x) else 0) \<longlonglongrightarrow> (if x \<in> (\<Union>n. F n) then norm (?D x) else 0)" for x
          by (force intro: tendsto_eventually eventually_sequentiallyI)
      qed auto
    next
      show "(\<lambda>k. if x \<in> ?U k then ?D x else 0) \<longlonglongrightarrow> (if x \<in> (\<Union>n. F n) then ?D x else 0)" for x
      proof clarsimp
        fix n
        assume "x \<in> F n"
        show "(\<lambda>m. if \<exists>j\<in>{..m}. x \<in> F j then ?D x else 0) \<longlonglongrightarrow> ?D x"
          using \<open>x \<in> F n\<close> by (auto intro!: tendsto_eventually eventually_sequentiallyI [of n])
      qed
    qed auto
    then show Dai: "?D absolutely_integrable_on (\<Union>n. F n)"
      unfolding absolutely_integrable_restrict_UNIV by simp
    show "integral (\<Union>n. F n) ?D = integral ((\<Union>x. g ` F x)) f"
    proof (rule LIMSEQ_unique)
      show "(\<lambda>n. integral (\<Union>m\<le>n. g ` F m) f) \<longlonglongrightarrow> integral (\<Union>n. F n) ?D"
        unfolding D_int [symmetric] by (rule integral_countable_UN_eu [OF Dai F_leb])
    qed (use fgU in metis)
  qed
qed


theorem has_absolute_integral_change_of_variables:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  obtain C N where "fsigma C" and N: "N \<in> null_sets lebesgue" and CNS: "C \<union> N = S" and "disjnt C N"
    using lebesgue_set_almost_fsigma [OF S] .
  then obtain F :: "nat \<Rightarrow> ('a) set"
    where F: "range F \<subseteq> Collect compact" and Ceq: "C = Union(range F)"
    using fsigma_Union_compact by metis
  have "negligible N"
    using N by (simp add: negligible_iff_null_sets)
  let ?D = "\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f (g x)"
  have "?D absolutely_integrable_on C \<and> integral C ?D = b
    \<longleftrightarrow> f absolutely_integrable_on (g ` C) \<and> integral (g ` C) f = b"
    unfolding Ceq
  proof (rule has_absolute_integral_change_of_variables_compact_family)
    fix n x
    assume "x \<in> \<Union>(F ` UNIV)"
    then show "(g has_derivative g' x) (at x within \<Union>(F ` UNIV))"
      using Ceq \<open>C \<union> N = S\<close> der_g has_derivative_subset by blast
  next
    have "\<Union>(F ` UNIV) \<subseteq> S"
      using Ceq \<open>C \<union> N = S\<close> by blast
    then show "inj_on g (\<Union>(F ` UNIV))"
      using inj by (meson inj_on_subset)
  qed (use F in auto)
  moreover
  have "?D absolutely_integrable_on C \<and> integral C ?D = b
    \<longleftrightarrow> ?D absolutely_integrable_on S \<and> integral S ?D = b"
  proof (rule conj_cong)
    have neg: "negligible {x \<in> C - S. ?D x \<noteq> 0}" "negligible {x \<in> S - C. ?D x \<noteq> 0}"
      using CNS by (blast intro: negligible_subset [OF \<open>negligible N\<close>])+
    then show "(?D absolutely_integrable_on C) = (?D absolutely_integrable_on S)"
      by (rule absolutely_integrable_spike_set_eq)
    show "(integral C ?D = b) \<longleftrightarrow> (integral S ?D = b)"
      using integral_spike_set [OF neg] by simp
  qed
  moreover
  have "f absolutely_integrable_on (g ` C) \<and> integral (g ` C) f = b
    \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
  proof (rule conj_cong)
    have "g differentiable_on N"
      by (metis CNS der_g differentiable_def differentiable_on_def differentiable_on_subset sup.cobounded2)
    with \<open>negligible N\<close>
    have neg_gN: "negligible (g ` N)"
      by (blast intro: negligible_differentiable_image_negligible)
    have neg: "negligible {x \<in> g ` C - g ` S. f x \<noteq> 0}"
              "negligible {x \<in> g ` S - g ` C. f x \<noteq> 0}"
      using CNS by (blast intro: negligible_subset [OF neg_gN])+
    then show "(f absolutely_integrable_on g ` C) = (f absolutely_integrable_on g ` S)"
      by (rule absolutely_integrable_spike_set_eq)
    show "(integral (g ` C) f = b) \<longleftrightarrow> (integral (g ` S) f = b)"
      using integral_spike_set [OF neg] by simp
  qed
  ultimately show ?thesis
    by simp
qed


corollary absolutely_integrable_change_of_variables:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes "S \<in> sets lebesgue"
    and "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and "inj_on g S"
  shows "f absolutely_integrable_on (g ` S)
     \<longleftrightarrow> (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S"
  using assms has_absolute_integral_change_of_variables by blast

corollary integral_change_of_variables:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
    and disj: "(f absolutely_integrable_on (g ` S) \<or>
        (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S)"
  shows "integral (g ` S) f = integral S (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x))"
  using has_absolute_integral_change_of_variables [OF S der_g inj] disj
  by blast

lemma has_absolute_integral_change_of_variables_1:
  fixes f :: "real \<Rightarrow> 'b::euclidean_space" and g :: "real \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_vector_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  have "(\<lambda>x. \<bar>eucl.det((*) (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
         integral S (\<lambda>x. \<bar>eucl.det((*) (g' x))\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
    by (rule has_absolute_integral_change_of_variables [OF S _ inj])
       (use der_g in \<open>auto simp: has_vector_derivative_def mult.commute\<close>)
  then show ?thesis
    by (simp add: det_real)
qed

corollary absolutely_integrable_change_of_variables_1:
  fixes f :: "real \<Rightarrow> 'b::euclidean_space" and g :: "real \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_vector_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(f absolutely_integrable_on g ` S \<longleftrightarrow>
             (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S)"
  using has_absolute_integral_change_of_variables_1 [OF assms] by auto

text \<open>when @{term "n=1"}\<close>
lemma has_absolute_integral_change_of_variables_1':
  fixes f :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(\<lambda>x. \<bar>g' x\<bar> * f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>g' x\<bar> * f (g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  have "(\<lambda>x. \<bar>g' x\<bar> *\<^sub>R vec (f(g x)) :: real ^ 1) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R vec (f(g x))) = (vec b :: real ^ 1)
         \<longleftrightarrow> (\<lambda>x. vec (f x) :: real ^ 1) absolutely_integrable_on (g ` S) \<and>
           integral (g ` S) (\<lambda>x. vec (f x)) = (vec b :: real ^ 1)"
    using assms unfolding has_real_derivative_iff_has_vector_derivative
    by (intro has_absolute_integral_change_of_variables_1 assms) auto
  thus ?thesis
    by (simp add: absolutely_integrable_on_1_iff integral_on_1_eq)
qed

subsection\<open>Change of variables for integrals: special case of linear function\<close>

lemma has_absolute_integral_change_of_variables_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes "linear g"
  shows "(\<lambda>x. \<bar>eucl.det g\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>eucl.det g\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof (cases "eucl.det g = 0")
  case True
  then have "negligible(g ` S)"
    using assms eucl.det_eq_0_iff negligible_linear_singular_image by blast
  with True show ?thesis
    by (auto simp: absolutely_integrable_on_def integrable_negligible integral_negligible)
next
  case False
  then have "inj g"
    using assms eucl.det_eq_0_iff by blast
  then have h: "\<And>x. x \<in> S \<Longrightarrow> inv g (g x) = x" "linear (inv g)"
    using inv_f_f eucl.inj_linear_imp_inv_linear assms by auto
  show ?thesis
  proof (rule has_absolute_integral_change_of_variables_invertible)
    show "(g has_derivative g) (at x within S)" for x
      by (simp add: assms linear_imp_has_derivative)
    show "continuous_on (g ` S) (inv g)"
      using continuous_on_eq_continuous_within has_derivative_continuous linear_imp_has_derivative h by blast
  qed (use h in auto)
qed

lemma absolutely_integrable_change_of_variables_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes "linear g"
  shows "(\<lambda>x. \<bar>eucl.det g\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S
     \<longleftrightarrow> f absolutely_integrable_on (g ` S)"
  using assms has_absolute_integral_change_of_variables_linear by blast

lemma absolutely_integrable_on_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes "linear g"
  shows "f absolutely_integrable_on (g ` S)
     \<longleftrightarrow> (f \<circ> g) absolutely_integrable_on S \<or> eucl.det g = 0"
  unfolding assms absolutely_integrable_change_of_variables_linear [OF assms, symmetric] absolutely_integrable_on_scaleR_iff
  by (auto simp: set_integrable_def)

lemma integral_change_of_variables_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes "linear g"
      and "f absolutely_integrable_on (g ` S) \<or> (f \<circ> g) absolutely_integrable_on S"
    shows "integral (g ` S) f = \<bar>eucl.det g\<bar> *\<^sub>R integral S (f \<circ> g)"
proof -
  have "((\<lambda>x. \<bar>eucl.det g\<bar> *\<^sub>R f (g x)) absolutely_integrable_on S) \<or> (f absolutely_integrable_on g ` S)"
    using absolutely_integrable_on_linear_image assms by blast
  moreover
  have ?thesis if "((\<lambda>x. \<bar>eucl.det g\<bar> *\<^sub>R f (g x)) absolutely_integrable_on S)" "(f absolutely_integrable_on g ` S)"
    using has_absolute_integral_change_of_variables_linear [OF \<open>linear g\<close>] that
    by (auto simp: o_def)
  ultimately show ?thesis
    using absolutely_integrable_change_of_variables_linear [OF \<open>linear g\<close>]
    by blast
qed

lemma absolutely_integrable_change_of_variables_1':
  fixes f :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> real"
  assumes "S \<in> sets lebesgue"
  assumes "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative h x) (at x within S)"
  assumes "inj_on g S"
  shows   "f absolutely_integrable_on g ` S \<longleftrightarrow> (\<lambda>x. \<bar>h x\<bar> * f (g x)) absolutely_integrable_on S"
  using has_absolute_integral_change_of_variables_1'[of S g h f] assms by auto

lemma absolutely_integrable_change_of_variables_real:
  fixes f :: "real \<Rightarrow> 'a :: euclidean_space" and g :: "real \<Rightarrow> real"
  assumes "S \<in> sets lebesgue"
  assumes "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative h x) (at x within S)"
  assumes "inj_on g S"
  shows   "f absolutely_integrable_on g ` S \<longleftrightarrow> (\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) absolutely_integrable_on S"
proof -
  have "(\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) absolutely_integrable_on S \<longleftrightarrow>
          (\<forall>a\<in>Basis. (\<lambda>x. \<bar>h x\<bar> * (f (g x) \<bullet> a)) absolutely_integrable_on S)"
    by (subst absolutely_integrable_componentwise_iff) simp_all
  also have "\<dots> = (\<forall>a\<in>Basis. (\<lambda>x. f x \<bullet> a) absolutely_integrable_on g ` S)"
    by (intro ball_cong absolutely_integrable_change_of_variables_1' [symmetric] assms refl)
  also have "\<dots> \<longleftrightarrow> f absolutely_integrable_on g ` S"
    by (subst absolutely_integrable_componentwise_iff) (simp_all add: Basis_complex_def)
  finally show ?thesis ..
qed

lemma has_absolute_integral_change_of_variables_real:
  fixes f :: "real \<Rightarrow> 'a :: euclidean_space" and g :: "real \<Rightarrow> real"
  assumes "S \<in> sets lebesgue"
  assumes "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative h x) (at x within S)"
  assumes "inj_on g S"
  shows   "(\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) absolutely_integrable_on S \<and> integral S (\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) = b
          \<longleftrightarrow> f absolutely_integrable_on g ` S \<and> integral (g ` S) f = b"
proof (intro conj_cong)
  show iff: "(\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) absolutely_integrable_on S \<longleftrightarrow> 
               f absolutely_integrable_on g ` S"
    by (rule sym, rule absolutely_integrable_change_of_variables_real) fact+

  assume "f absolutely_integrable_on g ` S"
  hence integrable: "f integrable_on g ` S" "(\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) integrable_on S"
    using set_lebesgue_integral_eq_integral(1) iff by metis+

  have "(\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) absolutely_integrable_on S \<and> 
        (integral S (\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) = b) \<longleftrightarrow>
        (\<forall>a\<in>Basis. (\<lambda>x. (\<bar>h x\<bar> *\<^sub>R f (g x)) \<bullet> a) absolutely_integrable_on S \<and> 
                   (integral S (\<lambda>x. (\<bar>h x\<bar> *\<^sub>R f (g x)) \<bullet> a) = b \<bullet> a))"    
    by (subst absolutely_integrable_componentwise_iff, subst integral_eq_iff_componentwise)
       (use integrable in auto)
  also have "\<dots> \<longleftrightarrow> (\<forall>a\<in>Basis. (\<lambda>x. \<bar>h x\<bar> * (f (g x) \<bullet> a)) absolutely_integrable_on S \<and> 
                       (integral S (\<lambda>x. \<bar>h x\<bar> * (f (g x) \<bullet> a)) = b \<bullet> a))"   
    by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>a\<in>Basis. (\<lambda>x. f x \<bullet> a) absolutely_integrable_on g ` S \<and> 
                       (integral (g ` S) (\<lambda>x. f x \<bullet> a) = b \<bullet> a))"
    by (intro ball_cong has_absolute_integral_change_of_variables_1' assms refl)
  also have "\<dots> \<longleftrightarrow> f absolutely_integrable_on g ` S \<and>  integral (g ` S) f = b"
    by (subst (2) absolutely_integrable_componentwise_iff, subst (2) integral_eq_iff_componentwise)
       (use integrable in auto)
  finally show "(integral S (\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) = b) = (integral (g ` S) f = b)"
    using \<open>f absolutely_integrable_on g ` S\<close> iff by blast
qed

subsection\<open>Change of variable for measure\<close>

lemma has_measure_differentiable_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "S \<in> sets lebesgue"
      and "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
      and "inj_on f S"
  shows "f ` S \<in> lmeasurable \<and> measure lebesgue (f ` S) = m
     \<longleftrightarrow> ((\<lambda>x. \<bar>eucl.det (f' x)\<bar>) has_integral m) S"
  using has_absolute_integral_change_of_variables [OF assms, of "\<lambda>x. (1::real^1)" "vec m"]
  unfolding absolutely_integrable_on_1_iff integral_on_1_eq integrable_on_1_iff absolutely_integrable_on_def
  by (auto simp: has_integral_iff lmeasurable_iff_integrable_on lmeasure_integral)

lemma measurable_differentiable_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes "S \<in> sets lebesgue"
      and "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
      and "inj_on f S"
  shows "f ` S \<in> lmeasurable \<longleftrightarrow> (\<lambda>x. \<bar>eucl.det (f' x)\<bar>) integrable_on S"
  using has_measure_differentiable_image [OF assms]
  by blast

lemma measurable_differentiable_image_alt:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "S \<in> sets lebesgue"
    and "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and "inj_on f S"
  shows "f ` S \<in> lmeasurable \<longleftrightarrow> (\<lambda>x. \<bar>eucl.det (f' x)\<bar>) absolutely_integrable_on S"
  using measurable_differentiable_image_eq [OF assms]
  by (simp only: absolutely_integrable_on_iff_nonneg)

lemma measure_differentiable_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes S: "S \<in> sets lebesgue"
    and der_f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and inj: "inj_on f S"
    and intS: "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) integrable_on S"
  shows "measure lebesgue (f ` S) = integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
  using measurable_differentiable_image_eq [OF S der_f inj]
        assms has_measure_differentiable_image by blast

lemma has_absolute_integral_reflect_real:
  fixes f :: "real \<Rightarrow> real"
  assumes "uminus ` A \<subseteq> B" "uminus ` B \<subseteq> A" "A \<in> sets lebesgue"
  shows "(\<lambda>x. f (-x)) absolutely_integrable_on A \<and> integral A (\<lambda>x. f (-x)) = b \<longleftrightarrow>
         f absolutely_integrable_on B \<and> integral B f = b"
proof -
  have bij: "bij_betw uminus A B"
    by (rule bij_betwI[of _ _ _ uminus]) (use assms in auto)
  have "((\<lambda>x. \<bar>-1\<bar> * f (-x)) absolutely_integrable_on A \<and>
          integral A (\<lambda>x. \<bar>-1\<bar> * f (-x)) = b) \<longleftrightarrow>
        (f absolutely_integrable_on uminus ` A \<and>
          integral (uminus ` A) f = b)" using assms
    by (intro has_absolute_integral_change_of_variables_1') (auto intro!: derivative_eq_intros)
  also have "uminus ` A = B"
    using bij by (simp add: bij_betw_def)
  finally show ?thesis
    by simp
qed

end
