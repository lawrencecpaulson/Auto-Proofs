(*  Title:      HOL/Analysis/Change_Of_Vars.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section\<open>Change of Variables Theorems\<close>

theory Change_Of_Vars_EU
  imports "HOL-Analysis.Vitali_Covering_Theorem" "HOL-Analysis.Determinants" 
          "Determinant_Linear_Function" "Euclidean_Space_Transfer"

begin

subsection \<open>Measurable Shear and Stretch\<close>

proposition
  fixes a :: "'a::euclidean_space"
  assumes "m \<in> Basis" "n \<in> Basis" "m \<noteq> n" and ab_ne: "cbox a b \<noteq> {}" and an: "0 \<le> a \<bullet> n"
  shows measurable_shear_interval_eu: "(\<lambda>x. x + (x \<bullet> n) *\<^sub>R m) ` (cbox a b) \<in> lmeasurable"
       (is  "?f ` _ \<in> _")
   and measure_shear_interval_eu: "measure lebesgue ((\<lambda>x. x + (x \<bullet> n) *\<^sub>R m) ` cbox a b)
               = measure lebesgue (cbox a b)" (is "?Q")
proof -
  note mB = \<open>m \<in> Basis\<close> and nB = \<open>n \<in> Basis\<close>
  have mn_ne: "m - n \<noteq> (0::'a)"
    using \<open>m \<noteq> n\<close> mB nB by (metis diff_eq_diff_eq diff_self inner_not_same_Basis inner_same_Basis one_neq_zero)
  have lin: "linear ?f"
    by (rule linearI) (auto simp: inner_left_distrib algebra_simps scaleR_add_left)
  show fab: "?f ` cbox a b \<in> lmeasurable"
    by (simp add: lin measurable_linear_image_interval)
  let ?c = "b + (b \<bullet> n) *\<^sub>R m"
  let ?mn = "m - n"
  \<comment> \<open>Key simplification rules for inner products with basis vectors\<close>
  have inner_f: "?f x \<bullet> i = (if i = m then x \<bullet> m + x \<bullet> n else x \<bullet> i)" if "i \<in> Basis" for x i
    using that mB nB \<open>m \<noteq> n\<close>
    by (simp add: inner_add_left inner_scaleR_left inner_same_Basis inner_not_same_Basis)
  have inner_c: "?c \<bullet> i = (if i = m then b \<bullet> m + b \<bullet> n else b \<bullet> i)" if "i \<in> Basis" for i
    using that mB nB \<open>m \<noteq> n\<close>
    by (simp add: inner_add_left inner_scaleR_left inner_same_Basis inner_not_same_Basis)
  have inner_mn: "?mn \<bullet> x = x \<bullet> m - x \<bullet> n" for x
    by (simp add: inner_diff_left inner_commute[of m] inner_commute[of n])
  \<comment> \<open>Galois connection for the shear map\<close>
  have shear_Galois: "?f x = y \<longleftrightarrow> x = y - (y \<bullet> n) *\<^sub>R m" if "True" for x y
  proof
    assume "?f x = y"
    then have "x = y - (x \<bullet> n) *\<^sub>R m" by (simp add: algebra_simps)
    moreover have "x \<bullet> n = y \<bullet> n"
      using \<open>?f x = y\<close> mB nB \<open>m \<noteq> n\<close>
      by (metis inner_add_left inner_not_same_Basis inner_scaleR_left mult_zero_right add_0_right)
    ultimately show "x = y - (y \<bullet> n) *\<^sub>R m" by simp
  next
    assume xy: "x = y - (y \<bullet> n) *\<^sub>R m"
    have "(y - (y \<bullet> n) *\<^sub>R m) \<bullet> n = y \<bullet> n"
      using mB nB \<open>m \<noteq> n\<close>
      by (simp add: inner_diff_left inner_scaleR_left inner_not_same_Basis)
    then show "?f x = y"
      by (simp add: xy algebra_simps)
  qed
  have eq1: "measure lebesgue (cbox a ?c)
            = measure lebesgue (?f ` cbox a b)
            + measure lebesgue (cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a \<bullet> m})
            + measure lebesgue (cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b \<bullet> m})"
  proof (rule measure_Un3_negligible)
    show "cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a \<bullet> m} \<in> lmeasurable" "cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b \<bullet> m} \<in> lmeasurable"
      by (auto simp: convex_Int convex_halfspace_le convex_halfspace_ge bounded_Int measurable_convex)
    have mn_f: "?mn \<bullet> (?f x) = x \<bullet> m" for x
      using mB nB \<open>m \<noteq> n\<close> using inner_f inner_mn by auto
    have "negligible {x. ?mn \<bullet> x = a \<bullet> m}"
      using mn_ne by (intro negligible_hyperplane) auto
    moreover have "?f ` cbox a b \<inter> (cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a \<bullet> m}) \<subseteq> {x. ?mn \<bullet> x = a \<bullet> m}"
    proof clarsimp
      fix x assume "x \<in> cbox a b" and "?mn \<bullet> (?f x) \<le> a \<bullet> m"
      then show "?mn \<bullet> (?f x) = a \<bullet> m"
        using mn_f[of x] mB by (auto simp: mem_box intro: antisym)
    qed
    ultimately show "negligible ((?f ` cbox a b) \<inter> (cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a \<bullet> m}))"
      by (rule negligible_subset)
    have "negligible {x. ?mn \<bullet> x = b \<bullet> m}"
      using mn_ne by (intro negligible_hyperplane) auto
    moreover have "(?f ` cbox a b) \<inter> (cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b \<bullet> m}) \<subseteq> {x. ?mn \<bullet> x = b \<bullet> m}"
      by (smt (verit) IntE imageE mB mem_Collect_eq mem_box(2) mn_f subsetI)
    ultimately show "negligible (?f ` cbox a b \<inter> (cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b \<bullet> m}))"
      by (rule negligible_subset)
    have "negligible {x. ?mn \<bullet> x = b \<bullet> m}"
      using mn_ne by (intro negligible_hyperplane) auto
    moreover have "(cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a \<bullet> m}) \<inter> (cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b \<bullet> m}) \<subseteq> {x. ?mn \<bullet> x = b \<bullet> m}"
    proof (clarsimp simp: inner_mn)
      fix x assume le: "x \<bullet> m - x \<bullet> n \<le> a \<bullet> m" and ge: "b \<bullet> m \<le> x \<bullet> m - x \<bullet> n"
      from le ge have "b \<bullet> m \<le> a \<bullet> m" by linarith
      moreover from ab_ne have "a \<bullet> m \<le> b \<bullet> m"
        using box_ne_empty mB by blast
      ultimately show "x \<bullet> m - x \<bullet> n = b \<bullet> m" using le ge by linarith
    qed
    ultimately show "negligible ((cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a \<bullet> m}) \<inter> (cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b \<bullet> m}))"
      by (rule negligible_subset)
    show "?f ` cbox a b \<union> cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a \<bullet> m} \<union> cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b \<bullet> m} = cbox a ?c"
      (is "?lhs = _")
    proof
      show "?lhs \<subseteq> cbox a ?c"
      proof (intro Un_least subsetI)
        fix y assume "y \<in> ?f ` cbox a b"
        then obtain x where "x \<in> cbox a b" and y: "y = ?f x" by auto
        then show "y \<in> cbox a ?c"
          using mB nB an \<open>m \<noteq> n\<close>
          by (auto simp: y mem_box inner_f inner_c intro: add_mono order_trans add_increasing2)
      qed auto
      show "cbox a ?c \<subseteq> ?lhs"
      proof
        fix y assume "y \<in> cbox a ?c"
        then have yac: "\<forall>i\<in>Basis. a \<bullet> i \<le> y \<bullet> i \<and> y \<bullet> i \<le> ?c \<bullet> i"
          by (simp add: mem_box)
        show "y \<in> ?lhs"
        proof (cases "a \<bullet> m \<le> y \<bullet> m - y \<bullet> n \<and> y \<bullet> m - y \<bullet> n \<le> b \<bullet> m")
          case True
          \<comment> \<open>y is in the image of the shear\<close>
          have "y - (y \<bullet> n) *\<^sub>R m \<in> cbox a b"
            unfolding mem_box by (metis True inner_f inner_mn mn_f shear_Galois yac)
          moreover have "?f (y - (y \<bullet> n) *\<^sub>R m) = y"
            using shear_Galois[of "y - (y \<bullet> n) *\<^sub>R m" y] by simp
          ultimately show ?thesis
            by (simp add: rev_image_eqI)
        next
          case False
          then have "?mn \<bullet> y \<le> a \<bullet> m \<or> b \<bullet> m \<le> ?mn \<bullet> y"
            by (auto simp: inner_mn)
          with \<open>y \<in> cbox a ?c\<close> show ?thesis by auto
        qed
      qed
    qed
  qed (fact fab)

  let ?d = "(a \<bullet> m - b \<bullet> m) *\<^sub>R m"
  let ?e = "b + (a \<bullet> m - b \<bullet> m + b \<bullet> n) *\<^sub>R m"
  have eq2: "measure lebesgue (cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a \<bullet> m}) + measure lebesgue (cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b \<bullet> m})
           = measure lebesgue (cbox a ?e)"
  proof (rule measure_translate_add[of "cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a \<bullet> m}" "cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b \<bullet> m}"
           "?d" "cbox a ?e"])
    show "(cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a \<bullet> m}) \<in> lmeasurable"
         "cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b \<bullet> m} \<in> lmeasurable"
      by (auto simp: convex_Int convex_halfspace_le convex_halfspace_ge bounded_Int measurable_convex)
    \<comment> \<open>Inner product of ?d with basis vectors\<close>
    have inner_d: "?d \<bullet> i = (if i = m then a \<bullet> m - b \<bullet> m else 0)" if "i \<in> Basis" for i
      using that mB nB \<open>m \<noteq> n\<close>
      by (simp add: inner_scaleR_left inner_same_Basis inner_not_same_Basis)
    \<comment> \<open>Inner product of ?e with basis vectors\<close>
    have inner_e: "?e \<bullet> i = (if i = m then a \<bullet> m + b \<bullet> n else b \<bullet> i)" if "i \<in> Basis" for i
      using that mB nB \<open>m \<noteq> n\<close>
      by (simp add: inner_add_left inner_scaleR_left inner_same_Basis inner_not_same_Basis)
    \<comment> \<open>?mn \<bullet> ?d = a \<bullet> m - b \<bullet> m\<close>
    have mn_d: "?mn \<bullet> ?d = a \<bullet> m - b \<bullet> m"
      using mB nB \<open>m \<noteq> n\<close>
      by (simp add: inner_diff_left inner_scaleR_right inner_same_Basis inner_not_same_Basis inner_commute[of n m])
    have mn_m: "?mn \<bullet> m = 1"
      using mB nB \<open>m \<noteq> n\<close>
      by (simp add: inner_diff_left inner_same_Basis inner_not_same_Basis inner_commute[of n m])
    \<comment> \<open>The translation shifts the halfspace\<close>
    have imeq: "(+) ?d ` {x. b \<bullet> m \<le> ?mn \<bullet> x} = {x. a \<bullet> m \<le> ?mn \<bullet> x}"
    proof (intro set_eqI iffI)
      fix x assume "x \<in> (+) ?d ` {x. b \<bullet> m \<le> ?mn \<bullet> x}"
      then obtain y where "b \<bullet> m \<le> ?mn \<bullet> y" "x = ?d + y" by auto
      then show "x \<in> {x. a \<bullet> m \<le> ?mn \<bullet> x}"
        using mn_d mn_m by (simp add: inner_add_right inner_scaleR_right)
    next
      fix x assume "x \<in> {x. a \<bullet> m \<le> ?mn \<bullet> x}"
      then show "x \<in> (+) ?d ` {x. b \<bullet> m \<le> ?mn \<bullet> x}"
        by (rule_tac x="x - ?d" in image_eqI) (simp_all add: inner_diff_right mn_d mn_m inner_scaleR_right)
    qed
    \<comment> \<open>The translated box-halfspace intersection equals cbox a ?e \<inter> halfspace\<close>
    have trans_eq: "(+) ?d ` (cbox a ?c \<inter> {x. b \<bullet> m \<le> ?mn \<bullet> x})
            = cbox a ?e \<inter> {x. a \<bullet> m \<le> ?mn \<bullet> x}"
    proof -
      have "(+) ?d ` (cbox a ?c \<inter> {x. b \<bullet> m \<le> ?mn \<bullet> x})
          = (+) ?d ` cbox a ?c \<inter> {x. a \<bullet> m \<le> ?mn \<bullet> x}"
        by (simp add: translation_Int imeq)
      also have shift: "(+) ?d ` cbox a ?c = cbox (a + ?d) (?c + ?d)"
        by (rule cbox_shift)
      finally have step: "(+) ?d ` (cbox a ?c \<inter> {x. b \<bullet> m \<le> ?mn \<bullet> x})
          = cbox (a + ?d) (?c + ?d) \<inter> {x. a \<bullet> m \<le> ?mn \<bullet> x}" .
      have cd_eq: "?c + ?d = ?e"
        by (simp add: scaleR_left_distrib)
      have ab_m: "a \<bullet> m \<le> b \<bullet> m"
        using ab_ne mB by (simp add: box_ne_empty)
      have "cbox (a + ?d) (?c + ?d) \<inter> {x. a \<bullet> m \<le> ?mn \<bullet> x}
          = cbox a ?e \<inter> {x. a \<bullet> m \<le> ?mn \<bullet> x}" (is "?L = ?R")
      proof (intro set_eqI iffI IntI)
        fix x assume x: "x \<in> ?L"
        then have xbox: "x \<in> cbox (a + ?d) ?e" and xh: "a \<bullet> m \<le> ?mn \<bullet> x"
          by (auto simp: cd_eq)
        show "x \<in> {x. a \<bullet> m \<le> ?mn \<bullet> x}" using xh by simp
        show "x \<in> cbox a ?e"
          unfolding mem_box
        proof (intro ballI conjI)
          fix i :: 'a assume iB: "i \<in> Basis"
          show "x \<bullet> i \<le> ?e \<bullet> i"
            using xbox iB by (auto simp: mem_box)
          show "a \<bullet> i \<le> x \<bullet> i"
          proof (cases "i = m")
            case True
            \<comment> \<open>From the halfspace: a\<bullet>m \<le> x\<bullet>m - x\<bullet>n. Since x\<bullet>n \<ge> a\<bullet>n \<ge> 0, we get x\<bullet>m \<ge> a\<bullet>m.\<close>
            have "x \<bullet> n \<ge> a \<bullet> n"
            proof -
              have "(a + ?d) \<bullet> n = a \<bullet> n"
                using nB mB \<open>m \<noteq> n\<close>
                by (simp add: inner_add_left inner_scaleR_left inner_not_same_Basis)
              then show ?thesis
                using xbox nB by (auto simp: mem_box)
            qed
            with xh an have "x \<bullet> m \<ge> a \<bullet> m"
              using inner_mn[of x] by linarith
            then show ?thesis using True by simp
          next
            case False
            then have "(a + ?d) \<bullet> i = a \<bullet> i"
              using iB mB nB \<open>m \<noteq> n\<close>
              by (simp add: inner_add_left inner_scaleR_left inner_not_same_Basis)
            then show ?thesis
              using xbox iB by (auto simp: mem_box)
          qed
        qed
      next
        fix x assume x: "x \<in> ?R"
        then have xbox: "x \<in> cbox a ?e" and xh: "a \<bullet> m \<le> ?mn \<bullet> x"
          by auto
        show "x \<in> {x. a \<bullet> m \<le> ?mn \<bullet> x}" using xh by simp
        show "x \<in> cbox (a + ?d) (?c + ?d)"
          unfolding cd_eq mem_box
        proof (intro ballI conjI)
          fix i :: 'a assume iB: "i \<in> Basis"
          show "x \<bullet> i \<le> ?e \<bullet> i"
            using xbox iB by (auto simp: mem_box)
          show "(a + ?d) \<bullet> i \<le> x \<bullet> i"
          proof (cases "i = m")
            case True
            have adm: "(a + ?d) \<bullet> m = 2 * (a \<bullet> m) - b \<bullet> m"
              using mB by (simp add: inner_add_left inner_scaleR_left inner_same_Basis)
            have "x \<bullet> m \<ge> a \<bullet> m"
              using xbox mB by (auto simp: mem_box)
            then have "(a + ?d) \<bullet> m \<le> x \<bullet> m"
              using adm ab_m by linarith
            then show ?thesis using True by simp
          next
            case False
            then have "(a + ?d) \<bullet> i = a \<bullet> i"
              using iB mB nB \<open>m \<noteq> n\<close>
              by (simp add: inner_add_left inner_scaleR_left inner_not_same_Basis)
            then show ?thesis
              using xbox iB by (auto simp: mem_box)
          qed
        qed
      qed
      then show ?thesis using step by simp
    qed
    \<comment> \<open>The union of the low piece and translated high piece equals cbox a ?e\<close>
    show "cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a \<bullet> m} \<union>
          (+) ?d ` (cbox a ?c \<inter> {x. b \<bullet> m \<le> ?mn \<bullet> x}) =
          cbox a ?e"  (is "?lhs = ?rhs")
    proof
      show "?lhs \<subseteq> ?rhs"
      proof (intro Un_least subsetI)
        fix x assume "x \<in> cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a \<bullet> m}"
        then have xbox: "x \<in> cbox a ?c" and xh: "?mn \<bullet> x \<le> a \<bullet> m" by auto
        show "x \<in> cbox a ?e"
          unfolding mem_box
        proof (intro ballI conjI)
          fix i :: 'a assume iB: "i \<in> Basis"
          show "a \<bullet> i \<le> x \<bullet> i"
            using xbox iB by (auto simp: mem_box)
          show "x \<bullet> i \<le> ?e \<bullet> i"
          proof (cases "i = m")
            case True
            have "x \<bullet> n \<le> ?c \<bullet> n"
              using xbox nB by (auto simp: mem_box)
            then have "x \<bullet> n \<le> b \<bullet> n"
              using inner_c[OF nB] \<open>m \<noteq> n\<close> by simp
            with xh have "x \<bullet> m \<le> a \<bullet> m + b \<bullet> n"
              using inner_mn[of x] by linarith
            then show ?thesis using True inner_e[OF mB] by simp
          next
            case False
            then show ?thesis
              using xbox iB inner_c[OF iB] inner_e[OF iB] by (auto simp: mem_box)
          qed
        qed
      next
        fix x assume "x \<in> (+) ?d ` (cbox a ?c \<inter> {x. b \<bullet> m \<le> ?mn \<bullet> x})"
        then show "x \<in> cbox a ?e"
          using trans_eq by auto
      qed
      show "?rhs \<subseteq> ?lhs"
      proof
        fix x assume "x \<in> cbox a ?e"
        then have xbox: "\<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> ?e \<bullet> i"
          by (simp add: mem_box)
        show "x \<in> ?lhs"
        proof (cases "?mn \<bullet> x \<le> a \<bullet> m")
          case True
          \<comment> \<open>x is in the low halfspace piece\<close>
          have "x \<in> cbox a ?c"
            unfolding mem_box
          proof (intro ballI conjI)
            fix i :: 'a assume iB: "i \<in> Basis"
            show "a \<bullet> i \<le> x \<bullet> i" using xbox iB by auto
            show "x \<bullet> i \<le> ?c \<bullet> i"
            proof (cases "i = m")
              case True
              have "x \<bullet> n \<ge> a \<bullet> n" using xbox nB by auto
              with an have "x \<bullet> n \<ge> 0" by linarith
              from True have "x \<bullet> m \<le> a \<bullet> m + b \<bullet> n"
                using xbox inner_e[OF mB] using mB by auto
              also have "\<dots> \<le> b \<bullet> m + b \<bullet> n"
                using ab_ne mB by (simp add: box_ne_empty)
              finally show ?thesis using True inner_c[OF mB] by simp
            next
              case False
              then show ?thesis
                using xbox iB inner_c[OF iB] inner_e[OF iB] by auto
            qed
          qed
          with True show ?thesis by auto
        next
          case False
          then have "a \<bullet> m \<le> ?mn \<bullet> x" by linarith
          then have "x \<in> cbox a ?e \<inter> {x. a \<bullet> m \<le> ?mn \<bullet> x}" using \<open>x \<in> cbox a ?e\<close> by auto
          then have "x \<in> (+) ?d ` (cbox a ?c \<inter> {x. b \<bullet> m \<le> ?mn \<bullet> x})"
            using trans_eq by auto
          then show ?thesis by auto
        qed
      qed
    qed
    \<comment> \<open>The intersection is negligible\<close>
    have "negligible {x. ?mn \<bullet> x = a \<bullet> m}"
      using mn_ne by (intro negligible_hyperplane) auto
    moreover have "(cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a \<bullet> m} \<inter>
                                 (+) ?d ` (cbox a ?c \<inter> {x. b \<bullet> m \<le> ?mn \<bullet> x})) \<subseteq> {x. ?mn \<bullet> x = a \<bullet> m}"
    proof (intro subsetI, clarsimp)
      fix xa assume xa_c: "xa \<in> cbox a ?c" and xa_h: "b \<bullet> m \<le> ?mn \<bullet> xa"
                    and dx_c: "?d + xa \<in> cbox a ?c" and dx_h: "?mn \<bullet> (?d + xa) \<le> a \<bullet> m"
      have "?mn \<bullet> (?d + xa) = (a \<bullet> m - b \<bullet> m) + ?mn \<bullet> xa"
        using mn_d by (simp add: inner_add_right)
      with dx_h xa_h show "?mn \<bullet> (?d + xa) = a \<bullet> m" by linarith
    qed
    ultimately show "negligible (cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a \<bullet> m} \<inter>
                                 (+) ?d ` (cbox a ?c \<inter> {x. b \<bullet> m \<le> ?mn \<bullet> x}))"
      by (rule negligible_subset)
  qed
  have eq3: "measure lebesgue (cbox a ?c) = measure lebesgue (cbox a ?e) + measure lebesgue (cbox a b)"
  proof -
    have ac_ne: "cbox a ?c \<noteq> {}"
    proof -
      have "a \<bullet> i \<le> ?c \<bullet> i" if "i \<in> Basis" for i
        using that ab_ne an mB nB \<open>m \<noteq> n\<close>
        by (cases "i = m") (auto simp: inner_c box_ne_empty intro: add_mono order_trans add_increasing2)
      then show ?thesis by (auto simp: box_ne_empty)
    qed
    have ae_ne: "cbox a ?e \<noteq> {}"
    proof -
      have ie: "?e \<bullet> i = (if i = m then a \<bullet> m + b \<bullet> n else b \<bullet> i)" if "i \<in> Basis" for i
        using that mB nB \<open>m \<noteq> n\<close>
        by (simp add: inner_add_left inner_scaleR_left inner_same_Basis inner_not_same_Basis)
      have "a \<bullet> i \<le> ?e \<bullet> i" if "i \<in> Basis" for i
        using that ab_ne an mB nB \<open>m \<noteq> n\<close>
        by (cases "i = m") (auto simp: ie box_ne_empty intro: add_increasing2)
      then show ?thesis by (auto simp: box_ne_empty)
    qed
    have ic: "?c \<bullet> i = (if i = m then b \<bullet> m + b \<bullet> n else b \<bullet> i)" if "i \<in> Basis" for i
      using inner_c[OF that] .
    have ie: "?e \<bullet> i = (if i = m then a \<bullet> m + b \<bullet> n else b \<bullet> i)" if "i \<in> Basis" for i
      using that mB nB \<open>m \<noteq> n\<close>
      by (simp add: inner_add_left inner_scaleR_left inner_same_Basis inner_not_same_Basis)
    \<comment> \<open>Express measures as products over Basis\<close>
    have cont_c: "measure lebesgue (cbox a ?c) = (\<Prod>i\<in>Basis. ?c \<bullet> i - a \<bullet> i)"
      using content_cbox'[OF ac_ne] by simp
    have cont_e: "measure lebesgue (cbox a ?e) = (\<Prod>i\<in>Basis. ?e \<bullet> i - a \<bullet> i)"
      using content_cbox'[OF ae_ne] by simp
    have cont_b: "measure lebesgue (cbox a b) = (\<Prod>i\<in>Basis. b \<bullet> i - a \<bullet> i)"
      using content_cbox'[OF ab_ne] by simp
    \<comment> \<open>The factors for i \<noteq> m are the same in all three products\<close>
    have same_c: "?c \<bullet> i - a \<bullet> i = b \<bullet> i - a \<bullet> i" if "i \<in> Basis" "i \<noteq> m" for i
      using ic[OF \<open>i \<in> Basis\<close>] that by simp
    have same_e: "?e \<bullet> i - a \<bullet> i = b \<bullet> i - a \<bullet> i" if "i \<in> Basis" "i \<noteq> m" for i
      using ie[OF \<open>i \<in> Basis\<close>] that by simp
    \<comment> \<open>Factor out the m-component using prod.remove\<close>
    let ?P = "\<Prod>i\<in>Basis - {m}. b \<bullet> i - a \<bullet> i"
    have prod_c: "(\<Prod>i\<in>Basis. ?c \<bullet> i - a \<bullet> i) = (?c \<bullet> m - a \<bullet> m) * ?P"
    proof -
      have "(\<Prod>i\<in>Basis. ?c \<bullet> i - a \<bullet> i) = (?c \<bullet> m - a \<bullet> m) * (\<Prod>i\<in>Basis - {m}. ?c \<bullet> i - a \<bullet> i)"
        using prod.remove[OF finite_Basis mB] by auto
      also have "(\<Prod>i\<in>Basis - {m}. ?c \<bullet> i - a \<bullet> i) = ?P"
        by (intro prod.cong) (auto simp: same_c)
      finally show ?thesis .
    qed
    have prod_e: "(\<Prod>i\<in>Basis. ?e \<bullet> i - a \<bullet> i) = (?e \<bullet> m - a \<bullet> m) * ?P"
    proof -
      have "(\<Prod>i\<in>Basis. ?e \<bullet> i - a \<bullet> i) = (?e \<bullet> m - a \<bullet> m) * (\<Prod>i\<in>Basis - {m}. ?e \<bullet> i - a \<bullet> i)"
        using prod.remove[OF finite_Basis mB] by auto
      also have "(\<Prod>i\<in>Basis - {m}. ?e \<bullet> i - a \<bullet> i) = ?P"
        by (intro prod.cong) (auto simp: same_e)
      finally show ?thesis .
    qed
    have prod_b: "(\<Prod>i\<in>Basis. b \<bullet> i - a \<bullet> i) = (b \<bullet> m - a \<bullet> m) * ?P"
      using prod.remove[OF finite_Basis mB] by auto
    \<comment> \<open>The m-component values\<close>
    have cm: "?c \<bullet> m - a \<bullet> m = b \<bullet> m + b \<bullet> n - a \<bullet> m"
      using ic[OF mB] by simp
    have em: "?e \<bullet> m - a \<bullet> m = b \<bullet> n"
      using ie[OF mB] by simp
    have bm: "b \<bullet> m - a \<bullet> m = b \<bullet> m - a \<bullet> m" by simp
    \<comment> \<open>The m-component identity\<close>
    have key: "?c \<bullet> m - a \<bullet> m = (?e \<bullet> m - a \<bullet> m) + (b \<bullet> m - a \<bullet> m)"
      using cm em by simp
    have "measure lebesgue (cbox a ?c) = (?c \<bullet> m - a \<bullet> m) * ?P"
      using cont_c prod_c by simp
    also have "\<dots> = ((?e \<bullet> m - a \<bullet> m) + (b \<bullet> m - a \<bullet> m)) * ?P"
      using key by simp
    also have "\<dots> = (?e \<bullet> m - a \<bullet> m) * ?P + (b \<bullet> m - a \<bullet> m) * ?P"
      by (rule distrib_right)
    also have "\<dots> = measure lebesgue (cbox a ?e) + measure lebesgue (cbox a b)"
      using cont_e prod_e cont_b prod_b by simp
    finally show ?thesis .
  qed
  show ?Q
    using eq1 eq2 eq3 by (simp add: algebra_simps)
qed

proposition
  fixes S :: "'a::euclidean_space set"
  assumes "S \<in> lmeasurable"
  shows measurable_stretch_eu: "((\<lambda>x. \<Sum>k\<in>Basis. (m k * (x \<bullet> k)) *\<^sub>R k) ` S) \<in> lmeasurable" (is "?f ` S \<in> _")
    and measure_stretch_eu: "measure lebesgue ((\<lambda>x. \<Sum>k\<in>Basis. (m k * (x \<bullet> k)) *\<^sub>R k) ` S) = \<bar>\<Prod>k\<in>Basis. m k\<bar> * measure lebesgue S"
      (is "?MEQ")
proof -
  have lin: "linear ?f"
  proof (intro linearI)
    fix x y :: 'a
    show "?f (x + y) = ?f x + ?f y"
      unfolding sum.distrib[symmetric]
      by (intro sum.cong refl)
         (simp only: inner_add_left distrib_left scaleR_add_left)
    fix c :: real
    show "?f (c *\<^sub>R x) = c *\<^sub>R ?f x"
      by (simp add: inner_scaleR_right mult.left_commute scaleR_sum_right)
  qed
  have meq: "measure lebesgue (?f ` cbox a b) = \<bar>\<Prod>k\<in>Basis. m k\<bar> * measure lebesgue (cbox a b)" for a b
  proof -
    have "measure lebesgue (?f ` cbox a b) = Henstock_Kurzweil_Integration.content (?f ` cbox a b)"
      using interval_image_stretch_interval [of m a b] by (force simp del: content_cbox_if)
    also have "\<dots> = \<bar>\<Prod>k\<in>Basis. m k\<bar> * Henstock_Kurzweil_Integration.content (cbox a b)"
      by (rule content_image_stretch_interval)
    also have "\<dots> = \<bar>\<Prod>k\<in>Basis. m k\<bar> * measure lebesgue (cbox a b)"
      by simp
    finally show ?thesis .
  qed
  show "?f ` S \<in> lmeasurable" ?MEQ
    using measure_linear_sufficient [OF lin assms meq] by metis+
qed

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


lemma borel_measurable_simple_function_limit_increasing:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  shows "(f \<in> borel_measurable lebesgue \<and> (\<forall>x. 0 \<le> f x)) \<longleftrightarrow>
         (\<exists>g. (\<forall>n x. 0 \<le> g n x \<and> g n x \<le> f x) \<and> (\<forall>n x. g n x \<le> (g(Suc n) x)) \<and>
              (\<forall>n. g n \<in> borel_measurable lebesgue) \<and> (\<forall>n. finite(range (g n))) \<and>
              (\<forall>x. (\<lambda>n. g n x) \<longlonglongrightarrow> f x))"
         (is "?lhs = ?rhs")
proof
  assume f: ?lhs
  have leb_f: "{x. a \<le> f x \<and> f x < b} \<in> sets lebesgue" for a b
  proof -
    have "{x. a \<le> f x \<and> f x < b} = {x. f x < b} - {x. f x < a}"
      by auto
    also have "\<dots> \<in> sets lebesgue"
      using borel_measurable_vimage_halfspace_component_lt [of f UNIV] f by auto
    finally show ?thesis .
  qed
  have "g n x \<le> f x"
        if inc_g: "\<And>n x. 0 \<le> g n x \<and> g n x \<le> g (Suc n) x"
           and meas_g: "\<And>n. g n \<in> borel_measurable lebesgue"
           and fin: "\<And>n. finite(range (g n))" and lim: "\<And>x. (\<lambda>n. g n x) \<longlonglongrightarrow> f x" for g n x
  proof -
    have "\<exists>r>0. \<forall>N. \<exists>n\<ge>N. dist (g n x) (f x) \<ge> r" if "g n x > f x"
    proof -
      have g: "g n x \<le> g (N + n) x" for N
        by (rule transitive_stepwise_le) (use inc_g in auto)
      have "\<exists>m\<ge>N. g n x - f x \<le> dist (g m x) (f x)" for N
      proof
        show "N \<le> N + n \<and> g n x - f x \<le> dist (g (N + n) x) (f x)"
          using g [of N] by (auto simp: dist_norm)
      qed
      with that show ?thesis
        using diff_gt_0_iff_gt by blast
    qed
    with lim show ?thesis
      unfolding lim_sequentially
      by (meson less_le_not_le not_le_imp_less)
  qed
  moreover
  let ?\<Omega> = "\<lambda>n k. indicator {y. k/2^n \<le> f y \<and> f y < (k+1)/2^n}"
  let ?g = "\<lambda>n x. (\<Sum>k::real | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). k/2^n * ?\<Omega> n k x)"
  have "\<exists>g. (\<forall>n x. 0 \<le> g n x \<and> g n x \<le> (g(Suc n) x)) \<and>
             (\<forall>n. g n \<in> borel_measurable lebesgue) \<and> (\<forall>n. finite(range (g n))) \<and>(\<forall>x. (\<lambda>n. g n x) \<longlonglongrightarrow> f x)"
  proof (intro exI allI conjI)
    show "0 \<le> ?g n x" for n x
    proof (clarify intro!: ordered_comm_monoid_add_class.sum_nonneg)
      fix k::real
      assume "k \<in> \<int>" and k: "\<bar>k\<bar> \<le> 2 ^ (2*n)"
      show "0 \<le> k/2^n * ?\<Omega> n k x"
        using f \<open>k \<in> \<int>\<close> apply (clarsimp simp: indicator_def field_split_simps Ints_def)
        by (smt (verit) int_less_real_le mult_nonneg_nonneg of_int_0 zero_le_power)
    qed
    show "?g n x \<le> ?g (Suc n) x" for n x
    proof -
      have "?g n x =
            (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n).
              k/2^n * (indicator {y. k/2^n \<le> f y \<and> f y < (k+1/2)/2^n} x +
              indicator {y. (k+1/2)/2^n \<le> f y \<and> f y < (k+1)/2^n} x))"
        by (rule sum.cong [OF refl]) (simp add: indicator_def field_split_simps)
      also have "\<dots> = (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). k/2^n * indicator {y. k/2^n \<le> f y \<and> f y < (k+1/2)/2^n} x) +
                       (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). k/2^n * indicator {y. (k+1/2)/2^n \<le> f y \<and> f y < (k+1)/2^n} x)"
        by (simp add:  comm_monoid_add_class.sum.distrib algebra_simps)
      also have "\<dots> = (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). (2 * k)/2 ^ Suc n * indicator {y. (2 * k)/2 ^ Suc n \<le> f y \<and> f y < (2 * k+1)/2 ^ Suc n} x) +
                       (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). (2 * k)/2 ^ Suc n * indicator {y. (2 * k+1)/2 ^ Suc n \<le> f y \<and> f y < ((2 * k+1) + 1)/2 ^ Suc n} x)"
        by (force simp: field_simps indicator_def intro: sum.cong)
      also have "\<dots> \<le> (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2 * Suc n). k/2 ^ Suc n * (indicator {y. k/2 ^ Suc n \<le> f y \<and> f y < (k+1)/2 ^ Suc n} x))"
                (is "?a + _ \<le> ?b")
      proof -
        have *: "\<lbrakk>sum f I \<le> sum h I; a + sum h I \<le> b\<rbrakk> \<Longrightarrow> a + sum f I \<le> b" for I a b f and h :: "real\<Rightarrow>real"
          by linarith
        let ?h = "\<lambda>k. (2*k+1)/2 ^ Suc n *
                      (indicator {y. (2 * k+1)/2 ^ Suc n \<le> f y \<and> f y < ((2*k+1) + 1)/2 ^ Suc n} x)"
        show ?thesis
        proof (rule *)
          show "(\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n).
                  2 * k/2 ^ Suc n * indicator {y. (2 * k+1)/2 ^ Suc n \<le> f y \<and> f y < (2 * k+1 + 1)/2 ^ Suc n} x)
                \<le> sum ?h {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}"
            by (rule sum_mono) (simp add: indicator_def field_split_simps)
        next
          have \<alpha>: "?a = (\<Sum>k \<in> (*)2 ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}.
                         k/2 ^ Suc n * indicator {y. k/2 ^ Suc n \<le> f y \<and> f y < (k+1)/2 ^ Suc n} x)"
            by (auto simp: inj_on_def field_simps comm_monoid_add_class.sum.reindex)
          have \<beta>: "sum ?h {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}
                   = (\<Sum>k \<in> (\<lambda>x. 2*x + 1) ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}.
                      k/2 ^ Suc n * indicator {y. k/2 ^ Suc n \<le> f y \<and> f y < (k+1)/2 ^ Suc n} x)"
            by (auto simp: inj_on_def field_simps comm_monoid_add_class.sum.reindex)
          have 0: "(*) 2 ` {k \<in> \<int>. P k} \<inter> (\<lambda>x. 2 * x + 1) ` {k \<in> \<int>. P k} = {}" for P :: "real \<Rightarrow> bool"
          proof -
            have "2 * i \<noteq> 2 * j + 1" for i j :: int by arith
            thus ?thesis
              unfolding Ints_def by auto (use of_int_eq_iff in fastforce)
          qed
          have "?a + sum ?h {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}
                = (\<Sum>k \<in> (*)2 ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)} \<union> (\<lambda>x. 2*x + 1) ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}.
                  k/2 ^ Suc n * indicator {y. k/2 ^ Suc n \<le> f y \<and> f y < (k+1)/2 ^ Suc n} x)"
            unfolding \<alpha> \<beta>
            using finite_abs_int_segment [of "2 ^ (2*n)"]
            by (subst sum_Un) (auto simp: 0)
          also have "\<dots> \<le> ?b"
          proof (rule sum_mono2)
            show "finite {k::real. k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2 * Suc n)}"
              by (rule finite_abs_int_segment)
            show "(*) 2 ` {k::real. k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2^(2*n)} \<union> (\<lambda>x. 2*x + 1) ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2^(2*n)} \<subseteq> {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2 * Suc n)}"
              apply (clarsimp simp: image_subset_iff)
              using one_le_power [of "2::real" "2*n"]  by linarith
            have *: "\<lbrakk>x \<in> (S \<union> T) - U; \<And>x. x \<in> S \<Longrightarrow> x \<in> U; \<And>x. x \<in> T \<Longrightarrow> x \<in> U\<rbrakk> \<Longrightarrow> P x" for S T U P
              by blast
            have "0 \<le> b" if "b \<in> \<int>" "f x * (2 * 2^n) < b + 1" for b
              by (smt (verit, ccfv_SIG) Ints_cases f int_le_real_less mult_nonneg_nonneg of_int_add one_le_power that)
            then show "0 \<le> b/2 ^ Suc n * indicator {y. b/2 ^ Suc n \<le> f y \<and> f y < (b + 1)/2 ^ Suc n} x"
                  if "b \<in> {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2 * Suc n)} -
                          ((*) 2 ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)} \<union> (\<lambda>x. 2*x + 1) ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)})" for b
              using that by (simp add: indicator_def divide_simps)
          qed
          finally show "?a + sum ?h {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)} \<le> ?b" .
        qed
      qed
      finally show ?thesis .
    qed
    show "?g n \<in> borel_measurable lebesgue" for n
      apply (intro borel_measurable_indicator borel_measurable_times borel_measurable_sum)
      using leb_f sets_restrict_UNIV by auto
    show "finite (range (?g n))" for n
    proof -
      have "(\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). k/2^n * ?\<Omega> n k x)
              \<in> (\<lambda>k. k/2^n) ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}" for x
      proof (cases "\<exists>k. k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n) \<and> k/2^n \<le> f x \<and> f x < (k+1)/2^n")
        case True
        then show ?thesis
          by (blast intro: indicator_sum_eq)
      next
        case False
        then have "(\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). k/2^n * ?\<Omega> n k x) = 0"
          by auto
        then show ?thesis by force
      qed
      then have "range (?g n) \<subseteq> ((\<lambda>k. (k/2^n)) ` {k. k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n)})"
        by auto
      moreover have "finite ((\<lambda>k::real. (k/2^n)) ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)})"
        by (intro finite_imageI finite_abs_int_segment)
      ultimately show ?thesis
        by (rule finite_subset)
    qed
    show "(\<lambda>n. ?g n x) \<longlonglongrightarrow> f x" for x
    proof (clarsimp simp add: lim_sequentially)
      fix e::real
      assume "e > 0"
      obtain N1 where N1: "2 ^ N1 > abs(f x)"
        using real_arch_pow by fastforce
      obtain N2 where N2: "(1/2) ^ N2 < e"
        using real_arch_pow_inv \<open>e > 0\<close> by fastforce
      have "dist (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). k/2^n * ?\<Omega> n k x) (f x) < e" if "N1 + N2 \<le> n" for n
      proof -
        let ?m = "real_of_int \<lfloor>2^n * f x\<rfloor>"
        have "\<bar>?m\<bar> \<le> 2^n * 2^N1"
          using N1 apply (simp add: f)
          by (meson floor_mono le_floor_iff less_le_not_le mult_le_cancel_left_pos zero_less_numeral zero_less_power)
        also have "\<dots> \<le> 2 ^ (2*n)"
          by (metis that add_leD1 add_le_cancel_left mult.commute mult_2_right one_less_numeral_iff
                    power_add power_increasing_iff semiring_norm(76))
        finally have m_le: "\<bar>?m\<bar> \<le> 2 ^ (2*n)" .
        have "?m/2^n \<le> f x" "f x < (?m + 1)/2^n"
          by (auto simp: mult.commute pos_divide_le_eq mult_imp_less_div_pos)
        then have eq: "dist (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). k/2^n * ?\<Omega> n k x) (f x)
                     = dist (?m/2^n) (f x)"
          by (subst indicator_sum_eq [of ?m]) (auto simp: m_le)
        have "\<bar>2^n\<bar> * \<bar>?m/2^n - f x\<bar> = \<bar>2^n * (?m/2^n - f x)\<bar>"
          by (simp add: abs_mult)
        also have "\<dots> < 2 ^ N2 * e"
          using N2 by (simp add: divide_simps mult.commute) linarith
        also have "\<dots> \<le> \<bar>2^n\<bar> * e"
          using that \<open>e > 0\<close> by auto
        finally show ?thesis
          using eq by (simp add: dist_real_def)
      qed
      then show "\<exists>no. \<forall>n\<ge>no. dist (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). k * ?\<Omega> n k x/2^n) (f x) < e"
        by force
    qed
  qed
  ultimately show ?rhs
    by metis
next
  assume RHS: ?rhs
  with borel_measurable_simple_function_limit [of f UNIV, unfolded lebesgue_on_UNIV_eq]
  show ?lhs
    by (blast intro: order_trans)
qed

subsection\<open>Borel measurable Jacobian determinant\<close>

lemma lemma_partial_derivatives0:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" and lim0: "((\<lambda>x. f x /\<^sub>R norm x) \<longlongrightarrow> 0) (at 0 within S)"
    and lb: "\<And>v. v \<noteq> 0 \<Longrightarrow> (\<exists>k>0. \<forall>e>0. \<exists>x. x \<in> S - {0} \<and> norm x < e \<and> k * norm x \<le> \<bar>v \<bullet> x\<bar>)"
  shows "f x = 0"
proof -
  interpret linear f by fact
  have "dim {x. f x = 0} \<le> DIM('a)"
    by (rule dim_subset_UNIV)
  moreover have False if less: "dim {x. f x = 0} < DIM('a)"
  proof -
    obtain d where "d \<noteq> 0" and d: "\<And>y. f y = 0 \<Longrightarrow> d \<bullet> y = 0"
      using orthogonal_to_subspace_exists [OF less] orthogonal_def
      by (metis (mono_tags, lifting) mem_Collect_eq span_base)
    then obtain k where "k > 0"
      and k: "\<And>e. e > 0 \<Longrightarrow> \<exists>y. y \<in> S - {0} \<and> norm y < e \<and> k * norm y \<le> \<bar>d \<bullet> y\<bar>"
      using lb by blast
    have "\<exists>h. \<forall>n. ((h n \<in> S \<and> h n \<noteq> 0 \<and> k * norm (h n) \<le> \<bar>d \<bullet> h n\<bar>) \<and> norm (h n) < 1 / real (Suc n)) \<and>
               norm (h (Suc n)) < norm (h n)"
    proof (rule dependent_nat_choice)
      show "\<exists>y. (y \<in> S \<and> y \<noteq> 0 \<and> k * norm y \<le> \<bar>d \<bullet> y\<bar>) \<and> norm y < 1 / real (Suc 0)"
        by simp (metis DiffE insertCI k not_less not_one_le_zero)
    qed (use k [of "min (norm x) (1/(Suc n + 1))" for x n] in auto)
    then obtain \<alpha> where \<alpha>: "\<And>n. \<alpha> n \<in> S - {0}" and kd: "\<And>n. k * norm(\<alpha> n) \<le> \<bar>d \<bullet> \<alpha> n\<bar>"
         and norm_lt: "\<And>n. norm(\<alpha> n) < 1/(Suc n)"
      by force
    let ?\<beta> = "\<lambda>n. \<alpha> n /\<^sub>R norm (\<alpha> n)"
    have com: "\<And>g. (\<forall>n. g n \<in> sphere (0::'a) 1)
              \<Longrightarrow> \<exists>l \<in> sphere 0 1. \<exists>\<rho>::nat\<Rightarrow>nat. strict_mono \<rho> \<and> (g \<circ> \<rho>) \<longlonglongrightarrow> l"
      using compact_sphere compact_def by metis
    moreover have "\<forall>n. ?\<beta> n \<in> sphere 0 1"
      using \<alpha> by auto
    ultimately obtain l::'a and \<rho>::"nat\<Rightarrow>nat"
       where l: "l \<in> sphere 0 1" and "strict_mono \<rho>" and to_l: "(?\<beta> \<circ> \<rho>) \<longlonglongrightarrow> l"
      by meson
    moreover have "continuous (at l) (\<lambda>x. (\<bar>d \<bullet> x\<bar> - k))"
      by (intro continuous_intros)
    ultimately have lim_dl: "((\<lambda>x. (\<bar>d \<bullet> x\<bar> - k)) \<circ> (?\<beta> \<circ> \<rho>)) \<longlonglongrightarrow> (\<bar>d \<bullet> l\<bar> - k)"
      by (meson continuous_imp_tendsto)
    have "\<forall>\<^sub>F i in sequentially. 0 \<le> ((\<lambda>x. \<bar>d \<bullet> x\<bar> - k) \<circ> ((\<lambda>n. \<alpha> n /\<^sub>R norm (\<alpha> n)) \<circ> \<rho>)) i"
      using \<alpha> kd by (auto simp: field_split_simps)
    then have "k \<le> \<bar>d \<bullet> l\<bar>"
      using tendsto_lowerbound [OF lim_dl, of 0] by auto
    moreover have "d \<bullet> l = 0"
    proof (rule d)
      show "f l = 0"
      proof (rule LIMSEQ_unique [of "f \<circ> ?\<beta> \<circ> \<rho>"])
        have "isCont f l"
          using \<open>linear f\<close> linear_continuous_at linear_conv_bounded_linear by blast
        then show "(f \<circ> (\<lambda>n. \<alpha> n /\<^sub>R norm (\<alpha> n)) \<circ> \<rho>) \<longlonglongrightarrow> f l"
          unfolding comp_assoc
          using to_l continuous_imp_tendsto by blast
        have "\<alpha> \<longlonglongrightarrow> 0"
          using norm_lt LIMSEQ_norm_0 by metis
        with \<open>strict_mono \<rho>\<close> have "(\<alpha> \<circ> \<rho>) \<longlonglongrightarrow> 0"
          by (metis LIMSEQ_subseq_LIMSEQ)
        with lim0 \<alpha> have "((\<lambda>x. f x /\<^sub>R norm x) \<circ> (\<alpha> \<circ> \<rho>)) \<longlonglongrightarrow> 0"
          by (force simp: tendsto_at_iff_sequentially)
        then show "(f \<circ> (\<lambda>n. \<alpha> n /\<^sub>R norm (\<alpha> n)) \<circ> \<rho>) \<longlonglongrightarrow> 0"
          by (simp add: o_def scale)
      qed
    qed
    ultimately show False
      using \<open>k > 0\<close> by auto
  qed
  ultimately have dim: "dim {x. f x = 0} = DIM('a)"
    by force
  then show ?thesis
    by (metis (mono_tags, lifting) dim_eq_full UNIV_I eq_0_on_span mem_Collect_eq span_raw_def)
qed

lemma lemma_partial_derivatives:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" and lim: "((\<lambda>x. f (x - a) /\<^sub>R norm (x - a)) \<longlongrightarrow> 0) (at a within S)"
    and lb: "\<And>v. v \<noteq> 0 \<Longrightarrow> (\<exists>k>0.  \<forall>e>0. \<exists>x \<in> S - {a}. norm(a - x) < e \<and> k * norm(a - x) \<le> \<bar>v \<bullet> (x - a)\<bar>)"
  shows "f x = 0"
proof -
  have "((\<lambda>x. f x /\<^sub>R norm x) \<longlongrightarrow> 0) (at 0 within (\<lambda>x. x-a) ` S)"
    using lim by (simp add: Lim_within dist_norm)
  then show ?thesis
  proof (rule lemma_partial_derivatives0 [OF \<open>linear f\<close>])
    fix v :: "'a"
    assume v: "v \<noteq> 0"
    show "\<exists>k>0. \<forall>e>0. \<exists>x. x \<in> (\<lambda>x. x - a) ` S - {0} \<and> norm x < e \<and> k * norm x \<le> \<bar>v \<bullet> x\<bar>"
      using lb [OF v] by (force simp:  norm_minus_commute)
  qed
qed

proposition borel_measurable_partial_derivatives_eu:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes S: "S \<in> sets lebesgue"
    and f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  shows "(\<lambda>x. f' x u \<bullet> v) \<in> borel_measurable (lebesgue_on S)"
proof -
  have lin: "linear (f' x)" if "x \<in> S" for x
    using f[OF that] has_derivative_linear by blast
  have basis_meas: "(\<lambda>x. f' x i \<bullet> j) \<in> borel_measurable (lebesgue_on S)"
    if iB: "i \<in> (Basis :: 'a set)" and jB: "j \<in> (Basis :: 'b set)" for i j
  proof -
    let ?\<phi> = "eucl_to_vec :: 'a \<Rightarrow> real ^ 'a basis"
    let ?\<psi> = "eucl_of_vec :: real ^ 'a basis \<Rightarrow> 'a"
    let ?\<phi>' = "eucl_to_vec :: 'b \<Rightarrow> real ^ 'b basis"
    let ?g = "?\<phi>' \<circ> f \<circ> ?\<psi>"
    let ?g' = "\<lambda>x. ?\<phi>' \<circ> f' (?\<psi> x) \<circ> ?\<psi>"
    let ?S' = "?\<phi> ` S"
    let ?m = "Abs_basis j :: 'b basis"
    let ?n = "Abs_basis i :: 'a basis"
    have lin_\<phi>: "linear ?\<phi>"
      unfolding linear_iff eucl_to_vec_def
      by (auto simp: vec_eq_iff inner_add_left inner_scaleR_left)
    have lin_\<psi>: "linear ?\<psi>"
      unfolding linear_iff eucl_of_vec_def
      by (auto simp: scaleR_sum_right algebra_simps sum.distrib)
    have lin_\<phi>': "linear ?\<phi>'"
      unfolding linear_iff eucl_to_vec_def
      by (auto simp: vec_eq_iff inner_add_left inner_scaleR_left)
    have S'_sets: "?S' \<in> sets lebesgue"
    proof (rule differentiable_image_in_sets_lebesgue [OF S _ linear_imp_differentiable_on[OF lin_\<phi>]])
      show "DIM('a) \<le> DIM(real ^ 'a basis)"
      proof -
        have "CARD('a basis) = card (Abs_basis ` (Basis :: 'a set))"
          by (simp add: UNIV_basis_eq)
        also have "\<dots> = DIM('a)"
          using card_image inj_Abs_basis by fastforce
        finally show ?thesis by simp
      qed
    qed
    have g_deriv: "(?g has_derivative ?g' x) (at x within ?S')" if xS': "x \<in> ?S'" for x
    proof -
      from xS' obtain y where y: "y \<in> S" "x = ?\<phi> y" by auto
      have df: "(f has_derivative f' y) (at y within S)"
        using f[OF y(1)] .
      have "(?\<psi> has_derivative ?\<psi>) (at x within ?S')"
        using lin_\<psi> by (rule linear_imp_has_derivative)
      moreover have "(f has_derivative f' (?\<psi> x)) (at (?\<psi> x) within ?\<psi> ` ?S')"
      proof -
        have "?\<psi> ` ?S' = S"
          by (auto simp: image_comp)
        then show ?thesis
          using df y by simp
      qed
      moreover have "(?\<phi>' has_derivative ?\<phi>') (at (f (?\<psi> x)) within f ` (?\<psi> ` ?S'))"
        using lin_\<phi>' by (rule linear_imp_has_derivative)
      ultimately show ?thesis
        unfolding comp_def
        by (metis has_derivative_in_compose lin_\<phi>' linear_imp_has_derivative)
    qed
    have entry_eq: "matrix (?g' (?\<phi> x)) $ ?m $ ?n = f' x i \<bullet> j" if "x \<in> S" for x
    proof -
      have lin_g': "linear (?g' (?\<phi> x))"
        using lin[OF that] lin_\<phi>' lin_\<psi> by (intro linear_compose) auto
      have "matrix (?g' (?\<phi> x)) $ ?m $ ?n = (?g' (?\<phi> x) (axis ?n 1)) $ ?m"
        by (simp add: matrix_def)
      also have "axis ?n 1 = eucl_to_vec i"
        by (metis Abs_basis_inverse eucl_of_vec_axis eucl_of_vec_eq_iff eucl_of_vec_to_vec iB
            pth_1)
      also have "?g' (?\<phi> x) (eucl_to_vec i) = ?\<phi>' (f' x i)"
        by simp
      also have "\<dots> $ ?m = f' x i \<bullet> j"
        using jB by (simp add: eucl_to_vec_def Abs_basis_inverse)
      finally show ?thesis .
    qed
    have vec_meas: "(\<lambda>x. matrix (?g' x) $ ?m $ ?n) \<in> borel_measurable (lebesgue_on ?S')"
      by (rule borel_measurable_partial_derivatives [OF S'_sets g_deriv])
    have comp_meas: "(\<lambda>x. matrix (?g' (?\<phi> x)) $ ?m $ ?n) \<in> borel_measurable (lebesgue_on S)"
    proof -
      have \<phi>_meas: "?\<phi> \<in> borel_measurable borel"
        using lin_\<phi> continuous_on_eq_continuous_within linear_continuous_on
        by (metis borel_measurable_continuous_onI linear_conv_bounded_linear)
      have if_meas: "(\<lambda>x. if x \<in> ?S' then matrix (?g' x) $ ?m $ ?n else 0) \<in> borel_measurable lebesgue"
        using borel_measurable_if_I[OF vec_meas S'_sets] .
      have global_meas: "(\<lambda>x. if ?\<phi> x \<in> ?S' then matrix (?g' (?\<phi> x)) $ ?m $ ?n else 0) \<in> borel_measurable lebesgue"
      proof (subst borel_measurable_lebesgue_preimage_borel, intro allI impI)
        fix T :: "real set" assume T: "T \<in> sets borel"
        let ?h = "\<lambda>x. if x \<in> ?S' then matrix (?g' x) $ ?m $ ?n else 0"
        have h_meas: "{x. ?h x \<in> T} \<in> sets lebesgue"
          using if_meas T by (simp add: borel_measurable_lebesgue_preimage_borel)
        have eq: "{x. ?h (?\<phi> x) \<in> T} = ?\<psi> ` {x. ?h x \<in> T}"
        proof (intro set_eqI iffI)
          fix x assume "x \<in> {x. ?h (?\<phi> x) \<in> T}"
          then have "?h (?\<phi> x) \<in> T" by simp
          moreover have "?\<phi> x \<in> {y. ?h y \<in> T}" using calculation by simp
          moreover have "x = ?\<psi> (?\<phi> x)" by (simp add: eucl_of_vec_to_vec)
          ultimately show "x \<in> ?\<psi> ` {x. ?h x \<in> T}" by blast
        next
          fix x assume "x \<in> ?\<psi> ` {x. ?h x \<in> T}"
          then obtain y where "?h y \<in> T" "x = ?\<psi> y" by auto
          then show "x \<in> {x. ?h (?\<phi> x) \<in> T}"
            by (simp add: eucl_to_vec_of_vec split: if_split_asm)
        qed
        have dim_le: "DIM(real ^ 'a basis) \<le> DIM('a)"
        proof -
          have "CARD('a basis) = card (Abs_basis ` (Basis :: 'a set))"
            by (simp add: UNIV_basis_eq)
          also have "\<dots> = DIM('a)"
            using card_image inj_Abs_basis by fastforce
          finally show ?thesis by simp
        qed
        show "{x. (if ?\<phi> x \<in> ?S' then matrix (?g' (?\<phi> x)) $ ?m $ ?n else 0) \<in> T} \<in> sets lebesgue"
          using eq differentiable_image_in_sets_lebesgue[OF h_meas dim_le linear_imp_differentiable_on[OF lin_\<psi>]]
          by simp
      qed
      have simp: "?\<phi> x \<in> ?S' \<longleftrightarrow> x \<in> S" for x
        using eucl_to_vec_eq_iff by auto
      have "(\<lambda>x. if x \<in> S then matrix (?g' (?\<phi> x)) $ ?m $ ?n else 0) \<in> borel_measurable lebesgue"
        using global_meas by (simp add: simp)
      then show ?thesis
        using borel_measurable_if_D S by fastforce
    qed
    show "(\<lambda>x. f' x i \<bullet> j) \<in> borel_measurable (lebesgue_on S)"
      by (smt (verit, del_insts) comp_meas entry_eq measurable_lebesgue_cong)
  qed
  have on_S: "f' x u \<bullet> v = (\<Sum>i\<in>(Basis::'a set). \<Sum>j\<in>(Basis::'b set). (u \<bullet> i) * (v \<bullet> j) * (f' x i \<bullet> j))"
    if "x \<in> S" for x
  proof -
    have "f' x u = (\<Sum>i\<in>Basis. (u \<bullet> i) *\<^sub>R f' x i)"
      using lin[OF that] using euclidean_representation linear_sum[of "f' x"] linear_scale[of "f' x"]
      by (metis (no_types, lifting) ext)
    then have eq1: "f' x u \<bullet> v = (\<Sum>i\<in>Basis. (u \<bullet> i) * (f' x i \<bullet> v))"
      by (simp add: inner_sum_left)
    have eq2: "f' x (i::'a) \<bullet> v = (\<Sum>j\<in>(Basis::'b set). (v \<bullet> j) * (f' x i \<bullet> j))" for i
      by (subst euclidean_representation[of v, symmetric])
         (simp add: inner_sum_right)
    show ?thesis
      unfolding eq1 by (simp add: eq2 sum_distrib_left mult.assoc)
  qed
  have "(\<lambda>x. \<Sum>i\<in>(Basis::'a set). \<Sum>j\<in>(Basis::'b set). (u \<bullet> i) * (v \<bullet> j) * (f' x i \<bullet> j))
        \<in> borel_measurable (lebesgue_on S)"
    by (intro borel_measurable_sum borel_measurable_times borel_measurable_const basis_meas) auto
  moreover have "(\<lambda>x. f' x u \<bullet> v) \<in> borel_measurable (lebesgue_on S) \<longleftrightarrow>
                 (\<lambda>x. \<Sum>i\<in>(Basis::'a set). \<Sum>j\<in>(Basis::'b set). (u \<bullet> i) * (v \<bullet> j) * (f' x i \<bullet> j))
                 \<in> borel_measurable (lebesgue_on S)"
    by (intro measurable_cong) (auto simp: on_S space_restrict_space)
  ultimately show ?thesis
    by simp
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

lemma Sard_lemma2:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n::{finite,wellorder}"
  assumes mlen: "CARD('m) \<le> CARD('n)" (is "?m \<le> ?n")
    and "B > 0" "bounded S"
    and derS: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and rank: "\<And>x. x \<in> S \<Longrightarrow> rank(matrix(f' x)) < CARD('n)"
    and B: "\<And>x. x \<in> S \<Longrightarrow> onorm(f' x) \<le> B"
  shows "negligible(f ` S)"
proof -
  have lin_f': "\<And>x. x \<in> S \<Longrightarrow> linear(f' x)"
    using derS has_derivative_linear by blast
  show ?thesis
  proof (clarsimp simp add: negligible_outer_le)
    fix e :: "real"
    assume "e > 0"
    obtain c where csub: "S \<subseteq> cbox (- (vec c)) (vec c)" and "c > 0"
    proof -
      obtain b where b: "\<And>x. x \<in> S \<Longrightarrow> norm x \<le> b"
        using \<open>bounded S\<close> by (auto simp: bounded_iff)
      show thesis
      proof
        have "- \<bar>b\<bar> - 1 \<le> x $ i \<and> x $ i \<le> \<bar>b\<bar> + 1" if "x \<in> S" for x i
          using component_le_norm_cart [of x i] b [OF that] by auto
        then show "S \<subseteq> cbox (- vec (\<bar>b\<bar> + 1)) (vec (\<bar>b\<bar> + 1))"
          by (auto simp: mem_box_cart)
      qed auto
    qed
    then have box_cc: "box (- (vec c)) (vec c) \<noteq> {}" and cbox_cc: "cbox (- (vec c)) (vec c) \<noteq> {}"
      by (auto simp: interval_eq_empty_cart)
    obtain d where "d > 0" "d \<le> B"
             and d: "(d * 2) * (4 * B) ^ (?n - 1) \<le> e / (2*c) ^ ?m / ?m ^ ?m"
      apply (rule that [of "min B (e / (2*c) ^ ?m / ?m ^ ?m / (4 * B) ^ (?n - 1) / 2)"])
      using \<open>B > 0\<close> \<open>c > 0\<close> \<open>e > 0\<close>
      by (simp_all add: divide_simps min_mult_distrib_right)
    have "\<exists>r. 0 < r \<and> r \<le> 1/2 \<and>
              (x \<in> S
               \<longrightarrow> (\<forall>y. y \<in> S \<and> norm(y - x) < r
                       \<longrightarrow> norm(f y - f x - f' x (y - x)) \<le> d * norm(y - x)))" for x
    proof (cases "x \<in> S")
      case True
      then obtain r where "r > 0"
              and "\<And>y. \<lbrakk>y \<in> S; norm (y - x) < r\<rbrakk>
                       \<Longrightarrow> norm (f y - f x - f' x (y - x)) \<le> d * norm (y - x)"
        using derS \<open>d > 0\<close> by (force simp: has_derivative_within_alt)
      then show ?thesis
        by (rule_tac x="min r (1/2)" in exI) simp
    next
      case False
      then show ?thesis
        by (rule_tac x="1/2" in exI) simp
    qed
    then obtain r where r12: "\<And>x. 0 < r x \<and> r x \<le> 1/2"
            and r: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; norm(y - x) < r x\<rbrakk>
                          \<Longrightarrow> norm(f y - f x - f' x (y - x)) \<le> d * norm(y - x)"
      by metis
    then have ga: "gauge (\<lambda>x. ball x (r x))"
      by (auto simp: gauge_def)
    obtain \<D> where \<D>: "countable \<D>" and sub_cc: "\<Union>\<D> \<subseteq> cbox (- vec c) (vec c)"
      and cbox: "\<And>K. K \<in> \<D> \<Longrightarrow> interior K \<noteq> {} \<and> (\<exists>u v. K = cbox u v)"
      and djointish: "pairwise (\<lambda>A B. interior A \<inter> interior B = {}) \<D>"
      and covered: "\<And>K. K \<in> \<D> \<Longrightarrow> \<exists>x \<in> S \<inter> K. K \<subseteq> ball x (r x)"
      and close: "\<And>u v. cbox u v \<in> \<D> \<Longrightarrow> \<exists>n. \<forall>i::'m. v $ i - u $ i = 2*c / 2^n"
      and covers: "S \<subseteq> \<Union>\<D>"
      apply (rule covering_lemma [OF csub box_cc ga])
      apply (auto simp: Basis_vec_def cart_eq_inner_axis [symmetric])
      done
    let ?\<mu> = "measure lebesgue"
    have "\<exists>T. T \<in> lmeasurable \<and> f ` (K \<inter> S) \<subseteq> T \<and> ?\<mu> T \<le> e / (2*c) ^ ?m * ?\<mu> K"
      if "K \<in> \<D>" for K
    proof -
      obtain u v where uv: "K = cbox u v"
        using cbox \<open>K \<in> \<D>\<close> by blast
      then have uv_ne: "cbox u v \<noteq> {}"
        using cbox that by fastforce
      obtain x where x: "x \<in> S \<inter> cbox u v" "cbox u v \<subseteq> ball x (r x)"
        using \<open>K \<in> \<D>\<close> covered uv by blast
      then have "dim (range (f' x)) < ?n"
        using rank_dim_range [of "matrix (f' x)"] x rank[of x]
        by (auto simp: matrix_works scalar_mult_eq_scaleR lin_f')
      then obtain T where T: "T \<in> lmeasurable"
            and subT: "{z. norm(z - f x) \<le> (2 * B) * norm(v - u) \<and> (\<exists>t \<in> range (f' x). norm(z - f x - t) \<le> d * norm(v - u))} \<subseteq> T"
            and measT: "?\<mu> T \<le> (2 * (d * norm(v - u))) * (2 * ((2 * B) * norm(v - u))) ^ (?n - 1)"
                        (is "_ \<le> ?DVU")
        using Sard_lemma1 [of "range (f' x)" "(2 * B) * norm(v - u)" "d * norm(v - u)"]
        using \<open>B > 0\<close> \<open>d > 0\<close> by auto
      show ?thesis
      proof (intro exI conjI)
        have "f ` (K \<inter> S) \<subseteq> {z. norm(z - f x) \<le> (2 * B) * norm(v - u) \<and> (\<exists>t \<in> range (f' x). norm(z - f x - t) \<le> d * norm(v - u))}"
          unfolding uv
        proof (clarsimp simp: mult.assoc, intro conjI)
          fix y
          assume y: "y \<in> cbox u v" and "y \<in> S"
          then have "norm (y - x) < r x"
            by (metis dist_norm mem_ball norm_minus_commute subsetCE x(2))
          then have le_dyx: "norm (f y - f x - f' x (y - x)) \<le> d * norm (y - x)"
            using r [of x y] x \<open>y \<in> S\<close> by blast
          have yx_le: "norm (y - x) \<le> norm (v - u)"
          proof (rule norm_le_componentwise_cart)
            show "norm ((y - x) $ i) \<le> norm ((v - u) $ i)" for i
              using x y by (force simp: mem_box_cart dest!: spec [where x=i])
          qed
          have *: "\<lbrakk>norm(y - x - z) \<le> d; norm z \<le> B; d \<le> B\<rbrakk> \<Longrightarrow> norm(y - x) \<le> 2 * B"
            for x y z :: "real^'n::_" and d B
            using norm_triangle_ineq2 [of "y - x" z] by auto
          show "norm (f y - f x) \<le> 2 * (B * norm (v - u))"
          proof (rule * [OF le_dyx])
            have "norm (f' x (y - x)) \<le> onorm (f' x) * norm (y - x)"
              using onorm [of "f' x" "y-x"] by (meson IntE lin_f' linear_linear x(1))
            also have "\<dots> \<le> B * norm (v - u)"
              by (meson B IntE lin_f' linear_linear mult_mono' norm_ge_zero onorm_pos_le x(1) yx_le)
            finally show "norm (f' x (y - x)) \<le> B * norm (v - u)" .
            show "d * norm (y - x) \<le> B * norm (v - u)"
              using \<open>B > 0\<close> by (auto intro: mult_mono [OF \<open>d \<le> B\<close> yx_le])
          qed
          show "\<exists>t. norm (f y - f x - f' x t) \<le> d * norm (v - u)"
            by (smt (verit, best) \<open>0 < d\<close> le_dyx mult_le_cancel_left_pos yx_le)
        qed
        with subT show "f ` (K \<inter> S) \<subseteq> T" by blast
        show "?\<mu> T \<le> e / (2*c) ^ ?m * ?\<mu> K"
        proof (rule order_trans [OF measT])
          have "?DVU = (d * 2 * (4 * B) ^ (?n - 1)) * norm (v - u)^?n"
            using \<open>c > 0\<close>
            apply (simp add: algebra_simps)
            by (metis Suc_pred power_Suc zero_less_card_finite)
          also have "\<dots> \<le> (e / (2*c) ^ ?m / (?m ^ ?m)) * norm(v - u) ^ ?n"
            by (rule mult_right_mono [OF d]) auto
          also have "\<dots> \<le> e / (2*c) ^ ?m * ?\<mu> K"
          proof -
            have "u \<in> ball (x) (r x)" "v \<in> ball x (r x)"
              using box_ne_empty(1) contra_subsetD [OF x(2)] mem_box(2) uv_ne by fastforce+
            moreover have "r x \<le> 1/2"
              using r12 by auto
            ultimately have "norm (v - u) \<le> 1"
              using norm_triangle_half_r [of x u 1 v]
              by (metis (no_types, opaque_lifting) dist_commute dist_norm less_eq_real_def less_le_trans mem_ball)
            then have "norm (v - u) ^ ?n \<le> norm (v - u) ^ ?m"
              by (simp add: power_decreasing [OF mlen])
            also have "\<dots> \<le> ?\<mu> K * real (?m ^ ?m)"
            proof -
              obtain n where n: "\<And>i. v$i - u$i = 2 * c / 2^n"
                using close [of u v] \<open>K \<in> \<D>\<close> uv by blast
              have "norm (v - u) ^ ?m \<le> (\<Sum>i\<in>UNIV. \<bar>(v - u) $ i\<bar>) ^ ?m"
                by (intro norm_le_l1_cart power_mono) auto
              also have "\<dots> \<le> (\<Prod>i\<in>UNIV. v $ i - u $ i) * real CARD('m) ^ CARD('m)"
                by (simp add: n field_simps \<open>c > 0\<close> less_eq_real_def)
              also have "\<dots> = ?\<mu> K * real (?m ^ ?m)"
                by (simp add: uv uv_ne content_cbox_cart)
              finally show ?thesis .
            qed
            finally have *: "1 / real (?m ^ ?m) * norm (v - u) ^ ?n \<le> ?\<mu> K"
              by (simp add: field_split_simps)
            show ?thesis
              using mult_left_mono [OF *, of "e / (2*c) ^ ?m"] \<open>c > 0\<close> \<open>e > 0\<close> by auto
          qed
          finally show "?DVU \<le> e / (2*c) ^ ?m * ?\<mu> K" .
        qed
      qed (use T in auto)
    qed
    then obtain g where meas_g: "\<And>K. K \<in> \<D> \<Longrightarrow> g K \<in> lmeasurable"
                    and sub_g: "\<And>K. K \<in> \<D> \<Longrightarrow> f ` (K \<inter> S) \<subseteq> g K"
                    and le_g: "\<And>K. K \<in> \<D> \<Longrightarrow> ?\<mu> (g K) \<le> e / (2*c)^?m * ?\<mu> K"
      by metis
    have le_e: "?\<mu> (\<Union>i\<in>\<F>. g i) \<le> e"
      if "\<F> \<subseteq> \<D>" "finite \<F>" for \<F>
    proof -
      have "?\<mu> (\<Union>i\<in>\<F>. g i) \<le> (\<Sum>i\<in>\<F>. ?\<mu> (g i))"
        using meas_g \<open>\<F> \<subseteq> \<D>\<close> by (auto intro: measure_UNION_le [OF \<open>finite \<F>\<close>])
      also have "\<dots> \<le> (\<Sum>K\<in>\<F>. e / (2*c) ^ ?m * ?\<mu> K)"
        using \<open>\<F> \<subseteq> \<D>\<close> sum_mono [OF le_g] by (meson le_g subsetCE sum_mono)
      also have "\<dots> = e / (2*c) ^ ?m * (\<Sum>K\<in>\<F>. ?\<mu> K)"
        by (simp add: sum_distrib_left)
      also have "\<dots> \<le> e"
      proof -
        have "\<F> division_of \<Union>\<F>"
        proof (rule division_ofI)
          show "K \<subseteq> \<Union>\<F>"  "K \<noteq> {}" "\<exists>a b. K = cbox a b" if "K \<in> \<F>" for K
            using \<open>K \<in> \<F>\<close> covered cbox \<open>\<F> \<subseteq> \<D>\<close> by (auto simp: Union_upper)
          show "interior K \<inter> interior L = {}" if "K \<in> \<F>" and "L \<in> \<F>" and "K \<noteq> L" for K L
            by (metis (mono_tags, lifting) \<open>\<F> \<subseteq> \<D>\<close> pairwiseD djointish pairwise_subset that)
        qed (use that in auto)
        then have "sum ?\<mu> \<F> \<le> ?\<mu> (\<Union>\<F>)"
          by (simp add: content_division)
        also have "\<dots> \<le> ?\<mu> (cbox (- vec c) (vec c) :: (real, 'm) vec set)"
        proof (rule measure_mono_fmeasurable)
          show "\<Union>\<F> \<subseteq> cbox (- vec c) (vec c)"
            by (meson Sup_subset_mono sub_cc order_trans \<open>\<F> \<subseteq> \<D>\<close>)
        qed (use \<open>\<F> division_of \<Union>\<F>\<close> lmeasurable_division in auto)
        also have "\<dots> = Henstock_Kurzweil_Integration.content (cbox (- vec c) (vec c) :: (real, 'm) vec set)"
          by simp
        also have "\<dots> \<le> (2 ^ ?m * c ^ ?m)"
          using \<open>c > 0\<close> by (simp add: content_cbox_if_cart)
        finally have "sum ?\<mu> \<F> \<le> (2 ^ ?m * c ^ ?m)" .
        then show ?thesis
          using \<open>e > 0\<close> \<open>c > 0\<close> by (auto simp: field_split_simps)
      qed
      finally show ?thesis .
    qed
    show "\<exists>T. f ` S \<subseteq> T \<and> T \<in> lmeasurable \<and> ?\<mu> T \<le> e"
    proof (intro exI conjI)
      show "f ` S \<subseteq> \<Union> (g ` \<D>)"
        using covers sub_g by force
      show "\<Union> (g ` \<D>) \<in> lmeasurable"
        by (rule fmeasurable_UN_bound [OF \<open>countable \<D>\<close> meas_g le_e])
      show "?\<mu> (\<Union> (g ` \<D>)) \<le> e"
        by (rule measure_UN_bound [OF \<open>countable \<D>\<close> meas_g le_e])
    qed
  qed
qed


theorem baby_Sard:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n::{finite,wellorder}"
  assumes mlen: "CARD('m) \<le> CARD('n)"
    and der: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and rank: "\<And>x. x \<in> S \<Longrightarrow> rank(matrix(f' x)) < CARD('n)"
  shows "negligible(f ` S)"
proof -
  let ?U = "\<lambda>n. {x \<in> S. norm(x) \<le> n \<and> onorm(f' x) \<le> real n}"
  have "\<And>x. x \<in> S \<Longrightarrow> \<exists>n. norm x \<le> real n \<and> onorm (f' x) \<le> real n"
    by (meson linear order_trans real_arch_simple)
  then have eq: "S = (\<Union>n. ?U n)"
    by auto
  have "negligible (f ` ?U n)" for n
  proof (rule Sard_lemma2 [OF mlen])
    show "0 < real n + 1"
      by auto
    show "bounded (?U n)"
      using bounded_iff by blast
    show "(f has_derivative f' x) (at x within ?U n)" if "x \<in> ?U n" for x
      using der that by (force intro: has_derivative_subset)
  qed (use rank in auto)
  then show ?thesis
    by (subst eq) (simp add: image_Union negligible_Union_nat)
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
    by (simp add: injI)
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
      using neg_etv negligible_iff_null_sets
      by (metis (no_types) negligible_differentiable_image_negligible [OF le_refl]
            differentiable_on_linear [OF eucl.linear_eucl_of_vec])
    finally show "negligible (f ` S)" .
  qed
qed




subsection\<open>A one-way version of change-of-variables not assuming injectivity. \<close>

lemma integral_on_image_ubound_weak:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
      and f: "f \<in> borel_measurable (lebesgue_on (g ` S))"
      and nonneg_fg:  "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f(g x)"
      and der_g:   "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and det_int_fg: "(\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * f(g x)) integrable_on S"
      and meas_gim: "\<And>T. \<lbrakk>T \<subseteq> g ` S; T \<in> sets lebesgue\<rbrakk> \<Longrightarrow> {x \<in> S. g x \<in> T} \<in> sets lebesgue"
    shows "f integrable_on (g ` S) \<and>
           integral (g ` S) f \<le> integral S (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * f(g x))"
         (is "_ \<and> _ \<le> ?b")
proof -
  let ?D = "\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar>"
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
    have "space (lebesgue_on (UNIV::(real,'n) vec set)) = UNIV"
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
                 \<le> integral S (\<lambda>t. \<bar>matrix_det (matrix (g' t))\<bar> * y * indicator {x. h n x = y} (g t))"
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
          have "(\<lambda>v. matrix_det (matrix (g' v))) \<in> borel_measurable (lebesgue_on (S \<inter> {v. h n (g v) = y}))"
            by (metis Int_lower1 S assms(4) borel_measurable_det_Jacobian_matrix measurable_restrict_mono)
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
      then have int_det: "(\<lambda>t. \<bar>matrix_det (matrix (g' t))\<bar>) integrable_on ({t. h n (g t) = y} \<inter> S)"
        using integrable_restrict_Int by force
      have "(g ` ({t. h n (g t) = y} \<inter> S)) \<in> lmeasurable"
        by (blast intro: has_derivative_subset [OF der_g]  measurable_differentiable_image [OF h_lmeas] int_det)
      moreover have "g ` ({t. h n (g t) = y} \<inter> S) = {x. h n x = y} \<inter> g ` S"
        by blast
      moreover have "measure lebesgue (g ` ({t. h n (g t) = y} \<inter> S))
                     \<le> integral ({t. h n (g t) = y} \<inter> S) (\<lambda>t. \<bar>matrix_det (matrix (g' t))\<bar>)"
        by (blast intro: has_derivative_subset [OF der_g] measure_differentiable_image [OF h_lmeas _ int_det])
      ultimately show ?thesis
        using \<open>y > 0\<close> integral_restrict_Int [of S "{t. h n (g t) = y}" "\<lambda>t. \<bar>matrix_det (matrix (g' t))\<bar> * y"]
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
      also have "\<dots> \<le> (\<Sum>y\<in>range (h n). integral S (\<lambda>u. \<bar>matrix_det (matrix (g' u))\<bar> * y * indicat_real {x. h n x = y} (g u)))"
        using yind by (force intro: sum_mono)
      also have "\<dots> = integral S (\<lambda>u. \<Sum>y\<in>range (h n). \<bar>matrix_det (matrix (g' u))\<bar> * y * indicat_real {x. h n x = y} (g u))"
      proof (rule integral_sum [OF fin_R, symmetric])
        fix y assume y: "y \<in> ?R"
        with nonneg_h have "y \<ge> 0"
          by auto
        show "(\<lambda>u. \<bar>matrix_det (matrix (g' u))\<bar> * y * indicat_real {x. h n x = y} (g u)) integrable_on S"
        proof (rule measurable_bounded_by_integrable_imp_integrable)
          have "(\<lambda>x. indicat_real {x. h n x = y} (g x)) \<in> borel_measurable (lebesgue_on S)"
            using h_lmeas S
            by (auto simp: indicator_vimage [symmetric] borel_measurable_indicator_iff sets_restrict_space_iff)
          then show "(\<lambda>u. \<bar>matrix_det (matrix (g' u))\<bar> * y * indicat_real {x. h n x = y} (g u)) \<in> borel_measurable (lebesgue_on S)"
            by (intro borel_measurable_times borel_measurable_abs borel_measurable_const borel_measurable_det_Jacobian_matrix [OF S der_g])
        next
          fix x
          assume "x \<in> S"
          then have "y * indicat_real {x. h n x = y} (g x) \<le> f (g x)"
            by (metis (full_types) h_le_f indicator_simps mem_Collect_eq mult.right_neutral mult_zero_right nonneg_fg)
          with \<open>y \<ge> 0\<close> show "norm (?D x * y * indicat_real {x. h n x = y} (g x)) \<le> ?D x * f(g x)"
            by (simp add: abs_mult mult.assoc mult_left_mono)
        qed (use S det_int_fg in auto)
      qed
      also have "\<dots> = integral S (\<lambda>T. \<bar>matrix_det (matrix (g' T))\<bar> *
                                        (\<Sum>y\<in>range (h n). y * indicat_real {x. h n x = y} (g T)))"
        by (simp add: sum_distrib_left mult.assoc)
      also have "\<dots> = ?rhs"
        by (metis hn_eq)
      finally show "integral (g ` S) (h n) \<le> ?rhs" .
    qed
  qed
  have le: "integral S (\<lambda>T. \<bar>matrix_det (matrix (g' T))\<bar> * h n (g T)) \<le> ?b" for n
  proof (rule integral_le)
    show "(\<lambda>T. \<bar>matrix_det (matrix (g' T))\<bar> * h n (g T)) integrable_on S"
    proof (rule measurable_bounded_by_integrable_imp_integrable)
      have "(\<lambda>T. \<bar>matrix_det (matrix (g' T))\<bar> *\<^sub>R h n (g T)) \<in> borel_measurable (lebesgue_on S)"
      proof (intro borel_measurable_scaleR borel_measurable_abs borel_measurable_det_Jacobian_matrix \<open>S \<in> sets lebesgue\<close>)
        have eq: "{x \<in> S. f x \<le> a} = (\<Union>b \<in> (f ` S) \<inter> atMost a. {x. f x = b} \<inter> S)" for f and a::real
          by auto
        have "finite ((\<lambda>x. h n (g x)) ` S \<inter> {..a})" for a
          by (force intro: finite_subset [OF _ fin_R])
        with h_lmeas [of n] show "(\<lambda>x. h n (g x)) \<in> borel_measurable (lebesgue_on S)"
          apply (simp add: borel_measurable_vimage_halfspace_component_le \<open>S \<in> sets lebesgue\<close> sets_restrict_space_iff eq)
          by (metis (mono_tags) SUP_inf sets.finite_UN)
      qed (use der_g in blast)
      then show "(\<lambda>T. \<bar>matrix_det (matrix (g' T))\<bar> * h n (g T)) \<in> borel_measurable (lebesgue_on S)"
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


lemma integral_on_image_ubound_nonneg:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real"
  assumes nonneg_fg: "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f(g x)"
      and der_g:   "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and intS: "(\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * f(g x)) integrable_on S"
  shows "f integrable_on (g ` S) \<and> integral (g ` S) f \<le> integral S (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * f(g x))"
         (is "_ \<and> _ \<le> ?b")
proof -
  let ?D = "\<lambda>x. matrix_det (matrix (g' x))"
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
      have "(\<lambda>v. matrix_det (matrix (g' v))) \<in> borel_measurable (lebesgue_on S')"
        using S' borel_measurable_det_Jacobian_matrix der_gS' by blast
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
        by (auto simp: S'_def det_nz_iff_inj)
    qed (use der_gS' in auto)
    ultimately show ?thesis
      using double_lebesgue_sets [OF S' gS' order_refl] that by blast
  qed
  have int_gS': "f integrable_on g ` S' \<and> integral (g ` S') f \<le> integral S' (\<lambda>x. \<bar>?D x\<bar> * f(g x))"
    using integral_on_image_ubound_weak [OF S' f nonneg_fg der_gS' intS' lebS'] S'_def by blast
  have "negligible (g ` {x \<in> S. matrix_det(matrix(g' x)) = 0})"
  proof (rule baby_Sard, simp_all)
    fix x
    assume x: "x \<in> S \<and> matrix_det (matrix (g' x)) = 0"
    then show "(g has_derivative g' x) (at x within {x \<in> S. matrix_det (matrix (g' x)) = 0})"
      by (metis (no_types, lifting) der_g has_derivative_subset mem_Collect_eq subsetI)
    then show "rank (matrix (g' x)) < CARD('n)"
      using det_nz_iff_inj matrix_vector_mul_linear x
      by (fastforce simp add: less_rank_noninjective)
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
      using  eq integral_restrict_Int by simp
    also have "\<dots> \<le> integral S' (\<lambda>x. \<bar>?D x\<bar> * f(g x))"
      by (metis int_gS')
    also have "\<dots> \<le> ?b"
      by (rule integral_subset_le [OF _ intS' intS]) (use nonneg_fg S'_def in auto)
    finally show "integral (g ` S) f \<le> ?b" .
  qed
qed


lemma absolutely_integrable_on_image_real:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real" and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and intS: "(\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * f(g x)) absolutely_integrable_on S"
  shows "f absolutely_integrable_on (g ` S)"
proof -
  let ?D = "\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * f (g x)"
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
         integral (g ` ?N) (\<lambda>x. - f x) \<le> integral ?N (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * - f (g x))"
  proof (rule integral_on_image_ubound_nonneg [OF _ der_gN])
    have 1: "?D integrable_on {x \<in> S. ?D x < 0}"
      using Dlt
      by (auto intro: set_lebesgue_integral_eq_integral [OF set_integrable_subset] intS)
    have "uminus \<circ> (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * - f (g x)) integrable_on ?N"
      by (simp add: o_def mult_less_0_iff empty_imp_negligible integrable_spike_set [OF 1])
    then show "(\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * - f (g x)) integrable_on ?N"
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
    proof (rule integral_on_image_ubound_nonneg [OF _ der_gP])
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


proposition absolutely_integrable_on_image:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and intS: "(\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S"
  shows "f absolutely_integrable_on (g ` S)"
  apply (rule absolutely_integrable_componentwise [OF absolutely_integrable_on_image_real [OF der_g]])
  using absolutely_integrable_component [OF intS]  by auto

proposition integral_on_image_ubound:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real" and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes"\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f(g x)"
    and "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and "(\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * f(g x)) integrable_on S"
  shows "integral (g ` S) f \<le> integral S (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * f(g x))"
  using integral_on_image_ubound_nonneg [OF assms] by simp


subsection\<open>Change-of-variables theorem\<close>

text\<open>The classic change-of-variables theorem. We have two versions with quite general hypotheses,
the first that the transforming function has a continuous inverse, the second that the base set is
Lebesgue measurable.\<close>
lemma cov_invertible_nonneg_le:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real" and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and der_h: "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
    and f0: "\<And>y. y \<in> T \<Longrightarrow> 0 \<le> f y"
    and hg: "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
    and gh: "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
    and id: "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "f integrable_on T \<and> (integral T f) \<le> b \<longleftrightarrow>
             (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * f(g x)) integrable_on S \<and>
             integral S (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * f(g x)) \<le> b"
        (is "?lhs = ?rhs")
proof -
  have Teq: "T = g`S" and Seq: "S = h`T"
    using hg gh image_iff by fastforce+
  have gS: "g differentiable_on S"
    by (meson der_g differentiable_def differentiable_on_def)
  let ?D = "\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * f (g x)"
  show ?thesis
  proof
    assume ?lhs
    then have fT: "f integrable_on T" and intf: "integral T f \<le> b"
      by blast+
    show ?rhs
    proof
      let ?fgh = "\<lambda>x. \<bar>matrix_det (matrix (h' x))\<bar> * (\<bar>matrix_det (matrix (g' (h x)))\<bar> * f (g (h x)))"
      have ddf: "?fgh x = f x"
        if "x \<in> T" for x
      proof -
        have "matrix (h' x) ** matrix (g' (h x)) = mat 1"
          by (metis der_g der_h gh has_derivative_linear local.id matrix_compose matrix_id_mat_1 that)
        then have "\<bar>matrix_det (matrix (h' x))\<bar> * \<bar>matrix_det (matrix (g' (h x)))\<bar> = 1"
          by (metis abs_1 abs_mult det_I det_mul)
        then show ?thesis
          by (simp add: gh that)
      qed
      have "?D integrable_on (h ` T)"
      proof (intro set_lebesgue_integral_eq_integral absolutely_integrable_on_image_real)
        show "(\<lambda>x. ?fgh x) absolutely_integrable_on T"
          by (smt (verit, del_insts) abs_absolutely_integrableI_1 ddf f0 fT integrable_eq)
      qed (use der_h in auto)
      with Seq show "(\<lambda>x. ?D x) integrable_on S"
        by simp
      have "integral S (\<lambda>x. ?D x) \<le> integral T (\<lambda>x. ?fgh x)"
        unfolding Seq
      proof (rule integral_on_image_ubound)
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
      using der_g f0 hg integral_on_image_ubound_nonneg by blast
    moreover have "integral (g ` S) f \<le> integral S (\<lambda>x. ?D x)"
      by (rule integral_on_image_ubound [OF f0 der_g]) (use R Teq in auto)
    ultimately show ?lhs
      using R by (simp add: Teq)
  qed
qed


lemma cov_invertible_nonneg_eq:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real" and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
      and "\<And>y. y \<in> T \<Longrightarrow> 0 \<le> f y"
      and "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
      and "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
      and "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "((\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * f(g x)) has_integral b) S \<longleftrightarrow> (f has_integral b) T"
  using cov_invertible_nonneg_le [OF assms]
  by (simp add: has_integral_iff) (meson eq_iff)


lemma cov_invertible_real:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real" and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and der_h: "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
      and hg: "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
      and gh: "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
      and id: "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "(\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * f(g x)) = b \<longleftrightarrow>
         f absolutely_integrable_on T \<and> integral T f = b"
         (is "?lhs = ?rhs")
proof -
  have Teq: "T = g`S" and Seq: "S = h`T"
    using hg gh image_iff by fastforce+
  let ?DP = "\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * f(g x)" and ?DN = "\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * -f(g x)"
  have "+": "(?DP has_integral b) {x \<in> S. f (g x) > 0} \<longleftrightarrow> (f has_integral b) {y \<in> T. f y > 0}" for b
  proof (rule cov_invertible_nonneg_eq)
    have *: "(\<lambda>x. f (g x)) -` Y \<inter> {x \<in> S. f (g x) > 0}
          = ((\<lambda>x. f (g x)) -` Y \<inter> S) \<inter> {x \<in> S. f (g x) > 0}" for Y
      by auto
    show "(g has_derivative g' x) (at x within {x \<in> S. f (g x) > 0})" if "x \<in> {x \<in> S. f (g x) > 0}" for x
      using that der_g has_derivative_subset by fastforce
    show "(h has_derivative h' y) (at y within {y \<in> T. f y > 0})" if "y \<in> {y \<in> T. f y > 0}" for y
      using that der_h has_derivative_subset by fastforce
  qed (use gh hg id in auto)
  have "-": "(?DN has_integral b) {x \<in> S. f (g x) < 0} \<longleftrightarrow> ((\<lambda>x. - f x) has_integral b) {y \<in> T. f y < 0}" for b
  proof (rule cov_invertible_nonneg_eq)
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
      have [simp]: "{y \<in> T. f y < 0} \<inter> {y \<in> T. 0 < f y} = {}" for T and f :: "(real^'n::_) \<Rightarrow> real"
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
      have [simp]: "{y \<in> S. f y < 0} \<inter> {y \<in> S. 0 < f y} = {}" for S and f :: "(real^'n::_) \<Rightarrow> real"
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
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and der_h: "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
    and hg: "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
    and gh: "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
    and id: "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "(\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
             integral S (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b
         \<longleftrightarrow> f absolutely_integrable_on T \<and> integral T f = b"
proof -
  let ?D = "\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)"
  have "((\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * f(g x) $ i) absolutely_integrable_on S \<and> integral S (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> * (f(g x) $ i)) = b $ i) \<longleftrightarrow>
        ((\<lambda>x. f x $ i) absolutely_integrable_on T \<and> integral T (\<lambda>x. f x $ i) = b $ i)" for i
    by (rule cov_invertible_real [OF der_g der_h hg gh id])
  then have "?D absolutely_integrable_on S \<and> (?D has_integral b) S \<longleftrightarrow>
        f absolutely_integrable_on T \<and> (f has_integral b) T"
    unfolding absolutely_integrable_componentwise_iff [where f=f] has_integral_componentwise_iff [of f]
              absolutely_integrable_componentwise_iff [where f="?D"] has_integral_componentwise_iff [of ?D]
    by (auto simp: all_conj_distrib Basis_vec_def cart_eq_inner_axis [symmetric]
           has_integral_iff set_lebesgue_integral_eq_integral)
  then show ?thesis
    using absolutely_integrable_on_def by blast
qed


lemma cv_inv_version4:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S) \<and> invertible(matrix(g' x))"
    and hg: "\<And>x. x \<in> S \<Longrightarrow> continuous_on (g ` S) h \<and> h(g x) = x"
  shows "(\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
             integral S (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b
         \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  have "\<forall>x. \<exists>h'. x \<in> S
           \<longrightarrow> (g has_derivative g' x) (at x within S) \<and> linear h' \<and> g' x \<circ> h' = id \<and> h' \<circ> g' x = id"
    using der_g matrix_invertible has_derivative_linear by blast
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
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and hg: "\<And>x. x \<in> S \<Longrightarrow> h(g x) = x"
      and conth: "continuous_on (g ` S) h"
  shows "(\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and> integral S (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b \<longleftrightarrow>
         f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
    (is "?lhs = ?rhs")
proof -
  let ?S = "{x \<in> S. invertible (matrix (g' x))}" and ?D = "\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)"
  have *: "?D absolutely_integrable_on ?S \<and> integral ?S ?D = b
           \<longleftrightarrow> f absolutely_integrable_on (g ` ?S) \<and> integral (g ` ?S) f = b"
  proof (rule cv_inv_version4)
    show "(g has_derivative g' x) (at x within ?S) \<and> invertible (matrix (g' x))"
      if "x \<in> ?S" for x
      using der_g that has_derivative_subset that by fastforce
    show "continuous_on (g ` ?S) h \<and> h (g x) = x"
      if "x \<in> ?S" for x
      using that continuous_on_subset [OF conth]  by (simp add: hg image_mono)
  qed
  have "(g has_derivative g' x) (at x within {x \<in> S. rank (matrix (g' x)) < CARD('m)})" if "x \<in> S" for x
    by (metis (no_types, lifting) der_g has_derivative_subset mem_Collect_eq subsetI that)
  then have "negligible (g ` {x \<in> S. \<not> invertible (matrix (g' x))})"
    by (auto simp: invertible_det_nz det_eq_0_rank intro: baby_Sard)
  then have neg: "negligible {x \<in> g ` S. x \<notin> g ` ?S \<and> f x \<noteq> 0}"
    by (auto intro: negligible_subset)
  have [simp]: "{x \<in> g ` ?S. x \<notin> g ` S \<and> f x \<noteq> 0} = {}"
    by auto
  have "?D absolutely_integrable_on ?S \<and> integral ?S ?D = b
    \<longleftrightarrow> ?D absolutely_integrable_on S \<and> integral S ?D = b"
    apply (intro conj_cong absolutely_integrable_spike_set_eq)
      apply(auto simp: integral_spike_set invertible_det_nz empty_imp_negligible neg)
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
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "compact S"
      and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and inj: "inj_on g S"
  shows "((\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
             integral S (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b
      \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b)"
proof -
  obtain h where hg: "\<And>x. x \<in> S \<Longrightarrow> h(g x) = x"
    using inj by (metis the_inv_into_f_f)
  have conth: "continuous_on (g ` S) h"
    by (metis \<open>compact S\<close> continuous_on_inv der_g has_derivative_continuous_on hg)
  show ?thesis
    by (rule has_absolute_integral_change_of_variables_invertible [OF der_g hg conth])
qed


lemma has_absolute_integral_change_of_variables_compact_family:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes compact: "\<And>n::nat. compact (F n)"
      and der_g: "\<And>x. x \<in> (\<Union>n. F n) \<Longrightarrow> (g has_derivative g' x) (at x within (\<Union>n. F n))"
      and inj: "inj_on g (\<Union>n. F n)"
  shows "((\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on (\<Union>n. F n) \<and>
             integral (\<Union>n. F n) (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b
      \<longleftrightarrow> f absolutely_integrable_on (g ` (\<Union>n. F n)) \<and> integral (g ` (\<Union>n. F n)) f = b)"
proof -
  let ?D = "\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f (g x)"
  let ?U = "\<lambda>n. \<Union>m\<le>n. F m"
  let ?lift = "vec::real\<Rightarrow>real^1"
  have F_leb: "F m \<in> sets lebesgue" for m
    by (simp add: compact borel_compact)
  have iff: "(\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f (g x)) absolutely_integrable_on (?U n) \<and>
             integral (?U n) (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f (g x)) = b
         \<longleftrightarrow> f absolutely_integrable_on (g ` (?U n)) \<and> integral (g ` (?U n)) f = b" for n b and f :: "real^'m::_ \<Rightarrow> real^'k"
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
      using integral_countable_UN [OF DS F_leb] by auto
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
            using iff [of n "vec \<circ> norm \<circ> f" "integral (?U n) (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R (?lift \<circ> norm \<circ> f) (g x))"]
            unfolding absolutely_integrable_on_1_iff integral_on_1_eq by (auto simp: o_def)
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
      proof (rule integral_countable_UN [OF fai])
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
      using integral_countable_UN [OF fs gF_leb] by auto
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
            using iff [of n "?lift \<circ> norm \<circ> f" "integral (g ` ?U n) (?lift \<circ> norm \<circ> f)"]
            unfolding absolutely_integrable_on_1_iff integral_on_1_eq image_UN by (auto simp: o_def)
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
        unfolding D_int [symmetric] by (rule integral_countable_UN [OF Dai F_leb])
    qed (use fgU in metis)
  qed
qed


theorem has_absolute_integral_change_of_variables:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  obtain C N where "fsigma C" and N: "N \<in> null_sets lebesgue" and CNS: "C \<union> N = S" and "disjnt C N"
    using lebesgue_set_almost_fsigma [OF S] .
  then obtain F :: "nat \<Rightarrow> (real^'m::_) set"
    where F: "range F \<subseteq> Collect compact" and Ceq: "C = Union(range F)"
    using fsigma_Union_compact by metis
  have "negligible N"
    using N by (simp add: negligible_iff_null_sets)
  let ?D = "\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f (g x)"
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
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "S \<in> sets lebesgue"
    and "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and "inj_on g S"
  shows "f absolutely_integrable_on (g ` S)
     \<longleftrightarrow> (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S"
  using assms has_absolute_integral_change_of_variables by blast

corollary integral_change_of_variables:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
    and disj: "(f absolutely_integrable_on (g ` S) \<or>
        (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S)"
  shows "integral (g ` S) f = integral S (\<lambda>x. \<bar>matrix_det (matrix (g' x))\<bar> *\<^sub>R f(g x))"
  using has_absolute_integral_change_of_variables [OF S der_g inj] disj
  by blast

lemma has_absolute_integral_change_of_variables_1:
  fixes f :: "real \<Rightarrow> real^'n::{finite,wellorder}" and g :: "real \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_vector_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  let ?lift = "vec :: real \<Rightarrow> real^1"
  let ?drop = "(\<lambda>x::real^1. x $ 1)"
  have S': "?lift ` S \<in> sets lebesgue"
    by (auto intro: differentiable_image_in_sets_lebesgue [OF S] differentiable_vec)
  have "((\<lambda>x. vec (g (x $ 1))) has_derivative (*\<^sub>R) (g' z)) (at (vec z) within ?lift ` S)"
    if "z \<in> S" for z
    using der_g [OF that]
    by (simp add: has_vector_derivative_def has_derivative_vector_1)
  then have der': "\<And>x. x \<in> ?lift ` S \<Longrightarrow>
        (?lift \<circ> g \<circ> ?drop has_derivative (*\<^sub>R) (g' (?drop x))) (at x within ?lift ` S)"
    by (auto simp: o_def)
  have inj': "inj_on (vec \<circ> g \<circ> ?drop) (vec ` S)"
    using inj by (simp add: inj_on_def)
  let ?fg = "\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)"
  have "((\<lambda>x. ?fg x $ i) absolutely_integrable_on S \<and> ((\<lambda>x. ?fg x $ i) has_integral b $ i) S
    \<longleftrightarrow> (\<lambda>x. f x $ i) absolutely_integrable_on g ` S \<and> ((\<lambda>x. f x $ i) has_integral b $ i) (g ` S))" for i
    using has_absolute_integral_change_of_variables [OF S' der' inj', of "\<lambda>x. ?lift(f (?drop x) $ i)" "?lift (b$i)"]
    unfolding integrable_on_1_iff integral_on_1_eq absolutely_integrable_on_1_iff absolutely_integrable_drop absolutely_integrable_on_def
    by (auto simp: image_comp o_def integral_vec1_eq has_integral_iff)
  then have "?fg absolutely_integrable_on S \<and> (?fg has_integral b) S
         \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> (f has_integral b) (g ` S)"
    unfolding has_integral_componentwise_iff [where y=b]
           absolutely_integrable_componentwise_iff [where f=f]
           absolutely_integrable_componentwise_iff [where f = ?fg]
    by (force simp: Basis_vec_def cart_eq_inner_axis)
  then show ?thesis
    using absolutely_integrable_on_def by blast
qed

corollary absolutely_integrable_change_of_variables_1:
  fixes f :: "real \<Rightarrow> real^'n::{finite,wellorder}" and g :: "real \<Rightarrow> real"
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
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "linear g"
  shows "(\<lambda>x. \<bar>matrix_det (matrix g)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>matrix_det (matrix g)\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof (cases "matrix_det(matrix g) = 0")
  case True
  then have "negligible(g ` S)"
    using assms det_nz_iff_inj negligible_linear_singular_image by blast
  with True show ?thesis
    by (auto simp: absolutely_integrable_on_def integrable_negligible integral_negligible)
next
  case False
  then obtain h where h: "\<And>x. x \<in> S \<Longrightarrow> h (g x) = x" "linear h"
    using assms det_nz_iff_inj linear_injective_isomorphism by metis
  show ?thesis
  proof (rule has_absolute_integral_change_of_variables_invertible)
    show "(g has_derivative g) (at x within S)" for x
      by (simp add: assms linear_imp_has_derivative)
    show "continuous_on (g ` S) h"
      using continuous_on_eq_continuous_within has_derivative_continuous linear_imp_has_derivative h by blast
  qed (use h in auto)
qed

lemma absolutely_integrable_change_of_variables_linear:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "linear g"
  shows "(\<lambda>x. \<bar>matrix_det (matrix g)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S
     \<longleftrightarrow> f absolutely_integrable_on (g ` S)"
  using assms has_absolute_integral_change_of_variables_linear by blast

lemma absolutely_integrable_on_linear_image:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "linear g"
  shows "f absolutely_integrable_on (g ` S)
     \<longleftrightarrow> (f \<circ> g) absolutely_integrable_on S \<or> matrix_det(matrix g) = 0"
  unfolding assms absolutely_integrable_change_of_variables_linear [OF assms, symmetric] absolutely_integrable_on_scaleR_iff
  by (auto simp: set_integrable_def)

lemma integral_change_of_variables_linear:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "linear g"
      and "f absolutely_integrable_on (g ` S) \<or> (f \<circ> g) absolutely_integrable_on S"
    shows "integral (g ` S) f = \<bar>matrix_det (matrix g)\<bar> *\<^sub>R integral S (f \<circ> g)"
proof -
  have "((\<lambda>x. \<bar>matrix_det (matrix g)\<bar> *\<^sub>R f (g x)) absolutely_integrable_on S) \<or> (f absolutely_integrable_on g ` S)"
    using absolutely_integrable_on_linear_image assms by blast
  moreover
  have ?thesis if "((\<lambda>x. \<bar>matrix_det (matrix g)\<bar> *\<^sub>R f (g x)) absolutely_integrable_on S)" "(f absolutely_integrable_on g ` S)"
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
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes "S \<in> sets lebesgue"
      and "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
      and "inj_on f S"
  shows "f ` S \<in> lmeasurable \<and> measure lebesgue (f ` S) = m
     \<longleftrightarrow> ((\<lambda>x. \<bar>matrix_det (matrix (f' x))\<bar>) has_integral m) S"
  using has_absolute_integral_change_of_variables [OF assms, of "\<lambda>x. (1::real^1)" "vec m"]
  unfolding absolutely_integrable_on_1_iff integral_on_1_eq integrable_on_1_iff absolutely_integrable_on_def
  by (auto simp: has_integral_iff lmeasurable_iff_integrable_on lmeasure_integral)

lemma measurable_differentiable_image_eq:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes "S \<in> sets lebesgue"
      and "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
      and "inj_on f S"
  shows "f ` S \<in> lmeasurable \<longleftrightarrow> (\<lambda>x. \<bar>matrix_det (matrix (f' x))\<bar>) integrable_on S"
  using has_measure_differentiable_image [OF assms]
  by blast

lemma measurable_differentiable_image_alt:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes "S \<in> sets lebesgue"
    and "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and "inj_on f S"
  shows "f ` S \<in> lmeasurable \<longleftrightarrow> (\<lambda>x. \<bar>matrix_det (matrix (f' x))\<bar>) absolutely_integrable_on S"
  using measurable_differentiable_image_eq [OF assms]
  by (simp only: absolutely_integrable_on_iff_nonneg)

lemma measure_differentiable_image_eq:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes S: "S \<in> sets lebesgue"
    and der_f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and inj: "inj_on f S"
    and intS: "(\<lambda>x. \<bar>matrix_det (matrix (f' x))\<bar>) integrable_on S"
  shows "measure lebesgue (f ` S) = integral S (\<lambda>x. \<bar>matrix_det (matrix (f' x))\<bar>)"
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
