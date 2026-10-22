theory Stokes_Oriented_Integration
  imports Stokes_Block_Determinant
begin

theorem oriented_integral_change_of_variables:
  fixes g :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
    and T :: "real ^ 'n \<Rightarrow> real"
  assumes measurable: "S \<in> sets lebesgue"
    and dg: "\<And>x. x \<in> S \<Longrightarrow> g differentiable (at x)"
    and inj: "inj_on g S"
    and positive: "\<And>x. x \<in> S \<Longrightarrow>
      0 < Determinants.det (jacobian g (at x))"
    and integrable: "T absolutely_integrable_on (g ` S)"
  shows "integral (g ` S) T =
    integral S (pull_top g T)"
proof -
  have der: "(g has_derivative frechet_derivative g (at x))
      (at x within S)" if "x \<in> S" for x
  proof -
    have "(g has_derivative frechet_derivative g (at x)) (at x)"
      using dg[OF that]
      by (simp add: frechet_derivative_works)
    then show ?thesis
      by (rule has_derivative_at_withinI)
  qed
  have det_eq: "eucl.det (frechet_derivative g (at x)) =
      Determinants.det (jacobian g (at x))"
    if "x \<in> S" for x
    using eucl_det_conv_matrix_det
      [OF linear_frechet_derivative[OF dg[OF that]]]
    by (simp add: jacobian_def)
  have cov: "integral (g ` S) T =
    integral S (\<lambda>x.
      \<bar>eucl.det (frechet_derivative g (at x))\<bar> *\<^sub>R T (g x))"
  proof (rule integral_change_of_variables
      [where f=T and g=g and g'="\<lambda>x. frechet_derivative g (at x)"
        and S=S])
    show "S \<in> sets lebesgue" by (rule measurable)
    show "\<And>x. x \<in> S \<Longrightarrow>
      (g has_derivative frechet_derivative g (at x)) (at x within S)"
      by (rule der)
    show "inj_on g S" by (rule inj)
    show "T absolutely_integrable_on (g ` S) \<or>
      (\<lambda>x. \<bar>eucl.det (frechet_derivative g (at x))\<bar> *\<^sub>R
        T (g x)) absolutely_integrable_on S"
      using integrable by blast
  qed
  have eq: "(\<lambda>x.
      \<bar>eucl.det (frechet_derivative g (at x))\<bar> *\<^sub>R T (g x)) x =
      pull_top g T x" if "x \<in> S" for x
    using positive[OF that] det_eq[OF that]
    by (simp add: pull_top_def)
  have int_eq: "integral S (\<lambda>x.
      \<bar>eucl.det (frechet_derivative g (at x))\<bar> *\<^sub>R T (g x)) =
      integral S (pull_top g T)"
    by (rule integral_cong) (use eq in auto)
  show ?thesis using cov int_eq by simp
qed

corollary oriented_chart_overlap_integral:
  fixes g :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
    and alpha beta :: "real ^ 'n \<Rightarrow> real"
  assumes measurable: "S \<in> sets lebesgue"
    and dg: "\<And>x. x \<in> S \<Longrightarrow> g differentiable (at x)"
    and inj: "inj_on g S"
    and positive: "\<And>x. x \<in> S \<Longrightarrow>
      0 < Determinants.det (jacobian g (at x))"
    and integrable: "beta absolutely_integrable_on (g ` S)"
    and compatible: "\<And>x. x \<in> S \<Longrightarrow>
      alpha x = pull_top g beta x"
  shows "integral S alpha = integral (g ` S) beta"
proof -
  have change: "integral (g ` S) beta =
    integral S (pull_top g beta)"
    by (rule oriented_integral_change_of_variables
      [OF measurable dg inj positive integrable])
  have "integral S alpha = integral S (pull_top g beta)"
    by (rule integral_cong) (use compatible in auto)
  with change show ?thesis by simp
qed

lemma integral_finite_partition:
  fixes T :: "'a::euclidean_space \<Rightarrow> real"
  assumes finite: "finite I"
    and partition: "\<And>x. x \<in> S \<Longrightarrow>
      (\<Sum>i\<in>I. rho i x) = 1"
    and integrable: "\<And>i. i \<in> I \<Longrightarrow>
      (\<lambda>x. rho i x * T x) integrable_on S"
  shows "integral S T =
    (\<Sum>i\<in>I. integral S (\<lambda>x. rho i x * T x))"
proof -
  have eq: "T x = (\<Sum>i\<in>I. rho i x * T x)"
    if "x \<in> S" for x
    using partition[OF that]
    by (simp add: sum_distrib_right[symmetric])
  have "integral S T =
      integral S (\<lambda>x. \<Sum>i\<in>I. rho i x * T x)"
    by (rule integral_cong) (use eq in auto)
  also have "\<dots> =
      (\<Sum>i\<in>I. integral S (\<lambda>x. rho i x * T x))"
    by (rule integral_sum[OF finite integrable])
  finally show ?thesis .
qed

lemma integral_common_refinement:
  fixes T :: "'a::euclidean_space \<Rightarrow> real"
    and rho :: "'i \<Rightarrow> 'a \<Rightarrow> real"
    and tau :: "'j \<Rightarrow> 'a \<Rightarrow> real"
  assumes finiteI: "finite I" and finiteJ: "finite J"
    and rho: "\<And>x. x \<in> S \<Longrightarrow>
      (\<Sum>i\<in>I. rho i x) = 1"
    and tau: "\<And>x. x \<in> S \<Longrightarrow>
      (\<Sum>j\<in>J. tau j x) = 1"
    and integrable: "\<And>i j. i \<in> I \<Longrightarrow>
      j \<in> J \<Longrightarrow>
      (\<lambda>x. rho i x * tau j x * T x) integrable_on S"
  shows "integral S T =
    (\<Sum>i\<in>I. \<Sum>j\<in>J.
      integral S (\<lambda>x. rho i x * tau j x * T x))"
proof -
  have partition: "(\<Sum>ij\<in>I \<times> J.
      rho (fst ij) x * tau (snd ij) x) = 1"
    if "x \<in> S" for x
  proof -
    have "(\<Sum>ij\<in>I \<times> J.
        rho (fst ij) x * tau (snd ij) x) =
      (\<Sum>i\<in>I. \<Sum>j\<in>J. rho i x * tau j x)"
      by (simp only: sum.cartesian_product, rule sum.cong)
         (auto split: prod.splits)
    also have "\<dots> =
      (\<Sum>i\<in>I. rho i x) * (\<Sum>j\<in>J. tau j x)"
      by (rule sum_product[symmetric])
    finally have "(\<Sum>ij\<in>I \<times> J.
        rho (fst ij) x * tau (snd ij) x) =
      (\<Sum>i\<in>I. rho i x) * (\<Sum>j\<in>J. tau j x)" .
    then show ?thesis
      by (simp add: rho[OF that] tau[OF that])
  qed
  have int: "\<And>ij. ij \<in> I \<times> J \<Longrightarrow>
    (\<lambda>x. (rho (fst ij) x * tau (snd ij) x) * T x)
      integrable_on S"
    using integrable by auto
  have "integral S T =
    (\<Sum>ij\<in>I \<times> J.
      integral S
        (\<lambda>x. (rho (fst ij) x * tau (snd ij) x) * T x))"
    by (rule integral_finite_partition
      [OF finite_cartesian_product[OF finiteI finiteJ]
        partition int])
  also have "\<dots> =
    (\<Sum>i\<in>I. \<Sum>j\<in>J.
      integral S (\<lambda>x. rho i x * tau j x * T x))"
    by (simp only: sum.cartesian_product, rule sum.cong)
       (auto split: prod.splits)
  finally show ?thesis .
qed

lemma absolutely_integrable_compact_support:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes compact: "compact K"
    and continuous: "continuous_on K f"
    and subset: "K \<subseteq> S"
    and zero: "\<And>x. x \<in> S \<Longrightarrow> x \<notin> K \<Longrightarrow> f x = 0"
  shows "f absolutely_integrable_on S"
proof -
  have bounded: "bounded (f ` K)"
    by (rule compact_imp_bounded)
       (rule compact_continuous_image[OF continuous compact])
  obtain B where B: "0 < B" "\<And>x. x \<in> K \<Longrightarrow> norm (f x) \<le> B"
    using bounded unfolding bounded_pos by auto
  have K_borel: "K \<in> sets borel"
    using compact by (auto intro: borel_closed compact_imp_closed)
  have K_measurable: "K \<in> lmeasurable"
    by (rule lmeasurable_compact[OF compact])
  have fm_borel: "(\<lambda>x. indicator K x *\<^sub>R f x)
      \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_on_indicator
      [OF K_borel continuous])
  have fm_lebesgue: "(\<lambda>x. indicator K x *\<^sub>R f x)
      \<in> borel_measurable lebesgue"
    using fm_borel by (simp add: measurable_completion)
  have intK: "f absolutely_integrable_on K"
  proof (rule set_integrable_bound
      [where f="\<lambda>_. B" and M=lebesgue and A=K])
    show "(\<lambda>_. B) absolutely_integrable_on K"
      using K_measurable by simp
    show "set_borel_measurable lebesgue K f"
      using fm_lebesgue by (simp add: set_borel_measurable_def)
    show "AE x in lebesgue.
      x \<in> K \<longrightarrow> norm (f x) \<le> norm ((\<lambda>_. B) x)"
      using B by (auto intro: always_eventually)
  qed
  have eq: "(\<lambda>x. indicator S x *\<^sub>R f x) =
    (\<lambda>x. indicator K x *\<^sub>R f x)"
  proof (rule ext)
    fix x
    show "indicator S x *\<^sub>R f x = indicator K x *\<^sub>R f x"
    proof (cases "x \<in> K")
      case True
      then have "x \<in> S"
        using subset by auto
      with True show ?thesis by simp
    next
      case False
      then show ?thesis
        using zero[of x] by (cases "x \<in> S") auto
    qed
  qed
  show ?thesis
    using intK unfolding set_integrable_def eq by simp
qed

end
