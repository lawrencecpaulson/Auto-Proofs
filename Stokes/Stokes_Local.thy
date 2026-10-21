theory Stokes_Local
  imports "HOL-Analysis.Interval_Integral"
    "HOL-Analysis.Topology_Euclidean_Space"
begin

text \<open>
  The normal-coordinate fundamental theorem of calculus is the analytic
  starting point for the local half-space Stokes theorem.  The first lemma
  records its slice form without choosing a tangential coordinate type.
\<close>

lemma normal_slice_FTC:
  fixes F f :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes ab: "a \<le> b"
    and deriv: "\<And>y t. y \<in> C \<Longrightarrow> t \<in> {a..b} \<Longrightarrow>
      ((\<lambda>s. F s y) has_vector_derivative f t y) (at t within {a..b})"
    and cont: "\<And>y. y \<in> C \<Longrightarrow> continuous_on {a..b} (\<lambda>t. f t y)"
  shows "\<And>y. y \<in> C \<Longrightarrow>
    (LINT t : {a..b} | lborel. f t y) = F b y - F a y"
proof -
  fix y assume y: "y \<in> C"
  show "(LINT t : {a..b} | lborel. f t y) = F b y - F a y"
    unfolding set_lebesgue_integral_def
    by (rule integral_FTC_atLeastAtMost[OF ab]) (use deriv[OF y] cont[OF y] in auto)
qed

text \<open>
  Fubini integrates the one-dimensional identity over tangential
  coordinates.  The integrability premise is separate from the slice
  regularity premises, so this lemma applies beyond rectangular boxes.
\<close>

lemma normal_slice_FTC_integral:
  fixes F f :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes ab: "a \<le> b"
    and deriv: "\<And>y t. y \<in> C \<Longrightarrow> t \<in> {a..b} \<Longrightarrow>
      ((\<lambda>s. F s y) has_vector_derivative f t y) (at t within {a..b})"
    and cont: "\<And>y. y \<in> C \<Longrightarrow> continuous_on {a..b} (\<lambda>t. f t y)"
    and int: "set_integrable lborel ({a..b} \<times> C) (case_prod f)"
  shows "(LINT p : {a..b} \<times> C | lborel. case_prod f p) =
    (LINT y : C | lborel. F b y - F a y)"
proof -
  let ?h = "\<lambda>(t,y). indicator ({a..b} \<times> C) (t,y) *\<^sub>R f t y"
  have intp: "integrable (lborel \<Otimes>\<^sub>M lborel) ?h"
    using int unfolding set_integrable_def by (simp add: lborel_prod split_def)
  have inner: "\<And>y. (\<integral>t. ?h (t,y) \<partial>lborel) =
      indicator C y *\<^sub>R (F b y - F a y)"
  proof -
    fix y
    show "(\<integral>t. ?h (t,y) \<partial>lborel) =
      indicator C y *\<^sub>R (F b y - F a y)"
    proof (cases "y \<in> C")
      case True
      have "(\<integral>t. ?h (t,y) \<partial>lborel) =
          (LINT t : {a..b} | lborel. f t y)"
        unfolding set_lebesgue_integral_def
        by (rule Bochner_Integration.integral_cong)
           (auto simp: indicator_def True)
      also have "\<dots> = F b y - F a y"
        by (rule normal_slice_FTC[OF ab deriv cont True])
      finally show ?thesis using True by simp
    next
      case False
      then show ?thesis by (simp add: indicator_def)
    qed
  qed
  have "(LINT p : {a..b} \<times> C | lborel. case_prod f p) =
      (\<integral>y. \<integral>t. ?h (t,y) \<partial>lborel \<partial>lborel)"
    using lborel_pair.integral_snd[OF intp]
    by (simp add: set_lebesgue_integral_def lborel_prod split_def)
  also have "\<dots> = (LINT y : C | lborel. F b y - F a y)"
    unfolding set_lebesgue_integral_def
    by (rule Bochner_Integration.integral_cong) (use inner in auto)
  finally show ?thesis .
qed

text \<open>
  The same argument can integrate in the second coordinate.  This
  version will make tangential derivatives disappear when both
  tangential face values vanish.
\<close>

lemma second_slice_FTC_integral:
  fixes F f :: "'a::euclidean_space \<Rightarrow> real \<Rightarrow> real"
  assumes ab: "a \<le> b"
    and deriv: "\<And>x t. x \<in> C \<Longrightarrow> t \<in> {a..b} \<Longrightarrow>
      ((\<lambda>s. F x s) has_vector_derivative f x t) (at t within {a..b})"
    and cont: "\<And>x. x \<in> C \<Longrightarrow> continuous_on {a..b} (f x)"
    and int: "set_integrable lborel (C \<times> {a..b}) (case_prod f)"
  shows "(LINT p : C \<times> {a..b} | lborel. case_prod f p) =
    (LINT x : C | lborel. F x b - F x a)"
proof -
  let ?h = "\<lambda>(x,t). indicator (C \<times> {a..b}) (x,t) *\<^sub>R f x t"
  have intp: "integrable (lborel \<Otimes>\<^sub>M lborel) ?h"
    using int unfolding set_integrable_def by (simp add: lborel_prod split_def)
  have inner: "\<And>x. (\<integral>t. ?h (x,t) \<partial>lborel) =
      indicator C x *\<^sub>R (F x b - F x a)"
  proof -
    fix x
    show "(\<integral>t. ?h (x,t) \<partial>lborel) =
      indicator C x *\<^sub>R (F x b - F x a)"
    proof (cases "x \<in> C")
      case True
      have "(\<integral>t. ?h (x,t) \<partial>lborel) =
          (LINT t : {a..b} | lborel. f x t)"
        unfolding set_lebesgue_integral_def
        by (rule Bochner_Integration.integral_cong)
           (auto simp: indicator_def True)
      also have "\<dots> = F x b - F x a"
        unfolding set_lebesgue_integral_def
        by (rule integral_FTC_atLeastAtMost[OF ab])
           (use deriv[OF True] cont[OF True] in auto)
      finally show ?thesis using True by simp
    next
      case False
      then show ?thesis by (simp add: indicator_def)
    qed
  qed
  have "(LINT p : C \<times> {a..b} | lborel. case_prod f p) =
      (\<integral>x. \<integral>t. ?h (x,t) \<partial>lborel \<partial>lborel)"
    using lborel_pair.integral_fst[OF intp]
    by (simp add: set_lebesgue_integral_def lborel_prod split_def)
  also have "\<dots> = (LINT x : C | lborel. F x b - F x a)"
    unfolding set_lebesgue_integral_def
    by (rule Bochner_Integration.integral_cong) (use inner in auto)
  finally show ?thesis .
qed

lemma second_slice_FTC_zero:
  fixes F f :: "'a::euclidean_space \<Rightarrow> real \<Rightarrow> real"
  assumes ab: "a \<le> b"
    and deriv: "\<And>x t. x \<in> C \<Longrightarrow> t \<in> {a..b} \<Longrightarrow>
      ((\<lambda>s. F x s) has_vector_derivative f x t) (at t within {a..b})"
    and cont: "\<And>x. x \<in> C \<Longrightarrow> continuous_on {a..b} (f x)"
    and int: "set_integrable lborel (C \<times> {a..b}) (case_prod f)"
    and faces_zero: "\<And>x. x \<in> C \<Longrightarrow> F x a = 0 \<and> F x b = 0"
  shows "(LINT p : C \<times> {a..b} | lborel. case_prod f p) = 0"
proof -
  have "(LINT p : C \<times> {a..b} | lborel. case_prod f p) =
      (LINT x : C | lborel. F x b - F x a)"
    by (rule second_slice_FTC_integral[OF ab deriv cont int])
  also have "\<dots> = 0"
  proof -
    have "(\<lambda>x. indicator C x *\<^sub>R (F x b - F x a)) = (\<lambda>x. 0)"
      by (rule ext) (auto simp: indicator_def faces_zero)
    then show ?thesis by (simp add: set_lebesgue_integral_def)
  qed
  finally show ?thesis .
qed

text \<open>
  For the orientation dt \<and> dy, a one-form P dt + Q dy would
  need a different coefficient order.  Here P multiplies dy and Q
  multiplies dt, so d(P dy + Q dt) has coefficient
  partial_t P - partial_y Q.
\<close>

theorem Stokes_box_2D:
  fixes P Q P_t Q_y :: "real \<Rightarrow> real \<Rightarrow> real"
  assumes ab: "a \<le> b" and cd: "c \<le> d"
    and deriv_P: "\<And>y t. y \<in> {c..d} \<Longrightarrow> t \<in> {a..b} \<Longrightarrow>
      ((\<lambda>s. P s y) has_vector_derivative P_t t y) (at t within {a..b})"
    and cont_P: "\<And>y. y \<in> {c..d} \<Longrightarrow> continuous_on {a..b} (\<lambda>t. P_t t y)"
    and int_P: "set_integrable lborel ({a..b} \<times> {c..d}) (case_prod P_t)"
    and deriv_Q: "\<And>t y. t \<in> {a..b} \<Longrightarrow> y \<in> {c..d} \<Longrightarrow>
      ((\<lambda>s. Q t s) has_vector_derivative Q_y t y) (at y within {c..d})"
    and cont_Q: "\<And>t. t \<in> {a..b} \<Longrightarrow> continuous_on {c..d} (Q_y t)"
    and int_Q: "set_integrable lborel ({a..b} \<times> {c..d}) (case_prod Q_y)"
  shows "(LINT p : {a..b} \<times> {c..d} | lborel.
      case_prod (\<lambda>t y. P_t t y - Q_y t y) p) =
    (LINT y : {c..d} | lborel. P b y - P a y) -
    (LINT t : {a..b} | lborel. Q t d - Q t c)"
proof -
  have split: "(LINT p : {a..b} \<times> {c..d} | lborel.
      case_prod (\<lambda>t y. P_t t y - Q_y t y) p) =
    (LINT p : {a..b} \<times> {c..d} | lborel. case_prod P_t p) -
    (LINT p : {a..b} \<times> {c..d} | lborel. case_prod Q_y p)"
    using int_P int_Q
    by (simp add: set_lebesgue_integral_def set_integrable_def
                  algebra_simps split_def)
  have normal: "(LINT p : {a..b} \<times> {c..d} | lborel. case_prod P_t p) =
      (LINT y : {c..d} | lborel. P b y - P a y)"
    by (rule normal_slice_FTC_integral[OF ab deriv_P cont_P int_P])
  have tangential: "(LINT p : {a..b} \<times> {c..d} | lborel. case_prod Q_y p) =
      (LINT t : {a..b} | lborel. Q t d - Q t c)"
    by (rule second_slice_FTC_integral[OF cd deriv_Q cont_Q int_Q])
  show ?thesis using split normal tangential by simp
qed

theorem Stokes_halfspace_2D:
  fixes P Q P_t Q_y :: "real \<Rightarrow> real \<Rightarrow> real"
  assumes R: "0 \<le> R" and cd: "c \<le> d"
    and deriv_P: "\<And>y t. y \<in> {c..d} \<Longrightarrow> t \<in> {0..R} \<Longrightarrow>
      ((\<lambda>s. P s y) has_vector_derivative P_t t y) (at t within {0..R})"
    and cont_P: "\<And>y. y \<in> {c..d} \<Longrightarrow> continuous_on {0..R} (\<lambda>t. P_t t y)"
    and int_P: "set_integrable lborel ({0..R} \<times> {c..d}) (case_prod P_t)"
    and deriv_Q: "\<And>t y. t \<in> {0..R} \<Longrightarrow> y \<in> {c..d} \<Longrightarrow>
      ((\<lambda>s. Q t s) has_vector_derivative Q_y t y) (at y within {c..d})"
    and cont_Q: "\<And>t. t \<in> {0..R} \<Longrightarrow> continuous_on {c..d} (Q_y t)"
    and int_Q: "set_integrable lborel ({0..R} \<times> {c..d}) (case_prod Q_y)"
    and upper_zero: "\<And>y. y \<in> {c..d} \<Longrightarrow> P R y = 0"
    and sides_zero: "\<And>t. t \<in> {0..R} \<Longrightarrow> Q t c = 0 \<and> Q t d = 0"
    and bulk_zero: "\<And>t y. 0 \<le> t \<Longrightarrow>
      (t,y) \<notin> {0..R} \<times> {c..d} \<Longrightarrow> P_t t y - Q_y t y = 0"
    and boundary_zero: "\<And>y. y \<notin> {c..d} \<Longrightarrow> P 0 y = 0"
  shows "(LINT p : {0..} \<times> UNIV | lborel.
      case_prod (\<lambda>t y. P_t t y - Q_y t y) p) =
    - (\<integral>y. P 0 y \<partial>lborel)"
proof -
  let ?g = "case_prod (\<lambda>t y. P_t t y - Q_y t y)"
  let ?H = "{0..} \<times> UNIV"
  let ?D = "{0..R} \<times> {c..d}"
  have DH: "?D \<subseteq> ?H" by auto
  have restrict: "(LINT p : {0..} \<times> UNIV | lborel. ?g p) =
      (LINT p : {0..R} \<times> {c..d} | lborel. ?g p)"
    unfolding set_lebesgue_integral_def
  proof (rule Bochner_Integration.integral_cong)
    show "lborel = lborel" ..
    fix p :: "real \<times> real" assume "p \<in> space lborel"
    show "indicator ?H p *\<^sub>R ?g p = indicator ?D p *\<^sub>R ?g p"
    proof (cases "p \<in> ?D")
      case True
      then have "p \<in> ?H" using DH by auto
      with True show ?thesis by (simp add: indicator_def)
    next
      case notD: False
      show ?thesis
      proof (cases "p \<in> ?H")
        case True
        obtain t y where p: "p = (t,y)" by (cases p) auto
        have "?g p = 0"
          using bulk_zero[of t y] True notD p by auto
        with notD show ?thesis by (simp add: indicator_def)
      next
        case False
        with notD show ?thesis by (simp add: indicator_def)
      qed
    qed
  qed
  have box: "(LINT p : {0..R} \<times> {c..d} | lborel. ?g p) =
      (LINT y : {c..d} | lborel. P R y - P 0 y) -
      (LINT t : {0..R} | lborel. Q t d - Q t c)"
    by (rule Stokes_box_2D[OF R cd deriv_P cont_P int_P
                               deriv_Q cont_Q int_Q])
  have normal: "(LINT y : {c..d} | lborel. P R y - P 0 y) =
      - (LINT y : {c..d} | lborel. P 0 y)"
  proof -
    have "(LINT y : {c..d} | lborel. P R y - P 0 y) =
        (LINT y : {c..d} | lborel. - P 0 y)"
      by (rule set_lebesgue_integral_cong) (auto simp: upper_zero)
    also have "\<dots> = - (LINT y : {c..d} | lborel. P 0 y)"
      by (simp add: set_lebesgue_integral_def algebra_simps)
    finally show ?thesis .
  qed
  have sides: "(LINT t : {0..R} | lborel. Q t d - Q t c) = 0"
  proof -
    have "(LINT t : {0..R} | lborel. Q t d - Q t c) =
        (LINT t : {0..R} | lborel. 0)"
      by (rule set_lebesgue_integral_cong) (auto simp: sides_zero)
    then show ?thesis by simp
  qed
  have boundary: "(LINT y : {c..d} | lborel. P 0 y) =
      (\<integral>y. P 0 y \<partial>lborel)"
    unfolding set_lebesgue_integral_def
    by (rule Bochner_Integration.integral_cong)
       (auto simp: indicator_def intro: boundary_zero)
  show ?thesis using restrict box normal sides boundary by simp
qed

text \<open>
  A rectangular support bound removes the upper normal face.  This is
  the normal-coordinate contribution to half-space Stokes; the
  tangential derivative contributions require a separate whole-space
  vanishing lemma.
\<close>

lemma normal_halfspace_FTC:
  fixes F f :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes R: "0 \<le> R"
    and deriv: "\<And>y t. y \<in> C \<Longrightarrow> t \<in> {0..R} \<Longrightarrow>
      ((\<lambda>s. F s y) has_vector_derivative f t y) (at t within {0..R})"
    and cont: "\<And>y. y \<in> C \<Longrightarrow> continuous_on {0..R} (\<lambda>t. f t y)"
    and int: "set_integrable lborel ({0..R} \<times> C) (case_prod f)"
    and end_zero: "\<And>y. y \<in> C \<Longrightarrow> F R y = 0"
    and tail_zero: "\<And>t y. R < t \<Longrightarrow> y \<in> C \<Longrightarrow> f t y = 0"
  shows "(LINT p : {0..} \<times> C | lborel. case_prod f p) =
    - (LINT y : C | lborel. F 0 y)"
proof -
  have restrict: "(LINT p : {0..} \<times> C | lborel. case_prod f p) =
      (LINT p : {0..R} \<times> C | lborel. case_prod f p)"
    unfolding set_lebesgue_integral_def
    by (rule Bochner_Integration.integral_cong)
       (auto simp: indicator_def tail_zero split: prod.splits if_splits)
  also have "\<dots> = (LINT y : C | lborel. F R y - F 0 y)"
    by (rule normal_slice_FTC_integral[OF R deriv cont int])
  also have "\<dots> = - (LINT y : C | lborel. F 0 y)"
    unfolding set_lebesgue_integral_def
    by (subst Bochner_Integration.integral_minus[symmetric])
       (rule Bochner_Integration.integral_cong;
        auto simp: indicator_def end_zero)
  finally show ?thesis .
qed

lemma compact_halfspace_support_bound:
  fixes F :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes support: "compact (closure
    {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod F p \<noteq> 0})"
  obtains R where "0 < R"
    and "\<And>t y. R \<le> t \<Longrightarrow> F t y = 0"
    and "\<And>t y. 0 \<le> t \<Longrightarrow> y \<notin> ball 0 R \<Longrightarrow> F t y = 0"
proof -
  let ?S = "{p::real \<times> 'a. 0 \<le> fst p \<and> case_prod F p \<noteq> 0}"
  have bounded: "bounded (closure ?S)"
    by (rule compact_imp_bounded[OF support])
  obtain R where R: "0 < R" and bound: "closure ?S \<subseteq> ball 0 R"
    using bounded_subset_ballD[OF bounded, of 0] by auto
  have inside: "\<And>t y. 0 \<le> t \<Longrightarrow> F t y \<noteq> 0 \<Longrightarrow>
      norm (t,y) < R"
  proof -
    fix t :: real and y :: 'a
    assume t: "0 \<le> t" and nz: "F t y \<noteq> 0"
    have "(t,y) \<in> ?S" using t nz by simp
    then have "(t,y) \<in> closure ?S"
      using closure_subset[of ?S] by auto
    then have "(t,y) \<in> ball 0 R" using bound by auto
    then show "norm (t,y) < R" by simp
  qed
  have upper: "\<And>t y. R \<le> t \<Longrightarrow> F t y = 0"
  proof -
    fix t :: real and y :: 'a
    assume rt: "R \<le> t"
    show "F t y = 0"
    proof (rule ccontr)
      assume nz: "F t y \<noteq> 0"
      have "norm (t,y) < R" by (rule inside[OF _ nz]) (use R rt in auto)
      moreover have "R \<le> norm (t,y)"
        using norm_fst_le[of t y] R rt by auto
      ultimately show False by simp
    qed
  qed
  have side: "\<And>t y. 0 \<le> t \<Longrightarrow> y \<notin> ball 0 R \<Longrightarrow> F t y = 0"
  proof -
    fix t :: real and y :: 'a
    assume t: "0 \<le> t" and out: "y \<notin> ball 0 R"
    show "F t y = 0"
    proof (rule ccontr)
      assume nz: "F t y \<noteq> 0"
      have "norm (t,y) < R" by (rule inside[OF t nz])
      moreover have "R \<le> norm (t,y)"
        using out norm_snd_le[of y t] by auto
      ultimately show False by simp
    qed
  qed
  show thesis by (rule that[OF R upper side])
qed

text \<open>
  In dimension one the lower half-space face has sign minus.  The
  derivative is assumed to vanish past the right end of a box, as it
  will when the original coefficient has compact support there.
\<close>

lemma halfline_FTC_compact:
  fixes F f :: "real \<Rightarrow> real"
  assumes R: "0 \<le> R"
    and deriv: "\<And>t. t \<in> {0..R} \<Longrightarrow>
      (F has_vector_derivative f t) (at t within {0..R})"
    and cont: "continuous_on {0..R} f"
    and end_zero: "F R = 0"
    and tail_zero: "\<And>t. R < t \<Longrightarrow> f t = 0"
  shows "(LINT t : {0..} | lborel. f t) = - F 0"
proof -
  have restrict: "(LINT t : {0..} | lborel. f t) =
      (LINT t : {0..R} | lborel. f t)"
    unfolding set_lebesgue_integral_def
    by (rule Bochner_Integration.integral_cong)
       (auto simp: indicator_def tail_zero split: if_splits)
  also have "\<dots> = F R - F 0"
    unfolding set_lebesgue_integral_def
    by (rule integral_FTC_atLeastAtMost[OF R])
       (use deriv cont in auto)
  also have "\<dots> = - F 0"
    by (simp add: end_zero)
  finally show ?thesis .
qed

lemma vector_derivative_zero_on_real_tail:
  fixes F :: "real \<Rightarrow> real"
  assumes deriv: "(F has_vector_derivative f) (at t)"
    and rt: "R < t"
    and zero: "\<And>s. R < s \<Longrightarrow> F s = 0"
  shows "f = 0"
proof -
  have const: "((\<lambda>s::real. 0::real) has_vector_derivative 0) (at t)"
    by (rule has_vector_derivative_const)
  have zero_deriv: "(F has_vector_derivative 0) (at t)"
    by (rule has_vector_derivative_transform_within_open
        [OF const, where S="{R<..}"])
       (use rt zero in auto)
  show ?thesis
    by (rule vector_derivative_unique_at[OF deriv zero_deriv])
qed

lemma vector_derivative_zero_off_closed_interval:
  fixes F :: "real \<Rightarrow> real"
  assumes deriv: "(F has_vector_derivative f) (at t)"
    and out: "t \<notin> {a..b}"
    and zero: "\<And>s. s \<notin> {a..b} \<Longrightarrow> F s = 0"
  shows "f = 0"
proof -
  have const: "((\<lambda>s::real. 0::real) has_vector_derivative 0) (at t)"
    by (rule has_vector_derivative_const)
  have zero_deriv: "(F has_vector_derivative 0) (at t)"
    by (rule has_vector_derivative_transform_within_open
        [OF const, where S="- {a..b}"])
       (use out zero in auto)
  show ?thesis
    by (rule vector_derivative_unique_at[OF deriv zero_deriv])
qed

lemma vector_derivative_zero_on_nonnegative:
  fixes F :: "real \<Rightarrow> real"
  assumes deriv: "(F has_vector_derivative f) (at t)"
    and t: "0 \<le> t"
    and zero: "\<And>s. 0 \<le> s \<Longrightarrow> F s = 0"
  shows "f = 0"
proof (cases "t = 0")
  case False
  then have pos: "0 < t" using t by simp
  show ?thesis
    by (rule vector_derivative_zero_on_real_tail[OF deriv pos])
       (use zero in auto)
next
  case True
  have DA: "(F has_vector_derivative f) (at 0)"
    using deriv True by simp
  have D: "(F has_vector_derivative f) (at 0 within {0..})"
    by (rule has_vector_derivative_at_within[OF DA])
  have D0: "((\<lambda>s::real. 0::real) has_vector_derivative 0) (at 0 within {0..})"
    by (rule has_vector_derivative_at_within)
       (rule has_vector_derivative_const)
  have Z: "(F has_vector_derivative 0) (at 0 within {0..})"
    by (rule has_vector_derivative_transform
        [where f="\<lambda>s::real. 0" and g=F and S="{0..}" and x=0,
         OF _ _ D0])
       (use zero in auto)
  have ne: "at (0::real) within {0..} \<noteq> bot"
  proof -
    have eq: "{0..} - {0::real} = {0<..}" by auto
    show ?thesis by (simp add: at_within_eq_bot_iff eq)
  qed
  show ?thesis
    by (rule vector_derivative_unique_within[OF ne D Z])
qed

lemma vector_derivative_zero_if_function_zero:
  fixes F :: "real \<Rightarrow> real"
  assumes deriv: "(F has_vector_derivative f) (at t)"
    and zero: "\<And>s. F s = 0"
  shows "f = 0"
proof -
  have eq: "F = (\<lambda>s. 0)" using zero by auto
  have "(F has_vector_derivative 0) (at t)"
    by (simp add: eq has_vector_derivative_const)
  show ?thesis
    by (rule vector_derivative_unique_at[OF deriv \<open>(F has_vector_derivative 0) (at t)\<close>])
qed

corollary halfline_FTC_from_coefficient_support:
  fixes F f :: "real \<Rightarrow> real"
  assumes R: "0 \<le> R"
    and deriv_box: "\<And>t. t \<in> {0..R} \<Longrightarrow>
      (F has_vector_derivative f t) (at t within {0..R})"
    and cont: "continuous_on {0..R} f"
    and coeff_zero: "\<And>t. R \<le> t \<Longrightarrow> F t = 0"
    and deriv_tail: "\<And>t. R < t \<Longrightarrow> (F has_vector_derivative f t) (at t)"
  shows "(LINT t : {0..} | lborel. f t) = - F 0"
proof (rule halfline_FTC_compact[OF R deriv_box cont])
  show "F R = 0" using coeff_zero by simp
  show "\<And>t. R < t \<Longrightarrow> f t = 0"
  proof -
    fix t assume t: "R < t"
    show "f t = 0"
      by (rule vector_derivative_zero_on_real_tail[OF deriv_tail[OF t] t])
         (use coeff_zero in auto)
  qed
qed

corollary halfline_FTC_compact_support:
  fixes F f :: "real \<Rightarrow> real"
  assumes deriv: "\<And>t. 0 \<le> t \<Longrightarrow> (F has_vector_derivative f t) (at t)"
    and cont: "continuous_on {0..} f"
    and support: "compact (closure {t. 0 \<le> t \<and> F t \<noteq> 0})"
  shows "(LINT t : {0..} | lborel. f t) = - F 0"
proof -
  let ?S = "{t. 0 \<le> t \<and> F t \<noteq> 0}"
  have bounded: "bounded (closure ?S)"
    by (rule compact_imp_bounded[OF support])
  obtain R where R: "0 < R" and bound: "closure ?S \<subseteq> ball 0 R"
    using bounded_subset_ballD[OF bounded, of 0] by auto
  have coeff_zero: "\<And>t. R \<le> t \<Longrightarrow> F t = 0"
  proof -
    fix t assume rt: "R \<le> t"
    show "F t = 0"
    proof (rule ccontr)
      assume "F t \<noteq> 0"
      then have "t \<in> ?S" using R rt by auto
      then have "t \<in> closure ?S"
        using closure_subset[of ?S] by auto
      then have "t \<in> ball 0 R" using bound by auto
      with rt show False by (simp add: dist_real_def)
    qed
  qed
  have deriv_box: "\<And>t. t \<in> {0..R} \<Longrightarrow>
      (F has_vector_derivative f t) (at t within {0..R})"
    using deriv by (auto intro: has_vector_derivative_at_within)
  have cont_box: "continuous_on {0..R} f"
    by (rule continuous_on_subset[OF cont]) auto
  have deriv_tail: "\<And>t. R < t \<Longrightarrow> (F has_vector_derivative f t) (at t)"
    using deriv R by auto
  show ?thesis
    by (rule halfline_FTC_from_coefficient_support
        [OF less_imp_le[OF R] deriv_box cont_box coeff_zero deriv_tail])
qed

theorem normal_halfspace_FTC_compact_support:
  fixes F f :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes support: "compact (closure
    {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod F p \<noteq> 0})"
    and deriv: "\<And>t y. 0 \<le> t \<Longrightarrow>
      ((\<lambda>s. F s y) has_vector_derivative f t y) (at t)"
    and cont: "\<And>y. continuous_on {0..} (\<lambda>t. f t y)"
    and int: "set_integrable lborel ({0..} \<times> UNIV) (case_prod f)"
  shows "(LINT p : {0..} \<times> UNIV | lborel. case_prod f p) =
    - (\<integral>y. F 0 y \<partial>lborel)"
proof -
  have ex: "\<exists>R. 0 < R \<and> (\<forall>t y. R \<le> t \<longrightarrow> F t y = 0)"
  proof (rule compact_halfspace_support_bound[OF support])
    fix R assume R: "0 < R"
      and upper: "\<And>t y. R \<le> t \<Longrightarrow> F t y = 0"
      and side: "\<And>t y. 0 \<le> t \<Longrightarrow> y \<notin> ball 0 R \<Longrightarrow> F t y = 0"
    show ?thesis
      by (rule exI[where x=R]) (use R upper in auto)
  qed
  then obtain R where R: "0 < R" and upper: "\<And>t y. R \<le> t \<Longrightarrow> F t y = 0"
    by auto
  have deriv_box: "\<And>y t. y \<in> UNIV \<Longrightarrow> t \<in> {0..R} \<Longrightarrow>
      ((\<lambda>s. F s y) has_vector_derivative f t y) (at t within {0..R})"
    using deriv by (auto intro: has_vector_derivative_at_within)
  have cont_box: "\<And>y. y \<in> UNIV \<Longrightarrow> continuous_on {0..R} (\<lambda>t. f t y)"
    by (rule continuous_on_subset[OF cont]) auto
  have int_box: "set_integrable lborel ({0..R} \<times> UNIV) (case_prod f)"
    by (rule set_integrable_subset[OF int]) (auto intro: borel_Times)
  have end_zero: "\<And>y. y \<in> UNIV \<Longrightarrow> F R y = 0"
    using upper by simp
  have tail_zero: "\<And>t y. R < t \<Longrightarrow> y \<in> UNIV \<Longrightarrow> f t y = 0"
  proof -
    fix t :: real and y :: 'a
    assume rt: "R < t" and "y \<in> UNIV"
    have D: "((\<lambda>s. F s y) has_vector_derivative f t y) (at t)"
      by (rule deriv) (use R rt in auto)
    show "f t y = 0"
      by (rule vector_derivative_zero_on_real_tail[OF D rt])
         (use upper in auto)
  qed
  have "(LINT p : {0..} \<times> UNIV | lborel. case_prod f p) =
    - (LINT y : UNIV | lborel. F 0 y)"
    by (rule normal_halfspace_FTC[OF less_imp_le[OF R]
      deriv_box cont_box int_box end_zero tail_zero])
  then show ?thesis by (simp add: set_lebesgue_integral_def)
qed

lemma set_lebesgue_integral_restrict_support:
  fixes f :: "'a \<Rightarrow> real"
  assumes subset: "S \<subseteq> T"
    and zero: "\<And>x. x \<in> T \<Longrightarrow> x \<notin> S \<Longrightarrow> f x = 0"
  shows "(LINT x : T | M. f x) = (LINT x : S | M. f x)"
  unfolding set_lebesgue_integral_def
proof (rule Bochner_Integration.integral_cong)
  show "M = M" ..
  fix x assume "x \<in> space M"
  show "indicator T x *\<^sub>R f x = indicator S x *\<^sub>R f x"
    using subset zero[of x] by (cases "x \<in> S") (auto simp: indicator_def)
qed

lemma set_integrable_continuous_compact_support:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes compact: "compact D"
    and sub: "D \<subseteq> H"
    and cont: "continuous_on D f"
    and zero: "\<And>x. x \<in> H \<Longrightarrow> x \<notin> D \<Longrightarrow> f x = 0"
  shows "set_integrable lborel H f"
proof -
  have intD: "set_integrable lborel D f"
    using borel_integrable_compact[OF compact cont]
    by (simp add: set_integrable_def)
  have eq: "(\<lambda>x. indicator H x *\<^sub>R f x) =
      (\<lambda>x. indicator D x *\<^sub>R f x)"
  proof (rule ext)
    fix x
    show "indicator H x *\<^sub>R f x = indicator D x *\<^sub>R f x"
    proof (cases "x \<in> D")
      case True
      then have "x \<in> H" using sub by auto
      with True show ?thesis by (simp add: indicator_def)
    next
      case notD: False
      show ?thesis
      proof (cases "x \<in> H")
        case True
        then have "f x = 0" by (rule zero[OF _ notD])
        with notD show ?thesis by (simp add: indicator_def)
      next
        case False
        with notD show ?thesis by (simp add: indicator_def)
      qed
    qed
  qed
  show ?thesis using intD eq by (simp add: set_integrable_def)
qed

lemma normal_halfspace_derivative_integrable:
  fixes F f :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes support: "compact (closure
    {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod F p \<noteq> 0})"
    and deriv: "\<And>t y. 0 \<le> t \<Longrightarrow>
      ((\<lambda>s. F s y) has_vector_derivative f t y) (at t)"
    and cont: "continuous_on ({0..} \<times> UNIV) (case_prod f)"
  shows "set_integrable lborel ({0..} \<times> UNIV) (case_prod f)"
proof -
  have ex: "\<exists>R. 0 < R \<and> (\<forall>t y. R \<le> t \<longrightarrow> F t y = 0) \<and>
    (\<forall>t y. 0 \<le> t \<longrightarrow> y \<notin> ball 0 R \<longrightarrow> F t y = 0)"
  proof (rule compact_halfspace_support_bound[OF support])
    fix R assume R: "0 < R"
      and upper: "\<And>t y. R \<le> t \<Longrightarrow> F t y = 0"
      and side: "\<And>t y. 0 \<le> t \<Longrightarrow> y \<notin> ball 0 R \<Longrightarrow> F t y = 0"
    show ?thesis
      by (rule exI[where x=R]) (use R upper side in auto)
  qed
  then obtain R where R: "0 < R"
    and upper: "\<And>t y. R \<le> t \<Longrightarrow> F t y = 0"
    and side: "\<And>t y. 0 \<le> t \<Longrightarrow> y \<notin> ball 0 R \<Longrightarrow> F t y = 0"
    by auto
  let ?D = "{0..R} \<times> cball (0::'a) R"
  let ?H = "({0..}::real set) \<times> (UNIV::'a set)"
  have compactD: "compact ?D"
    by (intro compact_Times compact_Icc compact_cball)
  have DH: "?D \<subseteq> ?H" by auto
  have contD: "continuous_on ?D (case_prod f)"
    by (rule continuous_on_subset[OF cont DH])
  have zero: "\<And>p. p \<in> ?H \<Longrightarrow> p \<notin> ?D \<Longrightarrow> case_prod f p = 0"
  proof -
    fix p :: "real \<times> 'a"
    assume H: "p \<in> ?H" and out: "p \<notin> ?D"
    obtain t y where p: "p = (t,y)" by (cases p) auto
    have t: "0 \<le> t" using H p by auto
    show "case_prod f p = 0"
    proof (cases "R < t")
      case True
      have D: "((\<lambda>s. F s y) has_vector_derivative f t y) (at t)"
        by (rule deriv[OF t])
      have "f t y = 0"
        by (rule vector_derivative_zero_on_real_tail[OF D True])
           (use upper in auto)
      then show ?thesis by (simp add: p)
    next
      case False
      then have outY: "y \<notin> cball 0 R" using out p t by auto
      have notball: "y \<notin> ball 0 R" using outY by auto
      have D: "((\<lambda>s. F s y) has_vector_derivative f t y) (at t)"
        by (rule deriv[OF t])
      have zeroF: "\<And>s. 0 \<le> s \<Longrightarrow> F s y = 0"
        using side[OF _ notball] by auto
      have "f t y = 0"
        by (rule vector_derivative_zero_on_nonnegative[OF D t zeroF])
      then show ?thesis by (simp add: p)
    qed
  qed
  show ?thesis
    by (rule set_integrable_continuous_compact_support
        [OF compactD DH contD zero])
qed

theorem normal_halfspace_FTC_C1:
  fixes F f :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes support: "compact (closure
    {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod F p \<noteq> 0})"
    and deriv: "\<And>t y. 0 \<le> t \<Longrightarrow>
      ((\<lambda>s. F s y) has_vector_derivative f t y) (at t)"
    and cont: "continuous_on ({0..} \<times> UNIV) (case_prod f)"
  shows "(LINT p : {0..} \<times> UNIV | lborel. case_prod f p) =
    - (\<integral>y. F 0 y \<partial>lborel)"
proof -
  have slice: "\<And>y. continuous_on {0..} (\<lambda>t. f t y)"
  proof -
    fix y :: 'a
    have pair_cont: "continuous_on {0..} (\<lambda>t. (t,y))"
      by (intro continuous_intros)
    have image: "(\<lambda>t. (t,y)) ` {0..} \<subseteq>
        ({0..}::real set) \<times> (UNIV::'a set)"
      by auto
    have "continuous_on {0..} (\<lambda>t. case_prod f (t,y))"
      by (rule continuous_on_compose2[OF cont pair_cont image])
    then show "continuous_on {0..} (\<lambda>t. f t y)" by simp
  qed
  have int: "set_integrable lborel ({0..} \<times> UNIV) (case_prod f)"
    by (rule normal_halfspace_derivative_integrable[OF support deriv cont])
  show ?thesis
    by (rule normal_halfspace_FTC_compact_support
        [OF support deriv slice int])
qed

lemma tangential_halfspace_derivative_integrable_2D:
  fixes Q g :: "real \<Rightarrow> real \<Rightarrow> real"
  assumes support: "compact (closure
    {p::real \<times> real. 0 \<le> fst p \<and> case_prod Q p \<noteq> 0})"
    and deriv: "\<And>t y. 0 \<le> t \<Longrightarrow>
      ((\<lambda>s. Q t s) has_vector_derivative g t y) (at y)"
    and cont: "continuous_on ({0..} \<times> UNIV) (case_prod g)"
  shows "set_integrable lborel ({0..} \<times> UNIV) (case_prod g)"
proof -
  have ex: "\<exists>R. 0 < R \<and> (\<forall>t y. R \<le> t \<longrightarrow> Q t y = 0) \<and>
    (\<forall>t y. 0 \<le> t \<longrightarrow> y \<notin> ball 0 R \<longrightarrow> Q t y = 0)"
  proof (rule compact_halfspace_support_bound[OF support])
    fix R assume R: "0 < R"
      and upper: "\<And>t y. R \<le> t \<Longrightarrow> Q t y = 0"
      and side: "\<And>t y. 0 \<le> t \<Longrightarrow> y \<notin> ball 0 R \<Longrightarrow> Q t y = 0"
    show ?thesis
      by (rule exI[where x=R]) (use R upper side in auto)
  qed
  then obtain R where R: "0 < R"
    and upper: "\<And>t y. R \<le> t \<Longrightarrow> Q t y = 0"
    and side: "\<And>t y. 0 \<le> t \<Longrightarrow> y \<notin> ball 0 R \<Longrightarrow> Q t y = 0"
    by auto
  have coeff_out: "\<And>t y. 0 \<le> t \<Longrightarrow> y \<notin> {-R..R} \<Longrightarrow> Q t y = 0"
    using side R by (auto simp: ball_def dist_real_def)
  let ?D = "{0..R} \<times> {-R..R}"
  let ?H = "{0..} \<times> UNIV"
  have compactD: "compact ?D"
    by (intro compact_Times compact_Icc)
  have DH: "?D \<subseteq> ?H" by auto
  have contD: "continuous_on ?D (case_prod g)"
    by (rule continuous_on_subset[OF cont DH])
  have zero: "\<And>p. p \<in> ?H \<Longrightarrow> p \<notin> ?D \<Longrightarrow> case_prod g p = 0"
  proof -
    fix p :: "real \<times> real"
    assume H: "p \<in> ?H" and out: "p \<notin> ?D"
    obtain t y where p: "p = (t,y)" by (cases p) auto
    have t: "0 \<le> t" using H p by auto
    show "case_prod g p = 0"
    proof (cases "R < t")
      case True
      have D: "((\<lambda>s. Q t s) has_vector_derivative g t y) (at y)"
        by (rule deriv[OF t])
      have zeroQ: "\<And>s. Q t s = 0"
        using upper R True by auto
      have "g t y = 0"
        by (rule vector_derivative_zero_if_function_zero[OF D zeroQ])
      then show ?thesis by (simp add: p)
    next
      case False
      then have outY: "y \<notin> {-R..R}" using out p t by auto
      have D: "((\<lambda>s. Q t s) has_vector_derivative g t y) (at y)"
        by (rule deriv[OF t])
      have zeroQ: "\<And>s. s \<notin> {-R..R} \<Longrightarrow> Q t s = 0"
        using coeff_out[OF t] by auto
      have "g t y = 0"
        by (rule vector_derivative_zero_off_closed_interval[OF D outY zeroQ])
      then show ?thesis by (simp add: p)
    qed
  qed
  show ?thesis
    by (rule set_integrable_continuous_compact_support
        [OF compactD DH contD zero])
qed

theorem tangential_halfspace_integral_zero_2D:
  fixes Q g :: "real \<Rightarrow> real \<Rightarrow> real"
  assumes support: "compact (closure
    {p::real \<times> real. 0 \<le> fst p \<and> case_prod Q p \<noteq> 0})"
    and deriv: "\<And>t y. 0 \<le> t \<Longrightarrow>
      ((\<lambda>s. Q t s) has_vector_derivative g t y) (at y)"
    and cont: "\<And>t. 0 \<le> t \<Longrightarrow> continuous_on UNIV (g t)"
    and int: "set_integrable lborel ({0..} \<times> UNIV) (case_prod g)"
  shows "(LINT p : {0..} \<times> UNIV | lborel. case_prod g p) = 0"
proof -
  have ex: "\<exists>R. 0 < R \<and>
      (\<forall>t y. 0 \<le> t \<longrightarrow> y \<notin> ball 0 R \<longrightarrow> Q t y = 0)"
  proof (rule compact_halfspace_support_bound[OF support])
    fix R assume R: "0 < R"
      and upper: "\<And>t y. R \<le> t \<Longrightarrow> Q t y = 0"
      and side: "\<And>t y. 0 \<le> t \<Longrightarrow> y \<notin> ball 0 R \<Longrightarrow> Q t y = 0"
    show ?thesis
      by (rule exI[where x=R]) (use R side in auto)
  qed
  then obtain R where R: "0 < R"
    and side: "\<And>t y. 0 \<le> t \<Longrightarrow> y \<notin> ball 0 R \<Longrightarrow> Q t y = 0"
    by auto
  have coeff_out: "\<And>t y. 0 \<le> t \<Longrightarrow> y \<notin> {-R..R} \<Longrightarrow> Q t y = 0"
    using side R by (auto simp: ball_def dist_real_def)
  have faces: "\<And>t. 0 \<le> t \<Longrightarrow> Q t (-R) = 0 \<and> Q t R = 0"
    using side R by (auto simp: ball_def dist_real_def)
  have deriv_box: "\<And>t y. t \<in> {0..} \<Longrightarrow> y \<in> {-R..R} \<Longrightarrow>
      ((\<lambda>s. Q t s) has_vector_derivative g t y) (at y within {-R..R})"
    using deriv by (auto intro: has_vector_derivative_at_within)
  have cont_box: "\<And>t. t \<in> {0..} \<Longrightarrow> continuous_on {-R..R} (g t)"
    by (rule continuous_on_subset[OF cont]) auto
  have int_box: "set_integrable lborel ({0..} \<times> {-R..R}) (case_prod g)"
    by (rule set_integrable_subset[OF int]) (auto intro: borel_Times)
  have faces_box: "\<And>t. t \<in> {0..} \<Longrightarrow> Q t (-R) = 0 \<and> Q t R = 0"
    using faces by auto
  have box_zero: "(LINT p : {0..} \<times> {-R..R} | lborel. case_prod g p) = 0"
    by (rule second_slice_FTC_zero[OF _ deriv_box cont_box int_box faces_box])
       (use R in auto)
  have deriv_out: "\<And>t y. 0 \<le> t \<Longrightarrow> y \<notin> {-R..R} \<Longrightarrow> g t y = 0"
  proof -
    fix t :: real and y :: real
    assume t: "0 \<le> t" and out: "y \<notin> {-R..R}"
    have D: "((\<lambda>s. Q t s) has_vector_derivative g t y) (at y)"
      by (rule deriv[OF t])
    have zero: "\<And>s. s \<notin> {-R..R} \<Longrightarrow> Q t s = 0"
      using coeff_out[OF t] by auto
    show "g t y = 0"
      by (rule vector_derivative_zero_off_closed_interval[OF D out zero])
  qed
  have DH: "{0..} \<times> {-R..R} \<subseteq> {0..} \<times> UNIV" by auto
  have zero_out: "\<And>p. p \<in> {0..} \<times> UNIV \<Longrightarrow>
      p \<notin> {0..} \<times> {-R..R} \<Longrightarrow> case_prod g p = 0"
  proof -
    fix p :: "real \<times> real"
    assume H: "p \<in> {0..} \<times> UNIV"
      and out: "p \<notin> {0..} \<times> {-R..R}"
    obtain t y where p: "p = (t,y)" by (cases p) auto
    have t: "0 \<le> t" using H p by auto
    have y: "y \<notin> {-R..R}" using out p t by auto
    show "case_prod g p = 0"
      using deriv_out[OF t y] by (simp add: p)
  qed
  have "(LINT p : {0..} \<times> UNIV | lborel. case_prod g p) =
      (LINT p : {0..} \<times> {-R..R} | lborel. case_prod g p)"
    by (rule set_lebesgue_integral_restrict_support[OF DH zero_out])
  also have "\<dots> = 0" by (rule box_zero)
  finally show ?thesis .
qed

theorem Stokes_halfspace_2D_compact_support:
  fixes P Q P_t Q_y :: "real \<Rightarrow> real \<Rightarrow> real"
  assumes support_P: "compact (closure
      {p::real \<times> real. 0 \<le> fst p \<and> case_prod P p \<noteq> 0})"
    and support_Q: "compact (closure
      {p::real \<times> real. 0 \<le> fst p \<and> case_prod Q p \<noteq> 0})"
    and deriv_P: "\<And>t y. 0 \<le> t \<Longrightarrow>
      ((\<lambda>s. P s y) has_vector_derivative P_t t y) (at t)"
    and cont_P: "\<And>y. continuous_on {0..} (\<lambda>t. P_t t y)"
    and int_P: "set_integrable lborel ({0..} \<times> UNIV) (case_prod P_t)"
    and deriv_Q: "\<And>t y. 0 \<le> t \<Longrightarrow>
      ((\<lambda>s. Q t s) has_vector_derivative Q_y t y) (at y)"
    and cont_Q: "\<And>t. 0 \<le> t \<Longrightarrow> continuous_on UNIV (Q_y t)"
    and int_Q: "set_integrable lborel ({0..} \<times> UNIV) (case_prod Q_y)"
  shows "(LINT p : {0..} \<times> UNIV | lborel.
      case_prod (\<lambda>t y. P_t t y - Q_y t y) p) =
    - (\<integral>y. P 0 y \<partial>lborel)"
proof -
  let ?H = "{0..} \<times> UNIV"
  have split: "(LINT p : ?H | lborel.
      case_prod (\<lambda>t y. P_t t y - Q_y t y) p) =
    (LINT p : ?H | lborel. case_prod P_t p) -
    (LINT p : ?H | lborel. case_prod Q_y p)"
    using int_P int_Q
    by (simp add: set_lebesgue_integral_def set_integrable_def
      algebra_simps split_def)
  have normal: "(LINT p : ?H | lborel. case_prod P_t p) =
      - (\<integral>y. P 0 y \<partial>lborel)"
    by (rule normal_halfspace_FTC_compact_support
        [OF support_P deriv_P cont_P int_P])
  have tangential: "(LINT p : ?H | lborel. case_prod Q_y p) = 0"
    by (rule tangential_halfspace_integral_zero_2D
        [OF support_Q deriv_Q cont_Q int_Q])
  show ?thesis using split normal tangential by simp
qed

theorem Stokes_halfspace_2D_C1:
  fixes P Q P_t Q_y :: "real \<Rightarrow> real \<Rightarrow> real"
  assumes support_P: "compact (closure
      {p::real \<times> real. 0 \<le> fst p \<and> case_prod P p \<noteq> 0})"
    and support_Q: "compact (closure
      {p::real \<times> real. 0 \<le> fst p \<and> case_prod Q p \<noteq> 0})"
    and deriv_P: "\<And>t y. 0 \<le> t \<Longrightarrow>
      ((\<lambda>s. P s y) has_vector_derivative P_t t y) (at t)"
    and deriv_Q: "\<And>t y. 0 \<le> t \<Longrightarrow>
      ((\<lambda>s. Q t s) has_vector_derivative Q_y t y) (at y)"
    and cont_P: "continuous_on ({0..} \<times> UNIV) (case_prod P_t)"
    and cont_Q: "continuous_on ({0..} \<times> UNIV) (case_prod Q_y)"
  shows "(LINT p : {0..} \<times> UNIV | lborel.
      case_prod (\<lambda>t y. P_t t y - Q_y t y) p) =
    - (\<integral>y. P 0 y \<partial>lborel)"
proof -
  have slice_P: "\<And>y. continuous_on {0..} (\<lambda>t. P_t t y)"
  proof -
    fix y :: real
    have pair_cont: "continuous_on {0..} (\<lambda>t. (t,y))"
      by (intro continuous_intros)
    have image: "(\<lambda>t. (t,y)) ` {0..} \<subseteq> {0..} \<times> UNIV"
      by auto
    have "continuous_on {0..} (\<lambda>t. case_prod P_t (t,y))"
      by (rule continuous_on_compose2[OF cont_P pair_cont image])
    show "continuous_on {0..} (\<lambda>t. P_t t y)"
      using \<open>continuous_on {0..} (\<lambda>t. case_prod P_t (t,y))\<close> by simp
  qed
  have slice_Q: "\<And>t. 0 \<le> t \<Longrightarrow> continuous_on UNIV (Q_y t)"
  proof -
    fix t :: real
    assume t: "0 \<le> t"
    have pair_cont: "continuous_on UNIV (\<lambda>y. (t,y))"
      by (intro continuous_intros)
    have image: "(\<lambda>y. (t,y)) ` UNIV \<subseteq> {0..} \<times> UNIV"
      using t by auto
    have "continuous_on UNIV (\<lambda>y. case_prod Q_y (t,y))"
      by (rule continuous_on_compose2[OF cont_Q pair_cont image])
    show "continuous_on UNIV (Q_y t)"
      using \<open>continuous_on UNIV (\<lambda>y. case_prod Q_y (t,y))\<close> by simp
  qed
  have int_P: "set_integrable lborel ({0..} \<times> UNIV) (case_prod P_t)"
    by (rule normal_halfspace_derivative_integrable
        [OF support_P deriv_P cont_P])
  have int_Q: "set_integrable lborel ({0..} \<times> UNIV) (case_prod Q_y)"
    by (rule tangential_halfspace_derivative_integrable_2D
        [OF support_Q deriv_Q cont_Q])
  show ?thesis
    by (rule Stokes_halfspace_2D_compact_support
        [OF support_P support_Q deriv_P slice_P int_P
            deriv_Q slice_Q int_Q])
qed

end
