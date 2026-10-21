theory Stokes_Chart_Local
  imports Stokes_Basis_Fubini
begin

definition zero_extend_halfspace ::
    "(real \<times> 'a) set \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow>
      real \<Rightarrow> 'a \<Rightarrow> real"
  where "zero_extend_halfspace U F t y =
    (if (t,y) \<in> U then F t y else 0)"

text \<open>
  At the boundary of a half-space, the normal derivative is naturally
  taken within the half-line.  This lemma supplies uniqueness when a
  coefficient vanishes on that half-line.
\<close>

lemma vector_derivative_zero_on_halfline_within:
  fixes F :: "real \<Rightarrow> real"
  assumes t: "0 \<le> t"
    and deriv: "(F has_vector_derivative f) (at t within {0..})"
    and zero: "\<And>s. 0 \<le> s \<Longrightarrow> F s = 0"
  shows "f = 0"
proof -
  have D0: "((\<lambda>s::real. 0::real) has_vector_derivative 0)
      (at t within {0..})"
    by (rule has_vector_derivative_at_within)
       (rule has_vector_derivative_const)
  have Z: "(F has_vector_derivative 0) (at t within {0..})"
    by (rule has_vector_derivative_transform
        [where f="\<lambda>s::real. 0" and g=F and S="{0..}" and x=t,
         OF _ _ D0])
       (use t zero in auto)
  have ne: "at t within {0..} \<noteq> bot"
  proof (cases "t = 0")
    case True
    have "{0..} - {0::real} = {0<..}" by auto
    then show ?thesis
      using True by (simp add: at_within_eq_bot_iff)
  next
    case False
    then have pos: "0 < t" using t by simp
    have "at t within {0..} = at t"
      by (rule at_within_open_subset[where S="{0<..}"])
         (use pos in auto)
    then show ?thesis by simp
  qed
  show ?thesis
    by (rule vector_derivative_unique_within[OF ne deriv Z])
qed

lemma normal_halfspace_derivative_integrable_within:
  fixes F f :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes support: "compact (closure
    {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod F p \<noteq> 0})"
    and deriv: "\<And>t y. 0 \<le> t \<Longrightarrow>
      ((\<lambda>s. F s y) has_vector_derivative f t y)
        (at t within {0..})"
    and cont: "continuous_on ({0..} \<times> UNIV) (case_prod f)"
  shows "set_integrable lborel ({0..} \<times> UNIV) (case_prod f)"
proof -
  have ex: "\<exists>R. 0 < R \<and>
    (\<forall>t y. R \<le> t \<longrightarrow> F t y = 0) \<and>
    (\<forall>t y. 0 \<le> t \<longrightarrow>
      y \<notin> ball 0 R \<longrightarrow> F t y = 0)"
  proof (rule compact_halfspace_support_bound[OF support])
    fix R assume R: "0 < R"
      and upper: "\<And>t y. R \<le> t \<Longrightarrow> F t y = 0"
      and side: "\<And>t y. 0 \<le> t \<Longrightarrow>
        y \<notin> ball 0 R \<Longrightarrow> F t y = 0"
    show ?thesis
      by (rule exI[where x=R]) (use R upper side in auto)
  qed
  then obtain R where R: "0 < R"
    and upper: "\<And>t y. R \<le> t \<Longrightarrow> F t y = 0"
    and side: "\<And>t y. 0 \<le> t \<Longrightarrow>
      y \<notin> ball 0 R \<Longrightarrow> F t y = 0"
    by auto
  let ?D = "{0..R} \<times> cball (0::'a) R"
  let ?H = "({0..}::real set) \<times> (UNIV::'a set)"
  have compactD: "compact ?D"
    by (intro compact_Times compact_Icc compact_cball)
  have DH: "?D \<subseteq> ?H" by auto
  have contD: "continuous_on ?D (case_prod f)"
    by (rule continuous_on_subset[OF cont DH])
  have zero: "\<And>p. p \<in> ?H \<Longrightarrow> p \<notin> ?D \<Longrightarrow>
      case_prod f p = 0"
  proof -
    fix p :: "real \<times> 'a"
    assume H: "p \<in> ?H" and out: "p \<notin> ?D"
    obtain t y where p: "p = (t,y)" by (cases p) auto
    have t: "0 \<le> t" using H p by auto
    show "case_prod f p = 0"
    proof (cases "R < t")
      case True
      have D: "((\<lambda>s. F s y) has_vector_derivative f t y)
          (at t within {0..})"
        by (rule deriv[OF t])
      have at_eq: "at t within {0..} = at t"
        by (rule at_within_open_subset[where S="{0<..}"])
           (use R True in auto)
      have D_at: "((\<lambda>s. F s y) has_vector_derivative f t y) (at t)"
        using D by (simp add: at_eq)
      have "f t y = 0"
        by (rule vector_derivative_zero_on_real_tail[OF D_at True])
           (use upper in auto)
      then show ?thesis by (simp add: p)
    next
      case False
      then have outY: "y \<notin> cball 0 R"
        using out p t by auto
      have notball: "y \<notin> ball 0 R"
        using outY by auto
      have D: "((\<lambda>s. F s y) has_vector_derivative f t y)
          (at t within {0..})"
        by (rule deriv[OF t])
      have zeroF: "\<And>s. 0 \<le> s \<Longrightarrow> F s y = 0"
        using side[OF _ notball] by auto
      have "f t y = 0"
        by (rule vector_derivative_zero_on_halfline_within
            [OF t D zeroF])
      then show ?thesis by (simp add: p)
    qed
  qed
  show ?thesis
    by (rule set_integrable_continuous_compact_support
        [OF compactD DH contD zero])
qed

theorem normal_halfspace_FTC_within:
  fixes F f :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes support: "compact (closure
    {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod F p \<noteq> 0})"
    and deriv: "\<And>t y. 0 \<le> t \<Longrightarrow>
      ((\<lambda>s. F s y) has_vector_derivative f t y)
        (at t within {0..})"
    and cont: "continuous_on ({0..} \<times> UNIV) (case_prod f)"
  shows "(LINT p : {0..} \<times> UNIV | lborel. case_prod f p) =
    - (\<integral>y. F 0 y \<partial>lborel)"
proof -
  have ex: "\<exists>R. 0 < R \<and>
    (\<forall>t y. R \<le> t \<longrightarrow> F t y = 0)"
  proof (rule compact_halfspace_support_bound[OF support])
    fix R assume R: "0 < R"
      and upper: "\<And>t y. R \<le> t \<Longrightarrow> F t y = 0"
      and side: "\<And>t y. 0 \<le> t \<Longrightarrow>
        y \<notin> ball 0 R \<Longrightarrow> F t y = 0"
    show ?thesis
      by (rule exI[where x=R]) (use R upper in auto)
  qed
  then obtain R where R: "0 < R"
    and upper: "\<And>t y. R \<le> t \<Longrightarrow> F t y = 0"
    by auto
  have deriv_box: "\<And>y t. y \<in> UNIV \<Longrightarrow> t \<in> {0..R} \<Longrightarrow>
      ((\<lambda>s. F s y) has_vector_derivative f t y)
        (at t within {0..R})"
  proof -
    fix y :: 'a and t :: real
    assume "y \<in> UNIV" and t: "t \<in> {0..R}"
    have D: "((\<lambda>s. F s y) has_vector_derivative f t y)
        (at t within {0..})"
      by (rule deriv) (use t in auto)
    show "((\<lambda>s. F s y) has_vector_derivative f t y)
        (at t within {0..R})"
      by (rule has_vector_derivative_within_subset[OF D]) auto
  qed
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
  have cont_box: "\<And>y. y \<in> UNIV \<Longrightarrow>
      continuous_on {0..R} (\<lambda>t. f t y)"
    by (rule continuous_on_subset[OF slice]) auto
  have int: "set_integrable lborel ({0..} \<times> UNIV) (case_prod f)"
    by (rule normal_halfspace_derivative_integrable_within
        [OF support deriv cont])
  have int_box: "set_integrable lborel ({0..R} \<times> UNIV) (case_prod f)"
    by (rule set_integrable_subset[OF int]) (auto intro: borel_Times)
  have end_zero: "\<And>y. y \<in> UNIV \<Longrightarrow> F R y = 0"
    using upper by simp
  have tail_zero: "\<And>t y. R < t \<Longrightarrow> y \<in> UNIV \<Longrightarrow>
      f t y = 0"
  proof -
    fix t :: real and y :: 'a
    assume rt: "R < t" and "y \<in> UNIV"
    have t: "0 \<le> t" using R rt by auto
    have D: "((\<lambda>s. F s y) has_vector_derivative f t y)
        (at t within {0..})"
      by (rule deriv[OF t])
    have at_eq: "at t within {0..} = at t"
      by (rule at_within_open_subset[where S="{0<..}"])
         (use R rt in auto)
    have D_at: "((\<lambda>s. F s y) has_vector_derivative f t y) (at t)"
      using D by (simp add: at_eq)
    show "f t y = 0"
      by (rule vector_derivative_zero_on_real_tail[OF D_at rt])
         (use upper in auto)
  qed
  have "(LINT p : {0..} \<times> UNIV | lborel. case_prod f p) =
      - (LINT y : UNIV | lborel. F 0 y)"
    by (rule normal_halfspace_FTC
        [OF less_imp_le[OF R] deriv_box cont_box int_box
            end_zero tail_zero])
  then show ?thesis by (simp add: set_lebesgue_integral_def)
qed

lemma continuous_on_relative_open_cover:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes open_U: "open U"
    and open_W: "open W"
    and cover: "H \<subseteq> U \<union> W"
    and cont_U: "continuous_on (H \<inter> U) f"
    and cont_W: "continuous_on (H \<inter> W) f"
  shows "continuous_on H f"
proof (unfold continuous_on_open_invariant, intro allI impI)
  fix C :: "'b set" assume open_C: "open C"
  obtain A where open_A: "open A"
    and eq_A: "A \<inter> (H \<inter> U) = f -` C \<inter> (H \<inter> U)"
    using cont_U open_C
    unfolding continuous_on_open_invariant by blast
  obtain B where open_B: "open B"
    and eq_B: "B \<inter> (H \<inter> W) = f -` C \<inter> (H \<inter> W)"
    using cont_W open_C
    unfolding continuous_on_open_invariant by blast
  have op: "open ((A \<inter> U) \<union> (B \<inter> W))"
    using open_A open_B open_U open_W by auto
  have eq: "((A \<inter> U) \<union> (B \<inter> W)) \<inter> H =
      f -` C \<inter> H"
    using cover eq_A eq_B by blast
  show "\<exists>A. open A \<and> A \<inter> H = f -` C \<inter> H"
    using op eq by blast
qed

lemma continuous_on_zero_extension_relative:
  fixes F :: "'a::euclidean_space \<Rightarrow> real"
  assumes open_U: "open U"
    and compact_K: "compact K"
    and KU: "K \<subseteq> U"
    and cont: "continuous_on (H \<inter> U) F"
    and zero: "\<And>x. x \<in> H \<Longrightarrow> x \<in> U \<Longrightarrow>
      x \<notin> K \<Longrightarrow> F x = 0"
  shows "continuous_on H (\<lambda>x. if x \<in> U then F x else 0)"
proof -
  let ?E = "\<lambda>x. if x \<in> U then F x else 0"
  have closed_K: "closed K"
    by (rule compact_imp_closed[OF compact_K])
  have open_notK: "open (- K)"
    by (rule open_Compl[OF closed_K])
  have cover: "H \<subseteq> U \<union> - K"
    using KU by auto
  have cont_U: "continuous_on (H \<inter> U) ?E"
    by (rule continuous_on_eq[OF cont]) auto
  have cont_notK: "continuous_on (H \<inter> - K) ?E"
  proof -
    have eq: "\<And>x. x \<in> H \<inter> - K \<Longrightarrow> ?E x = 0"
      using zero by auto
    have cont0: "continuous_on (H \<inter> - K) (\<lambda>x. 0::real)"
      by (rule continuous_on_const)
    show ?thesis
      by (rule continuous_on_eq[OF cont0])
         (rule sym, rule eq, assumption)
  qed
  show ?thesis
    by (rule continuous_on_relative_open_cover
        [OF open_U open_notK cover cont_U cont_notK])
qed

lemma compact_support_zero_extension_relative:
  fixes F :: "'a::euclidean_space \<Rightarrow> real"
  assumes compact_K: "compact K"
    and zero: "\<And>x. x \<in> H \<Longrightarrow> x \<in> U \<Longrightarrow>
      x \<notin> K \<Longrightarrow> F x = 0"
  shows "compact (closure
    {x. x \<in> H \<and> (if x \<in> U then F x else 0) \<noteq> 0})"
proof -
  let ?S = "{x. x \<in> H \<and> (if x \<in> U then F x else 0) \<noteq> 0}"
  have sub: "?S \<subseteq> K"
    using zero by auto
  have "bounded ?S"
    by (rule bounded_subset[OF compact_imp_bounded[OF compact_K] sub])
  then show ?thesis by simp
qed

lemma set_integral_zero_extension:
  fixes f :: "'a \<Rightarrow> real"
  shows "(LINT x : H | M. if x \<in> U then f x else 0) =
    (LINT x : H \<inter> U | M. f x)"
  unfolding set_lebesgue_integral_def
  by (rule Bochner_Integration.integral_cong[OF refl])
     (auto simp: indicator_def)

lemma zero_extend_vector_derivative_along:
  fixes c :: "real \<Rightarrow> 'a::euclidean_space"
    and F :: "'a \<Rightarrow> real"
  assumes open_U: "open U"
    and closed_K: "closed K"
    and KU: "K \<subseteq> U"
    and cont_c: "continuous_on UNIV c"
    and t: "t \<in> S"
    and path_H: "\<And>s. s \<in> S \<Longrightarrow> c s \<in> H"
    and deriv: "c t \<in> U \<Longrightarrow>
      ((\<lambda>s. F (c s)) has_vector_derivative g (c t))
        (at t within S)"
    and zero_F: "\<And>x. x \<in> H \<Longrightarrow> x \<in> U \<Longrightarrow>
      x \<notin> K \<Longrightarrow> F x = 0"
  shows "((\<lambda>s. if c s \<in> U then F (c s) else 0)
      has_vector_derivative
        (if c t \<in> U then g (c t) else 0)) (at t within S)"
proof (cases "c t \<in> U")
  case True
  have op: "open (c -` U)"
    using continuous_open_preimage[OF cont_c open_UNIV open_U]
    by simp
  have tin: "t \<in> c -` U" using True by simp
  obtain d where d: "0 < d" and ball: "ball t d \<subseteq> c -` U"
    by (rule openE[OF op tin])
  have D: "((\<lambda>s. F (c s)) has_vector_derivative g (c t))
      (at t within S)"
    by (rule deriv[OF True])
  have "((\<lambda>s. if c s \<in> U then F (c s) else 0)
      has_vector_derivative g (c t)) (at t within S)"
  proof (rule has_vector_derivative_transform_within[OF D d t])
    fix s assume "s \<in> S" and near: "dist s t < d"
    have "s \<in> ball t d" using near by (simp add: dist_commute)
    then have "c s \<in> U" using ball by auto
    then show "F (c s) = (if c s \<in> U then F (c s) else 0)"
      by simp
  qed
  then show ?thesis using True by simp
next
  case False
  have notK: "c t \<notin> K" using False KU by auto
  have op: "open (c -` (- K))"
    using continuous_open_preimage
      [OF cont_c open_UNIV open_Compl[OF closed_K]]
    by simp
  have tin: "t \<in> c -` (- K)" using notK by simp
  obtain d where d: "0 < d"
    and ball: "ball t d \<subseteq> c -` (- K)"
    by (rule openE[OF op tin])
  have D0: "((\<lambda>s::real. 0::real) has_vector_derivative 0)
      (at t within S)"
    by (rule has_vector_derivative_at_within)
       (rule has_vector_derivative_const)
  have D: "((\<lambda>s. if c s \<in> U then F (c s) else 0)
      has_vector_derivative 0) (at t within S)"
  proof (rule has_vector_derivative_transform_within[OF D0 d t])
    fix s assume s: "s \<in> S" and near: "dist s t < d"
    have "s \<in> ball t d" using near by (simp add: dist_commute)
    have outK: "c s \<notin> K"
      using ball \<open>s \<in> ball t d\<close> by auto
    show "0 = (if c s \<in> U then F (c s) else 0)"
      using zero_F[OF path_H[OF s] _ outK] by auto
  qed
  then show ?thesis using False by simp
qed

lemma vector_derivative_zero_on_relative_open:
  fixes c :: "real \<Rightarrow> 'a::euclidean_space"
    and F :: "'a \<Rightarrow> real"
  assumes open_U: "open U"
    and closed_K: "closed K"
    and cont_c: "continuous_on UNIV c"
    and t: "t \<in> S"
    and ne: "at t within S \<noteq> bot"
    and path_H: "\<And>s. s \<in> S \<Longrightarrow> c s \<in> H"
    and point: "c t \<in> U" "c t \<notin> K"
    and deriv: "((\<lambda>s. F (c s)) has_vector_derivative g)
      (at t within S)"
    and zero_F: "\<And>x. x \<in> H \<Longrightarrow> x \<in> U \<Longrightarrow>
      x \<notin> K \<Longrightarrow> F x = 0"
  shows "g = 0"
proof -
  let ?W = "U - K"
  have open_W: "open ?W"
    using open_U closed_K by auto
  have op: "open (c -` ?W)"
    using continuous_open_preimage[OF cont_c open_UNIV open_W]
    by simp
  have tin: "t \<in> c -` ?W"
    using point by simp
  obtain d where d: "0 < d"
    and ball: "ball t d \<subseteq> c -` ?W"
    by (rule openE[OF op tin])
  have D0: "((\<lambda>s::real. 0::real) has_vector_derivative 0)
      (at t within S)"
    by (rule has_vector_derivative_at_within)
       (rule has_vector_derivative_const)
  have Z: "((\<lambda>s. F (c s)) has_vector_derivative 0)
      (at t within S)"
  proof (rule has_vector_derivative_transform_within[OF D0 d t])
    fix s assume s: "s \<in> S" and near: "dist s t < d"
    have "s \<in> ball t d" using near by (simp add: dist_commute)
    then have "c s \<in> ?W" using ball by auto
    then have U: "c s \<in> U" and notK: "c s \<notin> K"
      by auto
    have "F (c s) = 0"
      by (rule zero_F[OF path_H[OF s] U notK])
    then show "0 = F (c s)" by simp
  qed
  show ?thesis
    by (rule vector_derivative_unique_within[OF ne deriv Z])
qed

lemma at_halfline_not_bot:
  fixes t :: real
  assumes t: "0 \<le> t"
  shows "at t within {0..} \<noteq> bot"
proof (cases "t = 0")
  case True
  have "{0..} - {0::real} = {0<..}" by auto
  then show ?thesis using True by (simp add: at_within_eq_bot_iff)
next
  case False
  then have pos: "0 < t" using t by simp
  have "at t within {0..} = at t"
    by (rule at_within_open_subset[where S="{0<..}"])
       (use pos in auto)
  then show ?thesis by simp
qed

lemma normal_zero_extension_derivative:
  fixes F G :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes open_U: "open U"
    and compact_K: "compact K"
    and KU: "K \<subseteq> U"
    and zero_F: "\<And>p. p \<in> {0..} \<times> UNIV \<Longrightarrow>
      p \<in> U \<Longrightarrow> p \<notin> K \<Longrightarrow> case_prod F p = 0"
    and deriv: "\<And>t y. 0 \<le> t \<Longrightarrow> (t,y) \<in> U \<Longrightarrow>
      ((\<lambda>s. F s y) has_vector_derivative G t y)
        (at t within {0..})"
    and t: "0 \<le> t"
  shows "((\<lambda>s. if (s,y) \<in> U then F s y else 0)
    has_vector_derivative
      (if (t,y) \<in> U then G t y else 0)) (at t within {0..})"
proof -
  let ?c = "\<lambda>s. (s,y)"
  have closed_K: "closed K"
    by (rule compact_imp_closed[OF compact_K])
  have cont_c: "continuous_on UNIV ?c"
    by (intro continuous_intros)
  have D: "((\<lambda>s. if ?c s \<in> U then case_prod F (?c s) else 0)
      has_vector_derivative
        (if ?c t \<in> U then case_prod G (?c t) else 0))
      (at t within {0..})"
  proof (rule zero_extend_vector_derivative_along
      [OF open_U closed_K KU cont_c])
    show "t \<in> {0..}" using t by simp
    fix s :: real assume "s \<in> {0..}"
    then show "?c s \<in> {0..} \<times> UNIV" by simp
  next
    assume "?c t \<in> U"
    then show "((\<lambda>s. case_prod F (?c s)) has_vector_derivative
        case_prod G (?c t)) (at t within {0..})"
      by (simp add: deriv[OF t])
  next
    fix p :: "real \<times> 'a"
    assume "p \<in> {0..} \<times> UNIV" "p \<in> U" "p \<notin> K"
    then show "case_prod F p = 0"
      by (rule zero_F)
  qed
  then show ?thesis by (simp only: case_prod_beta fst_conv snd_conv)
qed

lemma normal_local_derivative_zero_outside_support:
  fixes F G :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes open_U: "open U"
    and compact_K: "compact K"
    and zero_F: "\<And>p. p \<in> {0..} \<times> UNIV \<Longrightarrow>
      p \<in> U \<Longrightarrow> p \<notin> K \<Longrightarrow> case_prod F p = 0"
    and deriv: "\<And>t y. 0 \<le> t \<Longrightarrow> (t,y) \<in> U \<Longrightarrow>
      ((\<lambda>s. F s y) has_vector_derivative G t y)
        (at t within {0..})"
    and t: "0 \<le> t"
    and pU: "(t,y) \<in> U"
    and pK: "(t,y) \<notin> K"
  shows "G t y = 0"
proof -
  let ?c = "\<lambda>s. (s,y)"
  have closed_K: "closed K"
    by (rule compact_imp_closed[OF compact_K])
  have cont_c: "continuous_on UNIV ?c"
    by (intro continuous_intros)
  have D: "((\<lambda>s. case_prod F (?c s)) has_vector_derivative
      case_prod G (?c t)) (at t within {0..})"
    by (simp add: deriv[OF t pU])
  have "case_prod G (?c t) = 0"
  proof (rule vector_derivative_zero_on_relative_open
      [OF open_U closed_K cont_c])
    show "t \<in> {0..}" using t by simp
    show "at t within {0..} \<noteq> bot"
      by (rule at_halfline_not_bot[OF t])
    fix s :: real assume "s \<in> {0..}"
    then show "?c s \<in> {0..} \<times> UNIV" by simp
  next
    show "?c t \<in> U" using pU by simp
    show "?c t \<notin> K" using pK by simp
    show "((\<lambda>s. case_prod F (?c s)) has_vector_derivative
        case_prod G (?c t)) (at t within {0..})"
      by (rule D)
    fix p :: "real \<times> 'a"
    assume "p \<in> {0..} \<times> UNIV" "p \<in> U" "p \<notin> K"
    then show "case_prod F p = 0" by (rule zero_F)
  qed
  then show ?thesis by simp
qed

theorem normal_zero_extension_C1:
  fixes F G :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes open_U: "open U"
    and compact_K: "compact K"
    and K_chart: "K \<subseteq> ({0..} \<times> UNIV) \<inter> U"
    and zero_F: "\<And>p. p \<in> {0..} \<times> UNIV \<Longrightarrow>
      p \<in> U \<Longrightarrow> p \<notin> K \<Longrightarrow> case_prod F p = 0"
    and deriv_F: "\<And>t y. 0 \<le> t \<Longrightarrow> (t,y) \<in> U \<Longrightarrow>
      ((\<lambda>s. F s y) has_vector_derivative G t y)
        (at t within {0..})"
    and cont_G: "continuous_on (({0..} \<times> UNIV) \<inter> U)
      (case_prod G)"
  shows "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and>
        case_prod (zero_extend_halfspace U F) p \<noteq> 0})"
    and "continuous_on ({0..} \<times> UNIV)
      (case_prod (zero_extend_halfspace U G))"
    and "\<And>t y. 0 \<le> t \<Longrightarrow>
      ((\<lambda>s. zero_extend_halfspace U F s y) has_vector_derivative
        zero_extend_halfspace U G t y) (at t within {0..})"
proof -
  let ?H = "{0..} \<times> UNIV :: (real \<times> 'a) set"
  have KU: "K \<subseteq> U" using K_chart by auto
  have E_support: "compact (closure
    {p. p \<in> ?H \<and> (if p \<in> U then case_prod F p else 0) \<noteq> 0})"
    by (rule compact_support_zero_extension_relative
        [OF compact_K zero_F])
  have support_set_eq:
    "{p::real \<times> 'a. 0 \<le> fst p \<and>
        case_prod (zero_extend_halfspace U F) p \<noteq> 0} =
      {p. p \<in> ?H \<and> (if p \<in> U then case_prod F p else 0) \<noteq> 0}"
    by (rule set_eqI) (case_tac x, simp add: zero_extend_halfspace_def)
  show "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and>
        case_prod (zero_extend_halfspace U F) p \<noteq> 0})"
    by (subst support_set_eq, rule E_support)
  have zero_G: "\<And>p. p \<in> ?H \<Longrightarrow> p \<in> U \<Longrightarrow>
      p \<notin> K \<Longrightarrow> case_prod G p = 0"
  proof -
    fix p :: "real \<times> 'a"
    assume H: "p \<in> ?H" and pU: "p \<in> U" and pK: "p \<notin> K"
    obtain t y where p: "p = (t,y)" by (cases p) auto
    have t: "0 \<le> t" using H p by auto
    have "G t y = 0"
      by (rule normal_local_derivative_zero_outside_support
          [OF open_U compact_K zero_F deriv_F t])
         (use pU pK p in auto)
    then show "case_prod G p = 0" by (simp add: p)
  qed
  have E_cont: "continuous_on ?H
      (\<lambda>p. if p \<in> U then case_prod G p else 0)"
    by (rule continuous_on_zero_extension_relative
        [OF open_U compact_K KU cont_G zero_G])
  show "continuous_on ?H (case_prod (zero_extend_halfspace U G))"
  proof (rule continuous_on_eq[OF E_cont])
    fix p :: "real \<times> 'a"
    assume "p \<in> ?H"
    show "(if p \<in> U then case_prod G p else 0) =
      case_prod (zero_extend_halfspace U G) p"
      by (cases p) (simp add: zero_extend_halfspace_def)
  qed
  fix t :: real and y :: 'a
  assume t: "0 \<le> t"
  show "((\<lambda>s. zero_extend_halfspace U F s y) has_vector_derivative
      zero_extend_halfspace U G t y) (at t within {0..})"
    unfolding zero_extend_halfspace_def
    by (rule normal_zero_extension_derivative
        [OF open_U compact_K KU zero_F deriv_F t])
qed

lemma basis_slice_reconstruct:
  fixes b y :: "'a::euclidean_space"
  assumes b: "b \<in> Basis"
  shows "(\<Sum>j\<in>Basis.
    ((\<lambda>k. y \<bullet> k)(b:=y \<bullet> b)) j *\<^sub>R j) = y"
proof -
  have update: "((\<lambda>k. y \<bullet> k)(b:=y \<bullet> b)) =
      (\<lambda>k. y \<bullet> k)"
    by auto
  show ?thesis by (simp add: update euclidean_representation)
qed

lemma tangential_zero_extension_derivative:
  fixes F G :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
    and b :: 'a
  assumes b: "b \<in> Basis"
    and open_U: "open U"
    and compact_K: "compact K"
    and KU: "K \<subseteq> U"
    and zero_F: "\<And>p. p \<in> {0..} \<times> UNIV \<Longrightarrow>
      p \<in> U \<Longrightarrow> p \<notin> K \<Longrightarrow> case_prod F p = 0"
    and deriv: "\<And>t v s. 0 \<le> t \<Longrightarrow>
      (t, \<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j) \<in> U \<Longrightarrow>
      ((\<lambda>u. F t (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          G t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (at s)"
    and t: "0 \<le> t"
  shows "((\<lambda>u. if (t,\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j) \<in> U
      then F t (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j) else 0)
    has_vector_derivative
      (if (t,\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j) \<in> U
       then G t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j) else 0))
      (at s)"
proof -
  let ?line = "\<lambda>u. \<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j"
  let ?c = "\<lambda>u. (t, ?line u)"
  have closed_K: "closed K"
    by (rule compact_imp_closed[OF compact_K])
  have cont_c: "continuous_on UNIV ?c"
    by (rule continuous_on_Pair)
       (rule continuous_on_const,
        rule basis_slice_continuous[OF b])
  have D: "((\<lambda>u. if ?c u \<in> U then case_prod F (?c u) else 0)
      has_vector_derivative
        (if ?c s \<in> U then case_prod G (?c s) else 0))
      (at s within UNIV)"
  proof (rule zero_extend_vector_derivative_along
      [OF open_U closed_K KU cont_c])
    show "s \<in> UNIV" by simp
    fix u :: real assume "u \<in> UNIV"
    then show "?c u \<in> {0..} \<times> UNIV" using t by simp
  next
    assume "?c s \<in> U"
    then show "((\<lambda>u. case_prod F (?c u)) has_vector_derivative
        case_prod G (?c s)) (at s within UNIV)"
      using deriv[OF t, of v s] by simp
  next
    fix p :: "real \<times> 'a"
    assume "p \<in> {0..} \<times> UNIV" "p \<in> U" "p \<notin> K"
    then show "case_prod F p = 0" by (rule zero_F)
  qed
  then show ?thesis
    by (simp only: case_prod_beta fst_conv snd_conv)
qed

lemma tangential_local_derivative_zero_outside_support:
  fixes F G :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
    and b :: 'a
  assumes b: "b \<in> Basis"
    and open_U: "open U"
    and compact_K: "compact K"
    and zero_F: "\<And>p. p \<in> {0..} \<times> UNIV \<Longrightarrow>
      p \<in> U \<Longrightarrow> p \<notin> K \<Longrightarrow> case_prod F p = 0"
    and deriv: "\<And>t v s. 0 \<le> t \<Longrightarrow>
      (t, \<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j) \<in> U \<Longrightarrow>
      ((\<lambda>u. F t (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          G t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (at s)"
    and t: "0 \<le> t"
    and pU: "(t,y) \<in> U"
    and pK: "(t,y) \<notin> K"
  shows "G t y = 0"
proof -
  let ?v = "\<lambda>j. y \<bullet> j"
  let ?s = "y \<bullet> b"
  let ?line = "\<lambda>u. \<Sum>j\<in>Basis. (?v(b:=u)) j *\<^sub>R j"
  let ?c = "\<lambda>u. (t, ?line u)"
  have rep: "?line ?s = y"
    by (rule basis_slice_reconstruct[OF b])
  have coords: "(\<Sum>j\<in>Basis. (y \<bullet> j) *\<^sub>R j) = y"
    by (rule euclidean_representation)
  have closed_K: "closed K"
    by (rule compact_imp_closed[OF compact_K])
  have cont_c: "continuous_on UNIV ?c"
    by (rule continuous_on_Pair)
       (rule continuous_on_const,
        rule basis_slice_continuous[OF b])
  have D: "((\<lambda>u. case_prod F (?c u)) has_vector_derivative
      case_prod G (?c ?s)) (at ?s within UNIV)"
    using deriv[OF t, of ?v ?s] pU
    by (simp add: coords)
  have "case_prod G (?c ?s) = 0"
  proof (rule vector_derivative_zero_on_relative_open
      [OF open_U closed_K cont_c])
    show "?s \<in> UNIV" by simp
    show "at ?s within UNIV \<noteq> bot" by simp
    fix u :: real assume "u \<in> UNIV"
    then show "?c u \<in> {0..} \<times> UNIV" using t by simp
  next
    show "?c ?s \<in> U" using pU rep by simp
    show "?c ?s \<notin> K" using pK rep by simp
    show "((\<lambda>u. case_prod F (?c u)) has_vector_derivative
        case_prod G (?c ?s)) (at ?s within UNIV)"
      by (rule D)
    fix p :: "real \<times> 'a"
    assume "p \<in> {0..} \<times> UNIV" "p \<in> U" "p \<notin> K"
    then show "case_prod F p = 0" by (rule zero_F)
  qed
  then show ?thesis using rep by simp
qed

theorem tangential_zero_extension_C1:
  fixes F G :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
    and b :: 'a
  assumes b: "b \<in> Basis"
    and open_U: "open U"
    and compact_K: "compact K"
    and K_chart: "K \<subseteq> ({0..} \<times> UNIV) \<inter> U"
    and zero_F: "\<And>p. p \<in> {0..} \<times> UNIV \<Longrightarrow>
      p \<in> U \<Longrightarrow> p \<notin> K \<Longrightarrow> case_prod F p = 0"
    and deriv_F: "\<And>t v s. 0 \<le> t \<Longrightarrow>
      (t, \<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j) \<in> U \<Longrightarrow>
      ((\<lambda>u. F t (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          G t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (at s)"
    and cont_G: "continuous_on (({0..} \<times> UNIV) \<inter> U)
      (case_prod G)"
  shows "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and>
        case_prod (zero_extend_halfspace U F) p \<noteq> 0})"
    and "continuous_on ({0..} \<times> UNIV)
      (case_prod (zero_extend_halfspace U G))"
    and "\<And>t v s. 0 \<le> t \<Longrightarrow>
      ((\<lambda>u. zero_extend_halfspace U F t
          (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          zero_extend_halfspace U G t
            (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (at s)"
proof -
  let ?H = "{0..} \<times> UNIV :: (real \<times> 'a) set"
  have KU: "K \<subseteq> U" using K_chart by auto
  have E_support: "compact (closure
    {p. p \<in> ?H \<and> (if p \<in> U then case_prod F p else 0) \<noteq> 0})"
    by (rule compact_support_zero_extension_relative
        [OF compact_K zero_F])
  have support_set_eq:
    "{p::real \<times> 'a. 0 \<le> fst p \<and>
        case_prod (zero_extend_halfspace U F) p \<noteq> 0} =
      {p. p \<in> ?H \<and> (if p \<in> U then case_prod F p else 0) \<noteq> 0}"
    by (rule set_eqI) (case_tac x, simp add: zero_extend_halfspace_def)
  show "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and>
        case_prod (zero_extend_halfspace U F) p \<noteq> 0})"
    by (subst support_set_eq, rule E_support)
  have zero_G: "\<And>p. p \<in> ?H \<Longrightarrow> p \<in> U \<Longrightarrow>
      p \<notin> K \<Longrightarrow> case_prod G p = 0"
  proof -
    fix p :: "real \<times> 'a"
    assume H: "p \<in> ?H" and pU: "p \<in> U" and pK: "p \<notin> K"
    obtain t y where p: "p = (t,y)" by (cases p) auto
    have t: "0 \<le> t" using H p by auto
    have "G t y = 0"
      by (rule tangential_local_derivative_zero_outside_support
          [OF b open_U compact_K zero_F deriv_F t])
         (use pU pK p in auto)
    then show "case_prod G p = 0" by (simp add: p)
  qed
  have E_cont: "continuous_on ?H
      (\<lambda>p. if p \<in> U then case_prod G p else 0)"
    by (rule continuous_on_zero_extension_relative
        [OF open_U compact_K KU cont_G zero_G])
  show "continuous_on ?H (case_prod (zero_extend_halfspace U G))"
  proof (rule continuous_on_eq[OF E_cont])
    fix p :: "real \<times> 'a"
    assume "p \<in> ?H"
    show "(if p \<in> U then case_prod G p else 0) =
      case_prod (zero_extend_halfspace U G) p"
      by (cases p) (simp add: zero_extend_halfspace_def)
  qed
  fix t :: real and v :: "'a \<Rightarrow> real" and s :: real
  assume t: "0 \<le> t"
  show "((\<lambda>u. zero_extend_halfspace U F t
        (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
      has_vector_derivative zero_extend_halfspace U G t
        (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (at s)"
    unfolding zero_extend_halfspace_def
    by (rule tangential_zero_extension_derivative
        [OF b open_U compact_K KU zero_F deriv_F t])
qed

theorem Stokes_halfspace_basis_sum_within:
  fixes P P_t :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
    and Q Q_b :: "'a \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real"
  assumes B: "B \<subseteq> Basis"
    and support_P: "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod P p \<noteq> 0})"
    and deriv_P: "\<And>t y. 0 \<le> t \<Longrightarrow>
      ((\<lambda>s. P s y) has_vector_derivative P_t t y)
        (at t within {0..})"
    and cont_P: "continuous_on ({0..} \<times> UNIV) (case_prod P_t)"
    and support_Q: "\<And>b. b \<in> B \<Longrightarrow> compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod (Q b) p \<noteq> 0})"
    and deriv_Q: "\<And>b t v s. b \<in> B \<Longrightarrow> 0 \<le> t \<Longrightarrow>
      ((\<lambda>u. Q b t (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          Q_b b t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (at s)"
    and cont_Q: "\<And>b. b \<in> B \<Longrightarrow>
      continuous_on ({0..} \<times> UNIV) (case_prod (Q_b b))"
  shows "(LINT p : {0..} \<times> UNIV | lborel.
    case_prod (\<lambda>t y. P_t t y - (\<Sum>b\<in>B. Q_b b t y)) p) =
    - (\<integral>y. P 0 y \<partial>lborel)"
proof -
  let ?H = "{0..} \<times> UNIV"
  let ?S = "\<lambda>t y. \<Sum>b\<in>B. Q_b b t y"
  let ?h = "\<lambda>b p. indicator ?H p *\<^sub>R case_prod (Q_b b) p"
  have basis: "\<And>b. b \<in> B \<Longrightarrow> b \<in> Basis"
    using B by auto
  have int_P: "set_integrable lborel ?H (case_prod P_t)"
    by (rule normal_halfspace_derivative_integrable_within
        [OF support_P deriv_P cont_P])
  have int_Q: "\<And>b. b \<in> B \<Longrightarrow>
      set_integrable lborel ?H (case_prod (Q_b b))"
  proof -
    fix b assume bB: "b \<in> B"
    show "set_integrable lborel ?H (case_prod (Q_b b))"
      by (rule tangential_halfspace_derivative_integrable_basis
          [OF basis[OF bB] support_Q[OF bB]])
         (use deriv_Q[OF bB] cont_Q[OF bB] in auto)
  qed
  have h_int: "\<And>b. b \<in> B \<Longrightarrow> integrable lborel (?h b)"
    using int_Q by (simp add: set_integrable_def)
  have fun_eq: "(\<lambda>p. indicator ?H p *\<^sub>R case_prod ?S p) =
      (\<lambda>p. \<Sum>b\<in>B. ?h b p)"
    by (rule ext) (auto simp: split_def sum_distrib_left)
  have int_S: "set_integrable lborel ?H (case_prod ?S)"
    unfolding set_integrable_def fun_eq
    by (rule Bochner_Integration.integrable_sum[OF h_int])
  have sum_zero: "(LINT p : ?H | lborel. case_prod ?S p) = 0"
  proof -
    have "(LINT p : ?H | lborel. case_prod ?S p) =
        (\<Sum>b\<in>B. \<integral>p. ?h b p \<partial>lborel)"
      unfolding set_lebesgue_integral_def fun_eq
      by (rule Bochner_Integration.integral_sum[OF h_int])
    also have "\<dots> = 0"
    proof -
      have each: "\<And>b. b \<in> B \<Longrightarrow>
          (\<integral>p. ?h b p \<partial>lborel) = 0"
      proof -
        fix b assume bB: "b \<in> B"
        show "(\<integral>p. ?h b p \<partial>lborel) = 0"
          using tangential_halfspace_integral_zero_basis_C1
            [OF basis[OF bB] support_Q[OF bB]]
            deriv_Q[OF bB] cont_Q[OF bB]
          by (simp add: set_lebesgue_integral_def)
      qed
      show ?thesis
        by (rule sum.neutral) (intro ballI, rule each)
    qed
    finally show ?thesis .
  qed
  have split: "(LINT p : ?H | lborel.
      case_prod (\<lambda>t y. P_t t y - ?S t y) p) =
    (LINT p : ?H | lborel. case_prod P_t p) -
    (LINT p : ?H | lborel. case_prod ?S p)"
    using int_P int_S
    by (simp add: set_lebesgue_integral_def set_integrable_def
      algebra_simps split_def)
  have normal: "(LINT p : ?H | lborel. case_prod P_t p) =
      - (\<integral>y. P 0 y \<partial>lborel)"
    by (rule normal_halfspace_FTC_within[OF support_P deriv_P cont_P])
  show ?thesis using split normal sum_zero by simp
qed


end
