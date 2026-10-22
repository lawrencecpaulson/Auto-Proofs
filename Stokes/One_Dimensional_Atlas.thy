theory One_Dimensional_Atlas
  imports Chart_Local One_Dimensional_Chain
begin

lemma halfline_FTC_compact_support_within:
  fixes F f :: "real \<Rightarrow> real"
  assumes deriv: "\<And>t. 0 \<le> t \<Longrightarrow>
      (F has_vector_derivative f t) (at t within {0..})"
    and cont: "continuous_on {0..} f"
    and support: "compact (closure
      {t. 0 \<le> t \<and> F t \<noteq> 0})"
  shows "(LINT t : {0..} | lborel. f t) = - F 0"
proof -
  let ?S = "{t. 0 \<le> t \<and> F t \<noteq> 0}"
  have bounded: "bounded (closure ?S)"
    by (rule compact_imp_bounded[OF support])
  obtain R where R: "0 < R"
    and bound: "closure ?S \<subseteq> ball 0 R"
    using bounded_subset_ballD[OF bounded, of 0]
    by auto
  have zero_F: "F t = 0" if "R \<le> t" for t
  proof (rule ccontr)
    assume "F t \<noteq> 0"
    then have "t \<in> closure ?S"
      using that R closure_subset[of ?S]
      by auto
    then have "t \<in> ball 0 R"
      using bound by auto
    then show False
      using that by (simp add: dist_real_def)
  qed
  have deriv_box: "(F has_vector_derivative f t)
      (at t within {0..R})"
    if t: "t \<in> {0..R}" for t
    by (rule has_vector_derivative_within_subset
      [OF deriv[of t]])
       (use t in auto)
  have cont_box: "continuous_on {0..R} f"
    by (rule continuous_on_subset[OF cont]) auto
  have deriv_tail: "(F has_vector_derivative f t)
      (at t)"
    if t: "R < t" for t
  proof -
    have at: "at t within {0..} = at t"
      by (rule at_within_open_subset
        [where S="{0<..}"])
         (use R t in auto)
    show ?thesis
      using deriv[of t] R t
      by (simp add: at)
  qed
  show ?thesis
    by (rule halfline_FTC_from_coefficient_support
      [OF less_imp_le[OF R] deriv_box cont_box
        zero_F deriv_tail])
qed

theorem Stokes_one_dimensional_chart_C1:
  fixes F g :: "real \<Rightarrow> real"
  assumes openC: "openin (top_of_set {0::real..}) C"
    and compactK: "compact K"
    and KC: "K \<subseteq> C"
    and zeroF: "\<And>t. t \<in> C \<Longrightarrow>
      t \<notin> K \<Longrightarrow> F t = 0"
    and deriv: "\<And>t. t \<in> C \<Longrightarrow>
      (F has_vector_derivative g t)
        (at t within {0..})"
    and cont: "continuous_on C g"
  shows "(LINT t : C | lborel. g t) =
    finite_boundary_zero_integral
      ({0::real} \<inter> C) (\<lambda>_. - F 0)"
proof -
  obtain U where openU: "open U"
    and C: "C = {0..} \<inter> U"
    using openC by (auto simp: openin_open)
  have KU: "K \<subseteq> U"
    using KC C by auto
  have closedK: "closed K"
    by (rule compact_imp_closed[OF compactK])
  let ?E = "\<lambda>t. if t \<in> U then F t else 0"
  let ?dE = "\<lambda>t. if t \<in> U then g t else 0"
  have zeroU: "F t = 0"
    if "t \<in> {0..}" "t \<in> U" "t \<notin> K"
    for t
    by (rule zeroF)
       (use that C in auto)
  have cont_id: "continuous_on UNIV (id::real \<Rightarrow> real)"
    by (rule continuous_on_id')
  have dE: "(?E has_vector_derivative ?dE t)
      (at t within {0..})"
    if t: "0 \<le> t" for t
  proof -
    have raw: "((\<lambda>s. if id s \<in> U then F (id s) else 0)
        has_vector_derivative
        (if id t \<in> U then g (id t) else 0))
        (at t within {0..})"
      by (rule zero_extend_vector_derivative_along
        [where c=id and H="{0..}" and S="{0..}"
          and K=K and U=U and F=F and g=g,
          OF openU closedK KU cont_id])
         (use t deriv C zeroU in auto)
    have fun_eq:
        "(\<lambda>s. if id s \<in> U then F (id s) else 0) =
        ?E"
      by (rule ext) (simp add: id_def)
    have val_eq:
        "(if id t \<in> U then g (id t) else 0) = ?dE t"
      by (simp add: id_def)
    show ?thesis
      using raw by (simp only: fun_eq val_eq)
  qed
  have zero_g: "g t = 0"
    if t: "t \<in> C" "t \<notin> K" for t
  proof -
    have tH: "0 \<le> t"
      using t C by auto
    have fun_eq: "(\<lambda>s. F (id s)) = F"
      by (rule ext) (simp add: id_def)
    have raw_deriv:
        "((\<lambda>s. F (id s)) has_vector_derivative g t)
          (at t within {0..})"
      using deriv[OF t(1)] by (simp only: fun_eq)
    show ?thesis
      by (rule vector_derivative_zero_on_relative_open
        [where c=id and H="{0..}" and U=U and
          K=K and S="{0..}" and F=F and t=t,
          OF openU closedK cont_id])
         (use t tH C zeroU raw_deriv
           at_halfline_not_bot[OF tH] in auto)
  qed
  have cont_dE: "continuous_on {0..} ?dE"
    by (rule continuous_on_zero_extension_relative
      [OF openU compactK KU])
       (use cont C zero_g zeroU in auto)
  have supportE: "compact (closure
      {t. 0 \<le> t \<and> ?E t \<noteq> 0})"
  proof -
    have raw: "compact (closure
        {t. t \<in> {0..} \<and>
          (if t \<in> U then F t else 0) \<noteq> 0})"
      by (rule compact_support_zero_extension_relative
        [OF compactK])
         (use zeroU in auto)
    show ?thesis using raw by simp
  qed
  have FTC: "(LINT t : {0..} | lborel.
      ?dE t) = - ?E 0"
    by (rule halfline_FTC_compact_support_within
      [OF dE cont_dE supportE])
  have integral: "(LINT t : {0..} | lborel.
      ?dE t) = (LINT t : C | lborel. g t)"
    using set_integral_zero_extension
      [where H="{0..}" and U=U and f=g and M=lborel]
    by (simp add: C)
  have boundary:
      "finite_boundary_zero_integral
        ({0::real} \<inter> C) (\<lambda>_. - F 0) = - ?E 0"
    by (auto simp: finite_boundary_zero_integral_def C)
  show ?thesis
    using FTC integral boundary by simp
qed

lemma one_dimensional_boundary_partition_sum:
  fixes eps :: "'i \<Rightarrow> real"
    and sigma :: "'v \<Rightarrow> real"
    and phi :: "'i \<Rightarrow> 'v \<Rightarrow> real"
    and omega :: "'v \<Rightarrow> real"
  assumes finiteF: "finite F"
    and finiteB: "finite B"
    and face_point: "\<And>i. i \<in> F \<Longrightarrow>
      face i \<Longrightarrow> point i \<in> B"
    and sign: "\<And>i. i \<in> F \<Longrightarrow>
      face i \<Longrightarrow>
      eps i = sigma (point i)"
    and unity: "\<And>p. p \<in> B \<Longrightarrow>
      omega p \<noteq> 0 \<Longrightarrow>
      (\<Sum>i\<in>F.
        if face i \<and> point i = p then phi i p else 0) = 1"
  shows "(\<Sum>i\<in>F.
      if face i then
        - eps i * phi i (point i) * omega (point i)
      else 0) =
    finite_boundary_zero_integral B
      (\<lambda>p. - sigma p * omega p)"
proof -
  have each:
      "(if face i then
          - eps i * phi i (point i) * omega (point i)
        else 0) =
      (\<Sum>p\<in>B.
        if face i \<and> point i = p then
          - sigma p * phi i p * omega p
        else 0)"
    if i: "i \<in> F" for i
  proof (cases "face i")
    case True
    have pB: "point i \<in> B"
      by (rule face_point[OF i True])
    have eps: "eps i = sigma (point i)"
      by (rule sign[OF i True])
    show ?thesis
      using finiteB pB True eps
      by (simp add: sum.delta'[OF finiteB])
  next
    case False
    then show ?thesis by simp
  qed
  have first: "(\<Sum>i\<in>F.
      if face i then
        - eps i * phi i (point i) * omega (point i)
      else 0) =
    (\<Sum>p\<in>B.
      (\<Sum>i\<in>F.
        if face i \<and> point i = p then
          - sigma p * phi i p * omega p
        else 0))"
  proof -
    have eq: "(\<Sum>i\<in>F.
        if face i then
          - eps i * phi i (point i) * omega (point i)
        else 0) =
      (\<Sum>i\<in>F.
        (\<Sum>p\<in>B.
          if face i \<and> point i = p then
            - sigma p * phi i p * omega p
          else 0))"
      by (rule sum.cong[OF refl]) (rule each)
    have swap:
      "(\<Sum>i\<in>F.
        (\<Sum>p\<in>B.
          if face i \<and> point i = p then
            - sigma p * phi i p * omega p
          else 0)) =
      (\<Sum>p\<in>B.
        (\<Sum>i\<in>F.
          if face i \<and> point i = p then
            - sigma p * phi i p * omega p
          else 0))"
      by (rule sum.swap)
    show ?thesis
      using eq swap by simp
  qed
  have second:
      "(\<Sum>i\<in>F.
        if face i \<and> point i = p then
          - sigma p * phi i p * omega p
        else 0) =
      - sigma p * omega p"
    if p: "p \<in> B" for p
  proof -
    have pointwise: "(if face i \<and> point i = p then
          - sigma p * phi i p * omega p
        else 0) =
      (- sigma p * omega p) *
        (if face i \<and> point i = p then phi i p else 0)"
      for i
      by (cases "face i \<and> point i = p")
         (auto simp: algebra_simps)
    have eq: "(\<Sum>i\<in>F.
        if face i \<and> point i = p then
          - sigma p * phi i p * omega p
        else 0) =
      (- sigma p * omega p) *
        (\<Sum>i\<in>F.
          if face i \<and> point i = p then phi i p else 0)"
      by (simp add: pointwise sum_distrib_left)
    show ?thesis
    proof (cases "omega p = 0")
      case True
      then show ?thesis using eq by simp
    next
      case False
      then show ?thesis
        using eq unity[OF p False] by simp
    qed
  qed
  show ?thesis
    using first
    by (simp add: finite_boundary_zero_integral_def
      sum.cong[OF refl, OF second])
qed

end
