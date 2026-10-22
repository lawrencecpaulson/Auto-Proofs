theory Stokes_One_Dimensional_Chain
  imports Stokes_Halfline_Forms
begin

text \<open>
  A finite oriented interval presentation includes subdivided intervals
  and circles. Its boundary incidence counts terminal endpoints
  positively and initial endpoints negatively. At an interior vertex
  one incoming and one outgoing interval cancel.
\<close>

definition one_chain_vertices ::
    "'e set \<Rightarrow> ('e \<Rightarrow> 'v) \<Rightarrow>
      ('e \<Rightarrow> 'v) \<Rightarrow> 'v set"
  where "one_chain_vertices E src dst =
    src ` E \<union> dst ` E"

definition one_chain_incidence ::
    "'e set \<Rightarrow> ('e \<Rightarrow> 'v) \<Rightarrow>
      ('e \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> real"
  where "one_chain_incidence E src dst v =
    (\<Sum>e\<in>E. if dst e = v then 1 else 0) -
    (\<Sum>e\<in>E. if src e = v then 1 else 0)"

definition one_chain_boundary ::
    "'e set \<Rightarrow> ('e \<Rightarrow> 'v) \<Rightarrow>
      ('e \<Rightarrow> 'v) \<Rightarrow> 'v set"
  where "one_chain_boundary E src dst =
    {v\<in>one_chain_vertices E src dst.
      one_chain_incidence E src dst v \<noteq> 0}"

lemma one_chain_vertices_finite:
  "finite E \<Longrightarrow> finite (one_chain_vertices E src dst)"
  by (simp add: one_chain_vertices_def)

lemma one_chain_incidence_count:
  assumes finite: "finite E"
  shows "one_chain_incidence E src dst v =
    real (card {e\<in>E. dst e = v}) -
    real (card {e\<in>E. src e = v})"
proof -
  have dst:
      "(\<Sum>e\<in>E. if dst e = v then 1::real else 0) =
        real (card {e\<in>E. dst e = v})"
  proof -
    have "(\<Sum>e\<in>E.
        if dst e = v then 1::real else 0) =
      (\<Sum>e\<in>{e\<in>E. dst e = v}.
        if dst e = v then 1 else 0)"
      by (rule sum.mono_neutral_right[OF finite])
         auto
    then show ?thesis by simp
  qed
  have src:
      "(\<Sum>e\<in>E. if src e = v then 1::real else 0) =
        real (card {e\<in>E. src e = v})"
  proof -
    have "(\<Sum>e\<in>E.
        if src e = v then 1::real else 0) =
      (\<Sum>e\<in>{e\<in>E. src e = v}.
        if src e = v then 1 else 0)"
      by (rule sum.mono_neutral_right[OF finite])
         auto
    then show ?thesis by simp
  qed
  show ?thesis
    by (simp add: one_chain_incidence_def dst src)
qed

lemma one_chain_endpoint_sum:
  assumes finite: "finite E"
  shows "(\<Sum>e\<in>E. omega (dst e) - omega (src e)) =
    finite_boundary_zero_integral
      (one_chain_boundary E src dst)
      (\<lambda>v. one_chain_incidence E src dst v * omega v)"
proof -
  let ?V = "one_chain_vertices E src dst"
  let ?B = "one_chain_boundary E src dst"
  have finiteV: "finite ?V"
    by (rule one_chain_vertices_finite[OF finite])
  have dst_group:
      "(\<Sum>e\<in>E. omega (dst e)) =
      (\<Sum>v\<in>?V.
        (\<Sum>e\<in>E. if dst e = v then 1 else 0) *
          omega v)"
  proof -
    have each: "(\<Sum>v\<in>?V.
        (if dst e = v then 1 else 0) * omega v) =
      omega (dst e)" if "e \<in> E" for e
    proof -
      have "(\<Sum>v\<in>?V.
          (if dst e = v then 1 else 0) * omega v) =
        (\<Sum>v\<in>?V.
          if dst e = v then omega v else 0)"
        by (rule sum.cong[OF refl]) simp
      also have "\<dots> = omega (dst e)"
        using finiteV that
        by (simp add: one_chain_vertices_def
          sum.delta'[OF finiteV])
      finally show ?thesis .
    qed
    show ?thesis
      using each finite finiteV
      by (simp add: sum_distrib_right sum.swap)
  qed
  have src_group:
      "(\<Sum>e\<in>E. omega (src e)) =
      (\<Sum>v\<in>?V.
        (\<Sum>e\<in>E. if src e = v then 1 else 0) *
          omega v)"
  proof -
    have each: "(\<Sum>v\<in>?V.
        (if src e = v then 1 else 0) * omega v) =
      omega (src e)" if "e \<in> E" for e
    proof -
      have "(\<Sum>v\<in>?V.
          (if src e = v then 1 else 0) * omega v) =
        (\<Sum>v\<in>?V.
          if src e = v then omega v else 0)"
        by (rule sum.cong[OF refl]) simp
      also have "\<dots> = omega (src e)"
        using finiteV that
        by (simp add: one_chain_vertices_def
          sum.delta'[OF finiteV])
      finally show ?thesis .
    qed
    show ?thesis
      using each finite finiteV
      by (simp add: sum_distrib_right sum.swap)
  qed
  have all: "(\<Sum>e\<in>E.
      omega (dst e) - omega (src e)) =
    (\<Sum>v\<in>?V.
      one_chain_incidence E src dst v * omega v)"
    using dst_group src_group
    by (simp add: one_chain_incidence_def
      sum_subtractf algebra_simps)
  have boundary:
      "(\<Sum>v\<in>?V.
        one_chain_incidence E src dst v * omega v) =
      (\<Sum>v\<in>?B.
        one_chain_incidence E src dst v * omega v)"
    by (rule sum.mono_neutral_right[OF finiteV])
       (auto simp: one_chain_boundary_def)
  show ?thesis
    using all boundary
    by (simp add: finite_boundary_zero_integral_def)
qed

theorem Stokes_one_dimensional_finite_chain:
  fixes F :: "'e \<Rightarrow> real \<Rightarrow> real"
    and dF :: "'e \<Rightarrow> real \<Rightarrow> real"
  assumes finite: "finite E"
    and ab: "\<And>e. e \<in> E \<Longrightarrow> a e \<le> b e"
    and deriv: "\<And>e t. e \<in> E \<Longrightarrow>
      t \<in> {a e..b e} \<Longrightarrow>
      ((F e) has_vector_derivative dF e t)
        (at t within {a e..b e})"
    and cont: "\<And>e. e \<in> E \<Longrightarrow>
      continuous_on {a e..b e} (dF e)"
    and src_value: "\<And>e. e \<in> E \<Longrightarrow>
      F e (a e) = omega (src e)"
    and dst_value: "\<And>e. e \<in> E \<Longrightarrow>
      F e (b e) = omega (dst e)"
  shows "(\<Sum>e\<in>E.
      (LINT t : {a e..b e} | lborel. dF e t)) =
    finite_boundary_zero_integral
      (one_chain_boundary E src dst)
      (\<lambda>v. one_chain_incidence E src dst v * omega v)"
proof -
  have local: "(LINT t : {a e..b e} | lborel.
      dF e t) = F e (b e) - F e (a e)"
    if e: "e \<in> E" for e
    unfolding set_lebesgue_integral_def
    by (rule integral_FTC_atLeastAtMost[OF ab[OF e]])
       (use deriv[OF e] cont[OF e] in auto)
  have body: "(\<Sum>e\<in>E.
      (LINT t : {a e..b e} | lborel. dF e t)) =
    (\<Sum>e\<in>E.
      omega (dst e) - omega (src e))"
    by (rule sum.cong[OF refl])
       (use local src_value dst_value in auto)
  show ?thesis
    using body one_chain_endpoint_sum[OF finite,
      of omega dst src]
    by simp
qed

corollary Stokes_one_dimensional_closed_chain:
  fixes F :: "'e \<Rightarrow> real \<Rightarrow> real"
    and dF :: "'e \<Rightarrow> real \<Rightarrow> real"
  assumes finite: "finite E"
    and ab: "\<And>e. e \<in> E \<Longrightarrow> a e \<le> b e"
    and deriv: "\<And>e t. e \<in> E \<Longrightarrow>
      t \<in> {a e..b e} \<Longrightarrow>
      ((F e) has_vector_derivative dF e t)
        (at t within {a e..b e})"
    and cont: "\<And>e. e \<in> E \<Longrightarrow>
      continuous_on {a e..b e} (dF e)"
    and src_value: "\<And>e. e \<in> E \<Longrightarrow>
      F e (a e) = omega (src e)"
    and dst_value: "\<And>e. e \<in> E \<Longrightarrow>
      F e (b e) = omega (dst e)"
    and balance: "\<And>v. v \<in> one_chain_vertices E src dst
      \<Longrightarrow> one_chain_incidence E src dst v = 0"
  shows "(\<Sum>e\<in>E.
      (LINT t : {a e..b e} | lborel. dF e t)) = 0"
proof -
  have empty: "one_chain_boundary E src dst = {}"
    using balance
    by (auto simp: one_chain_boundary_def)
  show ?thesis
    using Stokes_one_dimensional_finite_chain
      [where E=E and a=a and b=b and F=F and dF=dF
        and omega=omega and src=src and dst=dst,
        OF finite ab deriv cont src_value dst_value]
    by (simp add: empty finite_boundary_zero_integral_def)
qed

corollary Stokes_line_form_C1_zero_integral:
  fixes F :: "real \<Rightarrow> real"
  assumes deriv: "\<And>t. F differentiable (at t)"
    and cont: "continuous_on UNIV
      (halfline_exterior_one F)"
    and support: "compact (closure {t. F t \<noteq> 0})"
  shows "(LINT t : UNIV | lborel.
      halfline_exterior_one F t) = 0"
proof -
  have bounded: "bounded (closure {t. F t \<noteq> 0})"
    by (rule compact_imp_bounded[OF support])
  obtain R where R: "0 < R"
    and bound: "closure {t. F t \<noteq> 0}
      \<subseteq> ball 0 R"
    using bounded_subset_ballD[OF bounded, of 0]
    by auto
  have zero_F: "F t = 0" if "t \<notin> {-R..R}"
    for t
  proof (rule ccontr)
    assume "F t \<noteq> 0"
    then have "t \<in> closure {s. F s \<noteq> 0}"
      by (intro subsetD[OF closure_subset]) simp
    then have "t \<in> ball 0 R"
      using bound by auto
    then show False
      using that by auto
  qed
  have end_zero: "F R = 0" "F (-R) = 0"
  proof -
    have "R \<notin> ball 0 R" "-R \<notin> ball 0 R"
      using R by simp_all
    then show "F R = 0" "F (-R) = 0"
      using bound closure_subset[of "{t. F t \<noteq> 0}"]
      by auto
  qed
  have D: "(F has_vector_derivative
      halfline_exterior_one F t) (at t)"
    for t
    using deriv[of t]
    by (simp add: halfline_exterior_one_def
      vector_derivative_works)
  have zero_d: "halfline_exterior_one F t = 0"
    if "t \<notin> {-R..R}" for t
    by (rule vector_derivative_zero_off_closed_interval
      [OF D that zero_F])
  have restrict:
      "(LINT t : UNIV | lborel.
        halfline_exterior_one F t) =
       (LINT t : {-R..R} | lborel.
        halfline_exterior_one F t)"
    by (rule set_lebesgue_integral_restrict_support)
       (use zero_d in auto)
  have FTC: "(LINT t : {-R..R} | lborel.
      halfline_exterior_one F t) = F R - F (-R)"
    unfolding set_lebesgue_integral_def
  proof (rule integral_FTC_atLeastAtMost)
    show "- R \<le> R" using R by simp
    show "(F has_vector_derivative
        halfline_exterior_one F t)
        (at t within {-R..R})"
      if "- R \<le> t" "t \<le> R" for t
      by (rule has_vector_derivative_at_within[OF D])
    show "continuous_on {-R..R}
        (halfline_exterior_one F)"
      by (rule continuous_on_subset[OF cont]) simp
  qed
  show ?thesis using restrict FTC end_zero by simp
qed

corollary Stokes_compact_interval_form_C1:
  fixes F :: "real \<Rightarrow> real"
  assumes ab: "a < b"
    and deriv: "\<And>t. t \<in> {a..b} \<Longrightarrow>
      (F has_vector_derivative f t)
        (at t within {a..b})"
    and cont: "continuous_on {a..b} f"
  shows "(LINT t : {a..b} | lborel. f t) =
    finite_boundary_zero_integral {a,b}
      (\<lambda>t. if t = a then - F a else F b)"
proof -
  have FTC: "(LINT t : {a..b} | lborel. f t) =
      F b - F a"
    unfolding set_lebesgue_integral_def
    by (rule integral_FTC_atLeastAtMost)
       (use ab deriv cont in auto)
  show ?thesis
    using FTC ab
    by (simp add: finite_boundary_zero_integral_def)
qed

corollary Stokes_periodic_interval_form_C1:
  fixes F :: "real \<Rightarrow> real"
  assumes ab: "a \<le> b"
    and deriv: "\<And>t. t \<in> {a..b} \<Longrightarrow>
      (F has_vector_derivative f t)
        (at t within {a..b})"
    and cont: "continuous_on {a..b} f"
    and periodic: "F a = F b"
  shows "(LINT t : {a..b} | lborel. f t) = 0"
proof -
  have FTC: "(LINT t : {a..b} | lborel. f t) =
      F b - F a"
    unfolding set_lebesgue_integral_def
    by (rule integral_FTC_atLeastAtMost[OF ab])
       (use deriv cont in auto)
  show ?thesis using FTC periodic by simp
qed

definition one_chain_global_incidence ::
    "'e set \<Rightarrow> ('e \<Rightarrow> 'v) \<Rightarrow>
      ('e \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> real"
  where "one_chain_global_incidence E src dst v =
    real (card {e\<in>E. dst e = v}) -
    real (card {e\<in>E. src e = v})"

definition one_chain_boundary_on_active ::
    "'e set \<Rightarrow> 'e set \<Rightarrow>
      ('e \<Rightarrow> 'v) \<Rightarrow>
      ('e \<Rightarrow> 'v) \<Rightarrow> 'v set"
  where "one_chain_boundary_on_active E F src dst =
    {v\<in>one_chain_vertices F src dst.
      one_chain_global_incidence E src dst v \<noteq> 0}"

theorem Stokes_one_dimensional_compactly_supported_chain:
  fixes G :: "'e \<Rightarrow> real \<Rightarrow> real"
    and dG :: "'e \<Rightarrow> real \<Rightarrow> real"
  assumes finite: "finite F"
    and FE: "F \<subseteq> E"
    and ab: "\<And>e. e \<in> E \<Longrightarrow> a e \<le> b e"
    and deriv: "\<And>e t. e \<in> F \<Longrightarrow>
      t \<in> {a e..b e} \<Longrightarrow>
      ((G e) has_vector_derivative dG e t)
        (at t within {a e..b e})"
    and cont: "\<And>e. e \<in> F \<Longrightarrow>
      continuous_on {a e..b e} (dG e)"
    and src_value: "\<And>e. e \<in> E \<Longrightarrow>
      G e (a e) = omega (src e)"
    and dst_value: "\<And>e. e \<in> E \<Longrightarrow>
      G e (b e) = omega (dst e)"
    and inactive: "\<And>e t. e \<in> E \<Longrightarrow>
      e \<notin> F \<Longrightarrow> t \<in> {a e..b e}
      \<Longrightarrow> G e t = 0"
  shows "(\<Sum>e\<in>F.
      (LINT t : {a e..b e} | lborel. dG e t)) =
    finite_boundary_zero_integral
      (one_chain_boundary_on_active E F src dst)
      (\<lambda>v. one_chain_global_incidence E src dst v *
        omega v)"
proof -
  let ?V = "one_chain_vertices F src dst"
  let ?BF = "one_chain_boundary F src dst"
  let ?B = "one_chain_boundary_on_active E F src dst"
  have finiteV: "finite ?V"
    by (rule one_chain_vertices_finite[OF finite])
  have active_body: "(\<Sum>e\<in>F.
      (LINT t : {a e..b e} | lborel. dG e t)) =
    finite_boundary_zero_integral ?BF
      (\<lambda>v. one_chain_incidence F src dst v * omega v)"
    by (rule Stokes_one_dimensional_finite_chain
      [OF finite _ deriv cont])
       (use FE ab src_value dst_value in auto)
  have coeff:
      "one_chain_incidence F src dst v * omega v =
      one_chain_global_incidence E src dst v * omega v"
    for v
  proof (cases "omega v = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have dstset: "{e\<in>E. dst e = v} =
        {e\<in>F. dst e = v}"
    proof
      show "{e\<in>E. dst e = v} \<subseteq>
        {e\<in>F. dst e = v}"
      proof
        fix e assume e: "e \<in> {e\<in>E. dst e = v}"
        have "e \<in> F"
        proof (rule ccontr)
          assume "e \<notin> F"
          then have "G e (b e) = 0"
            using inactive[of e "b e"] e ab[of e]
            by auto
          then show False
            using dst_value[of e] e False by auto
        qed
        with e show "e \<in> {e\<in>F. dst e = v}"
          by simp
      qed
      show "{e\<in>F. dst e = v} \<subseteq>
        {e\<in>E. dst e = v}"
        using FE by auto
    qed
    have srcset: "{e\<in>E. src e = v} =
        {e\<in>F. src e = v}"
    proof
      show "{e\<in>E. src e = v} \<subseteq>
        {e\<in>F. src e = v}"
      proof
        fix e assume e: "e \<in> {e\<in>E. src e = v}"
        have "e \<in> F"
        proof (rule ccontr)
          assume "e \<notin> F"
          then have "G e (a e) = 0"
            using inactive[of e "a e"] e ab[of e]
            by auto
          then show False
            using src_value[of e] e False by auto
        qed
        with e show "e \<in> {e\<in>F. src e = v}"
          by simp
      qed
      show "{e\<in>F. src e = v} \<subseteq>
        {e\<in>E. src e = v}"
        using FE by auto
    qed
    show ?thesis
      by (simp add: one_chain_incidence_count[OF finite]
        one_chain_global_incidence_def dstset srcset)
  qed
  have restrictF: "(\<Sum>v\<in>?BF.
      one_chain_incidence F src dst v * omega v) =
    (\<Sum>v\<in>?V.
      one_chain_incidence F src dst v * omega v)"
    by (rule sum.mono_neutral_right[OF finiteV,
      symmetric])
       (auto simp: one_chain_boundary_def)
  have restrictE: "(\<Sum>v\<in>?V.
      one_chain_global_incidence E src dst v * omega v) =
    (\<Sum>v\<in>?B.
      one_chain_global_incidence E src dst v * omega v)"
    by (rule sum.mono_neutral_right[OF finiteV])
       (auto simp: one_chain_boundary_on_active_def)
  have sum_coeff: "(\<Sum>v\<in>?V.
      one_chain_incidence F src dst v * omega v) =
    (\<Sum>v\<in>?V.
      one_chain_global_incidence E src dst v * omega v)"
    by (rule sum.cong[OF refl]) (rule coeff)
  show ?thesis
    using active_body restrictF restrictE sum_coeff
    by (simp only: finite_boundary_zero_integral_def)
qed

end
