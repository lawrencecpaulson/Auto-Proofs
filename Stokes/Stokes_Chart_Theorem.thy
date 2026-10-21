theory Stokes_Chart_Theorem
  imports Stokes_Chart_Local
begin

text \<open>
  The chart image is the relatively open set
  \<open>({0..} \<times> UNIV) \<inter> U\<close>, where \<open>U\<close> is ambient open.
  Each coefficient vanishes outside a compact subset of that image.
  The normal derivative at the boundary is one-sided.
\<close>

theorem Stokes_relatively_open_chart_C1:
  fixes P P_t :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
    and Q Q_b :: "'a \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real"
    and K_P :: "(real \<times> 'a) set"
    and K_Q :: "'a \<Rightarrow> (real \<times> 'a) set"
  assumes B: "B \<subseteq> Basis"
    and open_U: "open U"
    and compact_P: "compact K_P"
    and K_P_chart: "K_P \<subseteq> (({0..} \<times> UNIV) \<inter> U)"
    and zero_P: "\<And>p. p \<in> {0..} \<times> UNIV \<Longrightarrow>
      p \<in> U \<Longrightarrow> p \<notin> K_P \<Longrightarrow> case_prod P p = 0"
    and deriv_P: "\<And>t y. 0 \<le> t \<Longrightarrow> (t,y) \<in> U \<Longrightarrow>
      ((\<lambda>s. P s y) has_vector_derivative P_t t y)
        (at t within {0..})"
    and cont_P: "continuous_on (({0..} \<times> UNIV) \<inter> U)
      (case_prod P_t)"
    and compact_Q: "\<And>b. b \<in> B \<Longrightarrow> compact (K_Q b)"
    and K_Q_chart: "\<And>b. b \<in> B \<Longrightarrow>
      K_Q b \<subseteq> (({0..} \<times> UNIV) \<inter> U)"
    and zero_Q: "\<And>b p. b \<in> B \<Longrightarrow>
      p \<in> {0..} \<times> UNIV \<Longrightarrow> p \<in> U \<Longrightarrow>
      p \<notin> K_Q b \<Longrightarrow> case_prod (Q b) p = 0"
    and deriv_Q: "\<And>b t v s. b \<in> B \<Longrightarrow> 0 \<le> t \<Longrightarrow>
      (t, \<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j) \<in> U \<Longrightarrow>
      ((\<lambda>u. Q b t (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          Q_b b t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (at s)"
    and cont_Q: "\<And>b. b \<in> B \<Longrightarrow>
      continuous_on (({0..} \<times> UNIV) \<inter> U)
        (case_prod (Q_b b))"
  shows "(LINT p : ({0..} \<times> UNIV) \<inter> U | lborel.
      case_prod (\<lambda>t y.
        P_t t y - (\<Sum>b\<in>B. Q_b b t y)) p) =
    - (LINT y : {y. (0,y) \<in> U} | lborel. P 0 y)"
proof -
  let ?H = "{0..} \<times> UNIV"
  let ?EP = "zero_extend_halfspace U P"
  let ?EP_t = "zero_extend_halfspace U P_t"
  let ?EQ = "\<lambda>b. zero_extend_halfspace U (Q b)"
  let ?EQ_b = "\<lambda>b. zero_extend_halfspace U (Q_b b)"
  have basis: "\<And>b. b \<in> B \<Longrightarrow> b \<in> Basis"
    using B by auto
  have EP_support: "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod ?EP p \<noteq> 0})"
    by (rule normal_zero_extension_C1(1)
        [OF open_U compact_P K_P_chart zero_P deriv_P cont_P])
  have EP_cont: "continuous_on ?H (case_prod ?EP_t)"
    by (rule normal_zero_extension_C1(2)
        [OF open_U compact_P K_P_chart zero_P deriv_P cont_P])
  have EP_deriv: "\<And>t y. 0 \<le> t \<Longrightarrow>
      ((\<lambda>s. ?EP s y) has_vector_derivative ?EP_t t y)
        (at t within {0..})"
    by (rule normal_zero_extension_C1(3)
        [OF open_U compact_P K_P_chart zero_P deriv_P cont_P])
  have EQ_support: "\<And>b. b \<in> B \<Longrightarrow> compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod (?EQ b) p \<noteq> 0})"
  proof -
    fix b assume bB: "b \<in> B"
    show "compact (closure
        {p::real \<times> 'a. 0 \<le> fst p \<and>
          case_prod (?EQ b) p \<noteq> 0})"
      by (rule tangential_zero_extension_C1(1)
          [OF basis[OF bB] open_U compact_Q[OF bB]
            K_Q_chart[OF bB] zero_Q[OF bB]
            deriv_Q[OF bB] cont_Q[OF bB]])
  qed
  have EQ_cont: "\<And>b. b \<in> B \<Longrightarrow>
      continuous_on ?H (case_prod (?EQ_b b))"
  proof -
    fix b assume bB: "b \<in> B"
    show "continuous_on ?H (case_prod (?EQ_b b))"
      by (rule tangential_zero_extension_C1(2)
          [OF basis[OF bB] open_U compact_Q[OF bB]
            K_Q_chart[OF bB] zero_Q[OF bB]
            deriv_Q[OF bB] cont_Q[OF bB]])
  qed
  have EQ_deriv: "\<And>b t v s. b \<in> B \<Longrightarrow> 0 \<le> t \<Longrightarrow>
      ((\<lambda>u. ?EQ b t (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          ?EQ_b b t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (at s)"
  proof -
    fix b :: 'a and t :: real and v :: "'a \<Rightarrow> real"
      and s :: real
    assume bB: "b \<in> B" and t: "0 \<le> t"
    show "((\<lambda>u. ?EQ b t (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          ?EQ_b b t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (at s)"
      by (rule tangential_zero_extension_C1(3)
          [OF basis[OF bB] open_U compact_Q[OF bB]
            K_Q_chart[OF bB] zero_Q[OF bB]
            deriv_Q[OF bB] cont_Q[OF bB] t])
  qed
  have E_stokes: "(LINT p : ?H | lborel.
      case_prod (\<lambda>t y.
        ?EP_t t y - (\<Sum>b\<in>B. ?EQ_b b t y)) p) =
      - (\<integral>y. ?EP 0 y \<partial>lborel)"
    by (rule Stokes_halfspace_basis_sum_within
        [OF B EP_support EP_deriv EP_cont
          EQ_support EQ_deriv EQ_cont])
  let ?h = "case_prod (\<lambda>t y.
    P_t t y - (\<Sum>b\<in>B. Q_b b t y))"
  let ?eh = "case_prod (\<lambda>t y.
    ?EP_t t y - (\<Sum>b\<in>B. ?EQ_b b t y))"
  have eh_eq: "\<And>p. ?eh p = (if p \<in> U then ?h p else 0)"
    by (case_tac p) (simp add: zero_extend_halfspace_def)
  have eq_fun: "?eh = (\<lambda>p. if p \<in> U then ?h p else 0)"
    by (rule ext, rule eh_eq)
  have domain_eq: "(LINT p : ?H | lborel. ?eh p) =
      (LINT p : ?H \<inter> U | lborel. ?h p)"
    unfolding eq_fun
    by (rule set_integral_zero_extension)
  let ?U0 = "{y. (0,y) \<in> U}"
  have e0_fun: "(\<lambda>y. ?EP 0 y) =
      (\<lambda>y. if y \<in> ?U0 then P 0 y else 0)"
    by (rule ext) (simp add: zero_extend_halfspace_def)
  have boundary_eq: "(\<integral>y. ?EP 0 y \<partial>lborel) =
      (LINT y : ?U0 | lborel. P 0 y)"
  proof -
    have "(\<integral>y. ?EP 0 y \<partial>lborel) =
      (LINT y : UNIV | lborel. if y \<in> ?U0 then P 0 y else 0)"
      by (simp add: e0_fun set_lebesgue_integral_def)
    also have "\<dots> = (LINT y : UNIV \<inter> ?U0 | lborel. P 0 y)"
      by (rule set_integral_zero_extension)
    also have "\<dots> = (LINT y : ?U0 | lborel. P 0 y)"
      by simp
    finally show ?thesis .
  qed
  show ?thesis using E_stokes domain_eq boundary_eq by simp
qed

end
