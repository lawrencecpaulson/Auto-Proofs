theory Stokes_Form_Bridge
  imports Stokes_Chart_Theorem
begin

text \<open>
  This is the integration interface for a future near-top form library.
  \<open>P\<close> and \<open>Q\<close> are coefficients of a pulled-back near-top form,
  \<open>d_coeff\<close> is the coefficient of the pulled-back exterior
  derivative, and \<open>boundary_coeff\<close> uses the induced boundary
  orientation.  The two pointwise coordinate laws below are the
  algebraic and pullback obligations for the form development.
\<close>

theorem Stokes_chart_form_interface:
  fixes P P_t :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
    and Q Q_b :: "'a \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real"
    and d_coeff :: "real \<times> 'a \<Rightarrow> real"
    and boundary_coeff :: "'a \<Rightarrow> real"
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
    and exterior_pullback_coordinate:
      "\<And>t y. (t,y) \<in> ({0..} \<times> UNIV) \<inter> U \<Longrightarrow>
        d_coeff (t,y) =
          P_t t y - (\<Sum>b\<in>B. Q_b b t y)"
    and boundary_pullback_orientation:
      "\<And>y. (0,y) \<in> U \<Longrightarrow>
        boundary_coeff y = - P 0 y"
  shows "(LINT p : ({0..} \<times> UNIV) \<inter> U | lborel.
      d_coeff p) =
    (LINT y : {y. (0,y) \<in> U} | lborel. boundary_coeff y)"
proof -
  let ?V = "({0..} \<times> UNIV) \<inter> U"
  let ?D = "case_prod (\<lambda>t y.
    P_t t y - (\<Sum>b\<in>B. Q_b b t y))"
  let ?W = "{y. (0,y) \<in> U}"
  have coordinate_stokes: "(LINT p : ?V | lborel. ?D p) =
      - (LINT y : ?W | lborel. P 0 y)"
    by (rule Stokes_relatively_open_chart_C1
        [OF B open_U compact_P K_P_chart zero_P
          deriv_P cont_P compact_Q K_Q_chart zero_Q
          deriv_Q cont_Q])
  have d_eq: "(LINT p : ?V | lborel. d_coeff p) =
      (LINT p : ?V | lborel. ?D p)"
    unfolding set_lebesgue_integral_def
    by (rule Bochner_Integration.integral_cong[OF refl])
       (use exterior_pullback_coordinate in
        \<open>auto simp: indicator_def split: prod.splits\<close>)
  have boundary_eq: "(LINT y : ?W | lborel. boundary_coeff y) =
      - (LINT y : ?W | lborel. P 0 y)"
  proof -
    have "(LINT y : ?W | lborel. boundary_coeff y) =
        (LINT y : ?W | lborel. - P 0 y)"
      unfolding set_lebesgue_integral_def
      by (rule Bochner_Integration.integral_cong[OF refl])
         (use boundary_pullback_orientation in
          \<open>auto simp: indicator_def\<close>)
    also have "\<dots> = - (LINT y : ?W | lborel. P 0 y)"
      by (simp add: set_lebesgue_integral_def)
    finally show ?thesis .
  qed
  show ?thesis using coordinate_stokes d_eq boundary_eq by simp
qed

end
