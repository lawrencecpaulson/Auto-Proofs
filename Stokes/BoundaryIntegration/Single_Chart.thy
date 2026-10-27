theory Single_Chart
  imports Body_Local_Integration
begin

lemma stokes_lborel_empty:
  "(LINT x : {} | lborel. (f x::real)) = 0"
  by (simp add: set_lebesgue_integral_def)

context positively_oriented_C2_halfspace_atlas
begin

lemma product_exterior_top_zero_off_compact_interior:
  fixes A :: "real \<times> (real ^ 'n::finite) \<Rightarrow>
    real \<times> (real ^ 'n)"
  assumes i: "i \<in> I"
    and compact: "compact K"
    and zero: "\<And>p. p \<in> C i \<Longrightarrow>
      p \<notin> K \<Longrightarrow> A p = 0"
    and x: "x \<in> C i \<inter> open_halfspace"
    and out: "x \<notin> K"
  shows "product_exterior_top A x = 0"
proof -
  have overlap_eq: "coordinate_overlap i i = C i"
    using halfspace_chart.inverse_image[OF chart[OF i]]
    by (auto simp: coordinate_overlap_def)
  have open_int: "open (C i \<inter> open_halfspace)"
    using body_overlap_open[OF i i]
    by (simp only: body_overlap_def overlap_eq)
  have closedK: "closed K"
    by (rule compact_imp_closed[OF compact])
  let ?W = "(C i \<inter> open_halfspace) - K"
  have openW: "open ?W"
    by (rule open_Diff[OF open_int closedK])
  have xW: "x \<in> ?W"
    using x out by auto
  have zeroW: "\<And>p. p \<in> ?W \<Longrightarrow> A p = 0"
    using zero by auto
  have deriv: "frechet_derivative A (at x) =
    frechet_derivative (\<lambda>p. 0) (at x)"
    by (rule frechet_derivative_transform_within_open
      [OF openW xW zeroW])
  show ?thesis
    by (simp add: product_exterior_top_def deriv)
qed

theorem Stokes_boundary_chart_form_C1:
  fixes A :: "real \<times> (real ^ 'n::finite) \<Rightarrow>
    real \<times> (real ^ 'n)"
    and K_P :: "(real \<times> (real ^ 'n)) set"
    and K_Q :: "real ^ 'n \<Rightarrow>
      (real \<times> (real ^ 'n)) set"
  assumes i: "i \<in> I"
    and dA: "\<And>p. p \<in> C i \<Longrightarrow>
      A differentiable (at p)"
    and compact_P: "compact K_P"
    and K_P_chart: "K_P \<subseteq> C i"
    and zero_P: "\<And>p. p \<in> C i \<Longrightarrow>
      p \<notin> K_P \<Longrightarrow> fst (A p) = 0"
    and cont_P: "continuous_on (C i)
      (case_prod (product_normal_derivative A))"
    and compact_Q: "\<And>b. b \<in> Basis \<Longrightarrow>
      compact (K_Q b)"
    and K_Q_chart: "\<And>b. b \<in> Basis \<Longrightarrow>
      K_Q b \<subseteq> C i"
    and zero_Q: "\<And>b p. b \<in> Basis \<Longrightarrow>
      p \<in> C i \<Longrightarrow> p \<notin> K_Q b
      \<Longrightarrow> snd (A p) \<bullet> b = 0"
    and cont_Q: "\<And>b. b \<in> Basis \<Longrightarrow>
      continuous_on (C i)
        (case_prod (product_tangential_derivative A b))"
  shows "(LINT p : C i | lborel. product_exterior_top A p) =
    (LINT y : halfspace_face (C i) | lborel.
      product_boundary_coeff A y)"
proof -
  have open_C: "openin (top_of_set closed_halfspace)
      (C i)"
    by (rule halfspace_chart.open_C[OF chart[OF i]])
  obtain U where U: "open U"
    "C i = closed_halfspace \<inter> U"
    using open_C by (auto simp: openin_open)
  have V: "C i = ({0..} \<times> UNIV) \<inter> U"
    using U(2) by (simp only: closed_halfspace_product)
  have face: "halfspace_face (C i) =
      {y. (0,y) \<in> U}"
    using U(2) by (auto simp: halfspace_face_def
      closed_halfspace_def)
  have stokes_raw: "(LINT p : ({0..} \<times> UNIV) \<inter> U | lborel.
      product_exterior_top A p) =
    (LINT y : {y. (0,y) \<in> U} | lborel.
      product_boundary_coeff A y)"
    by (rule Stokes_product_form_chart_C1
      [where A=A and K_P=K_P and K_Q=K_Q and U=U,
        OF U(1)])
       (use dA compact_P K_P_chart zero_P cont_P
          compact_Q K_Q_chart zero_Q cont_Q in
        \<open>auto simp: V[symmetric]\<close>)
  have stokes: "(LINT p : C i | lborel.
      product_exterior_top A p) =
    (LINT y : {y. (0,y) \<in> U} | lborel.
      product_boundary_coeff A y)"
    using stokes_raw by (simp only: V[symmetric])
  show ?thesis using stokes by (simp add: face)
qed

corollary Stokes_boundary_chart_compact_C1:
  fixes A :: "real \<times> (real ^ 'n::finite) \<Rightarrow>
    real \<times> (real ^ 'n)"
  assumes i: "i \<in> I"
    and dA: "\<And>p. p \<in> C i \<Longrightarrow>
      A differentiable (at p)"
    and compact: "compact K"
    and Kchart: "K \<subseteq> C i"
    and zero: "\<And>p. p \<in> C i \<Longrightarrow>
      p \<notin> K \<Longrightarrow> A p = 0"
    and cont_normal: "continuous_on (C i)
      (\<lambda>p. frechet_derivative A (at p) (1,0))"
    and cont_tangent: "\<And>b. b \<in> Basis \<Longrightarrow>
      continuous_on (C i)
        (\<lambda>p. frechet_derivative A (at p) (0,b))"
  shows "(LINT p : C i | lborel. product_exterior_top A p) =
    (LINT y : halfspace_face (C i) | lborel.
      product_boundary_coeff A y)"
proof -
  have cont_P: "continuous_on (C i)
      (case_prod (product_normal_derivative A))"
  proof -
    have eq: "case_prod (product_normal_derivative A) =
      (\<lambda>p. fst (frechet_derivative A
        (at p) (1,0)))"
    proof (rule ext)
      fix p
      show "case_prod (product_normal_derivative A) p =
        fst (frechet_derivative A (at p) (1,0))"
        by (cases p) (simp add:
          product_normal_derivative_def)
    qed
    show ?thesis
      unfolding eq
      by (intro continuous_intros cont_normal)
  qed
  have cont_Q: "\<And>b. b \<in> Basis \<Longrightarrow>
      continuous_on (C i)
        (case_prod (product_tangential_derivative A b))"
  proof -
    fix b :: "real ^ 'n"
    assume b: "b \<in> Basis"
    have eq: "case_prod
        (product_tangential_derivative A b) =
      (\<lambda>p. - (snd (frechet_derivative A
        (at p) (0,b)) \<bullet> b))"
    proof (rule ext)
      fix p
      show "case_prod
          (product_tangential_derivative A b) p =
        - (snd (frechet_derivative A
          (at p) (0,b)) \<bullet> b)"
        by (cases p) (simp add:
          product_tangential_derivative_def)
    qed
    show "continuous_on (C i)
      (case_prod (product_tangential_derivative A b))"
      unfolding eq
      by (intro continuous_intros cont_tangent[OF b])
  qed
  show ?thesis
    by (rule Stokes_boundary_chart_form_C1
      [where A=A and K_P=K and K_Q="\<lambda>_. K",
        OF i dA compact Kchart])
       (use zero cont_P compact Kchart cont_Q in
         \<open>auto\<close>)
qed

corollary Stokes_boundary_chart_weighted_C1:
  fixes A :: "real \<times> (real ^ 'n::finite) \<Rightarrow>
    real \<times> (real ^ 'n)"
    and rho :: "real \<times> (real ^ 'n) \<Rightarrow> real"
  assumes i: "i \<in> I"
    and drho: "\<And>p. p \<in> C i \<Longrightarrow>
      rho differentiable (at p)"
    and dA: "\<And>p. p \<in> C i \<Longrightarrow>
      A differentiable (at p)"
    and compact: "compact K"
    and Kchart: "K \<subseteq> C i"
    and zero_rho: "\<And>p. p \<in> C i \<Longrightarrow>
      p \<notin> K \<Longrightarrow> rho p = 0"
    and cont_normal: "continuous_on (C i)
      (\<lambda>p. frechet_derivative
        (\<lambda>q. rho q *\<^sub>R A q) (at p) (1,0))"
    and cont_tangent: "\<And>b. b \<in> Basis \<Longrightarrow>
      continuous_on (C i)
        (\<lambda>p. frechet_derivative
          (\<lambda>q. rho q *\<^sub>R A q)
            (at p) (0,b))"
  shows "(LINT p : C i | lborel.
      product_exterior_top
        (\<lambda>q. rho q *\<^sub>R A q) p) =
    (LINT y : halfspace_face (C i) | lborel.
      product_boundary_coeff
        (\<lambda>q. rho q *\<^sub>R A q) y)"
proof -
  have d_weighted: "\<And>p. p \<in> C i \<Longrightarrow>
      (\<lambda>q. rho q *\<^sub>R A q)
        differentiable (at p)"
    by (intro differentiable_scaleR drho dA)
  have zero: "\<And>p. p \<in> C i \<Longrightarrow>
      p \<notin> K \<Longrightarrow> rho p *\<^sub>R A p = 0"
    using zero_rho by simp
  show ?thesis
    by (rule Stokes_boundary_chart_compact_C1
      [OF i d_weighted compact Kchart zero
        cont_normal cont_tangent])
qed

context
  fixes A :: "real \<times> (real ^ 'n::finite) \<Rightarrow>
    real \<times> (real ^ 'n)"
    and K_P :: "(real \<times> (real ^ 'n)) set"
    and K_Q :: "real ^ 'n \<Rightarrow>
      (real \<times> (real ^ 'n)) set"
    and i :: 'i
  assumes i: "i \<in> I"
    and dA: "\<And>p. p \<in> C i \<Longrightarrow>
      A differentiable (at p)"
    and compact_P: "compact K_P"
    and K_P_chart: "K_P \<subseteq> C i"
    and zero_P: "\<And>p. p \<in> C i \<Longrightarrow>
      p \<notin> K_P \<Longrightarrow> fst (A p) = 0"
    and cont_P: "continuous_on (C i)
      (case_prod (product_normal_derivative A))"
    and compact_Q: "\<And>b. b \<in> Basis \<Longrightarrow>
      compact (K_Q b)"
    and K_Q_chart: "\<And>b. b \<in> Basis \<Longrightarrow>
      K_Q b \<subseteq> C i"
    and zero_Q: "\<And>b p. b \<in> Basis \<Longrightarrow>
      p \<in> C i \<Longrightarrow> p \<notin> K_Q b
      \<Longrightarrow> snd (A p) \<bullet> b = 0"
    and cont_Q: "\<And>b. b \<in> Basis \<Longrightarrow>
      continuous_on (C i)
        (case_prod (product_tangential_derivative A b))"
begin

theorem Stokes_boundary_chart_integral_top_C1:
  assumes compatible: "boundary_top_coeff_compatible alpha"
    and compact: "compact K"
    and Kchart: "K \<subseteq> boundary_carrier \<inter> D i"
    and support: "boundary_form_support alpha \<subseteq> K"
    and coeff_cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (alpha j)"
    and coeff_i: "\<And>y. y \<in> halfspace_face (C i)
      \<Longrightarrow> alpha i y = product_boundary_coeff A y"
    and partition:
      "admissible_boundary_partition alpha phi F"
  shows "(LINT p : C i | lborel. product_exterior_top A p) =
    integral_boundary_top alpha"
proof -
  have local_stokes: "(LINT p : C i | lborel.
      product_exterior_top A p) =
    (LINT y : halfspace_face (C i) | lborel.
      product_boundary_coeff A y)"
    by (rule Stokes_boundary_chart_form_C1
      [OF i dA compact_P K_P_chart zero_P cont_P
        compact_Q K_Q_chart zero_Q cont_Q])
  have int_i: "set_integrable lborel
      (halfspace_face (C i)) (alpha i)"
  proof -
    have abs_i: "alpha i absolutely_integrable_on
        halfspace_face (C i)"
      by (rule boundary_chart_coeff_absolutely_integrable
        [OF compatible i compact Kchart support coeff_cont[OF i]])
    have open_face: "open (halfspace_face (C i))"
      by (rule halfspace_face_open)
         (rule halfspace_chart.open_C[OF chart[OF i]])
    have face_borel: "halfspace_face (C i) \<in> sets borel"
      using open_face by (rule borel_open)
    have measurable: "(\<lambda>y. indicator
        (halfspace_face (C i)) y *\<^sub>R alpha i y)
        \<in> borel_measurable lborel"
      using borel_measurable_continuous_on_indicator
        [OF face_borel coeff_cont[OF i]]
      by (simp add: sets_lborel)
    show ?thesis
      using abs_i measurable
      by (simp add: absolutely_integrable_on_def
        set_integrable_def integrable_completion)
  qed
  have integral_i: "(LINT y : halfspace_face (C i) | lborel.
      product_boundary_coeff A y) =
    integral (halfspace_face (C i)) (alpha i)"
  proof -
    have open_face: "open (halfspace_face (C i))"
      by (rule halfspace_face_open)
         (rule halfspace_chart.open_C[OF chart[OF i]])
    have measurable_face:
      "halfspace_face (C i) \<in> sets lborel"
      using open_face by (simp add: sets_lborel borel_open)
    have eq: "(LINT y : halfspace_face (C i) | lborel.
        product_boundary_coeff A y) =
      (LINT y : halfspace_face (C i) | lborel. alpha i y)"
      by (rule set_lebesgue_integral_cong
        [OF measurable_face]) (use coeff_i in auto)
    show ?thesis
      using eq set_borel_integral_eq_integral(2)[OF int_i]
      by simp
  qed
  have global: "integral_boundary_top alpha =
    integral (halfspace_face (C i)) (alpha i)"
    by (rule integral_boundary_top_local_chart
      [OF i compatible compact Kchart support coeff_cont
        partition])
  show ?thesis
    using local_stokes integral_i global by simp
qed

theorem Stokes_boundary_chart_single_top_C1:
  assumes edge_chart:
      "admissible_boundary_single_chart edge i K_edge"
    and compatible: "boundary_top_coeff_compatible edge"
    and coeff_cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (edge j)"
    and coeff_i: "\<And>y. y \<in> halfspace_face (C i)
      \<Longrightarrow> edge i y = product_boundary_coeff A y"
  shows "(LINT p : C i | lborel. product_exterior_top A p) =
    integral_boundary_single_top edge"
proof -
  have stokes: "(LINT p : C i | lborel.
      product_exterior_top A p) =
    (LINT y : halfspace_face (C i) | lborel.
      product_boundary_coeff A y)"
    by (rule Stokes_boundary_chart_form_C1
      [OF i dA compact_P K_P_chart zero_P cont_P
        compact_Q K_Q_chart zero_Q cont_Q])
  have edge_eq: "(LINT y : halfspace_face (C i) | lborel.
      product_boundary_coeff A y) =
    (LINT y : halfspace_face (C i) | lborel.
      edge i y)"
    unfolding set_lebesgue_integral_def
    by (rule Bochner_Integration.integral_cong[OF refl])
       (use coeff_i in \<open>auto simp: indicator_def\<close>)
  have gauge: "(LINT y : halfspace_face (C i) | lborel.
      edge i y) =
    integral (halfspace_face (C i)) (edge i)"
    by (rule boundary_single_chart_lborel_eq_integral
      [OF edge_chart compatible coeff_cont[OF i]])
  have local: "integral_boundary_single_top edge =
    integral (halfspace_face (C i)) (edge i)"
    by (rule integral_boundary_single_top_local_chart
      [OF edge_chart compatible coeff_cont])
  show ?thesis
    using stokes edge_eq gauge local by simp
qed

theorem Stokes_single_boundary_chart_local_integrals_C1:
  assumes body_chart: "admissible_body_single_chart
      body i K_body"
    and body_compatible: "body_top_coeff_compatible body"
    and positive: "\<And>j k x.
      j \<in> I \<Longrightarrow> k \<in> I \<Longrightarrow>
      x \<in> body_overlap j k \<Longrightarrow>
      0 < eucl.det (frechet_derivative
        (coordinate_transition j k) (at x))"
    and smooth: "\<And>j k.
      j \<in> I \<Longrightarrow> k \<in> I \<Longrightarrow>
      Ck_on 2 (coordinate_transition j k)
        (body_overlap j k)"
    and body_cont: "continuous_on (C i) (body i)"
    and body_coeff: "\<And>p. p \<in> C i \<Longrightarrow>
      body i p = product_exterior_top A p"
    and edge_chart:
      "admissible_boundary_single_chart edge i K_edge"
    and edge_compatible: "boundary_top_coeff_compatible edge"
    and edge_cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (edge j)"
    and edge_coeff: "\<And>y. y \<in> halfspace_face (C i)
      \<Longrightarrow> edge i y = product_boundary_coeff A y"
  shows "integral_body_single_top body =
    integral_boundary_single_top edge"
proof -
  have body_int: "body i absolutely_integrable_on C i"
    using body_chart
    by (auto simp: admissible_body_single_chart_def)
  have local_body: "integral_body_single_top body =
    integral (C i) (body i)"
    by (rule integral_body_single_top_local_chart
      [OF body_chart body_compatible positive smooth])
  have gauge: "(LINT p : C i | lborel. body i p) =
    integral (C i) (body i)"
    by (rule body_chart_lborel_eq_integral
      [OF i body_int body_cont])
  have coeff_eq: "(LINT p : C i | lborel. body i p) =
    (LINT p : C i | lborel.
      product_exterior_top A p)"
    unfolding set_lebesgue_integral_def
    by (rule Bochner_Integration.integral_cong[OF refl])
       (use body_coeff in
         \<open>auto simp: indicator_def\<close>)
  have stokes: "(LINT p : C i | lborel.
      product_exterior_top A p) =
    integral_boundary_single_top edge"
    by (rule Stokes_boundary_chart_single_top_C1
      [OF edge_chart edge_compatible edge_cont edge_coeff])
  show ?thesis
    using local_body gauge coeff_eq stokes by simp
qed

theorem Stokes_single_boundary_chart_integrals_C1:
  assumes body_chart: "admissible_body_single_chart
      body i K_body"
    and body_compatible: "body_top_coeff_compatible body"
    and positive: "\<And>j k x.
      j \<in> I \<Longrightarrow> k \<in> I \<Longrightarrow>
      x \<in> body_overlap j k \<Longrightarrow>
      0 < eucl.det (frechet_derivative
        (coordinate_transition j k) (at x))"
    and smooth: "\<And>j k.
      j \<in> I \<Longrightarrow> k \<in> I \<Longrightarrow>
      Ck_on 2 (coordinate_transition j k)
        (body_overlap j k)"
    and body_cont: "continuous_on (C i) (body i)"
    and body_coeff: "\<And>p. p \<in> C i \<Longrightarrow>
      body i p = product_exterior_top A p"
    and edge_compatible: "boundary_top_coeff_compatible edge"
    and compact_edge: "compact K_edge"
    and K_edge_chart:
      "K_edge \<subseteq> boundary_carrier \<inter> D i"
    and support_edge:
      "boundary_form_support edge \<subseteq> K_edge"
    and edge_cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (edge j)"
    and edge_coeff: "\<And>y. y \<in> halfspace_face (C i)
      \<Longrightarrow> edge i y = product_boundary_coeff A y"
    and partition: "admissible_boundary_partition
      edge phi F"
  shows "integral_body_single_top body =
    integral_boundary_top edge"
proof -
  have body_int: "body i absolutely_integrable_on C i"
    using body_chart
    by (auto simp: admissible_body_single_chart_def)
  have local_body: "integral_body_single_top body =
    integral (C i) (body i)"
    by (rule integral_body_single_top_local_chart
      [OF body_chart body_compatible positive smooth])
  have gauge: "(LINT p : C i | lborel. body i p) =
    integral (C i) (body i)"
    by (rule body_chart_lborel_eq_integral
      [OF i body_int body_cont])
  have coeff_eq: "(LINT p : C i | lborel. body i p) =
    (LINT p : C i | lborel.
      product_exterior_top A p)"
    unfolding set_lebesgue_integral_def
    by (rule Bochner_Integration.integral_cong[OF refl])
       (use body_coeff in
         \<open>auto simp: indicator_def\<close>)
  have stokes: "(LINT p : C i | lborel.
      product_exterior_top A p) =
    integral_boundary_top edge"
    by (rule Stokes_boundary_chart_integral_top_C1
      [OF edge_compatible compact_edge K_edge_chart
          support_edge edge_cont edge_coeff partition])
  show ?thesis
    using local_body gauge coeff_eq stokes by simp
qed

corollary Stokes_boundary_chart_gauge_C1:
  assumes compatible: "boundary_top_coeff_compatible alpha"
    and compact: "compact K"
    and Kchart: "K \<subseteq> boundary_carrier \<inter> D i"
    and support: "boundary_form_support alpha \<subseteq> K"
    and coeff_cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (alpha j)"
    and coeff_i: "\<And>y. y \<in> halfspace_face (C i)
      \<Longrightarrow> alpha i y = product_boundary_coeff A y"
    and partition:
      "admissible_boundary_partition alpha phi F"
    and integrable_body:
      "set_integrable lborel (C i) (product_exterior_top A)"
  shows "integral (C i) (product_exterior_top A) =
    integral_boundary_top alpha"
proof -
  have local: "(LINT p : C i | lborel.
      product_exterior_top A p) =
    integral_boundary_top alpha"
    by (rule Stokes_boundary_chart_integral_top_C1
      [OF compatible compact Kchart support coeff_cont
        coeff_i partition])
  show ?thesis
    using local
      set_borel_integral_eq_integral(2)[OF integrable_body]
    by simp
qed

end

corollary integral_boundary_top_normal_sign:
  assumes i: "i \<in> I"
    and compatible: "boundary_top_coeff_compatible alpha"
    and compact: "compact K"
    and Kchart: "K \<subseteq> boundary_carrier \<inter> D i"
    and support: "boundary_form_support alpha \<subseteq> K"
    and coeff_cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (alpha j)"
    and coeff_i: "\<And>y. y \<in> halfspace_face (C i)
      \<Longrightarrow> alpha i y = product_boundary_coeff A y"
    and partition:
      "admissible_boundary_partition alpha phi F"
  shows "integral_boundary_top alpha =
    - integral (halfspace_face (C i))
        (\<lambda>y. fst (A (0,y)))"
proof -
  have local: "integral_boundary_top alpha =
    integral (halfspace_face (C i)) (alpha i)"
    by (rule integral_boundary_top_local_chart
      [OF i compatible compact Kchart support coeff_cont
        partition])
  have eq: "integral (halfspace_face (C i)) (alpha i) =
      integral (halfspace_face (C i))
        (\<lambda>y. - fst (A (0,y)))"
    by (rule integral_cong)
       (use coeff_i in
        \<open>auto simp: product_boundary_coeff_def
          product_normal_coeff_def\<close>)
  show ?thesis
    using local eq by simp
qed

context
  fixes A :: "real \<times> (real ^ 'n::finite) \<Rightarrow>
    real \<times> (real ^ 'n)"
    and K_P :: "(real \<times> (real ^ 'n)) set"
    and K_Q :: "real ^ 'n \<Rightarrow>
      (real \<times> (real ^ 'n)) set"
    and i :: 'i
  assumes i: "i \<in> I"
    and no_face: "halfspace_face (C i) = {}"
    and dA: "\<And>p. p \<in> C i \<Longrightarrow>
      A differentiable (at p)"
    and compact_P: "compact K_P"
    and K_P_chart: "K_P \<subseteq> C i"
    and zero_P: "\<And>p. p \<in> C i \<Longrightarrow>
      p \<notin> K_P \<Longrightarrow> fst (A p) = 0"
    and cont_P: "continuous_on (C i)
      (case_prod (product_normal_derivative A))"
    and compact_Q: "\<And>b. b \<in> Basis \<Longrightarrow>
      compact (K_Q b)"
    and K_Q_chart: "\<And>b. b \<in> Basis \<Longrightarrow>
      K_Q b \<subseteq> C i"
    and zero_Q: "\<And>b p. b \<in> Basis \<Longrightarrow>
      p \<in> C i \<Longrightarrow> p \<notin> K_Q b
      \<Longrightarrow> snd (A p) \<bullet> b = 0"
    and cont_Q: "\<And>b. b \<in> Basis \<Longrightarrow>
      continuous_on (C i)
        (case_prod (product_tangential_derivative A b))"
begin

corollary Stokes_interior_chart_form_C1:
  shows "(LINT p : C i | lborel.
      product_exterior_top A p) = 0"
proof -
  have S: "(LINT p : C i | lborel.
      product_exterior_top A p) =
    (LINT y : halfspace_face (C i) | lborel.
      product_boundary_coeff A y)"
    by (rule Stokes_boundary_chart_form_C1
      [OF i dA compact_P K_P_chart zero_P cont_P
        compact_Q K_Q_chart zero_Q cont_Q])
  show ?thesis
    using S by (simp only: no_face stokes_lborel_empty)
qed

corollary Stokes_interior_chart_integral_top_C1:
  shows "(LINT p : C i | lborel. product_exterior_top A p) =
    integral_boundary_top (\<lambda>j y. 0)"
proof -
  have local: "(LINT p : C i | lborel.
      product_exterior_top A p) = 0"
    by (rule Stokes_interior_chart_form_C1)
  show ?thesis
    using local integral_boundary_top_zero_coeff
    by (simp only: integral_boundary_top_zero_coeff)
qed

theorem Stokes_single_interior_chart_integrals_C1:
  assumes body_chart: "admissible_body_single_chart
      body i K_body"
    and body_compatible: "body_top_coeff_compatible body"
    and positive: "\<And>j k x.
      j \<in> I \<Longrightarrow> k \<in> I \<Longrightarrow>
      x \<in> body_overlap j k \<Longrightarrow>
      0 < eucl.det (frechet_derivative
        (coordinate_transition j k) (at x))"
    and smooth: "\<And>j k.
      j \<in> I \<Longrightarrow> k \<in> I \<Longrightarrow>
      Ck_on 2 (coordinate_transition j k)
        (body_overlap j k)"
    and body_cont: "continuous_on (C i) (body i)"
    and body_coeff: "\<And>p. p \<in> C i \<Longrightarrow>
      body i p = product_exterior_top A p"
  shows "integral_body_single_top body =
    integral_boundary_single_top (\<lambda>j y. 0)"
proof -
  have body_int: "body i absolutely_integrable_on C i"
    using body_chart
    by (auto simp: admissible_body_single_chart_def)
  have local_body: "integral_body_single_top body =
    integral (C i) (body i)"
    by (rule integral_body_single_top_local_chart
      [OF body_chart body_compatible positive smooth])
  have gauge: "(LINT p : C i | lborel. body i p) =
    integral (C i) (body i)"
    by (rule body_chart_lborel_eq_integral
      [OF i body_int body_cont])
  have coeff_eq: "(LINT p : C i | lborel. body i p) =
    (LINT p : C i | lborel.
      product_exterior_top A p)"
    unfolding set_lebesgue_integral_def
    by (rule Bochner_Integration.integral_cong[OF refl])
       (use body_coeff in
         \<open>auto simp: indicator_def\<close>)
  have stokes: "(LINT p : C i | lborel.
      product_exterior_top A p) =
    integral_boundary_top (\<lambda>j y. 0)"
    by (rule Stokes_interior_chart_integral_top_C1)
  have old: "integral_body_single_top body =
      integral_boundary_top (\<lambda>j y. 0)"
    using local_body gauge coeff_eq stokes by simp
  show ?thesis
    using old boundary_zero_integrals_agree by simp
qed

end

end

context smooth_oriented_C2_halfspace_atlas
begin

theorem Stokes_chart_supported_near_top_C1:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n::finite)
    \<Rightarrow> real \<times> (real ^ 'n)"
    and body :: "'i \<Rightarrow> real \<times> (real ^ 'n)
      \<Rightarrow> real"
    and edge :: "'i \<Rightarrow> real ^ 'n \<Rightarrow> real"
  assumes i: "i \<in> I"
    and compact: "compact K"
    and K_chart: "K \<subseteq> D i"
    and support: "near_top_form_support A \<subseteq> K"
    and dA: "\<And>j x. j \<in> I \<Longrightarrow>
      x \<in> C j \<Longrightarrow>
      A j differentiable (at x)"
    and pull: "\<And>j k x. j \<in> I \<Longrightarrow>
      k \<in> I \<Longrightarrow> x \<in> body_overlap j k
      \<Longrightarrow> A j x = product_pull_near_top
        (coordinate_transition j k)
        (coordinate_transition k j) (A k) x"
    and cont_P: "continuous_on (C i)
      (case_prod (product_normal_derivative (A i)))"
    and cont_Q: "\<And>b. b \<in> Basis \<Longrightarrow>
      continuous_on (C i)
        (case_prod (product_tangential_derivative (A i) b))"
    and body_coeff: "\<And>j x. j \<in> I \<Longrightarrow>
      x \<in> C j \<inter> open_halfspace \<Longrightarrow>
      body j x = product_exterior_top (A j) x"
    and body_coeff_i: "\<And>x. x \<in> C i \<Longrightarrow>
      body i x = product_exterior_top (A i) x"
    and edge_coeff: "\<And>j y. j \<in> I \<Longrightarrow>
      y \<in> halfspace_face (C j) \<Longrightarrow>
      edge j y = product_boundary_coeff (A j) y"
  shows "integral_body_single_top body =
    integral_boundary_single_top edge"
proof -
  let ?Kc = "to_chart i ` K"
  have K_M: "K \<subseteq> M"
    using K_chart domain_subset_carrier[OF i] by auto
  have to_cont: "continuous_on K (to_chart i)"
    by (rule continuous_on_subset
      [OF homeomorphism_cont1
        [OF halfspace_chart.homeo[OF chart[OF i]]]
        K_chart])
  have Kc_compact: "compact ?Kc"
    by (rule compact_continuous_image[OF to_cont compact])
  have Kc_chart: "?Kc \<subseteq> C i"
    using K_chart
      halfspace_chart.chart_image[OF chart[OF i]]
    by auto
  have zero: "A i x = 0" if xC: "x \<in> C i"
    and xout: "x \<notin> ?Kc" for x
  proof (rule ccontr)
    assume nonzero: "A i x \<noteq> 0"
    have pD: "from_chart i x \<in> D i"
      using xC halfspace_chart.inverse_image
        [OF chart[OF i]] by auto
    have pM: "from_chart i x \<in> M"
      using pD domain_subset_carrier[OF i] by auto
    have xeq: "to_chart i (from_chart i x) = x"
      by (rule halfspace_chart.from_to
        [OF chart[OF i] xC])
    have "from_chart i x \<in> near_top_form_support A"
      using pM pD nonzero i xeq
      by (auto simp: near_top_form_support_def)
    then have "from_chart i x \<in> K"
      using support by auto
    then have "x \<in> ?Kc"
      using xeq by (metis image_eqI)
    then show False using xout by auto
  qed
  have body_support: "body_form_support body \<subseteq> K"
    by (rule exterior_top_support_subset
      [OF compact support body_coeff])
  have body_compatible: "body_top_coeff_compatible body"
    by (rule body_coeff_compatible_from_pullback
      [OF pull])
       (use dA body_coeff in auto)
  have body_cont: "continuous_on (C i) (body i)"
  proof -
    have "continuous_on (C i)
        (product_exterior_top (A i))"
      by (rule product_exterior_top_continuous_on
        [OF cont_P cont_Q])
    then show ?thesis
      by (subst continuous_on_cong
        [OF refl body_coeff_i])
         simp
  qed
  have body_integrable: "body i absolutely_integrable_on C i"
    by (rule body_chart_coeff_absolutely_integrable
      [OF i compact K_chart body_support body_cont])
  have body_chart: "admissible_body_single_chart
      body i K"
    using i compact K_chart body_support body_integrable
    by (simp add: admissible_body_single_chart_def)
  have edge_chart: "admissible_boundary_single_chart
      edge i (K \<inter> boundary_carrier)"
    by (rule boundary_restriction_admissible_single
      [OF i compact K_M K_chart support edge_coeff])
  have face_pull: "near_top_face_pull_compatible A"
    by (rule near_top_face_pull_compatible_from_pullback
      [OF pull dA])
  have edge_compatible: "boundary_top_coeff_compatible edge"
    by (rule boundary_coeff_compatible_from_geometric_pull
      [OF face_pull edge_coeff])
  have edge_cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (edge j)"
    by (rule boundary_restriction_continuous)
       (use dA edge_coeff in auto)
  have zero_P: "\<And>x. x \<in> C i \<Longrightarrow>
      x \<notin> ?Kc \<Longrightarrow> fst (A i x) = 0"
    using zero by simp
  have zero_Q: "\<And>b x. b \<in> Basis \<Longrightarrow>
      x \<in> C i \<Longrightarrow> x \<notin> ?Kc
      \<Longrightarrow> snd (A i x) \<bullet> b = 0"
    using zero by simp
  have dAi: "\<And>x. x \<in> C i \<Longrightarrow>
      A i differentiable (at x)"
    by (rule dA[OF i])
  show ?thesis
    by (rule Stokes_single_boundary_chart_local_integrals_C1
      [where A="A i" and K_P="to_chart i ` K" and
        K_Q="\<lambda>_. to_chart i ` K" and K_body=K and
        K_edge="K \<inter> boundary_carrier",
        OF i dAi Kc_compact Kc_chart
          zero_P cont_P Kc_compact Kc_chart
          zero_Q cont_Q body_chart
          body_compatible positive_body_transition
          body_transition_C2 body_cont body_coeff_i
          edge_chart edge_compatible edge_cont
          edge_coeff[OF i]])
qed

corollary Stokes_chart_supported_form_C1:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n::finite)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes i: "i \<in> I"
    and compact: "compact K"
    and K_chart: "K \<subseteq> D i"
    and support: "near_top_form_support A \<subseteq> K"
    and dA: "\<And>j x. j \<in> I \<Longrightarrow>
      x \<in> C j \<Longrightarrow>
      A j differentiable (at x)"
    and pull: "\<And>j k x. j \<in> I \<Longrightarrow>
      k \<in> I \<Longrightarrow> x \<in> body_overlap j k
      \<Longrightarrow> A j x = product_pull_near_top
        (coordinate_transition j k)
        (coordinate_transition k j) (A k) x"
    and cont_P: "continuous_on (C i)
      (case_prod (product_normal_derivative (A i)))"
    and cont_Q: "\<And>b. b \<in> Basis \<Longrightarrow>
      continuous_on (C i)
        (case_prod (product_tangential_derivative (A i) b))"
  shows "integral_body_single_top
      (\<lambda>j x. product_exterior_top (A j) x) =
    integral_boundary_single_top
      (\<lambda>j y. product_boundary_coeff (A j) y)"
  by (rule Stokes_chart_supported_near_top_C1
    [OF i compact K_chart support dA pull
      cont_P cont_Q])
     auto

corollary Stokes_chart_supported_form_boundary_top_C1:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n::finite)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes i: "i \<in> I"
    and compact: "compact K"
    and K_chart: "K \<subseteq> D i"
    and support: "near_top_form_support A \<subseteq> K"
    and dA: "\<And>j x. j \<in> I \<Longrightarrow>
      x \<in> C j \<Longrightarrow>
      A j differentiable (at x)"
    and pull: "\<And>j k x. j \<in> I \<Longrightarrow>
      k \<in> I \<Longrightarrow> x \<in> body_overlap j k
      \<Longrightarrow> A j x = product_pull_near_top
        (coordinate_transition j k)
        (coordinate_transition k j) (A k) x"
    and cont_P: "continuous_on (C i)
      (case_prod (product_normal_derivative (A i)))"
    and cont_Q: "\<And>b. b \<in> Basis \<Longrightarrow>
      continuous_on (C i)
        (case_prod (product_tangential_derivative (A i) b))"
  shows "integral_body_single_top
      (\<lambda>j x. product_exterior_top (A j) x) =
    integral_boundary_top
      (\<lambda>j y. product_boundary_coeff (A j) y)"
proof -
  let ?edge = "\<lambda>j y. product_boundary_coeff (A j) y"
  have K_M: "K \<subseteq> M"
    using K_chart domain_subset_carrier[OF i] by auto
  have edge_chart: "admissible_boundary_single_chart
      ?edge i (K \<inter> boundary_carrier)"
    by (rule boundary_restriction_admissible_single
      [OF i compact K_M K_chart support])
       simp
  have face_pull: "near_top_face_pull_compatible A"
    by (rule near_top_face_pull_compatible_from_pullback
      [OF pull dA])
  have edge_compatible: "boundary_top_coeff_compatible ?edge"
    by (rule boundary_coeff_compatible_from_geometric_pull
      [OF face_pull])
       simp
  have edge_cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (?edge j)"
    by (rule boundary_restriction_continuous)
       (use dA in auto)
  have edge_eq: "integral_boundary_single_top ?edge =
      integral_boundary_top ?edge"
    by (rule integral_boundary_single_top_eq_top_chart
      [OF edge_chart edge_compatible edge_cont])
  have stokes: "integral_body_single_top
      (\<lambda>j x. product_exterior_top (A j) x) =
      integral_boundary_single_top ?edge"
    by (rule Stokes_chart_supported_form_C1
      [OF i compact K_chart support dA pull
        cont_P cont_Q])
  show ?thesis using stokes edge_eq by simp
qed

theorem Stokes_chart_supported_form_integrals_C1:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n::finite)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes i: "i \<in> I"
    and compact: "compact K"
    and K_chart: "K \<subseteq> D i"
    and support: "near_top_form_support A \<subseteq> K"
    and dA: "\<And>j x. j \<in> I \<Longrightarrow>
      x \<in> C j \<Longrightarrow>
      A j differentiable (at x)"
    and pull: "\<And>j k x. j \<in> I \<Longrightarrow>
      k \<in> I \<Longrightarrow> x \<in> body_overlap j k
      \<Longrightarrow> A j x = product_pull_near_top
        (coordinate_transition j k)
        (coordinate_transition k j) (A k) x"
    and cont_P: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (C j)
        (case_prod (product_normal_derivative (A j)))"
    and cont_Q: "\<And>j b. j \<in> I \<Longrightarrow>
      b \<in> Basis \<Longrightarrow> continuous_on (C j)
        (case_prod (product_tangential_derivative (A j) b))"
  shows "integral_body_top
      (\<lambda>j x. product_exterior_top (A j) x) =
    integral_boundary_top
      (\<lambda>j y. product_boundary_coeff (A j) y)"
proof -
  let ?body = "\<lambda>j x. product_exterior_top (A j) x"
  let ?edge = "\<lambda>j y. product_boundary_coeff (A j) y"
  have body_support: "body_form_support ?body \<subseteq> K"
    by (rule exterior_top_support_subset
      [OF compact support]) simp
  have body_compatible: "body_top_coeff_compatible ?body"
    by (rule exterior_top_coeff_compatible_from_pullback
      [OF pull]) (use dA in auto)
  have body_cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (C j) (?body j)"
    by (rule product_exterior_top_continuous_on)
       (use cont_P cont_Q in auto)
  have body_integrable: "?body i absolutely_integrable_on C i"
    by (rule body_chart_coeff_absolutely_integrable
      [OF i compact K_chart body_support body_cont[OF i]])
  have body_chart: "admissible_body_single_chart
      ?body i K"
    using i compact K_chart body_support body_integrable
    by (simp add: admissible_body_single_chart_def)
  have body_eq: "integral_body_single_top ?body =
      integral_body_top ?body"
    by (rule integral_body_single_top_eq_top_chart
      [OF body_chart body_compatible body_cont])
  have stokes: "integral_body_single_top ?body =
      integral_boundary_top ?edge"
    by (rule Stokes_chart_supported_form_boundary_top_C1
      [OF i compact K_chart support dA pull
        cont_P[OF i] cont_Q[OF i]])
  show ?thesis using body_eq stokes by simp
qed

end

end
