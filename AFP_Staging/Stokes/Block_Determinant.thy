theory Block_Determinant
  imports Halfspace_Naturality
begin

definition tangential_block ::
    "'a::zero ^ (unit + 'n::finite) ^ (unit + 'n) \<Rightarrow>
      'a ^ 'n ^ 'n"
  where "tangential_block F = (\<chi> i j. F $ Inr i $ Inr j)"

lemma prod_UNIV_unit_plus:
  fixes f :: "unit + 'n::finite \<Rightarrow> 'a::comm_monoid_mult"
  shows "(\<Prod>i\<in>UNIV. f i) = f (Inl ()) * (\<Prod>j\<in>UNIV. f (Inr j))"
proof -
  have disj: "{Inl ()} \<inter> range (Inr :: 'n \<Rightarrow> unit + 'n) = {}"
    by auto
  have split:
    "prod f ({Inl ()} \<union> range (Inr :: 'n \<Rightarrow> unit + 'n)) =
      f (Inl ()) * prod f (range Inr)"
    using disj by (simp add: prod.union_disjoint)
  have right:
    "prod f (range (Inr :: 'n \<Rightarrow> unit + 'n)) =
      (\<Prod>j\<in>UNIV. f (Inr j))"
    by (simp add: prod.reindex)
  have left: "range (Inl :: unit \<Rightarrow> unit + 'n) = {Inl ()}"
    by auto
  show ?thesis using split right
    by (simp add: UNIV_sum left)
qed

lemma det_normal_tangential_block:
  fixes F :: "real ^ (unit + 'n::finite) ^ (unit + 'n)"
  assumes zero: "\<And>j. F $ Inl () $ Inr j = 0"
  shows "Determinants.det F =
    F $ Inl () $ Inl () * Determinants.det (tangential_block F)"
proof -
  let ?U = "UNIV :: 'n set"
  let ?B = "range (Inr :: 'n \<Rightarrow> unit + 'n)"
  let ?PU = "{p. p permutes ?U}"
  let ?PB = "{p. p permutes ?B}"
  let ?PAll = "{p. p permutes (UNIV :: (unit + 'n) set)}"
  let ?lift = "\<lambda>p x.
    if x \<in> ?B then Inr (p (inv_into ?U Inr x)) else x"
  let ?term = "\<lambda>p. of_int (sign p) *
    (\<Prod>i\<in>UNIV. F $ i $ p i)"
  have PB_sub: "?PB \<subseteq> ?PAll"
    by (auto intro: permutes_subset)
  have zero_out: "\<forall>p\<in>?PAll - ?PB. ?term p = 0"
  proof (intro ballI)
    fix p
    assume p: "p \<in> ?PAll - ?PB"
    have moved: "p (Inl ()) \<noteq> Inl ()"
    proof
      assume fixed: "p (Inl ()) = Inl ()"
      have fixed_outside: "\<And>x. x \<notin> ?B \<Longrightarrow> p x = x"
      proof -
        fix x
        assume "x \<notin> ?B"
        then obtain u where "x = Inl u"
          by (cases x) auto
        then show "p x = x"
          using fixed by (cases u) simp
      qed
      from p have bij: "\<And>y. \<exists>!x. p x = y"
        by (auto simp: permutes_def)
      have "p permutes ?B"
        unfolding permutes_def using fixed_outside bij by blast
      with p show False by blast
    qed
    then obtain j where entry_zero: "F $ Inl () $ p (Inl ()) = 0"
      using zero by (cases "p (Inl ())") auto
    have product_zero: "(\<Prod>i\<in>UNIV. F $ i $ p i) = 0"
      by (rule prod_zero) (use entry_zero in auto)
    show "?term p = 0"
      by (simp add: product_zero)
  qed
  have sum_restrict: "sum ?term ?PB = sum ?term ?PAll"
    by (rule sum.mono_neutral_cong_left[
      OF finite_permutations[OF finite] PB_sub zero_out]) auto
  have det_restrict: "Determinants.det F = sum ?term ?PB"
    unfolding Determinants.det_def using sum_restrict by (rule sym)
  have bij_inr: "bij_betw (Inr :: 'n \<Rightarrow> unit + 'n) ?U ?B"
    by (rule bij_betw_imageI) auto
  have bij_lift: "bij_betw ?lift ?PU ?PB"
    by (rule bij_betw_permutations[OF bij_inr])
  have lift_eq_map:
    "?lift p = map_permutation ?U (Inr :: 'n \<Rightarrow> unit + 'n) p" for p
    unfolding map_permutation_def
    by (auto simp: fun_eq_iff restrict_id_def o_def)
  have sign_lift: "sign (?lift p) = sign p" if "p \<in> ?PU" for p
    using sign_map_permutation[of "Inr :: 'n \<Rightarrow> unit + 'n" ?U p]
      that by (simp add: lift_eq_map)
  have product_lift:
    "(\<Prod>i\<in>UNIV. F $ i $ ?lift p i) =
     F $ Inl () $ Inl () *
      (\<Prod>i\<in>UNIV. tangential_block F $ i $ p i)"
    if "p \<in> ?PU" for p
  proof -
    have split:
      "(\<Prod>i\<in>UNIV. F $ i $ ?lift p i) =
        F $ Inl () $ ?lift p (Inl ()) *
        (\<Prod>i\<in>UNIV. F $ Inr i $ ?lift p (Inr i))"
      by (rule prod_UNIV_unit_plus)
    have inv_right: "inv_into ?U Inr (Inr i) = i" for i
      by (rule inv_into_f_f) auto
    have in_right: "Inr i \<in> ?B" for i by auto
    have not_right: "Inl () \<notin> ?B" by auto
    show ?thesis
      using split that
      by (simp add: tangential_block_def inv_right in_right not_right)
  qed
  have term_lift:
    "?term (?lift p) =
     F $ Inl () $ Inl () *
      (of_int (sign p) *
        (\<Prod>i\<in>UNIV. tangential_block F $ i $ p i))"
    if "p \<in> ?PU" for p
    using sign_lift[OF that] product_lift[OF that]
    by (simp add: mult_ac)
  have reindex:
    "sum (\<lambda>p. ?term (?lift p)) ?PU = sum ?term ?PB"
    by (rule sum.reindex_bij_betw[OF bij_lift])
  have "sum ?term ?PB = sum (\<lambda>p. ?term (?lift p)) ?PU"
    using reindex by (rule sym)
  also have "\<dots> =
      F $ Inl () $ Inl () *
       sum (\<lambda>p. of_int (sign p) *
        (\<Prod>i\<in>UNIV. tangential_block F $ i $ p i)) ?PU"
    by (simp add: sum_distrib_left term_lift)
  also have "\<dots> =
      F $ Inl () $ Inl () * Determinants.det (tangential_block F)"
    by (simp only: Determinants.det_def)
  finally show ?thesis
    using det_restrict by simp
qed

lemma inverse_cofactor_eq_tangential_det:
  fixes F G :: "real ^ (unit + 'n::finite) ^ (unit + 'n)"
  assumes inverse: "G ** F = mat 1"
    and f_zero: "\<And>j. F $ Inl () $ Inr j = 0"
    and g_zero: "\<And>j. G $ Inl () $ Inr j = 0"
  shows "Determinants.det F * G $ Inl () $ Inl () =
    Determinants.det (tangential_block F)"
proof -
  have normal_inverse:
    "G $ Inl () $ Inl () * F $ Inl () $ Inl () = 1"
  proof -
    have "(G ** F) $ Inl () $ Inl () = 1"
      using inverse by (simp add: mat_def)
    then have "(\<Sum>k\<in>UNIV.
       G $ Inl () $ k * F $ k $ Inl ()) = 1"
      by (simp add: matrix_matrix_mult_def)
    then show ?thesis
      by (simp add: sum_UNIV_unit_plus g_zero)
  qed
  have block: "Determinants.det F =
      F $ Inl () $ Inl () *
        Determinants.det (tangential_block F)"
    by (rule det_normal_tangential_block[OF f_zero])
  show ?thesis
    using block normal_inverse by (simp add: mult_ac)
qed

theorem cart_halfspace_boundary_orientation:
  fixes f :: "real ^ (unit + 'n::finite) \<Rightarrow>
      real ^ (unit + 'n)"
    and G :: "real ^ (unit + 'n) ^ (unit + 'n)"
  assumes openU: "open U" and xU: "x \<in> U"
    and xface: "x $ Inl () = 0"
    and fface: "f x $ Inl () = 0"
    and df: "f differentiable (at x)"
    and halfspace: "\<And>w. w \<in> U \<Longrightarrow>
      w \<in> cart_halfspace \<Longrightarrow> f w \<in> cart_halfspace"
    and face: "\<And>w. w \<in> U \<Longrightarrow>
      w $ Inl () = 0 \<Longrightarrow> f w $ Inl () = 0"
    and inverse: "jacobian f (at x) ** G = mat 1"
  shows "0 < jacobian f (at x) $ Inl () $ Inl ()"
    and "Determinants.det (jacobian f (at x)) =
      jacobian f (at x) $ Inl () $ Inl () *
        Determinants.det
          (tangential_block (jacobian f (at x)))"
proof -
  show "0 < jacobian f (at x) $ Inl () $ Inl ()"
    by (rule halfspace_chart_normal_positive
      [OF openU xU xface fface df halfspace face inverse])
  have zero: "\<And>j.
      jacobian f (at x) $ Inl () $ Inr j = 0"
    by (rule face_preserving_jacobian_tangential_zero
      [OF openU xU xface df face])
  show "Determinants.det (jacobian f (at x)) =
      jacobian f (at x) $ Inl () $ Inl () *
        Determinants.det
          (tangential_block (jacobian f (at x)))"
    by (rule det_normal_tangential_block[OF zero])
qed

definition cart_tangent_inclusion ::
    "real ^ 'n::finite \<Rightarrow> real ^ (unit + 'n)"
  where "cart_tangent_inclusion u = product_to_cart (0,u)"

definition cart_tangent_projection ::
    "real ^ (unit + 'n::finite) \<Rightarrow> real ^ 'n"
  where "cart_tangent_projection v = (\<chi> i. v $ Inr i)"

lemma cart_tangent_inclusion_bounded_linear:
  "bounded_linear (cart_tangent_inclusion ::
    real ^ 'n::finite \<Rightarrow> real ^ (unit + 'n))"
  by (simp add: linear_conv_bounded_linear[symmetric])
     (rule linearI, auto simp: cart_tangent_inclusion_def
       product_to_cart_def vec_eq_iff split: sum.splits)

lemma cart_tangent_projection_bounded_linear:
  "bounded_linear (cart_tangent_projection ::
    real ^ (unit + 'n::finite) \<Rightarrow> real ^ 'n)"
  by (simp add: linear_conv_bounded_linear[symmetric])
     (rule linearI, auto simp: cart_tangent_projection_def
       vec_eq_iff)

lemma cart_tangent_inclusion_axis [simp]:
  "cart_tangent_inclusion (axis j 1 :: real ^ 'n::finite) =
    axis (Inr j) 1"
  by (simp add: cart_tangent_inclusion_def
    product_to_cart_def vec_eq_iff axis_def
    split: sum.splits)

lemma jacobian_restricted_to_face:
  fixes F :: "real ^ (unit + 'n::finite) \<Rightarrow>
    real ^ (unit + 'n)"
  assumes dF: "F differentiable (at (cart_tangent_inclusion y))"
  shows "jacobian
      (cart_tangent_projection \<circ> (F \<circ> cart_tangent_inclusion))
      (at y) =
    tangential_block (jacobian F
      (at (cart_tangent_inclusion y)))"
proof -
  let ?E = "cart_tangent_inclusion :: real ^ 'n \<Rightarrow> real ^ (unit + 'n)"
  let ?P = "cart_tangent_projection :: real ^ (unit + 'n) \<Rightarrow> real ^ 'n"
  let ?H = "?P \<circ> (F \<circ> ?E)"
  let ?x = "?E y"
  have dE: "?E differentiable (at y)"
    by (rule bounded_linear_imp_differentiable
      [OF cart_tangent_inclusion_bounded_linear])
  have dP: "?P differentiable (at (F ?x))"
    by (rule bounded_linear_imp_differentiable
      [OF cart_tangent_projection_bounded_linear])
  have dFE: "(F \<circ> ?E) differentiable (at y)"
    by (rule differentiable_chain_at[OF dE dF])
  have dP': "?P differentiable (at ((F \<circ> ?E) y))"
    using dP by simp
  have dH: "?H differentiable (at y)"
    by (rule differentiable_chain_at[OF dFE dP'])
  have Ederiv: "frechet_derivative ?E (at y) = ?E"
    by (rule frechet_derivative_at[symmetric])
       (rule bounded_linear.has_derivative
         [OF cart_tangent_inclusion_bounded_linear], simp)
  have Pderiv: "frechet_derivative ?P (at (F ?x)) = ?P"
    by (rule frechet_derivative_at[symmetric])
       (rule bounded_linear.has_derivative
         [OF cart_tangent_projection_bounded_linear], simp)
  have derivative:
    "frechet_derivative ?H (at y) =
      ?P \<circ> frechet_derivative F (at ?x) \<circ> ?E"
  proof -
    have dh1: "frechet_derivative ?H (at y) =
        frechet_derivative ?P (at (F ?x)) \<circ>
          frechet_derivative (F \<circ> ?E) (at y)"
      using frechet_derivative_compose[OF dFE dP']
      by (simp add: comp_def)
    have dh2: "frechet_derivative (F \<circ> ?E) (at y) =
        frechet_derivative F (at ?x) \<circ>
          frechet_derivative ?E (at y)"
      using frechet_derivative_compose[OF dE dF]
      by (simp add: comp_def)
    show ?thesis using dh1 dh2
      by (simp add: Ederiv Pderiv o_assoc)
  qed
  have delta: "(a::real) * (if b then 1 else 0) =
      (if b then a else 0)" for a b
    by simp
  show ?thesis
  proof (rule vec_eq_iff[THEN iffD2], intro allI)
    fix i
    show "jacobian ?H (at y) $ i =
      tangential_block (jacobian F (at ?x)) $ i"
    proof (rule vec_eq_iff[THEN iffD2], intro allI)
      fix j
      have h_entry:
        "jacobian ?H (at y) $ i $ j =
          frechet_derivative ?H (at y) (axis j 1) $ i"
        using frechet_derivative_jacobian[OF dH]
        by (simp add: matrix_vector_mult_def axis_def
          delta sum.delta)
      have f_entry:
        "frechet_derivative F (at ?x) (axis (Inr j) 1) $ Inr i =
          jacobian F (at ?x) $ Inr i $ Inr j"
        using frechet_derivative_jacobian[OF dF]
        by (simp add: matrix_vector_mult_def axis_def
          delta sum.delta)
      show "jacobian ?H (at y) $ i $ j =
        tangential_block (jacobian F (at ?x)) $ i $ j"
        using h_entry f_entry
        by (simp add: derivative cart_tangent_projection_def
          tangential_block_def)
    qed
  qed
qed

lemma tangential_block_product_face_jacobian:
  fixes f :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
    (real \<times> (real ^ 'n))"
  assumes dF: "cart_map_of_product f differentiable
    (at (product_to_cart (0,y)))"
  shows "tangential_block (jacobian (cart_map_of_product f)
      (at (product_to_cart (0,y)))) =
    jacobian (\<lambda>u. snd (f (0,u))) (at y)"
proof -
  have eqfun:
    "cart_tangent_projection \<circ>
      (cart_map_of_product f \<circ> cart_tangent_inclusion) =
      (\<lambda>u. snd (f (0,u)))"
    by (rule ext)
       (simp add: cart_tangent_projection_def
         cart_tangent_inclusion_def)
  have "jacobian (\<lambda>u. snd (f (0,u))) (at y) =
      tangential_block (jacobian (cart_map_of_product f)
        (at (cart_tangent_inclusion y)))"
    unfolding eqfun[symmetric]
    by (rule jacobian_restricted_to_face)
       (use dF in \<open>simp add: cart_tangent_inclusion_def\<close>)
  then show ?thesis
    by (simp add: cart_tangent_inclusion_def)
qed

theorem product_boundary_coeff_pull_tangential:
  fixes f g A :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))"
  assumes p_def: "p = (0,y)"
    and F_def: "F = cart_map_of_product f"
    and G_def: "G = cart_map_of_product g"
    and x_def: "x = product_to_cart p"
    and z_def: "z = F x"
    and openZ: "open Z"
    and fZ: "f p \<in> Z"
    and faceF: "fst (f p) = 0"
    and dg: "g differentiable (at (f p))"
    and faceG: "\<And>q. q \<in> Z \<Longrightarrow>
      fst q = 0 \<Longrightarrow> fst (g q) = 0"
    and f_zero: "\<And>j.
      jacobian F (at x) $ Inl () $ Inr j = 0"
    and inverse:
      "jacobian G (at z) ** jacobian F (at x) = mat 1"
  shows "product_boundary_coeff
      (product_pull_near_top f g A) y =
    Determinants.det (tangential_block
      (jacobian F (at x))) *
      product_boundary_coeff A (snd (f p))"
proof -
  have cofactor: "product_boundary_coeff
      (product_pull_near_top f g A) y =
    product_boundary_pull_cofactor f g
      (product_boundary_coeff A) y"
  proof -
    have fZ': "f (0,y) \<in> Z"
      using fZ p_def by simp
    have faceF': "fst (f (0,y)) = 0"
      using faceF p_def by simp
    have dg': "g differentiable (at (f (0,y)))"
      using dg p_def by simp
    show ?thesis
      by (rule product_boundary_coeff_pull_cofactor
        [where f=f and g=g and A=A and y=y and Z=Z,
          OF openZ fZ' faceF' dg' faceG])
  qed
  have g_zero: "\<And>j.
      jacobian G (at z) $ Inl () $ Inr j = 0"
  proof -
    let ?V = "cart_to_product -` Z"
    have openV: "open ?V"
    proof -
      have cont: "\<And>v. continuous (at v) cart_to_product"
        by (rule bounded_linear.continuous[OF
          cart_to_product_bounded_linear continuous_ident])
      show ?thesis
        by (rule continuous_open_vimage[OF openZ cont])
    qed
    have zV: "z \<in> ?V"
      using fZ by (simp add: z_def F_def x_def p_def)
    have zface: "z $ Inl () = 0"
      using faceF by (simp add: z_def F_def x_def p_def)
    have map_eq: "cart_form_of_product g = G"
      by (rule ext)
         (simp add: G_def cart_form_of_product_def
           cart_map_of_product_def)
    have dG: "G differentiable (at z)"
      unfolding map_eq[symmetric]
      using cart_form_of_product_differentiable[OF dg]
      by (simp add: z_def F_def x_def p_def)
    have faceGc: "\<And>w. w \<in> ?V \<Longrightarrow>
        w $ Inl () = 0 \<Longrightarrow> G w $ Inl () = 0"
      using faceG
      by (simp add: G_def cart_map_of_product_def
        cart_to_product_def)
    show "\<And>j.
      jacobian G (at z) $ Inl () $ Inr j = 0"
      by (rule face_preserving_jacobian_tangential_zero
        [OF openV zV zface dG faceGc])
  qed
  have factor: "Determinants.det (jacobian F (at x)) *
      jacobian G (at z) $ Inl () $ Inl () =
      Determinants.det (tangential_block
        (jacobian F (at x)))"
    by (rule inverse_cofactor_eq_tangential_det
      [OF inverse f_zero g_zero])
  show ?thesis
    using cofactor factor
    by (simp add: product_boundary_pull_cofactor_def
      p_def F_def G_def x_def z_def
      matrix_vector_mult_def axis_def sum_UNIV_unit_plus Let_def)
qed

theorem product_boundary_coeff_pull_face:
  fixes f g A :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))"
  assumes p_def: "p = (0,y)"
    and F_def: "F = cart_map_of_product f"
    and G_def: "G = cart_map_of_product g"
    and x_def: "x = product_to_cart p"
    and z_def: "z = F x"
    and openZ: "open Z"
    and fZ: "f p \<in> Z"
    and faceF: "fst (f p) = 0"
    and dg: "g differentiable (at (f p))"
    and faceG: "\<And>q. q \<in> Z \<Longrightarrow>
      fst q = 0 \<Longrightarrow> fst (g q) = 0"
    and dF: "F differentiable (at x)"
    and f_zero: "\<And>j.
      jacobian F (at x) $ Inl () $ Inr j = 0"
    and inverse:
      "jacobian G (at z) ** jacobian F (at x) = mat 1"
  shows "product_boundary_coeff
      (product_pull_near_top f g A) y =
    Determinants.det (jacobian
      (\<lambda>u. snd (f (0,u))) (at y)) *
      product_boundary_coeff A (snd (f (0,y)))"
proof -
  have pull: "product_boundary_coeff
      (product_pull_near_top f g A) y =
    Determinants.det (tangential_block
      (jacobian F (at x))) *
      product_boundary_coeff A (snd (f p))"
    by (rule product_boundary_coeff_pull_tangential
      [OF p_def F_def G_def x_def z_def openZ fZ faceF
        dg faceG f_zero inverse])
  have block: "tangential_block (jacobian F (at x)) =
      jacobian (\<lambda>u. snd (f (0,u))) (at y)"
    using tangential_block_product_face_jacobian[of f y]
      dF p_def F_def x_def
    by simp
  show ?thesis using pull block p_def by simp
qed

theorem product_boundary_coeff_pull_face_local_inverse:
  fixes f g A :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))"
  assumes openW: "open W" and openZ: "open Z"
    and yW: "(0,y) \<in> W"
    and fZ: "f (0,y) \<in> Z"
    and faceF: "fst (f (0,y)) = 0"
    and df: "f differentiable (at (0,y))"
    and dg: "g differentiable (at (f (0,y)))"
    and faceFw: "\<And>q. q \<in> W \<Longrightarrow>
      fst q = 0 \<Longrightarrow> fst (f q) = 0"
    and faceG: "\<And>q. q \<in> Z \<Longrightarrow>
      fst q = 0 \<Longrightarrow> fst (g q) = 0"
    and inverse: "\<And>q. q \<in> W \<Longrightarrow>
      0 \<le> fst q \<Longrightarrow> g (f q) = q"
  shows "product_boundary_coeff
      (product_pull_near_top f g A) y =
    Determinants.det (jacobian
      (\<lambda>u. snd (f (0,u))) (at y)) *
      product_boundary_coeff A (snd (f (0,y)))"
proof -
  let ?p = "(0,y)"
  let ?x = "product_to_cart ?p"
  let ?F = "cart_map_of_product f"
  let ?G = "cart_map_of_product g"
  let ?z = "?F ?x"
  let ?U = "cart_to_product -` W"
  have openU: "open ?U"
  proof -
    have cont: "\<And>v. continuous (at v) cart_to_product"
      by (rule bounded_linear.continuous[OF
        cart_to_product_bounded_linear continuous_ident])
    show ?thesis
      by (rule continuous_open_vimage[OF openW cont])
  qed
  have xU: "?x \<in> ?U"
    using yW by simp
  have xH: "?x \<in> cart_halfspace"
    by simp
  have mapF: "cart_form_of_product f = ?F"
    by (rule ext)
       (simp add: cart_form_of_product_def
         cart_map_of_product_def)
  have dF: "?F differentiable (at ?x)"
    unfolding mapF[symmetric]
    using cart_form_of_product_differentiable[OF df]
    by simp
  have mapG: "cart_form_of_product g = ?G"
    by (rule ext)
       (simp add: cart_form_of_product_def
         cart_map_of_product_def)
  have dG: "?G differentiable (at ?z)"
    unfolding mapG[symmetric]
    using cart_form_of_product_differentiable[OF dg]
    by simp
  have f_zero: "\<And>j.
      jacobian ?F (at ?x) $ Inl () $ Inr j = 0"
  proof (rule face_preserving_jacobian_tangential_zero
      [OF openU xU _ dF])
    show "?x $ Inl () = 0" by simp
    show "\<And>w. w \<in> ?U \<Longrightarrow>
      w $ Inl () = 0 \<Longrightarrow> ?F w $ Inl () = 0"
      using faceFw
      by (simp add: cart_map_of_product_def
        cart_to_product_def)
  qed
  have inverse': "\<And>v. v \<in> ?U \<Longrightarrow>
      v \<in> cart_halfspace \<Longrightarrow> ?G (?F v) = v"
  proof -
    fix v
    assume vU: "v \<in> ?U" and vH: "v \<in> cart_halfspace"
    have qW: "cart_to_product v \<in> W"
      using vU by simp
    have qH: "0 \<le> fst (cart_to_product v)"
      using vH
      by (simp add: cart_halfspace_def cart_to_product_def)
    show "?G (?F v) = v"
      by (simp add: cart_map_of_product_def
        inverse[OF qW qH])
  qed
  have inv_J: "jacobian ?F (at ?x) **
      jacobian ?G (at ?z) = mat 1"
    by (rule jacobian_local_inverse_halfspace
      [OF openU xU xH dF dG])
       (rule inverse')
  have inverse_J: "jacobian ?G (at ?z) **
      jacobian ?F (at ?x) = mat 1"
    by (rule matrix_left_right_inverse1[OF inv_J])
  show ?thesis
    by (rule product_boundary_coeff_pull_face
      [where p="?p" and F="?F" and G="?G"
        and x="?x" and z="?z" and Z=Z,
        OF refl refl refl refl refl openZ fZ faceF
          dg faceG dF f_zero inverse_J])
qed

end
