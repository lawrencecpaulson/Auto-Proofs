theory Stokes_Halfspace_Naturality
  imports Stokes_Cart_Product
begin

definition cart_halfspace :: "(real ^ (unit + 'n::finite)) set"
  where "cart_halfspace = {v. 0 \<le> v $ Inl ()}"

lemma cart_halfspace_ambient_derivative_unique:
  fixes F G :: "real ^ (unit + 'n::finite) \<Rightarrow>
      'b::real_normed_vector"
  assumes openU: "open U"
    and xU: "x \<in> U"
    and xH: "x \<in> cart_halfspace"
    and dF: "F differentiable (at x)"
    and dG: "G differentiable (at x)"
    and eq: "\<And>v. v \<in> U \<Longrightarrow>
      v \<in> cart_halfspace \<Longrightarrow> F v = G v"
  shows "frechet_derivative F (at x) =
    frechet_derivative G (at x)"
proof -
  let ?S = "U \<inter> cart_halfspace"
  obtain r where r: "0 < r" "ball x r \<subseteq> U"
    using openE[OF openU xU] by blast
  have near: "\<And>i e. i \<in> (Basis::(real ^ (unit + 'n)) set) \<Longrightarrow>
      e > 0 \<Longrightarrow>
      \<exists>d::real. 0 < \<bar>d\<bar> \<and> \<bar>d\<bar> < e \<and>
        x + d *\<^sub>R i \<in> ?S"
  proof -
    fix i :: "real ^ (unit + 'n)" and e :: real
    assume i: "i \<in> Basis" and e: "0 < e"
    let ?d = "min e r / 2"
    have d: "0 < ?d" "?d < e" "?d < r"
      using e r by auto
    have nonneg: "0 \<le> i $ Inl ()"
      using i by (auto simp: Basis_vec_def
        UNION_singleton_eq_range axis_def)
    have n: "norm i = 1"
      using i by simp
    have h: "x + ?d *\<^sub>R i \<in> cart_halfspace"
      using xH nonneg d
      by (simp add: cart_halfspace_def
        add_nonneg_nonneg mult_nonneg_nonneg)
    have u: "x + ?d *\<^sub>R i \<in> U"
      using r d n
      by (auto simp: dist_norm intro: subsetD[OF r(2)])
    show "\<exists>d::real. 0 < \<bar>d\<bar> \<and> \<bar>d\<bar> < e \<and>
        x + d *\<^sub>R i \<in> ?S"
      by (rule exI[of _ ?d])
         (use d h u in auto)
  qed
  have Fh: "(F has_derivative
      frechet_derivative F (at x)) (at x within ?S)"
    by (rule has_derivative_at_withinI
        [OF frechet_derivative_works[THEN iffD1, OF dF]])
  have Gh: "(G has_derivative
      frechet_derivative G (at x)) (at x within ?S)"
    by (rule has_derivative_at_withinI
        [OF frechet_derivative_works[THEN iffD1, OF dG]])
  have Gf: "(G has_derivative
      frechet_derivative F (at x)) (at x within ?S)"
    by (rule has_derivative_transform_within[OF Fh, of 1])
       (use xU xH eq in auto)
  show ?thesis
    by (rule frechet_derivative_unique_within[OF Gf Gh near])
qed

lemma matrix_inverse_field_derivative_halfspace:
  fixes F G :: "real ^ (unit + 'n::finite) \<Rightarrow>
      real ^ 'm::finite ^ 'm"
  assumes openU: "open U" and xU: "x \<in> U"
    and xH: "x \<in> cart_halfspace"
    and inverse: "\<And>y. y \<in> U \<Longrightarrow>
      y \<in> cart_halfspace \<Longrightarrow> F y ** G y = mat 1"
    and left_inverse: "G x ** F x = mat 1"
    and dF: "F differentiable (at x)"
    and dG: "G differentiable (at x)"
  shows "frechet_derivative G (at x) h =
    - (G x ** (frechet_derivative F (at x) h ** G x))"
proof -
  have DF: "(F has_derivative frechet_derivative F (at x)) (at x)"
    using dF by (simp add: frechet_derivative_works)
  have DG: "(G has_derivative frechet_derivative G (at x)) (at x)"
    using dG by (simp add: frechet_derivative_works)
  have dP: "((\<lambda>y. F y ** G y)
    has_derivative (\<lambda>h.
      F x ** frechet_derivative G (at x) h +
      frechet_derivative F (at x) h ** G x)) (at x)"
    by (rule bounded_bilinear.FDERIV
        [OF matrix_mult_bounded_bilinear DF DG])
  have prod_d: "(\<lambda>y. F y ** G y) differentiable (at x)"
    by (rule differentiableI[OF dP])
  have Dprod: "frechet_derivative (\<lambda>y. F y ** G y)
      (at x) = (\<lambda>h.
        F x ** frechet_derivative G (at x) h +
        frechet_derivative F (at x) h ** G x)"
    by (rule frechet_derivative_at[OF dP, symmetric])
  have zero: "frechet_derivative (\<lambda>y. F y ** G y)
      (at x) = (\<lambda>h. 0)"
    using cart_halfspace_ambient_derivative_unique
      [OF openU xU xH prod_d differentiable_const inverse]
    by simp
  have D: "F x ** frechet_derivative G (at x) h +
      frechet_derivative F (at x) h ** G x = 0"
    using Dprod zero by (simp add: fun_eq_iff)
  have "G x ** (F x ** frechet_derivative G (at x) h +
      frechet_derivative F (at x) h ** G x) = 0"
    by (simp add: D)
  then have "frechet_derivative G (at x) h +
      G x ** (frechet_derivative F (at x) h ** G x) = 0"
    by (simp add: matrix_add_ldistrib
      matrix_mul_assoc left_inverse)
  then show ?thesis
    by (simp add: eq_neg_iff_add_eq_0)
qed

theorem piola_matrix_field_closed_halfspace:
  fixes F G :: "real ^ (unit + 'n::finite) \<Rightarrow>
      real ^ (unit + 'n) ^ (unit + 'n)"
  assumes openU: "open U" and xU: "x \<in> U"
    and xH: "x \<in> cart_halfspace"
    and inverse: "\<And>y. y \<in> U \<Longrightarrow>
      y \<in> cart_halfspace \<Longrightarrow> F y ** G y = mat 1"
    and left_inverse: "G x ** F x = mat 1"
    and dF: "F differentiable (at x)"
    and dG: "G differentiable (at x)"
    and mixed: "\<And>i a b.
      frechet_derivative F (at x) (axis i 1) $ a $ b =
      frechet_derivative F (at x) (axis b 1) $ a $ i"
  shows "exterior_top
    (\<lambda>y. Determinants.det (F y) *\<^sub>R
      (G y *v axis j 1)) x = 0"
proof -
  let ?H = "\<lambda>i. frechet_derivative F (at x) (axis i 1)"
  let ?r = "Determinants.det (F x)"
  let ?rho = "\<lambda>y. Determinants.det (F y)"
  let ?V = "\<lambda>y. G y *v axis j 1"
  have drho: "?rho differentiable (at x)"
    by (rule matrix_det_differentiable[OF dF])
  have dV: "?V differentiable (at x)"
    by (rule matrix_column_field_differentiable[OF dG])
  have det_term: "frechet_derivative ?rho (at x) (axis i 1) *
      ?V x $ i =
    ?r * (\<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G x $ b $ a * ?H i $ a $ b * G x $ i $ j)"
    for i
    by (simp add: matrix_det_field_derivative[OF dF left_inverse]
      piola_trace_component)
  have inv_term: "frechet_derivative ?V (at x) (axis i 1) $ i =
    - (\<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G x $ i $ a * ?H i $ a $ b * G x $ b $ j)"
    for i
    by (simp add: matrix_column_field_derivative[OF dG]
      matrix_inverse_field_derivative_halfspace
        [OF openU xU xH inverse left_inverse dF dG]
      matrix_vector_mul_minus_stokes piola_inverse_component)
  have pos: "(\<Sum>i\<in>UNIV.
      frechet_derivative ?rho (at x) (axis i 1) * ?V x $ i) =
    ?r * (\<Sum>i\<in>UNIV. \<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G x $ b $ a * ?H i $ a $ b * G x $ i $ j)"
    by (simp add: det_term sum_distrib_left)
  have neg: "exterior_top ?V x =
    - (\<Sum>i\<in>UNIV. \<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G x $ i $ a * ?H i $ a $ b * G x $ b $ j)"
    by (simp add: exterior_top_coordinate inv_term sum_negf)
  have cancel: "(\<Sum>i\<in>UNIV. \<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G x $ b $ a * ?H i $ a $ b * G x $ i $ j) =
    (\<Sum>i\<in>UNIV. \<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G x $ i $ a * ?H i $ a $ b * G x $ b $ j)"
    by (rule piola_coordinate_cancellation[OF mixed])
  have "exterior_top
    (\<lambda>y. Determinants.det (F y) *\<^sub>R
      (G y *v axis j 1)) x =
    ?r * exterior_top ?V x +
      (\<Sum>i\<in>UNIV.
        frechet_derivative ?rho (at x) (axis i 1) * ?V x $ i)"
    by (rule exterior_top_scale[OF drho dV])
  then show ?thesis
    by (simp add: pos neg cancel)
qed

lemma jacobian_local_inverse_halfspace:
  fixes f g :: "real ^ (unit + 'n::finite) \<Rightarrow>
      real ^ (unit + 'n)"
  assumes openU: "open U" and xU: "x \<in> U"
    and xH: "x \<in> cart_halfspace"
    and df: "f differentiable (at x)"
    and dg: "g differentiable (at (f x))"
    and inverse: "\<And>y. y \<in> U \<Longrightarrow>
      y \<in> cart_halfspace \<Longrightarrow> g (f y) = y"
  shows "jacobian f (at x) ** jacobian g (at (f x)) = mat 1"
proof -
  have dc: "(g \<circ> f) differentiable (at x)"
    by (rule differentiable_chain_at[OF df dg])
  have di: "id differentiable (at x)"
    unfolding id_def
    by (rule differentiableI[OF has_derivative_ident])
  have derivative_eq:
    "frechet_derivative (g \<circ> f) (at x) =
      frechet_derivative id (at x)"
    by (rule cart_halfspace_ambient_derivative_unique
        [OF openU xU xH dc di])
       (simp add: inverse comp_def)
  have "jacobian g (at (f x)) ** jacobian f (at x) = mat 1"
    using jacobian_compose_at[OF df dg] derivative_eq
    by (simp add: jacobian_def matrix_id_mat_1)
  then show ?thesis by (rule matrix_left_right_inverse1)
qed

theorem cofactor_column_closed_C2_halfspace:
  fixes f g :: "real ^ (unit + 'n::finite) \<Rightarrow>
      real ^ (unit + 'n)"
  assumes C2f: "Ck_on 2 f U" and xU: "x \<in> U"
    and xH: "x \<in> cart_halfspace"
    and C2g: "Ck_on 2 g V"
    and image: "\<And>y. y \<in> U \<Longrightarrow>
      y \<in> cart_halfspace \<Longrightarrow> f y \<in> V"
    and inverse: "\<And>y. y \<in> U \<Longrightarrow>
      y \<in> cart_halfspace \<Longrightarrow> g (f y) = y"
  shows "exterior_top (cofactor_column f g j) x = 0"
proof -
  let ?F = "\<lambda>y. jacobian f (at y)"
  let ?G = "\<lambda>y. jacobian g (at (f y))"
  have openU: "open U" by (rule Ck_on_open[OF C2f])
  have C2f': "Ck_on (Suc 1) f U"
    using C2f by (metis Suc_1)
  have C2g': "Ck_on (Suc 1) g V"
    using C2g by (metis Suc_1)
  have df_on: "f differentiable (at y)" if "y \<in> U" for y
    using Ck_on_Suc_iff[of 1 f U, THEN iffD1, OF C2f']
      that by blast
  have dg_on: "g differentiable (at z)" if "z \<in> V" for z
    using Ck_on_Suc_iff[of 1 g V, THEN iffD1, OF C2g']
      that by blast
  have invJ: "?F y ** ?G y = mat 1"
    if yU: "y \<in> U" and yH: "y \<in> cart_halfspace"
    for y
    by (rule jacobian_local_inverse_halfspace
        [OF openU yU yH df_on[OF yU]
          dg_on[OF image[OF yU yH]]])
       (use inverse in auto)
  have inverseJ: "\<And>y. y \<in> U \<Longrightarrow>
      y \<in> cart_halfspace \<Longrightarrow> ?F y ** ?G y = mat 1"
    by (rule invJ)
  have left_inverse: "?G x ** ?F x = mat 1"
    by (rule matrix_left_right_inverse1[OF invJ[OF xU xH]])
  have dF: "?F differentiable (at x)"
    by (rule Ck_on_2_jacobian_differentiable[OF C2f xU])
  have dJg: "(\<lambda>y. jacobian g (at y))
      differentiable (at (f x))"
    by (rule Ck_on_2_jacobian_differentiable
        [OF C2g image[OF xU xH]])
  have dG: "?G differentiable (at x)"
    using differentiable_chain_at[OF df_on[OF xU] dJg]
    by (simp add: comp_def)
  have mixed: "\<And>i a b.
      frechet_derivative ?F (at x) (axis i 1) $ a $ b =
      frechet_derivative ?F (at x) (axis b 1) $ a $ i"
    by (rule Ck_on_2_jacobian_mixed[OF C2f xU])
  show ?thesis
    unfolding cofactor_column_def
    by (rule piola_matrix_field_closed_halfspace
        [OF openU xU xH inverseJ left_inverse dF dG mixed])
qed

theorem exterior_top_pull_near_top_C2_halfspace:
  fixes f g A :: "real ^ (unit + 'n::finite) \<Rightarrow>
      real ^ (unit + 'n)"
  assumes C2f: "Ck_on 2 f U" and xU: "x \<in> U"
    and xH: "x \<in> cart_halfspace"
    and C2g: "Ck_on 2 g V"
    and image: "\<And>y. y \<in> U \<Longrightarrow>
      y \<in> cart_halfspace \<Longrightarrow> f y \<in> V"
    and inverse: "\<And>y. y \<in> U \<Longrightarrow>
      y \<in> cart_halfspace \<Longrightarrow> g (f y) = y"
    and dA: "A differentiable (at (f x))"
  shows "exterior_top (pull_near_top f g A) x =
    pull_top f (exterior_top A) x"
proof -
  have openU: "open U" by (rule Ck_on_open[OF C2f])
  have C2f': "Ck_on (Suc 1) f U"
    using C2f by (metis Suc_1)
  have df: "f differentiable (at x)"
    using Ck_on_Suc_iff[of 1 f U, THEN iffD1, OF C2f']
      xU by blast
  have C2g': "Ck_on (Suc 1) g V"
    using C2g by (metis Suc_1)
  have dg: "g differentiable (at (f x))"
    using Ck_on_Suc_iff[of 1 g V, THEN iffD1, OF C2g']
      image[OF xU xH] by blast
  have inverse_J:
    "jacobian f (at x) ** jacobian g (at (f x)) = mat 1"
    by (rule jacobian_local_inverse_halfspace
        [OF openU xU xH df dg])
       (use inverse in auto)
  have dJf: "(\<lambda>y. jacobian f (at y)) differentiable (at x)"
    by (rule Ck_on_2_jacobian_differentiable[OF C2f xU])
  have dJg: "(\<lambda>y. jacobian g (at y))
      differentiable (at (f x))"
    by (rule Ck_on_2_jacobian_differentiable
        [OF C2g image[OF xU xH]])
  have piola: "exterior_top (cofactor_column f g j) x = 0"
    for j
    by (rule cofactor_column_closed_C2_halfspace
        [OF C2f xU xH C2g image inverse])
  show ?thesis
    by (rule exterior_top_pull_near_top_if_piola
        [OF df dA inverse_J dJf dJg piola])
qed

lemma cart_halfspace_product_iff [simp]:
  "product_to_cart p \<in> cart_halfspace \<longleftrightarrow> 0 \<le> fst p"
  by (simp add: cart_halfspace_def)

theorem product_exterior_top_pull_near_top_C2_halfspace:
  fixes f g A :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))"
  assumes C2f: "Ck_on 2 f W" and pW: "p \<in> W"
    and pH: "0 \<le> fst p"
    and C2g: "Ck_on 2 g Z"
    and image: "\<And>q. q \<in> W \<Longrightarrow>
      0 \<le> fst q \<Longrightarrow> f q \<in> Z"
    and inverse: "\<And>q. q \<in> W \<Longrightarrow>
      0 \<le> fst q \<Longrightarrow> g (f q) = q"
    and dA: "A differentiable (at (f p))"
  shows "product_exterior_top (product_pull_near_top f g A) p =
    product_pull_top f (product_exterior_top A) p"
proof -
  let ?U = "cart_to_product -` W"
  let ?V = "cart_to_product -` Z"
  let ?F = "cart_map_of_product f"
  let ?G = "cart_map_of_product g"
  let ?B = "cart_form_of_product A"
  let ?v = "product_to_cart p"
  have C2F: "Ck_on 2 ?F ?U"
    by (rule Ck_on_cart_map_of_product[OF C2f])
  have C2G: "Ck_on 2 ?G ?V"
    by (rule Ck_on_cart_map_of_product[OF C2g])
  have vU: "?v \<in> ?U"
    using pW by simp
  have vH: "?v \<in> cart_halfspace"
    using pH by simp
  have image': "\<And>v. v \<in> ?U \<Longrightarrow>
      v \<in> cart_halfspace \<Longrightarrow> ?F v \<in> ?V"
    using image
    by (simp add: cart_map_of_product_def
      cart_halfspace_def cart_to_product_def)
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
  have dB: "?B differentiable (at (?F ?v))"
    using cart_form_of_product_differentiable[OF dA]
    by simp
  have dPB: "pull_near_top ?F ?G ?B differentiable (at ?v)"
    by (rule pull_near_top_differentiable_C2
        [OF C2F vU C2G image'[OF vU vH] dB])
  have lhs: "product_exterior_top (product_pull_near_top f g A) p =
      exterior_top (pull_near_top ?F ?G ?B) ?v"
    unfolding product_pull_near_top_def
    by (rule exterior_top_product_form_of_cart[OF dPB])
  have nat: "exterior_top (pull_near_top ?F ?G ?B) ?v =
      pull_top ?F (exterior_top ?B) ?v"
    by (rule exterior_top_pull_near_top_C2_halfspace
        [OF C2F vU vH C2G image' inverse' dB])
  have rhs: "pull_top ?F (exterior_top ?B) ?v =
      product_pull_top f (product_exterior_top A) p"
    by (simp add: pull_top_def product_pull_top_def
      exterior_top_cart_form_of_product[OF dA])
  show ?thesis
    using lhs nat rhs by simp
qed

lemma cart_pull_near_top_normal_component:
  fixes f g A :: "real ^ (unit + 'n::finite) \<Rightarrow>
      real ^ (unit + 'n)"
  assumes tangential_zero: "\<And>j.
    jacobian g (at (f x)) $ Inl () $ Inr j = 0"
  shows "pull_near_top f g A x $ Inl () =
    Determinants.det (jacobian f (at x)) *
      (jacobian g (at (f x)) *v axis (Inl ()) 1) $ Inl () *
      A (f x) $ Inl ()"
proof -
  let ?G = "jacobian g (at (f x))"
  have component: "(?G *v A (f x)) $ Inl () =
      (?G *v axis (Inl ()) 1) $ Inl () *
        A (f x) $ Inl ()"
    by (simp add: matrix_vector_mult_def
      matrix_vector_mult_basis sum_UNIV_unit_plus
      tangential_zero)
  show ?thesis
    by (simp add: pull_near_top_def component algebra_simps)
qed

lemma face_preserving_jacobian_tangential_zero:
  fixes g :: "real ^ (unit + 'n::finite) \<Rightarrow>
      real ^ (unit + 'n)"
  assumes openV: "open V" and zV: "z \<in> V"
    and face_z: "z $ Inl () = 0"
    and dg: "g differentiable (at z)"
    and face: "\<And>w. w \<in> V \<Longrightarrow>
      w $ Inl () = 0 \<Longrightarrow> g w $ Inl () = 0"
  shows "jacobian g (at z) $ Inl () $ Inr j = 0"
proof -
  let ?e = "axis (Inr j) 1 :: real ^ (unit + 'n)"
  let ?l = "\<lambda>t::real. z + t *\<^sub>R ?e"
  let ?S = "{t::real. ?l t \<in> V}"
  have e0: "?e $ Inl () = 0"
    by (simp add: axis_def)
  have line_face: "?l t $ Inl () = 0" for t
    using face_z by (simp add: e0)
  have bl: "bounded_linear (\<lambda>t::real. t *\<^sub>R ?e)"
    by (rule bounded_linear_scaleR_left)
  have dlin: "((\<lambda>t::real. t *\<^sub>R ?e)
      has_derivative (\<lambda>h. h *\<^sub>R ?e)) (at 0)"
    by (rule bounded_linear.has_derivative[OF bl]) simp
  have dconst: "((\<lambda>t::real. z) has_derivative (\<lambda>h. 0)) (at 0)"
    by (rule has_derivative_const)
  have dl: "(?l has_vector_derivative ?e) (at 0)"
    using has_derivative_add[OF dconst dlin]
    by (simp add: has_vector_derivative_def)
  have dline_g: "((\<lambda>t. g (?l t))
      has_vector_derivative frechet_derivative g (at z) ?e)
      (at 0)"
    using frechet_derivative_along_line[OF _ dl, of g]
      dg by simp
  have dcomponent: "((\<lambda>t. g (?l t) $ Inl ())
      has_vector_derivative
        frechet_derivative g (at z) ?e $ Inl ())
      (at 0)"
    by (rule bounded_linear_after_vector_derivative
        [OF dline_g bounded_linear_vec_nth])
  have cont_lin: "\<And>t. continuous (at t)
      (\<lambda>u::real. u *\<^sub>R ?e)"
    by (rule bounded_linear.continuous[OF bl continuous_ident])
  have cont_l: "\<And>t. continuous (at t) ?l"
    by (intro continuous_intros cont_lin)
  have openS: "open ?S"
    using continuous_open_vimage[OF openV cont_l]
    by (simp add: vimage_def)
  have zeroS: "0 \<in> ?S"
    using zV by simp
  have zero: "((\<lambda>t. g (?l t) $ Inl ())
      has_vector_derivative 0) (at 0)"
    by (rule has_vector_derivative_transform_within_open
        [OF has_vector_derivative_const openS zeroS])
       (use face line_face in auto)
  have "frechet_derivative g (at z) ?e $ Inl () = 0"
    by (rule vector_derivative_unique_at[OF dcomponent zero])
  then show ?thesis
    by (simp add: jacobian_def matrix_def)
qed

lemma halfspace_preserving_jacobian_normal_nonneg:
  fixes g :: "real ^ (unit + 'n::finite) \<Rightarrow>
      real ^ (unit + 'n)"
  assumes openV: "open V" and zV: "z \<in> V"
    and zface: "z $ Inl () = 0"
    and gface: "g z $ Inl () = 0"
    and dg: "g differentiable (at z)"
    and halfspace: "\<And>w. w \<in> V \<Longrightarrow>
      w \<in> cart_halfspace \<Longrightarrow> g w \<in> cart_halfspace"
  shows "0 \<le> jacobian g (at z) $ Inl () $ Inl ()"
proof -
  let ?e = "axis (Inl ()) 1 :: real ^ (unit + 'n)"
  let ?l = "\<lambda>t::real. z + t *\<^sub>R ?e"
  let ?h = "\<lambda>t::real. g (?l t) $ Inl ()"
  let ?a = "frechet_derivative g (at z) ?e $ Inl ()"
  let ?S = "{t::real. ?l t \<in> V}"
  have bl: "bounded_linear (\<lambda>t::real. t *\<^sub>R ?e)"
    by (rule bounded_linear_scaleR_left)
  have dlin: "((\<lambda>t::real. t *\<^sub>R ?e)
      has_derivative (\<lambda>h. h *\<^sub>R ?e)) (at 0)"
    by (rule bounded_linear.has_derivative[OF bl]) simp
  have dconst: "((\<lambda>t::real. z) has_derivative (\<lambda>h. 0)) (at 0)"
    by (rule has_derivative_const)
  have dl: "(?l has_vector_derivative ?e) (at 0)"
    using has_derivative_add[OF dconst dlin]
    by (simp add: has_vector_derivative_def)
  have dline_g: "((\<lambda>t. g (?l t))
      has_vector_derivative frechet_derivative g (at z) ?e)
      (at 0)"
    using frechet_derivative_along_line[OF _ dl, of g]
      dg by simp
  have dh: "(?h has_real_derivative ?a) (at 0)"
    using bounded_linear_after_vector_derivative
      [OF dline_g bounded_linear_vec_nth]
    by (simp add: has_real_derivative_iff_has_vector_derivative)
  have cont_lin: "\<And>t. continuous (at t)
      (\<lambda>u::real. u *\<^sub>R ?e)"
    by (rule bounded_linear.continuous[OF bl continuous_ident])
  have cont_l: "\<And>t. continuous (at t) ?l"
    by (intro continuous_intros cont_lin)
  have openS: "open ?S"
    using continuous_open_vimage[OF openV cont_l]
    by (simp add: vimage_def)
  have zeroS: "0 \<in> ?S"
    using zV by simp
  obtain r where r: "0 < r" "ball 0 r \<subseteq> ?S"
    using openE[OF openS zeroS] by blast
  have h0: "?h 0 = 0"
    using gface by simp
  have ah: "?a = jacobian g (at z) $ Inl () $ Inl ()"
    by (simp add: jacobian_def matrix_def)
  show ?thesis
  proof (rule ccontr)
    assume "\<not> 0 \<le> jacobian g (at z) $ Inl () $ Inl ()"
    then have a: "?a < 0"
      using ah by simp
    obtain d where d: "0 < d"
      and dec: "\<And>s. 0 < s \<Longrightarrow> s < d \<Longrightarrow>
        ?h 0 > ?h s"
      using has_real_derivative_neg_dec_right[OF _ a, of ?h 0 UNIV]
        dh by auto
    let ?s = "min d r / 2"
    have s: "0 < ?s" "?s < d" "?s < r"
      using d r by auto
    have sS: "?s \<in> ?S"
      by (rule subsetD[OF r(2)])
         (use s in \<open>simp add: dist_real_def\<close>)
    have inV: "?l ?s \<in> V"
      using sS by simp
    have inH: "?l ?s \<in> cart_halfspace"
      using zface s
      by (simp add: cart_halfspace_def axis_def)
    have "0 \<le> ?h ?s"
      using halfspace[OF inV inH]
      by (simp add: cart_halfspace_def)
    moreover have "?h ?s < 0"
      using dec[OF s(1,2)] h0 by simp
    ultimately show False by simp
  qed
qed

lemma invertible_normal_entry_nonzero:
  fixes F G :: "real ^ (unit + 'n::finite) ^ (unit + 'n)"
  assumes inverse: "G ** F = mat 1"
    and tangential_zero: "\<And>j. G $ Inl () $ Inr j = 0"
  shows "G $ Inl () $ Inl () \<noteq> 0"
proof
  assume zero: "G $ Inl () $ Inl () = 0"
  have row_zero: "row (Inl ()) G = 0"
  proof (rule vec_eq_iff[THEN iffD2], intro allI)
    fix i
    show "row (Inl ()) G $ i = (0::real ^ (unit + 'n)) $ i"
      using zero tangential_zero
      by (cases i) (auto simp: row_def)
  qed
  have det_zero: "Determinants.det G = 0"
    by (rule det_zero_row[OF row_zero])
  have "Determinants.det G * Determinants.det F = 1"
    using inverse by (simp add: det_mul[symmetric])
  with det_zero show False by simp
qed

lemma halfspace_chart_normal_positive:
  fixes g :: "real ^ (unit + 'n::finite) \<Rightarrow>
      real ^ (unit + 'n)"
    and F :: "real ^ (unit + 'n) ^ (unit + 'n)"
  assumes openV: "open V" and zV: "z \<in> V"
    and zface: "z $ Inl () = 0"
    and gface: "g z $ Inl () = 0"
    and dg: "g differentiable (at z)"
    and halfspace: "\<And>w. w \<in> V \<Longrightarrow>
      w \<in> cart_halfspace \<Longrightarrow> g w \<in> cart_halfspace"
    and face: "\<And>w. w \<in> V \<Longrightarrow>
      w $ Inl () = 0 \<Longrightarrow> g w $ Inl () = 0"
    and inverse: "jacobian g (at z) ** F = mat 1"
  shows "0 < jacobian g (at z) $ Inl () $ Inl ()"
proof -
  have nonneg: "0 \<le> jacobian g (at z) $ Inl () $ Inl ()"
    by (rule halfspace_preserving_jacobian_normal_nonneg
        [OF openV zV zface gface dg halfspace])
  have zero: "\<And>j.
      jacobian g (at z) $ Inl () $ Inr j = 0"
    by (rule face_preserving_jacobian_tangential_zero
        [OF openV zV zface dg face])
  have nonzero: "jacobian g (at z) $ Inl () $ Inl () \<noteq> 0"
    by (rule invertible_normal_entry_nonzero
        [OF inverse zero])
  show ?thesis using nonneg nonzero by linarith
qed

definition product_boundary_pull_cofactor ::
    "((real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))) \<Rightarrow>
      ((real \<times> (real ^ 'n)) \<Rightarrow>
      (real \<times> (real ^ 'n))) \<Rightarrow>
      ((real ^ 'n) \<Rightarrow> real) \<Rightarrow>
      real ^ 'n \<Rightarrow> real"
  where "product_boundary_pull_cofactor f g T y =
    (let p = (0,y);
      F = cart_map_of_product f;
      G = cart_map_of_product g;
      x = product_to_cart p
    in Determinants.det (jacobian F (at x)) *
      (jacobian G (at (F x)) *v axis (Inl ()) 1) $ Inl () *
      T (snd (f p)))"

theorem product_boundary_coeff_pull_cofactor:
  fixes f g A :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))"
  assumes openZ: "open Z"
    and fZ: "f (0,y) \<in> Z"
    and faceF: "fst (f (0,y)) = 0"
    and dg: "g differentiable (at (f (0,y)))"
    and faceG: "\<And>q. q \<in> Z \<Longrightarrow>
      fst q = 0 \<Longrightarrow> fst (g q) = 0"
  shows "product_boundary_coeff
      (product_pull_near_top f g A) y =
    product_boundary_pull_cofactor f g
      (product_boundary_coeff A) y"
proof -
  let ?p = "(0,y)"
  let ?x = "product_to_cart ?p"
  let ?F = "cart_map_of_product f"
  let ?G = "cart_map_of_product g"
  let ?B = "cart_form_of_product A"
  let ?V = "cart_to_product -` Z"
  let ?z = "?F ?x"
  have openV: "open ?V"
  proof -
    have cont: "\<And>v. continuous (at v) cart_to_product"
      by (rule bounded_linear.continuous[OF
          cart_to_product_bounded_linear continuous_ident])
    show ?thesis
      by (rule continuous_open_vimage[OF openZ cont])
  qed
  have zV: "?z \<in> ?V"
    using fZ by simp
  have zface: "?z $ Inl () = 0"
    using faceF by simp
  have map_eq: "cart_form_of_product g = ?G"
    by (rule ext)
       (simp add: cart_form_of_product_def
         cart_map_of_product_def)
  have dG: "?G differentiable (at ?z)"
    unfolding map_eq[symmetric]
    using cart_form_of_product_differentiable[OF dg]
    by simp
  have faceGc: "\<And>w. w \<in> ?V \<Longrightarrow>
      w $ Inl () = 0 \<Longrightarrow> ?G w $ Inl () = 0"
    using faceG
    by (simp add: cart_map_of_product_def
      cart_to_product_def)
  have zero: "\<And>j.
      jacobian ?G (at ?z) $ Inl () $ Inr j = 0"
    by (rule face_preserving_jacobian_tangential_zero
        [OF openV zV zface dG faceGc])
  have raw: "pull_near_top ?F ?G ?B ?x $ Inl () =
    Determinants.det (jacobian ?F (at ?x)) *
      (jacobian ?G (at ?z) *v axis (Inl ()) 1) $ Inl () *
      ?B (?F ?x) $ Inl ()"
    by (rule cart_pull_near_top_normal_component)
       (rule zero)
  have component: "pull_near_top ?F ?G ?B ?x $ Inl () =
    Determinants.det (jacobian ?F (at ?x)) *
      (jacobian ?G (at ?z) *v axis (Inl ()) 1) $ Inl () *
      fst (A (f ?p))"
    using raw
    by (simp add: cart_form_of_product_def)
  have fp: "f ?p = (0, snd (f ?p))"
    using faceF by (cases "f ?p") auto
  have trace: "product_normal_coeff
      (product_pull_near_top f g A) 0 y =
    Determinants.det (jacobian ?F (at ?x)) *
      (jacobian ?G (at ?z) *v axis (Inl ()) 1) $ Inl () *
      fst (A (f ?p))"
    using component
    by (simp add: product_normal_coeff_def
      product_pull_near_top_def product_form_of_cart_def
      cart_to_product_def)
  have face_coeff: "product_normal_coeff A 0 (snd (f ?p)) =
      fst (A (f ?p))"
  proof -
    have "A (f ?p) = A (0, snd (f ?p))"
      by (rule arg_cong[OF fp])
    then show ?thesis
      by (simp add: product_normal_coeff_def)
  qed
  have lhs: "product_boundary_coeff
      (product_pull_near_top f g A) y =
      - (Determinants.det (jacobian ?F (at ?x)) *
        (jacobian ?G (at ?z) *v axis (Inl ()) 1) $ Inl () *
        fst (A (f ?p)))"
    using trace by (simp add: product_boundary_coeff_def)
  have rhs: "product_boundary_pull_cofactor f g
      (product_boundary_coeff A) y =
      - (Determinants.det (jacobian ?F (at ?x)) *
        (jacobian ?G (at ?z) *v axis (Inl ()) 1) $ Inl () *
        fst (A (f ?p)))"
    by (simp add: product_boundary_pull_cofactor_def
      product_boundary_coeff_def face_coeff
      Let_def algebra_simps)
  show ?thesis
    using lhs rhs by simp
qed

end
