theory Global_Gluing
  imports Smooth_Partition Single_Chart
begin

lemma has_derivative_if_matching:
  fixes f g :: "'a::real_normed_vector \<Rightarrow>
    'b::real_normed_vector"
  assumes df: "(f has_derivative D) (at x)"
    and dg: "(g has_derivative D) (at x)"
    and agree: "f x = g x"
  shows "((\<lambda>y. if P y then f y else g y)
    has_derivative D) (at x)"
proof -
  let ?H = "\<lambda>y. max
    (norm ((f y - f x) - D (y - x)) /
      norm (y - x))
    (norm ((g y - g x) - D (y - x)) /
      norm (y - x))"
  have bounded: "bounded_linear D"
    using df by (simp add: has_derivative_iff_norm)
  have tend_f: "((\<lambda>y.
      norm ((f y - f x) - D (y - x)) /
        norm (y - x)) \<longlongrightarrow> 0) (at x)"
    using df by (simp add: has_derivative_iff_norm)
  have tend_g: "((\<lambda>y.
      norm ((g y - g x) - D (y - x)) /
        norm (y - x)) \<longlongrightarrow> 0) (at x)"
    using dg by (simp add: has_derivative_iff_norm)
  have tend_H: "(?H \<longlongrightarrow> 0) (at x)"
    using tendsto_max[OF tend_f tend_g]
    by simp
  show ?thesis
    apply (rule has_derivativeI_sandwich
      [where e=1 and H="?H"])
    using bounded tend_H agree
    by (auto simp: le_max_iff_disj
      split: if_splits)
qed

definition stokes_face_projection ::
    "real \<times> 'a \<Rightarrow> real \<times> 'a"
  where "stokes_face_projection p = (0,snd p)"

definition stokes_normal_reflection ::
    "real \<times> 'a \<Rightarrow> real \<times> 'a"
  where "stokes_normal_reflection p =
    (- fst p,snd p)"

lemma stokes_face_projection_bounded_linear:
  "bounded_linear (stokes_face_projection ::
    real \<times> 'a::euclidean_space \<Rightarrow>
      real \<times> 'a)"
proof -
  have "linear (stokes_face_projection ::
      real \<times> 'a \<Rightarrow> real \<times> 'a)"
    by (rule linearI)
       (auto simp: stokes_face_projection_def)
  then show ?thesis
    by (simp add: linear_conv_bounded_linear[symmetric])
qed

lemma stokes_normal_reflection_bounded_linear:
  "bounded_linear (stokes_normal_reflection ::
    real \<times> 'a::euclidean_space \<Rightarrow>
      real \<times> 'a)"
proof -
  have "linear (stokes_normal_reflection ::
      real \<times> 'a \<Rightarrow> real \<times> 'a)"
    by (rule linearI)
       (auto simp: stokes_normal_reflection_def)
  then show ?thesis
    by (simp add: linear_conv_bounded_linear[symmetric])
qed

definition stokes_reflect_extension ::
    "(real \<times> 'a::real_normed_vector \<Rightarrow>
      'b::real_normed_vector) \<Rightarrow>
    real \<times> 'a \<Rightarrow> 'b"
  where "stokes_reflect_extension f p =
    (if 0 \<le> fst p then f p
     else 2 *\<^sub>R f (stokes_face_projection p) -
       f (stokes_normal_reflection p))"

lemma stokes_reflect_extension_face_derivative:
  fixes f :: "real \<times> 'a::euclidean_space \<Rightarrow>
    'b::real_normed_vector"
  assumes face: "fst x = 0"
    and df: "f differentiable (at x)"
  shows "stokes_reflect_extension f
      differentiable (at x)"
    and "frechet_derivative
      (stokes_reflect_extension f) (at x) =
      frechet_derivative f (at x)"
proof -
  obtain D where fD: "(f has_derivative D) (at x)"
    using df by (auto simp: differentiable_def)
  have boundedD: "bounded_linear D"
    by (rule has_derivative_bounded_linear[OF fD])
  have linearD: "linear D"
    by (rule bounded_linear.linear[OF boundedD])
  have Px: "stokes_face_projection x = x"
    using face by (cases x)
      (simp add: stokes_face_projection_def)
  have Rx: "stokes_normal_reflection x = x"
    using face by (cases x)
      (simp add: stokes_normal_reflection_def)
  have Pder: "(stokes_face_projection
      has_derivative stokes_face_projection) (at x)"
    using bounded_linear.has_derivative
      [OF stokes_face_projection_bounded_linear
        has_derivative_id]
    by simp
  have Rder: "(stokes_normal_reflection
      has_derivative stokes_normal_reflection) (at x)"
    using bounded_linear.has_derivative
      [OF stokes_normal_reflection_bounded_linear
        has_derivative_id]
    by simp
  have fP: "((\<lambda>z. f (stokes_face_projection z))
      has_derivative
      (\<lambda>h. D (stokes_face_projection h))) (at x)"
    by (rule has_derivative_compose[OF Pder])
       (simp add: Px fD)
  have fR: "((\<lambda>z. f (stokes_normal_reflection z))
      has_derivative
      (\<lambda>h. D (stokes_normal_reflection h)))
        (at x)"
    by (rule has_derivative_compose[OF Rder])
       (simp add: Rx fD)
  have neg_der: "((\<lambda>z.
      2 *\<^sub>R f (stokes_face_projection z) -
        f (stokes_normal_reflection z))
      has_derivative
      (\<lambda>h.
        2 *\<^sub>R D (stokes_face_projection h) -
          D (stokes_normal_reflection h))) (at x)"
    by (intro has_derivative_diff
      has_derivative_scaleR_right fP fR)
  have Dh: "2 *\<^sub>R D (stokes_face_projection h) -
      D (stokes_normal_reflection h) = D h"
    for h
  proof -
    have id: "2 *\<^sub>R stokes_face_projection h -
        stokes_normal_reflection h = h"
      by (cases h)
         (simp add: stokes_face_projection_def
           stokes_normal_reflection_def
           scaleR_2)
    have "2 *\<^sub>R D (stokes_face_projection h) -
        D (stokes_normal_reflection h) =
      D (2 *\<^sub>R stokes_face_projection h -
        stokes_normal_reflection h)"
      by (simp add: linearD linear.scaleR
        linear_diff)
    also have "\<dots> = D h"
      by (simp only: id)
    finally show ?thesis .
  qed
  have neg_eq: "(\<lambda>h.
      2 *\<^sub>R D (stokes_face_projection h) -
        D (stokes_normal_reflection h)) = D"
    by (rule ext) (rule Dh)
  have neg_der_same: "((\<lambda>z.
      2 *\<^sub>R f (stokes_face_projection z) -
        f (stokes_normal_reflection z))
      has_derivative D) (at x)"
    using neg_der by (simp only: neg_eq)
  have val_eq: "f x =
      2 *\<^sub>R f (stokes_face_projection x) -
        f (stokes_normal_reflection x)"
    by (simp add: Px Rx scaleR_2)
  have der: "(stokes_reflect_extension f
      has_derivative D) (at x)"
    unfolding stokes_reflect_extension_def
    by (rule has_derivative_if_matching
      [OF fD neg_der_same val_eq])
  show "stokes_reflect_extension f
      differentiable (at x)"
    unfolding differentiable_def
    by (rule exI[where x=D]) (rule der)
  show "frechet_derivative
      (stokes_reflect_extension f) (at x) =
      frechet_derivative f (at x)"
    using frechet_derivative_at[OF der]
      frechet_derivative_at[OF fD]
    by simp
qed

lemma stokes_reflect_extension_halfspace_derivative:
  fixes f :: "real \<times> 'a::euclidean_space \<Rightarrow>
    'b::real_normed_vector"
  assumes half: "x \<in> closed_halfspace"
    and df: "f differentiable (at x)"
  shows "stokes_reflect_extension f
      differentiable (at x) \<and>
    frechet_derivative
      (stokes_reflect_extension f) (at x) =
      frechet_derivative f (at x)"
proof (cases "fst x = 0")
  case True
  show ?thesis
    using stokes_reflect_extension_face_derivative
      [OF True df] by blast
next
  case False
  have positive: "0 < fst x"
    using half False
    by (auto simp: closed_halfspace_def)
  have xopen: "x \<in> open_halfspace"
    using positive by (simp add: open_halfspace_def)
  have eq: "stokes_reflect_extension f z = f z"
    if "z \<in> open_halfspace" for z
    using that
    by (simp add: stokes_reflect_extension_def
      open_halfspace_def)
  have diff: "stokes_reflect_extension f
      differentiable (at x)"
    by (rule differentiable_transform_within_open
      [OF df open_open_halfspace xopen])
       (use eq in auto)
  have deriv: "frechet_derivative
      (stokes_reflect_extension f) (at x) =
      frechet_derivative f (at x)"
    by (rule frechet_derivative_transform_within_open
      [OF open_open_halfspace xopen])
       (use eq in auto)
  show ?thesis using diff deriv by simp
qed

lemma stokes_reflect_extension_local_C1:
  fixes f G :: "real \<times> 'a::euclidean_space \<Rightarrow>
    'b::real_normed_vector"
  assumes openC:
      "openin (top_of_set closed_halfspace) C"
    and xC: "x \<in> C"
    and smooth: "Ck_on 1 G U"
    and xU: "x \<in> U"
    and agree: "\<And>z. z \<in> U \<inter> C \<Longrightarrow>
      f z = G z"
  shows "stokes_reflect_extension f
      differentiable (at x) \<and>
    frechet_derivative
      (stokes_reflect_extension f) (at x) =
      frechet_derivative G (at x)"
proof -
  obtain W where openW: "open W"
    and C: "C = closed_halfspace \<inter> W"
    using openC by (auto simp: openin_open)
  have xH: "x \<in> closed_halfspace"
    using xC C by auto
  have xW: "x \<in> W"
    using xC C by auto
  have openU: "open U"
    by (rule Ck_on_open[OF smooth])
  have dG: "G differentiable (at x)"
    using Ck_onD[OF smooth xU]
    by (simp add: Ck_at.simps)
  show ?thesis
  proof (cases "0 < fst x")
    case True
    let ?V = "U \<inter> W \<inter> open_halfspace"
    have openV: "open ?V"
      using openU openW open_open_halfspace by auto
    have xV: "x \<in> ?V"
      using True xU xW
      by (simp add: open_halfspace_def)
    have eqV: "stokes_reflect_extension f z = G z"
      if z: "z \<in> ?V" for z
    proof -
      have zC: "z \<in> C"
        using z C
        by (auto simp: open_halfspace_def
          closed_halfspace_def)
      show ?thesis
        using agree[of z] z zC
        by (simp add: stokes_reflect_extension_def
          open_halfspace_def)
    qed
    have diff: "stokes_reflect_extension f
        differentiable (at x)"
      by (rule differentiable_transform_within_open
        [OF dG openV xV])
         (use eqV in auto)
    have deriv: "frechet_derivative
        (stokes_reflect_extension f) (at x) =
        frechet_derivative G (at x)"
      by (rule frechet_derivative_transform_within_open
        [OF openV xV])
         (use eqV in auto)
    show ?thesis using diff deriv by simp
  next
    case False
    have face: "fst x = 0"
      using xH False
      by (auto simp: closed_halfspace_def)
    let ?O = "U \<inter> W"
    let ?V = "?O \<inter>
      stokes_face_projection -` ?O \<inter>
      stokes_normal_reflection -` ?O"
    have openO: "open ?O"
      using openU openW by auto
    have contP: "continuous_on UNIV
        (stokes_face_projection ::
          real \<times> 'a \<Rightarrow> real \<times> 'a)"
      by (rule bounded_linear.continuous_on
        [OF stokes_face_projection_bounded_linear
          continuous_on_id])
    have contR: "continuous_on UNIV
        (stokes_normal_reflection ::
          real \<times> 'a \<Rightarrow> real \<times> 'a)"
      by (rule bounded_linear.continuous_on
        [OF stokes_normal_reflection_bounded_linear
          continuous_on_id])
    have openV: "open ?V"
      using open_vimage[OF openO contP]
        open_vimage[OF openO contR] openO
      by auto
    have Px: "stokes_face_projection x = x"
      using face by (cases x)
        (simp add: stokes_face_projection_def)
    have Rx: "stokes_normal_reflection x = x"
      using face by (cases x)
        (simp add: stokes_normal_reflection_def)
    have xV: "x \<in> ?V"
      using xU xW Px Rx by auto
    have eqV: "stokes_reflect_extension f z =
        stokes_reflect_extension G z"
      if z: "z \<in> ?V" for z
    proof (cases "0 \<le> fst z")
      case True
      have zC: "z \<in> C"
        using z True C
        by (auto simp: closed_halfspace_def)
      show ?thesis
        using agree[of z] z zC True
        by (simp add: stokes_reflect_extension_def)
    next
      case False
      have PzC: "stokes_face_projection z \<in> C"
        using z C
        by (auto simp: stokes_face_projection_def
          closed_halfspace_def)
      have RzC: "stokes_normal_reflection z \<in> C"
        using z C False
        by (auto simp: stokes_normal_reflection_def
          closed_halfspace_def)
      have eqP: "f (stokes_face_projection z) =
          G (stokes_face_projection z)"
        by (rule agree) (use z PzC in auto)
      have eqR: "f (stokes_normal_reflection z) =
          G (stokes_normal_reflection z)"
        by (rule agree) (use z RzC in auto)
      show ?thesis
        using False eqP eqR
        by (simp add: stokes_reflect_extension_def)
    qed
    have extG: "stokes_reflect_extension G
        differentiable (at x) \<and>
      frechet_derivative
        (stokes_reflect_extension G) (at x) =
        frechet_derivative G (at x)"
      by (rule stokes_reflect_extension_halfspace_derivative
        [OF xH dG])
    have diff: "stokes_reflect_extension f
        differentiable (at x)"
      by (rule differentiable_transform_within_open
        [OF conjunct1[OF extG] openV xV])
         (use eqV in auto)
    have deriv: "frechet_derivative
        (stokes_reflect_extension f) (at x) =
        frechet_derivative
          (stokes_reflect_extension G) (at x)"
      by (rule frechet_derivative_transform_within_open
        [OF openV xV])
         (use eqV in auto)
    show ?thesis
      using diff deriv extG by simp
  qed
qed

lemma product_to_cart_scaleR [simp]:
  "product_to_cart (c *\<^sub>R p) =
    c *\<^sub>R product_to_cart p"
  by (simp add: product_to_cart_def vec_eq_iff
    split: sum.splits)

lemma cart_to_product_scaleR [simp]:
  "cart_to_product (c *\<^sub>R v) =
    c *\<^sub>R cart_to_product v"
  by (simp add: cart_to_product_def vec_eq_iff)

lemma product_pull_near_top_weight:
  fixes f g A :: "real \<times> (real ^ 'n::finite)
    \<Rightarrow> real \<times> (real ^ 'n)"
  shows "product_pull_near_top f g
      (\<lambda>z. r z *\<^sub>R A z) x =
    r (f x) *\<^sub>R product_pull_near_top f g A x"
  by (simp add: product_pull_near_top_def
    product_form_of_cart_def pull_near_top_def
    cart_form_of_product_def cart_map_of_product_def
    matrix_vector_mult_scaleR scaleR_scaleR)

lemma product_pull_near_top_cong_at:
  fixes f g A B :: "real \<times> (real ^ 'n::finite)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes eq: "A (f x) = B (f x)"
  shows "product_pull_near_top f g A x =
    product_pull_near_top f g B x"
  using eq
  by (simp add: product_pull_near_top_def
    product_form_of_cart_def pull_near_top_def
    cart_form_of_product_def cart_map_of_product_def)

lemma stokes_product_normal_derivative_scale:
  fixes A :: "real \<times> 'a::euclidean_space \<Rightarrow>
    real \<times> 'a"
    and rho :: "real \<times> 'a \<Rightarrow> real"
  assumes drho: "rho differentiable (at (t,y))"
    and dA: "A differentiable (at (t,y))"
  shows "product_normal_derivative
      (\<lambda>p. rho p *\<^sub>R A p) t y =
    rho (t,y) * product_normal_derivative A t y +
    frechet_derivative rho (at (t,y)) (1,0) *
      fst (A (t,y))"
  using drho dA
  by (simp add: product_normal_derivative_def
    frechet_derivative_bilinear
      [OF bounded_bilinear_scaleR drho dA]
    algebra_simps)

lemma stokes_product_tangential_derivative_scale:
  fixes A :: "real \<times> 'a::euclidean_space \<Rightarrow>
    real \<times> 'a"
    and rho :: "real \<times> 'a \<Rightarrow> real"
  assumes drho: "rho differentiable (at (t,y))"
    and dA: "A differentiable (at (t,y))"
  shows "product_tangential_derivative
      (\<lambda>p. rho p *\<^sub>R A p) b t y =
    rho (t,y) * product_tangential_derivative A b t y -
    frechet_derivative rho (at (t,y)) (0,b) *
      (snd (A (t,y)) \<bullet> b)"
  using drho dA
  by (simp add: product_tangential_derivative_def
    frechet_derivative_bilinear
      [OF bounded_bilinear_scaleR drho dA]
    algebra_simps)

lemma stokes_product_normal_derivative_continuous_on:
  fixes A :: "real \<times> 'a::euclidean_space \<Rightarrow>
    real \<times> 'a"
    and rho :: "real \<times> 'a \<Rightarrow> real"
  assumes drho: "\<And>p. p \<in> C \<Longrightarrow>
      rho differentiable (at p)"
    and dA: "\<And>p. p \<in> C \<Longrightarrow>
      A differentiable (at p)"
    and cont_rho: "continuous_on C rho"
    and cont_A: "continuous_on C A"
    and cont_Drho: "continuous_on C
      (\<lambda>p. frechet_derivative rho (at p) (1,0))"
    and cont_AP: "continuous_on C
      (case_prod (product_normal_derivative A))"
  shows "continuous_on C
    (case_prod (product_normal_derivative
      (\<lambda>p. rho p *\<^sub>R A p)))"
proof -
  let ?R = "case_prod (product_normal_derivative A)"
  let ?D = "\<lambda>p. frechet_derivative rho (at p) (1,0)"
  have cont: "continuous_on C
      (\<lambda>p. rho p * ?R p + ?D p * fst (A p))"
    by (intro continuous_intros cont_rho cont_AP
      cont_Drho cont_A)
  show ?thesis
  proof (rule continuous_on_eq[OF cont])
    fix p assume p: "p \<in> C"
    show "rho p * ?R p + ?D p * fst (A p) =
      case_prod (product_normal_derivative
        (\<lambda>q. rho q *\<^sub>R A q)) p"
      using drho[OF p] dA[OF p]
      by (cases p)
         (simp add:
           stokes_product_normal_derivative_scale)
  qed
qed

lemma stokes_product_tangential_derivative_continuous_on:
  fixes A :: "real \<times> 'a::euclidean_space \<Rightarrow>
    real \<times> 'a"
    and rho :: "real \<times> 'a \<Rightarrow> real"
  assumes drho: "\<And>p. p \<in> C \<Longrightarrow>
      rho differentiable (at p)"
    and dA: "\<And>p. p \<in> C \<Longrightarrow>
      A differentiable (at p)"
    and cont_rho: "continuous_on C rho"
    and cont_A: "continuous_on C A"
    and cont_Drho: "continuous_on C
      (\<lambda>p. frechet_derivative rho (at p) (0,b))"
    and cont_AQ: "continuous_on C
      (case_prod (product_tangential_derivative A b))"
  shows "continuous_on C
    (case_prod (product_tangential_derivative
      (\<lambda>p. rho p *\<^sub>R A p) b))"
proof -
  let ?R = "case_prod (product_tangential_derivative A b)"
  let ?D = "\<lambda>p. frechet_derivative rho (at p) (0,b)"
  have cont: "continuous_on C
      (\<lambda>p. rho p * ?R p -
        ?D p * (snd (A p) \<bullet> b))"
    by (intro continuous_intros cont_rho cont_AQ
      cont_Drho cont_A)
  show ?thesis
  proof (rule continuous_on_eq[OF cont])
    fix p assume p: "p \<in> C"
    show "rho p * ?R p -
      ?D p * (snd (A p) \<bullet> b) =
      case_prod (product_tangential_derivative
        (\<lambda>q. rho q *\<^sub>R A q) b) p"
      using drho[OF p] dA[OF p]
      by (cases p)
         (simp add:
           stokes_product_tangential_derivative_scale)
  qed
qed

lemma stokes_differentiable_continuous_on:
  assumes diff: "\<And>x. x \<in> C \<Longrightarrow>
    f differentiable (at x)"
  shows "continuous_on C f"
  unfolding continuous_on_eq_continuous_within
  by (auto intro:
    differentiable_imp_continuous_within
    differentiable_at_withinI diff)

context smooth_oriented_C2_halfspace_atlas
begin

lemma chartwise_C1_reflected_pointwise:
  assumes C1: "chartwise_C1_scalar rho"
    and j: "j \<in> I"
    and x: "x \<in> C j"
  shows "stokes_reflect_extension
      (\<lambda>z. rho (from_chart j z))
      differentiable (at x)"
    and "stokes_reflect_extension
      (\<lambda>z. rho (from_chart j z)) x =
      rho (from_chart j x)"
proof -
  have ex: "\<exists>U G. Ck_on 1 G U \<and> x \<in> U \<and>
      (\<forall>z\<in>U \<inter> C j.
        G z = rho (from_chart j z))"
    using C1 j x
    by (simp add: chartwise_C1_scalar_def)
  obtain U G where smooth: "Ck_on 1 G U"
    and xU: "x \<in> U"
    and agree: "\<forall>z\<in>U \<inter> C j.
      G z = rho (from_chart j z)"
    using ex by blast
  have openC:
      "openin (top_of_set closed_halfspace) (C j)"
    by (rule halfspace_chart.open_C[OF chart[OF j]])
  have diff: "stokes_reflect_extension
      (\<lambda>z. rho (from_chart j z))
      differentiable (at x)"
    using stokes_reflect_extension_local_C1
      [OF openC x smooth xU, of
        "\<lambda>z. rho (from_chart j z)"]
      agree
    by auto
  show "stokes_reflect_extension
      (\<lambda>z. rho (from_chart j z))
      differentiable (at x)"
    by (rule diff)
  have xH: "x \<in> closed_halfspace"
    using openC x by (auto simp: openin_open)
  show "stokes_reflect_extension
      (\<lambda>z. rho (from_chart j z)) x =
      rho (from_chart j x)"
    using xH
    by (simp add: stokes_reflect_extension_def
      closed_halfspace_def)
qed

lemma chartwise_C1_reflected_derivative_continuous:
  assumes C1: "chartwise_C1_scalar rho"
    and j: "j \<in> I"
  shows "continuous_on (C j)
    (\<lambda>x. frechet_derivative
      (stokes_reflect_extension
        (\<lambda>z. rho (from_chart j z)))
      (at x) v)"
proof (simp add: continuous_on_eq_continuous_within, intro ballI)
  fix x assume x: "x \<in> C j"
  have ex: "\<exists>U G. Ck_on 1 G U \<and> x \<in> U \<and>
      (\<forall>z\<in>U \<inter> C j.
        G z = rho (from_chart j z))"
    using C1 j x
    by (simp add: chartwise_C1_scalar_def)
  obtain U G where smooth: "Ck_on 1 G U"
    and xU: "x \<in> U"
    and agree: "\<forall>z\<in>U \<inter> C j.
      G z = rho (from_chart j z)"
    using ex by blast
  have openC:
      "openin (top_of_set closed_halfspace) (C j)"
    by (rule halfspace_chart.open_C[OF chart[OF j]])
  have openU: "open U"
    by (rule Ck_on_open[OF smooth])
  have contG: "continuous_on U
      (\<lambda>z. frechet_derivative G (at z) v)"
    using smooth
    by (cases v)
       (auto simp: Ck_on_Suc_iff Ck_on_0_iff)
  have eq: "frechet_derivative
      (stokes_reflect_extension
        (\<lambda>w. rho (from_chart j w))) (at z) v =
      frechet_derivative G (at z) v"
    if z: "z \<in> U \<inter> C j" for z
  proof -
    have dz: "stokes_reflect_extension
        (\<lambda>w. rho (from_chart j w))
        differentiable (at z) \<and>
      frechet_derivative
        (stokes_reflect_extension
          (\<lambda>w. rho (from_chart j w))) (at z) =
        frechet_derivative G (at z)"
      by (rule stokes_reflect_extension_local_C1
        [OF openC _ smooth])
         (use z agree in auto)
    show ?thesis using dz by simp
  qed
  have cont_local: "continuous_on (U \<inter> C j)
      (\<lambda>z. frechet_derivative
        (stokes_reflect_extension
          (\<lambda>w. rho (from_chart j w)))
        (at z) v)"
    by (rule continuous_on_eq
      [OF continuous_on_subset[OF contG]])
       (use eq in auto)
  have within_local: "continuous
      (at x within U \<inter> C j)
      (\<lambda>z. frechet_derivative
        (stokes_reflect_extension
          (\<lambda>w. rho (from_chart j w)))
        (at z) v)"
    using cont_local xU x
    by (simp add: continuous_on_eq_continuous_within)
  have filter: "at x within U \<inter> C j =
      at x within C j"
    by (rule at_within_nhd[OF xU openU])
       auto
  show "continuous (at x within C j)
      (\<lambda>z. frechet_derivative
        (stokes_reflect_extension
          (\<lambda>w. rho (from_chart j w)))
        (at z) v)"
    using within_local by (simp only: filter)
qed

lemma chartwise_C1_scalar_interior:
  assumes C1: "chartwise_C1_scalar rho"
    and j: "j \<in> I"
  shows "Ck_on 1
    (\<lambda>x. rho (from_chart j x))
    (C j \<inter> open_halfspace)"
proof -
  let ?S = "C j \<inter> open_halfspace"
  have same: "body_overlap j j = ?S"
    using halfspace_chart.inverse_image[OF chart[OF j]]
    by (auto simp: body_overlap_def
      coordinate_overlap_def)
  have openS: "open ?S"
    using body_overlap_open[OF j j]
    by (simp add: same)
  show ?thesis
  proof (rule Ck_onI[OF openS])
    fix x assume x: "x \<in> ?S"
    have ex: "\<exists>U G. Ck_on 1 G U \<and> x \<in> U \<and>
        (\<forall>y\<in>U \<inter> C j.
          G y = rho (from_chart j y))"
      using C1 j x
      by (simp add: chartwise_C1_scalar_def)
    obtain U G where G: "Ck_on 1 G U"
      and xU: "x \<in> U"
      and eq: "\<forall>y\<in>U \<inter> C j.
        G y = rho (from_chart j y)"
      using ex by blast
    let ?W = "U \<inter> ?S"
    have openW: "open ?W"
      using Ck_on_open[OF G] openS by auto
    have xW: "x \<in> ?W"
      using x xU by auto
    have GW: "Ck_at 1 G x"
      by (rule Ck_onD[OF G xU])
    show "Ck_at 1
        (\<lambda>y. rho (from_chart j y)) x"
    proof (rule Ck_at_transfer_open[OF openW xW _ GW])
      fix y assume "y \<in> ?W"
      then show "G y = rho (from_chart j y)"
        using eq by auto
    qed
  qed
qed

definition weight_near_top ::
    "('a \<Rightarrow> real) \<Rightarrow>
      ('i \<Rightarrow> real \<times> (real ^ 'n) \<Rightarrow>
        real \<times> (real ^ 'n)) \<Rightarrow>
      'i \<Rightarrow> real \<times> (real ^ 'n) \<Rightarrow>
        real \<times> (real ^ 'n)"
  where "weight_near_top rho A j x =
    rho (from_chart j x) *\<^sub>R A j x"

definition reflected_weight_near_top ::
    "('a \<Rightarrow> real) \<Rightarrow>
      ('i \<Rightarrow> real \<times> (real ^ 'n) \<Rightarrow>
        real \<times> (real ^ 'n)) \<Rightarrow>
      'i \<Rightarrow> real \<times> (real ^ 'n) \<Rightarrow>
        real \<times> (real ^ 'n)"
  where "reflected_weight_near_top rho A j x =
    stokes_reflect_extension
      (\<lambda>z. rho (from_chart j z)) x *\<^sub>R A j x"

lemma reflected_weight_near_top_eq:
  assumes C1: "chartwise_C1_scalar rho"
    and j: "j \<in> I"
    and x: "x \<in> C j"
  shows "reflected_weight_near_top rho A j x =
    weight_near_top rho A j x"
  using chartwise_C1_reflected_pointwise(2)
    [OF C1 j x]
  by (simp add: reflected_weight_near_top_def
    weight_near_top_def)

lemma reflected_weight_near_top_differentiable:
  assumes C1: "chartwise_C1_scalar rho"
    and j: "j \<in> I"
    and x: "x \<in> C j"
    and dA: "A j differentiable (at x)"
  shows "reflected_weight_near_top rho A j
      differentiable (at x)"
  unfolding reflected_weight_near_top_def
  by (intro differentiable_scaleR
    chartwise_C1_reflected_pointwise(1)
      [OF C1 j x] dA)

lemma reflected_weight_near_top_normal_continuous:
  fixes A :: "'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
  assumes C1: "chartwise_C1_scalar rho"
    and j: "j \<in> I"
    and dA: "\<And>x. x \<in> C j \<Longrightarrow>
      A j differentiable (at x)"
    and cont_AP: "continuous_on (C j)
      (case_prod (product_normal_derivative (A j)))"
  shows "continuous_on (C j)
    (case_prod (product_normal_derivative
      (reflected_weight_near_top rho A j)))"
proof -
  let ?r = "stokes_reflect_extension
    (\<lambda>z. rho (from_chart j z))"
  have dr: "?r differentiable (at x)"
    if "x \<in> C j" for x
    by (rule chartwise_C1_reflected_pointwise(1)
      [OF C1 j that])
  have cr: "continuous_on (C j) ?r"
    by (rule stokes_differentiable_continuous_on[OF dr])
  have cA: "continuous_on (C j) (A j)"
    by (rule stokes_differentiable_continuous_on[OF dA])
  have cDr: "continuous_on (C j)
      (\<lambda>x. frechet_derivative ?r (at x) (1,0))"
    by (rule chartwise_C1_reflected_derivative_continuous
      [OF C1 j])
  show ?thesis
    unfolding reflected_weight_near_top_def
    by (rule stokes_product_normal_derivative_continuous_on
      [OF dr dA cr cA cDr cont_AP])
qed

lemma reflected_weight_near_top_tangential_continuous:
  fixes A :: "'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
  assumes C1: "chartwise_C1_scalar rho"
    and j: "j \<in> I"
    and dA: "\<And>x. x \<in> C j \<Longrightarrow>
      A j differentiable (at x)"
    and cont_AQ: "continuous_on (C j)
      (case_prod (product_tangential_derivative (A j) b))"
  shows "continuous_on (C j)
    (case_prod (product_tangential_derivative
      (reflected_weight_near_top rho A j) b))"
proof -
  let ?r = "stokes_reflect_extension
    (\<lambda>z. rho (from_chart j z))"
  have dr: "?r differentiable (at x)"
    if "x \<in> C j" for x
    by (rule chartwise_C1_reflected_pointwise(1)
      [OF C1 j that])
  have cr: "continuous_on (C j) ?r"
    by (rule stokes_differentiable_continuous_on[OF dr])
  have cA: "continuous_on (C j) (A j)"
    by (rule stokes_differentiable_continuous_on[OF dA])
  have cDr: "continuous_on (C j)
      (\<lambda>x. frechet_derivative ?r (at x) (0,b))"
    by (rule chartwise_C1_reflected_derivative_continuous
      [OF C1 j])
  show ?thesis
    unfolding reflected_weight_near_top_def
    by (rule stokes_product_tangential_derivative_continuous_on
      [OF dr dA cr cA cDr cont_AQ])
qed

lemma weight_near_top_differentiable_interior:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes C1: "chartwise_C1_scalar rho"
    and j: "j \<in> I"
    and x: "x \<in> C j \<inter> open_halfspace"
    and dA: "A j differentiable (at x)"
  shows "weight_near_top rho A j
    differentiable (at x)"
proof -
  have C1coord: "Ck_on 1
      (\<lambda>z. rho (from_chart j z))
      (C j \<inter> open_halfspace)"
    by (rule chartwise_C1_scalar_interior[OF C1 j])
  have drho:
      "(\<lambda>z. rho (from_chart j z))
        differentiable (at x)"
    using Ck_onD[OF C1coord x]
    by (simp add: Ck_at.simps)
  show ?thesis
    unfolding weight_near_top_def
    by (intro differentiable_scaleR drho dA)
qed

lemma weight_near_top_support:
  "near_top_form_support (weight_near_top rho A)
    \<subseteq> near_top_form_support A \<inter>
      {p\<in>M. rho p \<noteq> 0}"
proof
  fix p
  assume "p \<in> near_top_form_support
      (weight_near_top rho A)"
  then obtain j where pM: "p \<in> M"
    and j: "j \<in> I" "p \<in> D j"
    and nonzero: "weight_near_top rho A j
      (to_chart j p) \<noteq> 0"
    by (auto simp: near_top_form_support_def)
  have chart:
      "from_chart j (to_chart j p) = p"
    by (rule halfspace_chart.to_from[OF chart[OF j(1)] j(2)])
  have "rho p \<noteq> 0"
    using nonzero
    by (simp add: weight_near_top_def chart)
  moreover have "A j (to_chart j p) \<noteq> 0"
    using nonzero
    by (auto simp: weight_near_top_def chart)
  ultimately show "p \<in> near_top_form_support A \<inter>
      {p\<in>M. rho p \<noteq> 0}"
    using pM j
    by (auto simp: near_top_form_support_def)
qed

lemma near_top_form_support_cong_on_charts:
  assumes eq: "\<And>j x. j \<in> I \<Longrightarrow>
      x \<in> C j \<Longrightarrow> A j x = B j x"
  shows "near_top_form_support A =
    near_top_form_support B"
proof -
  have chart_eq: "A j (to_chart j p) =
      B j (to_chart j p)"
    if j: "j \<in> I" and p: "p \<in> D j" for j p
  proof -
    have "to_chart j p \<in> C j"
      using halfspace_chart.chart_image[OF chart[OF j]]
        p by auto
    then show ?thesis by (rule eq[OF j])
  qed
  show ?thesis
    using chart_eq
    by (auto simp: near_top_form_support_def)
qed

lemma weight_near_top_pull_compatible:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes pull: "\<And>j k x. j \<in> I \<Longrightarrow>
      k \<in> I \<Longrightarrow> x \<in> body_overlap j k
      \<Longrightarrow> A j x = product_pull_near_top
        (coordinate_transition j k)
        (coordinate_transition k j) (A k) x"
    and j: "j \<in> I" and k: "k \<in> I"
    and x: "x \<in> body_overlap j k"
  shows "weight_near_top rho A j x =
    product_pull_near_top
      (coordinate_transition j k)
      (coordinate_transition k j)
      (weight_near_top rho A k) x"
proof -
  have pD: "from_chart j x \<in> D k"
    using x
    by (auto simp: body_overlap_def
      coordinate_overlap_def)
  have from_eq:
      "from_chart k (coordinate_transition j k x) =
        from_chart j x"
    unfolding coordinate_transition_def
    by (rule halfspace_chart.to_from
      [OF chart[OF k] pD])
  have family_eq: "weight_near_top rho A k =
      (\<lambda>z. (rho \<circ> from_chart k) z *\<^sub>R A k z)"
    by (rule ext) (simp add: weight_near_top_def)
  have weighted:
      "product_pull_near_top
        (coordinate_transition j k)
        (coordinate_transition k j)
        (weight_near_top rho A k) x =
      rho (from_chart j x) *\<^sub>R
        product_pull_near_top
          (coordinate_transition j k)
          (coordinate_transition k j) (A k) x"
    by (simp add: family_eq
      product_pull_near_top_weight from_eq)
  show ?thesis
    by (simp add: weight_near_top_def
      pull[OF j k x] weighted)
qed

lemma near_top_partition_sum:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes finite: "finite F"
    and support: "near_top_form_support A \<subseteq> K"
    and unity: "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i p) = 1"
    and j: "j \<in> I" and x: "x \<in> C j"
  shows "A j x =
    (\<Sum>i\<in>F. weight_near_top (phi i) A j x)"
proof -
  let ?p = "from_chart j x"
  have pD: "?p \<in> D j"
    using halfspace_chart.inverse_image[OF chart[OF j]] x
    by auto
  have pM: "?p \<in> M"
    using domain_subset_carrier[OF j] pD by auto
  have to_from: "to_chart j ?p = x"
    by (rule halfspace_chart.from_to[OF chart[OF j] x])
  show ?thesis
  proof (cases "A j x = 0")
    case True
    then show ?thesis
      by (simp add: weight_near_top_def)
  next
    case False
    have witness: "\<exists>i\<in>I.
        ?p \<in> D i \<and> A i (to_chart i ?p) \<noteq> 0"
    proof (rule bexI[where x=j])
      show "?p \<in> D j \<and>
          A j (to_chart j ?p) \<noteq> 0"
        using pD False to_from by simp
      show "j \<in> I" by (rule j)
    qed
    have p_support: "?p \<in> near_top_form_support A"
      unfolding near_top_form_support_def
      using pM witness by simp
    have pK: "?p \<in> K"
      using support p_support by auto
    have "(\<Sum>i\<in>F. weight_near_top
        (phi i) A j x) =
      (\<Sum>i\<in>F. phi i ?p) *\<^sub>R A j x"
      by (simp add: weight_near_top_def
        scaleR_left.sum)
    also have "\<dots> = A j x"
      by (simp add: unity[OF pK])
    finally show ?thesis by simp
  qed
qed

lemma exterior_top_partition_sum_interior:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes finite: "finite F"
    and support: "near_top_form_support A \<subseteq> K"
    and unity: "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i p) = 1"
    and C1: "\<And>i. i \<in> F \<Longrightarrow>
      chartwise_C1_scalar (phi i)"
    and j: "j \<in> I"
    and x: "x \<in> C j \<inter> open_halfspace"
    and dA: "\<And>z. z \<in> C j \<inter> open_halfspace
      \<Longrightarrow> A j differentiable (at z)"
  shows "product_exterior_top (A j) x =
    (\<Sum>i\<in>F. product_exterior_top
      (weight_near_top (phi i) A j) x)"
proof -
  let ?S = "C j \<inter> open_halfspace"
  let ?B = "\<lambda>i. weight_near_top (phi i) A j"
  have same: "body_overlap j j = ?S"
    using halfspace_chart.inverse_image[OF chart[OF j]]
    by (auto simp: body_overlap_def
      coordinate_overlap_def)
  have openS: "open ?S"
    using body_overlap_open[OF j j]
    by (simp add: same)
  have eq: "A j z = (\<Sum>i\<in>F. ?B i z)"
    if "z \<in> ?S" for z
    by (rule near_top_partition_sum
      [OF finite support unity j]) (use that in auto)
  have derivative_eq:
      "frechet_derivative (A j) (at x) =
      frechet_derivative
        (\<lambda>z. \<Sum>i\<in>F. ?B i z) (at x)"
    by (rule frechet_derivative_transform_within_open
      [OF openS x eq])
  have dB: "?B i differentiable (at x)"
    if ii: "i \<in> F" for i
    using weight_near_top_differentiable_interior
      [where rho="phi i" and A=A and j=j and x=x,
        OF C1[OF ii] j x dA[OF x]]
    by simp
  show ?thesis
    using product_exterior_top_sum[OF finite dB]
    by (simp add: product_exterior_top_def
      derivative_eq)
qed

lemma boundary_coeff_weight_near_top:
  "product_boundary_coeff
      (weight_near_top rho A j) y =
    rho (from_chart j (0,y)) *
      product_boundary_coeff (A j) y"
  by (simp add: product_boundary_coeff_def
    product_normal_coeff_def weight_near_top_def)

lemma boundary_coeff_partition_sum:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes finite: "finite F"
    and support: "near_top_form_support A \<subseteq> K"
    and unity: "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i p) = 1"
    and j: "j \<in> I"
    and y: "y \<in> halfspace_face (C j)"
  shows "product_boundary_coeff (A j) y =
    (\<Sum>i\<in>F.
      product_boundary_coeff
        (weight_near_top (phi i) A j) y)"
proof -
  have xC: "(0,y) \<in> C j"
    using y by (simp add: halfspace_face_def)
  have form: "A j (0,y) =
    (\<Sum>i\<in>F.
      weight_near_top (phi i) A j (0,y))"
    by (rule near_top_partition_sum
      [OF finite support unity j xC])
  have fst_sum: "fst (\<Sum>i\<in>F.
      weight_near_top (phi i) A j (0,y)) =
    (\<Sum>i\<in>F. fst
      (weight_near_top (phi i) A j (0,y)))"
    using finite
    by (induction F rule: finite_induct) auto
  show ?thesis
    using form fst_sum
    by (simp add: product_boundary_coeff_def
      product_normal_coeff_def
      sum_negf)
qed

lemma weight_near_top_compact_chart_support:
  assumes compact: "compact K"
    and support: "near_top_form_support A \<subseteq> K"
    and closed: "closed L"
    and local: "L \<subseteq> D i"
    and rho: "{p\<in>M. rho p \<noteq> 0} \<subseteq> L"
  shows "compact (K \<inter> L)"
    and "K \<inter> L \<subseteq> D i"
    and "near_top_form_support
      (weight_near_top rho A) \<subseteq> K \<inter> L"
proof -
  show "compact (K \<inter> L)"
    using closed_Int_compact[OF closed compact]
    by (simp add: Int_commute)
  show "K \<inter> L \<subseteq> D i"
    using local by auto
  show "near_top_form_support
      (weight_near_top rho A) \<subseteq> K \<inter> L"
    using weight_near_top_support[of rho A]
      support rho by auto
qed

lemma body_top_coeff_sum_properties:
  assumes finite: "finite F"
    and compatible: "\<And>k. k \<in> F \<Longrightarrow>
      body_top_coeff_compatible (alpha k)"
    and support: "\<And>k. k \<in> F \<Longrightarrow>
      body_form_support (alpha k) \<subseteq> K"
    and cont: "\<And>k j. k \<in> F \<Longrightarrow>
      j \<in> I \<Longrightarrow>
      continuous_on (C j) (alpha k j)"
  shows "body_top_coeff_compatible
      (\<lambda>j x. \<Sum>k\<in>F. alpha k j x)"
    and "body_form_support
      (\<lambda>j x. \<Sum>k\<in>F. alpha k j x)
      \<subseteq> K"
    and "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (C j)
        (\<lambda>x. \<Sum>k\<in>F. alpha k j x)"
proof -
  show "body_top_coeff_compatible
      (\<lambda>j x. \<Sum>k\<in>F. alpha k j x)"
  proof (unfold body_top_coeff_compatible_def,
      intro ballI)
    fix j l x
    assume j: "j \<in> I" and l: "l \<in> I"
      and x: "x \<in> body_overlap j l"
    have eq: "alpha k j x =
        eucl.det (frechet_derivative
          (coordinate_transition j l) (at x)) *
        alpha k l (coordinate_transition j l x)"
      if k: "k \<in> F" for k
      using compatible[OF k] j l x
      by (auto simp: body_top_coeff_compatible_def)
    show "(\<Sum>k\<in>F. alpha k j x) =
      eucl.det (frechet_derivative
        (coordinate_transition j l) (at x)) *
      (\<Sum>k\<in>F.
        alpha k l (coordinate_transition j l x))"
      by (simp add: eq sum_distrib_left)
  qed
  show "body_form_support
      (\<lambda>j x. \<Sum>k\<in>F. alpha k j x)
      \<subseteq> K"
  proof
    fix p
    assume p: "p \<in> body_form_support
      (\<lambda>j x. \<Sum>k\<in>F. alpha k j x)"
    then obtain j where pI: "p \<in> interior_carrier"
      and j: "j \<in> I" "p \<in> D j"
      and nonzero: "(\<Sum>k\<in>F.
        alpha k j (to_chart j p)) \<noteq> 0"
      by (auto simp: body_form_support_def)
    show "p \<in> K"
    proof (rule ccontr)
      assume "p \<notin> K"
      then have "alpha k j (to_chart j p) = 0"
        if k: "k \<in> F" for k
        using support[OF k] pI j
        by (auto simp: body_form_support_def)
      then have "(\<Sum>k\<in>F.
          alpha k j (to_chart j p)) = 0"
        by simp
      with nonzero show False by simp
    qed
  qed
  show "continuous_on (C j)
      (\<lambda>x. \<Sum>k\<in>F. alpha k j x)"
    if j: "j \<in> I" for j
    by (intro continuous_intros cont[OF _ j])
qed

theorem integral_body_top_sum:
  assumes finite: "finite F"
    and compact: "compact K"
    and KM: "K \<subseteq> M"
    and compatible: "\<And>k. k \<in> F \<Longrightarrow>
      body_top_coeff_compatible (alpha k)"
    and support: "\<And>k. k \<in> F \<Longrightarrow>
      body_form_support (alpha k) \<subseteq> K"
    and cont: "\<And>k j. k \<in> F \<Longrightarrow>
      j \<in> I \<Longrightarrow>
      continuous_on (C j) (alpha k j)"
  shows "integral_body_top
      (\<lambda>j x. \<Sum>k\<in>F. alpha k j x) =
    (\<Sum>k\<in>F. integral_body_top (alpha k))"
  using finite compatible support cont
proof (induction F rule: finite_induct)
  case empty
  then show ?case
    by (simp add: integral_body_top_zero_coeff)
next
  case (insert a F)
  have compat_tail: "body_top_coeff_compatible
      (\<lambda>j x. \<Sum>k\<in>F. alpha k j x)"
    by (rule body_top_coeff_sum_properties(1)
      [OF insert.hyps(1)])
       (use insert.prems in auto)
  have support_tail: "body_form_support
      (\<lambda>j x. \<Sum>k\<in>F. alpha k j x)
      \<subseteq> K"
    by (rule body_top_coeff_sum_properties(2)
      [OF insert.hyps(1)])
       (use insert.prems in auto)
  have cont_tail: "continuous_on (C j)
      (\<lambda>x. \<Sum>k\<in>F. alpha k j x)"
    if j: "j \<in> I" for j
    by (rule body_top_coeff_sum_properties(3)
      [OF insert.hyps(1) _ _ _ j])
       (use insert.prems in auto)
  have add: "integral_body_top
      (\<lambda>j x. alpha a j x +
        (\<Sum>k\<in>F. alpha k j x)) =
    integral_body_top (alpha a) +
      integral_body_top
        (\<lambda>j x. \<Sum>k\<in>F. alpha k j x)"
    by (rule integral_body_top_add
      [OF _ compat_tail compact compact KM KM
        _ support_tail _ cont_tail])
       (use insert.prems in auto)
  have tail: "integral_body_top
      (\<lambda>j x. \<Sum>k\<in>F. alpha k j x) =
    (\<Sum>k\<in>F. integral_body_top (alpha k))"
    by (rule insert.IH)
       (use insert.prems in auto)
  show ?case
    using add tail insert.hyps by simp
qed

lemma boundary_top_coeff_sum_properties:
  assumes finite: "finite F"
    and compatible: "\<And>k. k \<in> F \<Longrightarrow>
      boundary_top_coeff_compatible (alpha k)"
    and support: "\<And>k. k \<in> F \<Longrightarrow>
      boundary_form_support (alpha k) \<subseteq> K"
    and cont: "\<And>k j. k \<in> F \<Longrightarrow>
      j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (alpha k j)"
  shows "boundary_top_coeff_compatible
      (\<lambda>j y. \<Sum>k\<in>F. alpha k j y)"
    and "boundary_form_support
      (\<lambda>j y. \<Sum>k\<in>F. alpha k j y)
      \<subseteq> K"
    and "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j))
        (\<lambda>y. \<Sum>k\<in>F. alpha k j y)"
proof -
  show "boundary_top_coeff_compatible
      (\<lambda>j y. \<Sum>k\<in>F. alpha k j y)"
  proof (unfold boundary_top_coeff_compatible_def,
      intro ballI)
    fix j l y
    assume j: "j \<in> I" and l: "l \<in> I"
      and y: "y \<in> boundary_overlap j l"
    have eq: "alpha k j y =
        pull_top (boundary_transition j l)
          (alpha k l) y"
      if k: "k \<in> F" for k
      using compatible[OF k] j l y
      by (auto simp: boundary_top_coeff_compatible_def)
    show "(\<Sum>k\<in>F. alpha k j y) =
      pull_top (boundary_transition j l)
        (\<lambda>z. \<Sum>k\<in>F. alpha k l z) y"
      by (simp add: eq pull_top_def
        sum_distrib_left)
  qed
  show "boundary_form_support
      (\<lambda>j y. \<Sum>k\<in>F. alpha k j y)
      \<subseteq> K"
  proof
    fix p
    assume p: "p \<in> boundary_form_support
      (\<lambda>j y. \<Sum>k\<in>F. alpha k j y)"
    then obtain j where pB: "p \<in> boundary_carrier"
      and j: "j \<in> I" "p \<in> D j"
      and nonzero: "(\<Sum>k\<in>F.
        alpha k j (snd (to_chart j p))) \<noteq> 0"
      by (auto simp: boundary_form_support_def)
    show "p \<in> K"
    proof (rule ccontr)
      assume "p \<notin> K"
      then have "alpha k j
          (snd (to_chart j p)) = 0"
        if k: "k \<in> F" for k
        using support[OF k] pB j
        by (auto simp: boundary_form_support_def)
      then have "(\<Sum>k\<in>F.
          alpha k j (snd (to_chart j p))) = 0"
        by simp
      with nonzero show False by simp
    qed
  qed
  show "continuous_on (halfspace_face (C j))
      (\<lambda>y. \<Sum>k\<in>F. alpha k j y)"
    if j: "j \<in> I" for j
    by (intro continuous_intros cont[OF _ j])
qed

theorem integral_boundary_top_sum:
  assumes finite: "finite F"
    and compact: "compact K"
    and KB: "K \<subseteq> boundary_carrier"
    and compatible: "\<And>k. k \<in> F \<Longrightarrow>
      boundary_top_coeff_compatible (alpha k)"
    and support: "\<And>k. k \<in> F \<Longrightarrow>
      boundary_form_support (alpha k) \<subseteq> K"
    and cont: "\<And>k j. k \<in> F \<Longrightarrow>
      j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (alpha k j)"
  shows "integral_boundary_top
      (\<lambda>j y. \<Sum>k\<in>F. alpha k j y) =
    (\<Sum>k\<in>F. integral_boundary_top (alpha k))"
  using finite compatible support cont
proof (induction F rule: finite_induct)
  case empty
  then show ?case
    by (simp add: integral_boundary_top_zero_coeff)
next
  case (insert a F)
  have compat_tail: "boundary_top_coeff_compatible
      (\<lambda>j y. \<Sum>k\<in>F. alpha k j y)"
    by (rule boundary_top_coeff_sum_properties(1)
      [OF insert.hyps(1)])
       (use insert.prems in auto)
  have support_tail: "boundary_form_support
      (\<lambda>j y. \<Sum>k\<in>F. alpha k j y)
      \<subseteq> K"
    by (rule boundary_top_coeff_sum_properties(2)
      [OF insert.hyps(1)])
       (use insert.prems in auto)
  have cont_tail: "continuous_on
      (halfspace_face (C j))
      (\<lambda>y. \<Sum>k\<in>F. alpha k j y)"
    if j: "j \<in> I" for j
    by (rule boundary_top_coeff_sum_properties(3)
      [OF insert.hyps(1) _ _ _ j])
       (use insert.prems in auto)
  have add: "integral_boundary_top
      (\<lambda>j y. alpha a j y +
        (\<Sum>k\<in>F. alpha k j y)) =
    integral_boundary_top (alpha a) +
      integral_boundary_top
        (\<lambda>j y. \<Sum>k\<in>F. alpha k j y)"
    by (rule integral_boundary_top_add
      [OF _ compat_tail compact compact KB KB
        _ support_tail _ cont_tail])
       (use insert.prems in auto)
  have tail: "integral_boundary_top
      (\<lambda>j y. \<Sum>k\<in>F. alpha k j y) =
    (\<Sum>k\<in>F. integral_boundary_top (alpha k))"
    by (rule insert.IH)
       (use insert.prems in auto)
  show ?case
    using add tail insert.hyps by simp
qed

lemma integral_body_top_cong_interior:
  assumes compact: "compact K"
    and KM: "K \<subseteq> M"
    and support_a: "body_form_support alpha \<subseteq> K"
    and support_b: "body_form_support beta \<subseteq> K"
    and compat_a: "body_top_coeff_compatible alpha"
    and compat_b: "body_top_coeff_compatible beta"
    and cont_a: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (C j) (alpha j)"
    and cont_b: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (C j) (beta j)"
    and eq: "\<And>j x. j \<in> I \<Longrightarrow>
      x \<in> C j \<inter> open_halfspace \<Longrightarrow>
      alpha j x = beta j x"
  shows "integral_body_top alpha =
    integral_body_top beta"
proof -
  have ex: "\<exists>phi F.
      admissible_body_partition alpha phi F \<and>
      (\<forall>p\<in>K.
        (\<Sum>i\<in>F. phi i p) = 1)"
    by (rule body_partition_exists
      [OF compact KM support_a])
  obtain phi F where part_a:
      "admissible_body_partition alpha phi F"
    and unity: "\<forall>p\<in>K.
      (\<Sum>i\<in>F. phi i p) = 1"
    using ex by blast
  have part_b: "admissible_body_partition beta phi F"
    using part_a unity support_b
    by (auto simp: admissible_body_partition_def)
  have int_a: "integral_body_top alpha =
    body_chart_partition_integral alpha phi F"
    by (rule integral_body_top_eq_partition
      [OF compat_a compact support_a cont_a part_a])
  have int_b: "integral_body_top beta =
    body_chart_partition_integral beta phi F"
    by (rule integral_body_top_eq_partition
      [OF compat_b compact support_b cont_b part_b])
  have local_eq: "integral (C i)
      (weight_body_coeff (phi i) alpha i) =
    integral (C i)
      (weight_body_coeff (phi i) beta i)"
    if ii: "i \<in> F" for i
  proof -
    have i: "i \<in> I"
      using part_a ii
      by (auto simp: admissible_body_partition_def)
    have left: "integral (C i)
        (weight_body_coeff (phi i) alpha i) =
      integral (C i \<inter> open_halfspace)
        (weight_body_coeff (phi i) alpha i)"
      by (rule body_chart_integral_eq_interior[OF i])
    have right: "integral (C i)
        (weight_body_coeff (phi i) beta i) =
      integral (C i \<inter> open_halfspace)
        (weight_body_coeff (phi i) beta i)"
      by (rule body_chart_integral_eq_interior[OF i])
    show ?thesis
      unfolding left right
      by (rule integral_cong)
         (use eq[OF i] in
           \<open>auto simp: weight_body_coeff_def\<close>)
  qed
  have "body_chart_partition_integral alpha phi F =
    body_chart_partition_integral beta phi F"
    unfolding body_chart_partition_integral_def
    by (rule sum.cong[OF refl]) (use local_eq in auto)
  with int_a int_b show ?thesis by simp
qed

lemma integral_boundary_top_cong_face:
  assumes compact: "compact K"
    and KB: "K \<subseteq> boundary_carrier"
    and support_a: "boundary_form_support alpha \<subseteq> K"
    and support_b: "boundary_form_support beta \<subseteq> K"
    and compat_a: "boundary_top_coeff_compatible alpha"
    and compat_b: "boundary_top_coeff_compatible beta"
    and cont_a: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (alpha j)"
    and cont_b: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (beta j)"
    and eq: "\<And>j y. j \<in> I \<Longrightarrow>
      y \<in> halfspace_face (C j) \<Longrightarrow>
      alpha j y = beta j y"
  shows "integral_boundary_top alpha =
    integral_boundary_top beta"
proof -
  have ex: "\<exists>phi F.
      admissible_boundary_partition alpha phi F \<and>
      (\<forall>p\<in>K.
        (\<Sum>i\<in>F. phi i p) = 1)"
    by (rule boundary_partition_exists
      [OF compact KB support_a])
  obtain phi F where part_a:
      "admissible_boundary_partition alpha phi F"
    and unity: "\<forall>p\<in>K.
      (\<Sum>i\<in>F. phi i p) = 1"
    using ex by blast
  have part_b: "admissible_boundary_partition beta phi F"
    using part_a unity support_b
    by (auto simp: admissible_boundary_partition_def)
  have int_a: "integral_boundary_top alpha =
    boundary_chart_partition_integral alpha phi F"
    by (rule integral_boundary_top_eq_partition
      [OF compat_a compact support_a cont_a part_a])
  have int_b: "integral_boundary_top beta =
    boundary_chart_partition_integral beta phi F"
    by (rule integral_boundary_top_eq_partition
      [OF compat_b compact support_b cont_b part_b])
  have local_eq: "integral (halfspace_face (C i))
      (weight_boundary_coeff (phi i) alpha i) =
    integral (halfspace_face (C i))
      (weight_boundary_coeff (phi i) beta i)"
    if ii: "i \<in> F" for i
  proof -
    have i: "i \<in> I"
      using part_a ii
      by (auto simp: admissible_boundary_partition_def)
    show ?thesis
      by (rule integral_cong)
         (use eq[OF i] in
           \<open>auto simp: weight_boundary_coeff_def\<close>)
  qed
  have "boundary_chart_partition_integral alpha phi F =
    boundary_chart_partition_integral beta phi F"
    unfolding boundary_chart_partition_integral_def
    by (rule sum.cong[OF refl]) (use local_eq in auto)
  with int_a int_b show ?thesis by simp
qed

lemma near_top_partition_sum_extensions:
  fixes A :: "'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
    and B :: "'i \<Rightarrow> 'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
  assumes finite: "finite F"
    and support: "near_top_form_support A \<subseteq> K"
    and unity: "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i p) = 1"
    and eqB: "\<And>i j x. i \<in> F \<Longrightarrow>
      j \<in> I \<Longrightarrow> x \<in> C j \<Longrightarrow>
      B i j x = weight_near_top (phi i) A j x"
    and j: "j \<in> I" and x: "x \<in> C j"
  shows "A j x = (\<Sum>i\<in>F. B i j x)"
proof -
  have raw: "A j x =
    (\<Sum>i\<in>F.
      weight_near_top (phi i) A j x)"
    by (rule near_top_partition_sum
      [OF finite support unity j x])
  show ?thesis
    unfolding raw
    by (rule sum.cong[OF refl])
       (use eqB[OF _ j x] in auto)
qed

lemma exterior_top_partition_sum_extensions:
  fixes A :: "'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
    and B :: "'i \<Rightarrow> 'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
  assumes finite: "finite F"
    and support: "near_top_form_support A \<subseteq> K"
    and unity: "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i p) = 1"
    and eqB: "\<And>i j x. i \<in> F \<Longrightarrow>
      j \<in> I \<Longrightarrow> x \<in> C j \<Longrightarrow>
      B i j x = weight_near_top (phi i) A j x"
    and dB: "\<And>i j x. i \<in> F \<Longrightarrow>
      j \<in> I \<Longrightarrow>
      x \<in> C j \<inter> open_halfspace \<Longrightarrow>
      B i j differentiable (at x)"
    and j: "j \<in> I"
    and x: "x \<in> C j \<inter> open_halfspace"
  shows "product_exterior_top (A j) x =
    (\<Sum>i\<in>F.
      product_exterior_top (B i j) x)"
proof -
  let ?S = "C j \<inter> open_halfspace"
  have same: "body_overlap j j = ?S"
    using halfspace_chart.inverse_image[OF chart[OF j]]
    by (auto simp: body_overlap_def
      coordinate_overlap_def)
  have openS: "open ?S"
    using body_overlap_open[OF j j]
    by (simp add: same)
  have eq: "A j z = (\<Sum>i\<in>F. B i j z)"
    if "z \<in> ?S" for z
    by (rule near_top_partition_sum_extensions
      [OF finite support unity eqB j])
       (use that in auto)
  have derivative_eq:
      "frechet_derivative (A j) (at x) =
      frechet_derivative
        (\<lambda>z. \<Sum>i\<in>F. B i j z) (at x)"
    by (rule frechet_derivative_transform_within_open
      [OF openS x eq])
  have dBi: "B i j differentiable (at x)"
    if "i \<in> F" for i
    by (rule dB[OF that j x])
  show ?thesis
    using product_exterior_top_sum
      [where A="\<lambda>i. B i j" and I=F and p=x,
        OF finite dBi]
    by (simp add: product_exterior_top_def
      derivative_eq)
qed

lemma boundary_coeff_partition_sum_extensions:
  fixes A :: "'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
    and B :: "'i \<Rightarrow> 'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
  assumes finite: "finite F"
    and support: "near_top_form_support A \<subseteq> K"
    and unity: "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i p) = 1"
    and eqB: "\<And>i j x. i \<in> F \<Longrightarrow>
      j \<in> I \<Longrightarrow> x \<in> C j \<Longrightarrow>
      B i j x = weight_near_top (phi i) A j x"
    and j: "j \<in> I"
    and y: "y \<in> halfspace_face (C j)"
  shows "product_boundary_coeff (A j) y =
    (\<Sum>i\<in>F.
      product_boundary_coeff (B i j) y)"
proof -
  have xC: "(0,y) \<in> C j"
    using y by (simp add: halfspace_face_def)
  have form: "A j (0,y) =
    (\<Sum>i\<in>F. B i j (0,y))"
    by (rule near_top_partition_sum_extensions
      [OF finite support unity eqB j xC])
  have fst_sum: "fst (\<Sum>i\<in>F. B i j (0,y)) =
    (\<Sum>i\<in>F. fst (B i j (0,y)))"
    using finite
    by (induction F rule: finite_induct) auto
  show ?thesis
    using form fst_sum
    by (simp add: product_boundary_coeff_def
      product_normal_coeff_def sum_negf)
qed

lemma extended_weight_pull_compatible:
  fixes A :: "'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
    and B :: "'i \<Rightarrow> 'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
  assumes pull: "\<And>j k x. j \<in> I \<Longrightarrow>
      k \<in> I \<Longrightarrow> x \<in> body_overlap j k
      \<Longrightarrow> A j x = product_pull_near_top
        (coordinate_transition j k)
        (coordinate_transition k j) (A k) x"
    and eqB: "\<And>i j x. i \<in> F \<Longrightarrow>
      j \<in> I \<Longrightarrow> x \<in> C j \<Longrightarrow>
      B i j x = weight_near_top (phi i) A j x"
    and i: "i \<in> F"
    and j: "j \<in> I" and k: "k \<in> I"
    and x: "x \<in> body_overlap j k"
  shows "B i j x =
    product_pull_near_top
      (coordinate_transition j k)
      (coordinate_transition k j) (B i k) x"
proof -
  let ?f = "coordinate_transition j k"
  let ?g = "coordinate_transition k j"
  have xC: "x \<in> C j"
    using x by (auto simp: body_overlap_def
      coordinate_overlap_def)
  have fxC: "?f x \<in> C k"
    using coordinate_transition_body_overlap[OF j k x]
    by (auto simp: body_overlap_def
      coordinate_overlap_def)
  have pull_raw:
      "weight_near_top (phi i) A j x =
      product_pull_near_top ?f ?g
        (weight_near_top (phi i) A k) x"
    by (rule weight_near_top_pull_compatible
      [OF pull j k x])
  have pull_eq:
      "product_pull_near_top ?f ?g
        (weight_near_top (phi i) A k) x =
      product_pull_near_top ?f ?g (B i k) x"
    by (rule product_pull_near_top_cong_at)
       (use eqB[OF i k fxC] in auto)
  show ?thesis
    using eqB[OF i j xC] pull_raw pull_eq
    by simp
qed

lemma extended_weight_compact_chart_support:
  assumes compact: "compact K"
    and support: "near_top_form_support A \<subseteq> K"
    and eqB: "\<And>j x. j \<in> I \<Longrightarrow>
      x \<in> C j \<Longrightarrow>
      B j x = weight_near_top rho A j x"
    and closed: "closed L"
    and local: "L \<subseteq> D i"
    and rho: "{p\<in>M. rho p \<noteq> 0} \<subseteq> L"
  shows "compact (K \<inter> L)"
    and "K \<inter> L \<subseteq> D i"
    and "near_top_form_support B \<subseteq> K \<inter> L"
proof -
  have same: "near_top_form_support B =
      near_top_form_support
        (weight_near_top rho A)"
    by (rule near_top_form_support_cong_on_charts
      [OF eqB])
  show "compact (K \<inter> L)"
    by (rule weight_near_top_compact_chart_support(1)
      [OF compact support closed local rho])
  show "K \<inter> L \<subseteq> D i"
    by (rule weight_near_top_compact_chart_support(2)
      [OF compact support closed local rho])
  show "near_top_form_support B \<subseteq> K \<inter> L"
    unfolding same
    by (rule weight_near_top_compact_chart_support(3)
      [OF compact support closed local rho])
qed

lemma extended_weight_chart_stokes:
  fixes A :: "'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
    and B :: "'i \<Rightarrow> 'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
  assumes compact: "compact K"
    and support: "near_top_form_support A \<subseteq> K"
    and pull: "\<And>j k x. j \<in> I \<Longrightarrow>
      k \<in> I \<Longrightarrow> x \<in> body_overlap j k
      \<Longrightarrow> A j x = product_pull_near_top
        (coordinate_transition j k)
        (coordinate_transition k j) (A k) x"
    and eqB: "\<And>h j x. h \<in> F \<Longrightarrow>
      j \<in> I \<Longrightarrow> x \<in> C j \<Longrightarrow>
      B h j x = weight_near_top (phi h) A j x"
    and i: "i \<in> F" "i \<in> I"
    and closed: "closed L"
    and local: "L \<subseteq> D i"
    and phi_support:
      "{p\<in>M. phi i p \<noteq> 0} \<subseteq> L"
    and dB: "\<And>j x. j \<in> I \<Longrightarrow>
      x \<in> C j \<Longrightarrow>
      B i j differentiable (at x)"
    and cont_P: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (C j)
        (case_prod (product_normal_derivative (B i j)))"
    and cont_Q: "\<And>j b. j \<in> I \<Longrightarrow>
      b \<in> Basis \<Longrightarrow>
      continuous_on (C j)
        (case_prod
          (product_tangential_derivative (B i j) b))"
  shows "integral_body_top
      (\<lambda>j x. product_exterior_top (B i j) x) =
    integral_boundary_top
      (\<lambda>j y. product_boundary_coeff (B i j) y)"
proof -
  let ?Ki = "K \<inter> L"
  have compact_i: "compact ?Ki"
    by (rule extended_weight_compact_chart_support(1)
      [OF compact support eqB[OF i(1)]
        closed local phi_support])
  have Ki_chart: "?Ki \<subseteq> D i"
    using local by auto
  have support_i: "near_top_form_support (B i)
      \<subseteq> ?Ki"
    by (rule extended_weight_compact_chart_support(3)
      [OF compact support eqB[OF i(1)]
        closed local phi_support])
  have pull_i: "B i j x =
    product_pull_near_top
      (coordinate_transition j k)
      (coordinate_transition k j) (B i k) x"
    if j: "j \<in> I" and k: "k \<in> I"
      and x: "x \<in> body_overlap j k"
    for j k x
    by (rule extended_weight_pull_compatible
      [OF pull eqB i(1) j k x])
  show ?thesis
    by (rule Stokes_chart_supported_form_integrals_C1
      [OF i(2) compact_i Ki_chart support_i
        dB pull_i cont_P cont_Q])
qed

theorem finite_stokes_gluing:
  assumes finite: "finite F"
    and compact_M: "compact K_M"
    and KM: "K_M \<subseteq> M"
    and compact_B: "compact K_B"
    and KB: "K_B \<subseteq> boundary_carrier"
    and compat_M: "body_top_coeff_compatible alpha"
    and support_M: "body_form_support alpha \<subseteq> K_M"
    and cont_M: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (C j) (alpha j)"
    and compat_B: "boundary_top_coeff_compatible beta"
    and support_B: "boundary_form_support beta \<subseteq> K_B"
    and cont_B: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (beta j)"
    and compat_Mi: "\<And>i. i \<in> F \<Longrightarrow>
      body_top_coeff_compatible (alpha_i i)"
    and support_Mi: "\<And>i. i \<in> F \<Longrightarrow>
      body_form_support (alpha_i i) \<subseteq> K_M"
    and cont_Mi: "\<And>i j. i \<in> F \<Longrightarrow>
      j \<in> I \<Longrightarrow>
      continuous_on (C j) (alpha_i i j)"
    and compat_Bi: "\<And>i. i \<in> F \<Longrightarrow>
      boundary_top_coeff_compatible (beta_i i)"
    and support_Bi: "\<And>i. i \<in> F \<Longrightarrow>
      boundary_form_support (beta_i i) \<subseteq> K_B"
    and cont_Bi: "\<And>i j. i \<in> F \<Longrightarrow>
      j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j))
        (beta_i i j)"
    and sum_M: "\<And>j x. j \<in> I \<Longrightarrow>
      x \<in> C j \<inter> open_halfspace \<Longrightarrow>
      alpha j x =
        (\<Sum>i\<in>F. alpha_i i j x)"
    and sum_B: "\<And>j y. j \<in> I \<Longrightarrow>
      y \<in> halfspace_face (C j) \<Longrightarrow>
      beta j y =
        (\<Sum>i\<in>F. beta_i i j y)"
    and local_stokes: "\<And>i. i \<in> F \<Longrightarrow>
      integral_body_top (alpha_i i) =
        integral_boundary_top (beta_i i)"
  shows "integral_body_top alpha =
    integral_boundary_top beta"
proof -
  let ?sum_M = "\<lambda>j x.
    \<Sum>i\<in>F. alpha_i i j x"
  let ?sum_B = "\<lambda>j y.
    \<Sum>i\<in>F. beta_i i j y"
  have compat_sum_M: "body_top_coeff_compatible ?sum_M"
    by (rule body_top_coeff_sum_properties(1)
      [OF finite compat_Mi support_Mi cont_Mi])
  have support_sum_M: "body_form_support ?sum_M
      \<subseteq> K_M"
    by (rule body_top_coeff_sum_properties(2)
      [OF finite compat_Mi support_Mi cont_Mi])
  have cont_sum_M: "continuous_on (C j) (?sum_M j)"
    if j: "j \<in> I" for j
    by (rule body_top_coeff_sum_properties(3)
      [OF finite compat_Mi support_Mi cont_Mi j])
  have compat_sum_B: "boundary_top_coeff_compatible ?sum_B"
    by (rule boundary_top_coeff_sum_properties(1)
      [OF finite compat_Bi support_Bi cont_Bi])
  have support_sum_B: "boundary_form_support ?sum_B
      \<subseteq> K_B"
    by (rule boundary_top_coeff_sum_properties(2)
      [OF finite compat_Bi support_Bi cont_Bi])
  have cont_sum_B:
      "continuous_on (halfspace_face (C j)) (?sum_B j)"
    if j: "j \<in> I" for j
    by (rule boundary_top_coeff_sum_properties(3)
      [OF finite compat_Bi support_Bi cont_Bi j])
  have eq_M: "integral_body_top alpha =
      integral_body_top ?sum_M"
    by (rule integral_body_top_cong_interior
      [OF compact_M KM support_M support_sum_M
        compat_M compat_sum_M cont_M cont_sum_M sum_M])
  have eq_B: "integral_boundary_top beta =
      integral_boundary_top ?sum_B"
    by (rule integral_boundary_top_cong_face
      [OF compact_B KB support_B support_sum_B
        compat_B compat_sum_B cont_B cont_sum_B sum_B])
  have split_M: "integral_body_top ?sum_M =
      (\<Sum>i\<in>F. integral_body_top (alpha_i i))"
    by (rule integral_body_top_sum
      [OF finite compact_M KM compat_Mi
        support_Mi cont_Mi])
  have split_B: "integral_boundary_top ?sum_B =
      (\<Sum>i\<in>F. integral_boundary_top (beta_i i))"
    by (rule integral_boundary_top_sum
      [OF finite compact_B KB compat_Bi
        support_Bi cont_Bi])
  have sums: "(\<Sum>i\<in>F. integral_body_top (alpha_i i)) =
      (\<Sum>i\<in>F. integral_boundary_top (beta_i i))"
    by (rule sum.cong[OF refl])
       (use local_stokes in auto)
  show ?thesis
    using eq_M eq_B split_M split_B sums by simp
qed

theorem global_stokes_with_weight_extensions:
  fixes A :: "'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
    and B :: "'i \<Rightarrow> 'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
  assumes compact: "compact K"
    and KM: "K \<subseteq> M"
    and support: "near_top_form_support A \<subseteq> K"
    and finite: "finite F"
    and FI: "F \<subseteq> I"
    and unity: "\<And>p. p \<in> K \<Longrightarrow>
      (\<Sum>i\<in>F. phi i p) = 1"
    and local: "\<And>i. i \<in> F \<Longrightarrow>
      \<exists>L. closed L \<and>
        {p\<in>M. phi i p \<noteq> 0} \<subseteq> L \<and>
        L \<subseteq> D i"
    and dA: "\<And>j x. j \<in> I \<Longrightarrow>
      x \<in> C j \<Longrightarrow>
      A j differentiable (at x)"
    and pull: "\<And>j k x. j \<in> I \<Longrightarrow>
      k \<in> I \<Longrightarrow>
      x \<in> body_overlap j k \<Longrightarrow>
      A j x = product_pull_near_top
        (coordinate_transition j k)
        (coordinate_transition k j) (A k) x"
    and cont_AP: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (C j)
        (case_prod (product_normal_derivative (A j)))"
    and cont_AQ: "\<And>j b. j \<in> I \<Longrightarrow>
      b \<in> Basis \<Longrightarrow>
      continuous_on (C j)
        (case_prod
          (product_tangential_derivative (A j) b))"
    and eqB: "\<And>i j x. i \<in> F \<Longrightarrow>
      j \<in> I \<Longrightarrow> x \<in> C j \<Longrightarrow>
      B i j x = weight_near_top (phi i) A j x"
    and dB: "\<And>i j x. i \<in> F \<Longrightarrow>
      j \<in> I \<Longrightarrow> x \<in> C j \<Longrightarrow>
      B i j differentiable (at x)"
    and cont_BP: "\<And>i j. i \<in> F \<Longrightarrow>
      j \<in> I \<Longrightarrow>
      continuous_on (C j)
        (case_prod (product_normal_derivative (B i j)))"
    and cont_BQ: "\<And>i j b. i \<in> F \<Longrightarrow>
      j \<in> I \<Longrightarrow> b \<in> Basis \<Longrightarrow>
      continuous_on (C j)
        (case_prod
          (product_tangential_derivative (B i j) b))"
  shows "integral_body_top
      (\<lambda>j x. product_exterior_top (A j) x) =
    integral_boundary_top
      (\<lambda>j y. product_boundary_coeff (A j) y)"
proof -
  let ?alpha = "\<lambda>j x. product_exterior_top (A j) x"
  let ?beta = "\<lambda>j y. product_boundary_coeff (A j) y"
  let ?alpha_i =
    "\<lambda>i j x. product_exterior_top (B i j) x"
  let ?beta_i =
    "\<lambda>i j y. product_boundary_coeff (B i j) y"
  let ?KB = "K \<inter> boundary_carrier"
  have compactB: "compact ?KB"
    by (rule compact_boundary_restriction[OF compact KM])
  have KB: "?KB \<subseteq> boundary_carrier"
    by auto
  have compatM: "body_top_coeff_compatible ?alpha"
    by (rule exterior_top_coeff_compatible_from_pullback
      [OF pull]) (use dA in auto)
  have supportM: "body_form_support ?alpha \<subseteq> K"
    by (rule exterior_top_support_subset
      [OF compact support]) simp
  have contM: "continuous_on (C j) (?alpha j)"
    if j: "j \<in> I" for j
    by (rule product_exterior_top_continuous_on)
       (use cont_AP[OF j] cont_AQ[OF j] in auto)
  have faceA: "near_top_face_pull_compatible A"
    by (rule near_top_face_pull_compatible_from_pullback
      [OF pull dA])
  have compatB: "boundary_top_coeff_compatible ?beta"
    by (rule boundary_coeff_compatible_from_geometric_pull
      [OF faceA]) simp
  have supportB: "boundary_form_support ?beta \<subseteq> ?KB"
  proof -
    have "boundary_form_support ?beta \<subseteq>
        near_top_form_support A \<inter> boundary_carrier"
      by (rule boundary_restriction_support) simp
    then show ?thesis using support by auto
  qed
  have contB: "continuous_on
      (halfspace_face (C j)) (?beta j)"
    if j: "j \<in> I" for j
    by (rule boundary_restriction_continuous
      [where A=A and edge="?beta" and i=j,
        OF j dA[OF j]]) auto
  have near_i: "near_top_form_support (B i) \<subseteq> K"
    if ii: "i \<in> F" for i
  proof -
    have eq: "near_top_form_support (B i) =
      near_top_form_support
        (weight_near_top (phi i) A)"
      by (rule near_top_form_support_cong_on_charts)
         (use eqB[OF ii] in auto)
    show ?thesis
      unfolding eq
      using weight_near_top_support[of "phi i" A]
        support by auto
  qed
  have pull_i: "B i j x =
    product_pull_near_top
      (coordinate_transition j k)
      (coordinate_transition k j) (B i k) x"
    if ii: "i \<in> F" and j: "j \<in> I"
      and k: "k \<in> I"
      and x: "x \<in> body_overlap j k"
    for i j k x
    by (rule extended_weight_pull_compatible
      [OF pull eqB ii j k x])
  have compatMi: "body_top_coeff_compatible (?alpha_i i)"
    if ii: "i \<in> F" for i
    by (rule exterior_top_coeff_compatible_from_pullback
      [OF pull_i[OF ii]])
       (use dB[OF ii] in auto)
  have supportMi: "body_form_support (?alpha_i i)
      \<subseteq> K"
    if ii: "i \<in> F" for i
    by (rule exterior_top_support_subset
      [OF compact near_i[OF ii]]) simp
  have contMi: "continuous_on (C j) (?alpha_i i j)"
    if ii: "i \<in> F" and j: "j \<in> I"
    for i j
    by (rule product_exterior_top_continuous_on)
       (use cont_BP[OF ii j]
         cont_BQ[OF ii j] in auto)
  have compatBi: "boundary_top_coeff_compatible (?beta_i i)"
    if ii: "i \<in> F" for i
  proof -
    have face: "near_top_face_pull_compatible (B i)"
      by (rule near_top_face_pull_compatible_from_pullback
        [OF pull_i[OF ii]])
         (use dB[OF ii] in auto)
    show ?thesis
      by (rule boundary_coeff_compatible_from_geometric_pull
        [OF face]) simp
  qed
  have supportBi: "boundary_form_support (?beta_i i)
      \<subseteq> ?KB"
    if ii: "i \<in> F" for i
    using boundary_restriction_support
      [where A="B i" and edge="?beta_i i"]
      near_i[OF ii]
    by auto
  have contBi: "continuous_on
      (halfspace_face (C j)) (?beta_i i j)"
    if ii: "i \<in> F" and j: "j \<in> I"
    for i j
    by (rule boundary_restriction_continuous
      [where A="B i" and edge="?beta_i i" and i=j,
        OF j dB[OF ii j]]) auto
  have sumM: "?alpha j x =
      (\<Sum>i\<in>F. ?alpha_i i j x)"
    if j: "j \<in> I"
      and x: "x \<in> C j \<inter> open_halfspace"
    for j x
    by (rule exterior_top_partition_sum_extensions
      [OF finite support unity eqB _ j x])
       (use dB in auto)
  have sumB: "?beta j y =
      (\<Sum>i\<in>F. ?beta_i i j y)"
    if j: "j \<in> I"
      and y: "y \<in> halfspace_face (C j)"
    for j y
    by (rule boundary_coeff_partition_sum_extensions
      [OF finite support unity eqB j y])
  have local_stokes:
      "integral_body_top (?alpha_i i) =
        integral_boundary_top (?beta_i i)"
    if ii: "i \<in> F" for i
  proof -
    obtain L where closed: "closed L"
      and phi_support:
        "{p\<in>M. phi i p \<noteq> 0} \<subseteq> L"
      and LD: "L \<subseteq> D i"
      using local[OF ii] by blast
    have iI: "i \<in> I"
      using FI ii by auto
    show ?thesis
      by (rule extended_weight_chart_stokes
        [where A=A and B=B and F=F and phi=phi
          and i=i and K=K and L=L,
          OF compact support pull eqB ii iI
          closed LD phi_support
          dB[OF ii] cont_BP[OF ii]
          cont_BQ[OF ii]])
  qed
  show ?thesis
    by (rule finite_stokes_gluing
      [OF finite compact KM compactB KB
        compatM supportM contM
        compatB supportB contB
        compatMi supportMi contMi
        compatBi supportBi contBi
        sumM sumB local_stokes])
qed

theorem global_stokes:
  fixes A :: "'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
  assumes compact: "compact K"
    and KM: "K \<subseteq> M"
    and support: "near_top_form_support A \<subseteq> K"
    and dA: "\<And>j x. j \<in> I \<Longrightarrow>
      x \<in> C j \<Longrightarrow>
      A j differentiable (at x)"
    and pull: "\<And>j k x. j \<in> I \<Longrightarrow>
      k \<in> I \<Longrightarrow>
      x \<in> body_overlap j k \<Longrightarrow>
      A j x = product_pull_near_top
        (coordinate_transition j k)
        (coordinate_transition k j) (A k) x"
    and cont_AP: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (C j)
        (case_prod (product_normal_derivative (A j)))"
    and cont_AQ: "\<And>j b. j \<in> I \<Longrightarrow>
      b \<in> Basis \<Longrightarrow>
      continuous_on (C j)
        (case_prod
          (product_tangential_derivative (A j) b))"
  shows "integral_body_top
      (\<lambda>j x. product_exterior_top (A j) x) =
    integral_boundary_top
      (\<lambda>j y. product_boundary_coeff (A j) y)"
proof -
  let ?alpha = "\<lambda>j x. product_exterior_top (A j) x"
  have support_body: "body_form_support ?alpha \<subseteq> K"
    by (rule exterior_top_support_subset
      [OF compact support]) simp
  have ex: "\<exists>phi F.
      admissible_body_partition ?alpha phi F \<and>
      (\<forall>p\<in>K. (\<Sum>i\<in>F. phi i p) = 1) \<and>
      (\<forall>i\<in>F. chartwise_C1_scalar (phi i)) \<and>
      (\<forall>i\<in>F. \<forall>p.
        0 \<le> phi i p \<and> phi i p \<le> 1)"
    by (rule body_C1_partition_exists
      [OF compact KM support_body])
  obtain phi F where partition:
      "admissible_body_partition ?alpha phi F"
    and unity: "\<forall>p\<in>K.
      (\<Sum>i\<in>F. phi i p) = 1"
    and C1: "\<forall>i\<in>F. chartwise_C1_scalar (phi i)"
    using ex by blast
  have finite: "finite F"
    and FI: "F \<subseteq> I"
    and local: "\<And>i. i \<in> F \<Longrightarrow>
      \<exists>L. closed L \<and>
        {p\<in>M. phi i p \<noteq> 0} \<subseteq> L \<and>
        L \<subseteq> D i"
    using partition
    by (auto simp: admissible_body_partition_def)
  let ?B = "\<lambda>i. reflected_weight_near_top (phi i) A"
  have eqB: "?B i j x =
      weight_near_top (phi i) A j x"
    if i: "i \<in> F" and j: "j \<in> I"
      and x: "x \<in> C j" for i j x
    by (rule reflected_weight_near_top_eq
      [OF C1[rule_format, OF i] j x])
  have dB: "?B i j differentiable (at x)"
    if i: "i \<in> F" and j: "j \<in> I"
      and x: "x \<in> C j" for i j x
    by (rule reflected_weight_near_top_differentiable
      [where rho="phi i" and A=A and j=j and x=x,
        OF C1[rule_format, OF i] j x dA[OF j x]])
  have cont_BP: "continuous_on (C j)
      (case_prod
        (product_normal_derivative (?B i j)))"
    if i: "i \<in> F" and j: "j \<in> I"
    for i j
    by (rule reflected_weight_near_top_normal_continuous
      [where rho="phi i" and A=A and j=j,
        OF C1[rule_format, OF i] j dA[OF j]
        cont_AP[OF j]])
  have cont_BQ: "continuous_on (C j)
      (case_prod
        (product_tangential_derivative (?B i j) b))"
    if i: "i \<in> F" and j: "j \<in> I"
      and b: "b \<in> Basis" for i j b
    by (rule
      reflected_weight_near_top_tangential_continuous
      [where rho="phi i" and A=A and j=j and b=b,
        OF C1[rule_format, OF i] j dA[OF j]
        cont_AQ[OF j b]])
  show ?thesis
    by (rule global_stokes_with_weight_extensions
      [OF compact KM support finite FI
        unity[rule_format] local dA pull
        cont_AP cont_AQ eqB dB cont_BP cont_BQ])
qed

corollary global_stokes_empty_boundary:
  fixes A :: "'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
  assumes empty: "boundary_carrier = {}"
    and compact: "compact K"
    and KM: "K \<subseteq> M"
    and support: "near_top_form_support A \<subseteq> K"
    and dA: "\<And>j x. j \<in> I \<Longrightarrow>
      x \<in> C j \<Longrightarrow>
      A j differentiable (at x)"
    and pull: "\<And>j k x. j \<in> I \<Longrightarrow>
      k \<in> I \<Longrightarrow>
      x \<in> body_overlap j k \<Longrightarrow>
      A j x = product_pull_near_top
        (coordinate_transition j k)
        (coordinate_transition k j) (A k) x"
    and cont_AP: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (C j)
        (case_prod (product_normal_derivative (A j)))"
    and cont_AQ: "\<And>j b. j \<in> I \<Longrightarrow>
      b \<in> Basis \<Longrightarrow>
      continuous_on (C j)
        (case_prod
          (product_tangential_derivative (A j) b))"
  shows "integral_body_top
      (\<lambda>j x. product_exterior_top (A j) x) = 0"
  using global_stokes[OF compact KM support
    dA pull cont_AP cont_AQ]
    integral_boundary_top_empty[OF empty]
  by simp

corollary global_stokes_compact_carrier:
  fixes A :: "'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow>
      real \<times> (real ^ 'n)"
  assumes compact: "compact M"
    and dA: "\<And>j x. j \<in> I \<Longrightarrow>
      x \<in> C j \<Longrightarrow>
      A j differentiable (at x)"
    and pull: "\<And>j k x. j \<in> I \<Longrightarrow>
      k \<in> I \<Longrightarrow>
      x \<in> body_overlap j k \<Longrightarrow>
      A j x = product_pull_near_top
        (coordinate_transition j k)
        (coordinate_transition k j) (A k) x"
    and cont_AP: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (C j)
        (case_prod (product_normal_derivative (A j)))"
    and cont_AQ: "\<And>j b. j \<in> I \<Longrightarrow>
      b \<in> Basis \<Longrightarrow>
      continuous_on (C j)
        (case_prod
          (product_tangential_derivative (A j) b))"
  shows "integral_body_top
      (\<lambda>j x. product_exterior_top (A j) x) =
    integral_boundary_top
      (\<lambda>j y. product_boundary_coeff (A j) y)"
proof -
  have support: "near_top_form_support A \<subseteq> M"
    by (simp add: near_top_form_support_def)
  show ?thesis
    by (rule global_stokes
      [OF compact subset_refl support dA pull
        cont_AP cont_AQ])
qed

end

end
