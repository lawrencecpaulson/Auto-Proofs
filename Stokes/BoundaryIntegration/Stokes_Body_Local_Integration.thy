theory Stokes_Body_Local_Integration
  imports Stokes_Body_Overlap
begin

lemma product_to_cart_normal_axis:
  "product_to_cart (1,0::real ^ 'n::finite) =
    axis (Inl ()) 1"
  by (simp add: product_to_cart_def axis_def
    vec_eq_iff split: sum.splits)

lemma product_to_cart_tangent_axis:
  "product_to_cart (0,axis j 1::real ^ 'n::finite) =
    axis (Inr j) 1"
  by (simp add: product_to_cart_def axis_def
    vec_eq_iff split: sum.splits)

lemma product_to_cart_Basis:
  "product_to_cart ` (Basis ::
      (real \<times> (real ^ 'n::finite)) set) =
    (Basis :: (real ^ (unit + 'n)) set)"
proof
  show "product_to_cart ` (Basis ::
      (real \<times> (real ^ 'n)) set)
      \<subseteq> (Basis :: (real ^ (unit + 'n)) set)"
    by (auto simp: Basis_prod_def Basis_real_def
      Basis_vec_def product_to_cart_normal_axis
      product_to_cart_tangent_axis)
  show "(Basis :: (real ^ (unit + 'n)) set)
      \<subseteq> product_to_cart ` (Basis ::
        (real \<times> (real ^ 'n)) set)"
  proof
    fix v :: "real ^ (unit + 'n)"
    assume "v \<in> Basis"
    then obtain k where v: "v = axis k 1"
      by (auto simp: Basis_vec_def)
    show "v \<in> product_to_cart ` (Basis ::
        (real \<times> (real ^ 'n)) set)"
    proof (cases k)
      case (Inl u)
      then have "u = ()" by simp
      have realbasis: "(1::real) \<in> Basis"
        by (simp add: Basis_real_def)
      have basis: "(1::real,0::real ^ 'n) \<in> Basis"
        using realbasis
        by (auto simp: Basis_prod_def)
      have "product_to_cart (1::real,0::real ^ 'n)
        \<in> product_to_cart ` (Basis ::
          (real \<times> (real ^ 'n)) set)"
        by (rule imageI[OF basis])
      then show ?thesis
        using v Inl \<open>u = ()\<close>
        by (simp add: product_to_cart_normal_axis)
    next
      case (Inr j)
      have axisbasis: "axis j 1 \<in> (Basis ::
          (real ^ 'n) set)"
        by (auto simp: Basis_vec_def
          intro!: exI[where x=j])
      have basis: "(0,axis j 1) \<in> (Basis ::
          (real \<times> (real ^ 'n)) set)"
        using axisbasis
        by (auto simp: Basis_prod_def)
      have "product_to_cart (0,axis j 1)
        \<in> product_to_cart ` (Basis ::
          (real \<times> (real ^ 'n)) set)"
        by (rule imageI[OF basis])
      then show ?thesis
        using v Inr
        by (simp add: product_to_cart_tangent_axis)
    qed
  qed
qed

lemma product_cart_det_linear:
  fixes L :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
    (real \<times> (real ^ 'n))"
  assumes L: "linear L"
  shows "eucl.det L = Determinants.det
    (matrix (product_to_cart \<circ> L \<circ> cart_to_product))"
proof -
  have inj_h: "inj (product_to_cart ::
      (real \<times> (real ^ 'n)) \<Rightarrow>
      real ^ (unit + 'n))"
    by (rule injI)
       (metis cart_to_product_to_cart)
  have surj_h: "surj (product_to_cart ::
      (real \<times> (real ^ 'n)) \<Rightarrow>
      real ^ (unit + 'n))"
    unfolding surj_def
    by (metis product_to_cart_to_product)
  have bij_h: "bij (product_to_cart ::
      (real \<times> (real ^ 'n)) \<Rightarrow>
      real ^ (unit + 'n))"
    using inj_h surj_h by (simp add: bij_def)
  have basis_h: "bij_betw product_to_cart
      (Basis :: (real \<times> (real ^ 'n)) set)
      (Basis :: (real ^ (unit + 'n)) set)"
  proof -
    have "inj_on product_to_cart
        (Basis :: (real \<times> (real ^ 'n)) set)"
      by (rule inj_onI)
         (erule injD[OF inj_h])
    then show ?thesis
      using product_to_cart_Basis
      by (simp add: bij_betw_def)
  qed
  have inv_h: "inv product_to_cart =
      (cart_to_product ::
        real ^ (unit + 'n) \<Rightarrow>
          (real \<times> (real ^ 'n)))"
    by (rule ext)
       (metis inj_h inv_f_f
         product_to_cart_to_product)
  have det: "eucl.det L = eucl.det
      (product_to_cart \<circ> L \<circ> inv product_to_cart)"
  proof (rule finite_dimensional_vector_space_pair.det_basis_change)
    show "finite_dimensional_vector_space_pair
        (scaleR :: real \<Rightarrow>
          (real \<times> (real ^ 'n)) \<Rightarrow> _)
        (Basis :: (real \<times> (real ^ 'n)) set)
        (scaleR :: real \<Rightarrow>
          (real ^ (unit + 'n)) \<Rightarrow> _)
        (Basis :: (real ^ (unit + 'n)) set)"
      by unfold_locales
    show "Vector_Spaces.linear
        (scaleR :: real \<Rightarrow>
          (real \<times> (real ^ 'n)) \<Rightarrow> _)
        (scaleR :: real \<Rightarrow>
          (real ^ (unit + 'n)) \<Rightarrow> _)
        product_to_cart"
      using product_to_cart_linear
      by (simp add: linear_def)
    show "bij_betw product_to_cart
        (Basis :: (real \<times> (real ^ 'n)) set)
        (Basis :: (real ^ (unit + 'n)) set)"
      by (rule basis_h)
  qed
  have lin_cart: "linear
      (product_to_cart \<circ> L \<circ> cart_to_product)"
    by (intro linear_compose product_to_cart_linear L
      cart_to_product_linear)
  show ?thesis
    using det eucl_det_conv_matrix_det[OF lin_cart]
    by (simp only: inv_h)
qed

lemma product_cart_jacobian_det:
  fixes f :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
    (real \<times> (real ^ 'n))"
  assumes df: "f differentiable (at x)"
  shows "Determinants.det
      (jacobian (cart_map_of_product f)
        (at (product_to_cart x))) =
    eucl.det (frechet_derivative f (at x))"
proof -
  let ?v = "product_to_cart x"
  have dC: "cart_to_product differentiable (at ?v)"
    by (rule bounded_linear_imp_differentiable
      [OF cart_to_product_bounded_linear])
  have dFC: "(f \<circ> cart_to_product)
      differentiable (at ?v)"
    by (rule differentiable_chain_at[OF dC])
       (use df in simp)
  have dP: "product_to_cart differentiable
      (at (f x))"
    by (rule bounded_linear_imp_differentiable
      [OF product_to_cart_bounded_linear])
  have dc: "frechet_derivative
      (f \<circ> cart_to_product) (at ?v) =
      frechet_derivative f (at x) \<circ>
        cart_to_product"
    using dC df
    by (simp add: frechet_derivative_compose)
  have dpc: "frechet_derivative
      (product_to_cart \<circ> (f \<circ> cart_to_product))
        (at ?v) =
      product_to_cart \<circ>
        frechet_derivative
          (f \<circ> cart_to_product) (at ?v)"
    using dFC dP
    by (simp add: frechet_derivative_compose)
  have map_eq: "cart_map_of_product f =
      product_to_cart \<circ> (f \<circ> cart_to_product)"
    by (rule ext)
       (simp add: cart_map_of_product_def)
  have deriv_eq: "frechet_derivative
      (cart_map_of_product f) (at ?v) =
      product_to_cart \<circ>
        frechet_derivative f (at x) \<circ>
          cart_to_product"
    using dpc dc by (simp add: map_eq comp_assoc)
  have lin: "linear (frechet_derivative f (at x))"
    by (rule linear_frechet_derivative[OF df])
  show ?thesis
    using product_cart_det_linear[OF lin]
    by (simp add: jacobian_def deriv_eq)
qed

lemma product_pull_near_top_differentiable_C2:
  fixes f g A :: "(real \<times> (real ^ 'n::finite))
    \<Rightarrow> (real \<times> (real ^ 'n))"
  assumes C2f: "Ck_on 2 f U" and pU: "p \<in> U"
    and C2g: "Ck_on 2 g V" and fpV: "f p \<in> V"
    and dA: "A differentiable (at (f p))"
  shows "product_pull_near_top f g A
    differentiable (at p)"
proof -
  let ?F = "cart_map_of_product f"
  let ?G = "cart_map_of_product g"
  let ?B = "cart_form_of_product A"
  let ?v = "product_to_cart p"
  have C2F: "Ck_on 2 ?F (cart_to_product -` U)"
    by (rule Ck_on_cart_map_of_product[OF C2f])
  have C2G: "Ck_on 2 ?G (cart_to_product -` V)"
    by (rule Ck_on_cart_map_of_product[OF C2g])
  have dB: "?B differentiable (at (?F ?v))"
    using cart_form_of_product_differentiable[OF dA]
    by simp
  have dPB: "pull_near_top ?F ?G ?B
      differentiable (at ?v)"
    by (rule pull_near_top_differentiable_C2
      [OF C2F _ C2G _ dB])
       (use pU fpV in
         \<open>auto simp: cart_map_of_product_def\<close>)
  show ?thesis
    unfolding product_pull_near_top_def
    by (rule product_form_of_cart_differentiable
      [OF dPB])
qed

lemma closure_product_open_halfspace:
  "closure (open_halfspace ::
      (real \<times> (real ^ 'n::finite)) set) =
    closed_halfspace"
proof -
  let ?a = "(1::real,0::real ^ 'n)"
  have nonzero: "?a \<noteq> 0"
    by (simp add: zero_prod_def)
  have open_eq: "(open_halfspace ::
      (real \<times> (real ^ 'n)) set) =
    {p. ?a \<bullet> p > 0}"
    by (auto simp: open_halfspace_def
      inner_prod_def)
  have closed_eq: "(closed_halfspace ::
      (real \<times> (real ^ 'n)) set) =
    {p. ?a \<bullet> p \<ge> 0}"
    by (auto simp: closed_halfspace_def
      inner_prod_def)
  show ?thesis
    using closure_halfspace_gt[OF nonzero, of 0]
    by (simp add: open_eq closed_eq)
qed

lemma face_in_closure_open_halfspace:
  fixes y :: "real ^ 'n::finite"
  assumes U: "open U" "(0,y) \<in> U"
  shows "(0,y) \<in> closure (U \<inter> open_halfspace)"
proof -
  have face: "(0,y) \<in> closure
      (open_halfspace ::
        (real \<times> (real ^ 'n)) set)"
    by (simp add: closure_product_open_halfspace
      closed_halfspace_def)
  show ?thesis
    using open_Int_closure_subset[OF U(1), of open_halfspace]
      U(2) face
    by auto
qed

lemma continuous_agree_at_closure:
  fixes f g :: "'a::{perfect_space,t2_space} \<Rightarrow>
    'b::t2_space"
  assumes cont_f: "continuous (at x) f"
    and cont_g: "continuous (at x) g"
    and closure: "x \<in> closure S"
    and out: "x \<notin> S"
    and agree: "\<And>q. q \<in> S \<Longrightarrow> f q = g q"
  shows "f x = g x"
proof -
  have nontrivial: "at x within S \<noteq> bot"
    using closure out
    by (simp add: at_within_eq_bot_iff)
  have lim_f: "(f \<longlongrightarrow> f x) (at x within S)"
    using cont_f continuous_at_imp_continuous_within
    by (simp add: continuous_within)
  have eventually_eq: "eventually
      (\<lambda>q. f q = g q) (at x within S)"
    using agree
    by (auto simp: eventually_at_filter)
  have lim_gf: "(g \<longlongrightarrow> f x)
      (at x within S)"
    using lim_f eventually_eq
    by (simp add: tendsto_cong)
  have lim_g: "(g \<longlongrightarrow> g x)
      (at x within S)"
    using cont_g continuous_at_imp_continuous_within
    by (simp add: continuous_within)
  show ?thesis
    using tendsto_unique[OF nontrivial lim_gf lim_g]
    by simp
qed

lemma product_exterior_top_continuous_on:
  fixes A :: "real \<times> (real ^ 'n::finite)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes cont_P: "continuous_on S
      (case_prod (product_normal_derivative A))"
    and cont_Q: "\<And>b. b \<in> Basis \<Longrightarrow>
      continuous_on S
        (case_prod (product_tangential_derivative A b))"
  shows "continuous_on S (product_exterior_top A)"
proof -
  have cont: "continuous_on S
      (\<lambda>p. case_prod (product_normal_derivative A) p -
        (\<Sum>b\<in>Basis.
          case_prod (product_tangential_derivative A b) p))"
    by (intro continuous_intros cont_P cont_Q)
  have eq: "\<And>p. p \<in> S \<Longrightarrow>
      product_exterior_top A p =
      case_prod (product_normal_derivative A) p -
        (\<Sum>b\<in>Basis.
          case_prod (product_tangential_derivative A b) p)"
  proof -
    fix p
    assume "p \<in> S"
    show "product_exterior_top A p =
      case_prod (product_normal_derivative A) p -
        (\<Sum>b\<in>Basis.
          case_prod (product_tangential_derivative A b) p)"
      by (cases p)
         (simp add: product_exterior_top_coordinate)
  qed
  show ?thesis
    using cont
    by (subst continuous_on_cong[OF refl eq])
       simp
qed

context positively_oriented_C2_halfspace_atlas
begin

definition near_top_form_support ::
    "('i \<Rightarrow> real \<times> (real ^ 'n)
      \<Rightarrow> real \<times> (real ^ 'n)) \<Rightarrow> 'a set"
  where "near_top_form_support A =
    {p\<in>M. \<exists>i\<in>I.
      p \<in> D i \<and> A i (to_chart i p) \<noteq> 0}"

lemma boundary_restriction_support:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes edge_coeff: "\<And>i y. i \<in> I
      \<Longrightarrow> y \<in> halfspace_face (C i)
      \<Longrightarrow> edge i y =
        product_boundary_coeff (A i) y"
  shows "boundary_form_support edge \<subseteq>
    near_top_form_support A \<inter> boundary_carrier"
proof
  fix p
  assume supp: "p \<in> boundary_form_support edge"
  then obtain i where i: "i \<in> I" "p \<in> D i"
    "edge i (snd (to_chart i p)) \<noteq> 0"
    by (auto simp: boundary_form_support_def)
  have pB: "p \<in> boundary_carrier"
    using supp by (simp add: boundary_form_support_def)
  have normal_zero: "fst (to_chart i p) = 0"
    using boundary_chart_classify[OF i(1,2)] pB
    by simp
  have xy: "(0,snd (to_chart i p)) = to_chart i p"
    using normal_zero by (cases "to_chart i p") auto
  have yface: "snd (to_chart i p)
      \<in> halfspace_face (C i)"
    using halfspace_chart.chart_image[OF chart[OF i(1)]]
      i(2) xy
    by (auto simp: halfspace_face_def)
  have nonzero: "A i (to_chart i p) \<noteq> 0"
    using i(3) edge_coeff[OF i(1) yface] xy
    by (auto simp: product_boundary_coeff_def
      product_normal_coeff_def)
  have pM: "p \<in> M"
    using domain_subset_carrier[OF i(1)] i(2) by auto
  show "p \<in> near_top_form_support A \<inter>
      boundary_carrier"
    using pM i(1,2) nonzero pB
    by (auto simp: near_top_form_support_def)
qed

lemma boundary_restriction_admissible_single:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes i: "i \<in> I"
    and compact: "compact K"
    and K_M: "K \<subseteq> M"
    and Kchart: "K \<subseteq> D i"
    and support: "near_top_form_support A \<subseteq> K"
    and edge_coeff: "\<And>j y. j \<in> I
      \<Longrightarrow> y \<in> halfspace_face (C j)
      \<Longrightarrow> edge j y =
        product_boundary_coeff (A j) y"
  shows "admissible_boundary_single_chart
    edge i (K \<inter> boundary_carrier)"
proof -
  have compact_edge: "compact (K \<inter>
      boundary_carrier)"
    by (rule compact_boundary_restriction
      [OF compact K_M])
  have suppA: "boundary_form_support edge
      \<subseteq> near_top_form_support A \<inter>
        boundary_carrier"
    by (rule boundary_restriction_support
      [where A=A and edge=edge, OF edge_coeff])
  have support_edge: "boundary_form_support edge
      \<subseteq> K \<inter> boundary_carrier"
    using suppA support by blast
  show ?thesis
    using i compact_edge support_edge Kchart
    by (auto simp: admissible_boundary_single_chart_def)
qed

definition near_top_face_pull_compatible ::
    "('i \<Rightarrow> real \<times> (real ^ 'n)
      \<Rightarrow> real \<times> (real ^ 'n)) \<Rightarrow> bool"
  where "near_top_face_pull_compatible A \<longleftrightarrow>
    (\<forall>i\<in>I. \<forall>j\<in>I.
      \<forall>y\<in>boundary_overlap i j.
      \<forall>U V F G.
        Ck_on 2 F U \<and> (0,y) \<in> U \<and>
        Ck_on 2 G V \<and>
        (\<forall>x\<in>U \<inter> closed_halfspace.
          F x \<in> V \<and> G (F x) = x \<and>
          F x \<in> closed_halfspace \<and>
          F x = coordinate_transition i j x) \<and>
        (\<forall>x\<in>U.
          fst x = 0 \<longrightarrow> fst (F x) = 0) \<and>
        (\<forall>x\<in>V.
          fst x = 0 \<longrightarrow> fst (G x) = 0)
        \<longrightarrow> A i (0,y) =
          product_pull_near_top F G (A j) (0,y))"

lemma boundary_coeff_compatible_from_geometric_pull:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes face_pull: "near_top_face_pull_compatible A"
    and edge_coeff: "\<And>i y. i \<in> I \<Longrightarrow>
      y \<in> halfspace_face (C i) \<Longrightarrow>
      edge i y = product_boundary_coeff (A i) y"
  shows "boundary_top_coeff_compatible edge"
proof (unfold boundary_top_coeff_compatible_def,
    intro ballI)
  fix i j y
  assume i: "i \<in> I" and j: "j \<in> I"
    and y: "y \<in> boundary_overlap i j"
  obtain U V F G where C2F: "Ck_on 2 F U"
    and xU: "(0,y) \<in> U"
    and C2G: "Ck_on 2 G V"
    and local: "\<forall>x\<in>U \<inter> closed_halfspace.
      F x \<in> V \<and> G (F x) = x \<and>
      F x \<in> closed_halfspace \<and>
      F x = coordinate_transition i j x"
    and faceF: "\<forall>x\<in>U.
      fst x = 0 \<longrightarrow> fst (F x) = 0"
    and faceG: "\<forall>x\<in>V.
      fst x = 0 \<longrightarrow> fst (G x) = 0"
    using local_transition_extensions_inverse[OF i j y]
    by blast
  have form: "A i (0,y) =
      product_pull_near_top F G (A j) (0,y)"
    using face_pull i j y C2F xU C2G
      local faceF faceG
    by (auto simp: near_top_face_pull_compatible_def)
  have law: "\<forall>B.
      product_boundary_coeff
        (product_pull_near_top F G B) y =
      pull_top (boundary_transition i j)
        (product_boundary_coeff B) y"
    by (rule boundary_coefficient_transition_for_extensions
      [OF i j y C2F xU C2G local faceF faceG])
  have law_A: "product_boundary_coeff
      (product_pull_near_top F G (A j)) y =
      pull_top (boundary_transition i j)
        (product_boundary_coeff (A j)) y"
    using law by blast
  have yface: "y \<in> halfspace_face (C i)"
    using y by (auto simp: boundary_overlap_def)
  have z: "boundary_transition i j y
      \<in> boundary_overlap j i"
    using homeomorphism_image1
      [OF boundary_transition_homeomorphism[OF i j]]
      y by auto
  have zface: "boundary_transition i j y
      \<in> halfspace_face (C j)"
    using z by (auto simp: boundary_overlap_def)
  have coeff_eq: "product_boundary_coeff (A i) y =
      pull_top (boundary_transition i j)
        (product_boundary_coeff (A j)) y"
    using form law_A
    by (simp add: product_boundary_coeff_def
      product_normal_coeff_def)
  show "edge i y =
      pull_top (boundary_transition i j) (edge j) y"
    using coeff_eq edge_coeff[OF i yface]
      edge_coeff[OF j zface]
    by (simp add: pull_top_def)
qed

lemma boundary_restriction_continuous:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes i: "i \<in> I"
    and dA: "\<And>x. x \<in> C i \<Longrightarrow>
      A i differentiable (at x)"
    and edge_coeff: "\<And>y. y \<in> halfspace_face (C i)
      \<Longrightarrow> edge i y =
        product_boundary_coeff (A i) y"
  shows "continuous_on
    (halfspace_face (C i)) (edge i)"
proof -
  let ?E = "halfspace_face (C i)"
  have cont_A: "continuous_on (C i) (A i)"
  proof (rule differentiable_imp_continuous_on)
    show "A i differentiable_on C i"
      using dA
      by (auto simp: differentiable_on_def
        intro: differentiable_at_withinI)
  qed
  have cont_embed: "continuous_on ?E
      (\<lambda>y. (0::real,y))"
    by (intro continuous_intros)
  have embed_C: "(\<lambda>y. (0::real,y)) ` ?E
      \<subseteq> C i"
    by (auto simp: halfspace_face_def)
  have cont_comp: "continuous_on ?E
      (\<lambda>y. A i (0,y))"
    by (rule continuous_on_compose2
      [OF cont_A cont_embed embed_C])
  have cont_coeff: "continuous_on ?E
      (\<lambda>y. - fst (A i (0,y)))"
    by (intro continuous_intros cont_comp)
  have eq: "\<And>y. y \<in> ?E \<Longrightarrow>
      edge i y = - fst (A i (0,y))"
    using edge_coeff
    by (simp add: product_boundary_coeff_def
      product_normal_coeff_def)
  show ?thesis
    using cont_coeff
    by (subst continuous_on_cong[OF refl eq])
       simp
qed

definition body_top_coeff_compatible ::
    "('i \<Rightarrow> real \<times> (real ^ 'n) \<Rightarrow> real)
      \<Rightarrow> bool"
  where "body_top_coeff_compatible alpha \<longleftrightarrow>
    (\<forall>i\<in>I. \<forall>j\<in>I. \<forall>x\<in>body_overlap i j.
      alpha i x =
        eucl.det (frechet_derivative
          (coordinate_transition i j) (at x)) *
        alpha j (coordinate_transition i j x))"

definition body_form_support ::
    "('i \<Rightarrow> real \<times> (real ^ 'n) \<Rightarrow> real)
      \<Rightarrow> 'a set"
  where "body_form_support alpha =
    {p\<in>interior_carrier. \<exists>i\<in>I.
      p \<in> D i \<and> alpha i (to_chart i p) \<noteq> 0}"

lemma body_interior_chart_classify:
  assumes i: "i \<in> I" and p: "p \<in> D i"
  shows "p \<in> interior_carrier \<longleftrightarrow>
    0 < fst (to_chart i p)"
proof -
  have pM: "p \<in> M"
    using domain_subset_carrier[OF i] p by auto
  have xC: "to_chart i p \<in> C i"
    using halfspace_chart.chart_image[OF chart[OF i]] p
    by auto
  have nonnegative: "0 \<le> fst (to_chart i p)"
    using halfspace_chart.codomain_subset_halfspace
      [OF chart[OF i]] xC
    by (auto simp: closed_halfspace_def)
  show ?thesis
    using pM nonnegative boundary_chart_classify[OF i p]
    by (auto simp: interior_carrier_def)
qed

lemma body_form_support_chart:
  assumes compatible: "body_top_coeff_compatible alpha"
    and positive: "\<And>i j x.
      i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
      x \<in> body_overlap i j \<Longrightarrow>
      0 < eucl.det (frechet_derivative
        (coordinate_transition i j) (at x))"
    and i: "i \<in> I"
    and p: "p \<in> interior_carrier \<inter> D i"
  shows "p \<in> body_form_support alpha \<longleftrightarrow>
    alpha i (to_chart i p) \<noteq> 0"
proof
  assume supp: "p \<in> body_form_support alpha"
  then obtain j where j: "j \<in> I" "p \<in> D j"
    "alpha j (to_chart j p) \<noteq> 0"
    by (auto simp: body_form_support_def)
  have pi: "p \<in> D i" using p by auto
  have xC: "to_chart i p \<in> C i"
    using halfspace_chart.chart_image[OF chart[OF i]]
      pi by auto
  have x_pos: "0 < fst (to_chart i p)"
    using body_interior_chart_classify[OF i pi] p by auto
  have xij: "to_chart i p \<in> body_overlap i j"
    using xC j(2)
      halfspace_chart.to_from[OF chart[OF i] pi]
      x_pos
    by (auto simp: body_overlap_def
      coordinate_overlap_def open_halfspace_def)
  have trans: "coordinate_transition i j
      (to_chart i p) = to_chart j p"
    using halfspace_chart.to_from[OF chart[OF i] pi]
    by (simp add: coordinate_transition_def)
  have coeff: "alpha i (to_chart i p) =
      eucl.det (frechet_derivative
        (coordinate_transition i j)
          (at (to_chart i p))) *
      alpha j (to_chart j p)"
    using compatible i j(1) xij trans
    by (auto simp: body_top_coeff_compatible_def)
  show "alpha i (to_chart i p) \<noteq> 0"
    using coeff positive[OF i j(1) xij] j(3)
    by auto
next
  assume nonzero: "alpha i (to_chart i p) \<noteq> 0"
  show "p \<in> body_form_support alpha"
    using p i nonzero
    by (auto simp: body_form_support_def)
qed

lemma body_chart_integral_localized_form:
  fixes alpha :: "'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow> real"
  assumes i: "i \<in> I"
    and compatible: "body_top_coeff_compatible alpha"
    and positive: "\<And>i j x.
      i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
      x \<in> body_overlap i j \<Longrightarrow>
      0 < eucl.det (frechet_derivative
        (coordinate_transition i j) (at x))"
    and support: "body_form_support alpha \<subseteq> K"
    and Kchart: "K \<subseteq> D j"
  shows "integral (C i) (alpha i) =
    integral (body_overlap i j) (alpha i)"
proof (rule body_chart_integral_localized[OF i])
  fix x
  assume x: "x \<in> C i \<inter> open_halfspace"
    and out: "x \<notin> body_overlap i j"
  let ?p = "from_chart i x"
  have xi: "x \<in> C i" and xpos: "0 < fst x"
    using x by (auto simp: open_halfspace_def)
  have pi: "?p \<in> D i"
    using halfspace_chart.inverse_image[OF chart[OF i]]
      xi by auto
  have chart_i: "to_chart i ?p = x"
    by (rule halfspace_chart.from_to[OF chart[OF i] xi])
  have p_int: "?p \<in> interior_carrier"
    using body_interior_chart_classify[OF i pi]
      chart_i xpos by simp
  have p_not_j: "?p \<notin> D j"
    using xi out xpos by (simp add: body_overlap_def
      coordinate_overlap_def open_halfspace_def)
  show "alpha i x = 0"
  proof (rule ccontr)
    assume nonzero: "alpha i x \<noteq> 0"
    have supp: "?p \<in> body_form_support alpha"
      using body_form_support_chart
        [OF compatible positive i]
        p_int pi chart_i nonzero by auto
    have "?p \<in> D j"
      using support Kchart supp by auto
    with p_not_j show False by simp
  qed
qed

theorem body_single_chart_integral_independent:
  fixes alpha :: "'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow> real"
  assumes i: "i \<in> I" and j: "j \<in> I"
    and compatible: "body_top_coeff_compatible alpha"
    and positive: "\<And>i j x.
      i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
      x \<in> body_overlap i j \<Longrightarrow>
      0 < eucl.det (frechet_derivative
        (coordinate_transition i j) (at x))"
    and smooth: "Ck_on 2 (coordinate_transition i j)
      (body_overlap i j)"
    and support_i: "body_form_support alpha \<subseteq> K_i"
    and K_i_chart: "K_i \<subseteq> D i"
    and support_j: "body_form_support alpha \<subseteq> K_j"
    and K_j_chart: "K_j \<subseteq> D j"
    and int_j: "alpha j absolutely_integrable_on C j"
  shows "integral (C i) (alpha i) =
    integral (C j) (alpha j)"
proof -
  have left: "integral (C i) (alpha i) =
    integral (body_overlap i j) (alpha i)"
    by (rule body_chart_integral_localized_form
      [OF i compatible positive support_j K_j_chart])
  have right: "integral (C j) (alpha j) =
    integral (body_overlap j i) (alpha j)"
    by (rule body_chart_integral_localized_form
      [OF j compatible positive support_i K_i_chart])
  have measurable: "body_overlap j i \<in> sets lebesgue"
    using body_overlap_open[OF j i]
    by (metis borel_open sets_lborel sets_completionI_sets)
  have subset: "body_overlap j i \<subseteq> C j"
    by (auto simp: body_overlap_def
      coordinate_overlap_def)
  have int_overlap: "alpha j absolutely_integrable_on
      body_overlap j i"
    by (rule set_integrable_subset
      [OF int_j measurable subset])
  have coeff: "\<And>x. x \<in> body_overlap i j \<Longrightarrow>
      alpha i x =
        eucl.det (frechet_derivative
          (coordinate_transition i j) (at x)) *
        alpha j (coordinate_transition i j x)"
    using compatible i j
    by (auto simp: body_top_coeff_compatible_def)
  have change: "integral (body_overlap i j) (alpha i) =
    integral (body_overlap j i) (alpha j)"
    by (rule body_overlap_integral
      [OF i j smooth positive[OF i j]
        int_overlap coeff])
  show ?thesis
    using left change right by simp
qed

definition admissible_body_single_chart ::
    "('i \<Rightarrow> real \<times> (real ^ 'n) \<Rightarrow> real)
      \<Rightarrow> 'i \<Rightarrow> 'a set \<Rightarrow> bool"
  where "admissible_body_single_chart alpha i K \<longleftrightarrow>
    i \<in> I \<and> compact K \<and> K \<subseteq> D i \<and>
    body_form_support alpha \<subseteq> K \<and>
    alpha i absolutely_integrable_on C i"

definition integral_body_single_top ::
    "('i \<Rightarrow> real \<times> (real ^ 'n) \<Rightarrow> real)
      \<Rightarrow> real"
  where "integral_body_single_top alpha =
    (SOME z. \<exists>i K.
      admissible_body_single_chart alpha i K \<and>
      z = integral (C i) (alpha i))"

theorem integral_body_single_top_local_chart:
  fixes alpha :: "'i \<Rightarrow>
    real \<times> (real ^ 'n) \<Rightarrow> real"
  assumes chart_i: "admissible_body_single_chart alpha i K"
    and compatible: "body_top_coeff_compatible alpha"
    and positive: "\<And>i j x.
      i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
      x \<in> body_overlap i j \<Longrightarrow>
      0 < eucl.det (frechet_derivative
        (coordinate_transition i j) (at x))"
    and smooth: "\<And>i j.
      i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
      Ck_on 2 (coordinate_transition i j)
        (body_overlap i j)"
  shows "integral_body_single_top alpha =
    integral (C i) (alpha i)"
proof -
  let ?P = "\<lambda>z. \<exists>j L.
      admissible_body_single_chart alpha j L \<and>
      z = integral (C j) (alpha j)"
  have ex: "\<exists>z. ?P z"
    using chart_i by blast
  have some: "?P (SOME z. ?P z)"
    by (rule someI_ex[OF ex])
  then obtain j L where chart_j:
      "admissible_body_single_chart alpha j L"
    and eq: "(SOME z. ?P z) =
      integral (C j) (alpha j)"
    by blast
  have i: "i \<in> I"
    and support_i: "body_form_support alpha \<subseteq> K"
    and K_i_chart: "K \<subseteq> D i"
    using chart_i
    by (auto simp: admissible_body_single_chart_def)
  have j: "j \<in> I"
    and support_j: "body_form_support alpha \<subseteq> L"
    and K_j_chart: "L \<subseteq> D j"
    and int_j: "alpha j absolutely_integrable_on C j"
    using chart_j
    by (auto simp: admissible_body_single_chart_def)
  have chart_eq: "integral (C j) (alpha j) =
    integral (C i) (alpha i)"
    by (rule body_single_chart_integral_independent
      [OF j i compatible positive smooth[OF j i]
        support_j K_j_chart support_i K_i_chart])
       (use chart_i in
        \<open>auto simp: admissible_body_single_chart_def\<close>)
  show ?thesis
    using eq chart_eq
    by (simp only: integral_body_single_top_def)
qed

lemma body_chart_lborel_eq_integral:
  fixes f :: "real \<times> (real ^ 'n) \<Rightarrow> real"
  assumes i: "i \<in> I"
    and integrable: "f absolutely_integrable_on C i"
    and continuous: "continuous_on (C i) f"
  shows "(LINT x : C i | lborel. f x) =
    integral (C i) f"
proof -
  obtain U where U: "open U"
    "C i = closed_halfspace \<inter> U"
    using halfspace_chart.open_C[OF chart[OF i]]
    by (auto simp: openin_open)
  have half_borel: "closed_halfspace \<in> sets borel"
    by (rule borel_closed[OF closed_closed_halfspace])
  have U_borel: "U \<in> sets borel"
    by (rule borel_open[OF U(1)])
  have chart_borel: "C i \<in> sets borel"
    unfolding U(2)
    by (rule sets.Int[OF half_borel U_borel])
  have measurable: "(\<lambda>x. indicator (C i) x *\<^sub>R f x)
      \<in> borel_measurable lborel"
    using borel_measurable_continuous_on_indicator
      [OF chart_borel continuous]
    by (simp add: sets_lborel)
  have lborel_int: "set_integrable lborel (C i) f"
    using integrable measurable
    by (simp add: absolutely_integrable_on_def
      set_integrable_def integrable_completion)
  show ?thesis
    by (rule set_borel_integral_eq_integral(2)
      [OF lborel_int])
qed

end

lemma compactin_open_compact_collar:
  assumes loc: "locally_compact_space X"
    and haus: "Hausdorff_space X"
    and compact: "compactin X K"
    and openW: "openin X W"
    and sub: "K \<subseteq> W"
  obtains V L where "openin X V" "compactin X L"
    "K \<subseteq> V" "V \<subseteq> L" "L \<subseteq> W"
proof -
  have regular: "regular_space X"
    by (rule locally_compact_Hausdorff_imp_regular_space
      [OF loc haus])
  have base: "neighbourhood_base_of (compactin X) X"
    by (rule locally_compact_imp_neighbourhood_base
      [OF loc regular])
  have witness: "\<And>p. p \<in> K \<Longrightarrow>
      \<exists>U L. openin X U \<and> compactin X L \<and>
        p \<in> U \<and> U \<subseteq> L \<and> L \<subseteq> W"
    using base openW sub by (auto simp: neighbourhood_base_of)
  obtain u l where data: "\<And>p. p \<in> K \<Longrightarrow>
      openin X (u p) \<and> compactin X (l p) \<and>
      p \<in> u p \<and> u p \<subseteq> l p \<and> l p \<subseteq> W"
    using witness by metis
  have cover: "K \<subseteq> \<Union>(u ` K)"
    using data by auto
  have open_cover: "\<And>T. T \<in> u ` K \<Longrightarrow> openin X T"
    using data by auto
  obtain F where F: "finite F" "F \<subseteq> u ` K"
    "K \<subseteq> \<Union>F"
    using compactinD[OF compact open_cover cover]
    by blast
  obtain P where P: "P \<subseteq> K" "finite P" "u ` P = F"
    using finite_subset_image[OF F(1,2)] by blast
  let ?V = "\<Union>(u ` P)"
  let ?L = "\<Union>(l ` P)"
  have openV: "openin X ?V"
    by (rule openin_Union) (use data P(1) in auto)
  have compactL: "compactin X ?L"
    by (rule compactin_Union)
       (use P data in auto)
  have KV: "K \<subseteq> ?V"
    using F(3) P(3) by simp
  have VL: "?V \<subseteq> ?L"
    using data P(1) by auto
  have LW: "?L \<subseteq> W"
    using data P(1) by auto
  show ?thesis
    by (rule that[OF openV compactL KV VL LW])
qed

lemma finite_compact_chart_refinement:
  fixes X :: "'a::topological_space topology"
    and D :: "'i \<Rightarrow> 'a set"
  assumes loc: "locally_compact_space X"
    and haus: "Hausdorff_space X"
    and compact: "compactin X K"
    and cover: "K \<subseteq> (\<Union>i\<in>I. D i)"
    and openD: "\<And>i. i \<in> I \<Longrightarrow> openin X (D i)"
  shows "\<exists>F Q. finite F \<and> F \<subseteq> I \<and>
    K \<subseteq> (\<Union>i\<in>F. Q i) \<and>
    (\<forall>i\<in>F. compactin X (Q i)) \<and>
    (\<forall>i\<in>F. Q i \<subseteq> D i)"
proof -
  have witness: "\<exists>i V L. i \<in> I \<and> openin X V \<and>
      p \<in> V \<and> compactin X L \<and> V \<subseteq> L \<and>
      L \<subseteq> D i" if p: "p \<in> K" for p
  proof -
    obtain i where i: "i \<in> I" "p \<in> D i"
      using cover p by auto
    have singleton: "compactin X {p}"
      using compactin_subset_topspace[OF compact] p
      by (intro finite_imp_compactin) auto
    obtain V L where V: "openin X V" "compactin X L"
      "{p} \<subseteq> V" "V \<subseteq> L" "L \<subseteq> D i"
      by (rule compactin_open_compact_collar
        [OF loc haus singleton openD[OF i(1)]])
         (use i(2) in auto)
    show ?thesis using i V by blast
  qed
  obtain j V L where data: "\<And>p. p \<in> K \<Longrightarrow>
      j p \<in> I \<and> openin X (V p) \<and> p \<in> V p \<and>
      compactin X (L p) \<and> V p \<subseteq> L p \<and>
      L p \<subseteq> D (j p)"
    using witness by metis
  have coverV: "K \<subseteq> \<Union>(V ` K)"
    using data by auto
  obtain T where T: "finite T" "T \<subseteq> V ` K"
      "K \<subseteq> \<Union>T"
    using compactinD[OF compact _ coverV] data
    by auto
  obtain P where P: "P \<subseteq> K" "finite P" "V ` P = T"
    using finite_subset_image[OF T(1,2)] by blast
  let ?F = "j ` P"
  let ?Q = "\<lambda>i. \<Union>p\<in>{p\<in>P. j p = i}. L p"
  have finiteF: "finite ?F" using P by simp
  have FI: "?F \<subseteq> I" using P data by auto
  have coverQ: "K \<subseteq> (\<Union>i\<in>?F. ?Q i)"
  proof
    fix x
    assume x: "x \<in> K"
    then obtain p where p: "p \<in> P" "x \<in> V p"
      using T(3) P(3) by auto
    have "x \<in> L p"
      using data[of p] P(1) p by auto
    then show "x \<in> (\<Union>i\<in>?F. ?Q i)"
      using p by blast
  qed
  have compactQ: "compactin X (?Q i)"
    if i: "i \<in> ?F" for i
    by (rule compactin_Union)
       (use P data in auto)
  have QD: "?Q i \<subseteq> D i"
    if i: "i \<in> ?F" for i
    using P data by auto
  show ?thesis
    apply (rule exI[where x="?F"])
    apply (rule exI[where x="?Q"])
    using finiteF FI coverQ compactQ QD by auto
qed

lemma finite_compact_chart_partition:
  fixes X :: "'a::topological_space set"
    and D :: "'i \<Rightarrow> 'a set"
  assumes finite: "finite F"
    and cover: "K \<subseteq> (\<Union>i\<in>F. Q i)"
    and cutoff: "\<And>i. i \<in> F \<Longrightarrow>
      \<exists>r L. continuous_on X r \<and> closed L \<and>
        {p\<in>X. r p \<noteq> (0::real)} \<subseteq> L \<and>
        L \<subseteq> D i \<and> (\<forall>p\<in>Q i. r p = 1)"
    and QX: "\<And>i. i \<in> F \<Longrightarrow> Q i \<subseteq> X"
  shows "\<exists>phi :: 'i \<Rightarrow> 'a \<Rightarrow> real.
    (\<forall>p\<in>K. (\<Sum>i\<in>F. phi i p) = 1) \<and>
    (\<forall>i\<in>F. continuous_on X (phi i)) \<and>
    (\<forall>i\<in>F. \<exists>L. closed L \<and>
      {p\<in>X. phi i p \<noteq> 0} \<subseteq> L \<and> L \<subseteq> D i)"
proof -
  let ?P = "\<lambda>i z. continuous_on X (fst z) \<and>
      closed (snd z) \<and>
      {p\<in>X. fst z p \<noteq> (0::real)} \<subseteq> snd z \<and>
      snd z \<subseteq> D i \<and>
      (\<forall>p\<in>Q i. fst z p = 1)"
  let ?h = "\<lambda>i. SOME z. ?P i z"
  let ?r = "\<lambda>i. fst (?h i)"
  let ?L = "\<lambda>i. snd (?h i)"
  have data: "\<And>i. i \<in> F \<Longrightarrow>
      continuous_on X (?r i) \<and> closed (?L i) \<and>
      {p\<in>X. ?r i p \<noteq> 0} \<subseteq> ?L i \<and>
      ?L i \<subseteq> D i \<and> (\<forall>p\<in>Q i. ?r i p = 1)"
  proof -
    fix i
    assume i: "i \<in> F"
    have "\<exists>z. ?P i z"
      using cutoff[OF i] by auto
    then show "continuous_on X (?r i) \<and>
        closed (?L i) \<and>
        {p\<in>X. ?r i p \<noteq> 0} \<subseteq> ?L i \<and>
        ?L i \<subseteq> D i \<and>
        (\<forall>p\<in>Q i. ?r i p = 1)"
      by (rule someI_ex)
  qed
  let ?w = "\<lambda>i p. max 0 (?r i p)"
  let ?R = "\<lambda>p. \<Sum>i\<in>F. ?w i p"
  let ?phi = "\<lambda>i p. ?w i p / max 1 (?R p)"
  have nonneg: "0 \<le> ?w i p" for i p by simp
  have R_pos: "1 \<le> ?R p" if p: "p \<in> K" for p
  proof -
    obtain i where i: "i \<in> F" "p \<in> Q i"
      using cover p by auto
    have wi: "?w i p = 1"
      using data[OF i(1)] i(2) by auto
    have "?w i p \<le> ?R p"
      by (rule member_le_sum[OF i(1) _ finite])
         (use nonneg in auto)
    then show ?thesis using wi by simp
  qed
  have unity: "(\<Sum>i\<in>F. ?phi i p) = 1"
    if p: "p \<in> K" for p
    using R_pos[OF p]
    by (simp add: sum_divide_distrib[symmetric])
  have contR: "continuous_on X ?R"
    by (rule continuous_intros)
       (use data in \<open>auto intro!: continuous_intros\<close>)
  have cont: "continuous_on X (?phi i)"
    if i: "i \<in> F" for i
  proof -
    have contw: "continuous_on X (?w i)"
      using data[OF i] by (auto intro!: continuous_intros)
    have contden: "continuous_on X (\<lambda>p. max 1 (?R p))"
      using contR by (auto intro!: continuous_intros)
    show ?thesis
      using contw contden
      by (auto intro!: continuous_intros)
  qed
  have support: "\<exists>T. closed T \<and>
      {p\<in>X. ?phi i p \<noteq> 0} \<subseteq> T \<and> T \<subseteq> D i"
    if i: "i \<in> F" for i
  proof -
    have "{p\<in>X. ?phi i p \<noteq> 0} \<subseteq> ?L i"
      using data[OF i] by auto
    then show ?thesis using data[OF i] by blast
  qed
  show ?thesis
    by (rule exI[where x="?phi"])
       (use unity cont support in auto)
qed

lemma compact_support_chart_partition:
  fixes X :: "'a::t2_space set"
    and D :: "'i \<Rightarrow> 'a set"
  assumes loc: "locally_compact_space (top_of_set X)"
    and haus: "Hausdorff_space (top_of_set X)"
    and compact: "compact K"
    and KX: "K \<subseteq> X"
    and cover: "K \<subseteq> (\<Union>i\<in>I. D i)"
    and openD: "\<And>i. i \<in> I \<Longrightarrow>
      openin (top_of_set X) (D i)"
    and cutoff: "\<And>i Q. i \<in> I \<Longrightarrow>
      compact Q \<Longrightarrow> Q \<subseteq> D i \<Longrightarrow>
      \<exists>r L. continuous_on X r \<and> closed L \<and>
        {p\<in>X. r p \<noteq> (0::real)} \<subseteq> L \<and>
        L \<subseteq> D i \<and> (\<forall>p\<in>Q. r p = 1)"
  obtains phi :: "'i \<Rightarrow> 'a \<Rightarrow> real" and F where
    "finite F" "F \<subseteq> I"
    "\<And>p. p \<in> K \<Longrightarrow> (\<Sum>i\<in>F. phi i p) = 1"
    "\<And>i. i \<in> F \<Longrightarrow> continuous_on X (phi i)"
    "\<And>i. i \<in> F \<Longrightarrow>
      \<exists>L. closed L \<and>
        {p\<in>X. phi i p \<noteq> 0} \<subseteq> L \<and> L \<subseteq> D i"
proof -
  have compactin: "compactin (top_of_set X) K"
    using compact KX by (simp add: compactin_subtopology)
  obtain F Q where F: "finite F" "F \<subseteq> I"
    and coverQ: "K \<subseteq> (\<Union>i\<in>F. Q i)"
    and compactQ: "\<And>i. i \<in> F \<Longrightarrow>
      compactin (top_of_set X) (Q i)"
    and QD: "\<And>i. i \<in> F \<Longrightarrow> Q i \<subseteq> D i"
    using finite_compact_chart_refinement
      [OF loc haus compactin cover openD] by blast
  have cutoffQ: "\<And>i. i \<in> F \<Longrightarrow>
      \<exists>r L. continuous_on X r \<and> closed L \<and>
        {p\<in>X. r p \<noteq> (0::real)} \<subseteq> L \<and>
        L \<subseteq> D i \<and> (\<forall>p\<in>Q i. r p = 1)"
  proof -
    fix i
    assume i: "i \<in> F"
    have iI: "i \<in> I" using F(2) i by auto
    have compact_abs: "compact (Q i)"
      using compactQ[OF i]
      by (simp add: compactin_subtopology)
    show "\<exists>r L. continuous_on X r \<and> closed L \<and>
        {p\<in>X. r p \<noteq> (0::real)} \<subseteq> L \<and>
        L \<subseteq> D i \<and> (\<forall>p\<in>Q i. r p = 1)"
      by (rule cutoff[OF iI compact_abs QD[OF i]])
  qed
  have QX: "\<And>i. i \<in> F \<Longrightarrow> Q i \<subseteq> X"
  proof -
    fix i
    assume i: "i \<in> F"
    show "Q i \<subseteq> X"
      using compactin_subset_topspace[OF compactQ[OF i]]
      by simp
  qed
  let ?P = "\<lambda>phi :: 'i \<Rightarrow> 'a \<Rightarrow> real.
    (\<forall>p\<in>K. (\<Sum>i\<in>F. phi i p) = 1) \<and>
    (\<forall>i\<in>F. continuous_on X (phi i)) \<and>
    (\<forall>i\<in>F. \<exists>L. closed L \<and>
      {p\<in>X. phi i p \<noteq> 0} \<subseteq> L \<and> L \<subseteq> D i)"
  let ?phi = "SOME phi. ?P phi"
  have ex: "\<exists>phi. ?P phi"
  proof (rule finite_compact_chart_partition)
    show "finite F" by (rule F(1))
    show "K \<subseteq> (\<Union>i\<in>F. Q i)"
      by (rule coverQ)
    show "\<And>i. i \<in> F \<Longrightarrow>
      \<exists>r L. continuous_on X r \<and> closed L \<and>
        {p\<in>X. r p \<noteq> (0::real)} \<subseteq> L \<and>
        L \<subseteq> D i \<and> (\<forall>p\<in>Q i. r p = 1)"
      by (rule cutoffQ)
    show "\<And>i. i \<in> F \<Longrightarrow> Q i \<subseteq> X"
      by (rule QX)
  qed
  have phi: "?P ?phi"
    by (rule someI_ex[OF ex])
  show thesis
    by (rule that[where phi="?phi" and F=F])
       (use F phi in auto)
qed

locale smooth_oriented_C2_halfspace_atlas =
  positively_oriented_C2_halfspace_atlas
    M I D C to_chart from_chart
  for M :: "'a::t2_space set"
    and I :: "'i set"
    and D :: "'i \<Rightarrow> 'a set"
    and C :: "'i \<Rightarrow>
      (real \<times> (real ^ 'n::finite)) set"
    and to_chart :: "'i \<Rightarrow> 'a \<Rightarrow>
      real \<times> (real ^ 'n)"
    and from_chart :: "'i \<Rightarrow>
      real \<times> (real ^ 'n) \<Rightarrow> 'a" +
  assumes smooth_interior_transition: "\<And>i j.
    i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
    Ck_on 2 (coordinate_transition i j)
      (coordinate_overlap i j \<inter> open_halfspace)"
    and positive_interior_transition: "\<And>i j x.
    i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
    x \<in> coordinate_overlap i j \<inter> open_halfspace
      \<Longrightarrow> 0 < eucl.det (frechet_derivative
        (coordinate_transition i j) (at x))"
begin

lemma boundary_carrier_Hausdorff:
  "Hausdorff_space (top_of_set boundary_carrier)"
proof (unfold Hausdorff_space_def, intro allI impI)
  fix p q
  assume pq: "p \<in> topspace (top_of_set boundary_carrier) \<and>
      q \<in> topspace (top_of_set boundary_carrier) \<and>
      p \<noteq> q"
  obtain U V where UV: "open U" "open V"
    "p \<in> U" "q \<in> V" "U \<inter> V = {}"
    using separation_t2[of p q] pq by blast
  let ?P = "boundary_carrier \<inter> U"
  let ?Q = "boundary_carrier \<inter> V"
  have openP: "openin (top_of_set boundary_carrier) ?P"
    unfolding openin_open
    by (rule exI[where x=U]) (use UV(1) in simp)
  have openQ: "openin (top_of_set boundary_carrier) ?Q"
    unfolding openin_open
    by (rule exI[where x=V]) (use UV(2) in simp)
  have pP: "p \<in> ?P" using pq UV(3) by simp
  have qQ: "q \<in> ?Q" using pq UV(4) by simp
  have disjoint: "disjnt ?P ?Q"
    using UV(5) unfolding disjnt_def by blast
  show "\<exists>P Q.
      openin (top_of_set boundary_carrier) P \<and>
      openin (top_of_set boundary_carrier) Q \<and>
      p \<in> P \<and> q \<in> Q \<and> disjnt P Q"
    by (rule exI[where x="?P"],
        rule exI[where x="?Q"])
       (intro conjI openP openQ pP qQ disjoint)
qed

lemma boundary_carrier_completely_regular:
  "completely_regular_space (top_of_set boundary_carrier)"
  by (rule locally_compact_regular_imp_completely_regular_space
    [OF boundary_carrier_locally_compact])
     (rule disjI1, rule boundary_carrier_Hausdorff)

lemma carrier_locally_compact:
  "locally_compact_space (top_of_set M)"
proof (unfold locally_compact_space_def, intro ballI)
  fix p
  assume p: "p \<in> topspace (top_of_set M)"
  obtain i where i: "i \<in> I" "p \<in> D i"
    using p cover by auto
  interpret c: halfspace_chart M "D i" "C i"
    "to_chart i" "from_chart i"
    by (rule chart[OF i(1)])
  obtain V K where V: "openin (top_of_set M) V"
    "p \<in> V" "compact K" "V \<subseteq> K"
    "K \<subseteq> D i"
    by (rule c.compact_relative_neighborhood[OF i(2)])
  have "compactin (top_of_set M) K"
    using V(3,5) domain_subset_carrier[OF i(1)]
    by (simp add: compactin_subtopology)
  then show "\<exists>U K. openin (top_of_set M) U \<and>
      compactin (top_of_set M) K \<and>
      p \<in> U \<and> U \<subseteq> K"
    using V by blast
qed

lemma carrier_Hausdorff:
  "Hausdorff_space (top_of_set M)"
proof (unfold Hausdorff_space_def, intro allI impI)
  fix p q
  assume pq: "p \<in> topspace (top_of_set M) \<and>
      q \<in> topspace (top_of_set M) \<and> p \<noteq> q"
  obtain U V where UV: "open U" "open V"
    "p \<in> U" "q \<in> V" "U \<inter> V = {}"
    using separation_t2[of p q] pq by blast
  let ?P = "M \<inter> U"
  let ?Q = "M \<inter> V"
  have openP: "openin (top_of_set M) ?P"
    unfolding openin_open
    by (rule exI[where x=U]) (use UV(1) in simp)
  have openQ: "openin (top_of_set M) ?Q"
    unfolding openin_open
    by (rule exI[where x=V]) (use UV(2) in simp)
  have pP: "p \<in> ?P" using pq UV(3) by simp
  have qQ: "q \<in> ?Q" using pq UV(4) by simp
  have disjoint: "disjnt ?P ?Q"
    using UV(5) unfolding disjnt_def by blast
  show "\<exists>P Q.
      openin (top_of_set M) P \<and>
      openin (top_of_set M) Q \<and>
      p \<in> P \<and> q \<in> Q \<and> disjnt P Q"
    by (rule exI[where x="?P"],
        rule exI[where x="?Q"])
       (intro conjI openP openQ pP qQ disjoint)
qed

lemma carrier_completely_regular:
  "completely_regular_space (top_of_set M)"
  by (rule locally_compact_regular_imp_completely_regular_space
    [OF carrier_locally_compact])
     (rule disjI1, rule carrier_Hausdorff)

lemma carrier_single_chart_cutoff:
  assumes i: "i \<in> I" and compact: "compact K"
    and Kchart: "K \<subseteq> D i"
  obtains phi :: "'a \<Rightarrow> real" and L where
    "continuous_on M phi"
    "closed L"
    "{p\<in>M. phi p \<noteq> 0} \<subseteq> L"
    "L \<subseteq> D i"
    "\<And>p. p \<in> K \<Longrightarrow> phi p = 1"
proof -
  let ?X = "top_of_set M"
  have openD: "openin ?X (D i)"
    by (rule halfspace_chart.open_D[OF chart[OF i]])
  have compactK: "compactin ?X K"
    using compact Kchart domain_subset_carrier[OF i]
    by (simp add: compactin_subtopology)
  obtain V L where V: "openin ?X V"
    and compactL: "compactin ?X L"
    and KV: "K \<subseteq> V"
    and VL: "V \<subseteq> L"
    and LD: "L \<subseteq> D i"
    by (rule compactin_open_compact_collar
      [OF carrier_locally_compact
        carrier_Hausdorff compactK openD Kchart])
  have Vsub: "V \<subseteq> M"
    using openin_subset[OF V] by simp
  have closedT: "closedin ?X (M - V)"
  proof -
    have "M - (M - V) = V"
      using Vsub by blast
    then show ?thesis
      using V by (simp add: closedin_def)
  qed
  have disj: "disjnt K (M - V)"
    using KV by (auto simp: disjnt_def)
  obtain phi :: "'a \<Rightarrow> real"
    where cont: "continuous_map ?X
        (top_of_set {0..1}) phi"
    and zero: "phi ` (M - V) \<subseteq> {0}"
    and one: "phi ` K \<subseteq> {1}"
    by (rule Urysohn_completely_regular_compact_closed
      [OF zero_le_one carrier_completely_regular
        compactK closedT disj])
  have cont_eucl: "continuous_map ?X euclidean phi"
    by (rule continuous_map_into_fulltopology[OF cont])
  have continuous: "continuous_on M phi"
    using cont_eucl by simp
  have compactL_abs: "compact L"
    using compactL by (simp add: compactin_subtopology)
  have closedL: "closed L"
    by (rule compact_imp_closed[OF compactL_abs])
  have support: "{p\<in>M. phi p \<noteq> 0} \<subseteq> L"
  proof
    fix p
    assume p: "p \<in> {p\<in>M. phi p \<noteq> 0}"
    have "p \<in> V"
      using zero p by blast
    then show "p \<in> L"
      using VL by blast
  qed
  have oneK: "\<And>p. p \<in> K \<Longrightarrow> phi p = 1"
    using one by auto
  show thesis
    using continuous closedL support LD oneK
    by (rule that[where phi=phi and L=L])
qed

lemma boundary_single_chart_cutoff:
  assumes i: "i \<in> I" and compact: "compact K"
    and Kchart: "K \<subseteq> boundary_carrier \<inter> D i"
  obtains phi :: "'a \<Rightarrow> real" and L where
    "continuous_on boundary_carrier phi"
    "closed L"
    "{p\<in>boundary_carrier. phi p \<noteq> 0} \<subseteq> L"
    "L \<subseteq> boundary_carrier \<inter> D i"
    "\<And>p. p \<in> K \<Longrightarrow> phi p = 1"
proof -
  let ?X = "top_of_set boundary_carrier"
  let ?W = "boundary_carrier \<inter> D i"
  have openD: "openin (top_of_set M) (D i)"
    by (rule halfspace_chart.open_D[OF chart[OF i]])
  have openW: "openin ?X ?W"
    using openD boundary_subset_carrier
    by (auto simp: openin_open)
  have compactK: "compactin ?X K"
    using compact Kchart
    by (simp add: compactin_subtopology)
  obtain V L where V: "openin ?X V"
    and compactL: "compactin ?X L"
    and KV: "K \<subseteq> V"
    and VL: "V \<subseteq> L"
    and LW: "L \<subseteq> ?W"
    by (rule compactin_open_compact_collar
      [OF boundary_carrier_locally_compact
        boundary_carrier_Hausdorff compactK openW Kchart])
  have Vsub: "V \<subseteq> boundary_carrier"
    using openin_subset[OF V] by simp
  have closedT: "closedin ?X (boundary_carrier - V)"
  proof -
    have "boundary_carrier - (boundary_carrier - V) = V"
      using Vsub by blast
    then show ?thesis
      using V by (simp add: closedin_def)
  qed
  have disj: "disjnt K (boundary_carrier - V)"
    using KV by (auto simp: disjnt_def)
  obtain phi :: "'a \<Rightarrow> real"
    where cont: "continuous_map ?X
        (top_of_set {0..1}) phi"
    and zero: "phi ` (boundary_carrier - V) \<subseteq> {0}"
    and one: "phi ` K \<subseteq> {1}"
    by (rule Urysohn_completely_regular_compact_closed
      [OF zero_le_one boundary_carrier_completely_regular
        compactK closedT disj])
  have cont_eucl: "continuous_map ?X euclidean phi"
    by (rule continuous_map_into_fulltopology[OF cont])
  have continuous: "continuous_on boundary_carrier phi"
    using cont_eucl by simp
  have compactL_abs: "compact L"
    using compactL by (simp add: compactin_subtopology)
  have closedL: "closed L"
    by (rule compact_imp_closed[OF compactL_abs])
  have support: "{p\<in>boundary_carrier. phi p \<noteq> 0} \<subseteq> L"
  proof
    fix p
    assume p: "p \<in> {p\<in>boundary_carrier. phi p \<noteq> 0}"
    have "p \<in> V"
      using zero p by blast
    then show "p \<in> L"
      using VL by blast
  qed
  have oneK: "\<And>p. p \<in> K \<Longrightarrow> phi p = 1"
    using one by auto
  show thesis
    using continuous closedL support LW oneK
    by (rule that[where phi=phi and L=L])
qed

theorem boundary_partition_exists:
  assumes compact: "compact K"
    and KB: "K \<subseteq> boundary_carrier"
    and support: "boundary_form_support alpha \<subseteq> K"
  shows "\<exists>phi F.
    admissible_boundary_partition alpha phi F \<and>
    (\<forall>p\<in>K. (\<Sum>i\<in>F. phi i p) = 1)"
proof -
  let ?E = "\<lambda>i. boundary_carrier \<inter> D i"
  have coverK: "K \<subseteq> (\<Union>i\<in>I. ?E i)"
    using KB cover boundary_subset_carrier by auto
  have openE: "openin (top_of_set boundary_carrier) (?E i)"
    if i: "i \<in> I" for i
    by (rule boundary_chart_domain_open[OF i])
  have cutoff: "\<exists>r L.
      continuous_on boundary_carrier r \<and> closed L \<and>
      {p\<in>boundary_carrier. r p \<noteq> (0::real)}
        \<subseteq> L \<and>
      L \<subseteq> ?E i \<and> (\<forall>p\<in>Q. r p = 1)"
    if i: "i \<in> I" and compactQ: "compact Q"
      and QD: "Q \<subseteq> ?E i" for i Q
  proof (rule boundary_single_chart_cutoff[OF i compactQ QD])
    fix r :: "'a \<Rightarrow> real" and L :: "'a set"
    assume r: "continuous_on boundary_carrier r"
      "closed L"
      "{p\<in>boundary_carrier. r p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> ?E i"
      "\<And>p. p \<in> Q \<Longrightarrow> r p = 1"
    show ?thesis
      apply (rule exI[where x=r])
      apply (rule exI[where x=L])
      using r by auto
  qed
  show ?thesis
  proof (rule compact_support_chart_partition
      [OF boundary_carrier_locally_compact
        boundary_carrier_Hausdorff compact KB
        coverK openE cutoff])
    fix phi :: "'i \<Rightarrow> 'a \<Rightarrow> real" and F
    assume F: "finite F" "F \<subseteq> I"
      and unity: "\<And>p. p \<in> K \<Longrightarrow>
        (\<Sum>i\<in>F. phi i p) = 1"
      and cont: "\<And>i. i \<in> F \<Longrightarrow>
        continuous_on boundary_carrier (phi i)"
      and local: "\<And>i. i \<in> F \<Longrightarrow>
        \<exists>L. closed L \<and>
          {p\<in>boundary_carrier. phi i p \<noteq> 0}
            \<subseteq> L \<and> L \<subseteq> ?E i"
    have part: "admissible_boundary_partition alpha phi F"
      using F unity cont local support
      by (auto simp: admissible_boundary_partition_def)
    show ?thesis
      by (rule exI[where x=phi],
          rule exI[where x=F],
          intro conjI)
         (use part unity in auto)
  qed
qed

lemma boundary_top_coeff_compatible_add:
  assumes "boundary_top_coeff_compatible alpha"
    and "boundary_top_coeff_compatible beta"
  shows "boundary_top_coeff_compatible
    (\<lambda>i y. alpha i y + beta i y)"
  using assms
  by (auto simp: boundary_top_coeff_compatible_def
    pull_top_def algebra_simps)

lemma boundary_form_support_add:
  "boundary_form_support
      (\<lambda>i y. alpha i y + beta i y)
    \<subseteq> boundary_form_support alpha \<union>
      boundary_form_support beta"
  by (auto simp: boundary_form_support_def)

theorem integral_boundary_top_add:
  assumes compatible_alpha: "boundary_top_coeff_compatible alpha"
    and compatible_beta: "boundary_top_coeff_compatible beta"
    and compact_alpha: "compact K_alpha"
    and compact_beta: "compact K_beta"
    and K_alpha: "K_alpha \<subseteq> boundary_carrier"
    and K_beta: "K_beta \<subseteq> boundary_carrier"
    and support_alpha:
      "boundary_form_support alpha \<subseteq> K_alpha"
    and support_beta:
      "boundary_form_support beta \<subseteq> K_beta"
    and cont_alpha: "\<And>i. i \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C i)) (alpha i)"
    and cont_beta: "\<And>i. i \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C i)) (beta i)"
  shows "integral_boundary_top
      (\<lambda>i y. alpha i y + beta i y) =
    integral_boundary_top alpha + integral_boundary_top beta"
proof -
  let ?gamma = "\<lambda>i y. alpha i y + beta i y"
  let ?K = "K_alpha \<union> K_beta"
  have compactK: "compact ?K"
    by (rule compact_Un[OF compact_alpha compact_beta])
  have KB: "?K \<subseteq> boundary_carrier"
    using K_alpha K_beta by auto
  have compat: "boundary_top_coeff_compatible ?gamma"
    by (rule boundary_top_coeff_compatible_add
      [OF compatible_alpha compatible_beta])
  have support: "boundary_form_support ?gamma \<subseteq> ?K"
    using boundary_form_support_add[of alpha beta]
      support_alpha support_beta by auto
  have cont: "continuous_on (halfspace_face (C i)) (?gamma i)"
    if i: "i \<in> I" for i
    using cont_alpha[OF i] cont_beta[OF i]
    by (auto intro!: continuous_intros)
  obtain phi F where partition:
      "admissible_boundary_partition ?gamma phi F"
    and unity: "\<forall>p\<in>?K. (\<Sum>i\<in>F. phi i p) = 1"
    using boundary_partition_exists[OF compactK KB support]
    by blast
  have partition_alpha:
      "admissible_boundary_partition alpha phi F"
    using partition unity support_alpha
    by (auto simp: admissible_boundary_partition_def)
  have partition_beta:
      "admissible_boundary_partition beta phi F"
    using partition unity support_beta
    by (auto simp: admissible_boundary_partition_def)
  have int_alpha: "weight_boundary_coeff (phi i) alpha i
      absolutely_integrable_on halfspace_face (C i)"
    if ii: "i \<in> F" for i
  proof -
    obtain L where L: "closed L"
      "{p\<in>boundary_carrier. phi i p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> boundary_carrier \<inter> D i"
      and cont_phi: "continuous_on boundary_carrier (phi i)"
      using partition ii
      by (auto simp: admissible_boundary_partition_def)
    have iI: "i \<in> I"
      using partition ii
      by (auto simp: admissible_boundary_partition_def)
    show ?thesis
      by (rule boundary_weight_absolutely_integrable
        [OF compatible_alpha iI compact_alpha
          support_alpha L(1,2) _ cont_phi
          cont_alpha[OF iI]])
         (use L(3) in auto)
  qed
  have int_beta: "weight_boundary_coeff (phi i) beta i
      absolutely_integrable_on halfspace_face (C i)"
    if ii: "i \<in> F" for i
  proof -
    obtain L where L: "closed L"
      "{p\<in>boundary_carrier. phi i p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> boundary_carrier \<inter> D i"
      and cont_phi: "continuous_on boundary_carrier (phi i)"
      using partition ii
      by (auto simp: admissible_boundary_partition_def)
    have iI: "i \<in> I"
      using partition ii
      by (auto simp: admissible_boundary_partition_def)
    show ?thesis
      by (rule boundary_weight_absolutely_integrable
        [OF compatible_beta iI compact_beta
          support_beta L(1,2) _ cont_phi
          cont_beta[OF iI]])
         (use L(3) in auto)
  qed
  have integral_add: "integral (halfspace_face (C i))
      (weight_boundary_coeff (phi i) ?gamma i) =
    integral (halfspace_face (C i))
      (weight_boundary_coeff (phi i) alpha i) +
    integral (halfspace_face (C i))
      (weight_boundary_coeff (phi i) beta i)"
    if ii: "i \<in> F" for i
  proof -
    have int_a: "weight_boundary_coeff (phi i) alpha i
        integrable_on halfspace_face (C i)"
      using int_alpha[OF ii]
      by (simp add: absolutely_integrable_on_def)
    have int_b: "weight_boundary_coeff (phi i) beta i
        integrable_on halfspace_face (C i)"
      using int_beta[OF ii]
      by (simp add: absolutely_integrable_on_def)
    have eq: "weight_boundary_coeff (phi i) ?gamma i =
      (\<lambda>y. weight_boundary_coeff (phi i) alpha i y +
        weight_boundary_coeff (phi i) beta i y)"
      by (rule ext)
         (simp add: weight_boundary_coeff_def algebra_simps)
    show ?thesis unfolding eq
      by (rule integral_add[OF int_a int_b])
  qed
  have split: "boundary_chart_partition_integral ?gamma phi F =
      boundary_chart_partition_integral alpha phi F +
      boundary_chart_partition_integral beta phi F"
    using integral_add
    by (simp add: boundary_chart_partition_integral_def
      sum.distrib)
  show ?thesis
    using split integral_boundary_top_eq_partition
      [OF compat compactK support cont partition]
      integral_boundary_top_eq_partition
      [OF compatible_alpha compact_alpha support_alpha
        cont_alpha partition_alpha]
      integral_boundary_top_eq_partition
      [OF compatible_beta compact_beta support_beta
        cont_beta partition_beta]
    by simp
qed

lemma boundary_top_coeff_compatible_scale:
  assumes "boundary_top_coeff_compatible alpha"
  shows "boundary_top_coeff_compatible
    (\<lambda>i y. c * alpha i y)"
  using assms
  by (auto simp: boundary_top_coeff_compatible_def
    pull_top_def algebra_simps)

lemma boundary_form_support_scale:
  "boundary_form_support (\<lambda>i y. c * alpha i y)
    \<subseteq> boundary_form_support alpha"
  by (auto simp: boundary_form_support_def)

theorem integral_boundary_top_scale:
  assumes compatible: "boundary_top_coeff_compatible alpha"
    and compact: "compact K"
    and KB: "K \<subseteq> boundary_carrier"
    and support: "boundary_form_support alpha \<subseteq> K"
    and cont: "\<And>i. i \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C i)) (alpha i)"
  shows "integral_boundary_top
    (\<lambda>i y. c * alpha i y) =
    c * integral_boundary_top alpha"
proof -
  let ?gamma = "\<lambda>i y. c * alpha i y"
  have compat_gamma: "boundary_top_coeff_compatible ?gamma"
    by (rule boundary_top_coeff_compatible_scale[OF compatible])
  have support_gamma: "boundary_form_support ?gamma \<subseteq> K"
    using boundary_form_support_scale[of c alpha] support
    by auto
  have cont_gamma:
      "continuous_on (halfspace_face (C i)) (?gamma i)"
    if i: "i \<in> I" for i
    using cont[OF i] by (auto intro!: continuous_intros)
  obtain phi F where partition:
      "admissible_boundary_partition alpha phi F"
    using boundary_partition_exists[OF compact KB support]
    by blast
  have partition_gamma:
      "admissible_boundary_partition ?gamma phi F"
    using partition boundary_form_support_scale[of c alpha]
    by (auto simp: admissible_boundary_partition_def)
  have weighted: "integral (halfspace_face (C i))
      (weight_boundary_coeff (phi i) ?gamma i) =
    c * integral (halfspace_face (C i))
      (weight_boundary_coeff (phi i) alpha i)" for i
  proof -
    have eq: "weight_boundary_coeff (phi i) ?gamma i =
      (\<lambda>y. c *\<^sub>R
        weight_boundary_coeff (phi i) alpha i y)"
      by (rule ext)
         (simp add: weight_boundary_coeff_def
           scaleR_conv_of_real algebra_simps)
    show ?thesis unfolding eq
      by (simp add: integral_cmul
        scaleR_conv_of_real)
  qed
  have split: "boundary_chart_partition_integral
      ?gamma phi F =
    c * boundary_chart_partition_integral alpha phi F"
    using weighted
    by (simp add: boundary_chart_partition_integral_def
      sum_distrib_left)
  show ?thesis
    using split integral_boundary_top_eq_partition
      [OF compat_gamma compact support_gamma
        cont_gamma partition_gamma]
      integral_boundary_top_eq_partition
      [OF compatible compact support cont partition]
    by simp
qed

theorem integral_boundary_top_compact_local_chart:
  assumes i: "i \<in> I"
    and compatible: "boundary_top_coeff_compatible alpha"
    and compact: "compact K"
    and Kchart: "K \<subseteq> boundary_carrier \<inter> D i"
    and support: "boundary_form_support alpha \<subseteq> K"
    and cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (alpha j)"
  shows "integral_boundary_top alpha =
    integral (halfspace_face (C i)) (alpha i)"
proof -
  have KB: "K \<subseteq> boundary_carrier"
    using Kchart by auto
  obtain phi F where partition:
      "admissible_boundary_partition alpha phi F"
    using boundary_partition_exists[OF compact KB support]
    by blast
  show ?thesis
    by (rule integral_boundary_top_local_chart
      [OF i compatible compact Kchart support cont partition])
qed

lemma boundary_single_chart_partition_exists:
  assumes chart_i:
    "admissible_boundary_single_chart alpha i K"
  shows "\<exists>phi F.
    admissible_boundary_partition alpha phi F"
proof -
  have i: "i \<in> I" and compact: "compact K"
    and Kchart: "K \<subseteq> boundary_carrier \<inter> D i"
    and support: "boundary_form_support alpha \<subseteq> K"
    using chart_i
    by (auto simp: admissible_boundary_single_chart_def)
  obtain phi :: "'a \<Rightarrow> real" and L
    where cont: "continuous_on boundary_carrier phi"
    and closed: "closed L"
    and nonzero: "{p\<in>boundary_carrier. phi p \<noteq> 0}
      \<subseteq> L"
    and Lchart: "L \<subseteq> boundary_carrier \<inter> D i"
    and one: "\<And>p. p \<in> K \<Longrightarrow> phi p = 1"
    using boundary_single_chart_cutoff
      [OF i compact Kchart]
    by blast
  have partition: "admissible_boundary_partition
      alpha (\<lambda>_. phi) {i}"
    using i cont closed nonzero Lchart one support
    by (auto simp: admissible_boundary_partition_def)
  show ?thesis
    using partition by blast
qed

theorem integral_boundary_single_top_eq_top_chart:
  assumes chart_i:
    "admissible_boundary_single_chart alpha i K"
    and compatible: "boundary_top_coeff_compatible alpha"
    and coeff_cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (halfspace_face (C j)) (alpha j)"
  shows "integral_boundary_single_top alpha =
    integral_boundary_top alpha"
proof -
  obtain phi F where partition:
    "admissible_boundary_partition alpha phi F"
    using boundary_single_chart_partition_exists
      [OF chart_i] by blast
  show ?thesis
    by (rule integral_boundary_single_top_eq_partition
      [OF chart_i compatible coeff_cont partition])
qed

lemma exterior_top_zero_off_near_support:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes i: "i \<in> I"
    and compact: "compact K"
    and support: "near_top_form_support A \<subseteq> K"
    and x: "x \<in> C i \<inter> open_halfspace"
    and out: "from_chart i x \<notin> K"
  shows "product_exterior_top (A i) x = 0"
proof -
  have closedK: "closed K"
    by (rule compact_imp_closed[OF compact])
  let ?V = "D i - K"
  have Vopen: "openin (top_of_set (D i)) ?V"
    using closedK
    by (auto simp: openin_open)
  let ?E = "to_chart i ` ?V"
  have Eopen: "openin (top_of_set (C i)) ?E"
    by (rule homeomorphism_imp_open_map
      [OF halfspace_chart.homeo[OF chart[OF i]]
        Vopen])
  obtain U where U: "open U" "?E = C i \<inter> U"
    using Eopen by (auto simp: openin_open)
  have Ci_open: "open (C i \<inter> open_halfspace)"
  proof -
    have overlap_eq: "coordinate_overlap i i = C i"
      using halfspace_chart.inverse_image[OF chart[OF i]]
      by (auto simp: coordinate_overlap_def)
    show ?thesis
      using body_overlap_open[OF i i]
      by (simp only: body_overlap_def overlap_eq)
  qed
  let ?W = "U \<inter> (C i \<inter> open_halfspace)"
  have Wopen: "open ?W"
    using U(1) Ci_open by auto
  have xW: "x \<in> ?W"
  proof -
    have "from_chart i x \<in> D i"
      using x halfspace_chart.inverse_image[OF chart[OF i]]
      by auto
    moreover have "to_chart i (from_chart i x) = x"
      using x halfspace_chart.from_to[OF chart[OF i]]
      by auto
    ultimately have "x \<in> ?E"
      using out by (metis DiffI image_eqI)
    then show ?thesis using U x by auto
  qed
  have zeroW: "A i q = 0" if q: "q \<in> ?W" for q
  proof (rule ccontr)
    assume nonzero: "A i q \<noteq> 0"
    have qC: "q \<in> C i" using q by auto
    have qD: "from_chart i q \<in> D i"
      using qC halfspace_chart.inverse_image[OF chart[OF i]]
      by auto
    have qout: "from_chart i q \<notin> K"
    proof -
      have "q \<in> ?E" using q U by auto
      then obtain p where p: "p \<in> D i - K"
        "q = to_chart i p"
        by auto
      have "from_chart i q = p"
        using p halfspace_chart.to_from[OF chart[OF i]]
        by auto
      then show ?thesis using p by auto
    qed
    have qM: "from_chart i q \<in> M"
      using qD domain_subset_carrier[OF i] by auto
    have "from_chart i q \<in> near_top_form_support A"
      using qM qD nonzero
        halfspace_chart.from_to[OF chart[OF i] qC] i
      by (auto simp: near_top_form_support_def)
    then show False using support qout by auto
  qed
  have deriv: "frechet_derivative (A i) (at x) =
    frechet_derivative (\<lambda>p. 0) (at x)"
    by (rule frechet_derivative_transform_within_open
      [OF Wopen xW zeroW])
  show ?thesis
    by (simp add: product_exterior_top_def deriv)
qed

lemma exterior_top_support_subset:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes compact: "compact K"
    and support: "near_top_form_support A \<subseteq> K"
    and body_coeff: "\<And>i x. i \<in> I \<Longrightarrow>
      x \<in> C i \<inter> open_halfspace \<Longrightarrow>
      body i x = product_exterior_top (A i) x"
  shows "body_form_support body \<subseteq> K"
proof
  fix p
  assume "p \<in> body_form_support body"
  then obtain i where i: "i \<in> I" "p \<in> D i"
    "body i (to_chart i p) \<noteq> 0"
    and p_int: "p \<in> interior_carrier"
    by (auto simp: body_form_support_def)
  have xC: "to_chart i p \<in> C i"
    using halfspace_chart.chart_image[OF chart[OF i(1)]]
      i(2) by auto
  have x_open: "to_chart i p \<in> open_halfspace"
    using body_interior_chart_classify[OF i(1,2)]
      p_int by (simp add: open_halfspace_def)
  have p_eq: "from_chart i (to_chart i p) = p"
    by (rule halfspace_chart.to_from
      [OF chart[OF i(1)] i(2)])
  show "p \<in> K"
  proof (rule ccontr)
    assume "p \<notin> K"
    then have out: "from_chart i (to_chart i p)
      \<notin> K"
      using p_eq by simp
    have zero: "product_exterior_top (A i)
      (to_chart i p) = 0"
      by (rule exterior_top_zero_off_near_support
        [OF i(1) compact support])
         (use xC x_open out in auto)
    show False
      using body_coeff[OF i(1)] xC x_open i(3) zero
      by auto
  qed
qed

lemma body_chart_coeff_absolutely_integrable:
  assumes i: "i \<in> I"
    and compact: "compact K"
    and K_chart: "K \<subseteq> D i"
    and support: "body_form_support body \<subseteq> K"
    and continuous: "continuous_on (C i) (body i)"
  shows "body i absolutely_integrable_on C i"
proof -
  let ?Kc = "to_chart i ` K"
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
  have coeff_cont: "continuous_on ?Kc (body i)"
    by (rule continuous_on_subset
      [OF continuous Kc_chart])
  have int_Kc: "body i absolutely_integrable_on ?Kc"
    by (rule absolutely_integrable_compact_support
      [OF Kc_compact coeff_cont subset_refl])
       simp
  have zero_interior: "body i x = 0"
    if x: "x \<in> C i \<inter> open_halfspace"
      "x \<notin> ?Kc" for x
  proof (rule ccontr)
    assume nonzero: "body i x \<noteq> 0"
    have pD: "from_chart i x \<in> D i"
      using x halfspace_chart.inverse_image
        [OF chart[OF i]] by auto
    have p_int: "from_chart i x \<in> interior_carrier"
      using body_interior_chart_classify[OF i pD]
        halfspace_chart.from_to[OF chart[OF i]]
        x by (auto simp: open_halfspace_def)
    have xeq: "to_chart i (from_chart i x) = x"
      using x halfspace_chart.from_to[OF chart[OF i]]
      by auto
    have p_supp: "from_chart i x
      \<in> body_form_support body"
      using p_int pD nonzero i xeq
      by (auto simp: body_form_support_def
        intro!: bexI[where x=i])
    have "from_chart i x \<in> K"
      using support p_supp by auto
    then have "x \<in> ?Kc"
      using xeq by (metis image_eqI)
    then show False using x by auto
  qed
  have negligible_extra: "negligible
      {x \<in> C i - ?Kc. body i x \<noteq> 0}"
  proof (rule negligible_subset
      [OF negligible_product_face])
    show "{x \<in> C i - ?Kc. body i x \<noteq> 0}
      \<subseteq> {p. fst p = 0}"
    proof
      fix x
      assume x: "x \<in> {x \<in> C i - ?Kc.
        body i x \<noteq> 0}"
      have nonnegative: "0 \<le> fst x"
        using x
          halfspace_chart.codomain_subset_halfspace
            [OF chart[OF i]]
        by (auto simp: closed_halfspace_def)
      have "\<not> 0 < fst x"
      proof
        assume pos: "0 < fst x"
        have "x \<in> C i \<inter> open_halfspace"
          using x pos by (auto simp: open_halfspace_def)
        then have "body i x = 0"
          by (rule zero_interior) (use x in auto)
        then show False using x by auto
      qed
      then show "x \<in> {p. fst p = 0}"
        using nonnegative by auto
    qed
  qed
  have negligible_reverse: "negligible
      {x \<in> ?Kc - C i. body i x \<noteq> 0}"
  proof -
    have "{x \<in> ?Kc - C i. body i x \<noteq> 0} = {}"
      using Kc_chart by auto
    then show ?thesis by (simp only: negligible_empty)
  qed
  show ?thesis
    by (rule absolutely_integrable_spike_set
      [OF int_Kc negligible_reverse negligible_extra])
qed

lemma body_transition_C2:
  assumes "i \<in> I" "j \<in> I"
  shows "Ck_on 2 (coordinate_transition i j)
    (body_overlap i j)"
  using smooth_interior_transition[OF assms]
  by (simp only: body_overlap_def)

lemma positive_body_transition:
  assumes "i \<in> I" "j \<in> I"
    "x \<in> body_overlap i j"
  shows "0 < eucl.det (frechet_derivative
    (coordinate_transition i j) (at x))"
  using positive_interior_transition[OF assms(1,2)]
    assms(3)
  by (simp only: body_overlap_def)

lemma body_transition_homeomorphism:
  assumes i: "i \<in> I" and j: "j \<in> I"
  shows "homeomorphism (body_overlap i j)
    (body_overlap j i)
    (coordinate_transition i j)
    (coordinate_transition j i)"
proof -
  have cont_ij: "continuous_on (body_overlap i j)
      (coordinate_transition i j)"
    by (rule Ck_on_imp_continuous_on
      [OF body_transition_C2[OF i j]])
  have cont_ji: "continuous_on (body_overlap j i)
      (coordinate_transition j i)"
    by (rule Ck_on_imp_continuous_on
      [OF body_transition_C2[OF j i]])
  have image_ij: "coordinate_transition i j `
      body_overlap i j = body_overlap j i"
    by (rule coordinate_transition_body_image[OF i j])
  have image_ji: "coordinate_transition j i `
      body_overlap j i = body_overlap i j"
    by (rule coordinate_transition_body_image[OF j i])
  have inv_ij: "\<And>x. x \<in> body_overlap i j \<Longrightarrow>
      coordinate_transition j i
        (coordinate_transition i j x) = x"
    by (rule coordinate_transition_inverse(2)
      [OF i j]) (simp add: body_overlap_def)
  have inv_ji: "\<And>z. z \<in> body_overlap j i \<Longrightarrow>
      coordinate_transition i j
        (coordinate_transition j i z) = z"
    by (rule coordinate_transition_inverse(2)
      [OF j i]) (simp add: body_overlap_def)
  show ?thesis
    using cont_ij cont_ji image_ij image_ji
      inv_ij inv_ji
    by (auto simp: homeomorphism_def)
qed

lemma geometric_interior_pull_eq_transition:
  fixes A :: "real \<times> (real ^ 'n)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes i: "i \<in> I" and j: "j \<in> I"
    and C2F: "Ck_on 2 F U"
    and local: "\<forall>x\<in>U \<inter> closed_halfspace.
      F x \<in> V \<and> G (F x) = x \<and>
      F x \<in> closed_halfspace \<and>
      F x = coordinate_transition i j x"
    and q: "q \<in> U \<inter> body_overlap i j"
  shows "product_pull_near_top F G A q =
    product_pull_near_top
      (coordinate_transition i j)
      (coordinate_transition j i) A q"
proof -
  let ?W = "U \<inter> body_overlap i j"
  let ?S = "coordinate_transition i j ` ?W"
  have openU: "open U"
    by (rule Ck_on_open[OF C2F])
  have openW: "open ?W"
    using openU body_overlap_open[OF i j] by auto
  have Wrel: "openin (top_of_set (body_overlap i j)) ?W"
    using openU by (auto simp: openin_open)
  have Srel: "openin (top_of_set (body_overlap j i)) ?S"
    by (rule homeomorphism_imp_open_map
      [OF body_transition_homeomorphism[OF i j] Wrel])
  have openS: "open ?S"
    using Srel body_overlap_open[OF j i]
    by (auto simp: openin_open)
  have Whalf: "?W \<subseteq> U \<inter> closed_halfspace"
    by (auto simp: body_overlap_def
      open_halfspace_def closed_halfspace_def)
  have eqF: "\<And>x. x \<in> ?W \<Longrightarrow>
      F x = coordinate_transition i j x"
    using local Whalf by blast
  have eqG: "\<And>z. z \<in> ?S \<Longrightarrow>
      G z = coordinate_transition j i z"
  proof -
    fix z
    assume z: "z \<in> ?S"
    then obtain x where xW: "x \<in> ?W"
      and zx: "z = coordinate_transition i j x"
      by blast
    have xhalf: "x \<in> U \<inter> closed_halfspace"
      using Whalf xW by auto
    have Gx: "G (F x) = x"
      using local xhalf by blast
    have xij: "x \<in> coordinate_overlap i j"
      using xW by (auto simp: body_overlap_def)
    have inverse: "coordinate_transition j i
        (coordinate_transition i j x) = x"
      by (rule coordinate_transition_inverse(2)
        [OF i j xij])
    show "G z = coordinate_transition j i z"
      using Gx inverse eqF[OF xW]
      by (simp add: zx)
  qed
  have FqS: "F q \<in> ?S"
    using q eqF[OF q] by auto
  show ?thesis
    by (rule product_pull_near_top_cong_open
      [where U="?W" and V="?S" and f=F and g=G
        and f'="coordinate_transition i j"
        and g'="coordinate_transition j i",
        OF openW q eqF openS FqS eqG])
qed

lemma geometric_face_pull_from_interior_agreement:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes i: "i \<in> I" and j: "j \<in> I"
    and y: "y \<in> boundary_overlap i j"
    and C2F: "Ck_on 2 F U"
    and xU: "(0,y) \<in> U"
    and C2G: "Ck_on 2 G V"
    and local: "\<forall>x\<in>U \<inter> closed_halfspace.
      F x \<in> V \<and> G (F x) = x \<and>
      F x \<in> closed_halfspace \<and>
      F x = coordinate_transition i j x"
    and dAi: "A i differentiable (at (0,y))"
    and dAj: "A j differentiable (at (F (0,y)))"
    and agree: "\<And>q. q \<in> U \<inter> body_overlap i j
      \<Longrightarrow> A i q =
        product_pull_near_top F G (A j) q"
  shows "A i (0,y) =
    product_pull_near_top F G (A j) (0,y)"
proof -
  let ?x = "(0,y)"
  let ?W = "U \<inter> body_overlap i j"
  have xij: "?x \<in> coordinate_overlap i j"
    by (rule boundary_in_coordinate_overlap[OF y])
  obtain W0 where W0: "open W0"
    "coordinate_overlap i j =
      closed_halfspace \<inter> W0"
    using coordinate_overlap_open[OF i j]
    by (auto simp: openin_open)
  have xO: "?x \<in> W0"
    using xij W0 by auto
  have W_eq: "?W = (U \<inter> W0) \<inter> open_halfspace"
    unfolding body_overlap_def W0(2)
    by (auto simp: closed_halfspace_def
      open_halfspace_def)
  have openU: "open U"
    by (rule Ck_on_open[OF C2F])
  have openUW: "open (U \<inter> W0)"
    using openU W0(1) by auto
  have xUW: "?x \<in> U \<inter> W0"
    using xU xO by auto
  have xclosure: "?x \<in> closure ?W"
    using face_in_closure_open_halfspace
      [OF openUW xUW]
    by (simp add: W_eq)
  have xout: "?x \<notin> ?W"
    by (auto simp: body_overlap_def
      open_halfspace_def)
  have xhalf: "?x \<in> closed_halfspace"
    by (simp add: closed_halfspace_def)
  have FV: "F ?x \<in> V"
    using local xU xhalf by blast
  have dpull: "product_pull_near_top F G (A j)
      differentiable (at ?x)"
    by (rule product_pull_near_top_differentiable_C2
      [OF C2F xU C2G FV dAj])
  have cont_Ai: "continuous (at ?x) (A i)"
    by (rule differentiable_imp_continuous_within
      [OF dAi])
  have cont_pull: "continuous (at ?x)
      (product_pull_near_top F G (A j))"
    by (rule differentiable_imp_continuous_within
      [OF dpull])
  have agreeW: "\<And>q. q \<in> ?W \<Longrightarrow>
      A i q = product_pull_near_top F G (A j) q"
    by (rule agree)
  show ?thesis
    by (rule continuous_agree_at_closure
      [OF cont_Ai cont_pull xclosure xout agreeW])
qed

theorem near_top_face_pull_compatible_from_pullback:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes pull: "\<And>i j x.
      i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
      x \<in> body_overlap i j \<Longrightarrow>
      A i x = product_pull_near_top
        (coordinate_transition i j)
        (coordinate_transition j i) (A j) x"
    and dA: "\<And>j z. j \<in> I \<Longrightarrow>
      z \<in> C j \<Longrightarrow>
      A j differentiable (at z)"
  shows "near_top_face_pull_compatible A"
proof (unfold near_top_face_pull_compatible_def,
    intro ballI allI impI)
  fix i j y U V F G
  assume i: "i \<in> I" and j: "j \<in> I"
    and y: "y \<in> boundary_overlap i j"
    and geometric: "Ck_on 2 F U \<and> (0,y) \<in> U \<and>
      Ck_on 2 G V \<and>
      (\<forall>x\<in>U \<inter> closed_halfspace.
        F x \<in> V \<and> G (F x) = x \<and>
        F x \<in> closed_halfspace \<and>
        F x = coordinate_transition i j x) \<and>
      (\<forall>x\<in>U.
        fst x = 0 \<longrightarrow> fst (F x) = 0) \<and>
      (\<forall>x\<in>V.
        fst x = 0 \<longrightarrow> fst (G x) = 0)"
  have C2F: "Ck_on 2 F U"
    and xU: "(0,y) \<in> U"
    and C2G: "Ck_on 2 G V"
    and local: "\<forall>x\<in>U \<inter> closed_halfspace.
      F x \<in> V \<and> G (F x) = x \<and>
      F x \<in> closed_halfspace \<and>
      F x = coordinate_transition i j x"
    using geometric by blast+
  have xij: "(0,y) \<in> coordinate_overlap i j"
    by (rule boundary_in_coordinate_overlap[OF y])
  have xCi: "(0,y) \<in> C i"
    using xij by (auto simp: coordinate_overlap_def)
  have Fz: "F (0,y) =
      coordinate_transition i j (0,y)"
    using local xU
    by (auto simp: closed_halfspace_def)
  have Fzj: "F (0,y) \<in> coordinate_overlap j i"
    using coordinate_transition_inverse(1)
      [OF i j xij]
    by (simp only: Fz)
  have FzC: "F (0,y) \<in> C j"
    using Fzj by (auto simp: coordinate_overlap_def)
  have agree: "\<And>q. q \<in> U \<inter> body_overlap i j
      \<Longrightarrow> A i q =
        product_pull_near_top F G (A j) q"
  proof -
    fix q
    assume q: "q \<in> U \<inter> body_overlap i j"
    have eq: "product_pull_near_top F G (A j) q =
      product_pull_near_top
        (coordinate_transition i j)
        (coordinate_transition j i) (A j) q"
      by (rule geometric_interior_pull_eq_transition
        [OF i j C2F local q])
    show "A i q = product_pull_near_top F G (A j) q"
      using pull[OF i j] q eq by auto
  qed
  show "A i (0,y) =
      product_pull_near_top F G (A j) (0,y)"
    by (rule geometric_face_pull_from_interior_agreement
      [OF i j y C2F xU C2G local
        dA[OF i xCi] dA[OF j FzC] agree])
qed

theorem exterior_top_coeff_compatible_from_pullback:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes pull: "\<And>i j x.
      i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
      x \<in> body_overlap i j \<Longrightarrow>
      A i x = product_pull_near_top
        (coordinate_transition i j)
        (coordinate_transition j i) (A j) x"
    and dA: "\<And>j z. j \<in> I \<Longrightarrow>
      z \<in> C j \<inter> open_halfspace \<Longrightarrow>
      A j differentiable (at z)"
  shows "body_top_coeff_compatible
    (\<lambda>i x. product_exterior_top (A i) x)"
proof (unfold body_top_coeff_compatible_def,
    intro ballI)
  fix i j x
  assume i: "i \<in> I" and j: "j \<in> I"
    and x: "x \<in> body_overlap i j"
  let ?f = "coordinate_transition i j"
  let ?g = "coordinate_transition j i"
  let ?W = "body_overlap i j"
  let ?Z = "body_overlap j i"
  have C2f: "Ck_on 2 ?f ?W"
    by (rule body_transition_C2[OF i j])
  have C2g: "Ck_on 2 ?g ?Z"
    by (rule body_transition_C2[OF j i])
  have openW: "open ?W"
    by (rule body_overlap_open[OF i j])
  have xH: "0 \<le> fst x"
    using x by (auto simp: body_overlap_def
      open_halfspace_def)
  have fZ: "?f x \<in> ?Z"
    by (rule coordinate_transition_body_overlap
      [OF i j x])
  have image: "\<And>q. q \<in> ?W \<Longrightarrow>
      0 \<le> fst q \<Longrightarrow> ?f q \<in> ?Z"
    by (rule coordinate_transition_body_overlap
      [OF i j])
  have inverse: "\<And>q. q \<in> ?W \<Longrightarrow>
      0 \<le> fst q \<Longrightarrow> ?g (?f q) = q"
    by (rule coordinate_transition_inverse(2)
      [OF i j])
       (auto simp: body_overlap_def)
  have dAj: "A j differentiable (at (?f x))"
    by (rule dA[OF j])
       (use fZ in
         \<open>auto simp: body_overlap_def
           coordinate_overlap_def\<close>)
  have nat: "product_exterior_top
      (product_pull_near_top ?f ?g (A j)) x =
      product_pull_top ?f
        (product_exterior_top (A j)) x"
    by (rule product_exterior_top_pull_near_top_C2_halfspace
      [OF C2f x xH C2g image inverse dAj])
  have deriv_eq: "frechet_derivative (A i) (at x) =
      frechet_derivative
        (product_pull_near_top ?f ?g (A j)) (at x)"
    by (rule frechet_derivative_transform_within_open
      [OF openW x pull[OF i j]])
  have coeff_i: "product_exterior_top (A i) x =
      product_exterior_top
        (product_pull_near_top ?f ?g (A j)) x"
    by (simp add: product_exterior_top_def deriv_eq)
  have df: "?f differentiable (at x)"
    by (metis Ck_at.simps(2) Ck_on_def Suc_1
      C2f x)
  have det: "Determinants.det
      (jacobian (cart_map_of_product ?f)
        (at (product_to_cart x))) =
      eucl.det (frechet_derivative ?f (at x))"
    by (rule product_cart_jacobian_det[OF df])
  show "product_exterior_top (A i) x =
      eucl.det (frechet_derivative ?f (at x)) *
        product_exterior_top (A j) (?f x)"
    using coeff_i nat det
    by (simp add: product_pull_top_def)
qed

corollary body_coeff_compatible_from_pullback:
  fixes A :: "'i \<Rightarrow> real \<times> (real ^ 'n)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes pull: "\<And>i j x.
      i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
      x \<in> body_overlap i j \<Longrightarrow>
      A i x = product_pull_near_top
        (coordinate_transition i j)
        (coordinate_transition j i) (A j) x"
    and dA: "\<And>j z. j \<in> I \<Longrightarrow>
      z \<in> C j \<inter> open_halfspace \<Longrightarrow>
      A j differentiable (at z)"
    and coeff: "\<And>j z. j \<in> I \<Longrightarrow>
      z \<in> C j \<inter> open_halfspace \<Longrightarrow>
      body j z = product_exterior_top (A j) z"
  shows "body_top_coeff_compatible body"
proof -
  have raw: "body_top_coeff_compatible
      (\<lambda>j z. product_exterior_top (A j) z)"
    by (rule exterior_top_coeff_compatible_from_pullback
      [OF pull dA])
  show ?thesis
  proof (unfold body_top_coeff_compatible_def,
      intro ballI)
    fix i j x
    assume i: "i \<in> I" and j: "j \<in> I"
      and x: "x \<in> body_overlap i j"
    have xC: "x \<in> C i \<inter> open_halfspace"
      using x by (auto simp: body_overlap_def
        coordinate_overlap_def)
    have fC: "coordinate_transition i j x
        \<in> C j \<inter> open_halfspace"
      using coordinate_transition_body_overlap
        [OF i j x]
      by (auto simp: body_overlap_def
        coordinate_overlap_def)
    have raw_eq: "product_exterior_top (A i) x =
        eucl.det (frechet_derivative
          (coordinate_transition i j) (at x)) *
        product_exterior_top (A j)
          (coordinate_transition i j x)"
      using raw i j x
      by (auto simp: body_top_coeff_compatible_def)
    show "body i x =
        eucl.det (frechet_derivative
          (coordinate_transition i j) (at x)) *
        body j (coordinate_transition i j x)"
      using raw_eq coeff[OF i xC] coeff[OF j fC]
      by simp
  qed
qed

theorem integral_body_single_top_chart_rule:
  assumes chart_i:
      "admissible_body_single_chart alpha i K"
    and compatible: "body_top_coeff_compatible alpha"
  shows "integral_body_single_top alpha =
    integral (C i) (alpha i)"
  by (rule integral_body_single_top_local_chart
    [OF chart_i compatible positive_body_transition
      body_transition_C2])

definition weight_body_coeff ::
    "('a \<Rightarrow> real) \<Rightarrow>
      ('i \<Rightarrow> real \<times> (real ^ 'n) \<Rightarrow> real) \<Rightarrow>
      'i \<Rightarrow> real \<times> (real ^ 'n) \<Rightarrow> real"
  where "weight_body_coeff rho alpha i x =
    rho (from_chart i x) * alpha i x"

lemma weight_body_coeff_compatible:
  assumes compatible: "body_top_coeff_compatible alpha"
  shows "body_top_coeff_compatible
    (weight_body_coeff rho alpha)"
proof (unfold body_top_coeff_compatible_def, intro ballI)
  fix i j x
  assume i: "i \<in> I" and j: "j \<in> I"
    and x: "x \<in> body_overlap i j"
  have xij: "x \<in> coordinate_overlap i j"
    using x by (simp add: body_overlap_def)
  have pj: "from_chart i x \<in> D j"
    using xij by (simp add: coordinate_overlap_def)
  have same_point: "from_chart j
      (coordinate_transition i j x) = from_chart i x"
    using halfspace_chart.to_from[OF chart[OF j] pj]
    by (simp add: coordinate_transition_def)
  have coeff: "alpha i x =
      eucl.det (frechet_derivative
        (coordinate_transition i j) (at x)) *
      alpha j (coordinate_transition i j x)"
    using compatible i j x
    by (auto simp: body_top_coeff_compatible_def)
  show "weight_body_coeff rho alpha i x =
      eucl.det (frechet_derivative
        (coordinate_transition i j) (at x)) *
      weight_body_coeff rho alpha j
        (coordinate_transition i j x)"
    using coeff same_point
    by (simp add: weight_body_coeff_def algebra_simps)
qed

lemma body_form_support_weight:
  "body_form_support (weight_body_coeff rho alpha)
    \<subseteq> body_form_support alpha \<inter>
      {p\<in>interior_carrier. rho p \<noteq> 0}"
proof
  fix p
  assume p: "p \<in> body_form_support
      (weight_body_coeff rho alpha)"
  then obtain i where i: "i \<in> I" "p \<in> D i"
    "weight_body_coeff rho alpha i
      (to_chart i p) \<noteq> 0"
    by (auto simp: body_form_support_def)
  have pint: "p \<in> interior_carrier"
    using p by (simp add: body_form_support_def)
  have pfrom: "from_chart i (to_chart i p) = p"
    by (rule halfspace_chart.to_from[OF chart[OF i(1)] i(2)])
  have nz: "rho p * alpha i (to_chart i p) \<noteq> 0"
    using i(3) pfrom
    by (simp add: weight_body_coeff_def)
  show "p \<in> body_form_support alpha \<inter>
      {p\<in>interior_carrier. rho p \<noteq> 0}"
    using pint i nz by (auto simp: body_form_support_def)
qed

lemma weight_body_coeff_continuous:
  assumes i: "i \<in> I"
    and rho_cont: "continuous_on M rho"
    and alpha_cont: "continuous_on (C i) (alpha i)"
  shows "continuous_on (C i)
    (weight_body_coeff rho alpha i)"
proof -
  have homeo: "homeomorphism (D i) (C i)
      (to_chart i) (from_chart i)"
    by (rule halfspace_chart.homeo[OF chart[OF i]])
  have inverse_cont: "continuous_on (C i) (from_chart i)"
    by (rule homeomorphism_cont2[OF homeo])
  have image: "from_chart i ` C i \<subseteq> M"
    using halfspace_chart.inverse_image[OF chart[OF i]]
      domain_subset_carrier[OF i] by auto
  have rho_chart: "continuous_on (C i)
      (\<lambda>x. rho (from_chart i x))"
    by (rule continuous_on_compose2
      [OF rho_cont inverse_cont image])
  show ?thesis
    using rho_chart alpha_cont
    by (auto simp: weight_body_coeff_def
      intro!: continuous_intros)
qed

lemma body_weight_absolutely_integrable:
  assumes compatible: "body_top_coeff_compatible alpha"
    and i: "i \<in> I"
    and compactK: "compact K"
    and supportK: "body_form_support alpha \<subseteq> K"
    and closedL: "closed L"
    and supportL: "{p\<in>M. rho p \<noteq> 0} \<subseteq> L"
    and local: "K \<inter> L \<subseteq> D i"
    and rho_cont: "continuous_on M rho"
    and alpha_cont: "continuous_on (C i) (alpha i)"
  shows "weight_body_coeff rho alpha i
    absolutely_integrable_on C i"
proof -
  have compactKL: "compact (K \<inter> L)"
    by (rule compact_Int_closed[OF compactK closedL])
  have support: "body_form_support
      (weight_body_coeff rho alpha) \<subseteq> K \<inter> L"
    using body_form_support_weight[of rho alpha]
      supportK supportL
    by (auto simp: interior_carrier_def)
  have compatible': "body_top_coeff_compatible
      (weight_body_coeff rho alpha)"
    by (rule weight_body_coeff_compatible[OF compatible])
  have cont: "continuous_on (C i)
      (weight_body_coeff rho alpha i)"
    by (rule weight_body_coeff_continuous
      [where i=i and rho=rho and alpha=alpha,
        OF i rho_cont alpha_cont])
  show ?thesis
    by (rule body_chart_coeff_absolutely_integrable
      [OF i compactKL local support cont])
qed

lemma weight_body_coeff_partition_interior:
  assumes i: "i \<in> I"
    and x: "x \<in> C i \<inter> open_halfspace"
    and compatible: "body_top_coeff_compatible alpha"
    and unity: "\<And>p. p \<in> body_form_support alpha
      \<Longrightarrow> (\<Sum>j\<in>J. psi j p) = 1"
  shows "weight_body_coeff rho alpha i x =
    (\<Sum>j\<in>J. weight_body_coeff
      (\<lambda>p. rho p * psi j p) alpha i x)"
proof -
  let ?p = "from_chart i x"
  have pD: "?p \<in> D i"
    using x halfspace_chart.inverse_image
      [OF chart[OF i]] by auto
  have xeq: "to_chart i ?p = x"
    by (rule halfspace_chart.from_to
      [OF chart[OF i]]) (use x in auto)
  have pint: "?p \<in> interior_carrier"
    using body_interior_chart_classify[OF i pD]
      xeq x
    by (auto simp: open_halfspace_def)
  show ?thesis
  proof (cases "alpha i x = 0")
    case True
    then show ?thesis
      by (simp add: weight_body_coeff_def)
  next
    case False
    have "?p \<in> body_form_support alpha"
      using body_form_support_chart
        [OF compatible positive_body_transition i]
        pint pD xeq False by auto
    then have "(\<Sum>j\<in>J. psi j ?p) = 1"
      by (rule unity)
    then show ?thesis
      by (simp add: weight_body_coeff_def
        sum_distrib_left[symmetric]
        sum_distrib_right[symmetric] algebra_simps)
  qed
qed

lemma body_chart_integral_partition:
  assumes i: "i \<in> I" and finite: "finite J"
    and compatible: "body_top_coeff_compatible alpha"
    and unity: "\<And>p. p \<in> body_form_support alpha
      \<Longrightarrow> (\<Sum>j\<in>J. psi j p) = 1"
    and integrable: "\<And>j. j \<in> J \<Longrightarrow>
      weight_body_coeff (\<lambda>p. rho p * psi j p)
        alpha i absolutely_integrable_on C i"
  shows "integral (C i) (weight_body_coeff rho alpha i) =
    (\<Sum>j\<in>J. integral (C i)
      (weight_body_coeff
        (\<lambda>p. rho p * psi j p) alpha i))"
proof -
  let ?S = "C i \<inter> open_halfspace"
  have overlap_eq: "coordinate_overlap i i = C i"
    using halfspace_chart.inverse_image[OF chart[OF i]]
    by (auto simp: coordinate_overlap_def)
  have openS: "open ?S"
    using body_overlap_open[OF i i]
    by (simp only: body_overlap_def overlap_eq)
  have measurable: "?S \<in> sets lebesgue"
    using openS
    by (metis borel_open sets_lborel sets_completionI_sets)
  have sub: "?S \<subseteq> C i" by auto
  have intS: "weight_body_coeff
      (\<lambda>p. rho p * psi j p) alpha i
      integrable_on ?S" if j: "j \<in> J" for j
  proof -
    have "weight_body_coeff
        (\<lambda>p. rho p * psi j p) alpha i
        absolutely_integrable_on ?S"
      by (rule set_integrable_subset
        [OF integrable[OF j] measurable sub])
    then show ?thesis
      by (simp add: absolutely_integrable_on_def)
  qed
  have expand: "integral ?S (weight_body_coeff rho alpha i) =
      (\<Sum>j\<in>J. integral ?S
        (weight_body_coeff
          (\<lambda>p. rho p * psi j p) alpha i))"
  proof -
    have "integral ?S (weight_body_coeff rho alpha i) =
      integral ?S (\<lambda>x. \<Sum>j\<in>J.
        weight_body_coeff
          (\<lambda>p. rho p * psi j p) alpha i x)"
      by (rule integral_cong)
         (use weight_body_coeff_partition_interior
           [OF i _ compatible unity] in auto)
    also have "\<dots> = (\<Sum>j\<in>J. integral ?S
        (weight_body_coeff
          (\<lambda>p. rho p * psi j p) alpha i))"
      by (rule integral_sum[OF finite intS])
    finally show ?thesis .
  qed
  show ?thesis
    using expand body_chart_integral_eq_interior[OF i]
    by simp
qed

lemma body_weight_chart_integral_eq:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and compatible: "body_top_coeff_compatible alpha"
    and compactK: "compact K"
    and supportK: "body_form_support alpha \<subseteq> K"
    and closedL: "closed L"
    and supportL: "{p\<in>M. rho p \<noteq> 0} \<subseteq> L"
    and local: "K \<inter> L \<subseteq> D i \<inter> D j"
    and rho_cont: "continuous_on M rho"
    and alpha_cont_j: "continuous_on (C j) (alpha j)"
  shows "integral (C i) (weight_body_coeff rho alpha i) =
    integral (C j) (weight_body_coeff rho alpha j)"
proof -
  let ?beta = "weight_body_coeff rho alpha"
  have compat: "body_top_coeff_compatible ?beta"
    by (rule weight_body_coeff_compatible[OF compatible])
  have support: "body_form_support ?beta \<subseteq> K \<inter> L"
    using body_form_support_weight[of rho alpha]
      supportK supportL
    by (auto simp: interior_carrier_def)
  have sub_i: "K \<inter> L \<subseteq> D i"
    using local by auto
  have sub_j: "K \<inter> L \<subseteq> D j"
    using local by auto
  have int_j: "?beta j absolutely_integrable_on C j"
    by (rule body_weight_absolutely_integrable
      [OF compatible j compactK supportK closedL
        supportL sub_j rho_cont alpha_cont_j])
  show ?thesis
    by (rule body_single_chart_integral_independent
      [where alpha="?beta" and K_i="K \<inter> L"
        and K_j="K \<inter> L",
        OF i j compat positive_body_transition
          body_transition_C2[OF i j]
          support sub_i support sub_j int_j])
qed

definition body_chart_partition_integral ::
    "('i \<Rightarrow> real \<times> (real ^ 'n) \<Rightarrow> real) \<Rightarrow>
      ('i \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow>
      'i set \<Rightarrow> real"
  where "body_chart_partition_integral alpha phi F =
    (\<Sum>i\<in>F. integral (C i)
      (weight_body_coeff (phi i) alpha i))"

definition admissible_body_partition ::
    "('i \<Rightarrow> real \<times> (real ^ 'n) \<Rightarrow> real) \<Rightarrow>
      ('i \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow>
      'i set \<Rightarrow> bool"
  where "admissible_body_partition alpha phi F \<longleftrightarrow>
    finite F \<and> F \<subseteq> I \<and>
    (\<forall>p\<in>body_form_support alpha.
      (\<Sum>i\<in>F. phi i p) = 1) \<and>
    (\<forall>i\<in>F.
      continuous_on M (phi i) \<and>
      (\<exists>L. closed L \<and>
        {p\<in>M. phi i p \<noteq> 0} \<subseteq> L \<and>
        L \<subseteq> D i))"

theorem body_partition_exists:
  assumes compact: "compact K"
    and KM: "K \<subseteq> M"
    and support: "body_form_support alpha \<subseteq> K"
  shows "\<exists>phi F. admissible_body_partition alpha phi F \<and>
    (\<forall>p\<in>K. (\<Sum>i\<in>F. phi i p) = 1)"
proof -
  have coverK: "K \<subseteq> (\<Union>i\<in>I. D i)"
    using KM cover by auto
  have openD: "openin (top_of_set M) (D i)"
    if i: "i \<in> I" for i
    by (rule halfspace_chart.open_D[OF chart[OF i]])
  have cutoff: "\<exists>r L.
      continuous_on M r \<and> closed L \<and>
      {p\<in>M. r p \<noteq> (0::real)} \<subseteq> L \<and>
      L \<subseteq> D i \<and> (\<forall>p\<in>Q. r p = 1)"
    if i: "i \<in> I" and compactQ: "compact Q"
      and QD: "Q \<subseteq> D i" for i Q
  proof (rule carrier_single_chart_cutoff[OF i compactQ QD])
    fix r :: "'a \<Rightarrow> real" and L :: "'a set"
    assume r: "continuous_on M r" "closed L"
      "{p\<in>M. r p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> D i"
      "\<And>p. p \<in> Q \<Longrightarrow> r p = 1"
    show ?thesis
      apply (rule exI[where x=r])
      apply (rule exI[where x=L])
      using r by auto
  qed
  show ?thesis
  proof (rule compact_support_chart_partition
      [OF carrier_locally_compact carrier_Hausdorff
        compact KM coverK openD cutoff])
    fix phi :: "'i \<Rightarrow> 'a \<Rightarrow> real" and F
    assume F: "finite F" "F \<subseteq> I"
      and unity: "\<And>p. p \<in> K \<Longrightarrow>
        (\<Sum>i\<in>F. phi i p) = 1"
      and cont: "\<And>i. i \<in> F \<Longrightarrow>
        continuous_on M (phi i)"
      and local: "\<And>i. i \<in> F \<Longrightarrow>
        \<exists>L. closed L \<and>
          {p\<in>M. phi i p \<noteq> 0} \<subseteq> L \<and>
          L \<subseteq> D i"
    have part: "admissible_body_partition alpha phi F"
      using F unity cont local support
      by (auto simp: admissible_body_partition_def)
    show ?thesis
      by (rule exI[where x=phi],
          rule exI[where x=F],
          intro conjI)
         (use part unity in auto)
  qed
qed

theorem body_partition_integral_independent_admissible:
  assumes compatible: "body_top_coeff_compatible alpha"
    and compact: "compact K"
    and support: "body_form_support alpha \<subseteq> K"
    and coeff_cont: "\<And>i. i \<in> I \<Longrightarrow>
      continuous_on (C i) (alpha i)"
    and phi: "admissible_body_partition alpha phi F"
    and psi: "admissible_body_partition alpha psi G"
  shows "body_chart_partition_integral alpha phi F =
    body_chart_partition_integral alpha psi G"
proof -
  have finiteF: "finite F" and finiteG: "finite G"
    and FI: "F \<subseteq> I" and GI: "G \<subseteq> I"
    and unityF: "\<And>p. p \<in> body_form_support alpha
      \<Longrightarrow> (\<Sum>i\<in>F. phi i p) = 1"
    and unityG: "\<And>p. p \<in> body_form_support alpha
      \<Longrightarrow> (\<Sum>j\<in>G. psi j p) = 1"
    using phi psi by (auto simp: admissible_body_partition_def)
  have local: "integral (C i)
      (weight_body_coeff
        (\<lambda>p. phi i p * psi j p) alpha i) =
    integral (C j)
      (weight_body_coeff
        (\<lambda>p. phi i p * psi j p) alpha j)"
    and int_i: "weight_body_coeff
        (\<lambda>p. phi i p * psi j p) alpha i
        absolutely_integrable_on C i"
    and int_j: "weight_body_coeff
        (\<lambda>p. phi i p * psi j p) alpha j
        absolutely_integrable_on C j"
    if ii: "i \<in> F" and jj: "j \<in> G" for i j
  proof -
    obtain L where L: "closed L"
      "{p\<in>M. phi i p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> D i"
      and cont_phi: "continuous_on M (phi i)"
      using phi ii
      by (auto simp: admissible_body_partition_def)
    obtain N where N: "closed N"
      "{p\<in>M. psi j p \<noteq> 0} \<subseteq> N"
      "N \<subseteq> D j"
      and cont_psi: "continuous_on M (psi j)"
      using psi jj
      by (auto simp: admissible_body_partition_def)
    have iI: "i \<in> I" and jI: "j \<in> I"
      using FI GI ii jj by auto
    have closedLN: "closed (L \<inter> N)"
      by (rule closed_Int[OF L(1) N(1)])
    have supportLN: "{p\<in>M.
        phi i p * psi j p \<noteq> 0} \<subseteq> L \<inter> N"
      using L(2) N(2) by auto
    have localLN: "K \<inter> (L \<inter> N) \<subseteq> D i \<inter> D j"
      using L(3) N(3) by auto
    have cont: "continuous_on M
        (\<lambda>p. phi i p * psi j p)"
      using cont_phi cont_psi
      by (auto intro!: continuous_intros)
    show "integral (C i)
        (weight_body_coeff
          (\<lambda>p. phi i p * psi j p) alpha i) =
      integral (C j)
        (weight_body_coeff
          (\<lambda>p. phi i p * psi j p) alpha j)"
      by (rule body_weight_chart_integral_eq
        [OF iI jI compatible compact support
          closedLN supportLN localLN cont coeff_cont[OF jI]])
    show "weight_body_coeff
        (\<lambda>p. phi i p * psi j p) alpha i
        absolutely_integrable_on C i"
      by (rule body_weight_absolutely_integrable
        [OF compatible iI compact support closedLN
          supportLN _ cont coeff_cont[OF iI]])
         (use localLN in auto)
    show "weight_body_coeff
        (\<lambda>p. phi i p * psi j p) alpha j
        absolutely_integrable_on C j"
      by (rule body_weight_absolutely_integrable
        [OF compatible jI compact support closedLN
          supportLN _ cont coeff_cont[OF jI]])
         (use localLN in auto)
  qed
  have intF: "weight_body_coeff
      (\<lambda>p. phi i p * psi j p) alpha i
      absolutely_integrable_on C i"
    if "i \<in> F" "j \<in> G" for i j
    by (rule int_i[OF that])
  have intG: "weight_body_coeff
      (\<lambda>p. psi j p * phi i p) alpha j
      absolutely_integrable_on C j"
    if "i \<in> F" "j \<in> G" for i j
    using int_j[OF that]
    by (simp add: weight_body_coeff_def mult.commute)
  have left: "body_chart_partition_integral alpha phi F =
    (\<Sum>i\<in>F. \<Sum>j\<in>G.
      integral (C i)
        (weight_body_coeff
          (\<lambda>p. phi i p * psi j p) alpha i))"
    unfolding body_chart_partition_integral_def
    by (rule sum.cong[OF refl])
       (use FI finiteG compatible unityG intF in
        \<open>auto intro: body_chart_integral_partition\<close>)
  have right: "body_chart_partition_integral alpha psi G =
    (\<Sum>j\<in>G. \<Sum>i\<in>F.
      integral (C j)
        (weight_body_coeff
          (\<lambda>p. phi i p * psi j p) alpha j))"
  proof -
    have "body_chart_partition_integral alpha psi G =
      (\<Sum>j\<in>G. \<Sum>i\<in>F.
        integral (C j)
          (weight_body_coeff
            (\<lambda>p. psi j p * phi i p) alpha j))"
      unfolding body_chart_partition_integral_def
      by (rule sum.cong[OF refl])
         (use GI finiteF compatible unityF intG in
          \<open>auto intro: body_chart_integral_partition\<close>)
    also have "\<dots> =
      (\<Sum>j\<in>G. \<Sum>i\<in>F.
        integral (C j)
          (weight_body_coeff
            (\<lambda>p. phi i p * psi j p) alpha j))"
      by (simp add: weight_body_coeff_def mult.commute)
    finally show ?thesis .
  qed
  have "(\<Sum>i\<in>F. \<Sum>j\<in>G.
      integral (C i)
        (weight_body_coeff
          (\<lambda>p. phi i p * psi j p) alpha i)) =
    (\<Sum>i\<in>F. \<Sum>j\<in>G.
      integral (C j)
        (weight_body_coeff
          (\<lambda>p. phi i p * psi j p) alpha j))"
    by (rule sum.cong[OF refl], rule sum.cong[OF refl])
       (use local in auto)
  also have "\<dots> =
    (\<Sum>j\<in>G. \<Sum>i\<in>F.
      integral (C j)
        (weight_body_coeff
          (\<lambda>p. phi i p * psi j p) alpha j))"
    by (rule sum.swap)
  finally show ?thesis using left right by simp
qed

definition integral_body_top ::
    "('i \<Rightarrow> real \<times> (real ^ 'n) \<Rightarrow> real)
      \<Rightarrow> real"
  where "integral_body_top alpha =
    (SOME z. \<exists>phi F.
      admissible_body_partition alpha phi F \<and>
      z = body_chart_partition_integral alpha phi F)"

theorem integral_body_top_eq_partition:
  assumes compatible: "body_top_coeff_compatible alpha"
    and compact: "compact K"
    and support: "body_form_support alpha \<subseteq> K"
    and coeff_cont: "\<And>i. i \<in> I \<Longrightarrow>
      continuous_on (C i) (alpha i)"
    and partition: "admissible_body_partition alpha phi F"
  shows "integral_body_top alpha =
    body_chart_partition_integral alpha phi F"
proof -
  let ?P = "\<lambda>z. \<exists>psi G.
    admissible_body_partition alpha psi G \<and>
    z = body_chart_partition_integral alpha psi G"
  have ex: "\<exists>z. ?P z" using partition by blast
  have "?P (SOME z. ?P z)"
    by (rule someI_ex[OF ex])
  then obtain psi G where psi:
      "admissible_body_partition alpha psi G"
    and eq: "(SOME z. ?P z) =
      body_chart_partition_integral alpha psi G"
    by blast
  show ?thesis
    unfolding integral_body_top_def
    using eq body_partition_integral_independent_admissible
      [OF compatible compact support coeff_cont psi partition]
    by simp
qed

lemma body_top_coeff_compatible_add:
  assumes "body_top_coeff_compatible alpha"
    and "body_top_coeff_compatible beta"
  shows "body_top_coeff_compatible
    (\<lambda>i x. alpha i x + beta i x)"
  using assms
  by (auto simp: body_top_coeff_compatible_def
    algebra_simps)

lemma body_form_support_add:
  "body_form_support
      (\<lambda>i x. alpha i x + beta i x)
    \<subseteq> body_form_support alpha \<union>
      body_form_support beta"
  by (auto simp: body_form_support_def)

theorem integral_body_top_add:
  assumes compatible_alpha: "body_top_coeff_compatible alpha"
    and compatible_beta: "body_top_coeff_compatible beta"
    and compact_alpha: "compact K_alpha"
    and compact_beta: "compact K_beta"
    and K_alpha: "K_alpha \<subseteq> M"
    and K_beta: "K_beta \<subseteq> M"
    and support_alpha: "body_form_support alpha \<subseteq> K_alpha"
    and support_beta: "body_form_support beta \<subseteq> K_beta"
    and cont_alpha: "\<And>i. i \<in> I \<Longrightarrow>
      continuous_on (C i) (alpha i)"
    and cont_beta: "\<And>i. i \<in> I \<Longrightarrow>
      continuous_on (C i) (beta i)"
  shows "integral_body_top
      (\<lambda>i x. alpha i x + beta i x) =
    integral_body_top alpha + integral_body_top beta"
proof -
  let ?gamma = "\<lambda>i x. alpha i x + beta i x"
  let ?K = "K_alpha \<union> K_beta"
  have compactK: "compact ?K"
    by (rule compact_Un[OF compact_alpha compact_beta])
  have KM: "?K \<subseteq> M"
    using K_alpha K_beta by auto
  have compat: "body_top_coeff_compatible ?gamma"
    by (rule body_top_coeff_compatible_add
      [OF compatible_alpha compatible_beta])
  have support: "body_form_support ?gamma \<subseteq> ?K"
    using body_form_support_add[of alpha beta]
      support_alpha support_beta by auto
  have cont: "continuous_on (C i) (?gamma i)"
    if i: "i \<in> I" for i
    using cont_alpha[OF i] cont_beta[OF i]
    by (auto intro!: continuous_intros)
  obtain phi F where partition:
      "admissible_body_partition ?gamma phi F"
    and unity: "\<forall>p\<in>?K. (\<Sum>i\<in>F. phi i p) = 1"
    using body_partition_exists[OF compactK KM support]
    by blast
  have partition_alpha:
      "admissible_body_partition alpha phi F"
    using partition unity support_alpha
    by (auto simp: admissible_body_partition_def)
  have partition_beta:
      "admissible_body_partition beta phi F"
    using partition unity support_beta
    by (auto simp: admissible_body_partition_def)
  have int_alpha: "weight_body_coeff (phi i) alpha i
      absolutely_integrable_on C i"
    if ii: "i \<in> F" for i
  proof -
    obtain L where L: "closed L"
      "{p\<in>M. phi i p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> D i"
      and cont_phi: "continuous_on M (phi i)"
      using partition ii
      by (auto simp: admissible_body_partition_def)
    have iI: "i \<in> I"
      using partition ii
      by (auto simp: admissible_body_partition_def)
    show ?thesis
      by (rule body_weight_absolutely_integrable
        [OF compatible_alpha iI compact_alpha
          support_alpha L(1,2) _ cont_phi
          cont_alpha[OF iI]])
         (use L(3) in auto)
  qed
  have int_beta: "weight_body_coeff (phi i) beta i
      absolutely_integrable_on C i"
    if ii: "i \<in> F" for i
  proof -
    obtain L where L: "closed L"
      "{p\<in>M. phi i p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> D i"
      and cont_phi: "continuous_on M (phi i)"
      using partition ii
      by (auto simp: admissible_body_partition_def)
    have iI: "i \<in> I"
      using partition ii
      by (auto simp: admissible_body_partition_def)
    show ?thesis
      by (rule body_weight_absolutely_integrable
        [OF compatible_beta iI compact_beta
          support_beta L(1,2) _ cont_phi
          cont_beta[OF iI]])
         (use L(3) in auto)
  qed
  have integral_add: "integral (C i)
      (weight_body_coeff (phi i) ?gamma i) =
    integral (C i) (weight_body_coeff (phi i) alpha i) +
    integral (C i) (weight_body_coeff (phi i) beta i)"
    if ii: "i \<in> F" for i
  proof -
    have int_a: "weight_body_coeff (phi i) alpha i
        integrable_on C i"
      using int_alpha[OF ii]
      by (simp add: absolutely_integrable_on_def)
    have int_b: "weight_body_coeff (phi i) beta i
        integrable_on C i"
      using int_beta[OF ii]
      by (simp add: absolutely_integrable_on_def)
    have eq: "weight_body_coeff (phi i) ?gamma i =
      (\<lambda>x. weight_body_coeff (phi i) alpha i x +
        weight_body_coeff (phi i) beta i x)"
      by (rule ext)
         (simp add: weight_body_coeff_def algebra_simps)
    show ?thesis unfolding eq
      by (rule integral_add[OF int_a int_b])
  qed
  have split: "body_chart_partition_integral ?gamma phi F =
      body_chart_partition_integral alpha phi F +
      body_chart_partition_integral beta phi F"
    using integral_add
    by (simp add: body_chart_partition_integral_def
      sum.distrib)
  show ?thesis
    using split integral_body_top_eq_partition
      [OF compat compactK support cont partition]
      integral_body_top_eq_partition
      [OF compatible_alpha compact_alpha support_alpha
        cont_alpha partition_alpha]
      integral_body_top_eq_partition
      [OF compatible_beta compact_beta support_beta
        cont_beta partition_beta]
    by simp
qed

lemma body_top_coeff_compatible_scale:
  assumes "body_top_coeff_compatible alpha"
  shows "body_top_coeff_compatible
    (\<lambda>i x. c * alpha i x)"
  using assms
  by (auto simp: body_top_coeff_compatible_def
    algebra_simps)

lemma body_form_support_scale:
  "body_form_support (\<lambda>i x. c * alpha i x)
    \<subseteq> body_form_support alpha"
  by (auto simp: body_form_support_def)

theorem integral_body_top_scale:
  assumes compatible: "body_top_coeff_compatible alpha"
    and compact: "compact K"
    and KM: "K \<subseteq> M"
    and support: "body_form_support alpha \<subseteq> K"
    and cont: "\<And>i. i \<in> I \<Longrightarrow>
      continuous_on (C i) (alpha i)"
  shows "integral_body_top
    (\<lambda>i x. c * alpha i x) =
    c * integral_body_top alpha"
proof -
  let ?gamma = "\<lambda>i x. c * alpha i x"
  have compat_gamma: "body_top_coeff_compatible ?gamma"
    by (rule body_top_coeff_compatible_scale[OF compatible])
  have support_gamma: "body_form_support ?gamma \<subseteq> K"
    using body_form_support_scale[of c alpha] support
    by auto
  have cont_gamma: "continuous_on (C i) (?gamma i)"
    if i: "i \<in> I" for i
    using cont[OF i] by (auto intro!: continuous_intros)
  obtain phi F where partition:
      "admissible_body_partition alpha phi F"
    using body_partition_exists[OF compact KM support]
    by blast
  have partition_gamma:
      "admissible_body_partition ?gamma phi F"
    using partition body_form_support_scale[of c alpha]
    by (auto simp: admissible_body_partition_def)
  have weighted: "integral (C i)
      (weight_body_coeff (phi i) ?gamma i) =
    c * integral (C i)
      (weight_body_coeff (phi i) alpha i)" for i
  proof -
    have eq: "weight_body_coeff (phi i) ?gamma i =
      (\<lambda>x. c *\<^sub>R
        weight_body_coeff (phi i) alpha i x)"
      by (rule ext)
         (simp add: weight_body_coeff_def
           scaleR_conv_of_real algebra_simps)
    show ?thesis unfolding eq
      by (simp add: integral_cmul
        scaleR_conv_of_real)
  qed
  have split: "body_chart_partition_integral
      ?gamma phi F =
    c * body_chart_partition_integral alpha phi F"
    using weighted
    by (simp add: body_chart_partition_integral_def
      sum_distrib_left)
  show ?thesis
    using split integral_body_top_eq_partition
      [OF compat_gamma compact support_gamma
        cont_gamma partition_gamma]
      integral_body_top_eq_partition
      [OF compatible compact support cont partition]
    by simp
qed

lemma integral_body_top_zero_coeff:
  "integral_body_top (\<lambda>i x. 0) = 0"
proof -
  have compatible: "body_top_coeff_compatible
      (\<lambda>i x. 0)"
    by (simp add: body_top_coeff_compatible_def)
  have support: "body_form_support
      (\<lambda>i x. 0) \<subseteq> {}"
    by (simp add: body_form_support_def)
  have cont: "\<And>i. i \<in> I \<Longrightarrow>
      continuous_on (C i) ((\<lambda>i x. 0) i)"
    by (intro continuous_intros)
  have partition: "admissible_body_partition
      (\<lambda>i x. 0) (\<lambda>i p. 0) {}"
    by (simp add: admissible_body_partition_def
      body_form_support_def)
  have "integral_body_top (\<lambda>i x. 0) =
    body_chart_partition_integral
      (\<lambda>i x. 0) (\<lambda>i p. 0) {}"
    by (rule integral_body_top_eq_partition
      [OF compatible compact_empty support cont partition])
  then show ?thesis
    by (simp add: body_chart_partition_integral_def)
qed

lemma body_single_chart_partition_exists:
  assumes chart_i: "admissible_body_single_chart alpha i K"
  shows "\<exists>phi F. admissible_body_partition alpha phi F"
proof -
  have i: "i \<in> I" and compact: "compact K"
    and Kchart: "K \<subseteq> D i"
    and support: "body_form_support alpha \<subseteq> K"
    using chart_i
    by (auto simp: admissible_body_single_chart_def)
  obtain phi :: "'a \<Rightarrow> real" and L
    where cont: "continuous_on M phi"
    and closed: "closed L"
    and nonzero: "{p\<in>M. phi p \<noteq> 0} \<subseteq> L"
    and Lchart: "L \<subseteq> D i"
    and one: "\<And>p. p \<in> K \<Longrightarrow> phi p = 1"
    using carrier_single_chart_cutoff
      [OF i compact Kchart]
    by blast
  have partition: "admissible_body_partition
      alpha (\<lambda>_. phi) {i}"
    using i cont closed nonzero Lchart one support
    by (auto simp: admissible_body_partition_def)
  show ?thesis using partition by blast
qed

theorem body_partition_integral_local_chart:
  assumes i: "i \<in> I"
    and compatible: "body_top_coeff_compatible alpha"
    and compact: "compact K"
    and Kchart: "K \<subseteq> D i"
    and support: "body_form_support alpha \<subseteq> K"
    and coeff_cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (C j) (alpha j)"
    and partition: "admissible_body_partition alpha phi F"
  shows "body_chart_partition_integral alpha phi F =
    integral (C i) (alpha i)"
proof -
  have finite: "finite F"
    and FI: "F \<subseteq> I"
    and unity: "\<And>p. p \<in> body_form_support alpha
      \<Longrightarrow> (\<Sum>j\<in>F. phi j p) = 1"
    using partition
    by (auto simp: admissible_body_partition_def)
  have int_i: "weight_body_coeff (phi j) alpha i
      absolutely_integrable_on C i"
    if jj: "j \<in> F" for j
  proof -
    obtain L where L: "closed L"
      "{p\<in>M. phi j p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> D j"
      and cont: "continuous_on M (phi j)"
      using partition jj
      by (auto simp: admissible_body_partition_def)
    have local: "K \<inter> L \<subseteq> D i"
      using Kchart by auto
    show ?thesis
      by (rule body_weight_absolutely_integrable
        [OF compatible i compact support L(1,2)
          local cont coeff_cont[OF i]])
  qed
  have local: "integral (C j)
      (weight_body_coeff (phi j) alpha j) =
    integral (C i)
      (weight_body_coeff (phi j) alpha i)"
    if jj: "j \<in> F" for j
  proof -
    obtain L where L: "closed L"
      "{p\<in>M. phi j p \<noteq> 0} \<subseteq> L"
      "L \<subseteq> D j"
      and cont: "continuous_on M (phi j)"
      using partition jj
      by (auto simp: admissible_body_partition_def)
    have j: "j \<in> I"
      using FI jj by auto
    have local: "K \<inter> L \<subseteq> D i \<inter> D j"
      using Kchart L(3) by auto
    have eq: "integral (C i)
        (weight_body_coeff (phi j) alpha i) =
      integral (C j)
        (weight_body_coeff (phi j) alpha j)"
      by (rule body_weight_chart_integral_eq
        [OF i j compatible compact support L(1,2)
          local cont coeff_cont[OF j]])
    show ?thesis using eq by simp
  qed
  have integrable: "weight_body_coeff
      (\<lambda>p. (1::real) * phi j p) alpha i
      absolutely_integrable_on C i"
    if jj: "j \<in> F" for j
    using int_i[OF jj] by simp
  have one_eq: "weight_body_coeff (\<lambda>_. 1) alpha i =
      alpha i"
    by (rule ext) (simp add: weight_body_coeff_def)
  have weight_eq: "weight_body_coeff
      (\<lambda>p. (1::real) * phi j p) alpha i =
      weight_body_coeff (phi j) alpha i" for j
    by (rule ext) (simp add: weight_body_coeff_def)
  have expansion: "integral (C i) (alpha i) =
    (\<Sum>j\<in>F. integral (C i)
      (weight_body_coeff (phi j) alpha i))"
    using body_chart_integral_partition
      [where rho="\<lambda>_. 1",
        OF i finite compatible unity integrable]
    by (simp add: one_eq weight_eq)
  have partition_eq:
    "body_chart_partition_integral alpha phi F =
      (\<Sum>j\<in>F. integral (C i)
        (weight_body_coeff (phi j) alpha i))"
    unfolding body_chart_partition_integral_def
    by (rule sum.cong[OF refl])
       (use local in simp)
  show ?thesis using partition_eq expansion by simp
qed

theorem integral_body_top_local_chart:
  assumes chart_i:
    "admissible_body_single_chart alpha i K"
    and compatible: "body_top_coeff_compatible alpha"
    and coeff_cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (C j) (alpha j)"
  shows "integral_body_top alpha =
    integral (C i) (alpha i)"
proof -
  have i: "i \<in> I" and compact: "compact K"
    and Kchart: "K \<subseteq> D i"
    and support: "body_form_support alpha \<subseteq> K"
    using chart_i
    by (auto simp: admissible_body_single_chart_def)
  let ?P = "\<lambda>z. \<exists>phi F.
      admissible_body_partition alpha phi F \<and>
      z = body_chart_partition_integral alpha phi F"
  obtain phi F where partition:
    "admissible_body_partition alpha phi F"
    using body_single_chart_partition_exists[OF chart_i]
    by blast
  have ex: "\<exists>z. ?P z"
    using partition by blast
  have some: "?P (SOME z. ?P z)"
    by (rule someI_ex[OF ex])
  then obtain psi G where psi:
      "admissible_body_partition alpha psi G"
    and eq: "(SOME z. ?P z) =
      body_chart_partition_integral alpha psi G"
    by blast
  have chart_eq: "body_chart_partition_integral
      alpha psi G = integral (C i) (alpha i)"
    by (rule body_partition_integral_local_chart
      [OF i compatible compact Kchart support
        coeff_cont psi])
  show ?thesis
    unfolding integral_body_top_def
    using eq chart_eq by simp
qed

theorem integral_body_single_top_eq_top_chart:
  assumes chart_i:
    "admissible_body_single_chart alpha i K"
    and compatible: "body_top_coeff_compatible alpha"
    and coeff_cont: "\<And>j. j \<in> I \<Longrightarrow>
      continuous_on (C j) (alpha j)"
  shows "integral_body_single_top alpha =
    integral_body_top alpha"
proof -
  have single: "integral_body_single_top alpha =
      integral (C i) (alpha i)"
    by (rule integral_body_single_top_chart_rule
      [OF chart_i compatible])
  have global: "integral_body_top alpha =
      integral (C i) (alpha i)"
    by (rule integral_body_top_local_chart
      [OF chart_i compatible coeff_cont])
  show ?thesis using single global by simp
qed

end

end
