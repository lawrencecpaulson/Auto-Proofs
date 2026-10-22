theory Stokes_Boundary_Charts
  imports Stokes_Block_Determinant
begin

definition closed_halfspace ::
    "(real \<times> 'e::euclidean_space) set"
  where "closed_halfspace = {p. 0 \<le> fst p}"

definition open_halfspace ::
    "(real \<times> 'e::euclidean_space) set"
  where "open_halfspace = {p. 0 < fst p}"

definition halfspace_face ::
    "(real \<times> 'e::euclidean_space) set \<Rightarrow> 'e set"
  where "halfspace_face C = {y. (0,y) \<in> C}"

lemma closed_halfspace_product:
  "(closed_halfspace :: (real \<times> 'e::euclidean_space) set) =
    {0..} \<times> UNIV"
  by (auto simp: closed_halfspace_def)

lemma closed_closed_halfspace:
  "closed (closed_halfspace :: (real \<times> 'e::euclidean_space) set)"
  unfolding closed_halfspace_def
  by (intro closed_Collect_le continuous_intros)

lemma open_open_halfspace:
  "open (open_halfspace :: (real \<times> 'e::euclidean_space) set)"
  unfolding open_halfspace_def
  by (intro open_Collect_less continuous_intros)

lemma openin_open_halfspace:
  "openin (top_of_set (closed_halfspace ::
      (real \<times> 'e::euclidean_space) set)) open_halfspace"
  using open_open_halfspace
  by (auto simp: openin_open open_halfspace_def
    closed_halfspace_def)

lemma halfspace_face_open:
  fixes C :: "(real \<times> 'e::euclidean_space) set"
  assumes C: "openin (top_of_set closed_halfspace) C"
  shows "open (halfspace_face C)"
proof -
  obtain U where U: "open U" "C = closed_halfspace \<inter> U"
    using C by (auto simp: openin_open)
  have cont: "continuous_on UNIV
      (\<lambda>y::'e. (0::real,y))"
    by (intro continuous_intros)
  have "halfspace_face C =
    (\<lambda>y::'e. (0::real,y)) -` U"
    using U by (auto simp: halfspace_face_def
      closed_halfspace_def)
  then show ?thesis
    using U(1) cont
    by (auto intro: open_vimage)
qed

lemma Ck_on_face_restriction:
  fixes F :: "(real \<times> 'e::euclidean_space) \<Rightarrow>
    (real \<times> 'e)"
  assumes C2: "Ck_on 2 F U"
  shows "Ck_on 2
    (\<lambda>y. snd (F (0,y)))
    (halfspace_face U)"
proof -
  have openU: "open U"
    by (rule Ck_on_open[OF C2])
  have open_face: "open (halfspace_face U)"
  proof -
    have cont: "continuous_on UNIV
        (\<lambda>y::'e. (0::real,y))"
      by (intro continuous_intros)
    have "halfspace_face U =
      (\<lambda>y::'e. (0::real,y)) -` U"
      by (auto simp: halfspace_face_def)
    then show ?thesis
      using openU cont by (auto intro: open_vimage)
  qed
  have pair_linear: "bounded_linear
      (\<lambda>y::'e. (0::real,y))"
    by (simp add: linear_conv_bounded_linear[symmetric])
       (rule linearI, auto)
  have pair_C2: "Ck_on 2
      (\<lambda>y::'e. (0::real,y))
      (halfspace_face U)"
    by (rule Ck_on_bounded_linear[OF pair_linear open_face])
  have F_C2: "Ck_on 2
      (\<lambda>y. F (0,y))
      (halfspace_face U)"
    by (rule Ck_on_compose[OF C2 pair_C2])
       (auto simp: halfspace_face_def)
  show ?thesis
    by (rule Ck_on_bounded_linear_compose
      [OF bounded_linear_snd F_C2])
qed

lemma positive_face_jacobian_from_cart_extension:
  fixes F :: "real ^ (unit + 'n::finite) \<Rightarrow>
      real ^ (unit + 'n)"
  assumes openU: "open U"
    and yU: "cart_tangent_inclusion y \<in> U"
    and face_value:
      "F (cart_tangent_inclusion y) $ Inl () = 0"
    and differentiable:
      "F differentiable (at (cart_tangent_inclusion y))"
    and halfspace: "\<And>x. x \<in> U \<Longrightarrow>
      x \<in> cart_halfspace \<Longrightarrow>
      F x \<in> cart_halfspace"
    and face: "\<And>x. x \<in> U \<Longrightarrow>
      x $ Inl () = 0 \<Longrightarrow> F x $ Inl () = 0"
    and inverse: "jacobian F
      (at (cart_tangent_inclusion y)) ** G = mat 1"
    and positive: "0 < Determinants.det
      (jacobian F (at (cart_tangent_inclusion y)))"
  shows "0 < Determinants.det
    (jacobian
      (\<lambda>u. cart_tangent_projection
        (F (cart_tangent_inclusion u)))
      (at y))"
proof -
  let ?x = "cart_tangent_inclusion y"
  let ?J = "jacobian F (at ?x)"
  have xface: "?x $ Inl () = 0"
    by (simp add: cart_tangent_inclusion_def)
  note orientation = cart_halfspace_boundary_orientation
    [OF openU yU xface face_value differentiable
      halfspace face inverse]
  have normal: "0 < ?J $ Inl () $ Inl ()"
    by (rule orientation(1))
  have block: "Determinants.det ?J =
      ?J $ Inl () $ Inl () *
        Determinants.det (tangential_block ?J)"
    by (rule orientation(2))
  have block_pos:
    "0 < Determinants.det (tangential_block ?J)"
  proof -
    have "0 < ?J $ Inl () $ Inl () *
        Determinants.det (tangential_block ?J)"
      using positive block by simp
    with normal show ?thesis
      by (simp add: zero_less_mult_iff)
  qed
  have face_jac: "jacobian
      (\<lambda>u. cart_tangent_projection
        (F (cart_tangent_inclusion u)))
      (at y) = tangential_block ?J"
    using jacobian_restricted_to_face[OF differentiable]
    by (simp add: o_def)
  show ?thesis
    using block_pos by (simp add: face_jac)
qed

lemma positive_face_jacobian_from_inverse_extensions:
  fixes F G :: "real ^ (unit + 'n::finite) \<Rightarrow>
      real ^ (unit + 'n)"
  assumes C2F: "Ck_on 2 F U"
    and xU: "cart_tangent_inclusion y \<in> U"
    and C2G: "Ck_on 2 G V"
    and image: "\<And>x. x \<in> U \<Longrightarrow>
      x \<in> cart_halfspace \<Longrightarrow> F x \<in> V"
    and inverse: "\<And>x. x \<in> U \<Longrightarrow>
      x \<in> cart_halfspace \<Longrightarrow> G (F x) = x"
    and halfspace: "\<And>x. x \<in> U \<Longrightarrow>
      x \<in> cart_halfspace \<Longrightarrow>
      F x \<in> cart_halfspace"
    and face: "\<And>x. x \<in> U \<Longrightarrow>
      x $ Inl () = 0 \<Longrightarrow>
      F x $ Inl () = 0"
    and positive: "0 < Determinants.det
      (jacobian F (at (cart_tangent_inclusion y)))"
  shows "0 < Determinants.det
    (jacobian
      (\<lambda>u. cart_tangent_projection
        (F (cart_tangent_inclusion u)))
      (at y))"
proof -
  let ?x = "cart_tangent_inclusion y"
  have openU: "open U"
    by (rule Ck_on_open[OF C2F])
  have xH: "?x \<in> cart_halfspace"
    by (simp add: cart_tangent_inclusion_def
      cart_halfspace_def)
  have xface: "?x $ Inl () = 0"
    by (simp add: cart_tangent_inclusion_def)
  have FxV: "F ?x \<in> V"
    by (rule image[OF xU xH])
  have C2F': "Ck_on (Suc 1) F U"
    using C2F by (metis Suc_1)
  have C2G': "Ck_on (Suc 1) G V"
    using C2G by (metis Suc_1)
  have dF: "F differentiable (at ?x)"
    using Ck_on_Suc_iff[of 1 F U, THEN iffD1, OF C2F']
      xU by blast
  have dG: "G differentiable (at (F ?x))"
    using Ck_on_Suc_iff[of 1 G V, THEN iffD1, OF C2G']
      FxV by blast
  have inverse_J: "jacobian F (at ?x) **
      jacobian G (at (F ?x)) = mat 1"
    by (rule jacobian_local_inverse_halfspace
      [OF openU xU xH dF dG inverse])
  have Fface: "F ?x $ Inl () = 0"
    by (rule face[OF xU xface])
  show ?thesis
    by (rule positive_face_jacobian_from_cart_extension
      [OF openU xU Fface dF halfspace face
        inverse_J positive])
qed

lemma positive_face_jacobian_of_local_transition:
  fixes F G :: "real ^ (unit + 'n::finite) \<Rightarrow>
      real ^ (unit + 'n)"
    and h :: "real ^ 'n \<Rightarrow> real ^ 'n"
  assumes C2F: "Ck_on 2 F U"
    and xU: "cart_tangent_inclusion y \<in> U"
    and C2G: "Ck_on 2 G V"
    and image: "\<And>x. x \<in> U \<Longrightarrow>
      x \<in> cart_halfspace \<Longrightarrow> F x \<in> V"
    and inverse: "\<And>x. x \<in> U \<Longrightarrow>
      x \<in> cart_halfspace \<Longrightarrow> G (F x) = x"
    and halfspace: "\<And>x. x \<in> U \<Longrightarrow>
      x \<in> cart_halfspace \<Longrightarrow>
      F x \<in> cart_halfspace"
    and face: "\<And>x. x \<in> U \<Longrightarrow>
      x $ Inl () = 0 \<Longrightarrow>
      F x $ Inl () = 0"
    and positive: "0 < Determinants.det
      (jacobian F (at (cart_tangent_inclusion y)))"
    and openW: "open W"
    and yW: "y \<in> W"
    and agree: "\<And>z. z \<in> W \<Longrightarrow>
      h z = cart_tangent_projection
        (F (cart_tangent_inclusion z))"
  shows "0 < Determinants.det (jacobian h (at y))"
proof -
  let ?g = "\<lambda>z. cart_tangent_projection
    (F (cart_tangent_inclusion z))"
  have face_pos: "0 < Determinants.det
      (jacobian ?g (at y))"
    by (rule positive_face_jacobian_from_inverse_extensions
      [OF C2F xU C2G image inverse halfspace face positive])
  have deriv_eq: "frechet_derivative h (at y) =
    frechet_derivative ?g (at y)"
    by (rule frechet_derivative_transform_within_open
      [OF openW yW agree])
  have "jacobian h (at y) = jacobian ?g (at y)"
    using deriv_eq by (simp add: jacobian_def)
  with face_pos show ?thesis by simp
qed

lemma positive_face_jacobian_from_product_extensions:
  fixes F G :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
    (real \<times> (real ^ 'n))"
  assumes C2F: "Ck_on 2 F U"
    and xU: "(0,y) \<in> U"
    and C2G: "Ck_on 2 G V"
    and image: "\<And>x. x \<in> U \<Longrightarrow>
      x \<in> closed_halfspace \<Longrightarrow> F x \<in> V"
    and inverse: "\<And>x. x \<in> U \<Longrightarrow>
      x \<in> closed_halfspace \<Longrightarrow> G (F x) = x"
    and halfspace: "\<And>x. x \<in> U \<Longrightarrow>
      x \<in> closed_halfspace \<Longrightarrow>
      F x \<in> closed_halfspace"
    and face: "\<And>x. x \<in> U \<Longrightarrow>
      fst x = 0 \<Longrightarrow> fst (F x) = 0"
    and positive: "0 < Determinants.det
      (jacobian (cart_map_of_product F)
        (at (product_to_cart (0,y))))"
  shows "0 < Determinants.det
    (jacobian (\<lambda>z. snd (F (0,z))) (at y))"
proof -
  let ?Fc = "cart_map_of_product F"
  let ?Gc = "cart_map_of_product G"
  let ?Uc = "cart_to_product -` U"
  let ?Vc = "cart_to_product -` V"
  have C2Fc: "Ck_on 2 ?Fc ?Uc"
    by (rule Ck_on_cart_map_of_product[OF C2F])
  have C2Gc: "Ck_on 2 ?Gc ?Vc"
    by (rule Ck_on_cart_map_of_product[OF C2G])
  have yUc: "cart_tangent_inclusion y \<in> ?Uc"
    using xU by (simp add: cart_tangent_inclusion_def)
  have imc: "?Fc x \<in> ?Vc" if x: "x \<in> ?Uc"
    and xH: "x \<in> cart_halfspace" for x
    using image[of "cart_to_product x"] x xH
    by (simp add: cart_map_of_product_def
      cart_halfspace_def closed_halfspace_def
      cart_to_product_def)
  have invc: "?Gc (?Fc x) = x" if x: "x \<in> ?Uc"
    and xH: "x \<in> cart_halfspace" for x
    using inverse[of "cart_to_product x"] x xH
    by (simp add: cart_map_of_product_def
      cart_halfspace_def closed_halfspace_def
      cart_to_product_def product_to_cart_def
      vec_eq_iff split: sum.splits)
  have halfc: "?Fc x \<in> cart_halfspace"
    if x: "x \<in> ?Uc" and xH: "x \<in> cart_halfspace"
    for x
    using halfspace[of "cart_to_product x"] x xH
    by (simp add: cart_map_of_product_def
      cart_halfspace_def closed_halfspace_def
      cart_to_product_def)
  have facec: "?Fc x $ Inl () = 0"
    if x: "x \<in> ?Uc" and xface: "x $ Inl () = 0"
    for x
    using face[of "cart_to_product x"] x xface
    by (simp add: cart_map_of_product_def
      cart_to_product_def product_to_cart_def)
  have positive_c: "0 < Determinants.det
      (jacobian ?Fc (at (cart_tangent_inclusion y)))"
    using positive
    by (simp only: cart_tangent_inclusion_def)
  have pos: "0 < Determinants.det
    (jacobian (\<lambda>z. cart_tangent_projection
      (?Fc (cart_tangent_inclusion z))) (at y))"
    by (rule positive_face_jacobian_from_inverse_extensions
      [OF C2Fc yUc C2Gc imc invc halfc facec positive_c])
  have eq: "(\<lambda>z. cart_tangent_projection
      (?Fc (cart_tangent_inclusion z))) =
      (\<lambda>z. snd (F (0,z)))"
    by (simp add: fun_eq_iff cart_tangent_inclusion_def
      cart_tangent_projection_def cart_to_product_def
      product_to_cart_def cart_map_of_product_def
      vec_eq_iff)
  show ?thesis using pos by (simp add: eq)
qed

lemma product_halfspace_extension_jacobian_unique:
  fixes F G :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
    (real \<times> (real ^ 'n))"
  assumes C2F: "Ck_on 2 F U" and xU: "(0,y) \<in> U"
    and C2G: "Ck_on 2 G V" and xV: "(0,y) \<in> V"
    and agree: "\<And>p. p \<in> U \<Longrightarrow> p \<in> V
      \<Longrightarrow> p \<in> closed_halfspace
      \<Longrightarrow> F p = G p"
  shows "jacobian (cart_map_of_product F)
      (at (product_to_cart (0,y))) =
    jacobian (cart_map_of_product G)
      (at (product_to_cart (0,y)))"
proof -
  let ?Fc = "cart_map_of_product F"
  let ?Gc = "cart_map_of_product G"
  let ?Uc = "cart_to_product -` U"
  let ?Vc = "cart_to_product -` V"
  let ?x = "product_to_cart (0,y)"
  have C2Fc: "Ck_on 2 ?Fc ?Uc"
    by (rule Ck_on_cart_map_of_product[OF C2F])
  have C2Gc: "Ck_on 2 ?Gc ?Vc"
    by (rule Ck_on_cart_map_of_product[OF C2G])
  have openW: "open (?Uc \<inter> ?Vc)"
    by (rule open_Int)
       (use Ck_on_open[OF C2Fc]
         Ck_on_open[OF C2Gc] in auto)
  have xW: "?x \<in> ?Uc \<inter> ?Vc"
    using xU xV by simp
  have xH: "?x \<in> cart_halfspace"
    by (simp add: cart_halfspace_def
      product_to_cart_def)
  have C1Fc: "Ck_on (Suc 0) ?Fc ?Uc"
    by (rule Ck_on_mono[OF C2Fc]) simp
  have C1Gc: "Ck_on (Suc 0) ?Gc ?Vc"
    by (rule Ck_on_mono[OF C2Gc]) simp
  have dF: "?Fc differentiable (at ?x)"
    using Ck_on_Suc_iff[of 0 ?Fc ?Uc,
      THEN iffD1, OF C1Fc] xW by blast
  have dG: "?Gc differentiable (at ?x)"
    using Ck_on_Suc_iff[of 0 ?Gc ?Vc,
      THEN iffD1, OF C1Gc] xW by blast
  have eq: "?Fc v = ?Gc v"
    if v: "v \<in> ?Uc \<inter> ?Vc"
      and vH: "v \<in> cart_halfspace" for v
    using agree[of "cart_to_product v"] v vH
    by (simp add: cart_map_of_product_def
      cart_halfspace_def closed_halfspace_def
      cart_to_product_def)
  have deriv: "frechet_derivative ?Fc (at ?x) =
      frechet_derivative ?Gc (at ?x)"
    by (rule cart_halfspace_ambient_derivative_unique
      [OF openW xW xH dF dG]) (use eq in auto)
  show ?thesis using deriv by (simp add: jacobian_def)
qed

locale halfspace_chart =
  fixes M :: "'a::topological_space set"
    and D :: "'a set"
    and C :: "(real \<times> 'e::euclidean_space) set"
    and to_chart :: "'a \<Rightarrow> real \<times> 'e"
    and from_chart :: "real \<times> 'e \<Rightarrow> 'a"
  assumes open_D: "openin (top_of_set M) D"
    and open_C: "openin (top_of_set closed_halfspace) C"
    and homeo: "homeomorphism D C to_chart from_chart"
begin

lemma domain_subset_carrier: "D \<subseteq> M"
  using open_D by (auto simp: openin_open)

lemma codomain_subset_halfspace: "C \<subseteq> closed_halfspace"
  using open_C by (auto simp: openin_open)

lemma to_from:
  assumes "p \<in> D"
  shows "from_chart (to_chart p) = p"
  by (rule homeomorphism_apply1[OF homeo assms])

lemma from_to:
  assumes "x \<in> C"
  shows "to_chart (from_chart x) = x"
  by (rule homeomorphism_apply2[OF homeo assms])

lemma chart_image: "to_chart ` D = C"
  by (rule homeomorphism_image1[OF homeo])

lemma inverse_image: "from_chart ` C = D"
  by (rule homeomorphism_image2[OF homeo])

lemma face_open: "open (halfspace_face C)"
  by (rule halfspace_face_open[OF open_C])

lemma restrict:
  assumes V: "openin (top_of_set M) V"
    and VD: "V \<subseteq> D"
  shows "halfspace_chart M V (to_chart ` V)
    to_chart from_chart"
proof -
  have VC: "V \<subseteq> M"
    using V by (auto simp: openin_open)
  obtain W where W: "open W" "V = M \<inter> W"
    using V by (auto simp: openin_open)
  have V_open_D: "openin (top_of_set D) V"
    using W VD domain_subset_carrier
    by (auto simp: openin_open)
  have image_open_C:
    "openin (top_of_set C) (to_chart ` V)"
    by (rule homeomorphism_imp_open_map[OF homeo V_open_D])
  have image_open_H:
    "openin (top_of_set closed_halfspace) (to_chart ` V)"
    using image_open_C open_C
    by (rule openin_trans)
  have homeoV: "homeomorphism V (to_chart ` V)
    to_chart from_chart"
    by (rule homeomorphism_of_subsets[OF homeo VD _
      refl]) (use chart_image in auto)
  show ?thesis
    by (unfold_locales)
       (use V image_open_H homeoV in auto)
qed

lemma compact_relative_neighborhood:
  assumes p: "p \<in> D"
  obtains V K where
    "openin (top_of_set M) V"
    "p \<in> V"
    "compact K"
    "V \<subseteq> K"
    "K \<subseteq> D"
proof -
  let ?x = "to_chart p"
  have xC: "?x \<in> C"
    using chart_image p by auto
  obtain U where U: "open U"
    "C = closed_halfspace \<inter> U"
    using open_C by (auto simp: openin_open)
  have xU: "?x \<in> U" and xH: "?x \<in> closed_halfspace"
    using xC U by auto
  obtain e :: real where e: "0 < e"
    "cball ?x e \<subseteq> U"
    using open_contains_cball[THEN iffD1, OF U(1)]
      xU by blast
  let ?Bc = "ball ?x e \<inter> closed_halfspace"
  let ?Kc = "cball ?x e \<inter> closed_halfspace"
  let ?V = "from_chart ` ?Bc"
  let ?K = "from_chart ` ?Kc"
  have ballU: "ball ?x e \<subseteq> U"
    using e(2) by auto
  have Bc: "?Bc = C \<inter> ball ?x e"
    using ballU U(2) by auto
  have Kc: "?Kc \<subseteq> C"
    using e(2) U(2) by auto
  have Bopen: "openin (top_of_set C) ?Bc"
    using Bc
    by (auto simp: openin_open
      intro!: exI[of _ "ball ?x e"])
  have inv_homeo: "homeomorphism C D
      from_chart to_chart"
    by (rule homeomorphism_symD[OF homeo])
  have Vopen_D: "openin (top_of_set D) ?V"
    by (rule homeomorphism_imp_open_map
      [OF inv_homeo Bopen])
  have Vopen: "openin (top_of_set M) ?V"
    by (rule openin_trans[OF Vopen_D open_D])
  have xB: "?x \<in> ?Bc"
    using e(1) xH by simp
  have pV: "p \<in> ?V"
    using to_from[OF p] xB by (metis imageI)
  have compactKc: "compact ?Kc"
    by (rule compact_Int_closed)
       (simp_all add: closed_closed_halfspace)
  have cont_inv: "continuous_on C from_chart"
    by (rule homeomorphism_cont2[OF homeo])
  have cont_Kc: "continuous_on ?Kc from_chart"
    by (rule continuous_on_subset[OF cont_inv Kc])
  have compactK: "compact ?K"
    by (rule compact_continuous_image[OF cont_Kc compactKc])
  have VK: "?V \<subseteq> ?K" by auto
  have KD: "?K \<subseteq> D"
    using Kc inverse_image by auto
  show ?thesis
    by (rule that[OF Vopen pV compactK VK KD])
qed

end

lemma zero_face_chart_homeomorphism:
  fixes C :: "(real \<times> 'e::euclidean_space) set"
  assumes homeo: "homeomorphism D C to_chart from_chart"
  shows "homeomorphism
    {p\<in>D. fst (to_chart p) = 0}
    (halfspace_face C)
    (\<lambda>p. snd (to_chart p))
    (\<lambda>y. from_chart (0,y))"
proof (rule homeomorphismI)
  have cont_to: "continuous_on D to_chart"
    by (rule homeomorphism_cont1[OF homeo])
  have cont_to_restricted: "continuous_on
      {p\<in>D. fst (to_chart p) = 0} to_chart"
    by (rule continuous_on_subset[OF cont_to]) auto
  have cont_snd: "continuous_on UNIV snd"
    by (intro continuous_intros)
  show "continuous_on
      {p\<in>D. fst (to_chart p) = 0}
      (\<lambda>p. snd (to_chart p))"
    by (rule continuous_on_compose2
      [OF cont_snd cont_to_restricted])
       auto
  have cont_from: "continuous_on C from_chart"
    by (rule homeomorphism_cont2[OF homeo])
  have cont_pair: "continuous_on (halfspace_face C)
      (\<lambda>y::'e. (0::real,y))"
    by (intro continuous_intros)
  have pair_image: "(\<lambda>y::'e. (0::real,y)) `
      halfspace_face C \<subseteq> C"
    by (auto simp: halfspace_face_def)
  show "continuous_on (halfspace_face C)
      (\<lambda>y. from_chart (0,y))"
    by (rule continuous_on_compose2
      [OF cont_from cont_pair pair_image])
  show "(\<lambda>p. snd (to_chart p)) `
      {p\<in>D. fst (to_chart p) = 0}
      \<subseteq> halfspace_face C"
  proof
    fix y
    assume "y \<in> (\<lambda>p. snd (to_chart p)) `
      {p\<in>D. fst (to_chart p) = 0}"
    then obtain p where p: "p \<in> D"
      "fst (to_chart p) = 0" "y = snd (to_chart p)"
      by auto
    have "to_chart p = (0,y)"
      using p by (cases "to_chart p") auto
    moreover have "to_chart p \<in> C"
      using homeomorphism_image1[OF homeo] p
      by auto
    ultimately show "y \<in> halfspace_face C"
      by (simp add: halfspace_face_def)
  qed
  show "(\<lambda>y. from_chart (0,y)) `
      halfspace_face C \<subseteq>
      {p\<in>D. fst (to_chart p) = 0}"
  proof
    fix p
    assume "p \<in> (\<lambda>y. from_chart (0,y)) `
      halfspace_face C"
    then obtain y where y: "y \<in> halfspace_face C"
      "p = from_chart (0,y)" by auto
    have xy: "(0,y) \<in> C"
      using y by (simp add: halfspace_face_def)
    have "p \<in> D"
      using homeomorphism_image2[OF homeo] xy y
      by auto
    moreover have "fst (to_chart p) = 0"
      using homeomorphism_apply2[OF homeo xy] y
      by simp
    ultimately show "p \<in>
      {p\<in>D. fst (to_chart p) = 0}" by auto
  qed
  show "\<And>p. p \<in> {p\<in>D. fst (to_chart p) = 0} \<Longrightarrow>
      from_chart (0, snd (to_chart p)) = p"
  proof -
    fix p
    assume p: "p \<in> {p\<in>D. fst (to_chart p) = 0}"
    then have "to_chart p = (0, snd (to_chart p))"
      by (cases "to_chart p") auto
    then show "from_chart (0, snd (to_chart p)) = p"
      using homeomorphism_apply1[OF homeo] p by auto
  qed
  show "\<And>y. y \<in> halfspace_face C \<Longrightarrow>
      snd (to_chart (from_chart (0,y))) = y"
  proof -
    fix y
    assume "y \<in> halfspace_face C"
    then have "(0,y) \<in> C"
      by (simp add: halfspace_face_def)
    then have "to_chart (from_chart (0,y)) = (0,y)"
      by (rule homeomorphism_apply2[OF homeo])
    then show "snd (to_chart (from_chart (0,y))) = y"
      by simp
  qed
qed

lemma identity_closed_halfspace_chart:
  "halfspace_chart
    (closed_halfspace :: (real \<times> 'e::euclidean_space) set)
    closed_halfspace closed_halfspace id id"
  by (unfold_locales)
     (auto simp: openin_open id_def
       intro: homeomorphism_ident)

lemma identity_open_halfspace_chart:
  "halfspace_chart
    (open_halfspace :: (real \<times> 'e::euclidean_space) set)
    open_halfspace open_halfspace id id"
proof (unfold_locales)
  show "openin (top_of_set open_halfspace) open_halfspace"
    by (simp add: openin_open)
  show "openin (top_of_set closed_halfspace)
      open_halfspace"
    by (rule openin_open_halfspace)
  show "homeomorphism open_halfspace
      open_halfspace id id"
    by (simp add: id_def homeomorphism_ident)
qed

lemma closed_halfspace_face:
  "halfspace_face (closed_halfspace ::
    (real \<times> 'e::euclidean_space) set) = UNIV"
  by (auto simp: halfspace_face_def closed_halfspace_def)

lemma open_halfspace_face:
  "halfspace_face (open_halfspace ::
    (real \<times> 'e::euclidean_space) set) = {}"
  by (auto simp: halfspace_face_def open_halfspace_def)

locale halfspace_atlas =
  fixes M :: "'a::topological_space set"
    and I :: "'i set"
    and D :: "'i \<Rightarrow> 'a set"
    and C :: "'i \<Rightarrow> (real \<times> 'e::euclidean_space) set"
    and to_chart :: "'i \<Rightarrow> 'a \<Rightarrow> real \<times> 'e"
    and from_chart :: "'i \<Rightarrow> real \<times> 'e \<Rightarrow> 'a"
  assumes chart: "\<And>i. i \<in> I \<Longrightarrow>
      halfspace_chart M (D i) (C i)
        (to_chart i) (from_chart i)"
    and cover: "M \<subseteq> (\<Union>i\<in>I. D i)"
    and face_compatible: "\<And>i j p.
      i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
      p \<in> D i \<Longrightarrow> p \<in> D j \<Longrightarrow>
      (fst (to_chart i p) = 0 \<longleftrightarrow>
        fst (to_chart j p) = 0)"
begin

definition boundary_carrier where
  "boundary_carrier =
    {p\<in>M. \<exists>i\<in>I.
      p \<in> D i \<and> fst (to_chart i p) = 0}"

definition interior_carrier where
  "interior_carrier = M - boundary_carrier"

lemma domain_subset_carrier:
  assumes i: "i \<in> I"
  shows "D i \<subseteq> M"
  by (rule halfspace_chart.domain_subset_carrier[OF chart[OF i]])

lemma boundary_subset_carrier:
  "boundary_carrier \<subseteq> M"
  by (auto simp: boundary_carrier_def)

lemma boundary_chart_classify:
  assumes i: "i \<in> I"
    and p: "p \<in> D i"
  shows "p \<in> boundary_carrier \<longleftrightarrow>
    fst (to_chart i p) = 0"
proof
  assume "p \<in> boundary_carrier"
  then obtain j where j: "j \<in> I" "p \<in> D j"
    "fst (to_chart j p) = 0"
    by (auto simp: boundary_carrier_def)
  show "fst (to_chart i p) = 0"
    using face_compatible[OF i j(1) p j(2)] j(3)
    by simp
next
  assume "fst (to_chart i p) = 0"
  moreover have "p \<in> M"
    using domain_subset_carrier[OF i] p by auto
  ultimately show "p \<in> boundary_carrier"
    using i p by (auto simp: boundary_carrier_def)
qed

lemma chart_interior_open:
  assumes i: "i \<in> I"
  shows "openin (top_of_set M)
    {p\<in>D i. 0 < fst (to_chart i p)}"
proof -
  have d_open: "openin (top_of_set M) (D i)"
    by (rule halfspace_chart.open_D[OF chart[OF i]])
  have cont: "continuous_on (D i) (to_chart i)"
    by (rule homeomorphism_cont1
      [OF halfspace_chart.homeo[OF chart[OF i]]])
  have U_open: "open {x::real \<times> 'e. 0 < fst x}"
    by (intro open_Collect_less continuous_intros)
  have all: "\<forall>T. open T \<longrightarrow>
      openin (top_of_set (D i))
        (D i \<inter> (to_chart i) -` T)"
    using cont by (simp only: continuous_openin_preimage_eq)
  have rel: "openin (top_of_set (D i))
      (D i \<inter> (to_chart i) -`
        {x::real \<times> 'e. 0 < fst x})"
    using all U_open by blast
  have "openin (top_of_set M)
      (D i \<inter> (to_chart i) -` {x. 0 < fst x})"
    by (rule openin_trans[OF rel d_open])
  moreover have "D i \<inter> (to_chart i) -` {x. 0 < fst x} =
    {p\<in>D i. 0 < fst (to_chart i p)}"
    by auto
  ultimately show ?thesis by simp
qed

lemma interior_carrier_union:
  "interior_carrier =
    (\<Union>i\<in>I. {p\<in>D i. 0 < fst (to_chart i p)})"
proof
  show "interior_carrier \<subseteq>
    (\<Union>i\<in>I. {p\<in>D i. 0 < fst (to_chart i p)})"
  proof
    fix p
    assume p: "p \<in> interior_carrier"
    then have pM: "p \<in> M"
      by (simp add: interior_carrier_def)
    obtain i where i: "i \<in> I" "p \<in> D i"
      using cover pM by blast
    have "to_chart i p \<in> closed_halfspace"
      using halfspace_chart.codomain_subset_halfspace
        [OF chart[OF i(1)]]
        halfspace_chart.chart_image[OF chart[OF i(1)]]
        i(2)
      by blast
    then have nonnegative: "0 \<le> fst (to_chart i p)"
      by (simp add: closed_halfspace_def)
    have "fst (to_chart i p) \<noteq> 0"
      using p boundary_chart_classify[OF i]
      by (auto simp: interior_carrier_def)
    with nonnegative have "0 < fst (to_chart i p)"
      by simp
    with i show "p \<in>
      (\<Union>i\<in>I. {p\<in>D i. 0 < fst (to_chart i p)})"
      by blast
  qed
  show "(\<Union>i\<in>I.
      {p\<in>D i. 0 < fst (to_chart i p)})
    \<subseteq> interior_carrier"
  proof
    fix p
    assume "p \<in> (\<Union>i\<in>I.
      {p\<in>D i. 0 < fst (to_chart i p)})"
    then obtain i where i: "i \<in> I" "p \<in> D i"
      "0 < fst (to_chart i p)" by blast
    have "p \<in> M"
      using domain_subset_carrier[OF i(1)] i(2) by auto
    moreover have "p \<notin> boundary_carrier"
      using boundary_chart_classify[OF i(1,2)] i(3)
      by auto
    ultimately show "p \<in> interior_carrier"
      by (simp add: interior_carrier_def)
  qed
qed

lemma interior_carrier_open:
  "openin (top_of_set M) interior_carrier"
  unfolding interior_carrier_union
  by (intro openin_Union) (auto intro: chart_interior_open)

lemma boundary_carrier_closed:
  "closedin (top_of_set M) boundary_carrier"
  using boundary_subset_carrier interior_carrier_open
  by (auto simp: closedin_def interior_carrier_def)

lemma boundary_compact_relative_neighborhood:
  assumes p: "p \<in> boundary_carrier"
  obtains i V K where
    "i \<in> I"
    "openin (top_of_set boundary_carrier) V"
    "p \<in> V"
    "compact K"
    "V \<subseteq> K"
    "K \<subseteq> boundary_carrier \<inter> D i"
proof -
  have pM: "p \<in> M"
    using boundary_subset_carrier p by auto
  obtain i where i: "i \<in> I" "p \<in> D i"
    using cover pM by blast
  interpret c: halfspace_chart M "D i" "C i"
    "to_chart i" "from_chart i"
    by (rule chart[OF i(1)])
  obtain V0 K0 where V0: "openin (top_of_set M) V0"
    "p \<in> V0" "compact K0" "V0 \<subseteq> K0"
    "K0 \<subseteq> D i"
    by (rule c.compact_relative_neighborhood[OF i(2)])
  let ?V = "boundary_carrier \<inter> V0"
  let ?K = "boundary_carrier \<inter> K0"
  have Vopen: "openin (top_of_set boundary_carrier) ?V"
    using V0(1) boundary_subset_carrier
    by (auto simp: openin_open)
  have pV: "p \<in> ?V" using p V0(2) by auto
  obtain T where T: "closed T"
    "boundary_carrier = M \<inter> T"
    using boundary_carrier_closed
    by (auto simp: closedin_closed)
  have K0M: "K0 \<subseteq> M"
    using V0(5) domain_subset_carrier[OF i(1)]
    by auto
  have Keq: "?K = K0 \<inter> T"
    using T(2) K0M by auto
  have compactK: "compact ?K"
    unfolding Keq
    by (rule compact_Int_closed[OF V0(3) T(1)])
  have VK: "?V \<subseteq> ?K" using V0(4) by auto
  have KD: "?K \<subseteq> boundary_carrier \<inter> D i"
    using V0(5) by auto
  show ?thesis
    by (rule that[OF i(1) Vopen pV compactK VK KD])
qed

lemma finite_boundary_chart_neighborhoods:
  assumes compact: "compact K"
    and KB: "K \<subseteq> boundary_carrier"
  obtains P j V L where
    "finite P"
    "P \<subseteq> K"
    "K \<subseteq> (\<Union>p\<in>P. V p)"
    "\<And>p. p \<in> P \<Longrightarrow> j p \<in> I"
    "\<And>p. p \<in> P \<Longrightarrow>
      openin (top_of_set boundary_carrier) (V p)"
    "\<And>p. p \<in> P \<Longrightarrow> p \<in> V p"
    "\<And>p. p \<in> P \<Longrightarrow> compact (L p)"
    "\<And>p. p \<in> P \<Longrightarrow> V p \<subseteq> L p"
    "\<And>p. p \<in> P \<Longrightarrow>
      L p \<subseteq> boundary_carrier \<inter> D (j p)"
proof -
  have witness: "\<exists>i W Q.
      i \<in> I \<and>
      openin (top_of_set boundary_carrier) W \<and>
      p \<in> W \<and> compact Q \<and>
      W \<subseteq> Q \<and>
      Q \<subseteq> boundary_carrier \<inter> D i"
    if p: "p \<in> K" for p
  proof -
    obtain i W Q where data: "i \<in> I"
      "openin (top_of_set boundary_carrier) W"
      "p \<in> W" "compact Q" "W \<subseteq> Q"
      "Q \<subseteq> boundary_carrier \<inter> D i"
      by (rule boundary_compact_relative_neighborhood
        [OF subsetD[OF KB p]])
    show ?thesis using data by blast
  qed
  then obtain j V L where data: "\<And>p. p \<in> K \<Longrightarrow>
      j p \<in> I \<and>
      openin (top_of_set boundary_carrier) (V p) \<and>
      p \<in> V p \<and> compact (L p) \<and>
      V p \<subseteq> L p \<and>
      L p \<subseteq> boundary_carrier \<inter> D (j p)"
    by metis
  have ambient: "\<forall>p\<in>K. \<exists>U.
      open U \<and> V p = boundary_carrier \<inter> U"
    using data by (auto simp: openin_open)
  then obtain U where U: "\<And>p. p \<in> K \<Longrightarrow>
      open (U p) \<and> V p = boundary_carrier \<inter> U p"
    by metis
  have cover: "K \<subseteq> (\<Union>p\<in>K. U p)"
    using data U by auto
  obtain P where P: "P \<subseteq> K" "finite P"
    "K \<subseteq> (\<Union>p\<in>P. U p)"
    by (rule compactE_image[OF compact]) (use U cover in auto)
  have coverV: "K \<subseteq> (\<Union>p\<in>P. V p)"
  proof
    fix x
    assume xK: "x \<in> K"
    then obtain q where q: "q \<in> P" "x \<in> U q"
      using P(3) by auto
    have qK: "q \<in> K" using P(1) q(1) by auto
    have xB: "x \<in> boundary_carrier"
      using KB xK by auto
    have "x \<in> V q"
      using U[OF qK] q(2) xB by auto
    with q(1) show "x \<in> (\<Union>p\<in>P. V p)"
      by auto
  qed
  have jI: "j p \<in> I" if "p \<in> P" for p
    using data[of p] P(1) that by auto
  have Vopen: "openin (top_of_set boundary_carrier) (V p)"
    if "p \<in> P" for p
    using data[of p] P(1) that by auto
  have pV: "p \<in> V p" if "p \<in> P" for p
    using data[of p] P(1) that by auto
  have compactL: "compact (L p)" if "p \<in> P" for p
    using data[of p] P(1) that by auto
  have VL: "V p \<subseteq> L p" if "p \<in> P" for p
    using data[of p] P(1) that by auto
  have LD: "L p \<subseteq> boundary_carrier \<inter> D (j p)"
    if "p \<in> P" for p
    using data[of p] P(1) that by auto
  show ?thesis
    by (rule that[OF P(2,1) coverV jI Vopen pV compactL VL LD])
qed

lemma boundary_chart_domain_open:
  assumes i: "i \<in> I"
  shows "openin (top_of_set boundary_carrier)
    (boundary_carrier \<inter> D i)"
proof -
  have D_open: "openin (top_of_set M) (D i)"
    by (rule halfspace_chart.open_D[OF chart[OF i]])
  obtain U where U: "open U" "D i = M \<inter> U"
    using D_open by (auto simp: openin_open)
  have "boundary_carrier \<inter> D i =
      boundary_carrier \<inter> U"
    using U boundary_subset_carrier by auto
  with U show ?thesis
    by (auto simp: openin_open)
qed

lemma boundary_chart_codomain_open:
  assumes i: "i \<in> I"
  shows "open (halfspace_face (C i))"
  by (rule halfspace_chart.face_open[OF chart[OF i]])

lemma boundary_restricted_homeomorphism:
  assumes i: "i \<in> I"
  shows "homeomorphism
    (boundary_carrier \<inter> D i)
    (halfspace_face (C i))
    (\<lambda>p. snd (to_chart i p))
    (\<lambda>y. from_chart i (0,y))"
proof -
  have eq: "boundary_carrier \<inter> D i =
    {p\<in>D i. fst (to_chart i p) = 0}"
    using boundary_chart_classify[OF i]
    by auto
  show ?thesis
    unfolding eq
    by (rule zero_face_chart_homeomorphism
      [OF halfspace_chart.homeo[OF chart[OF i]]])
qed

lemma boundary_chart_cover:
  "boundary_carrier \<subseteq>
    (\<Union>i\<in>I. boundary_carrier \<inter> D i)"
proof
  fix p
  assume p: "p \<in> boundary_carrier"
  then have "p \<in> M"
    using boundary_subset_carrier by auto
  then obtain i where "i \<in> I" "p \<in> D i"
    using cover by blast
  with p show "p \<in>
    (\<Union>i\<in>I. boundary_carrier \<inter> D i)"
    by blast
qed

definition coordinate_overlap ::
    "'i \<Rightarrow> 'i \<Rightarrow> (real \<times> 'e) set"
  where "coordinate_overlap i j =
    {x\<in>C i. from_chart i x \<in> D j}"

definition coordinate_transition ::
    "'i \<Rightarrow> 'i \<Rightarrow> real \<times> 'e \<Rightarrow> real \<times> 'e"
  where "coordinate_transition i j x =
    to_chart j (from_chart i x)"

lemma coordinate_overlap_image:
  assumes i: "i \<in> I"
  shows "coordinate_overlap i j =
    to_chart i ` (D i \<inter> D j)"
proof
  show "coordinate_overlap i j \<subseteq>
      to_chart i ` (D i \<inter> D j)"
  proof
    fix x
    assume x: "x \<in> coordinate_overlap i j"
    then have xi: "x \<in> C i"
      and pj: "from_chart i x \<in> D j"
      by (auto simp: coordinate_overlap_def)
    have pi: "from_chart i x \<in> D i"
      using halfspace_chart.inverse_image[OF chart[OF i]] xi
      by auto
    have "to_chart i (from_chart i x) = x"
      by (rule halfspace_chart.from_to[OF chart[OF i] xi])
    with pi pj show "x \<in> to_chart i ` (D i \<inter> D j)"
      by (metis IntI imageI)
  qed
  show "to_chart i ` (D i \<inter> D j) \<subseteq>
      coordinate_overlap i j"
  proof
    fix x
    assume "x \<in> to_chart i ` (D i \<inter> D j)"
    then obtain p where p: "p \<in> D i" "p \<in> D j"
      "x = to_chart i p" by auto
    have "x \<in> C i"
      using halfspace_chart.chart_image[OF chart[OF i]]
        p(1,3) by auto
    moreover have "from_chart i x \<in> D j"
      using halfspace_chart.to_from[OF chart[OF i] p(1)]
        p(2,3) by simp
    ultimately show "x \<in> coordinate_overlap i j"
      by (simp add: coordinate_overlap_def)
  qed
qed

lemma coordinate_overlap_open:
  assumes i: "i \<in> I" and j: "j \<in> I"
  shows "openin (top_of_set closed_halfspace)
    (coordinate_overlap i j)"
proof -
  have open_Dj: "openin (top_of_set M) (D j)"
    by (rule halfspace_chart.open_D[OF chart[OF j]])
  have sub: "D i \<subseteq> M"
    by (rule domain_subset_carrier[OF i])
  have open_inter: "openin (top_of_set (D i))
      (D i \<inter> D j)"
    using open_Dj sub by (auto simp: openin_open)
  have open_image: "openin (top_of_set (C i))
      (to_chart i ` (D i \<inter> D j))"
    by (rule homeomorphism_imp_open_map
      [OF halfspace_chart.homeo[OF chart[OF i]]
        open_inter])
  have open_C: "openin (top_of_set closed_halfspace)
      (C i)"
    by (rule halfspace_chart.open_C[OF chart[OF i]])
  show ?thesis
    using openin_trans[OF open_image open_C]
    by (simp add: coordinate_overlap_image[OF i])
qed

lemma coordinate_transition_inverse:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and x: "x \<in> coordinate_overlap i j"
  shows "coordinate_transition i j x
      \<in> coordinate_overlap j i"
    and "coordinate_transition j i
      (coordinate_transition i j x) = x"
proof -
  have xi: "x \<in> C i" and pj: "from_chart i x \<in> D j"
    using x by (auto simp: coordinate_overlap_def)
  have pi: "from_chart i x \<in> D i"
    using halfspace_chart.inverse_image[OF chart[OF i]] xi
    by auto
  have zC: "coordinate_transition i j x \<in> C j"
    using halfspace_chart.chart_image[OF chart[OF j]] pj
    by (auto simp: coordinate_transition_def)
  have zfrom: "from_chart j
      (coordinate_transition i j x) = from_chart i x"
    using halfspace_chart.to_from[OF chart[OF j] pj]
    by (simp add: coordinate_transition_def)
  show "coordinate_transition i j x
      \<in> coordinate_overlap j i"
    using zC zfrom pi by (simp add: coordinate_overlap_def)
  show "coordinate_transition j i
      (coordinate_transition i j x) = x"
    using zfrom halfspace_chart.from_to[OF chart[OF i] xi]
    by (simp add: coordinate_transition_def)
qed

definition boundary_overlap ::
    "'i \<Rightarrow> 'i \<Rightarrow> 'e set"
  where "boundary_overlap i j =
    {y\<in>halfspace_face (C i).
      from_chart i (0,y) \<in> D j}"

definition boundary_transition ::
    "'i \<Rightarrow> 'i \<Rightarrow> 'e \<Rightarrow> 'e"
  where "boundary_transition i j y =
    snd (to_chart j (from_chart i (0,y)))"

lemma boundary_in_coordinate_overlap:
  assumes y: "y \<in> boundary_overlap i j"
  shows "(0,y) \<in> coordinate_overlap i j"
  using y by (auto simp: boundary_overlap_def
    coordinate_overlap_def halfspace_face_def)

lemma coordinate_transition_preserves_face:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and x: "x \<in> coordinate_overlap i j"
    and face: "fst x = 0"
  shows "fst (coordinate_transition i j x) = 0"
proof -
  have xi: "x \<in> C i" and pj: "from_chart i x \<in> D j"
    using x by (auto simp: coordinate_overlap_def)
  have pi: "from_chart i x \<in> D i"
    using halfspace_chart.inverse_image[OF chart[OF i]]
      xi by auto
  have "to_chart i (from_chart i x) = x"
    by (rule halfspace_chart.from_to[OF chart[OF i] xi])
  with face face_compatible[OF i j pi pj]
  show ?thesis
    by (simp add: coordinate_transition_def)
qed

lemma coordinate_transition_in_halfspace:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and x: "x \<in> coordinate_overlap i j"
  shows "coordinate_transition i j x \<in> closed_halfspace"
  using coordinate_transition_inverse(1)[OF i j x]
    halfspace_chart.codomain_subset_halfspace[OF chart[OF j]]
  by (auto simp: coordinate_overlap_def)

lemma boundary_overlap_image:
  assumes i: "i \<in> I"
  shows "boundary_overlap i j =
    (\<lambda>p. snd (to_chart i p)) `
      (boundary_carrier \<inter> D i \<inter> D j)"
proof
  show "boundary_overlap i j \<subseteq>
    (\<lambda>p. snd (to_chart i p)) `
      (boundary_carrier \<inter> D i \<inter> D j)"
  proof
    fix y
    assume y: "y \<in> boundary_overlap i j"
    let ?p = "from_chart i (0,y)"
    have xy: "(0,y) \<in> C i"
      using y by (simp add: boundary_overlap_def
        halfspace_face_def)
    have pi: "?p \<in> D i"
      using halfspace_chart.inverse_image[OF chart[OF i]]
        xy by auto
    have pb: "?p \<in> boundary_carrier"
      using boundary_chart_classify[OF i pi]
        halfspace_chart.from_to[OF chart[OF i] xy]
      by simp
    have pj: "?p \<in> D j"
      using y by (simp add: boundary_overlap_def)
    have "snd (to_chart i ?p) = y"
      using halfspace_chart.from_to[OF chart[OF i] xy]
      by simp
    moreover have "?p \<in>
        boundary_carrier \<inter> D i \<inter> D j"
      using pb pi pj by auto
    ultimately show "y \<in>
      (\<lambda>p. snd (to_chart i p)) `
        (boundary_carrier \<inter> D i \<inter> D j)"
      by (metis imageI)
  qed
  show "(\<lambda>p. snd (to_chart i p)) `
      (boundary_carrier \<inter> D i \<inter> D j)
    \<subseteq> boundary_overlap i j"
  proof
    fix y
    assume "y \<in> (\<lambda>p. snd (to_chart i p)) `
      (boundary_carrier \<inter> D i \<inter> D j)"
    then obtain p where p: "p \<in> boundary_carrier"
      "p \<in> D i" "p \<in> D j"
      "y = snd (to_chart i p)" by auto
    have face0: "fst (to_chart i p) = 0"
      using boundary_chart_classify[OF i p(2)] p(1)
      by simp
    have xy: "(0,y) = to_chart i p"
      using face0 p by (cases "to_chart i p") auto
    have "y \<in> halfspace_face (C i)"
      using halfspace_chart.chart_image[OF chart[OF i]]
        p(2) xy
      by (auto simp: halfspace_face_def)
    moreover have "from_chart i (0,y) \<in> D j"
      using halfspace_chart.to_from[OF chart[OF i] p(2)]
        p xy by simp
    ultimately show "y \<in> boundary_overlap i j"
      by (simp add: boundary_overlap_def)
  qed
qed

lemma boundary_overlap_open:
  assumes i: "i \<in> I" and j: "j \<in> I"
  shows "open (boundary_overlap i j)"
proof -
  have dom_open: "openin (top_of_set boundary_carrier)
      (boundary_carrier \<inter> D i \<inter> D j)"
  proof -
    have "openin (top_of_set boundary_carrier)
      ((boundary_carrier \<inter> D i) \<inter>
        (boundary_carrier \<inter> D j))"
      by (rule openin_Int[OF
        boundary_chart_domain_open[OF i]
        boundary_chart_domain_open[OF j]])
    then show ?thesis
      by (simp add: Int_assoc Int_left_commute Int_commute)
  qed
  have dom_open_restricted:
    "openin (top_of_set (boundary_carrier \<inter> D i))
      (boundary_carrier \<inter> D i \<inter> D j)"
  proof -
    obtain U where U: "open U"
      "boundary_carrier \<inter> D i \<inter> D j =
        boundary_carrier \<inter> U"
      using dom_open by (auto simp: openin_open)
    have "boundary_carrier \<inter> D i \<inter> D j =
      (boundary_carrier \<inter> D i) \<inter> U"
      using U by auto
    with U show ?thesis
      by (auto simp: openin_open)
  qed
  have rel_open: "openin (top_of_set
      (halfspace_face (C i)))
      ((\<lambda>p. snd (to_chart i p)) `
        (boundary_carrier \<inter> D i \<inter> D j))"
    by (rule homeomorphism_imp_open_map
      [OF boundary_restricted_homeomorphism[OF i]])
       (rule dom_open_restricted)
  have "openin (top_of_set (halfspace_face (C i)))
      (boundary_overlap i j)"
    using rel_open by (simp add: boundary_overlap_image[OF i])
  then show ?thesis
    by (rule openin_open_trans[OF _
      boundary_chart_codomain_open[OF i]])
qed

lemma boundary_overlap_homeomorphism:
  assumes i: "i \<in> I"
  shows "homeomorphism
    (boundary_carrier \<inter> D i \<inter> D j)
    (boundary_overlap i j)
    (\<lambda>p. snd (to_chart i p))
    (\<lambda>y. from_chart i (0,y))"
proof (rule homeomorphism_of_subsets
    [OF boundary_restricted_homeomorphism[OF i]])
  show "boundary_carrier \<inter> D i \<inter> D j
      \<subseteq> boundary_carrier \<inter> D i"
    by auto
  show "halfspace_face (C i) \<subseteq>
      halfspace_face (C i)" by simp
  show "(\<lambda>p. snd (to_chart i p)) `
      (boundary_carrier \<inter> D i \<inter> D j) =
    boundary_overlap i j"
    by (simp add: boundary_overlap_image[OF i])
qed

lemma boundary_transition_homeomorphism:
  assumes i: "i \<in> I" and j: "j \<in> I"
  shows "homeomorphism
    (boundary_overlap i j)
    (boundary_overlap j i)
    (boundary_transition i j)
    (boundary_transition j i)"
proof -
  have h_i: "homeomorphism
      (boundary_overlap i j)
      (boundary_carrier \<inter> D i \<inter> D j)
      (\<lambda>y. from_chart i (0,y))
      (\<lambda>p. snd (to_chart i p))"
    by (rule homeomorphism_symD
      [OF boundary_overlap_homeomorphism[OF i]])
  have h_j: "homeomorphism
      (boundary_carrier \<inter> D i \<inter> D j)
      (boundary_overlap j i)
      (\<lambda>p. snd (to_chart j p))
      (\<lambda>y. from_chart j (0,y))"
    using boundary_overlap_homeomorphism[OF j, of i]
    by (simp add: Int_assoc Int_left_commute Int_commute)
  have comp: "homeomorphism
      (boundary_overlap i j)
      (boundary_overlap j i)
      ((\<lambda>p. snd (to_chart j p)) \<circ>
        (\<lambda>y. from_chart i (0,y)))
      ((\<lambda>p. snd (to_chart i p)) \<circ>
        (\<lambda>y. from_chart j (0,y)))"
    by (rule homeomorphism_compose[OF h_i h_j])
  show ?thesis
    using comp
    unfolding boundary_transition_def
    by (simp only: o_def)
qed

lemma boundary_transition_chart_point:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and y: "y \<in> boundary_overlap i j"
  shows "from_chart j
      (0,boundary_transition i j y) =
    from_chart i (0,y)"
proof -
  let ?p = "from_chart i (0,y)"
  have xi: "(0,y) \<in> C i"
    using y by (simp add: boundary_overlap_def
      halfspace_face_def)
  have pj: "?p \<in> D j"
    using y by (simp add: boundary_overlap_def)
  have pi: "?p \<in> D i"
    using halfspace_chart.inverse_image[OF chart[OF i]]
      xi by auto
  have i0: "fst (to_chart i ?p) = 0"
    using halfspace_chart.from_to[OF chart[OF i] xi]
    by simp
  have j0: "fst (to_chart j ?p) = 0"
    using face_compatible[OF i j pi pj] i0
    by simp
  have pair: "to_chart j ?p =
      (0,boundary_transition i j y)"
    using j0 by (cases "to_chart j ?p")
      (simp add: boundary_transition_def)
  show ?thesis
    using halfspace_chart.to_from[OF chart[OF j] pj]
      pair by simp
qed

end

lemma identity_closed_halfspace_atlas:
  "halfspace_atlas
    (closed_halfspace :: (real \<times> 'e::euclidean_space) set)
    (UNIV::unit set)
    (\<lambda>_. closed_halfspace)
    (\<lambda>_. closed_halfspace)
    (\<lambda>_. id) (\<lambda>_. id)"
  by (rule halfspace_atlas.intro)
     (auto intro: identity_closed_halfspace_chart)

lemma identity_open_halfspace_atlas:
  "halfspace_atlas
    (open_halfspace :: (real \<times> 'e::euclidean_space) set)
    (UNIV::unit set)
    (\<lambda>_. open_halfspace)
    (\<lambda>_. open_halfspace)
    (\<lambda>_. id) (\<lambda>_. id)"
  by (rule halfspace_atlas.intro)
     (auto intro: identity_open_halfspace_chart)

lemma identity_closed_halfspace_boundary:
  "halfspace_atlas.boundary_carrier
    (closed_halfspace :: (real \<times> 'e::euclidean_space) set)
    (UNIV::unit set)
    (\<lambda>_. closed_halfspace)
    (\<lambda>_. id) =
    {p. fst p = 0}"
proof -
  interpret A: halfspace_atlas
    "closed_halfspace :: (real \<times> 'e) set"
    "UNIV::unit set"
    "\<lambda>_. closed_halfspace"
    "\<lambda>_. closed_halfspace"
    "\<lambda>_. id" "\<lambda>_. id"
    by (rule identity_closed_halfspace_atlas)
  show ?thesis
  proof (rule set_eqI)
    fix p :: "real \<times> 'e"
    show "p \<in> A.boundary_carrier \<longleftrightarrow>
      p \<in> {p. fst p = 0}"
    proof
      assume B: "p \<in> A.boundary_carrier"
      have "p \<in> closed_halfspace"
        using A.boundary_subset_carrier B by auto
      with A.boundary_chart_classify[of "()" p] B
      show "p \<in> {p. fst p = 0}"
        by (simp add: id_def)
    next
      assume "p \<in> {p. fst p = 0}"
      then have "p \<in> closed_halfspace"
        by (simp add: closed_halfspace_def)
      with \<open>p \<in> {p. fst p = 0}\<close>
        A.boundary_chart_classify[of "()" p]
      show "p \<in> A.boundary_carrier"
        by (simp add: id_def)
    qed
  qed
qed

lemma identity_open_halfspace_boundary:
  "halfspace_atlas.boundary_carrier
    (open_halfspace :: (real \<times> 'e::euclidean_space) set)
    (UNIV::unit set)
    (\<lambda>_. open_halfspace)
    (\<lambda>_. id) = {}"
proof -
  interpret A: halfspace_atlas
    "open_halfspace :: (real \<times> 'e) set"
    "UNIV::unit set"
    "\<lambda>_. open_halfspace"
    "\<lambda>_. open_halfspace"
    "\<lambda>_. id" "\<lambda>_. id"
    by (rule identity_open_halfspace_atlas)
  show ?thesis
  proof (rule ccontr)
    assume "A.boundary_carrier \<noteq> {}"
    then obtain p where B: "p \<in> A.boundary_carrier"
      by auto
    have "p \<in> open_halfspace"
      using A.boundary_subset_carrier B by auto
    then have "0 < fst p"
      by (simp add: open_halfspace_def)
    moreover have "fst p = 0"
      using A.boundary_chart_classify[of "()" p] B
        \<open>p \<in> open_halfspace\<close>
      by (simp add: id_def)
    ultimately show False by simp
  qed
qed

locale C2_halfspace_atlas =
  halfspace_atlas M I D C to_chart from_chart
  for M :: "'a::topological_space set"
    and I :: "'i set"
    and D :: "'i \<Rightarrow> 'a set"
    and C :: "'i \<Rightarrow> (real \<times> 'e::euclidean_space) set"
    and to_chart :: "'i \<Rightarrow> 'a \<Rightarrow> real \<times> 'e"
    and from_chart :: "'i \<Rightarrow> real \<times> 'e \<Rightarrow> 'a" +
  assumes transition_extension: "\<And>i j y.
    i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
    y \<in> boundary_overlap i j \<Longrightarrow>
    \<exists>U F. open U \<and> (0,y) \<in> U \<and>
      Ck_on 2 F U \<and>
      (\<forall>x\<in>U \<inter> C i.
        from_chart i x \<in> D j \<longrightarrow>
          F x = to_chart j (from_chart i x))"
begin

lemma local_transition_extensions_inverse:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and y: "y \<in> boundary_overlap i j"
  shows "\<exists>U V F G.
    Ck_on 2 F U \<and> (0,y) \<in> U \<and> Ck_on 2 G V \<and>
    (\<forall>x\<in>U \<inter> closed_halfspace.
      F x \<in> V \<and> G (F x) = x \<and>
      F x \<in> closed_halfspace \<and>
      F x = coordinate_transition i j x) \<and>
    (\<forall>x\<in>U. fst x = 0 \<longrightarrow> fst (F x) = 0) \<and>
    (\<forall>x\<in>V. fst x = 0 \<longrightarrow> fst (G x) = 0)"
proof -
  let ?x = "(0,y)"
  have xij: "?x \<in> coordinate_overlap i j"
    by (rule boundary_in_coordinate_overlap[OF y])
  let ?z = "coordinate_transition i j ?x"
  have zji: "?z \<in> coordinate_overlap j i"
    by (rule coordinate_transition_inverse(1)[OF i j xij])
  have zface: "fst ?z = 0"
    by (rule coordinate_transition_preserves_face[OF i j xij])
       simp
  have zboundary: "snd ?z \<in> boundary_overlap j i"
    using zji zface
    by (cases ?z) (auto simp: boundary_overlap_def
      coordinate_overlap_def halfspace_face_def)
  obtain U0 F where U0: "open U0" "?x \<in> U0"
    and C2F: "Ck_on 2 F U0"
    and agreeF: "\<forall>q\<in>U0 \<inter> C i.
      from_chart i q \<in> D j \<longrightarrow>
        F q = coordinate_transition i j q"
    using transition_extension[OF i j y]
    by (auto simp: coordinate_transition_def)
  obtain V G where V: "open V" "(0,snd ?z) \<in> V"
    and C2G: "Ck_on 2 G V"
    and agreeG: "\<forall>q\<in>V \<inter> C j.
      from_chart j q \<in> D i \<longrightarrow>
        G q = coordinate_transition j i q"
    using transition_extension[OF j i zboundary]
    by (auto simp: coordinate_transition_def)
  obtain Oi where Oi: "open Oi"
    "coordinate_overlap i j = closed_halfspace \<inter> Oi"
    using coordinate_overlap_open[OF i j]
    by (auto simp: openin_open)
  obtain Oj where Oj: "open Oj"
    "coordinate_overlap j i = closed_halfspace \<inter> Oj"
    using coordinate_overlap_open[OF j i]
    by (auto simp: openin_open)
  have xOi: "?x \<in> Oi" using xij Oi by auto
  have zOj: "?z \<in> Oj" using zji Oj by auto
  have Fx: "F ?x = ?z"
    using agreeF U0(2) xij
    by (auto simp: coordinate_overlap_def)
  have zV: "?z \<in> V" using V(2) zface
    by (cases ?z) auto
  let ?U = "U0 \<inter> Oi \<inter> F -` (V \<inter> Oj)"
  have openFV: "open (U0 \<inter> F -` (V \<inter> Oj))"
    by (rule continuous_open_preimage
      [OF Ck_on_imp_continuous_on[OF C2F] U0(1)])
       (use V(1) Oj(1) in auto)
  have openU: "open ?U"
    using openFV Oi(1)
    by (metis Int_assoc Int_commute open_Int)
  have xU: "?x \<in> ?U"
    using U0(2) xOi Fx zV zOj by auto
  have subU: "?U \<subseteq> U0" by auto
  have C2U: "Ck_on 2 F ?U"
    by (rule Ck_on_subset[OF C2F openU subU])
  let ?V = "V \<inter> Oj"
  have openV: "open ?V"
    by (rule open_Int[OF V(1) Oj(1)])
  have C2V: "Ck_on 2 G ?V"
    by (rule Ck_on_subset[OF C2G openV]) auto
  have local: "F q \<in> V \<and> G (F q) = q \<and>
      F q \<in> closed_halfspace \<and>
      F q = coordinate_transition i j q"
    if q: "q \<in> ?U \<inter> closed_halfspace" for q
  proof -
    have qij: "q \<in> coordinate_overlap i j"
      using q Oi(2) by auto
    have Fq: "F q = coordinate_transition i j q"
      using agreeF q qij
      by (auto simp: coordinate_overlap_def)
    have Fqji: "F q \<in> coordinate_overlap j i"
      using coordinate_transition_inverse(1)[OF i j qij]
        Fq by simp
    have FqV: "F q \<in> V" using q by auto
    have GFq: "G (F q) = coordinate_transition j i (F q)"
      using agreeG FqV Fqji
      by (auto simp: coordinate_overlap_def)
    have "coordinate_transition j i (F q) = q"
      using coordinate_transition_inverse(2)[OF i j qij]
        Fq by simp
    moreover have "F q \<in> closed_halfspace"
      using coordinate_transition_in_halfspace[OF i j qij]
        Fq by simp
    ultimately show ?thesis
      using FqV GFq Fq by simp
  qed
  have localV: "F q \<in> ?V \<and> G (F q) = q \<and>
      F q \<in> closed_halfspace \<and>
      F q = coordinate_transition i j q"
    if "q \<in> ?U \<inter> closed_halfspace" for q
    using local[OF that] that by auto
  have face: "fst (F q) = 0" if q: "q \<in> ?U"
    and qface: "fst q = 0" for q
  proof -
    have qH: "q \<in> closed_halfspace"
      using qface by (simp add: closed_halfspace_def)
    have qij: "q \<in> coordinate_overlap i j"
      using q qH Oi(2) by auto
    have Fq: "F q = coordinate_transition i j q"
      using local q qH by auto
    show ?thesis
      using coordinate_transition_preserves_face[OF i j qij qface]
        Fq by simp
  qed
  have Gface: "fst (G q) = 0" if q: "q \<in> ?V"
    and qface: "fst q = 0" for q
  proof -
    have qH: "q \<in> closed_halfspace"
      using qface by (simp add: closed_halfspace_def)
    have qji: "q \<in> coordinate_overlap j i"
      using q qH Oj(2) by auto
    have Gq: "G q = coordinate_transition j i q"
      using agreeG q qji
      by (auto simp: coordinate_overlap_def)
    show ?thesis
      using coordinate_transition_preserves_face
        [OF j i qji qface] Gq by simp
  qed
  show ?thesis
    using C2U xU C2V localV face Gface by blast
qed

lemma boundary_transition_C2:
  assumes i: "i \<in> I" and j: "j \<in> I"
  shows "Ck_on 2 (boundary_transition i j)
    (boundary_overlap i j)"
proof (rule Ck_onI[OF boundary_overlap_open[OF i j]])
  fix y
  assume y: "y \<in> boundary_overlap i j"
  obtain U F where U: "open U" "(0,y) \<in> U"
    and F: "Ck_on 2 F U"
    and agree: "\<forall>x\<in>U \<inter> C i.
      from_chart i x \<in> D j \<longrightarrow>
        F x = to_chart j (from_chart i x)"
    using transition_extension[OF i j y] by blast
  let ?V = "boundary_overlap i j \<inter> halfspace_face U"
  have face_C2: "Ck_on 2
      (\<lambda>z. snd (F (0,z))) (halfspace_face U)"
    by (rule Ck_on_face_restriction[OF F])
  have openV: "open ?V"
    using boundary_overlap_open[OF i j]
      Ck_on_open[OF face_C2] by auto
  have subV: "?V \<subseteq> halfspace_face U"
    by auto
  have face_V: "Ck_on 2
      (\<lambda>z. snd (F (0,z))) ?V"
    by (rule Ck_on_subset[OF face_C2 openV subV])
  have eq: "boundary_transition i j z =
      snd (F (0,z))" if z: "z \<in> ?V" for z
  proof -
    have zi: "(0,z) \<in> C i"
      using z by (simp add: boundary_overlap_def
        halfspace_face_def)
    have zU: "(0,z) \<in> U"
      using z by (simp add: halfspace_face_def)
    have zj: "from_chart i (0,z) \<in> D j"
      using z by (simp add: boundary_overlap_def)
    have "F (0,z) =
      to_chart j (from_chart i (0,z))"
      using agree zi zU zj by auto
    then show ?thesis
      by (simp add: boundary_transition_def)
  qed
  have C2V: "Ck_on 2 (boundary_transition i j) ?V"
    by (rule Ck_on_congI[OF face_V eq])
  have "y \<in> ?V"
    using y U by (simp add: halfspace_face_def)
  then show "Ck_at 2 (boundary_transition i j) y"
    by (rule Ck_onD[OF C2V])
qed

end

locale oriented_C2_halfspace_atlas =
  C2_halfspace_atlas M I D C to_chart from_chart
  for M :: "'a::topological_space set"
    and I :: "'i set"
    and D :: "'i \<Rightarrow> 'a set"
    and C :: "'i \<Rightarrow> (real \<times> (real ^ 'n::finite)) set"
    and to_chart :: "'i \<Rightarrow> 'a \<Rightarrow>
      real \<times> (real ^ 'n)"
    and from_chart :: "'i \<Rightarrow>
      real \<times> (real ^ 'n) \<Rightarrow> 'a" +
  assumes oriented_transition_extension: "\<And>i j y.
    i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
    y \<in> boundary_overlap i j \<Longrightarrow>
    \<exists>U V W F G.
      Ck_on 2 F U \<and>
      cart_tangent_inclusion y \<in> U \<and>
      Ck_on 2 G V \<and>
      (\<forall>x\<in>U \<inter> cart_halfspace.
        F x \<in> V \<and> G (F x) = x \<and>
        F x \<in> cart_halfspace) \<and>
      (\<forall>x\<in>U.
        x $ Inl () = 0 \<longrightarrow>
          F x $ Inl () = 0) \<and>
      0 < Determinants.det
        (jacobian F (at (cart_tangent_inclusion y))) \<and>
      open W \<and> y \<in> W \<and>
      (\<forall>z\<in>W.
        boundary_transition i j z =
          cart_tangent_projection
            (F (cart_tangent_inclusion z)))"
begin

lemma positive_boundary_transition:
  assumes i: "i \<in> I"
    and j: "j \<in> I"
    and y: "y \<in> boundary_overlap i j"
  shows "0 < Determinants.det
    (jacobian (boundary_transition i j) (at y))"
proof -
  obtain U V W F G where
    C2F: "Ck_on 2 F U"
    and xU: "cart_tangent_inclusion y \<in> U"
    and C2G: "Ck_on 2 G V"
    and inv: "\<forall>x\<in>U \<inter> cart_halfspace.
        F x \<in> V \<and> G (F x) = x \<and>
        F x \<in> cart_halfspace"
    and face: "\<forall>x\<in>U.
        x $ Inl () = 0 \<longrightarrow>
          F x $ Inl () = 0"
    and positive: "0 < Determinants.det
      (jacobian F (at (cart_tangent_inclusion y)))"
    and openW: "open W"
    and yW: "y \<in> W"
    and agree: "\<forall>z\<in>W.
      boundary_transition i j z =
        cart_tangent_projection
          (F (cart_tangent_inclusion z))"
    using oriented_transition_extension[OF i j y]
    by blast
  show ?thesis
    by (rule positive_face_jacobian_of_local_transition
      [OF C2F xU C2G _ _ _ _ positive openW yW])
       (use inv face agree in auto)
qed

end

locale positively_oriented_C2_halfspace_atlas =
  C2_halfspace_atlas M I D C to_chart from_chart
  for M :: "'a::topological_space set"
    and I :: "'i set"
    and D :: "'i \<Rightarrow> 'a set"
    and C :: "'i \<Rightarrow> (real \<times> (real ^ 'n::finite)) set"
    and to_chart :: "'i \<Rightarrow> 'a \<Rightarrow>
      real \<times> (real ^ 'n)"
    and from_chart :: "'i \<Rightarrow>
      real \<times> (real ^ 'n) \<Rightarrow> 'a" +
  assumes positive_coordinate_extension_exists: "\<And>i j y.
    i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
    y \<in> boundary_overlap i j \<Longrightarrow>
    \<exists>U F. Ck_on 2 F U \<and> (0,y) \<in> U \<and>
      (\<forall>x\<in>U \<inter> closed_halfspace.
        F x = coordinate_transition i j x) \<and>
      0 < Determinants.det (jacobian
        (cart_map_of_product F)
        (at (product_to_cart (0,y))))"
begin

lemma positive_coordinate_extension:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and y: "y \<in> boundary_overlap i j"
    and C2F: "Ck_on 2 F U" and xU: "(0,y) \<in> U"
    and agreeF: "\<And>x. x \<in> U \<Longrightarrow>
      x \<in> closed_halfspace \<Longrightarrow>
      F x = coordinate_transition i j x"
  shows "0 < Determinants.det (jacobian
      (cart_map_of_product F)
      (at (product_to_cart (0,y))))"
proof -
  obtain V G where C2G: "Ck_on 2 G V"
    and xV: "(0,y) \<in> V"
    and agreeG: "\<forall>x\<in>V \<inter> closed_halfspace.
      G x = coordinate_transition i j x"
    and positive: "0 < Determinants.det (jacobian
      (cart_map_of_product G)
      (at (product_to_cart (0,y))))"
    using positive_coordinate_extension_exists[OF i j y]
    by blast
  have agree: "F x = G x" if xU: "x \<in> U"
    and xV: "x \<in> V"
    and xH: "x \<in> closed_halfspace" for x
  proof -
    have Gx: "G x = coordinate_transition i j x"
      using agreeG xV xH by auto
    show ?thesis using agreeF[OF xU xH] Gx by simp
  qed
  have jac: "jacobian (cart_map_of_product F)
      (at (product_to_cart (0,y))) =
    jacobian (cart_map_of_product G)
      (at (product_to_cart (0,y)))"
    by (rule product_halfspace_extension_jacobian_unique
      [OF C2F xU C2G xV agree])
  show ?thesis using positive by (simp add: jac)
qed

lemma boundary_coefficient_transition_for_extensions:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and y: "y \<in> boundary_overlap i j"
    and C2F: "Ck_on 2 F U"
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
  shows "\<forall>A.
    product_boundary_coeff (product_pull_near_top F G A) y =
      pull_top (boundary_transition i j)
        (product_boundary_coeff A) y"
proof -
  have openU: "open U" by (rule Ck_on_open[OF C2F])
  have openV: "open V" by (rule Ck_on_open[OF C2G])
  have xH: "(0,y) \<in> closed_halfspace"
    by (simp add: closed_halfspace_def)
  have FxV: "F (0,y) \<in> V"
    using local xU xH by blast
  have Fface: "fst (F (0,y)) = 0"
    using faceF xU by auto
  have C1F: "Ck_on (Suc 0) F U"
    by (rule Ck_on_mono[OF C2F]) simp
  have C1G: "Ck_on (Suc 0) G V"
    by (rule Ck_on_mono[OF C2G]) simp
  have dF: "F differentiable (at (0,y))"
    using Ck_on_Suc_iff[of 0 F U, THEN iffD1, OF C1F]
      xU by blast
  have dG: "G differentiable (at (F (0,y)))"
    using Ck_on_Suc_iff[of 0 G V, THEN iffD1, OF C1G]
      FxV by blast
  let ?W = "boundary_overlap i j \<inter> halfspace_face U"
  have openW: "open ?W"
    using boundary_overlap_open[OF i j]
      Ck_on_open[OF Ck_on_face_restriction[OF C2F]]
    by (rule open_Int)
  have yW: "y \<in> ?W"
    using y xU by (simp add: halfspace_face_def)
  have agree: "boundary_transition i j z =
      snd (F (0,z))" if z: "z \<in> ?W" for z
  proof -
    have zU: "(0,z) \<in> U"
      using z by (simp add: halfspace_face_def)
    have zH: "(0,z) \<in> closed_halfspace"
      by (simp add: closed_halfspace_def)
    have "F (0,z) = coordinate_transition i j (0,z)"
      using local zU zH by auto
    then show ?thesis
      by (simp add: boundary_transition_def
        coordinate_transition_def)
  qed
  have face_jac: "jacobian
      (\<lambda>z. snd (F (0,z))) (at y) =
      jacobian (boundary_transition i j) (at y)"
  proof -
    have deriv: "frechet_derivative
        (boundary_transition i j) (at y) =
        frechet_derivative (\<lambda>z. snd (F (0,z))) (at y)"
      by (rule frechet_derivative_transform_within_open
        [OF openW yW agree])
    show ?thesis using deriv by (simp add: jacobian_def)
  qed
  have Fvalue: "snd (F (0,y)) =
      boundary_transition i j y"
    using agree yW by simp
  have faceFw: "fst (F q) = 0"
    if "q \<in> U" and "fst q = 0" for q
    using faceF that by blast
  have faceGw: "fst (G q) = 0"
    if "q \<in> V" and "fst q = 0" for q
    using faceG that by blast
  have inversew: "G (F q) = q"
    if "q \<in> U" and "0 \<le> fst q" for q
  proof -
    have "q \<in> closed_halfspace"
      using that(2) by (simp add: closed_halfspace_def)
    with local that(1) show ?thesis by blast
  qed
  have law: "product_boundary_coeff
      (product_pull_near_top F G A) y =
    pull_top (boundary_transition i j)
      (product_boundary_coeff A) y" for A
  proof -
    have raw: "product_boundary_coeff
        (product_pull_near_top F G A) y =
      Determinants.det (jacobian
        (\<lambda>u. snd (F (0,u))) (at y)) *
        product_boundary_coeff A (snd (F (0,y)))"
      by (rule product_boundary_coeff_pull_face_local_inverse
        [OF openU openV xU FxV Fface dF dG
          faceFw faceGw inversew])
    show ?thesis
      using raw by (simp add: face_jac Fvalue pull_top_def)
  qed
  show ?thesis using law by blast
qed

lemma local_boundary_coefficient_transition:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and y: "y \<in> boundary_overlap i j"
  shows "\<exists>F G. \<forall>A.
    product_boundary_coeff (product_pull_near_top F G A) y =
      pull_top (boundary_transition i j)
        (product_boundary_coeff A) y"
proof -
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
  have law: "\<forall>A.
      product_boundary_coeff
        (product_pull_near_top F G A) y =
      pull_top (boundary_transition i j)
        (product_boundary_coeff A) y"
    by (rule boundary_coefficient_transition_for_extensions
      [OF i j y C2F xU C2G local faceF faceG])
  show ?thesis using law by blast
qed

lemma positive_boundary_transition:
  assumes i: "i \<in> I" and j: "j \<in> I"
    and y: "y \<in> boundary_overlap i j"
  shows "0 < Determinants.det
    (jacobian (boundary_transition i j) (at y))"
proof -
  obtain U V F G where C2F: "Ck_on 2 F U"
    and xU: "(0,y) \<in> U"
    and C2G: "Ck_on 2 G V"
    and local: "\<forall>x\<in>U \<inter> closed_halfspace.
      F x \<in> V \<and> G (F x) = x \<and>
      F x \<in> closed_halfspace \<and>
      F x = coordinate_transition i j x"
    and face: "\<forall>x\<in>U.
      fst x = 0 \<longrightarrow> fst (F x) = 0"
    and reverse_face: "\<forall>x\<in>V.
      fst x = 0 \<longrightarrow> fst (G x) = 0"
    using local_transition_extensions_inverse[OF i j y]
    by blast
  have positive: "0 < Determinants.det
      (jacobian (cart_map_of_product F)
        (at (product_to_cart (0,y))))"
    by (rule positive_coordinate_extension
      [OF i j y C2F xU]) (use local in auto)
  have image: "F x \<in> V" if "x \<in> U"
    and "x \<in> closed_halfspace" for x
    using local that by blast
  have inverse: "G (F x) = x" if "x \<in> U"
    and "x \<in> closed_halfspace" for x
    using local that by blast
  have halfspace: "F x \<in> closed_halfspace"
    if "x \<in> U" and "x \<in> closed_halfspace" for x
    using local that by blast
  have face0: "fst (F x) = 0" if "x \<in> U"
    and "fst x = 0" for x
    using face that by blast
  have face_pos: "0 < Determinants.det
      (jacobian (\<lambda>z. snd (F (0,z))) (at y))"
    by (rule positive_face_jacobian_from_product_extensions
      [OF C2F xU C2G image inverse halfspace face0
        positive])
  let ?W = "boundary_overlap i j \<inter> halfspace_face U"
  have openW: "open ?W"
    using boundary_overlap_open[OF i j]
      Ck_on_open[OF Ck_on_face_restriction[OF C2F]]
    by (rule open_Int)
  have yW: "y \<in> ?W"
    using y xU by (simp add: halfspace_face_def)
  have agree: "boundary_transition i j z =
      snd (F (0,z))" if z: "z \<in> ?W" for z
  proof -
    have zU: "(0,z) \<in> U"
      using z by (simp add: halfspace_face_def)
    have zH: "(0,z) \<in> closed_halfspace"
      by (simp add: closed_halfspace_def)
    have "F (0,z) = coordinate_transition i j (0,z)"
      using local zU zH by auto
    then show ?thesis
      by (simp add: boundary_transition_def
        coordinate_transition_def)
  qed
  have deriv_eq: "frechet_derivative
      (boundary_transition i j) (at y) =
      frechet_derivative (\<lambda>z. snd (F (0,z))) (at y)"
    by (rule frechet_derivative_transform_within_open
      [OF openW yW agree])
  show ?thesis
    using face_pos deriv_eq by (simp add: jacobian_def)
qed

end

end
