theory Cart_Product
  imports Forms Product_Forms
begin

definition product_to_cart ::
    "(real \<times> (real ^ 'n::finite)) \<Rightarrow> real ^ (unit + 'n)"
  where "product_to_cart p =
    (\<chi> i. case_sum (\<lambda>u. fst p) (\<lambda>j. snd p $ j) i)"

definition cart_to_product ::
    "real ^ (unit + 'n::finite) \<Rightarrow> (real \<times> (real ^ 'n))"
  where "cart_to_product v =
    (v $ Inl (), \<chi> j. v $ Inr j)"

lemma cart_to_product_to_cart [simp]:
  "cart_to_product (product_to_cart p) = p"
  by (cases p) (simp add: cart_to_product_def product_to_cart_def
    vec_eq_iff)

lemma product_to_cart_to_product [simp]:
  "product_to_cart (cart_to_product v) = v"
  by (simp add: cart_to_product_def product_to_cart_def
    vec_eq_iff split: sum.splits)

lemma product_to_cart_linear:
  "linear (product_to_cart ::
      (real \<times> (real ^ 'n::finite)) \<Rightarrow> real ^ (unit + 'n))"
  by (rule linearI)
     (auto simp: product_to_cart_def vec_eq_iff
       split: sum.splits)

lemma cart_to_product_linear:
  "linear (cart_to_product ::
      real ^ (unit + 'n::finite) \<Rightarrow> (real \<times> (real ^ 'n)))"
  by (rule linearI)
     (auto simp: cart_to_product_def vec_eq_iff)

lemma product_to_cart_bounded_linear:
  "bounded_linear (product_to_cart ::
      (real \<times> (real ^ 'n::finite)) \<Rightarrow> real ^ (unit + 'n))"
  by (simp add: linear_conv_bounded_linear[symmetric]
    product_to_cart_linear)

lemma cart_to_product_bounded_linear:
  "bounded_linear (cart_to_product ::
      real ^ (unit + 'n::finite) \<Rightarrow> (real \<times> (real ^ 'n)))"
  by (simp add: linear_conv_bounded_linear[symmetric]
    cart_to_product_linear)

lemma product_to_cart_frechet_derivative [simp]:
  "frechet_derivative (product_to_cart ::
      (real \<times> (real ^ 'n::finite)) \<Rightarrow> real ^ (unit + 'n))
      (at p) = product_to_cart"
  by (rule frechet_derivative_at[symmetric])
     (rule bounded_linear.has_derivative[OF product_to_cart_bounded_linear],
      simp)

lemma cart_to_product_frechet_derivative [simp]:
  "frechet_derivative (cart_to_product ::
      real ^ (unit + 'n::finite) \<Rightarrow> (real \<times> (real ^ 'n)))
      (at v) = cart_to_product"
  by (rule frechet_derivative_at[symmetric])
     (rule bounded_linear.has_derivative[OF cart_to_product_bounded_linear],
      simp)

definition cart_form_of_product ::
    "((real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))) \<Rightarrow>
      real ^ (unit + 'n) \<Rightarrow> real ^ (unit + 'n)"
  where "cart_form_of_product A v =
    product_to_cart (A (cart_to_product v))"

lemma cart_form_of_product_frechet_derivative:
  fixes A :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))"
  assumes dA: "A differentiable (at p)"
  shows "frechet_derivative (cart_form_of_product A)
      (at (product_to_cart p)) =
    product_to_cart \<circ> frechet_derivative A (at p) \<circ>
      cart_to_product"
proof -
  let ?v = "product_to_cart p"
  have dC: "cart_to_product differentiable (at ?v)"
    by (rule bounded_linear_imp_differentiable
        [OF cart_to_product_bounded_linear])
  have dA': "A differentiable (at (cart_to_product ?v))"
    using dA by simp
  have dAC: "(A \<circ> cart_to_product) differentiable (at ?v)"
    by (rule differentiable_chain_at[OF dC dA'])
  have dP: "product_to_cart differentiable (at (A p))"
    by (rule bounded_linear_imp_differentiable
        [OF product_to_cart_bounded_linear])
  have dP': "product_to_cart differentiable
      (at ((A \<circ> cart_to_product) ?v))"
    using dP by simp
  have eqfun: "cart_form_of_product A =
      product_to_cart \<circ> (A \<circ> cart_to_product)"
    by (rule ext) (simp add: cart_form_of_product_def)
  have "frechet_derivative (cart_form_of_product A) (at ?v) =
      frechet_derivative product_to_cart (at (A p)) \<circ>
        frechet_derivative (A \<circ> cart_to_product) (at ?v)"
    unfolding eqfun
    using frechet_derivative_compose[OF dAC dP']
    by (simp add: comp_def)
  also have "\<dots> = product_to_cart \<circ>
      frechet_derivative A (at p) \<circ> cart_to_product"
    by (simp add: frechet_derivative_compose[OF dC dA']
      o_assoc)
  finally show ?thesis .
qed

lemma cart_to_product_axis_normal [simp]:
  "cart_to_product (axis (Inl ()) 1) =
    (1, 0::real ^ 'n::finite)"
  by (simp add: cart_to_product_def vec_eq_iff axis_def)

lemma cart_to_product_axis_tangential [simp]:
  "cart_to_product (axis (Inr j) 1) =
    (0, axis j 1::real ^ 'n::finite)"
  by (simp add: cart_to_product_def vec_eq_iff axis_def)

lemma product_to_cart_normal [simp]:
  "product_to_cart p $ Inl () = fst p"
  by (simp add: product_to_cart_def)

lemma product_to_cart_tangential [simp]:
  "product_to_cart p $ Inr j = snd p $ j"
  by (simp add: product_to_cart_def)

lemma sum_UNIV_unit_plus:
  fixes h :: "(unit + 'n::finite) \<Rightarrow> real"
  shows "(\<Sum>i\<in>UNIV. h i) =
    h (Inl ()) + (\<Sum>j\<in>UNIV. h (Inr j))"
proof -
  have decomp: "(UNIV::(unit + 'n) set) =
      {Inl ()} \<union> Inr ` (UNIV::'n set)"
  proof (rule set_eqI)
    fix x :: "unit + 'n"
    show "x \<in> UNIV \<longleftrightarrow>
        x \<in> {Inl ()} \<union> Inr ` (UNIV::'n set)"
      by (cases x) auto
  qed
  have inj: "inj_on Inr (UNIV::'n set)"
    by (rule inj_onI) simp
  have fin: "finite (Inr ` (UNIV::'n set))"
    by simp
  have nin: "Inl () \<notin> Inr ` (UNIV::'n set)"
    by auto
  have "(\<Sum>i\<in>UNIV. h i) =
      h (Inl ()) + (\<Sum>i\<in>Inr ` (UNIV::'n set). h i)"
    by (simp add: decomp sum.insert[OF fin nin])
  also have "\<dots> =
      h (Inl ()) + (\<Sum>j\<in>UNIV. h (Inr j))"
    by (simp add: sum.reindex[OF inj])
  finally show ?thesis .
qed

lemma product_exterior_top_cartesian:
  fixes A :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))"
  shows "product_exterior_top A p =
    fst (frechet_derivative A (at p) (1,0)) +
      (\<Sum>j\<in>UNIV.
        snd (frechet_derivative A (at p) (0,axis j 1)) $ j)"
  by (simp add: product_exterior_top_def Basis_vec_def
    UNION_singleton_eq_range sum.reindex axis_eq_axis
    inj_on_def inner_axis)

theorem exterior_top_cart_form_of_product:
  fixes A :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))"
  assumes dA: "A differentiable (at p)"
  shows "exterior_top (cart_form_of_product A) (product_to_cart p) =
    product_exterior_top A p"
proof -
  let ?D = "frechet_derivative A (at p)"
  have D: "frechet_derivative (cart_form_of_product A)
      (at (product_to_cart p)) =
    product_to_cart \<circ> ?D \<circ> cart_to_product"
    by (rule cart_form_of_product_frechet_derivative[OF dA])
  have "exterior_top (cart_form_of_product A) (product_to_cart p) =
      (\<Sum>i\<in>UNIV.
        (product_to_cart \<circ> ?D \<circ> cart_to_product)
          (axis i 1) $ i)"
    by (simp add: exterior_top_coordinate D)
  also have "\<dots> =
      fst (?D (1,0)) +
        (\<Sum>j\<in>UNIV. snd (?D (0,axis j 1)) $ j)"
    by (simp add: sum_UNIV_unit_plus)
  also have "\<dots> = product_exterior_top A p"
    by (simp add: product_exterior_top_cartesian)
  finally show ?thesis .
qed

definition product_form_of_cart ::
    "(real ^ (unit + 'n::finite) \<Rightarrow>
      real ^ (unit + 'n)) \<Rightarrow>
      (real \<times> (real ^ 'n)) \<Rightarrow> (real \<times> (real ^ 'n))"
  where "product_form_of_cart B p =
    cart_to_product (B (product_to_cart p))"

lemma cart_form_of_product_form_of_cart [simp]:
  "cart_form_of_product (product_form_of_cart B) = B"
  by (rule ext)
     (simp add: cart_form_of_product_def product_form_of_cart_def)

lemma product_form_of_cart_form_of_product [simp]:
  "product_form_of_cart (cart_form_of_product A) = A"
  by (rule ext)
     (simp add: cart_form_of_product_def product_form_of_cart_def)

lemma product_form_of_cart_differentiable:
  fixes B :: "real ^ (unit + 'n::finite) \<Rightarrow>
    real ^ (unit + 'n)"
  assumes dB: "B differentiable (at (product_to_cart p))"
  shows "product_form_of_cart B differentiable (at p)"
proof -
  have dP: "product_to_cart differentiable (at p)"
    by (rule bounded_linear_imp_differentiable
        [OF product_to_cart_bounded_linear])
  have dPB: "(B \<circ> product_to_cart) differentiable (at p)"
    by (rule differentiable_chain_at[OF dP dB])
  have dC: "cart_to_product differentiable
      (at (B (product_to_cart p)))"
    by (rule bounded_linear_imp_differentiable
        [OF cart_to_product_bounded_linear])
  have dC': "cart_to_product differentiable
      (at ((B \<circ> product_to_cart) p))"
    using dC by simp
  have d: "(cart_to_product \<circ> (B \<circ> product_to_cart))
      differentiable (at p)"
    by (rule differentiable_chain_at[OF dPB dC'])
  show ?thesis
    unfolding product_form_of_cart_def
    using d by (simp add: comp_def)
qed

lemma cart_form_of_product_differentiable:
  fixes A :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))"
  assumes dA: "A differentiable (at p)"
  shows "cart_form_of_product A differentiable
    (at (product_to_cart p))"
proof -
  have dC: "cart_to_product differentiable
      (at (product_to_cart p))"
    by (rule bounded_linear_imp_differentiable
        [OF cart_to_product_bounded_linear])
  have dCA: "(A \<circ> cart_to_product) differentiable
      (at (product_to_cart p))"
    by (rule differentiable_chain_at[OF dC])
       (use dA in simp)
  have dP: "product_to_cart differentiable (at (A p))"
    by (rule bounded_linear_imp_differentiable
        [OF product_to_cart_bounded_linear])
  have dP': "product_to_cart differentiable
      (at ((A \<circ> cart_to_product) (product_to_cart p)))"
    using dP by simp
  have d: "(product_to_cart \<circ> (A \<circ> cart_to_product))
      differentiable (at (product_to_cart p))"
    by (rule differentiable_chain_at[OF dCA dP'])
  show ?thesis
    unfolding cart_form_of_product_def
    using d by (simp add: comp_def)
qed

lemma exterior_top_product_form_of_cart:
  fixes B :: "real ^ (unit + 'n::finite) \<Rightarrow>
    real ^ (unit + 'n)"
  assumes dB: "B differentiable (at (product_to_cart p))"
  shows "product_exterior_top (product_form_of_cart B) p =
    exterior_top B (product_to_cart p)"
proof -
  have d: "product_form_of_cart B differentiable (at p)"
    by (rule product_form_of_cart_differentiable[OF dB])
  have "exterior_top
      (cart_form_of_product (product_form_of_cart B))
      (product_to_cart p) =
      product_exterior_top (product_form_of_cart B) p"
    by (rule exterior_top_cart_form_of_product[OF d])
  then show ?thesis by simp
qed

definition cart_map_of_product ::
    "((real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))) \<Rightarrow>
      real ^ (unit + 'n) \<Rightarrow> real ^ (unit + 'n)"
  where "cart_map_of_product f v =
    product_to_cart (f (cart_to_product v))"

lemma cart_map_of_product_at [simp]:
  "cart_map_of_product f (product_to_cart p) =
    product_to_cart (f p)"
  by (simp add: cart_map_of_product_def)

lemma Ck_on_cart_map_of_product:
  fixes f :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))"
  assumes C2: "Ck_on 2 f W"
  shows "Ck_on 2 (cart_map_of_product f)
    (cart_to_product -` W)"
proof -
  let ?U = "cart_to_product -` W"
  have openW: "open W"
    by (rule Ck_on_open[OF C2])
  have contC: "\<And>v. continuous (at v) cart_to_product"
    by (rule bounded_linear.continuous[OF
        cart_to_product_bounded_linear continuous_ident])
  have openU: "open ?U"
    by (rule continuous_open_vimage[OF openW contC])
  have CkC: "Ck_on 2 cart_to_product ?U"
    by (rule Ck_on_bounded_linear
        [OF cart_to_product_bounded_linear openU])
  have CkF: "Ck_on 2 (\<lambda>v. f (cart_to_product v)) ?U"
    by (rule Ck_on_compose[OF C2 CkC]) auto
  have "Ck_on 2
      (\<lambda>v. product_to_cart (f (cart_to_product v))) ?U"
    by (rule Ck_on_bounded_linear_compose
        [OF product_to_cart_bounded_linear CkF])
  then show ?thesis
    unfolding cart_map_of_product_def .
qed

definition product_pull_near_top ::
    "((real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))) \<Rightarrow>
      ((real \<times> (real ^ 'n)) \<Rightarrow>
      (real \<times> (real ^ 'n))) \<Rightarrow>
      ((real \<times> (real ^ 'n)) \<Rightarrow>
      (real \<times> (real ^ 'n))) \<Rightarrow>
      (real \<times> (real ^ 'n)) \<Rightarrow>
      (real \<times> (real ^ 'n))"
  where "product_pull_near_top f g A =
    product_form_of_cart
      (pull_near_top (cart_map_of_product f)
        (cart_map_of_product g) (cart_form_of_product A))"

lemma product_pull_near_top_cong_open:
  fixes f g f' g' A :: "real \<times> (real ^ 'n::finite)
    \<Rightarrow> real \<times> (real ^ 'n)"
  assumes openU: "open U" and pU: "p \<in> U"
    and eqF: "\<And>q. q \<in> U \<Longrightarrow> f q = f' q"
    and openV: "open V" and fpV: "f p \<in> V"
    and eqG: "\<And>z. z \<in> V \<Longrightarrow> g z = g' z"
  shows "product_pull_near_top f g A p =
    product_pull_near_top f' g' A p"
proof -
  let ?u = "product_to_cart p"
  let ?U = "cart_to_product -` U"
  let ?V = "cart_to_product -` V"
  have contC: "\<And>v. continuous (at v) cart_to_product"
    by (rule bounded_linear.continuous[OF
        cart_to_product_bounded_linear continuous_ident])
  have openUc: "open ?U"
    by (rule continuous_open_vimage[OF openU contC])
  have openVc: "open ?V"
    by (rule continuous_open_vimage[OF openV contC])
  have uU: "?u \<in> ?U" using pU by simp
  have fuV: "cart_map_of_product f ?u \<in> ?V"
    using fpV by simp
  have fval: "cart_map_of_product f ?u =
      cart_map_of_product f' ?u"
    using eqF pU by simp
  have Df: "frechet_derivative (cart_map_of_product f)
      (at ?u) =
      frechet_derivative (cart_map_of_product f') (at ?u)"
    by (rule frechet_derivative_transform_within_open
      [OF openUc uU])
       (use eqF in
         \<open>auto simp: cart_map_of_product_def\<close>)
  have Dg: "frechet_derivative (cart_map_of_product g)
      (at (cart_map_of_product f ?u)) =
      frechet_derivative (cart_map_of_product g')
        (at (cart_map_of_product f ?u))"
    by (rule frechet_derivative_transform_within_open
      [OF openVc fuV])
       (use eqG in
         \<open>auto simp: cart_map_of_product_def\<close>)
  have gval: "cart_map_of_product g
      (cart_map_of_product f ?u) =
      cart_map_of_product g'
        (cart_map_of_product f ?u)"
    using eqG fpV by (simp add: cart_map_of_product_def)
  show ?thesis
    using fval Df Dg gval
    by (simp add: product_pull_near_top_def
      pull_near_top_def jacobian_def
      product_form_of_cart_def)
qed

definition product_pull_top ::
    "((real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))) \<Rightarrow>
      ((real \<times> (real ^ 'n)) \<Rightarrow> real) \<Rightarrow>
      (real \<times> (real ^ 'n)) \<Rightarrow> real"
  where "product_pull_top f T p =
    Determinants.det
      (jacobian (cart_map_of_product f) (at (product_to_cart p))) *
      T (f p)"

theorem product_exterior_top_pull_near_top_C2:
  fixes f g A :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))"
  assumes C2f: "Ck_on 2 (cart_map_of_product f) U"
    and pU: "product_to_cart p \<in> U"
    and C2g: "Ck_on 2 (cart_map_of_product g) V"
    and image: "\<And>v. v \<in> U \<Longrightarrow>
      cart_map_of_product f v \<in> V"
    and inverse: "\<And>v. v \<in> U \<Longrightarrow>
      cart_map_of_product g (cart_map_of_product f v) = v"
    and dA: "A differentiable (at (f p))"
  shows "product_exterior_top (product_pull_near_top f g A) p =
    product_pull_top f (product_exterior_top A) p"
proof -
  let ?F = "cart_map_of_product f"
  let ?G = "cart_map_of_product g"
  let ?B = "cart_form_of_product A"
  let ?v = "product_to_cart p"
  have dB: "?B differentiable (at (?F ?v))"
    using cart_form_of_product_differentiable[OF dA]
    by simp
  have dPB: "pull_near_top ?F ?G ?B differentiable (at ?v)"
    by (rule pull_near_top_differentiable_C2
        [OF C2f pU C2g image[OF pU] dB])
  have lhs: "product_exterior_top (product_pull_near_top f g A) p =
      exterior_top (pull_near_top ?F ?G ?B) ?v"
    unfolding product_pull_near_top_def
    by (rule exterior_top_product_form_of_cart[OF dPB])
  have nat: "exterior_top (pull_near_top ?F ?G ?B) ?v =
      pull_top ?F (exterior_top ?B) ?v"
    by (rule exterior_top_pull_near_top_C2
        [OF C2f pU C2g image inverse dB])
  have rhs: "pull_top ?F (exterior_top ?B) ?v =
      product_pull_top f (product_exterior_top A) p"
    by (simp add: pull_top_def product_pull_top_def
      exterior_top_cart_form_of_product[OF dA])
  show ?thesis
    using lhs nat rhs by simp
qed

theorem product_exterior_top_pull_near_top_C2_on:
  fixes f g A :: "(real \<times> (real ^ 'n::finite)) \<Rightarrow>
      (real \<times> (real ^ 'n))"
  assumes C2f: "Ck_on 2 f W" and pW: "p \<in> W"
    and C2g: "Ck_on 2 g Z"
    and image: "\<And>q. q \<in> W \<Longrightarrow> f q \<in> Z"
    and inverse: "\<And>q. q \<in> W \<Longrightarrow> g (f q) = q"
    and dA: "A differentiable (at (f p))"
  shows "product_exterior_top (product_pull_near_top f g A) p =
    product_pull_top f (product_exterior_top A) p"
proof -
  let ?U = "cart_to_product -` W"
  let ?V = "cart_to_product -` Z"
  have C2F: "Ck_on 2 (cart_map_of_product f) ?U"
    by (rule Ck_on_cart_map_of_product[OF C2f])
  have C2G: "Ck_on 2 (cart_map_of_product g) ?V"
    by (rule Ck_on_cart_map_of_product[OF C2g])
  have pU: "product_to_cart p \<in> ?U"
    using pW by simp
  have image': "\<And>v. v \<in> ?U \<Longrightarrow>
      cart_map_of_product f v \<in> ?V"
    using image by (simp add: cart_map_of_product_def)
  have inverse': "\<And>v. v \<in> ?U \<Longrightarrow>
      cart_map_of_product g (cart_map_of_product f v) = v"
    using inverse by (simp add: cart_map_of_product_def)
  show ?thesis
    by (rule product_exterior_top_pull_near_top_C2
        [OF C2F pU C2G image' inverse' dA])
qed

end
