theory Green_Cauchy_Pompeiu
  imports Green_Cauchy_Curl
begin

lemma green_lipschitz_joinpaths_ordered:
  fixes g h :: "real \<Rightarrow> complex"
  assumes g: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow>
      norm (g x - g y) \<le> A * \<bar>x - y\<bar>"
    and h: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow>
      norm (h x - h y) \<le> B * \<bar>x - y\<bar>"
    and join: "g 1 = h 0"
    and A: "0 \<le> A" and B: "0 \<le> B"
    and x: "x \<in> {0..1}" and y: "y \<in> {0..1}"
    and xy: "x \<le> y"
  shows "norm ((g +++ h) x - (g +++ h) y) \<le>
    2 * (A + B) * \<bar>x - y\<bar>"
proof -
  show ?thesis
  proof (cases "y \<le> 1/2")
    case True
    with xy x y have xy': "2*x \<in> {0..1}" "2*y \<in> {0..1}"
      by auto
    have "norm ((g +++ h) x - (g +++ h) y) =
        norm (g (2*x) - g (2*y))"
      using True xy by (simp add: joinpaths_def)
    also have "\<dots> \<le> A * \<bar>2*x - 2*y\<bar>"
      by (rule g[OF xy'])
    also have "\<dots> \<le> 2 * (A + B) * \<bar>x - y\<bar>"
    proof -
      have "A * \<bar>2*x - 2*y\<bar> = (2*A) * \<bar>x-y\<bar>"
      proof -
        have "A * \<bar>2*x - 2*y\<bar> = A * \<bar>2*(x-y)\<bar>"
          by (simp add: algebra_simps)
        also have "\<dots> = (2*A) * \<bar>x-y\<bar>"
          by (simp only: abs_mult)
        finally show ?thesis .
      qed
      also have "\<dots> \<le> (2*(A+B)) * \<bar>x-y\<bar>"
        by (rule mult_right_mono) (use B in simp_all)
      finally show ?thesis .
    qed
    finally show ?thesis .
  next
    case False
    show ?thesis
    proof (cases "1/2 \<le> x")
      case True
      with False x y have xy: "2*x-1 \<in> {0..1}" "2*y-1 \<in> {0..1}"
        by auto
      have "norm ((g +++ h) x - (g +++ h) y) =
          norm (h (2*x-1) - h (2*y-1))"
      proof (cases "x = 1/2")
        case True
        show ?thesis
          unfolding True
          using False join by (simp add: joinpaths_def)
      next
        case False
        then show ?thesis
          using True \<open>\<not> y \<le> 1/2\<close> by (simp add: joinpaths_def)
      qed
      also have "\<dots> \<le> B * \<bar>(2*x-1) - (2*y-1)\<bar>"
        by (rule h[OF xy])
      also have "\<dots> \<le> 2 * (A + B) * \<bar>x - y\<bar>"
      proof -
        have "B * \<bar>(2*x-1) - (2*y-1)\<bar> = (2*B) * \<bar>x-y\<bar>"
        proof -
          have "B * \<bar>(2*x-1) - (2*y-1)\<bar> =
              B * \<bar>2*(x-y)\<bar>"
            by (simp add: algebra_simps)
          also have "\<dots> = (2*B) * \<bar>x-y\<bar>"
            by (simp only: abs_mult)
          finally show ?thesis .
        qed
        also have "\<dots> \<le> (2*(A+B)) * \<bar>x-y\<bar>"
          by (rule mult_right_mono) (use A in simp_all)
        finally show ?thesis .
      qed
      finally show ?thesis .
    next
      case False
      have x2: "2*x \<in> {0..1}" and y2: "2*y-1 \<in> {0..1}"
        using x y False xy \<open>\<not> y \<le> 1/2\<close> by auto
      have val: "(g +++ h) x = g (2*x)"
        using False by (simp add: joinpaths_def)
      have val': "(g +++ h) y = h (2*y-1)"
        using \<open>\<not> y \<le> 1/2\<close> by (simp add: joinpaths_def)
      have tri: "norm (g (2*x) - h (2*y-1)) \<le>
          norm (g (2*x) - g 1) + norm (h 0 - h (2*y-1))"
        using norm_triangle_ineq[of "g (2*x) - g 1" "h 0 - h (2*y-1)"]
        by (simp add: join)
      have gx: "norm (g (2*x) - g 1) \<le> A * (1 - 2*x)"
      proof -
        have bound: "norm (g (2*x) - g 1) \<le> A * \<bar>2*x-1\<bar>"
          by (rule g[OF x2]) simp
        have "2*x-1 < 0" using False by linarith
        then show ?thesis using bound by simp
      qed
      have hy: "norm (h 0 - h (2*y-1)) \<le> B * (2*y - 1)"
      proof -
        have bound: "norm (h 0 - h (2*y-1)) \<le> B * \<bar>0-(2*y-1)\<bar>"
          by (rule h[OF _ y2]) simp
        have "0 < 2*y-1" using \<open>\<not> y \<le> 1/2\<close> by linarith
        then show ?thesis using bound by simp
      qed
      have "norm ((g +++ h) x - (g +++ h) y) \<le>
          A * (1 - 2*x) + B * (2*y - 1)"
        using tri gx hy by (simp add: val val')
      also have "\<dots> \<le> 2 * (A + B) * \<bar>x-y\<bar>"
      proof -
        have ax: "1 - 2*x \<le> 2*(y-x)"
          using y \<open>\<not> y \<le> 1/2\<close> by auto
        have by': "2*y - 1 \<le> 2*(y-x)"
          using x False by auto
        have "A * (1 - 2*x) + B * (2*y - 1) \<le>
            A * (2*(y-x)) + B * (2*(y-x))"
          by (intro add_mono mult_left_mono ax by' A B)
        then show ?thesis using xy by (simp add: algebra_simps)
      qed
      finally show ?thesis .
    qed
  qed
qed

lemma green_lipschitz_joinpaths:
  fixes g h :: "real \<Rightarrow> complex"
  assumes g: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow>
      norm (g x - g y) \<le> A * \<bar>x - y\<bar>"
    and h: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow>
      norm (h x - h y) \<le> B * \<bar>x - y\<bar>"
    and join: "g 1 = h 0"
    and A: "0 \<le> A" and B: "0 \<le> B"
    and x: "x \<in> {0..1}" and y: "y \<in> {0..1}"
  shows "norm ((g +++ h) x - (g +++ h) y) \<le>
    2 * (A + B) * \<bar>x - y\<bar>"
proof (cases "x \<le> y")
  case True
  show ?thesis
    by (rule green_lipschitz_joinpaths_ordered[OF g h join A B x y True])
next
  case False
  have "norm ((g +++ h) y - (g +++ h) x) \<le>
      2 * (A + B) * \<bar>y - x\<bar>"
    by (rule green_lipschitz_joinpaths_ordered[OF g h join A B y x])
      (use False in auto)
  then show ?thesis by (metis abs_minus_commute norm_minus_commute)
qed

lemma green_lipschitz_linepath:
  fixes a b :: complex
  shows "norm (linepath a b x - linepath a b y) \<le>
    norm (b-a) * \<bar>x-y\<bar>"
proof -
  have "linepath a b x - linepath a b y =
      (x-y) *\<^sub>R (b-a)"
    by (simp add: linepath_def algebra_simps)
  then show ?thesis by (simp add: mult.commute)
qed

lemma green_rectpath_absolutely_continuous:
  fixes a b :: complex
  shows "absolutely_continuous_on {0..1} (rectpath a b)"
proof -
  let ?p2 = "Complex (Re b) (Im a)"
  let ?p4 = "Complex (Re a) (Im b)"
  let ?g1 = "linepath a ?p2"
  let ?g2 = "linepath ?p2 b"
  let ?g3 = "linepath b ?p4"
  let ?g4 = "linepath ?p4 a"
  let ?L1 = "norm (?p2-a)"
  let ?L2 = "norm (b-?p2)"
  let ?L3 = "norm (?p4-b)"
  let ?L4 = "norm (a-?p4)"
  let ?L34 = "2*(?L3+?L4)"
  let ?L234 = "2*(?L2+?L34)"
  let ?L = "2*(?L1+?L234)"
  have g34: "norm ((?g3 +++ ?g4) x - (?g3 +++ ?g4) y) \<le>
      ?L34 * \<bar>x-y\<bar>"
    if x: "x \<in> {0..1}" and y: "y \<in> {0..1}" for x y
    by (rule green_lipschitz_joinpaths[OF
      green_lipschitz_linepath green_lipschitz_linepath
      _ _ _ x y]) (simp_all add: joinpaths_def linepath_def)
  have g234: "norm ((?g2 +++ (?g3 +++ ?g4)) x -
      (?g2 +++ (?g3 +++ ?g4)) y) \<le> ?L234 * \<bar>x-y\<bar>"
    if x: "x \<in> {0..1}" and y: "y \<in> {0..1}" for x y
    by (rule green_lipschitz_joinpaths[OF
      green_lipschitz_linepath g34 _ _ _ x y])
      (simp_all add: joinpaths_def linepath_def)
  have glip: "norm ((?g1 +++ (?g2 +++ (?g3 +++ ?g4))) x -
      (?g1 +++ (?g2 +++ (?g3 +++ ?g4))) y) \<le> ?L * \<bar>x-y\<bar>"
    if x: "x \<in> {0..1}" and y: "y \<in> {0..1}" for x y
    by (rule green_lipschitz_joinpaths[OF
      green_lipschitz_linepath g234 _ _ _ x y])
      (simp_all add: joinpaths_def linepath_def)
  have eq: "rectpath a b = ?g1 +++ (?g2 +++ (?g3 +++ ?g4))"
    by (simp add: rectpath_def Let_def)
  show ?thesis
    unfolding eq
    by (rule Lipschitz_imp_absolutely_continuous[OF glip])
qed

lemma green_rectpath_winding_off_path:
  assumes ab: "a < b" and cd: "c < d"
  shows "green_winding_off_path
      (rectpath (Complex a c) (Complex b d)) z =
    (if z \<in> box (Complex a c) (Complex b d) then 1 else 0)"
proof -
  let ?p = "rectpath (Complex a c) (Complex b d)"
  let ?B = "box (Complex a c) (Complex b d)"
  let ?C = "cbox (Complex a c) (Complex b d)"
  have path: "path_image ?p = ?C - ?B"
    by (rule path_image_rectpath_cbox_minus_box) (use ab cd in simp_all)
  show ?thesis
  proof (cases "z \<in> ?B")
    case True
    then have wind: "winding_number ?p z = 1"
      by (rule winding_number_rectpath)
    from True have "z \<notin> path_image ?p"
      using path by simp
    with True wind show ?thesis
      by (simp add: green_winding_off_path_def)
  next
    case False
    note znotB = False
    show ?thesis
    proof (cases "z \<in> ?C")
      case True
      then show ?thesis
        using path znotB by (simp add: green_winding_off_path_def)
    next
      case False
      have "winding_number ?p z = 0"
        by (rule winding_number_rectpath_outside)
          (use ab cd False in simp_all)
      then show ?thesis
        using znotB by (simp add: green_winding_off_path_def)
    qed
  qed
qed

lemma green_rectpath_ac_data:
  fixes a b :: complex
  obtains N B where "negligible N"
    and "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (rectpath a b has_vector_derivative
        vector_derivative (rectpath a b) (at t)) (at t)"
    and "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (rectpath a b t) \<le> B"
proof -
  obtain N where fin: "finite N"
    and diff: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      rectpath a b differentiable (at t)"
    using valid_path_rectpath[of a b]
    by (auto simp: valid_path_def
      piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have "\<exists>B. \<forall>t\<in>{0..1}. norm (rectpath a b t) \<le> B"
    using bounded_path_image[OF path_rectpath[of a b]]
    unfolding path_image_def bounded_iff by blast
  then obtain B where bound: "\<And>t. t \<in> {0..1} \<Longrightarrow>
      norm (rectpath a b t) \<le> B"
    by blast
  show thesis
    by (rule that[of N B])
      (use fin diff bound in
        \<open>auto simp: negligible_finite vector_derivative_works\<close>)
qed

lemma green_field_of_complex_C1:
  fixes f :: "complex \<Rightarrow> complex"
  assumes C1: "Ck_on 1 f UNIV"
  shows "Ck_on 1 (green_field_of_complex f) UNIV"
proof -
  have Ec: "Ck_on 1 green_complex_of_pair UNIV"
    by (rule Ck_on_bounded_linear
      [OF green_complex_of_pair_bounded_linear open_UNIV])
  have comp: "Ck_on 1 (\<lambda>p. f (green_complex_of_pair p)) UNIV"
    by (rule Ck_on_compose[OF C1 Ec]) simp
  have L: "bounded_linear (\<lambda>z::complex. (Re z, - Im z))"
    by (intro bounded_linear_Pair bounded_linear_Re
      bounded_linear_minus[OF bounded_linear_Im])
  show ?thesis
    unfolding green_field_of_complex_def
    by (rule Ck_on_bounded_linear_compose[OF L comp])
qed

lemma green_complex_of_pair_rectangle:
  "green_complex_of_pair p \<in>
    cbox (Complex a c) (Complex b d) \<longleftrightarrow>
    p \<in> {a..b} \<times> {c..d}"
  by (cases p) (auto simp: green_complex_of_pair_def in_cbox_complex_iff)

lemma green_field_of_complex_rectangle_C1_local:
  fixes f :: "complex \<Rightarrow> complex"
  assumes C1: "Ck_on 1 f U"
    and rect: "cbox (Complex a c) (Complex b d) \<subseteq> U"
  shows "green_rectangle_C1
      (\<lambda>p. fst (green_field_of_complex f p))
      (\<lambda>p. snd (green_field_of_complex f p))
      a b c d"
proof -
  let ?V = "green_complex_of_pair -` U"
  let ?S = "{a..b} \<times> {c..d}"
  have openU: "open U" by (rule Ck_on_open[OF C1])
  have cont: "continuous (at p) green_complex_of_pair" for p
    by (rule bounded_linear.continuous
      [OF green_complex_of_pair_bounded_linear continuous_ident])
  have openV: "open ?V"
    by (rule continuous_open_vimage[OF openU cont])
  have EV: "Ck_on 1 green_complex_of_pair ?V"
    by (rule Ck_on_bounded_linear
      [OF green_complex_of_pair_bounded_linear openV])
  have comp: "Ck_on 1 (\<lambda>p. f (green_complex_of_pair p)) ?V"
    by (rule Ck_on_compose[OF C1 EV]) auto
  have L: "bounded_linear (\<lambda>z::complex. (Re z, - Im z))"
    by (intro bounded_linear_Pair bounded_linear_Re
      bounded_linear_minus[OF bounded_linear_Im])
  have Fc: "Ck_on 1 (green_field_of_complex f) ?V"
    unfolding green_field_of_complex_def
    by (rule Ck_on_bounded_linear_compose[OF L comp])
  have Pc: "Ck_on 1
      (\<lambda>p. fst (green_field_of_complex f p)) ?V"
    by (rule Ck_on_bounded_linear_compose[OF bounded_linear_fst Fc])
  have Qc: "Ck_on 1
      (\<lambda>p. snd (green_field_of_complex f p)) ?V"
    by (rule Ck_on_bounded_linear_compose[OF bounded_linear_snd Fc])
  have sub: "?S \<subseteq> ?V"
  proof
    fix p
    assume "p \<in> ?S"
    then have "green_complex_of_pair p \<in>
        cbox (Complex a c) (Complex b d)"
      by (simp add: green_complex_of_pair_rectangle)
    then show "p \<in> ?V" using rect by blast
  qed
  show ?thesis
    using sub Pc Qc by (auto simp: green_rectangle_C1_def)
qed

lemma green_field_of_complex_rectangle_C1:
  fixes f :: "complex \<Rightarrow> complex"
  assumes C1: "Ck_on 1 f UNIV"
  shows "green_rectangle_C1
      (\<lambda>p. fst (green_field_of_complex f p))
      (\<lambda>p. snd (green_field_of_complex f p))
      a b c d"
  by (rule green_field_of_complex_rectangle_C1_local[OF C1]) simp

lemma green_wirtinger_dbar_imul:
  fixes f :: "complex \<Rightarrow> complex"
  assumes diff: "f differentiable (at z)"
  shows "green_wirtinger_dbar (\<lambda>w. \<i> * f w) z =
    \<i> * green_wirtinger_dbar f z"
proof -
  let ?m = "\<lambda>w::complex. \<i> * w"
  let ?Df = "frechet_derivative f (at z)"
  have bl: "bounded_linear ?m"
    by (rule bounded_linear_mult_right)
  have fd: "(f has_derivative ?Df) (at z)"
    using diff by (simp add: frechet_derivative_works)
  have md: "(?m has_derivative ?m) (at (f z))"
    by (rule bounded_linear.has_derivative
      [OF bl has_derivative_ident])
  have comp: "((?m \<circ> f) has_derivative (?m \<circ> ?Df)) (at z)"
    by (rule diff_chain_at[OF fd md])
  have der: "frechet_derivative (\<lambda>w. \<i> * f w) (at z) =
      (\<lambda>h. \<i> * ?Df h)"
    using frechet_derivative_at[OF comp] by (simp add: o_def)
  show ?thesis
    by (simp add: green_wirtinger_dbar_def der algebra_simps)
qed

lemma green_wirtinger_dbar_mult_holomorphic:
  fixes f g :: "complex \<Rightarrow> complex"
  assumes f: "f differentiable (at z)"
    and g: "g field_differentiable (at z)"
  shows "green_wirtinger_dbar (\<lambda>x. f x * g x) z =
    green_wirtinger_dbar f z * g z"
proof -
  obtain g' where dg: "(g has_field_derivative g') (at z)"
    using g by (auto simp: field_differentiable_def)
  have gd: "g differentiable (at z)"
    using g by (rule field_differentiable_imp_differentiable)
  have Dg: "frechet_derivative g (at z) = (\<lambda>h. g' * h)"
    by (rule frechet_derivative_at[symmetric])
      (use dg in \<open>simp add: has_field_derivative_def\<close>)
  have Dfg: "frechet_derivative (\<lambda>x. f x * g x) (at z) =
      (\<lambda>h. f z * (g' * h) +
        frechet_derivative f (at z) h * g z)"
    using frechet_derivative_bilinear[OF bounded_bilinear_mult f gd]
    by (simp add: Dg)
  show ?thesis
    by (simp add: green_wirtinger_dbar_def Dfg algebra_simps)
qed

lemma green_set_integral_Re:
  assumes "set_integrable lborel S f"
  shows
  "Re (LINT x:S|lborel. f x) = (LINT x:S|lborel. Re (f x))"
  using assms
  unfolding set_lebesgue_integral_def
    set_integrable_def
  by (simp add: integral_Re[symmetric] scaleR_conv_of_real)

lemma green_set_integral_Im:
  assumes "set_integrable lborel S f"
  shows
  "Im (LINT x:S|lborel. f x) = (LINT x:S|lborel. Im (f x))"
  using assms
  unfolding set_lebesgue_integral_def
    set_integrable_def
  by (simp add: integral_Im[symmetric] scaleR_conv_of_real)

lemma green_complex_rectangle_contour_C1_local:
  fixes f :: "complex \<Rightarrow> complex"
  assumes ab: "a \<le> b" and cd: "c \<le> d"
    and C1: "Ck_on 1 f U"
    and rect: "cbox (Complex a c) (Complex b d) \<subseteq> U"
  shows "(LINT p:{a..b} \<times> {c..d}|lborel.
      green_wirtinger_dbar f (green_complex_of_pair p)) =
    - (\<i> / 2) * contour_integral
      (rectpath (Complex a c) (Complex b d)) f"
proof -
  let ?S = "{a..b} \<times> {c..d}"
  let ?g = "rectpath (Complex a c) (Complex b d)"
  let ?h = "\<lambda>z. \<i> * f z"
  let ?D = "\<lambda>p. green_wirtinger_dbar f (green_complex_of_pair p)"
  have image: "green_complex_of_pair p \<in> U" if "p \<in> ?S" for p
  proof -
    have "green_complex_of_pair p \<in> cbox (Complex a c) (Complex b d)"
      using that by (simp add: green_complex_of_pair_rectangle)
    then show ?thesis using rect by blast
  qed
  have diff: "f differentiable (at z)" if "z \<in> U" for z
    using C1 that by (simp add: Ck_on_Suc_iff)
  have dOn: "f differentiable (at (green_complex_of_pair p))"
    if "p \<in> ?S" for p
    by (rule diff[OF image[OF that]])
  have hC1: "Ck_on 1 ?h U"
    by (rule Ck_on_bounded_linear_compose
      [OF bounded_linear_mult_right C1])
  have hdOn: "?h differentiable (at (green_complex_of_pair p))"
    if "p \<in> ?S" for p
    using hC1 image[OF that] by (simp add: Ck_on_Suc_iff)
  have deriv_cont: "continuous_on U
      (\<lambda>z. frechet_derivative f (at z) v)" for v
    using C1 by (simp add: Ck_on_Suc_iff Ck_on_0_iff)
  have econt: "continuous_on ?S green_complex_of_pair"
    by (rule bounded_linear.continuous_on
      [OF green_complex_of_pair_bounded_linear continuous_on_id])
  have dcont: "continuous_on ?S
      (\<lambda>p. frechet_derivative f (at (green_complex_of_pair p)) v)"
    for v
    by (rule continuous_on_compose2[OF deriv_cont econt])
      (use image in auto)
  have Dcont: "continuous_on ?S ?D"
    unfolding green_wirtinger_dbar_def
    by (intro continuous_intros dcont) simp_all
  have Dint: "set_integrable lborel ?S ?D"
    using Dcont
    unfolding set_integrable_def
    by (intro borel_integrable_compact compact_Times compact_Icc) auto
  have real_part: "(LINT p:?S|lborel. Im (?D p)) =
      - Re (contour_integral ?g f) / 2"
  proof -
    note G = Green_rectangle_contour_C1[OF ab cd
      green_field_of_complex_rectangle_C1_local[OF C1 rect]]
    have eq: "(LINT p:?S|lborel.
        green_curl (green_field_of_complex f) p) =
        (LINT p:?S|lborel. - 2 * Im (?D p))"
    proof (rule set_lebesgue_integral_cong)
      show "?S \<in> sets (lborel :: (real \<times> real) measure)"
        by (simp add: borel_closed closed_Times)
      show "\<forall>p. p \<in> ?S \<longrightarrow>
        green_curl (green_field_of_complex f) p =
        - 2 * Im (?D p)"
      proof (intro allI impI)
        fix p
        assume p: "p \<in> ?S"
        show "green_curl (green_field_of_complex f) p =
            - 2 * Im (?D p)"
          by (rule green_field_of_complex_curl_dbar[OF dOn[OF p]])
      qed
    qed
    have pull: "(LINT p:?S|lborel. - 2 * Im (?D p)) =
        (-2) * (LINT p:?S|lborel. Im (?D p))"
      unfolding set_lebesgue_integral_def
      by (simp add: scaleR_conv_of_real algebra_simps)
    have G': "(LINT p:?S|lborel.
        green_curl (green_field_of_complex f) p) =
        Re (contour_integral ?g f)"
      using G
      by (simp add: green_curl_def[symmetric]
        green_field_of_complex_coefficient)
    have identity: "(-2) * (LINT p:?S|lborel. Im (?D p)) =
        Re (contour_integral ?g f)"
      using G' eq pull by simp
    show ?thesis using identity by linarith
  qed
  have imag_part: "(LINT p:?S|lborel. Re (?D p)) =
      Im (contour_integral ?g f) / 2"
  proof -
    note G = Green_rectangle_contour_C1[OF ab cd
      green_field_of_complex_rectangle_C1_local[OF hC1 rect]]
    have eq: "(LINT p:?S|lborel.
        green_curl (green_field_of_complex ?h) p) =
        (LINT p:?S|lborel. - 2 * Re (?D p))"
    proof (rule set_lebesgue_integral_cong)
      show "?S \<in> sets (lborel :: (real \<times> real) measure)"
        by (simp add: borel_closed closed_Times)
      show "\<forall>p. p \<in> ?S \<longrightarrow>
        green_curl (green_field_of_complex ?h) p =
        - 2 * Re (?D p)"
      proof (intro allI impI)
        fix p
        assume p: "p \<in> ?S"
        show "green_curl (green_field_of_complex ?h) p =
            - 2 * Re (?D p)"
          using green_field_of_complex_curl_dbar[OF hdOn[OF p]]
            green_wirtinger_dbar_imul[OF dOn[OF p]]
          by simp
      qed
    qed
    have pull: "(LINT p:?S|lborel. - 2 * Re (?D p)) =
        (-2) * (LINT p:?S|lborel. Re (?D p))"
      unfolding set_lebesgue_integral_def
      by (simp add: scaleR_conv_of_real algebra_simps)
    have G': "(LINT p:?S|lborel.
        green_curl (green_field_of_complex ?h) p) =
        Re (contour_integral ?g ?h)"
      using G
      by (simp add: green_curl_def[symmetric]
        green_field_of_complex_coefficient)
    have identity: "(-2) * (LINT p:?S|lborel. Re (?D p)) =
        Re (contour_integral ?g ?h)"
      using G' eq pull by simp
    show ?thesis
      using identity
      by (simp add: contour_integral_lmul; linarith)
  qed
  show ?thesis
    using real_part imag_part
    by (simp add: complex_eq_iff green_set_integral_Re
      green_set_integral_Im Dint)
qed

lemma green_complex_rectangle_contour_C1:
  fixes f :: "complex \<Rightarrow> complex"
  assumes ab: "a \<le> b" and cd: "c \<le> d"
    and C1: "Ck_on 1 f UNIV"
  shows "(LINT p:{a..b} \<times> {c..d}|lborel.
      green_wirtinger_dbar f (green_complex_of_pair p)) =
    - (\<i> / 2) * contour_integral
      (rectpath (Complex a c) (Complex b d)) f"
  by (rule green_complex_rectangle_contour_C1_local[OF ab cd C1]) simp

lemma green_cauchy_rectangle_exterior:
  fixes u :: "complex \<Rightarrow> complex"
  assumes ab: "a \<le> b" and cd: "c \<le> d"
    and C1: "Ck_on 1 u V"
    and rect: "cbox (Complex a c) (Complex b d) \<subseteq> V"
    and wout: "w \<notin> cbox (Complex a c) (Complex b d)"
  shows "contour_integral
      (rectpath (Complex a c) (Complex b d))
      (\<lambda>z. u z / (z - w)) =
    2 * \<i> * (LINT p:{a..b} \<times> {c..d}|lborel.
      green_wirtinger_dbar u (green_complex_of_pair p) /
        (green_complex_of_pair p - w))"
proof -
  let ?S = "{a..b} \<times> {c..d}"
  let ?U = "V - {w}"
  let ?g = "\<lambda>z. inverse (z - w)"
  let ?f = "\<lambda>z. u z / (z - w)"
  have openV: "open V" by (rule Ck_on_open[OF C1])
  have openU: "open ?U" using openV by (simp add: open_Diff)
  have rectU: "cbox (Complex a c) (Complex b d) \<subseteq> ?U"
    using rect wout by blast
  have uC1: "Ck_on 1 u ?U"
    by (rule Ck_on_subset[OF C1 openU]) auto
  have denC1: "Ck_on 1 (\<lambda>z. z - w) ?U"
    by (intro Ck_on_sub Ck_on_id Ck_on_const openU)
  have gC1: "Ck_on 1 ?g ?U"
    by (rule Ck_on_inverse[OF denC1]) auto
  have fC1: "Ck_on 1 ?f ?U"
    unfolding divide_inverse by (rule Ck_on_mult[OF uC1 gC1])
  have image: "green_complex_of_pair p \<in>
      cbox (Complex a c) (Complex b d)" if "p \<in> ?S" for p
    using that by (simp add: green_complex_of_pair_rectangle)
  have dbar_eq: "green_wirtinger_dbar ?f (green_complex_of_pair p) =
      green_wirtinger_dbar u (green_complex_of_pair p) /
        (green_complex_of_pair p - w)" if "p \<in> ?S" for p
  proof -
    let ?z = "green_complex_of_pair p"
    have zU: "?z \<in> ?U" using image[OF that] rectU by blast
    have ud: "u differentiable (at ?z)"
      using uC1 zU by (simp add: Ck_on_Suc_iff)
    have gd: "?g field_differentiable (at ?z)"
      using zU by (auto intro!: derivative_intros)
    show ?thesis
      using green_wirtinger_dbar_mult_holomorphic[OF ud gd]
      by (simp add: divide_inverse)
  qed
  have Green: "(LINT p:?S|lborel.
      green_wirtinger_dbar ?f (green_complex_of_pair p)) =
      - (\<i> / 2) * contour_integral
        (rectpath (Complex a c) (Complex b d)) ?f"
    by (rule green_complex_rectangle_contour_C1_local
      [OF ab cd fC1 rectU])
  have eq: "(LINT p:?S|lborel.
      green_wirtinger_dbar ?f (green_complex_of_pair p)) =
      (LINT p:?S|lborel.
        green_wirtinger_dbar u (green_complex_of_pair p) /
          (green_complex_of_pair p - w))"
  proof (rule set_lebesgue_integral_cong)
    show "?S \<in> sets (lborel :: (real \<times> real) measure)"
      by (simp add: borel_closed closed_Times)
    show "\<forall>p. p \<in> ?S \<longrightarrow>
      green_wirtinger_dbar ?f (green_complex_of_pair p) =
      green_wirtinger_dbar u (green_complex_of_pair p) /
        (green_complex_of_pair p - w)"
      using dbar_eq by blast
  qed
  show ?thesis using Green eq by (simp add: algebra_simps)
qed

lemma green_complex_rectangle_set_integral:
  fixes f :: "complex \<Rightarrow> complex"
  assumes cont: "continuous_on UNIV f"
  shows "(LINT z:cbox (Complex a c) (Complex b d)|lborel. f z) =
    (LINT p:{a..b} \<times> {c..d}|lborel.
      f (green_complex_of_pair p))"
proof -
  let ?E = green_complex_of_pair
  let ?S = "cbox (Complex a c) (Complex b d)"
  have Eeq: "?E = (\<lambda>(x,y). Complex x y)"
    by (rule ext) (auto simp: green_complex_of_pair_def)
  have Emeas: "?E \<in> measurable (lborel :: (real \<times> real) measure)
      (borel :: complex measure)"
    using green_complex_pair_measurable Eeq by simp
  have distr_eq: "distr (lborel :: (real \<times> real) measure)
      borel ?E = (lborel :: complex measure)"
    using lborel_distr_complex_pair Eeq by simp
  have Hmeas: "(\<lambda>z. indicator ?S z *\<^sub>R f z) \<in>
      borel_measurable (borel :: complex measure)"
    using cont
    by (intro borel_measurable_scaleR)
      (auto intro!: borel_measurable_continuous_onI)
  have pull: "?E -` ?S = {a..b} \<times> {c..d}"
    by (auto simp: green_complex_of_pair_rectangle)
  have mem: "?E p \<in> ?S \<longleftrightarrow> p \<in> {a..b} \<times> {c..d}" for p
    using pull by auto
  have "(LINT z:?S|lborel. f z) =
      (\<integral>p. indicator ?S (?E p) *\<^sub>R f (?E p)
        \<partial>(lborel :: (real \<times> real) measure))"
    unfolding set_lebesgue_integral_def
    using integral_distr[OF Emeas Hmeas]
    by (simp only: distr_eq)
  also have "\<dots> =
      (LINT p:{a..b} \<times> {c..d}|lborel. f (?E p))"
    by (simp add: set_lebesgue_integral_def indicator_def mem)
  finally show ?thesis .
qed

lemma green_box_cbox_set_integral:
  fixes f :: "complex \<Rightarrow> complex"
  assumes cont: "continuous_on UNIV f"
  shows "(LINT z:box a b|lborel. f z) =
    (LINT z:cbox a b|lborel. f z)"
proof -
  have meas: "f \<in> borel_measurable (lborel :: complex measure)"
    using cont by (simp add: borel_measurable_continuous_onI)
  have ae: "AE z in (lborel :: complex measure).
      z \<in> box a b \<longleftrightarrow> z \<in> cbox a b"
  proof (rule eventually_mono
      [OF AE_not_in[OF null_sets_cbox_Diff_box[of a b]]])
    fix z :: complex
    assume "z \<notin> cbox a b - box a b"
    then show "z \<in> box a b \<longleftrightarrow> z \<in> cbox a b"
      using box_subset_cbox by auto
  qed
  show ?thesis
  proof (rule set_integral_cong_set[OF _ _ ae, symmetric])
    show "set_borel_measurable lborel (box a b) f"
      using meas by (simp add: set_borel_measurable_def)
    show "set_borel_measurable lborel (cbox a b) f"
      using meas by (simp add: set_borel_measurable_def)
  qed
qed

lemma green_continuous_zero_from_rectangles:
  fixes f :: "complex \<Rightarrow> complex"
  assumes cont: "continuous_on UNIV f"
    and zero: "\<And>a b. box a b \<noteq> {} \<Longrightarrow>
      (LINT z:cbox a b|lborel. f z) = 0"
  shows "f w = 0"
proof (rule ccontr)
  assume nonzero: "f w \<noteq> 0"
  let ?F = "\<lambda>z. cnj (f w) * f z"
  let ?g = "\<lambda>z. Re (?F z)"
  let ?A = "{z. 0 < ?g z}"
  have Fc: "continuous_on UNIV ?F"
    by (intro continuous_intros cont)
  have gc: "continuous_on UNIV ?g"
    by (intro continuous_intros Fc)
  have pos: "0 < ?g w"
    using nonzero
    by (simp add: mult.commute complex_mult_cnj
      sum_power2_gt_zero_iff complex_eq_iff)
  have Aopen: "open ?A"
    by (rule open_Collect_less[OF continuous_on_const gc])
  have win: "w \<in> ?A" using pos by simp
  obtain a b where sub: "cbox a b \<subseteq> ?A"
    and wbox: "w \<in> box a b"
    by (rule open_contains_cbox[OF Aopen win])
  have box_ne: "box a b \<noteq> {}"
    using wbox by auto
  have Fint: "set_integrable lborel (cbox a b) ?F"
    using Fc unfolding set_integrable_def
    by (intro borel_integrable_compact compact_cbox)
      (auto intro: continuous_on_subset)
  have gint: "set_integrable lborel (cbox a b) ?g"
    using gc unfolding set_integrable_def
    by (intro borel_integrable_compact compact_cbox)
      (auto intro: continuous_on_subset)
  have F0: "(LINT z:cbox a b|lborel. ?F z) = 0"
    by (simp only: set_integral_mult_right zero[OF box_ne]
      mult_zero_right)
  have gint0: "(LINT z:cbox a b|lborel. ?g z) = 0"
  proof -
    have eq: "(LINT z:cbox a b|lborel. ?g z) =
        Re (LINT z:cbox a b|lborel. ?F z)"
      by (rule green_set_integral_Re[OF Fint, symmetric])
    show ?thesis using eq
      by (simp only: F0; simp)
  qed
  have gi: "?g integrable_on cbox a b"
    by (rule set_borel_integral_eq_integral(1)[OF gint])
  have g0: "integral (cbox a b) ?g = 0"
    using gint0 set_borel_integral_eq_integral(2)[OF gint]
    by simp
  have hk: "(?g has_integral 0) (cbox a b)"
    using integrable_integral[OF gi] g0 by simp
  have wz: "w \<in> cbox a b"
    using wbox box_subset_cbox by auto
  have gcbox: "continuous_on (cbox a b) ?g"
    using gc by (rule continuous_on_subset) auto
  have nonneg: "0 \<le> ?g z" if "z \<in> box a b" for z
  proof -
    have "z \<in> cbox a b"
      using that by (rule subsetD[OF box_subset_cbox])
    then have "z \<in> ?A" by (rule subsetD[OF sub])
    then show ?thesis by simp
  qed
  have "?g w = 0"
    by (rule has_integral_0_cbox_imp_0
      [OF gcbox nonneg hk box_ne wz])
  with pos show False by simp
qed

context green_cauchy_regular_density
begin

lemma green_cauchy_rectpath_contour_area:
  assumes ab: "a < b" and cd: "c < d"
  shows "contour_integral
      (rectpath (Complex a c) (Complex b d))
      (green_cauchy_area_transform u) =
    -(2 * pi * \<i>) *
      (LINT z:box (Complex a c) (Complex b d)|lborel. u z)"
proof -
  let ?g = "rectpath (Complex a c) (Complex b d)"
  let ?V = "\<lambda>t. vector_derivative ?g (at t)"
  obtain N B where null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (?g has_vector_derivative ?V t) (at t)"
    and bound: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (?g t) \<le> B"
    using green_rectpath_ac_data[of "Complex a c" "Complex b d"]
    by blast
  have contour: "contour_integral ?g
      (green_cauchy_area_transform u) =
      -(2 * pi * \<i>) *
        (\<integral>z. u z * green_winding_off_path ?g z
          \<partial>(lborel :: complex measure))"
    by (rule green_ac_cauchy_contour_winding_area(2)
      [where C=C and R=R and B=B and v="?V" and N=N])
      (use green_rectpath_absolutely_continuous
        null deriv uc u_bound u_supp R C bound in auto)
  have eq: "(\<lambda>z. u z * green_winding_off_path ?g z) =
      (\<lambda>z. indicator (box (Complex a c) (Complex b d)) z *\<^sub>R u z)"
    by (rule ext)
      (simp add: green_rectpath_winding_off_path[OF ab cd] indicator_def)
  show ?thesis
    using contour by (simp only: eq set_lebesgue_integral_def)
qed

lemma green_cauchy_rectangle_dbar_integral:
  assumes ab: "a < b" and cd: "c < d"
  shows "(LINT p:{a..b} \<times> {c..d}|lborel.
      green_wirtinger_dbar (green_cauchy_area_transform u)
        (green_complex_of_pair p)) =
    - pi * (LINT p:{a..b} \<times> {c..d}|lborel.
      u (green_complex_of_pair p))"
proof -
  let ?g = "rectpath (Complex a c) (Complex b d)"
  have box_eq: "(LINT z:box (Complex a c) (Complex b d)|lborel. u z) =
      (LINT p:{a..b} \<times> {c..d}|lborel.
        u (green_complex_of_pair p))"
    using green_box_cbox_set_integral[OF uc,
      of "Complex a c" "Complex b d"]
      green_complex_rectangle_set_integral[OF uc,
        of a c b d]
    by simp
  have green: "(LINT p:{a..b} \<times> {c..d}|lborel.
      green_wirtinger_dbar (green_cauchy_area_transform u)
        (green_complex_of_pair p)) =
    - (\<i> / 2) * contour_integral ?g
      (green_cauchy_area_transform u)"
    by (rule green_complex_rectangle_contour_C1
      [OF less_imp_le[OF ab] less_imp_le[OF cd]
        green_cauchy_area_transform_C1])
  have area: "contour_integral ?g
      (green_cauchy_area_transform u) =
      -(2 * pi * \<i>) *
        (LINT p:{a..b} \<times> {c..d}|lborel.
          u (green_complex_of_pair p))"
    using green_cauchy_rectpath_contour_area[OF ab cd]
    by (simp only: box_eq)
  show ?thesis using green area by (simp add: algebra_simps)
qed

theorem green_cauchy_area_transform_dbar_inverse:
  "green_cauchy_area_transform (green_wirtinger_dbar u) w =
    - pi * u w"
proof -
  let ?T = green_cauchy_area_transform
  let ?D = "green_wirtinger_dbar (?T u)"
  let ?h = "\<lambda>z. ?D z + pi * u z"
  have Tc: "continuous_on UNIV
      (?T (green_wirtinger_dbar u))"
    by (rule green_cauchy_area_transform_continuous
      [OF green_wirtinger_dbar_density_continuous
        green_wirtinger_dbar_density_bound
        green_wirtinger_dbar_density_support R D])
  have Deq: "?D = ?T (green_wirtinger_dbar u)"
    by (rule ext) (rule green_cauchy_area_transform_dbar_commute)
  have Dc: "continuous_on UNIV ?D"
    using Tc by (simp only: Deq)
  have hc: "continuous_on UNIV ?h"
    by (intro continuous_intros Dc uc)
  have zero: "(LINT z:cbox a b|lborel. ?h z) = 0"
    if ne: "box a b \<noteq> {}" for a b :: complex
  proof -
    let ?A = "Re a"
    let ?B = "Re b"
    let ?C = "Im a"
    let ?E = "Im b"
    let ?S = "{?A..?B} \<times> {?C..?E}"
    let ?e = green_complex_of_pair
    obtain z where z: "z \<in> box a b"
      using ne by auto
    have ab: "?A < ?B" and cd: "?C < ?E"
      using z by (auto simp: in_box_complex_iff)
    have ec: "continuous_on UNIV ?e"
      by (rule bounded_linear.continuous_on
        [OF green_complex_of_pair_bounded_linear])
        (rule continuous_on_id)
    have Dpc: "continuous_on UNIV (\<lambda>p. ?D (?e p))"
      by (rule continuous_on_compose2[OF Dc ec]) auto
    have upc: "continuous_on UNIV (\<lambda>p. u (?e p))"
      by (rule continuous_on_compose2[OF uc ec]) auto
    have Dint: "set_integrable lborel ?S (\<lambda>p. ?D (?e p))"
      using Dpc unfolding set_integrable_def
      by (intro borel_integrable_compact compact_Times)
        (auto intro: continuous_on_subset)
    have uint: "set_integrable lborel ?S (\<lambda>p. u (?e p))"
      using upc unfolding set_integrable_def
      by (intro borel_integrable_compact compact_Times)
        (auto intro: continuous_on_subset)
    have pair0: "(LINT p:?S|lborel. ?h (?e p)) = 0"
      using green_cauchy_rectangle_dbar_integral[OF ab cd]
      by (simp add: set_integral_add[OF Dint
        set_integrable_mult_right[OF uint]])
    have "(LINT z:cbox (Complex ?A ?C) (Complex ?B ?E)|lborel.
        ?h z) = 0"
      using green_complex_rectangle_set_integral[OF hc,
        of ?A ?C ?B ?E] pair0 by simp
    then show ?thesis by simp
  qed
  have "?h w = 0"
    by (rule green_continuous_zero_from_rectangles[OF hc zero])
  then have eq: "?T (green_wirtinger_dbar u) w =
      - (pi * u w)"
    by (simp only: Deq eq_neg_iff_add_eq_0)
  show ?thesis using eq by (simp add: algebra_simps)
qed

theorem green_cauchy_area_transform_dbar_right_inverse:
  "green_wirtinger_dbar (green_cauchy_area_transform u) w =
    - pi * u w"
  by (simp add: green_cauchy_area_transform_dbar_commute
    green_cauchy_area_transform_dbar_inverse)

theorem green_ac_contour_wirtinger_dbar_winding_area:
  fixes g v :: "real \<Rightarrow> complex"
    and N :: "real set"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (g has_vector_derivative v t) (at t)"
    and gb: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (g t) \<le> B"
  shows "u contour_integrable_on g"
    and "contour_integral g u =
      2 * \<i> * (\<integral>z. green_wirtinger_dbar u z *
        green_winding_off_path g z \<partial>(lborel :: complex measure))"
proof -
  have ucg: "continuous_on (path_image g) u"
    by (rule continuous_on_subset[OF uc]) simp
  show "u contour_integrable_on g"
    by (rule green_ac_contour_integrable[OF ac null])
      (use deriv ucg in \<open>auto\<close>)
  have contour: "contour_integral g
      (green_cauchy_area_transform (green_wirtinger_dbar u)) =
      -(2 * pi * \<i>) *
        (\<integral>z. green_wirtinger_dbar u z *
          green_winding_off_path g z \<partial>(lborel :: complex measure))"
    by (rule green_ac_cauchy_contour_winding_area(2)
      [where C=D and R=R and B=B and v=v and N=N])
      (use ac null deriv green_wirtinger_dbar_density_continuous
        green_wirtinger_dbar_density_bound
        green_wirtinger_dbar_density_support R D gb in \<open>auto\<close>)
  have transform_eq:
    "green_cauchy_area_transform (green_wirtinger_dbar u) =
      (\<lambda>z. - pi * u z)"
    by (rule ext) (rule green_cauchy_area_transform_dbar_inverse)
  have "- pi * contour_integral g u =
      -(2 * pi * \<i>) *
        (\<integral>z. green_wirtinger_dbar u z *
          green_winding_off_path g z \<partial>(lborel :: complex measure))"
    using contour
    by (simp only: transform_eq contour_integral_lmul)
  then show "contour_integral g u =
      2 * \<i> * (\<integral>z. green_wirtinger_dbar u z *
        green_winding_off_path g z \<partial>(lborel :: complex measure))"
    by (simp add: mult.assoc)
qed

end

end
