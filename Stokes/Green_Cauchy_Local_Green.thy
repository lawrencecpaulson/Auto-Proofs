theory Green_Cauchy_Local_Green
  imports Green_Cauchy_Pompeiu Smooth_Cutoff
begin

lemma green_complex_onorm_basis_bound:
  fixes L :: "complex \<Rightarrow> complex"
  assumes lin: "bounded_linear L"
  shows "onorm L \<le> norm (L 1) + norm (L \<i>)"
proof (rule onorm_bound)
  show "0 \<le> norm (L 1) + norm (L \<i>)" by simp
next
  fix h :: complex
  have decomp: "h = Re h *\<^sub>R 1 + Im h *\<^sub>R \<i>"
    by (simp add: complex_eq_iff)
  have eq: "L h = Re h *\<^sub>R L 1 + Im h *\<^sub>R L \<i>"
    using bounded_linear.linear[OF lin]
    by (subst decomp) (simp add: linear_add linear_scale)
  have "norm (L h) \<le> \<bar>Re h\<bar> * norm (L 1) + \<bar>Im h\<bar> * norm (L \<i>)"
    unfolding eq
    by (rule order_trans[OF norm_triangle_ineq]) simp
  also have "\<dots> \<le> (norm (L 1) + norm (L \<i>)) * norm h"
  proof -
    have a: "\<bar>Re h\<bar> * norm (L 1) \<le> norm h * norm (L 1)"
      by (intro mult_right_mono abs_Re_le_cmod) simp
    have b: "\<bar>Im h\<bar> * norm (L \<i>) \<le> norm h * norm (L \<i>)"
      by (intro mult_right_mono abs_Im_le_cmod) simp
    have "\<bar>Re h\<bar> * norm (L 1) + \<bar>Im h\<bar> * norm (L \<i>)
        \<le> norm h * norm (L 1) + norm h * norm (L \<i>)"
      by (rule add_mono[OF a b])
    then show ?thesis by (simp add: distrib_left mult.commute)
  qed
  finally show "norm (L h) \<le> (norm (L 1) + norm (L \<i>)) * norm h" .
qed

lemma green_continuous_compact_support_uniform:
  fixes f :: "complex \<Rightarrow> complex"
  assumes cont: "continuous_on UNIV f"
    and supp: "\<And>z. z \<notin> cball 0 R \<Longrightarrow> f z = 0"
    and R: "0 \<le> R"
  shows "uniformly_continuous_on UNIV f"
proof -
  have uc: "uniformly_continuous_on (cball 0 (R + 1)) f"
    by (intro compact_uniformly_continuous compact_cball
      continuous_on_subset[OF cont]) auto
  show ?thesis
    unfolding uniformly_continuous_on_def
  proof (intro allI impI)
    fix e :: real
    assume e: "0 < e"
    obtain d where d: "0 < d" and close:
      "\<And>x y. x \<in> cball 0 (R + 1) \<Longrightarrow>
        y \<in> cball 0 (R + 1) \<Longrightarrow>
        dist x y < d \<Longrightarrow> dist (f x) (f y) < e"
      using uc e unfolding uniformly_continuous_on_def by blast
    let ?d = "min d 1"
    have dpos: "0 < ?d" using d by simp
    show "\<exists>d>0. \<forall>x\<in>UNIV. \<forall>y\<in>UNIV.
      dist y x < d \<longrightarrow> dist (f y) (f x) < e"
    proof (intro exI[of _ ?d] conjI ballI impI)
      show "0 < ?d" by (rule dpos)
      fix x y :: complex
      assume xy: "dist y x < ?d"
      have xy1: "dist x y < 1" and xyd: "dist x y < d"
        using xy by (auto simp: dist_commute)
      have ball_y: "y \<in> cball 0 (R + 1)" if "x \<in> cball 0 R"
        using that xy1 dist_triangle[of 0 y x]
        by (auto simp: dist_commute)
      have ball_x: "x \<in> cball 0 (R + 1)" if "y \<in> cball 0 R"
        using that xy1 dist_triangle[of 0 x y]
        by (auto simp: dist_commute)
      have "dist (f x) (f y) < e"
      proof (cases "x \<in> cball 0 R")
        case True
        have xc: "x \<in> cball 0 (R + 1)" using True R by auto
        show ?thesis by (rule close[OF xc ball_y[OF True] xyd])
      next
        case False
        show ?thesis
        proof (cases "y \<in> cball 0 R")
          case True
          have yc: "y \<in> cball 0 (R + 1)" using True R by auto
          show ?thesis by (rule close[OF ball_x[OF True] yc xyd])
        next
          case False
          then show ?thesis using supp[OF \<open>x \<notin> cball 0 R\<close>]
            supp[OF False] e by simp
        qed
      qed
      then show "dist (f y) (f x) < e" by (simp add: dist_commute)
    qed
  qed
qed

lemma green_complex_derivative_modulus:
  fixes Du :: "complex \<Rightarrow> complex \<Rightarrow> complex"
  assumes lin: "\<And>z. bounded_linear (Du z)"
    and cont: "\<And>h. continuous_on UNIV (\<lambda>z. Du z h)"
    and supp: "\<And>z h. z \<notin> cball 0 R \<Longrightarrow> Du z h = 0"
    and R: "0 \<le> R"
    and e: "0 < e"
  shows "\<exists>d>0. \<forall>z z'. norm (z' - z) < d \<longrightarrow>
    onorm (Du z' - Du z) \<le> e"
proof -
  have uc1: "uniformly_continuous_on UNIV (\<lambda>z. Du z 1)"
    by (rule green_continuous_compact_support_uniform[OF cont])
      (use supp R in auto)
  have uci: "uniformly_continuous_on UNIV (\<lambda>z. Du z \<i>)"
    by (rule green_continuous_compact_support_uniform[OF cont])
      (use supp R in auto)
  have e2: "0 < e / 2" using e by simp
  obtain d1 where d1: "0 < d1" and small1:
      "\<And>z z'. dist z' z < d1 \<Longrightarrow>
        dist (Du z' 1) (Du z 1) < e / 2"
    using uc1 e2 unfolding uniformly_continuous_on_def by blast
  obtain di where di: "0 < di" and smalli:
      "\<And>z z'. dist z' z < di \<Longrightarrow>
        dist (Du z' \<i>) (Du z \<i>) < e / 2"
    using uci e2 unfolding uniformly_continuous_on_def by blast
  let ?d = "min d1 di"
  show ?thesis
  proof (intro exI[of _ ?d] conjI allI impI)
    show "0 < ?d" using d1 di by simp
    fix z z' :: complex
    assume zz: "norm (z' - z) < ?d"
    have zz1: "dist z' z < d1" and zzi: "dist z' z < di"
      using zz by (auto simp: dist_norm)
    have bl: "bounded_linear (Du z' - Du z)"
      using lin by (simp add: fun_diff_def bounded_linear_sub)
    have "onorm (Du z' - Du z) \<le>
        norm (Du z' 1 - Du z 1) + norm (Du z' \<i> - Du z \<i>)"
      using green_complex_onorm_basis_bound[OF bl]
      by (simp add: fun_diff_def)
    also have "\<dots> \<le> e"
      using small1[OF zz1] smalli[OF zzi]
      by (simp add: dist_norm)
    finally show "onorm (Du z' - Du z) \<le> e" .
  qed
qed

lemma green_continuous_cball_bound:
  fixes f :: "complex \<Rightarrow> complex"
  assumes cont: "continuous_on UNIV f"
  shows "\<exists>B. \<forall>z\<in>cball 0 R. norm (f z) \<le> B"
proof -
  have fc: "continuous_on (cball 0 R) f"
    by (rule continuous_on_subset[OF cont]) auto
  have "bounded (f ` cball 0 R)"
    by (rule compact_imp_bounded)
      (rule compact_continuous_image[OF fc compact_cball])
  then show ?thesis unfolding bounded_iff by auto
qed

lemma green_compact_C1_regular_density:
  fixes u :: "complex \<Rightarrow> complex"
  assumes diff: "u differentiable_on UNIV"
    and Du_cont: "\<And>h. continuous_on UNIV
      (\<lambda>z. frechet_derivative u (at z) h)"
    and supp: "\<And>z. z \<notin> cball 0 R \<Longrightarrow> u z = 0"
    and R: "0 \<le> R"
  shows "\<exists>C D. green_cauchy_regular_density u
    (\<lambda>z. frechet_derivative u (at z)) C D R"
proof -
  let ?Du = "\<lambda>z. frechet_derivative u (at z)"
  have uc: "continuous_on UNIV u"
    by (rule differentiable_imp_continuous_on[OF diff])
  have uder: "\<And>z. (u has_derivative ?Du z) (at z)"
    using diff by (simp add: differentiable_on_def frechet_derivative_works)
  have lin: "\<And>z. bounded_linear (?Du z)"
    using uder has_derivative_bounded_linear by blast
  have Du_supp: "?Du z h = 0" if z: "z \<notin> cball 0 R" for z h
  proof -
    have eq: "?Du z = frechet_derivative (\<lambda>_::complex. 0) (at z)"
      by (rule frechet_derivative_transform_within_open
        [where s="- cball 0 R"]) (use z supp in auto)
    show ?thesis using eq by simp
  qed
  have modulus: "\<And>e. 0 < e \<Longrightarrow> \<exists>d>0. \<forall>z z'.
      norm (z' - z) < d \<longrightarrow> onorm (?Du z' - ?Du z) \<le> e"
    by (rule green_complex_derivative_modulus[OF lin Du_cont Du_supp R])
  obtain C0 where C0: "\<forall>z\<in>cball 0 R. norm (u z) \<le> C0"
    using green_continuous_cball_bound[OF uc, of R] by blast
  obtain A1 where A1: "\<forall>z\<in>cball 0 R. norm (?Du z 1) \<le> A1"
    using green_continuous_cball_bound[OF Du_cont[of 1], of R] by blast
  obtain Ai where Ai: "\<forall>z\<in>cball 0 R. norm (?Du z \<i>) \<le> Ai"
    using green_continuous_cball_bound[OF Du_cont[of \<i>], of R] by blast
  let ?C = "max 0 C0"
  let ?D = "max 0 A1 + max 0 Ai"
  have ub: "norm (u z) \<le> ?C" for z
    using C0[rule_format, of z] supp[of z] by (cases "z \<in> cball 0 R") (auto intro: order_trans[OF _ max.cobounded2])
  have db1: "norm (?Du z 1) \<le> max 0 A1" for z
    using A1[rule_format, of z] Du_supp[of z 1] by (cases "z \<in> cball 0 R") (auto intro: order_trans[OF _ max.cobounded2])
  have dbi: "norm (?Du z \<i>) \<le> max 0 Ai" for z
    using Ai[rule_format, of z] Du_supp[of z \<i>] by (cases "z \<in> cball 0 R") (auto intro: order_trans[OF _ max.cobounded2])
  have db: "norm (?Du z h) \<le> ?D * norm h" for z h
  proof -
    have "norm (?Du z h) \<le> onorm (?Du z) * norm h"
      by (rule onorm[OF lin])
    also have "\<dots> \<le> ?D * norm h"
      using green_complex_onorm_basis_bound[OF lin[of z]]
        db1[of z] dbi[of z]
      by (intro mult_right_mono) auto
    finally show ?thesis .
  qed
  have gd: "green_cauchy_regular_density u ?Du ?C ?D R"
    by (unfold_locales) (use uc uder Du_cont ub db supp Du_supp
      modulus R in auto)
  show ?thesis using gd by blast
qed

theorem green_ac_contour_dbar_winding_compact_C1:
  fixes u :: "complex \<Rightarrow> complex"
    and g v :: "real \<Rightarrow> complex"
    and N :: "real set"
  assumes diff: "u differentiable_on UNIV"
    and Du_cont: "\<And>h. continuous_on UNIV
      (\<lambda>z. frechet_derivative u (at z) h)"
    and supp: "\<And>z. z \<notin> cball 0 R \<Longrightarrow> u z = 0"
    and R: "0 \<le> R"
    and ac: "absolutely_continuous_on {0..1} g"
    and null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (g has_vector_derivative v t) (at t)"
    and gb: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (g t) \<le> B"
  shows "u contour_integrable_on g"
    and "contour_integral g u = 2 * \<i> *
      (\<integral>z. green_wirtinger_dbar u z * green_winding_off_path g z
        \<partial>(lborel :: complex measure))"
    and "integrable (lborel :: complex measure)
      (\<lambda>z. green_wirtinger_dbar u z * green_winding_off_path g z)"
proof -
  obtain C D where reg: "green_cauchy_regular_density u
    (\<lambda>z. frechet_derivative u (at z)) C D R"
    using green_compact_C1_regular_density[OF diff Du_cont supp R]
    by blast
  interpret gd: green_cauchy_regular_density u
    "\<lambda>z. frechet_derivative u (at z)" C D R
    by (rule reg)
  show "u contour_integrable_on g"
    by (rule gd.green_ac_contour_wirtinger_dbar_winding_area(1)
      [OF ac null deriv gb])
  show "contour_integral g u = 2 * \<i> *
      (\<integral>z. green_wirtinger_dbar u z * green_winding_off_path g z
        \<partial>(lborel :: complex measure))"
    by (rule gd.green_ac_contour_wirtinger_dbar_winding_area(2)
      [OF ac null deriv gb])
  show "integrable (lborel :: complex measure)
      (\<lambda>z. green_wirtinger_dbar u z * green_winding_off_path g z)"
    by (rule green_ac_cauchy_winding_area(1)
      [where g=g and v=v and N=N and C=D and R=R and B=B])
      (use ac null deriv gd.green_wirtinger_dbar_density_continuous
        gd.green_wirtinger_dbar_density_bound
        gd.green_wirtinger_dbar_density_support gd.R gd.D gb in auto)
qed

lemma green_C1_zero_extension:
  fixes f :: "complex \<Rightarrow> complex" and \<phi> :: "complex \<Rightarrow> real"
  assumes openU: "open U"
    and compL: "compact L"
    and LU: "L \<subseteq> U"
    and fC1: "Ck_on 1 f U"
    and \<phi>C1: "Ck_on 1 \<phi> UNIV"
    and \<phi>supp: "{z. \<phi> z \<noteq> 0} \<subseteq> L"
  defines "F \<equiv> \<lambda>z. if z \<in> U then \<phi> z *\<^sub>R f z else 0"
  shows "Ck_on 1 F UNIV"
    and "\<And>z. z \<notin> L \<Longrightarrow> F z = 0"
proof -
  have \<phi>U: "Ck_on 1 \<phi> U"
    by (rule Ck_on_subset[OF \<phi>C1 openU]) auto
  have prod: "Ck_on 1 (\<lambda>z. \<phi> z *\<^sub>R f z) U"
    by (rule Ck_on_bilinear[OF bounded_bilinear_scaleR \<phi>U fC1])
  have FU: "Ck_on 1 F U"
    by (rule Ck_on_congI[OF prod]) (simp add: F_def)
  have zero: "F z = 0" if "z \<notin> L" for z
    using that \<phi>supp by (auto simp: F_def)
  have openL: "open (-L)" by (rule open_Compl[OF compact_imp_closed[OF compL]])
  have Fout: "Ck_on 1 F (-L)"
    by (rule Ck_on_congI[OF Ck_on_const[OF openL]])
      (use zero in auto)
  show "Ck_on 1 F UNIV"
  proof (rule Ck_onI[OF open_UNIV])
    fix z :: complex
    assume "z \<in> UNIV"
    show "Ck_at 1 F z"
    proof (cases "z \<in> U")
      case True
      then show ?thesis by (rule Ck_onD[OF FU])
    next
      case False
      then have "z \<in> - L" using LU by auto
      then show ?thesis by (rule Ck_onD[OF Fout])
    qed
  qed
  show "F z = 0" if "z \<notin> L" for z by (rule zero[OF that])
qed

lemma green_closed_path_winding_support:
  fixes g :: "real \<Rightarrow> complex"
  assumes path: "path g" and loop: "pathfinish g = pathstart g"
    and z: "z \<notin> inside (path_image g)"
  shows "green_winding_off_path g z = 0"
proof (cases "z \<in> path_image g")
  case True
  then show ?thesis by (simp add: green_winding_off_path_def)
next
  case False
  then have "z \<in> outside (path_image g)"
    using z False by (simp add: outside_inside)
  then have "winding_number g z = 0"
    by (rule winding_number_zero_in_outside[OF path loop])
  then show ?thesis using False by (simp add: green_winding_off_path_def)
qed

lemma green_closed_path_filled_compact:
  fixes g :: "real \<Rightarrow> complex"
  assumes path: "path g"
  shows "compact (path_image g \<union> inside (path_image g))"
proof -
  have bdp: "bounded (path_image g)" by (rule bounded_path_image[OF path])
  have bdi: "bounded (inside (path_image g))" by (rule bounded_inside[OF bdp])
  have bdk: "bounded (path_image g \<union> inside (path_image g))"
    using bdp bdi by simp
  have clk: "closed (path_image g \<union> inside (path_image g))"
    by (rule closed_path_image_Un_inside[OF path])
  show ?thesis using bdk clk by (simp add: compact_eq_bounded_closed)
qed

theorem green_ac_contour_dbar_winding_local_C1:
  fixes f :: "complex \<Rightarrow> complex"
    and g v :: "real \<Rightarrow> complex"
    and N :: "real set"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and loop: "pathfinish g = pathstart g"
    and openU: "open U"
    and KU: "path_image g \<union> inside (path_image g) \<subseteq> U"
    and diff: "f differentiable_on U"
    and Dcont: "\<And>h. continuous_on U
      (\<lambda>z. frechet_derivative f (at z) h)"
    and null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (g has_vector_derivative v t) (at t)"
    and gb: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (g t) \<le> B"
  shows "f contour_integrable_on g"
    and "contour_integral g f = 2 * \<i> *
      (\<integral>z. green_wirtinger_dbar f z * green_winding_off_path g z
        \<partial>(lborel :: complex measure))"
    and "integrable (lborel :: complex measure)
      (\<lambda>z. green_wirtinger_dbar f z * green_winding_off_path g z)"
proof -
  let ?K = "path_image g \<union> inside (path_image g)"
  have path: "path g" by (rule green_ac_path_is_path[OF ac])
  have Kcompact: "compact ?K" by (rule green_closed_path_filled_compact[OF path])
  have fat: "\<And>z. z \<in> U \<Longrightarrow> f differentiable (at z)"
  proof -
    fix z assume z: "z \<in> U"
    have "f differentiable (at z within U)"
      by (rule differentiable_onD[OF diff z])
    then show "f differentiable (at z)"
      by (simp only: at_within_open[OF z openU])
  qed
  have fC1: "Ck_on 1 f U"
    using openU fat Dcont by (auto simp: Ck_on_Suc_iff Ck_on_0_iff)
  obtain \<phi> :: "complex \<Rightarrow> real" and L where
    \<phi>C1: "Ck_on 1 \<phi> UNIV"
    and Lcompact: "compact L"
    and LU: "L \<subseteq> U"
    and \<phi>supp: "{z. \<phi> z \<noteq> 0} \<subseteq> L"
    and \<phi>one: "\<And>z. z \<in> ?K \<Longrightarrow> \<phi> z = 1"
    and \<phi>nonneg: "\<And>z. 0 \<le> \<phi> z"
    and \<phi>le: "\<And>z. \<phi> z \<le> 1"
    by (rule euclidean_smooth_compact_cutoff[where k=1, OF Kcompact openU KU]) blast
  let ?F = "\<lambda>z. if z \<in> U then \<phi> z *\<^sub>R f z else 0"
  note Fextension = green_C1_zero_extension
    [OF openU Lcompact LU fC1 \<phi>C1 \<phi>supp]
  have FC1: "Ck_on 1 ?F UNIV" by (rule Fextension(1))
  have FL: "?F z = 0" if "z \<notin> L" for z
    by (rule Fextension(2)[OF that])
  obtain R where R: "0 < R" and LR: "L \<subseteq> ball 0 R"
    using bounded_subset_ballD[OF compact_imp_bounded[OF Lcompact], of 0]
    by blast
  have Fsupp: "?F z = 0" if "z \<notin> cball 0 R" for z
  proof -
    have "z \<notin> L" using that LR by auto
    then show ?thesis by (rule FL)
  qed
  have Fdiff: "?F differentiable_on UNIV"
    using FC1 by (auto simp: Ck_on_Suc_iff differentiable_on_def)
  have FDcont: "\<And>h. continuous_on UNIV
      (\<lambda>z. frechet_derivative ?F (at z) h)"
    using FC1 by (auto simp: Ck_on_Suc_iff Ck_on_0_iff)
  note Fdata = green_ac_contour_dbar_winding_compact_C1
    [OF Fdiff FDcont Fsupp less_imp_le[OF R] ac null deriv gb]
  have Fcint: "?F contour_integrable_on g" by (rule Fdata(1))
  have Fgreen: "contour_integral g ?F = 2 * \<i> *
      (\<integral>z. green_wirtinger_dbar ?F z * green_winding_off_path g z
        \<partial>(lborel :: complex measure))"
    by (rule Fdata(2))
  have Fint: "integrable (lborel :: complex measure)
      (\<lambda>z. green_wirtinger_dbar ?F z * green_winding_off_path g z)"
    by (rule Fdata(3))
  have Feq: "?F z = f z" if "z \<in> ?K" for z
    using that KU \<phi>one[OF that] by auto
  have Feq_path: "\<And>z. z \<in> path_image g \<Longrightarrow> ?F z = f z"
    using Feq by auto
  have cint: "f contour_integrable_on g"
    using Fcint unfolding contour_integrable_on_def
    by (simp only: has_contour_integral_cong[OF Feq_path refl refl])
  show "f contour_integrable_on g" by (rule cint)
  have ceq: "contour_integral g ?F = contour_integral g f"
    by (rule contour_integral_cong[OF refl]) (use Feq in auto)
  have dbar_eq: "green_wirtinger_dbar ?F z = green_wirtinger_dbar f z"
    if z: "z \<in> inside (path_image g)" for z
  proof -
    have openI: "open (inside (path_image g))"
      by (rule open_inside) (rule closed_path_image[OF path])
    have eq: "frechet_derivative ?F (at z) = frechet_derivative f (at z)"
      by (rule frechet_derivative_transform_within_open[OF openI z])
        (use Feq in auto)
    show ?thesis by (simp add: green_wirtinger_dbar_def eq)
  qed
  have area_eq: "(\<lambda>z. green_wirtinger_dbar ?F z * green_winding_off_path g z) =
    (\<lambda>z. green_wirtinger_dbar f z * green_winding_off_path g z)"
  proof (rule ext)
    fix z :: complex
    show "green_wirtinger_dbar ?F z * green_winding_off_path g z =
      green_wirtinger_dbar f z * green_winding_off_path g z"
      by (cases "z \<in> inside (path_image g)")
        (simp_all add: dbar_eq green_closed_path_winding_support[OF path loop])
  qed
  show "contour_integral g f = 2 * \<i> *
      (\<integral>z. green_wirtinger_dbar f z * green_winding_off_path g z
        \<partial>(lborel :: complex measure))"
    using Fgreen by (simp only: ceq area_eq)
  show "integrable (lborel :: complex measure)
      (\<lambda>z. green_wirtinger_dbar f z * green_winding_off_path g z)"
    using Fint by (simp only: area_eq)
qed

theorem green_ac_contour_dbar_winding_C1:
  fixes f :: "complex \<Rightarrow> complex"
    and g :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and loop: "pathfinish g = pathstart g"
    and openU: "open U"
    and KU: "path_image g \<union> inside (path_image g) \<subseteq> U"
    and diff: "f differentiable_on U"
    and Dcont: "\<And>h. continuous_on U
      (\<lambda>z. frechet_derivative f (at z) h)"
  shows "integrable (lborel :: complex measure)
      (\<lambda>z. green_wirtinger_dbar f z * green_winding_off_path g z)"
    and "f contour_integrable_on g"
    and "contour_integral g f = 2 * \<i> *
      (\<integral>z. green_wirtinger_dbar f z * green_winding_off_path g z
        \<partial>(lborel :: complex measure))"
proof -
  let ?N = "{t \<in> {0..1}. \<not> g differentiable (at t)}"
  let ?v = "\<lambda>t. vector_derivative g (at t)"
  have null: "negligible ?N"
    by (rule green_ac_path_derivative_ae[OF ac])
  have deriv: "(g has_vector_derivative ?v t) (at t)"
    if "t \<in> {0..1} - ?N" for t
    using that by (simp add: vector_derivative_works)
  have path: "path g" by (rule green_ac_path_is_path[OF ac])
  obtain B where B: "0 < B" and image: "path_image g \<subseteq> ball 0 B"
    using bounded_subset_ballD[OF bounded_path_image[OF path], of 0]
    by blast
  have gb: "norm (g t) \<le> B" if "t \<in> {0..1}" for t
  proof -
    have "g t \<in> path_image g" using that by (auto simp: path_image_def)
    then have "g t \<in> ball 0 B" using image by blast
    then show ?thesis by auto
  qed
  note loc = green_ac_contour_dbar_winding_local_C1
    [OF ac loop openU KU diff Dcont null deriv gb]
  show "integrable (lborel :: complex measure)
      (\<lambda>z. green_wirtinger_dbar f z * green_winding_off_path g z)"
    by (rule loc(3))
  show "f contour_integrable_on g" by (rule loc(1))
  show "contour_integral g f = 2 * \<i> *
      (\<integral>z. green_wirtinger_dbar f z * green_winding_off_path g z
        \<partial>(lborel :: complex measure))"
    by (rule loc(2))
qed

end
