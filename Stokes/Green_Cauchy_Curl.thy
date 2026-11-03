theory Green_Cauchy_Curl
  imports Green_Cauchy_Differentiability
begin

definition green_complex_of_pair :: "real \<times> real \<Rightarrow> complex" where
  "green_complex_of_pair p = Complex (fst p) (snd p)"

lemma green_complex_of_pair_bounded_linear:
  "bounded_linear green_complex_of_pair"
  unfolding green_complex_of_pair_def
  by (rule bounded_linear_intro[where K=1])
    (auto simp: norm_complex_def norm_prod_def complex_eq_iff)

definition green_field_of_complex ::
    "(complex \<Rightarrow> complex) \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real" where
  "green_field_of_complex f p =
    (Re (f (green_complex_of_pair p)),
      - Im (f (green_complex_of_pair p)))"

lemma green_field_of_complex_coefficient:
  fixes f :: "complex \<Rightarrow> complex"
  shows "green_contour_coefficient
      (\<lambda>p. fst (green_field_of_complex f p))
      (\<lambda>p. snd (green_field_of_complex f p)) = f"
  by (rule ext) (simp add: green_field_of_complex_def
    green_contour_coefficient_def green_complex_of_pair_def complex_eq_iff)

lemma green_field_of_complex_circulation:
  fixes f :: "complex \<Rightarrow> complex"
  shows "green_circulation (green_field_of_complex f) g =
    Re (contour_integral g f)"
  by (simp add: green_circulation_def green_field_of_complex_coefficient)

definition green_wirtinger_dbar ::
    "(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> complex" where
  "green_wirtinger_dbar f z =
    (frechet_derivative f (at z) 1 +
      \<i> * frechet_derivative f (at z) \<i>) / 2"

lemma green_field_of_complex_curl:
  fixes f :: "complex \<Rightarrow> complex"
  assumes diff: "f differentiable (at (green_complex_of_pair p))"
  shows "green_curl (green_field_of_complex f) p =
    - Im (frechet_derivative f (at (green_complex_of_pair p)) 1) -
      Re (frechet_derivative f (at (green_complex_of_pair p)) \<i>)"
proof -
  let ?E = green_complex_of_pair
  let ?D = "frechet_derivative f (at (?E p))"
  have Eder: "(?E has_derivative ?E) (at p)"
    by (rule bounded_linear.has_derivative
      [OF green_complex_of_pair_bounded_linear has_derivative_ident])
  have fder: "(f has_derivative ?D) (at (?E p))"
    using diff by (simp add: frechet_derivative_works)
  have comp: "((f \<circ> ?E) has_derivative (?D \<circ> ?E)) (at p)"
    by (rule diff_chain_at[OF Eder fder])
  have Pder: "frechet_derivative
      (\<lambda>x. Re (f (?E x))) (at p) = (\<lambda>h. Re (?D (?E h)))"
  proof -
    have rder: "(Re has_derivative Re) (at ((f \<circ> ?E) p))"
      by (rule bounded_linear.has_derivative
        [OF bounded_linear_Re has_derivative_ident])
    have "((Re \<circ> (f \<circ> ?E)) has_derivative
        (Re \<circ> (?D \<circ> ?E))) (at p)"
      by (rule diff_chain_at[OF comp rder])
    then have "Re \<circ> (?D \<circ> ?E) =
        frechet_derivative (Re \<circ> (f \<circ> ?E)) (at p)"
      by (rule frechet_derivative_at)
    then show ?thesis by (simp add: o_def)
  qed
  have Qder: "frechet_derivative
      (\<lambda>x. - Im (f (?E x))) (at p) =
      (\<lambda>h. - Im (?D (?E h)))"
  proof -
    have qlin: "bounded_linear (\<lambda>z::complex. - Im z)"
      by (rule bounded_linear_minus[OF bounded_linear_Im])
    have qder: "((\<lambda>z::complex. - Im z) has_derivative
        (\<lambda>z. - Im z)) (at ((f \<circ> ?E) p))"
      by (rule bounded_linear.has_derivative[OF qlin has_derivative_ident])
    have "(((\<lambda>z::complex. - Im z) \<circ> (f \<circ> ?E))
        has_derivative
        ((\<lambda>z::complex. - Im z) \<circ> (?D \<circ> ?E))) (at p)"
      by (rule diff_chain_at[OF comp qder])
    then have "((\<lambda>z::complex. - Im z) \<circ> (?D \<circ> ?E)) =
        frechet_derivative
          ((\<lambda>z::complex. - Im z) \<circ> (f \<circ> ?E)) (at p)"
      by (rule frechet_derivative_at)
    then show ?thesis by (simp add: o_def)
  qed
  have "green_curl (green_field_of_complex f) p =
      - Im (?D (?E (1,0))) - Re (?D (?E (0,1)))"
    by (simp add: green_curl_def green_field_of_complex_def Pder Qder)
  moreover have "?E (1,0) = 1" "?E (0,1) = \<i>"
    by (simp_all add: green_complex_of_pair_def complex_eq_iff)
  ultimately show ?thesis by simp
qed

lemma green_field_of_complex_curl_dbar:
  fixes f :: "complex \<Rightarrow> complex"
  assumes diff: "f differentiable (at (green_complex_of_pair p))"
  shows "green_curl (green_field_of_complex f) p =
    - 2 * Im (green_wirtinger_dbar f (green_complex_of_pair p))"
  using green_field_of_complex_curl[OF diff]
  by (simp add: green_wirtinger_dbar_def)

definition green_cauchy_field ::
    "(complex \<Rightarrow> complex) \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real" where
  "green_cauchy_field u =
    green_field_of_complex (green_cauchy_area_transform u)"

context green_cauchy_regular_density
begin

lemma green_wirtinger_dbar_density_eq:
  "green_wirtinger_dbar u z =
    (Du z 1 + \<i> * Du z \<i>) / 2"
proof -
  have "frechet_derivative u (at z) = Du z"
    by (rule frechet_derivative_at[symmetric]) (rule uder)
  then show ?thesis
    by (simp add: green_wirtinger_dbar_def)
qed

lemma green_cauchy_area_transform_dbar_integral:
  "green_wirtinger_dbar (green_cauchy_area_transform u) w =
    (\<integral>y. green_wirtinger_dbar u (y + w) / y
      \<partial>(lborel :: complex measure))"
proof -
  let ?M = "(lborel :: complex measure)"
  have deriv: "frechet_derivative (green_cauchy_area_transform u) (at w) =
      (\<lambda>h. \<integral>y. Du (y + w) h / y \<partial>?M)"
    by (rule frechet_derivative_at[symmetric])
      (rule green_cauchy_area_transform_has_derivative)
  have int1: "integrable ?M (\<lambda>y. Du (y + w) 1 / y)"
    by (rule green_cauchy_translated_derivative_integrable
      [OF Du_cont Du_bound Du_supp R D])
  have inti: "integrable ?M (\<lambda>y. Du (y + w) \<i> / y)"
    by (rule green_cauchy_translated_derivative_integrable
      [OF Du_cont Du_bound Du_supp R D])
  have intmul: "integrable ?M
      (\<lambda>y. \<i> * (Du (y + w) \<i> / y))"
    by (rule Bochner_Integration.integrable_mult_right[OF inti])
  have mul_eq: "(\<integral>y. \<i> * (Du (y + w) \<i> / y)
      \<partial>?M) =
      \<i> * (\<integral>y. Du (y + w) \<i> / y \<partial>?M)"
    by (rule Bochner_Integration.integral_mult_right_zero)
  have add_eq: "(\<integral>y. Du (y + w) 1 / y +
      \<i> * (Du (y + w) \<i> / y) \<partial>?M) =
      (\<integral>y. Du (y + w) 1 / y \<partial>?M) +
      (\<integral>y. \<i> * (Du (y + w) \<i> / y) \<partial>?M)"
    by (rule Bochner_Integration.integral_add[OF int1 intmul])
  have "green_wirtinger_dbar (green_cauchy_area_transform u) w =
      ((\<integral>y. Du (y + w) 1 / y \<partial>?M) +
        \<i> * (\<integral>y. Du (y + w) \<i> / y \<partial>?M)) / 2"
    by (simp add: green_wirtinger_dbar_def deriv)
  also have "\<dots> =
      (\<integral>y. (Du (y + w) 1 / y +
        \<i> * (Du (y + w) \<i> / y)) / 2 \<partial>?M)"
    by (simp only: Bochner_Integration.integral_divide_zero
      add_eq mul_eq)
  also have "\<dots> =
      (\<integral>y. (Du (y + w) 1 + \<i> * Du (y + w) \<i>) / 2 / y
        \<partial>?M)"
  proof (rule Bochner_Integration.integral_cong)
    fix y :: complex
    assume "y \<in> space ?M"
    have "(Du (y + w) 1 / y +
        \<i> * (Du (y + w) \<i> / y)) / 2 =
      ((Du (y + w) 1 + \<i> * Du (y + w) \<i>) / y) / 2"
      by (simp only: times_divide_eq_right
        add_divide_distrib[symmetric])
    also have "\<dots> =
      (Du (y + w) 1 + \<i> * Du (y + w) \<i>) / 2 / y"
      by (simp only: divide_inverse ac_simps)
    finally show "(Du (y + w) 1 / y +
        \<i> * (Du (y + w) \<i> / y)) / 2 =
      (Du (y + w) 1 + \<i> * Du (y + w) \<i>) / 2 / y" .
  qed simp
  also have "\<dots> =
      (\<integral>y. green_wirtinger_dbar u (y + w) / y \<partial>?M)"
    by (simp add: green_wirtinger_dbar_density_eq)
  finally show ?thesis .
qed

lemma green_wirtinger_dbar_density_continuous:
  "continuous_on UNIV (green_wirtinger_dbar u)"
proof -
  have eq: "green_wirtinger_dbar u =
      (\<lambda>z. (Du z 1 + \<i> * Du z \<i>) / 2)"
    by (rule ext) (simp add: green_wirtinger_dbar_density_eq)
  show ?thesis
    unfolding eq
    by (intro continuous_intros Du_cont) simp_all
qed

lemma green_wirtinger_dbar_density_bound:
  "norm (green_wirtinger_dbar u z) \<le> D"
proof -
  have tri: "norm (Du z 1 + \<i> * Du z \<i>) \<le>
      norm (Du z 1) + norm (Du z \<i>)"
    using norm_triangle_ineq[of "Du z 1" "\<i> * Du z \<i>"]
    by (simp add: norm_mult)
  have one: "norm (Du z 1) \<le> D"
    using Du_bound[of z 1] by simp
  have ii: "norm (Du z \<i>) \<le> D"
    using Du_bound[of z \<i>] by simp
  show ?thesis
    using tri one ii
    by (simp add: green_wirtinger_dbar_density_eq
      norm_divide)
qed

lemma green_wirtinger_dbar_density_support:
  assumes "z \<notin> cball 0 R"
  shows "green_wirtinger_dbar u z = 0"
  by (simp add: green_wirtinger_dbar_density_eq
    Du_supp[OF assms])

theorem green_cauchy_area_transform_dbar_commute:
  "green_wirtinger_dbar (green_cauchy_area_transform u) w =
    green_cauchy_area_transform (green_wirtinger_dbar u) w"
  by (simp add: green_cauchy_area_transform_dbar_integral
    green_cauchy_area_transform_translate
      [OF green_wirtinger_dbar_density_continuous])

theorem green_cauchy_field_curl_transform:
  "green_curl (green_cauchy_field u) p =
    - 2 * Im (green_cauchy_area_transform
      (green_wirtinger_dbar u) (green_complex_of_pair p))"
proof -
  have diff: "green_cauchy_area_transform u differentiable
      (at (green_complex_of_pair p))"
    unfolding differentiable_def
    using green_cauchy_area_transform_has_derivative by blast
  show ?thesis
    using green_field_of_complex_curl_dbar[OF diff]
    by (simp add: green_cauchy_field_def
      green_cauchy_area_transform_dbar_commute)
qed

lemma green_cauchy_field_curl_integral:
  "green_curl (green_cauchy_field u) p =
    - 2 * Im (\<integral>y.
      green_wirtinger_dbar u (y + green_complex_of_pair p) / y
      \<partial>(lborel :: complex measure))"
  by (simp add: green_cauchy_field_curl_transform
    green_cauchy_area_transform_translate
      [OF green_wirtinger_dbar_density_continuous])

theorem green_cauchy_field_curl_continuous:
  "continuous_on UNIV (green_curl (green_cauchy_field u))"
proof -
  have cont: "continuous_on UNIV
      (green_cauchy_area_transform (green_wirtinger_dbar u))"
    by (rule green_cauchy_area_transform_continuous
      [OF green_wirtinger_dbar_density_continuous
        green_wirtinger_dbar_density_bound
        green_wirtinger_dbar_density_support R D])
  have E: "continuous_on UNIV green_complex_of_pair"
    by (rule bounded_linear.continuous_on
      [OF green_complex_of_pair_bounded_linear])
      (rule continuous_on_id)
  have comp: "continuous_on UNIV
      (green_cauchy_area_transform
        (green_wirtinger_dbar u) \<circ> green_complex_of_pair)"
    unfolding o_def
    by (rule continuous_on_compose2[OF cont E]) simp
  have eq: "green_curl (green_cauchy_field u) =
      (\<lambda>p. - 2 * Im (green_cauchy_area_transform
        (green_wirtinger_dbar u) (green_complex_of_pair p)))"
    by (rule ext) (rule green_cauchy_field_curl_transform)
  show ?thesis
    unfolding eq
    using comp by (auto simp: o_def intro!: continuous_intros)
qed

end

context
  fixes g v :: "real \<Rightarrow> complex"
    and N :: "real set"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (g has_vector_derivative v t) (at t)"
begin

theorem green_ac_cauchy_field_circulation:
  fixes u :: "complex \<Rightarrow> complex"
  assumes uc: "continuous_on UNIV u"
    and C: "\<And>z. norm (u z) \<le> C"
    and supp: "\<And>z. z \<notin> cball 0 R \<Longrightarrow> u z = 0"
    and R: "0 \<le> R"
    and Cnonneg: "0 \<le> C"
    and gb: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (g t) \<le> B"
  shows "green_circulation (green_cauchy_field u) g =
    2 * pi * Im
      (\<integral>z. u z * green_winding_off_path g z
        \<partial>(lborel :: complex measure))"
proof -
  have contour: "contour_integral g (green_cauchy_area_transform u) =
      -(2 * pi * \<i>) *
        (\<integral>z. u z * green_winding_off_path g z
          \<partial>(lborel :: complex measure))"
    by (rule green_ac_cauchy_contour_winding_area(2)
      [where C=C and R=R and B=B])
      (use ac null deriv uc C supp R Cnonneg gb in auto)
  show ?thesis
    using contour
    by (simp add: green_cauchy_field_def
      green_field_of_complex_circulation)
qed

end

end
