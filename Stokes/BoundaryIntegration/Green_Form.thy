theory Green_Form
  imports Disk_Stokes
begin

text \<open>The coefficient vector is volume-contracted: its first
  entry is the coefficient of \<open>dy\<close>, and minus its second
  entry is the coefficient of \<open>dx\<close>.\<close>

definition green_chart_field ::
    "(real \<times> (real ^ 1) \<Rightarrow> real) \<Rightarrow>
      (real \<times> (real ^ 1) \<Rightarrow> real) \<Rightarrow>
      real \<times> (real ^ 1) \<Rightarrow>
        real \<times> (real ^ 1)" where
  "green_chart_field P Q p = (Q p, - vec (P p))"

definition green_partial_x ::
    "(real \<times> (real ^ 1) \<Rightarrow> real) \<Rightarrow>
      real \<times> (real ^ 1) \<Rightarrow> real" where
  "green_partial_x f p =
    frechet_derivative f (at p) (1,0)"

definition green_partial_y ::
    "(real \<times> (real ^ 1) \<Rightarrow> real) \<Rightarrow>
      real \<times> (real ^ 1) \<Rightarrow> real" where
  "green_partial_y f p =
    frechet_derivative f (at p) (0,vec 1)"

lemma green_chart_field_coefficients:
  "product_normal_coeff (green_chart_field P Q) x y = Q (x,y)"
  "product_tangential_coeff (green_chart_field P Q)
      (vec 1) x y = P (x,y)"
  by (simp_all add: green_chart_field_def
    product_normal_coeff_def product_tangential_coeff_def
    vector_one_nth inner_vec_def)

lemma green_chart_field_differentiable:
  fixes P Q :: "real \<times> (real ^ 1) \<Rightarrow> real"
  assumes P: "P differentiable (at p)"
    and Q: "Q differentiable (at p)"
  shows "green_chart_field P Q differentiable (at p)"
proof -
  have dv: "(vec :: real \<Rightarrow> real ^ 1)
      differentiable (at (P p))"
    using differentiable_vec[of UNIV]
    by (auto simp: differentiable_on_def)
  have dvec: "(\<lambda>q. vec (P q) :: real ^ 1)
      differentiable (at p)"
    using differentiable_chain_at[OF P dv]
    by (simp add: o_def)
  have dneg: "(\<lambda>q. - vec (P q) :: real ^ 1)
      differentiable (at p)"
    using dvec by (rule differentiable_minus)
  show ?thesis
    unfolding green_chart_field_def
    by (rule differentiable_Pair[OF Q dneg])
qed

lemma green_chart_field_exterior:
  fixes P Q :: "real \<times> (real ^ 1) \<Rightarrow> real"
  assumes P: "P differentiable (at p)"
    and Q: "Q differentiable (at p)"
  shows "product_exterior_top (green_chart_field P Q) p =
    green_partial_x Q p - green_partial_y P p"
proof -
  let ?L = "\<lambda>r::real. - vec r :: real ^ 1"
  have lin: "linear ?L"
    by (rule linearI)
      (simp_all add: vec_eq_iff)
  have bL: "bounded_linear ?L"
    using lin by (simp add: linear_conv_bounded_linear)
  let ?dP = "frechet_derivative P (at p)"
  let ?dQ = "frechet_derivative Q (at p)"
  have dP: "(P has_derivative ?dP) (at p)"
    using P by (rule frechet_derivative_works[THEN iffD1])
  have dQ: "(Q has_derivative ?dQ) (at p)"
    using Q by (rule frechet_derivative_works[THEN iffD1])
  have dL: "(?L has_derivative ?L) (at (P p))"
    by (rule bounded_linear.has_derivative[OF bL]) simp
  have dLP: "((\<lambda>q. ?L (P q)) has_derivative
      (\<lambda>h. ?L (?dP h))) (at p)"
    using has_derivative_compose[OF dP dL]
    by (simp add: o_def)
  have dA: "(green_chart_field P Q has_derivative
      (\<lambda>h. (?dQ h, ?L (?dP h)))) (at p)"
    unfolding green_chart_field_def
    by (rule has_derivative_Pair[OF dQ dLP])
  have deriv: "frechet_derivative (green_chart_field P Q) (at p) =
      (\<lambda>h. (?dQ h, ?L (?dP h)))"
    by (rule frechet_derivative_at[symmetric])
      (rule dA)
  show ?thesis
    by (simp add: product_exterior_top_def
      green_partial_x_def green_partial_y_def
      deriv real_one_vector_Basis vector_one_nth
      inner_vec_def)
qed

definition green_plane_field ::
    "(complex \<Rightarrow> real) \<Rightarrow>
      (complex \<Rightarrow> real) \<Rightarrow>
      real \<times> (real ^ 1) \<Rightarrow>
        real \<times> (real ^ 1)" where
  "green_plane_field P Q =
    green_chart_field
      (P \<circ> halfspace_to_complex)
      (Q \<circ> halfspace_to_complex)"

lemma green_plane_field_coefficients:
  "product_normal_coeff (green_plane_field P Q)
      x y = Q (halfspace_to_complex (x,y))"
  "product_tangential_coeff (green_plane_field P Q)
      (vec 1) x y =
    P (halfspace_to_complex (x,y))"
  by (simp_all add: green_plane_field_def
    green_chart_field_def
    product_normal_coeff_def
    product_tangential_coeff_def
    inner_vec_def)

lemma green_plane_field_boundary:
  "product_boundary_coeff (green_plane_field P Q) y =
    - Q (halfspace_to_complex (0,y))"
  by (simp add: product_boundary_coeff_def
    green_plane_field_coefficients)

lemma green_plane_field_exterior:
  fixes P Q :: "complex \<Rightarrow> real"
  assumes P: "P differentiable
      (at (halfspace_to_complex p))"
    and Q: "Q differentiable
      (at (halfspace_to_complex p))"
  shows "product_exterior_top
      (green_plane_field P Q) p =
    frechet_derivative Q
      (at (halfspace_to_complex p)) 1 -
    frechet_derivative P
      (at (halfspace_to_complex p)) \<i>"
proof -
  let ?z = "halfspace_to_complex p"
  let ?PP = "P \<circ> halfspace_to_complex"
  let ?QQ = "Q \<circ> halfspace_to_complex"
  have dh: "(halfspace_to_complex
      has_derivative halfspace_to_complex) (at p)"
    by (rule bounded_linear.has_derivative
      [OF halfspace_to_complex_bounded_linear])
      simp
  have dPP: "(?PP has_derivative
      (\<lambda>h. frechet_derivative P (at ?z)
        (halfspace_to_complex h))) (at p)"
    using has_derivative_compose
      [OF dh frechet_derivative_works
        [THEN iffD1, OF P]]
    by (simp add: o_def)
  have dQQ: "(?QQ has_derivative
      (\<lambda>h. frechet_derivative Q (at ?z)
        (halfspace_to_complex h))) (at p)"
    using has_derivative_compose
      [OF dh frechet_derivative_works
        [THEN iffD1, OF Q]]
    by (simp add: o_def)
  have PP: "?PP differentiable (at p)"
    using dPP by (auto simp: differentiable_def)
  have QQ: "?QQ differentiable (at p)"
    using dQQ by (auto simp: differentiable_def)
  have FP: "frechet_derivative ?PP (at p) =
      (\<lambda>h. frechet_derivative P (at ?z)
        (halfspace_to_complex h))"
    by (rule frechet_derivative_at[symmetric])
      (rule dPP)
  have FQ: "frechet_derivative ?QQ (at p) =
      (\<lambda>h. frechet_derivative Q (at ?z)
        (halfspace_to_complex h))"
    by (rule frechet_derivative_at[symmetric])
      (rule dQQ)
  have hx: "halfspace_to_complex
      ((1,0)::real \<times> (real ^ 1)) = 1"
    by (simp add: halfspace_to_complex_def
      complex_eq_iff)
  have hy: "halfspace_to_complex
      ((0,1)::real \<times> (real ^ 1)) = \<i>"
    by (simp add: halfspace_to_complex_def
      complex_eq_iff vec_eq_iff)
  show ?thesis
    using green_chart_field_exterior[OF PP QQ]
    by (simp add: green_plane_field_def
      green_partial_x_def green_partial_y_def
      FP FQ hx hy)
qed

theorem closed_unit_disk_stokes_green_chart:
  fixes P Q :: "bool \<Rightarrow>
    real \<times> (real ^ 1) \<Rightarrow> real"
  assumes dP: "\<And>j x. P j differentiable (at x)"
    and dQ: "\<And>j x. Q j differentiable (at x)"
    and pull: "\<And>j k x.
      x \<in> disk_body_overlap j k \<Longrightarrow>
      green_chart_field (P j) (Q j) x =
        product_pull_near_top
          (disk_transition j k)
          (disk_transition k j)
          (green_chart_field (P k) (Q k)) x"
    and cont_Qx: "\<And>j.
      continuous_on closed_halfspace
        (case_prod (product_normal_derivative
          (green_chart_field (P j) (Q j))))"
    and cont_Py: "\<And>j b. b \<in> Basis \<Longrightarrow>
      continuous_on closed_halfspace
        (case_prod (product_tangential_derivative
          (green_chart_field (P j) (Q j)) b))"
  shows "disk_integral_body_top
      (\<lambda>j x. green_partial_x (Q j) x -
        green_partial_y (P j) x) =
    disk_integral_boundary_top
      (\<lambda>j y. - Q j (0,y))"
proof -
  have stokes: "disk_integral_body_top
      (\<lambda>j x. product_exterior_top
        (green_chart_field (P j) (Q j)) x) =
    disk_integral_boundary_top
      (\<lambda>j y. product_boundary_coeff
        (green_chart_field (P j) (Q j)) y)"
    by (rule closed_unit_disk_stokes)
      (use dP dQ pull cont_Qx cont_Py
        in \<open>auto intro: green_chart_field_differentiable\<close>)
  have body_eq: "(\<lambda>j x. product_exterior_top
      (green_chart_field (P j) (Q j)) x) =
    (\<lambda>j x. green_partial_x (Q j) x -
      green_partial_y (P j) x)"
    by (intro ext)
      (rule green_chart_field_exterior[OF dP dQ])
  have boundary_eq: "(\<lambda>j y. product_boundary_coeff
      (green_chart_field (P j) (Q j)) y) =
    (\<lambda>j y. - Q j (0,y))"
    by (intro ext)
      (simp add: green_chart_field_def
        product_boundary_coeff_def
        product_normal_coeff_def)
  show ?thesis
    using stokes by (simp only: body_eq boundary_eq)
qed

end
