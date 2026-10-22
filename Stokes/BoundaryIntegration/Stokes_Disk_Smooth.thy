theory Stokes_Disk_Smooth
  imports Stokes_Body_Local_Integration
    Stokes_Disk_Atlas
begin

lemma real_one_vector_Basis:
  "(Basis :: (real ^ 1) set) = {vec 1}"
  by (auto simp: Basis_vec_def axis_def
    vec_eq_iff)

lemma halfspace_to_complex_Basis:
  "halfspace_to_complex `
      (Basis :: (real \<times> (real ^ 1)) set) =
    (Basis :: complex set)"
  by (auto simp: Basis_prod_def
    real_one_vector_Basis Basis_complex_def
    halfspace_to_complex_def zero_prod_def
    vec_eq_iff complex_eq_iff)

lemma product_complex_det_linear:
  fixes L :: "real \<times> (real ^ 1) \<Rightarrow>
    real \<times> (real ^ 1)"
  assumes L: "linear L"
  shows "eucl.det L =
    eucl.det (halfspace_to_complex \<circ> L \<circ>
      complex_to_halfspace)"
proof -
  have inj_h: "inj halfspace_to_complex"
    by (rule injI)
      (metis complex_halfspace_inverse)
  have surj_h: "surj halfspace_to_complex"
    unfolding surj_def
    by (metis halfspace_complex_inverse)
  have bij_h: "bij halfspace_to_complex"
    using inj_h surj_h by (simp add: bij_def)
  have basis_h: "bij_betw halfspace_to_complex
      (Basis :: (real \<times> (real ^ 1)) set)
      (Basis :: complex set)"
  proof -
    have "inj_on halfspace_to_complex
        (Basis :: (real \<times> (real ^ 1)) set)"
      by (rule inj_onI)
        (erule injD[OF inj_h])
    then show ?thesis
      using halfspace_to_complex_Basis
      by (simp add: bij_betw_def)
  qed
  have inv_h: "inv halfspace_to_complex =
      complex_to_halfspace"
    by (rule ext)
      (metis inj_h inv_f_f
        halfspace_complex_inverse)
  have det: "eucl.det L =
      eucl.det (halfspace_to_complex \<circ> L \<circ>
        inv halfspace_to_complex)"
  proof (rule finite_dimensional_vector_space_pair.det_basis_change)
    show "finite_dimensional_vector_space_pair
        (scaleR :: real \<Rightarrow>
          (real \<times> (real ^ 1)) \<Rightarrow> _)
        (Basis :: (real \<times> (real ^ 1)) set)
        (scaleR :: real \<Rightarrow> complex \<Rightarrow> _)
        (Basis :: complex set)"
      by unfold_locales
    show "Vector_Spaces.linear
        (scaleR :: real \<Rightarrow>
          (real \<times> (real ^ 1)) \<Rightarrow> _)
        (scaleR :: real \<Rightarrow> complex \<Rightarrow> _)
        halfspace_to_complex"
      using bounded_linear.linear
        [OF halfspace_to_complex_bounded_linear]
      by (simp add: linear_def)
    show "bij_betw halfspace_to_complex
        (Basis :: (real \<times> (real ^ 1)) set)
        (Basis :: complex set)"
      by (rule basis_h)
  qed
  show ?thesis
    using det by (simp only: inv_h)
qed

lemma disk_transition_extension_has_derivative:
  fixes x :: "real \<times> (real ^ 1)"
  assumes x: "x \<noteq> 0"
  defines "w \<equiv> halfspace_to_complex x"
  shows "(disk_transition_extension has_derivative
    (\<lambda>h. complex_to_halfspace
      (- (inverse w * halfspace_to_complex h *
        inverse w)))) (at x)"
proof -
  have wn: "w \<noteq> 0"
    using x halfspace_to_complex_nonzero
    by (simp add: w_def)
  have dh: "(halfspace_to_complex
      has_derivative halfspace_to_complex) (at x)"
    by (rule bounded_linear.has_derivative
      [OF halfspace_to_complex_bounded_linear])
      simp
  have dinv: "(inverse has_derivative
      (\<lambda>h. - (inverse w * h * inverse w)))
      (at w)"
    by (rule Deriv.has_derivative_inverse'[OF wn])
  have di: "((\<lambda>y. inverse (halfspace_to_complex y))
      has_derivative
      (\<lambda>h. - (inverse w *
        halfspace_to_complex h * inverse w)))
      (at x)"
    using has_derivative_compose[OF dh dinv[unfolded w_def]]
    by (simp add: o_def w_def)
  have dc: "(complex_to_halfspace
      has_derivative complex_to_halfspace)
      (at (inverse w))"
    by (rule bounded_linear.has_derivative
      [OF complex_to_halfspace_bounded_linear])
      simp
  show ?thesis
    unfolding disk_transition_extension_def
    using has_derivative_compose[OF di dc[unfolded w_def]]
    by (simp add: o_def w_def)
qed

lemma complex_multiplication_det:
  fixes a :: complex
  shows "eucl.det ((*) a) = (norm a)\<^sup>2"
  by (simp add: det_complex cmod_power2
    power2_eq_square[symmetric])

lemma disk_transition_extension_positive_det:
  fixes x :: "real \<times> (real ^ 1)"
  assumes x: "x \<noteq> 0"
  shows "0 < eucl.det
    (frechet_derivative disk_transition_extension (at x))"
proof -
  let ?w = "halfspace_to_complex x"
  let ?a = "- (inverse ?w * inverse ?w)"
  have wn: "?w \<noteq> 0"
    by (rule halfspace_to_complex_nonzero[OF x])
  have an: "?a \<noteq> 0"
    using wn by simp
  have d: "frechet_derivative disk_transition_extension (at x) =
      (\<lambda>h. complex_to_halfspace
        (- (inverse ?w * halfspace_to_complex h *
          inverse ?w)))"
    by (rule frechet_derivative_at[symmetric])
      (rule disk_transition_extension_has_derivative[OF x, simplified])
  have eq: "halfspace_to_complex \<circ>
      frechet_derivative disk_transition_extension (at x) \<circ>
      complex_to_halfspace = ((*) ?a)"
    by (rule ext)
      (simp add: d o_def mult_ac)
  have lin: "linear
      (frechet_derivative disk_transition_extension (at x))"
    using d by (auto intro: has_derivative_linear
      disk_transition_extension_has_derivative[OF x])
  show ?thesis
    using product_complex_det_linear[OF lin]
      complex_multiplication_det[of ?a] an
    by (simp add: eq)
qed

definition disk_overlap :: "bool \<Rightarrow> bool \<Rightarrow> (real \<times> (real ^ 1)) set" where
  "disk_overlap i j =
    halfspace_atlas.coordinate_overlap disk_domain
      (\<lambda>_. closed_halfspace ::
        (real \<times> (real ^ 1)) set)
      disk_from_chart i j"

definition disk_transition :: "bool \<Rightarrow> bool \<Rightarrow>
    (real \<times> (real ^ 1)) \<Rightarrow>
      (real \<times> (real ^ 1))" where
  "disk_transition i j =
    halfspace_atlas.coordinate_transition
      disk_to_chart disk_from_chart i j"

lemma disk_overlap_open:
  "openin (top_of_set closed_halfspace)
    (disk_overlap i j)"
  unfolding disk_overlap_def
  by (rule halfspace_atlas.coordinate_overlap_open
    [OF disk_halfspace_atlas]) simp_all

lemma disk_overlap_open_rep:
  "\<exists>W. open W \<and>
    disk_overlap i j = closed_halfspace \<inter> W"
  using disk_overlap_open[of i j]
  unfolding openin_open by blast

lemma disk_overlap_interior_open:
  "open (disk_overlap i j \<inter>
    open_halfspace)"
proof -
  obtain W where W: "open W"
    "disk_overlap i j = closed_halfspace \<inter> W"
    using disk_overlap_open_rep[of i j] by blast
  have sub: "open_halfspace \<subseteq>
      (closed_halfspace ::
        (real \<times> (real ^ 1)) set)"
    by (auto simp: open_halfspace_def
      closed_halfspace_def)
  have eq: "disk_overlap i j \<inter>
      open_halfspace = W \<inter> open_halfspace"
    using W(2) sub by blast
  show ?thesis
    unfolding eq
    by (rule open_Int[OF W(1)
      open_open_halfspace])
qed

lemma disk_interior_transition_eq:
  assumes x: "x \<in> disk_overlap i j \<inter>
    open_halfspace"
  shows "disk_transition i j x =
    (if i = j then x else
      disk_transition_extension x)"
proof (cases "i = j")
  case True
  have xc: "x \<in> closed_halfspace"
    using x by (auto simp: open_halfspace_def
      closed_halfspace_def)
  show ?thesis
    using disk_to_from[OF xc] True
    by (simp add: disk_transition_def
      halfspace_atlas.coordinate_transition_def
        [OF disk_halfspace_atlas])
next
  case False
  have xc: "x \<in> closed_halfspace"
    using x by (auto simp: open_halfspace_def
      closed_halfspace_def)
  show ?thesis
    using disk_other_chart_transition[OF xc, of i] False
    by (cases i; cases j)
      (simp_all add: disk_transition_def
        halfspace_atlas.coordinate_transition_def
          [OF disk_halfspace_atlas])
qed

lemma disk_interior_transition_C2:
  "Ck_on 2 (disk_transition i j)
    (disk_overlap i j \<inter>
      open_halfspace)"
proof (cases "i = j")
  case True
  have c2: "Ck_on 2 id
      (disk_overlap i j \<inter>
        open_halfspace)"
    using disk_overlap_interior_open
    by (simp add: id_def Ck_on_id)
  show ?thesis
    by (rule Ck_on_congI[OF c2])
      (use True disk_interior_transition_eq in auto)
next
  case False
  let ?U = "disk_overlap i j \<inter>
      open_halfspace"
  have sub: "?U \<subseteq> UNIV - {0}"
    by (auto simp: open_halfspace_def
      zero_prod_def)
  have c2: "Ck_on 2 disk_transition_extension ?U"
    by (rule Ck_on_subset
      [OF disk_transition_extension_C2
        disk_overlap_interior_open sub])
  show ?thesis
    by (rule Ck_on_congI[OF c2])
      (use False disk_interior_transition_eq in auto)
qed

lemma disk_interior_transition_positive_det:
  assumes x: "x \<in> disk_overlap i j \<inter>
    open_halfspace"
  shows "0 < eucl.det (frechet_derivative
    (disk_transition i j) (at x))"
proof (cases "i = j")
  case True
  have eq: "frechet_derivative
      (disk_transition i j) (at x) =
      frechet_derivative id (at x)"
    by (rule frechet_derivative_transform_within_open
      [OF disk_overlap_interior_open x])
      (use True disk_interior_transition_eq in auto)
  show ?thesis
    by (simp add: eq)
next
  case False
  have eq: "frechet_derivative
      (disk_transition i j) (at x) =
      frechet_derivative disk_transition_extension
        (at x)"
    by (rule frechet_derivative_transform_within_open
      [OF disk_overlap_interior_open x])
      (use False disk_interior_transition_eq in auto)
  have nz: "x \<noteq> 0"
    using x by (auto simp: open_halfspace_def
      zero_prod_def)
  show ?thesis
    using disk_transition_extension_positive_det[OF nz]
    by (simp add: eq)
qed

lemma disk_smooth_oriented_C2_halfspace_atlas:
  "smooth_oriented_C2_halfspace_atlas
    disk_carrier (UNIV::bool set) disk_domain
    (\<lambda>_. closed_halfspace ::
      (real \<times> (real ^ 1)) set)
    disk_to_chart disk_from_chart"
proof (rule smooth_oriented_C2_halfspace_atlas.intro)
  show "positively_oriented_C2_halfspace_atlas
      disk_carrier (UNIV::bool set) disk_domain
      (\<lambda>_. closed_halfspace ::
        (real \<times> (real ^ 1)) set)
      disk_to_chart disk_from_chart"
    by (rule disk_positively_oriented_C2_halfspace_atlas)
  show "smooth_oriented_C2_halfspace_atlas_axioms
      (UNIV::bool set) disk_domain
      (\<lambda>_. closed_halfspace ::
        (real \<times> (real ^ 1)) set)
      disk_to_chart disk_from_chart"
  proof (rule smooth_oriented_C2_halfspace_atlas_axioms.intro)
    fix i j :: bool
    assume "i \<in> (UNIV::bool set)" "j \<in> (UNIV::bool set)"
    show "Ck_on 2
        (halfspace_atlas.coordinate_transition
          disk_to_chart disk_from_chart i j)
        (halfspace_atlas.coordinate_overlap
          disk_domain
          (\<lambda>_. closed_halfspace ::
            (real \<times> (real ^ 1)) set)
          disk_from_chart i j \<inter>
          open_halfspace)"
      using disk_interior_transition_C2[of i j]
      by (simp only: disk_transition_def
        disk_overlap_def)
  next
    fix i j :: bool and x :: "real \<times> (real ^ 1)"
    assume "i \<in> (UNIV::bool set)"
      "j \<in> (UNIV::bool set)"
      and x: "x \<in>
        halfspace_atlas.coordinate_overlap disk_domain
          (\<lambda>_. closed_halfspace ::
            (real \<times> (real ^ 1)) set)
          disk_from_chart i j \<inter> open_halfspace"
    show "0 < eucl.det (frechet_derivative
        (halfspace_atlas.coordinate_transition
          disk_to_chart disk_from_chart i j) (at x))"
      using disk_interior_transition_positive_det
        [of x i j] x
      by (simp only: disk_transition_def
        disk_overlap_def)
  qed
qed

end
