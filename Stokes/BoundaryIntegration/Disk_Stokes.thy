theory Disk_Stokes
  imports Global_Gluing Disk_Smooth
begin

definition disk_body_overlap ::
    "bool \<Rightarrow> bool \<Rightarrow>
      (real \<times> (real ^ 1)) set" where
  "disk_body_overlap i j =
    positively_oriented_C2_halfspace_atlas.body_overlap
      disk_domain
      (\<lambda>_. closed_halfspace ::
        (real \<times> (real ^ 1)) set)
      disk_from_chart i j"

definition disk_integral_body_top ::
    "(bool \<Rightarrow> real \<times> (real ^ 1) \<Rightarrow> real)
      \<Rightarrow> real" where
  "disk_integral_body_top alpha =
    smooth_oriented_C2_halfspace_atlas.integral_body_top
      disk_carrier (UNIV::bool set) disk_domain
      (\<lambda>_. closed_halfspace ::
        (real \<times> (real ^ 1)) set)
      disk_to_chart disk_from_chart alpha"

definition disk_integral_boundary_top ::
    "(bool \<Rightarrow> real ^ 1 \<Rightarrow> real)
      \<Rightarrow> real" where
  "disk_integral_boundary_top beta =
    positively_oriented_C2_halfspace_atlas.integral_boundary_top
      disk_carrier (UNIV::bool set) disk_domain
      (\<lambda>_. closed_halfspace ::
        (real \<times> (real ^ 1)) set)
      disk_to_chart disk_from_chart beta"

lemma disk_body_overlap_eq:
  "disk_body_overlap i j =
    disk_overlap i j \<inter> open_halfspace"
  by (simp add: disk_body_overlap_def
    disk_overlap_def
    positively_oriented_C2_halfspace_atlas.body_overlap_def
      [OF disk_positively_oriented_C2_halfspace_atlas])

lemma closed_unit_disk_boundary:
  "halfspace_atlas.boundary_carrier
    disk_carrier (UNIV::bool set)
    disk_domain disk_to_chart = sphere 0 1"
  by (rule disk_boundary_carrier)

text \<open>Stokes on the closed unit disk, represented by two
  smooth Cayley halfspace charts.\<close>

theorem closed_unit_disk_stokes:
  fixes A :: "bool \<Rightarrow>
    real \<times> (real ^ 1) \<Rightarrow>
      real \<times> (real ^ 1)"
  assumes dA: "\<And>j x.
      x \<in> closed_halfspace \<Longrightarrow>
      A j differentiable (at x)"
    and pull: "\<And>j k x.
      x \<in> disk_body_overlap j k \<Longrightarrow>
      A j x = product_pull_near_top
        (disk_transition j k)
        (disk_transition k j)
        (A k) x"
    and cont_AP: "\<And>j.
      continuous_on closed_halfspace
        (case_prod
          (product_normal_derivative (A j)))"
    and cont_AQ: "\<And>j b. b \<in> Basis \<Longrightarrow>
      continuous_on closed_halfspace
        (case_prod
          (product_tangential_derivative (A j) b))"
  shows "disk_integral_body_top
      (\<lambda>j x. product_exterior_top (A j) x) =
    disk_integral_boundary_top
      (\<lambda>j y. product_boundary_coeff (A j) y)"
proof -
  have pull': "A j x = product_pull_near_top
      (halfspace_atlas.coordinate_transition
        disk_to_chart disk_from_chart j k)
      (halfspace_atlas.coordinate_transition
        disk_to_chart disk_from_chart k j)
      (A k) x"
    if "x \<in>
      positively_oriented_C2_halfspace_atlas.body_overlap
        disk_domain
        (\<lambda>_. closed_halfspace ::
          (real \<times> (real ^ 1)) set)
        disk_from_chart j k" for j k x
    using pull[of x j k] that
    by (simp only: disk_body_overlap_def
      disk_transition_def)
  show ?thesis
    unfolding disk_integral_body_top_def
      disk_integral_boundary_top_def
    by (rule smooth_oriented_C2_halfspace_atlas.global_stokes_compact_carrier
      [OF disk_smooth_oriented_C2_halfspace_atlas
        disk_carrier_compact])
      (use dA pull' cont_AP cont_AQ in auto)
qed

end
