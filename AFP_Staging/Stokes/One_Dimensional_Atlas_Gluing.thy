theory One_Dimensional_Atlas_Gluing
  imports One_Dimensional_Atlas
begin

theorem Stokes_one_dimensional_finite_atlas_gluing:
  fixes eps :: "'i \<Rightarrow> real"
    and sigma :: "'v \<Rightarrow> real"
    and phi :: "'i \<Rightarrow> 'v \<Rightarrow> real"
    and omega :: "'v \<Rightarrow> real"
    and G g :: "'i \<Rightarrow> real \<Rightarrow> real"
  assumes finiteF: "finite F"
    and finiteB: "finite B"
    and openC: "\<And>i. i \<in> F \<Longrightarrow>
      openin (top_of_set {0::real..}) (C i)"
    and compactK: "\<And>i. i \<in> F \<Longrightarrow>
      compact (K i)"
    and KC: "\<And>i. i \<in> F \<Longrightarrow>
      K i \<subseteq> C i"
    and zeroG: "\<And>i t. i \<in> F \<Longrightarrow>
      t \<in> C i \<Longrightarrow> t \<notin> K i
      \<Longrightarrow> G i t = 0"
    and deriv: "\<And>i t. i \<in> F \<Longrightarrow>
      t \<in> C i \<Longrightarrow>
      (G i has_vector_derivative g i t)
        (at t within {0..})"
    and cont: "\<And>i. i \<in> F \<Longrightarrow>
      continuous_on (C i) (g i)"
    and face: "\<And>i. i \<in> F \<Longrightarrow>
      face i \<longleftrightarrow> 0 \<in> C i"
    and face_point: "\<And>i. i \<in> F \<Longrightarrow>
      face i \<Longrightarrow> point i \<in> B"
    and boundary_value: "\<And>i. i \<in> F \<Longrightarrow>
      face i \<Longrightarrow>
      G i 0 = phi i (point i) * omega (point i)"
    and sign: "\<And>i. i \<in> F \<Longrightarrow>
      face i \<Longrightarrow>
      eps i = sigma (point i)"
    and unity: "\<And>p. p \<in> B \<Longrightarrow>
      omega p \<noteq> 0 \<Longrightarrow>
      (\<Sum>i\<in>F.
        if face i \<and> point i = p then phi i p else 0) = 1"
  shows "(\<Sum>i\<in>F.
      eps i *
        (LINT t : C i | lborel. g i t)) =
    finite_boundary_zero_integral B
      (\<lambda>p. - sigma p * omega p)"
proof -
  have local: "(LINT t : C i | lborel. g i t) =
      (if face i then - G i 0 else 0)"
    if i: "i \<in> F" for i
  proof -
    have eq: "(LINT t : C i | lborel. g i t) =
      finite_boundary_zero_integral
        ({0::real} \<inter> C i) (\<lambda>_. - G i 0)"
      by (rule Stokes_one_dimensional_chart_C1
        [OF openC[OF i] compactK[OF i] KC[OF i]
          zeroG[OF i] deriv[OF i] cont[OF i]])
    show ?thesis
      using eq face[OF i]
      by (auto simp: finite_boundary_zero_integral_def)
  qed
  have body: "(\<Sum>i\<in>F.
      eps i * (LINT t : C i | lborel. g i t)) =
    (\<Sum>i\<in>F.
      if face i then
        - eps i * phi i (point i) * omega (point i)
      else 0)"
  proof (rule sum.cong[OF refl])
    fix i assume i: "i \<in> F"
    show "eps i * (LINT t : C i | lborel. g i t) =
      (if face i then
        - eps i * phi i (point i) * omega (point i)
      else 0)"
      using local[OF i] boundary_value[OF i]
      by (cases "face i") (auto simp: algebra_simps)
  qed
  show ?thesis
    using body
      one_dimensional_boundary_partition_sum
        [where F=F and B=B and face=face and
          point=point and eps=eps and sigma=sigma
          and phi=phi and omega=omega,
          OF finiteF finiteB face_point sign unity]
    by simp
qed

end
