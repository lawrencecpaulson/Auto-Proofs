theory Disk_Atlas
  imports Boundary_Charts
begin

text \<open>Two Cayley charts for the closed unit disk.  Both charts use the
  inward half-plane as coordinate model.  Their transition on the
  overlap is complex inversion.\<close>

definition disk_carrier :: "complex set" where
  "disk_carrier = cball 0 1"

definition disk_puncture :: "bool \<Rightarrow> complex" where
  "disk_puncture b = (if b then 1 else -1)"

definition disk_domain :: "bool \<Rightarrow> complex set" where
  "disk_domain b = disk_carrier - {disk_puncture b}"

definition disk_mobius :: "complex \<Rightarrow> complex" where
  "disk_mobius z = (1 - z) / (1 + z)"

definition disk_cayley :: "bool \<Rightarrow> complex \<Rightarrow> complex" where
  "disk_cayley b z =
    (if b then (1 + z) / (1 - z)
      else (1 - z) / (1 + z))"

definition disk_uncayley :: "bool \<Rightarrow> complex \<Rightarrow> complex" where
  "disk_uncayley b w =
    (if b then (w - 1) / (w + 1)
      else (1 - w) / (1 + w))"

definition complex_to_halfspace ::
    "complex \<Rightarrow> real \<times> (real ^ 1)" where
  "complex_to_halfspace z = (Re z, vec (Im z))"

definition halfspace_to_complex ::
    "real \<times> (real ^ 1) \<Rightarrow> complex" where
  "halfspace_to_complex x =
    Complex (fst x) ((snd x) $ 1)"

definition disk_to_chart ::
    "bool \<Rightarrow> complex \<Rightarrow> real \<times> (real ^ 1)" where
  "disk_to_chart b z =
    complex_to_halfspace (disk_cayley b z)"

definition disk_from_chart ::
    "bool \<Rightarrow> real \<times> (real ^ 1) \<Rightarrow> complex" where
  "disk_from_chart b x =
    disk_uncayley b (halfspace_to_complex x)"

lemma halfspace_complex_inverse [simp]:
  "halfspace_to_complex (complex_to_halfspace z) = z"
  by (simp add: halfspace_to_complex_def
    complex_to_halfspace_def complex_eq_iff)

lemma complex_halfspace_inverse [simp]:
  "complex_to_halfspace (halfspace_to_complex x) = x"
  by (cases x)
     (simp add: halfspace_to_complex_def
       complex_to_halfspace_def vector_one_nth)

lemma complex_in_closed_halfspace:
  "complex_to_halfspace z \<in> closed_halfspace
    \<longleftrightarrow> 0 \<le> Re z"
  by (simp add: complex_to_halfspace_def
    closed_halfspace_def)

lemma disk_cayley_Re_true:
  "Re (disk_cayley True z) =
    (1 - (norm z)\<^sup>2) / (norm (1 - z))\<^sup>2"
  by (simp add: disk_cayley_def Re_divide'
    cmod_power2 power2_eq_square algebra_simps;
    metis cmod_power2 power2_eq_square add.commute)

lemma disk_cayley_Re_false:
  "Re (disk_cayley False z) =
    (1 - (norm z)\<^sup>2) / (norm (1 + z))\<^sup>2"
  by (simp add: disk_cayley_def Re_divide'
    cmod_power2 power2_eq_square algebra_simps;
    metis cmod_power2 power2_eq_square add.commute)

lemma disk_domain_iff:
  "z \<in> disk_domain b \<longleftrightarrow>
    norm z \<le> 1 \<and> z \<noteq> disk_puncture b"
  by (simp add: disk_domain_def disk_carrier_def
    dist_norm)

lemma disk_domain_cover:
  "disk_carrier \<subseteq>
    disk_domain True \<union> disk_domain False"
  by (auto simp: disk_domain_def disk_puncture_def)

lemma disk_domain_open:
  "openin (top_of_set disk_carrier) (disk_domain b)"
  by (auto simp: disk_domain_def openin_open
    intro!: exI[of _ "- {disk_puncture b}"])

lemma disk_puncture_outside:
  assumes "z \<in> disk_domain b"
  shows "(if b then 1 - z else 1 + z) \<noteq> 0"
  using assms by (cases b)
    (auto simp: disk_domain_iff disk_puncture_def
      add_eq_0_iff2 neg_eq_iff_add_eq_0)

lemma disk_mobius_involutive:
  assumes nz: "1 + z \<noteq> 0"
  shows "disk_mobius (disk_mobius z) = z"
proof -
  have top: "1 - disk_mobius z =
      (2 * z) / (1 + z)"
    using nz
    by (simp add: disk_mobius_def
      diff_divide_eq_iff algebra_simps)
  have bot: "1 + disk_mobius z =
      2 / (1 + z)"
    using nz
    by (simp add: disk_mobius_def
      add_divide_eq_iff algebra_simps)
  have "disk_mobius (disk_mobius z) =
      (1 - disk_mobius z) /
        (1 + disk_mobius z)"
    by (simp add: disk_mobius_def)
  also have "\<dots> = ((2 * z) / (1 + z)) /
      (2 / (1 + z))"
    by (simp add: top bot)
  also have "\<dots> = z"
    using nz
    by (simp add: divide_divide_eq_left')
  finally show ?thesis .
qed

lemma disk_cayley_as_mobius:
  "disk_cayley b z =
    disk_mobius (if b then - z else z)"
  by (cases b)
    (simp_all add: disk_cayley_def disk_mobius_def)

lemma disk_uncayley_as_mobius:
  "disk_uncayley b w =
    (if b then - disk_mobius w else disk_mobius w)"
  by (cases b)
    (simp_all add: disk_uncayley_def disk_mobius_def
      minus_divide_left)

lemma disk_uncayley_cayley:
  assumes "z \<in> disk_domain b"
  shows "disk_uncayley b (disk_cayley b z) = z"
proof (cases b)
  case True
  have nz: "1 - z \<noteq> 0"
    using disk_puncture_outside[OF assms] True by simp
  show ?thesis
    using True nz
    by (simp add: disk_cayley_as_mobius
      disk_uncayley_as_mobius
      disk_mobius_involutive)
next
  case False
  have nz: "1 + z \<noteq> 0"
    using disk_puncture_outside[OF assms] False by simp
  show ?thesis
    using False nz
    by (simp add: disk_cayley_as_mobius
      disk_uncayley_as_mobius
      disk_mobius_involutive)
qed

lemma right_halfplane_not_minus_one:
  assumes "0 \<le> Re w"
  shows "w + 1 \<noteq> 0"
  using assms by (auto simp: add_eq_0_iff2)

lemma disk_cayley_uncayley:
  assumes "0 \<le> Re w"
  shows "disk_cayley b (disk_uncayley b w) = w"
proof (cases b)
  case True
  have nz: "w + 1 \<noteq> 0"
    by (rule right_halfplane_not_minus_one[OF assms])
  show ?thesis
    using True nz
    by (simp add: disk_cayley_as_mobius
      disk_uncayley_as_mobius
      disk_mobius_involutive add.commute)
next
  case False
  have nz: "w + 1 \<noteq> 0"
    by (rule right_halfplane_not_minus_one[OF assms])
  show ?thesis
    using False nz
    by (simp add: disk_cayley_as_mobius
      disk_uncayley_as_mobius
      disk_mobius_involutive add.commute)
qed

lemma disk_cayley_in_halfplane:
  assumes z: "z \<in> disk_domain b"
  shows "0 \<le> Re (disk_cayley b z)"
proof -
  have norm: "norm z \<le> 1"
    using z by (simp add: disk_domain_iff)
  have num: "0 \<le> 1 - (norm z)\<^sup>2"
    using norm by (simp add: abs_square_le_1)
  show ?thesis
  proof (cases b)
    case True
    then show ?thesis
      using num disk_cayley_Re_true[of z]
      by simp
  next
    case False
    then show ?thesis
      using num disk_cayley_Re_false[of z]
      by simp
  qed
qed

lemma disk_mobius_not_minus_one:
  assumes nz: "1 + w \<noteq> 0"
  shows "disk_mobius w \<noteq> -1"
proof -
  have "1 + disk_mobius w = 2 / (1 + w)"
    using nz
    by (simp add: disk_mobius_def
      add_divide_eq_iff algebra_simps)
  then show ?thesis
    using nz by (auto simp: add_eq_0_iff2)
qed

lemma disk_mobius_norm_le_one:
  assumes re: "0 \<le> Re w"
  shows "norm (disk_mobius w) \<le> 1"
proof -
  have nz: "1 + w \<noteq> 0"
    using right_halfplane_not_minus_one[OF re]
    by (simp add: add.commute)
  have denom: "0 < norm (1 + w)"
    using nz by simp
  have eq: "(norm (1 + w))\<^sup>2 -
      (norm (1 - w))\<^sup>2 = 4 * Re w"
    by (simp add: cmod_power2; algebra)
  have sq: "(norm (1 - w))\<^sup>2 \<le>
      (norm (1 + w))\<^sup>2"
    using eq re by linarith
  have le: "norm (1 - w) \<le> norm (1 + w)"
    by (rule power2_le_imp_le[OF sq norm_ge_zero])
  show ?thesis
    using denom le
    by (simp add: disk_mobius_def
      norm_divide divide_le_eq)
qed

lemma disk_uncayley_in_domain:
  assumes re: "0 \<le> Re w"
  shows "disk_uncayley b w \<in> disk_domain b"
proof -
  have nz: "1 + w \<noteq> 0"
    using right_halfplane_not_minus_one[OF re]
    by (simp add: add.commute)
  have norm: "norm (disk_uncayley b w) \<le> 1"
    using disk_mobius_norm_le_one[OF re]
    by (simp add: disk_uncayley_as_mobius
      split: if_splits)
  have puncture: "disk_uncayley b w \<noteq>
      disk_puncture b"
    using disk_mobius_not_minus_one[OF nz]
    by (cases b)
      (auto simp: disk_uncayley_as_mobius
        disk_puncture_def neg_eq_iff_add_eq_0
        add_eq_0_iff2)
  show ?thesis
    by (simp add: disk_domain_iff norm puncture)
qed

lemma disk_to_chart_continuous:
  "continuous_on (disk_domain b) (disk_to_chart b)"
proof -
  have nz: "\<And>z. z \<in> disk_domain b \<Longrightarrow>
      (if b then 1 - z else 1 + z) \<noteq> 0"
    by (rule disk_puncture_outside)
  have cayley: "continuous_on (disk_domain b)
      (disk_cayley b)"
  proof (cases b)
    case True
    have "continuous_on (disk_domain True)
      (\<lambda>z. (1 + z) / (1 - z))"
      by (intro continuous_intros)
        (use nz True in auto)
    then show ?thesis
      by (simp add: True disk_cayley_def)
  next
    case False
    have "continuous_on (disk_domain False)
      (\<lambda>z. (1 - z) / (1 + z))"
      by (intro continuous_intros)
        (use nz False in auto)
    then show ?thesis
      by (simp add: False disk_cayley_def)
  qed
  show ?thesis
    unfolding disk_to_chart_def
      complex_to_halfspace_def vec_def
    by (intro continuous_intros cayley)
qed

lemma disk_from_chart_continuous:
  "continuous_on
    (closed_halfspace :: (real \<times> (real ^ 1)) set)
    (disk_from_chart b)"
proof -
  have nz: "\<And>x. x \<in>
      (closed_halfspace :: (real \<times> (real ^ 1)) set)
      \<Longrightarrow> 1 + halfspace_to_complex x \<noteq> 0"
  proof -
    fix x :: "real \<times> (real ^ 1)"
    assume x: "x \<in> closed_halfspace"
    have re: "0 \<le> Re (halfspace_to_complex x)"
      using x by (simp add: closed_halfspace_def
        halfspace_to_complex_def)
    have "halfspace_to_complex x + 1 \<noteq> 0"
      by (rule right_halfplane_not_minus_one[OF re])
    then show "1 + halfspace_to_complex x \<noteq> 0"
      by (simp add: add.commute)
  qed
  have cont: "continuous_on
      (closed_halfspace :: (real \<times> (real ^ 1)) set)
      halfspace_to_complex"
    unfolding halfspace_to_complex_def
    by (intro continuous_intros)
  show ?thesis
  proof (cases b)
    case True
    have "continuous_on
        (closed_halfspace :: (real \<times> (real ^ 1)) set)
        (\<lambda>x. (halfspace_to_complex x - 1) /
          (halfspace_to_complex x + 1))"
      by (intro continuous_intros cont)
        (metis nz add.commute)
    then show ?thesis
      by (simp add: True disk_from_chart_def
        disk_uncayley_def)
  next
    case False
    have "continuous_on
        (closed_halfspace :: (real \<times> (real ^ 1)) set)
        (\<lambda>x. (1 - halfspace_to_complex x) /
          (1 + halfspace_to_complex x))"
      by (intro continuous_intros cont)
        (metis nz)
    then show ?thesis
      by (simp add: False disk_from_chart_def
        disk_uncayley_def)
  qed
qed

lemma disk_to_chart_in_halfspace:
  assumes "z \<in> disk_domain b"
  shows "disk_to_chart b z \<in> closed_halfspace"
  using disk_cayley_in_halfplane[OF assms]
  by (simp add: disk_to_chart_def
    complex_in_closed_halfspace)

lemma disk_from_chart_in_domain:
  assumes "x \<in> (closed_halfspace ::
      (real \<times> (real ^ 1)) set)"
  shows "disk_from_chart b x \<in> disk_domain b"
proof -
  have "0 \<le> Re (halfspace_to_complex x)"
    using assms
    by (simp add: halfspace_to_complex_def
      closed_halfspace_def)
  then show ?thesis
    by (simp add: disk_from_chart_def
      disk_uncayley_in_domain)
qed

lemma disk_from_to [simp]:
  assumes "z \<in> disk_domain b"
  shows "disk_from_chart b (disk_to_chart b z) = z"
  using assms
  by (simp add: disk_from_chart_def
    disk_to_chart_def disk_uncayley_cayley)

lemma disk_to_from [simp]:
  assumes "x \<in> (closed_halfspace ::
      (real \<times> (real ^ 1)) set)"
  shows "disk_to_chart b (disk_from_chart b x) = x"
proof -
  have re: "0 \<le> Re (halfspace_to_complex x)"
    using assms
    by (simp add: halfspace_to_complex_def
      closed_halfspace_def)
  show ?thesis
    by (simp add: disk_to_chart_def
      disk_from_chart_def
      disk_cayley_uncayley[OF re])
qed

lemma disk_chart_homeomorphism:
  "homeomorphism (disk_domain b)
    (closed_halfspace :: (real \<times> (real ^ 1)) set)
    (disk_to_chart b) (disk_from_chart b)"
  by (rule homeomorphismI)
    (auto intro: disk_to_chart_continuous
      disk_from_chart_continuous
      disk_to_chart_in_halfspace
      disk_from_chart_in_domain)

lemma disk_halfspace_chart:
  "halfspace_chart disk_carrier (disk_domain b)
    (closed_halfspace :: (real \<times> (real ^ 1)) set)
    (disk_to_chart b) (disk_from_chart b)"
  by (unfold_locales)
    (auto intro: disk_domain_open
      disk_chart_homeomorphism)

lemma disk_chart_face_iff:
  assumes z: "z \<in> disk_domain b"
  shows "fst (disk_to_chart b z) = 0
    \<longleftrightarrow> norm z = 1"
proof -
  have nz: "0 < (norm
    (if b then 1 - z else 1 + z))\<^sup>2"
    using disk_puncture_outside[OF z]
    by (cases b) auto
  have eq: "1 - (norm z)\<^sup>2 = 0
    \<longleftrightarrow> norm z = 1"
    by (simp add: abs_square_eq_1)
  show ?thesis
    using nz eq
    by (cases b)
      (simp_all add: disk_to_chart_def
        complex_to_halfspace_def
        disk_cayley_Re_true
        disk_cayley_Re_false)
qed

lemma disk_halfspace_atlas:
  "halfspace_atlas disk_carrier (UNIV::bool set)
    disk_domain
    (\<lambda>_. closed_halfspace ::
      (real \<times> (real ^ 1)) set)
    disk_to_chart disk_from_chart"
proof (rule halfspace_atlas.intro)
  show "disk_carrier \<subseteq>
      (\<Union>i\<in>(UNIV::bool set). disk_domain i)"
    using disk_domain_cover by auto
  show "\<And>i. i \<in> (UNIV::bool set) \<Longrightarrow>
      halfspace_chart disk_carrier
        (disk_domain i) closed_halfspace
        (disk_to_chart i) (disk_from_chart i)"
    by (rule disk_halfspace_chart)
  show "\<And>i j p.
    i \<in> (UNIV::bool set) \<Longrightarrow>
    j \<in> UNIV \<Longrightarrow>
    p \<in> disk_domain i \<Longrightarrow>
    p \<in> disk_domain j \<Longrightarrow>
    (fst (disk_to_chart i p) = 0
      \<longleftrightarrow> fst (disk_to_chart j p) = 0)"
    by (simp add: disk_chart_face_iff)
qed

lemma disk_boundary_carrier:
  "halfspace_atlas.boundary_carrier
    disk_carrier (UNIV::bool set)
    disk_domain disk_to_chart =
    sphere 0 1"
proof -
  interpret disk: halfspace_atlas
    disk_carrier "UNIV::bool set"
    disk_domain
    "\<lambda>_. closed_halfspace ::
      (real \<times> (real ^ 1)) set"
    disk_to_chart disk_from_chart
    by (rule disk_halfspace_atlas)
  have "disk.boundary_carrier = sphere 0 1"
  proof
    show "disk.boundary_carrier \<subseteq> sphere 0 1"
      unfolding disk.boundary_carrier_def
      by (auto simp: disk_chart_face_iff
        disk_carrier_def dist_norm)
    show "sphere 0 1 \<subseteq> disk.boundary_carrier"
    proof
      fix z :: complex
      assume z: "z \<in> sphere 0 1"
      have carrier: "z \<in> disk_carrier"
        using z by (simp add: disk_carrier_def
          dist_norm)
      obtain b where b: "z \<in> disk_domain b"
        using disk_domain_cover carrier by blast
      have face: "fst (disk_to_chart b z) = 0"
        using disk_chart_face_iff[OF b] z
        by (simp add: dist_norm)
      show "z \<in> disk.boundary_carrier"
        unfolding disk.boundary_carrier_def
        using carrier b face by blast
    qed
  qed
  show ?thesis
    using \<open>disk.boundary_carrier = sphere 0 1\<close>
    by simp
qed

lemma disk_cayley_other:
  "disk_cayley (\<not> b) z =
    inverse (disk_cayley b z)"
  by (cases b)
    (simp_all add: disk_cayley_def)

definition disk_transition_extension ::
    "real \<times> (real ^ 1) \<Rightarrow>
      real \<times> (real ^ 1)" where
  "disk_transition_extension x =
    complex_to_halfspace
      (inverse (halfspace_to_complex x))"

lemma disk_other_chart_transition:
  assumes x: "x \<in> (closed_halfspace ::
      (real \<times> (real ^ 1)) set)"
  shows "disk_to_chart (\<not> b)
      (disk_from_chart b x) =
    disk_transition_extension x"
proof -
  have re: "0 \<le> Re (halfspace_to_complex x)"
    using x by (simp add: closed_halfspace_def
      halfspace_to_complex_def)
  show ?thesis
    using disk_cayley_uncayley[OF re, of b]
    by (simp add: disk_to_chart_def
      disk_from_chart_def
      disk_transition_extension_def
      disk_cayley_other)
qed

lemma complex_to_halfspace_bounded_linear:
  "bounded_linear complex_to_halfspace"
proof (rule linear_conv_bounded_linear[THEN iffD1])
  show "linear complex_to_halfspace"
    by (rule linearI)
      (simp_all add: complex_to_halfspace_def
        vec_eq_iff)
qed

lemma halfspace_to_complex_bounded_linear:
  "bounded_linear halfspace_to_complex"
proof (rule linear_conv_bounded_linear[THEN iffD1])
  show "linear halfspace_to_complex"
    by (rule linearI)
      (simp_all add: halfspace_to_complex_def
        complex_eq_iff)
qed

lemma halfspace_to_complex_nonzero:
  assumes "x \<noteq> 0"
  shows "halfspace_to_complex x \<noteq> 0"
proof
  assume "halfspace_to_complex x = 0"
  then have "complex_to_halfspace
      (halfspace_to_complex x) = 0"
    by (simp add: complex_to_halfspace_def
      zero_prod_def)
  then show False
    using assms by simp
qed

lemma disk_transition_extension_C2:
  "Ck_on 2 disk_transition_extension
    (UNIV - {0})"
proof -
  have openU: "open (UNIV - {0} ::
      (real \<times> (real ^ 1)) set)"
    by (intro open_Diff) simp_all
  have lin: "Ck_on 2 halfspace_to_complex
      (UNIV - {0})"
    by (rule Ck_on_bounded_linear
      [OF halfspace_to_complex_bounded_linear openU])
  have inv: "Ck_on 2
      (\<lambda>x. inverse (halfspace_to_complex x))
      (UNIV - {0})"
    by (rule Ck_on_inverse[OF lin])
      (metis DiffD2 singletonI
        halfspace_to_complex_nonzero)
  show ?thesis
    unfolding disk_transition_extension_def
    by (rule Ck_on_bounded_linear_compose
      [OF complex_to_halfspace_bounded_linear inv])
qed

lemma disk_from_chart_zero:
  "disk_from_chart b 0 = disk_puncture (\<not> b)"
proof -
  have h0: "halfspace_to_complex 0 = 0"
    by (simp add: halfspace_to_complex_def
      zero_prod_def complex_eq_iff)
  show ?thesis
    by (cases b)
      (simp_all add: disk_from_chart_def
        disk_uncayley_def disk_puncture_def h0)
qed

lemma disk_boundary_overlap_nonzero:
  fixes i j :: bool
  assumes ij: "i \<noteq> j"
    and y: "y \<in>
      halfspace_atlas.boundary_overlap
        disk_domain
        (\<lambda>_. closed_halfspace ::
          (real \<times> (real ^ 1)) set)
        disk_from_chart i j"
  shows "((0::real),y) \<noteq> 0"
proof -
  interpret disk: halfspace_atlas
    disk_carrier "UNIV::bool set"
    disk_domain
    "\<lambda>_. closed_halfspace ::
      (real \<times> (real ^ 1)) set"
    disk_to_chart disk_from_chart
    by (rule disk_halfspace_atlas)
  have in_j: "disk_from_chart i (0,y) \<in>
      disk_domain j"
    using y by (simp add: disk.boundary_overlap_def)
  show ?thesis
  proof
    assume zero: "((0::real),y) = 0"
    have ji: "j = (\<not> i)"
      using ij by (cases i; cases j) auto
    have "disk_from_chart i (0,y) =
        disk_from_chart i 0"
      using zero by metis
    also have "\<dots> = disk_puncture j"
      by (simp add: ji disk_from_chart_zero)
    finally have "disk_from_chart i (0,y) =
        disk_puncture j" .
    with in_j show False
      by (simp add: disk_domain_def)
  qed
qed

lemma disk_C2_halfspace_atlas:
  "C2_halfspace_atlas disk_carrier
    (UNIV::bool set)
    disk_domain
    (\<lambda>_. closed_halfspace ::
      (real \<times> (real ^ 1)) set)
    disk_to_chart disk_from_chart"
proof (rule C2_halfspace_atlas.intro)
  show "halfspace_atlas disk_carrier
      (UNIV::bool set) disk_domain
      (\<lambda>_. closed_halfspace ::
        (real \<times> (real ^ 1)) set)
      disk_to_chart disk_from_chart"
    by (rule disk_halfspace_atlas)
  show "C2_halfspace_atlas_axioms
      (UNIV::bool set) disk_domain
      (\<lambda>_. closed_halfspace ::
        (real \<times> (real ^ 1)) set)
      disk_to_chart disk_from_chart"
  proof (rule C2_halfspace_atlas_axioms.intro)
  interpret disk: halfspace_atlas
    disk_carrier "UNIV::bool set"
    disk_domain
    "\<lambda>_. closed_halfspace ::
      (real \<times> (real ^ 1)) set"
    disk_to_chart disk_from_chart
    by (rule disk_halfspace_atlas)
  fix i j :: bool and y :: "real ^ 1"
  assume i: "i \<in> (UNIV::bool set)"
    and j: "j \<in> (UNIV::bool set)"
    and y: "y \<in> disk.boundary_overlap i j"
  show "\<exists>U F. open U \<and> (0,y) \<in> U \<and>
      Ck_on 2 F U \<and>
      (\<forall>x\<in>U \<inter> closed_halfspace.
        disk_from_chart i x \<in> disk_domain j
          \<longrightarrow>
        F x = disk_to_chart j
          (disk_from_chart i x))"
  proof (cases "i = j")
    case True
    have eq: "disk_to_chart j
        (disk_from_chart i x) = x"
      if x: "x \<in> closed_halfspace" for x
      using True disk_to_from[OF x]
      by simp
    have c2: "Ck_on 2 id
        (UNIV :: (real \<times> (real ^ 1)) set)"
      by (simp add: id_def Ck_on_id)
    show ?thesis
      by (intro exI[of _ UNIV]
          exI[of _ id])
        (auto simp: eq intro: c2)
  next
    case False
    have nz: "((0::real),y) \<noteq> 0"
      by (rule disk_boundary_overlap_nonzero
        [OF False y])
    have eq: "disk_to_chart j
        (disk_from_chart i x) =
        disk_transition_extension x"
      if x: "x \<in> closed_halfspace" for x
      using False disk_other_chart_transition[OF x, of i]
      by (cases i; cases j)
        simp_all
    show ?thesis
      by (intro exI[of _ "UNIV - {0}"]
          exI[of _ disk_transition_extension])
        (auto simp: nz eq
          intro: disk_transition_extension_C2)
  qed
  qed
qed

lemma complex_inverse_face_coefficient:
  fixes u :: real
  assumes u: "u \<noteq> 0"
  shows "- (inverse (Complex 0 u) *
      inverse (Complex 0 u)) =
    of_real (inverse (u\<^sup>2))"
proof -
  have inv: "inverse (Complex 0 u) =
      Complex 0 (- inverse u)"
    using u
    by (simp add: complex_eq_iff
      inverse_complex.sel power2_eq_square
      divide_inverse)
  have cancel: "u * (u *
      (inverse u * inverse u)) = 1"
  proof -
    have "u * (u * (inverse u * inverse u)) =
        (u * inverse u) * (u * inverse u)"
      by (simp add: mult_ac)
    also have "\<dots> = 1"
      using u by simp
    finally show ?thesis .
  qed
  show ?thesis
    using u cancel
    by (simp add: inv complex_eq_iff
      divide_inverse inverse_mult_distrib
      power2_eq_square mult_ac)
qed

lemma complex_halfspace_real_scale:
  fixes r :: real and h :: "real \<times> (real ^ 1)"
  shows "complex_to_halfspace
      (of_real r * halfspace_to_complex h) =
    r *\<^sub>R h"
  by (cases h)
    (simp add: complex_to_halfspace_def
      halfspace_to_complex_def
      scaleR_prod_def vec_eq_iff
      of_real_def)

lemma disk_transition_face_has_derivative:
  fixes u :: real
  assumes u: "u \<noteq> 0"
  shows "(disk_transition_extension has_derivative
      (\<lambda>h. inverse (u\<^sup>2) *\<^sub>R h))
    (at (0, vec u))"
proof -
  let ?x = "(0,vec u) ::
    real \<times> (real ^ 1)"
  let ?w = "halfspace_to_complex ?x"
  have w: "?w = Complex 0 u"
    by (simp add: halfspace_to_complex_def)
  have wn: "?w \<noteq> 0"
    using u by (simp add: w complex_eq_iff)
  have dh: "(halfspace_to_complex
      has_derivative halfspace_to_complex) (at ?x)"
    by (rule bounded_linear.has_derivative
      [OF halfspace_to_complex_bounded_linear])
      simp
  have dinv: "(inverse has_derivative
      (\<lambda>h. - (inverse ?w * h * inverse ?w)))
      (at ?w)"
    by (rule Deriv.has_derivative_inverse'[OF wn])
  have di: "((\<lambda>x. inverse (halfspace_to_complex x))
      has_derivative
      (\<lambda>h. - (inverse ?w *
        halfspace_to_complex h * inverse ?w)))
      (at ?x)"
    using has_derivative_compose[OF dh dinv]
    by (simp add: o_def)
  have dc: "(complex_to_halfspace
      has_derivative complex_to_halfspace)
      (at (inverse ?w))"
    by (rule bounded_linear.has_derivative
      [OF complex_to_halfspace_bounded_linear])
      simp
  have dF: "(disk_transition_extension
      has_derivative
      (\<lambda>h. complex_to_halfspace
        (- (inverse ?w *
          halfspace_to_complex h * inverse ?w))))
      (at ?x)"
    unfolding disk_transition_extension_def
    using has_derivative_compose[OF di dc]
    by (simp add: o_def)
  have coeff: "- (inverse ?w * inverse ?w) =
      of_real (inverse (u\<^sup>2))"
    using complex_inverse_face_coefficient[OF u]
    by (simp add: w)
  have lin_eq: "(\<lambda>h. complex_to_halfspace
        (- (inverse ?w *
          halfspace_to_complex h * inverse ?w))) =
      (\<lambda>h. inverse (u\<^sup>2) *\<^sub>R h)"
  proof (rule ext)
    fix h :: "real \<times> (real ^ 1)"
    have alg: "- (inverse ?w *
        halfspace_to_complex h * inverse ?w) =
        of_real (inverse (u\<^sup>2)) *
          halfspace_to_complex h"
    proof -
      have "- (inverse ?w *
          halfspace_to_complex h * inverse ?w) =
          (- (inverse ?w * inverse ?w)) *
            halfspace_to_complex h"
        by (simp add: mult_ac)
      also have "\<dots> = of_real (inverse (u\<^sup>2)) *
          halfspace_to_complex h"
        using coeff by simp
      finally show ?thesis .
    qed
    have "complex_to_halfspace
        (- (inverse ?w *
          halfspace_to_complex h * inverse ?w)) =
        complex_to_halfspace
          (of_real (inverse (u\<^sup>2)) *
            halfspace_to_complex h)"
      by (simp only: alg)
    also have "\<dots> =
        inverse (u\<^sup>2) *\<^sub>R h"
      by (rule complex_halfspace_real_scale)
    finally show "complex_to_halfspace
        (- (inverse ?w *
          halfspace_to_complex h * inverse ?w)) =
        inverse (u\<^sup>2) *\<^sub>R h" .
  qed
  show ?thesis
    using dF lin_eq by simp
qed

lemma cart_map_of_product_has_derivative_scale:
  fixes f :: "real \<times> (real ^ 'n::finite)
      \<Rightarrow> real \<times> (real ^ 'n)"
  assumes f: "(f has_derivative
      (\<lambda>h. r *\<^sub>R h)) (at p)"
  shows "(cart_map_of_product f has_derivative
      (\<lambda>h. r *\<^sub>R h))
    (at (product_to_cart p))"
proof -
  let ?x = "product_to_cart p"
  have dc: "(cart_to_product
      has_derivative cart_to_product) (at ?x)"
    by (rule bounded_linear.has_derivative
      [OF cart_to_product_bounded_linear])
      simp
  have fp: "(f has_derivative
      (\<lambda>h. r *\<^sub>R h))
      (at (cart_to_product ?x))"
    using f by simp
  have d1: "((\<lambda>v. f (cart_to_product v))
      has_derivative
      (\<lambda>h. r *\<^sub>R cart_to_product h))
    (at ?x)"
    using has_derivative_compose[OF dc fp]
    by (simp add: o_def)
  have dp: "(product_to_cart
      has_derivative product_to_cart)
    (at (f p))"
    by (rule bounded_linear.has_derivative
      [OF product_to_cart_bounded_linear])
      simp
  have dp': "(product_to_cart
      has_derivative product_to_cart)
    (at (f (cart_to_product ?x)))"
    using dp by simp
  have d2: "(cart_map_of_product f
      has_derivative
      (\<lambda>h. product_to_cart
        (r *\<^sub>R cart_to_product h)))
      (at ?x)"
    unfolding cart_map_of_product_def
    using has_derivative_compose[OF d1 dp']
    by (simp add: o_def)
  have eq: "(\<lambda>h. product_to_cart
        (r *\<^sub>R cart_to_product h)) =
      (\<lambda>h. r *\<^sub>R h)"
    by (rule ext)
      (simp add: product_to_cart_def
        cart_to_product_def vec_eq_iff
        split: sum.splits)
  show ?thesis
    using d2 eq by metis
qed

lemma disk_transition_face_positive_jacobian:
  fixes u :: real
  assumes u: "u \<noteq> 0"
  shows "0 < Determinants.det
    (jacobian
      (cart_map_of_product disk_transition_extension)
      (at (product_to_cart (0,vec u))))"
proof -
  let ?r = "inverse (u\<^sup>2)"
  have r: "0 < ?r"
    using u by simp
  have d: "(cart_map_of_product
      disk_transition_extension has_derivative
      (\<lambda>h. ?r *\<^sub>R h))
      (at (product_to_cart (0,vec u)))"
    by (rule cart_map_of_product_has_derivative_scale
      [OF disk_transition_face_has_derivative[OF u]])
  have eq: "jacobian
      (cart_map_of_product disk_transition_extension)
      (at (product_to_cart (0,vec u))) =
      matrix (\<lambda>h. ?r *\<^sub>R h)"
    using frechet_derivative_at[OF d]
    by (simp add: jacobian_def)
  show ?thesis
    using r
    by (auto simp: eq intro: mult_pos_pos)
qed

lemma disk_carrier_compact:
  "compact disk_carrier"
  by (simp add: disk_carrier_def)

lemma disk_positively_oriented_C2_halfspace_atlas:
  "positively_oriented_C2_halfspace_atlas
    disk_carrier (UNIV::bool set)
    disk_domain
    (\<lambda>_. closed_halfspace ::
      (real \<times> (real ^ 1)) set)
    disk_to_chart disk_from_chart"
proof (rule positively_oriented_C2_halfspace_atlas.intro)
  show "C2_halfspace_atlas disk_carrier
      (UNIV::bool set) disk_domain
      (\<lambda>_. closed_halfspace ::
        (real \<times> (real ^ 1)) set)
      disk_to_chart disk_from_chart"
    by (rule disk_C2_halfspace_atlas)
  show "positively_oriented_C2_halfspace_atlas_axioms
      (UNIV::bool set) disk_domain
      (\<lambda>_. closed_halfspace ::
        (real \<times> (real ^ 1)) set)
      disk_to_chart disk_from_chart"
  proof (rule positively_oriented_C2_halfspace_atlas_axioms.intro)
    interpret disk: halfspace_atlas
      disk_carrier "UNIV::bool set"
      disk_domain
      "\<lambda>_. closed_halfspace ::
        (real \<times> (real ^ 1)) set"
      disk_to_chart disk_from_chart
      by (rule disk_halfspace_atlas)
    fix i j :: bool and y :: "real ^ 1"
    assume i: "i \<in> (UNIV::bool set)"
      and j: "j \<in> (UNIV::bool set)"
      and y: "y \<in> disk.boundary_overlap i j"
    show "\<exists>U F. Ck_on 2 F U \<and>
        (0,y) \<in> U \<and>
        (\<forall>x\<in>U \<inter> closed_halfspace.
          F x = disk.coordinate_transition i j x) \<and>
        0 < Determinants.det
          (jacobian (cart_map_of_product F)
            (at (product_to_cart (0,y))))"
    proof (cases "i = j")
      case True
      have eq: "disk.coordinate_transition i j x = x"
        if x: "x \<in> closed_halfspace" for x
        using True disk_to_from[OF x]
        by (simp add: disk.coordinate_transition_def)
      have c2: "Ck_on 2 id
          (UNIV :: (real \<times> (real ^ 1)) set)"
        by (simp add: id_def Ck_on_id)
      have map_id: "cart_map_of_product
          (id :: real \<times> (real ^ 1) \<Rightarrow>
            real \<times> (real ^ 1)) = id"
        by (rule ext)
          (simp add: cart_map_of_product_def)
      have pos: "0 < Determinants.det
          (jacobian (cart_map_of_product id)
            (at (product_to_cart (0,y))))"
        by (simp add: map_id jacobian_def)
      show ?thesis
        by (intro exI[of _ UNIV]
            exI[of _ id])
          (auto simp: eq intro: c2 pos)
    next
      case False
      have nz: "((0::real),y) \<noteq> 0"
        by (rule disk_boundary_overlap_nonzero
          [OF False y])
      have un: "y $ 1 \<noteq> 0"
      proof
        assume "y $ 1 = 0"
        then have "y = 0"
          by (metis vector_one_nth vec_0)
        with nz show False
          by (simp add: zero_prod_def)
      qed
      have eq: "disk.coordinate_transition i j x =
          disk_transition_extension x"
        if x: "x \<in> closed_halfspace" for x
        using False disk_other_chart_transition[OF x, of i]
        by (cases i; cases j)
          (simp_all add: disk.coordinate_transition_def)
      have pos: "0 < Determinants.det
          (jacobian
            (cart_map_of_product
              disk_transition_extension)
            (at (product_to_cart (0,y))))"
        using disk_transition_face_positive_jacobian
            [OF un]
        by (simp add: vector_one_nth)
      show ?thesis
        by (intro exI[of _ "UNIV - {0}"]
            exI[of _ disk_transition_extension])
          (auto simp: nz eq
            intro: disk_transition_extension_C2 pos)
    qed
  qed
qed

end
