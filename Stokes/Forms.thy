theory Forms
  imports "HOL-Analysis.Analysis"
begin

text \<open>
  In oriented Cartesian Euclidean coordinates, contraction with the
  standard volume form identifies a near-top form with a vector field.
  Its exterior derivative is the divergence of that vector field.
  A top form is represented by its scalar coefficient.
\<close>

type_synonym 'n near_top_eucl_form = "(real ^ 'n) \<Rightarrow> real ^ 'n"
type_synonym 'n top_eucl_form = "(real ^ 'n) \<Rightarrow> real"

definition exterior_top ::
    "'n::finite near_top_eucl_form \<Rightarrow> 'n top_eucl_form"
  where "exterior_top A x =
    trace (matrix (frechet_derivative A (at x)))"

definition signed_near_top_coeff ::
    "('n::finite \<Rightarrow> real) \<Rightarrow>
      ('n \<Rightarrow> real ^ 'n \<Rightarrow> real) \<Rightarrow>
      'n near_top_eucl_form"
  where "signed_near_top_coeff s a x =
    (\<chi> i. s i * a i x)"

definition restrict_near_top ::
    "(real ^ 'n) set \<Rightarrow> 'n near_top_eucl_form \<Rightarrow>
      'n near_top_eucl_form"
  where "restrict_near_top U A x = (if x \<in> U then A x else 0)"

definition restrict_top ::
    "(real ^ 'n) set \<Rightarrow> 'n top_eucl_form \<Rightarrow>
      'n top_eucl_form"
  where "restrict_top U T x = (if x \<in> U then T x else 0)"

definition pull_top_affine ::
    "real ^ 'n::finite ^ 'n \<Rightarrow> real ^ 'n \<Rightarrow>
      'n top_eucl_form \<Rightarrow> 'n top_eucl_form"
  where "pull_top_affine F c T x =
    Determinants.det F * T (F *v x + c)"

definition pull_near_top_affine ::
    "real ^ 'n::finite ^ 'n \<Rightarrow> real ^ 'n ^ 'n \<Rightarrow>
      real ^ 'n \<Rightarrow> 'n near_top_eucl_form \<Rightarrow>
      'n near_top_eucl_form"
  where "pull_near_top_affine F G c A x =
    Determinants.det F *\<^sub>R (G *v A (F *v x + c))"

definition pull_top ::
    "(real ^ 'n::finite \<Rightarrow> real ^ 'n) \<Rightarrow>
      'n top_eucl_form \<Rightarrow> 'n top_eucl_form"
  where "pull_top f T x =
    Determinants.det (jacobian f (at x)) * T (f x)"

definition pull_near_top ::
    "(real ^ 'n::finite \<Rightarrow> real ^ 'n) \<Rightarrow>
      (real ^ 'n \<Rightarrow> real ^ 'n) \<Rightarrow>
      'n near_top_eucl_form \<Rightarrow> 'n near_top_eucl_form"
  where "pull_near_top f g A x =
    Determinants.det (jacobian f (at x)) *\<^sub>R
      (jacobian g (at (f x)) *v A (f x))"

definition cofactor_column ::
    "(real ^ 'n::finite \<Rightarrow> real ^ 'n) \<Rightarrow>
      (real ^ 'n \<Rightarrow> real ^ 'n) \<Rightarrow> 'n \<Rightarrow>
      'n near_top_eucl_form"
  where "cofactor_column f g j x =
    Determinants.det (jacobian f (at x)) *\<^sub>R
      (jacobian g (at (f x)) *v axis j 1)"

lemma exterior_top_coordinate:
  "exterior_top A x =
    (\<Sum>i\<in>UNIV. frechet_derivative A (at x) (axis i 1) $ i)"
  by (simp add: exterior_top_def trace_def matrix_def)

lemma signed_near_top_coeff_differentiable:
  fixes a :: "'n::finite \<Rightarrow> real ^ 'n \<Rightarrow> real"
  assumes da: "\<And>i. a i differentiable (at x)"
  shows "signed_near_top_coeff s a differentiable (at x)"
proof -
  have comp: "(\<lambda>y. signed_near_top_coeff s a y $ i)
      differentiable (at x)" for i
  proof -
    have "(\<lambda>y. s i * a i y) differentiable (at x)"
      by (intro differentiable_mult differentiable_const da)
    then show ?thesis
      by (simp add: signed_near_top_coeff_def)
  qed
  have "\<forall>b\<in>(Basis :: (real ^ 'n) set).
      (\<lambda>y. signed_near_top_coeff s a y \<bullet> b)
        differentiable (at x within UNIV)"
    using comp by (auto simp: Basis_vec_def inner_axis)
  then show ?thesis
    using differentiable_componentwise_within
      [of "signed_near_top_coeff s a" x UNIV]
    by simp
qed

lemma exterior_top_signed_coeff:
  fixes a :: "'n::finite \<Rightarrow> real ^ 'n \<Rightarrow> real"
  assumes da: "\<And>i. a i differentiable (at x)"
  shows "exterior_top (signed_near_top_coeff s a) x =
    (\<Sum>i\<in>UNIV. s i *
      frechet_derivative (a i) (at x) (axis i 1))"
proof -
  have d: "signed_near_top_coeff s a differentiable (at x)"
    by (rule signed_near_top_coeff_differentiable[OF da])
  have component: "frechet_derivative (signed_near_top_coeff s a)
      (at x) (axis i 1) $ i =
    s i * frechet_derivative (a i) (at x) (axis i 1)" for i
  proof -
    have "frechet_derivative (signed_near_top_coeff s a)
        (at x) (axis i 1) $ i =
      frechet_derivative (\<lambda>y. signed_near_top_coeff s a y $ i)
        (at x) (axis i 1)"
      using jacobian_component[OF d, of i i]
      by (simp add: jacobian_def matrix_def)
    also have "\<dots> =
      s i * frechet_derivative (a i) (at x) (axis i 1)"
      using da[of i]
      by (simp add: signed_near_top_coeff_def
        frechet_derivative_bilinear[OF bounded_bilinear_mult])
    finally show ?thesis .
  qed
  show ?thesis
    by (simp add: exterior_top_coordinate component)
qed

lemma exterior_top_add:
  assumes "A differentiable (at x)" "B differentiable (at x)"
  shows "exterior_top (\<lambda>y. A y + B y) x =
    exterior_top A x + exterior_top B x"
  by (simp add: exterior_top_coordinate
    frechet_derivative_add[OF assms] sum.distrib)

lemma exterior_top_zero [simp]:
  "exterior_top (\<lambda>y. 0) x = 0"
  by (simp add: exterior_top_coordinate)

lemma exterior_top_const [simp]:
  "exterior_top (\<lambda>y. c) x = 0"
  by (simp add: exterior_top_coordinate)

lemma exterior_top_scale:
  fixes A :: "'n::finite near_top_eucl_form"
    and rho :: "(real ^ 'n) \<Rightarrow> real"
  assumes "rho differentiable (at x)" "A differentiable (at x)"
  shows "exterior_top (\<lambda>y. rho y *\<^sub>R A y) x =
    rho x * exterior_top A x +
      (\<Sum>i\<in>UNIV.
        frechet_derivative rho (at x) (axis i 1) * A x $ i)"
  by (simp add: exterior_top_coordinate
    frechet_derivative_bilinear[OF bounded_bilinear_scaleR assms]
    sum.distrib algebra_simps sum_distrib_left)

lemma exterior_top_sum:
  fixes A :: "'i \<Rightarrow> 'n::finite near_top_eucl_form"
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> A i differentiable (at x)"
  shows "exterior_top (\<lambda>y. \<Sum>i\<in>I. A i y) x =
    (\<Sum>i\<in>I. exterior_top (A i) x)"
  using assms
proof (induction I rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert i I)
  have dI: "(\<lambda>y. \<Sum>j\<in>I. A j y) differentiable (at x)"
    by (intro differentiable_sum) (use insert.hyps insert.prems in auto)
  have di: "A i differentiable (at x)"
    using insert.prems by simp
  have "exterior_top (\<lambda>y. \<Sum>j\<in>insert i I. A j y) x =
      exterior_top (\<lambda>y. A i y +
        (\<Sum>j\<in>I. A j y)) x"
    using insert.hyps by simp
  also have "\<dots> = exterior_top (A i) x +
      exterior_top (\<lambda>y. \<Sum>j\<in>I. A j y) x"
    by (rule exterior_top_add[OF di dI])
  also have "\<dots> = (\<Sum>j\<in>insert i I. exterior_top (A j) x)"
    using insert by simp
  finally show ?case .
qed

lemma restrict_near_top_in [simp]:
  "x \<in> U \<Longrightarrow> restrict_near_top U A x = A x"
  by (simp add: restrict_near_top_def)

lemma restrict_near_top_out [simp]:
  "x \<notin> U \<Longrightarrow> restrict_near_top U A x = 0"
  by (simp add: restrict_near_top_def)

lemma restrict_top_in [simp]:
  "x \<in> U \<Longrightarrow> restrict_top U T x = T x"
  by (simp add: restrict_top_def)

lemma restrict_top_out [simp]:
  "x \<notin> U \<Longrightarrow> restrict_top U T x = 0"
  by (simp add: restrict_top_def)

lemma exterior_top_restrict_near_top:
  assumes "open U" "x \<in> U"
  shows "exterior_top (restrict_near_top U A) x =
    exterior_top A x"
  unfolding exterior_top_def
  by (subst frechet_derivative_transform_within_open
    [OF assms, of "restrict_near_top U A" A])
     simp_all

lemma pull_top_affine_id [simp]:
  "pull_top_affine (mat 1) 0 T = T"
  by (rule ext) (simp add: pull_top_affine_def)

lemma pull_near_top_affine_id [simp]:
  "pull_near_top_affine (mat 1) (mat 1) 0 A = A"
  by (rule ext) (simp add: pull_near_top_affine_def)

lemma pull_top_affine_add:
  "pull_top_affine F c (\<lambda>x. T x + S x) =
    (\<lambda>x. pull_top_affine F c T x + pull_top_affine F c S x)"
  by (rule ext) (simp add: pull_top_affine_def algebra_simps)

lemma pull_near_top_affine_add:
  "pull_near_top_affine F G c (\<lambda>x. A x + B x) =
    (\<lambda>x. pull_near_top_affine F G c A x +
      pull_near_top_affine F G c B x)"
  by (rule ext)
     (simp add: pull_near_top_affine_def
       matrix_vector_right_distrib scaleR_right_distrib)

lemma pull_top_affine_compose:
  "pull_top_affine F c (pull_top_affine H d T) =
    pull_top_affine (H ** F) (H *v c + d) T"
  by (rule ext)
     (simp add: pull_top_affine_def matrix_vector_mul_assoc
       matrix_vector_mult_add_rdistrib det_mul algebra_simps)

lemma pull_near_top_affine_compose:
  assumes "F ** G = mat 1" "G ** F = mat 1"
    and "H ** J = mat 1" "J ** H = mat 1"
  shows "pull_near_top_affine F G c
      (pull_near_top_affine H J d A) =
    pull_near_top_affine (H ** F) (G ** J) (H *v c + d) A"
  by (rule ext)
     (simp add: pull_near_top_affine_def matrix_vector_mul_assoc
       matrix_vector_mult_add_rdistrib matrix_vector_mult_scaleR
       det_mul scaleR_scaleR algebra_simps)

lemma jacobian_compose_at:
  fixes f h :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes "f differentiable (at x)" "h differentiable (at (f x))"
  shows "jacobian (h \<circ> f) (at x) =
    jacobian h (at (f x)) ** jacobian f (at x)"
  unfolding jacobian_def
  by (simp add: frechet_derivative_compose[OF assms]
    matrix_compose[OF linear_frechet_derivative[OF assms(1)]
      linear_frechet_derivative[OF assms(2)]])

lemma pull_top_compose_at:
  fixes f h :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes "f differentiable (at x)" "h differentiable (at (f x))"
  shows "pull_top f (pull_top h T) x =
    pull_top (h \<circ> f) T x"
  by (simp add: pull_top_def jacobian_compose_at[OF assms]
    det_mul algebra_simps)

lemma pull_near_top_compose_at:
  fixes f g h k :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes "f differentiable (at x)"
    and "h differentiable (at (f x))"
    and "k differentiable (at (h (f x)))"
    and "g differentiable (at (f x))"
    and "k (h (f x)) = f x"
  shows "pull_near_top f g (pull_near_top h k A) x =
    pull_near_top (h \<circ> f) (g \<circ> k) A x"
  by (simp add: pull_near_top_def assms(5)
    jacobian_compose_at[OF assms(1,2)]
    jacobian_compose_at[OF assms(3)]
    assms(4) det_mul matrix_vector_mult_scaleR
    matrix_vector_mul_assoc scaleR_scaleR algebra_simps)

lemma pull_near_top_cofactor_sum:
  fixes f g A :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  shows "pull_near_top f g A x =
    (\<Sum>j\<in>UNIV. A (f x) $ j *\<^sub>R cofactor_column f g j x)"
proof -
  let ?F = "jacobian f (at x)"
  let ?G = "jacobian g (at (f x))"
  let ?r = "Determinants.det ?F"
  have expansion:
    "(\<Sum>j\<in>UNIV. A (f x) $ j *\<^sub>R (axis j 1 :: real ^ 'n)) =
      A (f x)"
    by (metis basis_expansion scalar_mult_eq_scaleR)
  have distribute:
    "(\<Sum>j\<in>UNIV. ?G *v
      (A (f x) $ j *\<^sub>R (axis j 1 :: real ^ 'n))) =
      ?G *v (\<Sum>j\<in>UNIV. A (f x) $ j *\<^sub>R axis j 1)"
    by (rule linear_sum[OF matrix_vector_mul_linear, symmetric])
  have "(\<Sum>j\<in>UNIV. A (f x) $ j *\<^sub>R
      cofactor_column f g j x) =
    ?r *\<^sub>R (\<Sum>j\<in>UNIV. ?G *v
      (A (f x) $ j *\<^sub>R axis j 1))"
    by (simp add: cofactor_column_def
      scaleR_scaleR matrix_vector_mult_scaleR scaleR_sum_right
      mult.commute)
  also have "\<dots> = ?r *\<^sub>R (?G *v A (f x))"
    by (simp add: distribute expansion)
  also have "\<dots> = pull_near_top f g A x"
    by (simp add: pull_near_top_def)
  finally show ?thesis by simp
qed

lemma pullback_component_derivative:
  fixes f A :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes "f differentiable (at x)"
    and "A differentiable (at (f x))"
  shows "frechet_derivative (\<lambda>y. A (f y) $ j) (at x)
      (axis i 1) =
    (jacobian A (at (f x)) ** jacobian f (at x)) $ j $ i"
proof -
  have d: "(A \<circ> f) differentiable (at x)"
    by (rule differentiable_chain_at[OF assms])
  have "frechet_derivative (\<lambda>y. A (f y) $ j) (at x)
      (axis i 1) = jacobian (A \<circ> f) (at x) $ j $ i"
    using jacobian_component[OF d, of j i]
    by (simp add: comp_def)
  also have "\<dots> =
    (jacobian A (at (f x)) ** jacobian f (at x)) $ j $ i"
    by (simp add: jacobian_compose_at[OF assms])
  finally show ?thesis .
qed

lemma pullback_component_differentiable:
  fixes f A :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes "f differentiable (at x)"
    and "A differentiable (at (f x))"
  shows "(\<lambda>y. A (f y) $ j) differentiable (at x)"
proof -
  have d: "(A \<circ> f) differentiable (at x)"
    by (rule differentiable_chain_at[OF assms])
  have "(\<lambda>y. (A \<circ> f) y \<bullet> axis j 1)
      differentiable (at x)"
    using d differentiable_componentwise_within
      [of "A \<circ> f" x UNIV]
    by (auto simp: Basis_vec_def)
  then show ?thesis
    by (simp add: comp_def inner_axis)
qed

lemma trace_cofactor_columns:
  fixes F G M :: "real ^ 'n::finite ^ 'n"
  assumes "F ** G = mat 1"
  shows "(\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV.
      (M ** F) $ j $ i * (G *v axis j 1) $ i) =
    trace M"
proof -
  have "(\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV.
      (M ** F) $ j $ i * (G *v axis j 1) $ i) =
    trace ((M ** F) ** G)"
    by (simp add: trace_def matrix_matrix_mult_def
      matrix_vector_mult_basis column_def)
  also have "\<dots> = trace M"
    by (simp add: matrix_mul_assoc[symmetric] assms)
  finally show ?thesis .
qed

lemma piola_coordinate_cancellation:
  fixes G :: "real ^ 'n::finite ^ 'n"
    and H :: "'n \<Rightarrow> real ^ 'n ^ 'n"
  assumes mixed: "\<And>i a b. H i $ a $ b = H b $ a $ i"
  shows "(\<Sum>i\<in>UNIV. \<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G $ b $ a * H i $ a $ b * G $ i $ j) =
    (\<Sum>i\<in>UNIV. \<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G $ i $ a * H i $ a $ b * G $ b $ j)"
proof -
  have each: "(\<Sum>i\<in>UNIV. \<Sum>b\<in>UNIV.
      G $ b $ a * H i $ a $ b * G $ i $ j) =
    (\<Sum>i\<in>UNIV. \<Sum>b\<in>UNIV.
      G $ i $ a * H i $ a $ b * G $ b $ j)"
    for a
  proof -
    have "(\<Sum>i\<in>UNIV. \<Sum>b\<in>UNIV.
      G $ b $ a * H i $ a $ b * G $ i $ j) =
      (\<Sum>i\<in>UNIV. \<Sum>b\<in>UNIV.
      G $ i $ a * H b $ a $ i * G $ b $ j)"
      by (rule sum.swap)
    also have "\<dots> =
      (\<Sum>i\<in>UNIV. \<Sum>b\<in>UNIV.
      G $ i $ a * H i $ a $ b * G $ b $ j)"
      by (simp add: mixed)
    finally show ?thesis .
  qed
  have "(\<Sum>i\<in>UNIV. \<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G $ b $ a * H i $ a $ b * G $ i $ j) =
    (\<Sum>a\<in>UNIV. \<Sum>i\<in>UNIV. \<Sum>b\<in>UNIV.
      G $ b $ a * H i $ a $ b * G $ i $ j)"
    by (rule sum.swap)
  also have "\<dots> =
    (\<Sum>a\<in>UNIV. \<Sum>i\<in>UNIV. \<Sum>b\<in>UNIV.
      G $ i $ a * H i $ a $ b * G $ b $ j)"
    by (simp only: each)
  also have "\<dots> =
    (\<Sum>i\<in>UNIV. \<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G $ i $ a * H i $ a $ b * G $ b $ j)"
    by (rule sum.swap[symmetric])
  finally show ?thesis .
qed

text \<open>
  The following theorem isolates the Piola identity needed for
  smooth pullback naturality.  The regularity of cofactor columns is
  proved below.  Their zero divergence remains a separate obligation.
\<close>

theorem exterior_top_pull_near_top_if_cofactor_closed:
  fixes f g A :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes df: "f differentiable (at x)"
    and dA: "A differentiable (at (f x))"
    and inverse: "jacobian f (at x) ** jacobian g (at (f x)) =
      mat 1"
    and dcolumn: "\<And>j. cofactor_column f g j differentiable (at x)"
    and closed_column: "\<And>j. exterior_top (cofactor_column f g j) x = 0"
  shows "exterior_top (pull_near_top f g A) x =
    pull_top f (exterior_top A) x"
proof -
  let ?F = "jacobian f (at x)"
  let ?G = "jacobian g (at (f x))"
  let ?M = "jacobian A (at (f x))"
  let ?r = "Determinants.det ?F"
  let ?rho = "\<lambda>j y. A (f y) $ j"
  let ?C = "cofactor_column f g"
  have drho: "\<And>j. ?rho j differentiable (at x)"
    by (rule pullback_component_differentiable[OF df dA])
  have dterm: "\<And>j. (\<lambda>y. ?rho j y *\<^sub>R ?C j y)
      differentiable (at x)"
    by (intro differentiable_scaleR drho dcolumn)
  have fun_eq: "pull_near_top f g A =
      (\<lambda>y. \<Sum>j\<in>UNIV. ?rho j y *\<^sub>R ?C j y)"
    by (rule ext) (rule pull_near_top_cofactor_sum)
  have sum:
    "exterior_top (pull_near_top f g A) x =
      (\<Sum>j\<in>UNIV.
        exterior_top (\<lambda>y. ?rho j y *\<^sub>R ?C j y) x)"
    unfolding fun_eq
    by (rule exterior_top_sum) (auto intro: dterm)
  have each: "exterior_top (\<lambda>y. ?rho j y *\<^sub>R ?C j y) x =
    (\<Sum>i\<in>UNIV.
      (?M ** ?F) $ j $ i * ?C j x $ i)" for j
    using exterior_top_scale[OF drho[of j] dcolumn[of j]]
      closed_column[of j]
    by (simp add: pullback_component_derivative[OF df dA])
  have "exterior_top (pull_near_top f g A) x =
    (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV.
      (?M ** ?F) $ j $ i * ?C j x $ i)"
    by (simp add: sum each)
  also have "\<dots> = ?r *
    (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV.
      (?M ** ?F) $ j $ i * (?G *v axis j 1) $ i)"
    by (simp add: cofactor_column_def
      sum_distrib_left algebra_simps)
  also have "\<dots> = ?r * trace ?M"
    by (simp add: trace_cofactor_columns[OF inverse])
  also have "\<dots> = pull_top f (exterior_top A) x"
    by (simp add: pull_top_def exterior_top_def jacobian_def)
  finally show ?thesis .
qed

lemma restrict_near_top_support:
  "support_on U (restrict_near_top U A) \<subseteq> support_on U A"
  by (auto simp: support_on_def restrict_near_top_def)

lemma restrict_top_support:
  "support_on U (restrict_top U T) \<subseteq> support_on U T"
  by (auto simp: support_on_def restrict_top_def)

lemma near_top_scale_support:
  fixes A :: "'n::finite near_top_eucl_form"
    and rho :: "(real ^ 'n) \<Rightarrow> real"
  shows "support_on U (\<lambda>x. rho x *\<^sub>R A x) \<subseteq> support_on U A"
proof
  fix x
  assume h: "x \<in> support_on U (\<lambda>x. rho x *\<^sub>R A x)"
  then have xU: "x \<in> U" and nz: "rho x *\<^sub>R A x \<noteq> 0"
    by (auto simp: support_on_def)
  have "A x \<noteq> 0"
  proof
    assume "A x = 0"
    then have "rho x *\<^sub>R A x = 0" by simp
    with nz show False by blast
  qed
  with xU show "x \<in> support_on U A"
    by (simp add: support_on_def)
qed

lemma top_scale_support:
  fixes T :: "'n::finite top_eucl_form"
    and rho :: "(real ^ 'n) \<Rightarrow> real"
  shows "support_on U (\<lambda>x. rho x * T x) \<subseteq> support_on U T"
proof
  fix x
  assume h: "x \<in> support_on U (\<lambda>x. rho x * T x)"
  then have xU: "x \<in> U" and nz: "rho x * T x \<noteq> 0"
    by (auto simp: support_on_def)
  have "T x \<noteq> 0"
  proof
    assume "T x = 0"
    then have "rho x * T x = 0" by simp
    with nz show False by blast
  qed
  with xU show "x \<in> support_on U T"
    by (simp add: support_on_def)
qed

lemma near_top_scale_compact_support:
  fixes A :: "'n::finite near_top_eucl_form"
    and rho :: "(real ^ 'n) \<Rightarrow> real"
  assumes "compact (closure (support_on U A))"
  shows "compact (closure
    (support_on U (\<lambda>x. rho x *\<^sub>R A x)))"
proof -
  have "bounded (support_on U A)"
    by (rule bounded_subset
      [OF compact_imp_bounded[OF assms] closure_subset])
  then have "bounded (support_on U
      (\<lambda>x. rho x *\<^sub>R A x))"
    by (rule bounded_subset[OF _ near_top_scale_support])
  then show ?thesis by simp
qed

lemma top_scale_compact_support:
  fixes T :: "'n::finite top_eucl_form"
    and rho :: "(real ^ 'n) \<Rightarrow> real"
  assumes "compact (closure (support_on U T))"
  shows "compact (closure
    (support_on U (\<lambda>x. rho x * T x)))"
proof -
  have "bounded (support_on U T)"
    by (rule bounded_subset
      [OF compact_imp_bounded[OF assms] closure_subset])
  then have "bounded (support_on U
      (\<lambda>x. rho x * T x))"
    by (rule bounded_subset[OF _ top_scale_support])
  then show ?thesis by simp
qed

lemma differentiable_finite_prod:
  fixes a :: "'i \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> a i differentiable (at x)"
  shows "(\<lambda>y. \<Prod>i\<in>I. a i y) differentiable (at x)"
  using assms
proof (induction I rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert i I)
  have di: "a i differentiable (at x)"
    using insert.prems by simp
  have dI: "(\<lambda>y. \<Prod>j\<in>I. a j y) differentiable (at x)"
    by (rule insert.IH) (use insert.prems in auto)
  show ?case
    using insert.hyps
    by (simp add: differentiable_mult[OF di dI])
qed

lemma matrix_entry_differentiable:
  fixes J :: "'a::euclidean_space \<Rightarrow> real ^ 'n::finite ^ 'n"
  assumes "J differentiable (at x)"
  shows "(\<lambda>y. J y $ i $ j) differentiable (at x)"
proof -
  have lin: "linear (\<lambda>M::real ^ 'n ^ 'n. M $ i $ j)"
    by (simp add: linear_iff)
  have "((\<lambda>M::real ^ 'n ^ 'n. M $ i $ j) \<circ> J)
      differentiable (at x)"
    by (rule differentiable_chain_at[OF assms])
       (simp add: lin linear_imp_differentiable)
  then show ?thesis by (simp add: comp_def)
qed

lemma matrix_entry_has_derivative:
  fixes M :: "real ^ 'n::finite ^ 'n"
  shows "((\<lambda>N::real ^ 'n ^ 'n. N $ i $ j)
    has_derivative (\<lambda>K. K $ i $ j)) (at M)"
proof -
  have row: "bounded_linear
      (\<lambda>N::real ^ 'n ^ 'n. N $ i)"
    by (rule bounded_linear_vec_nth)
  have col: "bounded_linear
      (\<lambda>v::real ^ 'n. v $ j)"
    by (rule bounded_linear_vec_nth)
  have bl: "bounded_linear
      (\<lambda>N::real ^ 'n ^ 'n. N $ i $ j)"
    using bounded_linear_compose[OF col row] by simp
  show ?thesis
    by (rule bounded_linear.has_derivative[OF bl]) simp
qed

lemma permutes_two_moved:
  fixes p :: "'n::finite \<Rightarrow> 'n"
  assumes p: "p permutes UNIV" and pi: "p i \<noteq> i"
  obtains j where "j \<noteq> i" "p j \<noteq> j"
proof -
  obtain j where j: "p j = i"
    using permutes_surj[OF p] by (metis surj_def)
  have "j \<noteq> i" using j pi by auto
  moreover have "p j \<noteq> j" using j \<open>j \<noteq> i\<close> by auto
  ultimately show thesis by (rule that)
qed

lemma permutes_nonid_det_derivative_term_zero:
  fixes p :: "'n::finite \<Rightarrow> 'n"
    and K :: "real ^ 'n ^ 'n"
  assumes p: "p permutes UNIV" and nonid: "p \<noteq> id"
  shows "(\<Sum>i\<in>UNIV. K $ i $ p i *
    (\<Prod>j\<in>UNIV - {i}.
      (mat 1 :: real ^ 'n ^ 'n) $ j $ p j)) = 0"
proof -
  obtain a where a: "p a \<noteq> a"
    using nonid by (metis ext id_apply)
  obtain b where b: "b \<noteq> a" "p b \<noteq> b"
    by (rule permutes_two_moved[OF p a])
  have zero: "(\<Prod>j\<in>UNIV - {i}.
      (mat 1 :: real ^ 'n ^ 'n) $ j $ p j) = 0" for i
  proof -
    obtain j where j: "j \<noteq> i" "p j \<noteq> j"
      using a b by metis
    have z: "(mat 1 :: real ^ 'n ^ 'n) $ j $ p j = 0"
      using j(2) by (simp add: mat_def)
    show ?thesis
      by (rule prod_zero) (use j(1) z in auto)
  qed
  show ?thesis by (simp add: zero)
qed

lemma matrix_det_differentiable:
  fixes J :: "'a::euclidean_space \<Rightarrow> real ^ 'n::finite ^ 'n"
  assumes "J differentiable (at x)"
  shows "(\<lambda>y. Determinants.det (J y)) differentiable (at x)"
proof -
  have fin: "finite {p. p permutes (UNIV::'n set)}"
    by (rule finite_permutations) simp
  have dterm: "(\<lambda>y. of_int (sign p) *
      (\<Prod>i\<in>UNIV. J y $ i $ p i)) differentiable (at x)"
    for p
    by (intro differentiable_mult differentiable_const
      differentiable_finite_prod matrix_entry_differentiable[OF assms])
       simp
  show ?thesis
    unfolding Determinants.det_def
    by (intro differentiable_sum) (use fin dterm in auto)
qed

lemma matrix_det_has_derivative_at_I:
  "((\<lambda>M::real ^ 'n::finite ^ 'n. Determinants.det M)
    has_derivative trace) (at (mat 1 :: real ^ 'n ^ 'n))"
proof -
  let ?I = "mat 1 :: real ^ 'n ^ 'n"
  let ?P = "{p. p permutes (UNIV::'n set)}"
  let ?T = "\<lambda>p M::real ^ 'n ^ 'n.
    of_int (sign p) * (\<Prod>i\<in>UNIV. M $ i $ p i)"
  let ?D = "\<lambda>p K::real ^ 'n ^ 'n.
    of_int (sign p) * (\<Sum>i\<in>UNIV. K $ i $ p i *
      (\<Prod>j\<in>UNIV - {i}. ?I $ j $ p j))"
  have fin: "finite ?P"
    by (rule finite_permutations) simp
  have dprod: "((\<lambda>M::real ^ 'n ^ 'n.
      \<Prod>i\<in>UNIV. M $ i $ p i)
      has_derivative (\<lambda>K. \<Sum>i\<in>UNIV.
        K $ i $ p i * (\<Prod>j\<in>UNIV - {i}. ?I $ j $ p j)))
      (at ?I)" for p
    by (rule has_derivative_prod)
       (rule matrix_entry_has_derivative)
  have dterm: "(?T p has_derivative ?D p) (at ?I)" for p
  proof -
    have dc: "((\<lambda>M::real ^ 'n ^ 'n. of_int (sign p))
      has_derivative (\<lambda>K. 0)) (at ?I)"
      by simp
    show ?thesis
      using has_derivative_mult[OF dc dprod[of p]]
      by simp
  qed
  have dsum: "((\<lambda>M. \<Sum>p\<in>?P. ?T p M)
      has_derivative (\<lambda>K. \<Sum>p\<in>?P. ?D p K))
      (at ?I)"
    by (rule has_derivative_sum) (rule dterm)
  have idP: "{id} \<subseteq> ?P"
    by (auto simp: permutes_id)
  have zero: "?D p K = 0" if "p \<in> ?P - {id}"
    for p K
    using permutes_nonid_det_derivative_term_zero[of p K]
      that by auto
  have Dsum: "(\<Sum>p\<in>?P. ?D p K) = trace K" for K
  proof -
    have "(\<Sum>p\<in>?P. ?D p K) =
      (\<Sum>p\<in>{id}. ?D p K)"
      by (rule sum.mono_neutral_cong_left[OF fin idP, symmetric])
         (use zero in auto)
    also have "\<dots> = trace K"
      by (simp add: trace_def mat_def sign_id)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding Determinants.det_def
    using dsum by (simp add: Dsum)
qed

lemma matrix_left_mul_has_derivative:
  fixes G A :: "real ^ 'n::finite ^ 'n"
  shows "((\<lambda>M. G ** M)
    has_derivative (\<lambda>K. G ** K)) (at A)"
proof -
  have lin: "linear (\<lambda>M::real ^ 'n ^ 'n. G ** M)"
    by (simp add: linear_iff matrix_add_ldistrib matrix_scalar_ac
      scalar_matrix_assoc[symmetric])
  have bl: "bounded_linear (\<lambda>M::real ^ 'n ^ 'n. G ** M)"
    using lin by (simp add: linear_conv_bounded_linear)
  show ?thesis
    by (rule bounded_linear.has_derivative[OF bl]) simp
qed

lemma matrix_det_has_derivative_invertible:
  fixes A G :: "real ^ 'n::finite ^ 'n"
  assumes inverse: "G ** A = mat 1"
  shows "((\<lambda>M::real ^ 'n ^ 'n. Determinants.det M)
    has_derivative
      (\<lambda>K. Determinants.det A * trace (G ** K))) (at A)"
proof -
  have dleft: "((\<lambda>M. G ** M)
    has_derivative (\<lambda>K. G ** K)) (at A)"
    by (rule matrix_left_mul_has_derivative)
  have detI: "((\<lambda>M::real ^ 'n ^ 'n. Determinants.det M)
    has_derivative trace) (at (G ** A))"
    using matrix_det_has_derivative_at_I inverse by simp
  have dcomp: "((\<lambda>M::real ^ 'n ^ 'n.
      Determinants.det (G ** M))
    has_derivative (\<lambda>K. trace (G ** K))) (at A)"
    by (rule has_derivative_compose[OF dleft detI])
  have dc: "((\<lambda>M::real ^ 'n ^ 'n.
      Determinants.det A) has_derivative (\<lambda>K. 0)) (at A)"
    by simp
  have dscaled: "((\<lambda>M::real ^ 'n ^ 'n.
      Determinants.det A * Determinants.det (G ** M))
    has_derivative
      (\<lambda>K. Determinants.det A * trace (G ** K))) (at A)"
    using has_derivative_mult[OF dc dcomp] by simp
  have detGA: "Determinants.det G * Determinants.det A = 1"
    using inverse by (simp add: det_mul[symmetric])
  have detAG: "Determinants.det A * Determinants.det G = 1"
    using detGA by (simp add: mult.commute)
  have eq: "Determinants.det A * Determinants.det (G ** M) =
      Determinants.det M" for M :: "real ^ 'n ^ 'n"
    by (simp add: det_mul detAG mult.assoc)
  have fun_eq: "(\<lambda>M::real ^ 'n ^ 'n.
      Determinants.det A * Determinants.det (G ** M)) =
    Determinants.det"
    by (rule ext) (rule eq)
  show ?thesis using dscaled by (simp only: fun_eq)
qed

lemma matrix_add_rdistrib_stokes:
  fixes A B C :: "real ^ 'n::finite ^ 'n"
  shows "(A + B) ** C = A ** C + B ** C"
  by (vector matrix_matrix_mult_def sum.distrib[symmetric]
    field_simps)

lemma matrix_mult_bounded_bilinear:
  "bounded_bilinear
    (\<lambda>(A::real ^ 'n::finite ^ 'n)
      (B::real ^ 'n ^ 'n). A ** B)"
proof -
  have left: "linear
      (\<lambda>B::real ^ 'n ^ 'n. (A::real ^ 'n ^ 'n) ** B)"
      for A
    by (simp add: linear_iff matrix_add_ldistrib matrix_scalar_ac
      scalar_matrix_assoc[symmetric])
  have right: "linear
      (\<lambda>A::real ^ 'n ^ 'n. A ** (B::real ^ 'n ^ 'n))"
      for B
    by (simp add: linear_iff matrix_add_rdistrib_stokes
      scalar_matrix_assoc[symmetric])
  have "bilinear
      (\<lambda>(A::real ^ 'n ^ 'n)
        (B::real ^ 'n ^ 'n). A ** B)"
    using left right by (simp add: bilinear_def)
  then show ?thesis
    by (simp add: bilinear_conv_bounded_bilinear)
qed

lemma matrix_inverse_field_derivative:
  fixes F G :: "real ^ 'n::finite \<Rightarrow> real ^ 'n ^ 'n"
  assumes openU: "open U" and xU: "x \<in> U"
    and inverse: "\<And>y. y \<in> U \<Longrightarrow> F y ** G y = mat 1"
    and left_inverse: "G x ** F x = mat 1"
    and dF: "F differentiable (at x)"
    and dG: "G differentiable (at x)"
  shows "frechet_derivative G (at x) h =
    - (G x ** (frechet_derivative F (at x) h ** G x))"
proof -
  have DF: "(F has_derivative frechet_derivative F (at x)) (at x)"
    using dF by (simp add: frechet_derivative_works)
  have DG: "(G has_derivative frechet_derivative G (at x)) (at x)"
    using dG by (simp add: frechet_derivative_works)
  have product: "((\<lambda>y. F y ** G y)
    has_derivative (\<lambda>h.
      F x ** frechet_derivative G (at x) h +
      frechet_derivative F (at x) h ** G x)) (at x)"
    by (rule bounded_bilinear.FDERIV
        [OF matrix_mult_bounded_bilinear DF DG])
  have zero: "((\<lambda>y. F y ** G y)
    has_derivative (\<lambda>h. 0)) (at x)"
    by (rule has_derivative_transform_within_open
        [OF has_derivative_const openU xU])
       (simp add: inverse)
  have D: "F x ** frechet_derivative G (at x) h +
      frechet_derivative F (at x) h ** G x = 0"
    using has_derivative_unique[OF product zero]
    by (simp add: fun_eq_iff)
  have "G x ** (F x ** frechet_derivative G (at x) h +
      frechet_derivative F (at x) h ** G x) = 0"
    by (simp add: D)
  then have "frechet_derivative G (at x) h +
      G x ** (frechet_derivative F (at x) h ** G x) = 0"
    by (simp add: matrix_add_ldistrib
      matrix_mul_assoc left_inverse)
  then show ?thesis
    by (simp add: eq_neg_iff_add_eq_0)
qed

lemma matrix_det_field_derivative:
  fixes F :: "real ^ 'n::finite \<Rightarrow> real ^ 'n ^ 'n"
    and G :: "real ^ 'n ^ 'n"
  assumes dF: "F differentiable (at x)"
    and inverse: "G ** F x = mat 1"
  shows "frechet_derivative
      (\<lambda>y. Determinants.det (F y)) (at x) h =
    Determinants.det (F x) *
      trace (G ** frechet_derivative F (at x) h)"
proof -
  have DF: "(F has_derivative frechet_derivative F (at x)) (at x)"
    using dF by (simp add: frechet_derivative_works)
  have det: "((\<lambda>M::real ^ 'n ^ 'n. Determinants.det M)
    has_derivative (\<lambda>K. Determinants.det (F x) *
      trace (G ** K))) (at (F x))"
    by (rule matrix_det_has_derivative_invertible[OF inverse])
  have chain: "((\<lambda>y. Determinants.det (F y))
    has_derivative (\<lambda>h. Determinants.det (F x) *
      trace (G ** frechet_derivative F (at x) h))) (at x)"
    by (rule has_derivative_compose[OF DF det])
  show ?thesis
    using frechet_derivative_at[OF chain]
    by (simp add: fun_eq_iff)
qed

lemma matrix_column_field_derivative:
  fixes G :: "real ^ 'n::finite \<Rightarrow> real ^ 'n ^ 'n"
  assumes dG: "G differentiable (at x)"
  shows "frechet_derivative
      (\<lambda>y. G y *v axis j 1) (at x) h =
    frechet_derivative G (at x) h *v axis j 1"
proof -
  have lin: "linear (\<lambda>M::real ^ 'n ^ 'n.
      M *v axis j 1)"
    by (simp add: linear_iff matrix_vector_mult_add_rdistrib
      scaleR_matrix_vector_assoc)
  have bl: "bounded_linear (\<lambda>M::real ^ 'n ^ 'n.
      M *v axis j 1)"
    using lin by (simp add: linear_conv_bounded_linear)
  have DG: "(G has_derivative frechet_derivative G (at x)) (at x)"
    using dG by (simp add: frechet_derivative_works)
  have chain: "((\<lambda>y. G y *v axis j 1)
    has_derivative
      (\<lambda>h. frechet_derivative G (at x) h *v axis j 1))
    (at x)"
    by (rule bounded_linear.has_derivative[OF bl DG])
  show ?thesis
    using frechet_derivative_at[OF chain]
    by (simp add: fun_eq_iff)
qed

lemma matrix_column_field_differentiable:
  fixes G :: "real ^ 'n::finite \<Rightarrow> real ^ 'n ^ 'n"
  assumes "G differentiable (at x)"
  shows "(\<lambda>y. G y *v axis j 1) differentiable (at x)"
proof -
  have lin: "linear (\<lambda>M::real ^ 'n ^ 'n. M *v axis j 1)"
    by (simp add: linear_iff matrix_vector_mult_add_rdistrib
      scaleR_matrix_vector_assoc)
  have "((\<lambda>M::real ^ 'n ^ 'n. M *v axis j 1) \<circ> G)
    differentiable (at x)"
    by (rule differentiable_chain_at[OF assms])
       (simp add: lin linear_imp_differentiable)
  then show ?thesis by (simp add: comp_def)
qed

lemma matrix_vector_mul_minus_stokes:
  fixes M :: "real ^ 'n::finite ^ 'n"
  shows "(- M) *v v = - (M *v v)"
  using scaleR_matrix_vector_assoc[of "-1" M v] by simp

lemma piola_trace_component:
  fixes G H :: "real ^ 'n::finite ^ 'n"
  shows "trace (G ** H) * (G *v axis j 1) $ i =
    (\<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G $ b $ a * H $ a $ b * G $ i $ j)"
proof -
  have "trace (G ** H) * (G *v axis j 1) $ i =
    (\<Sum>b\<in>UNIV. \<Sum>a\<in>UNIV.
      G $ b $ a * H $ a $ b * G $ i $ j)"
    by (simp add: trace_def matrix_matrix_mult_def
      matrix_vector_mult_basis column_def
      sum_distrib_left sum_distrib_right algebra_simps)
  also have "\<dots> =
    (\<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G $ b $ a * H $ a $ b * G $ i $ j)"
    by (rule sum.swap)
  finally show ?thesis .
qed

lemma piola_inverse_component:
  fixes G H :: "real ^ 'n::finite ^ 'n"
  shows "(G ** (H ** G) *v axis j 1) $ i =
    (\<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G $ i $ a * H $ a $ b * G $ b $ j)"
  by (simp add: matrix_matrix_mult_def
    matrix_vector_mult_basis column_def
    sum_distrib_left algebra_simps)

lemma piola_matrix_field_closed_from_inverse_derivative:
  fixes F G :: "real ^ 'n::finite \<Rightarrow> real ^ 'n ^ 'n"
  assumes left_inverse: "G x ** F x = mat 1"
    and dF: "F differentiable (at x)"
    and dG: "G differentiable (at x)"
    and mixed: "\<And>i a b.
      frechet_derivative F (at x) (axis i 1) $ a $ b =
      frechet_derivative F (at x) (axis b 1) $ a $ i"
    and inverse_dG: "\<And>i. frechet_derivative G (at x) (axis i 1) =
      - (G x ** (frechet_derivative F (at x) (axis i 1) ** G x))"
  shows "exterior_top
    (\<lambda>y. Determinants.det (F y) *\<^sub>R
      (G y *v axis j 1)) x = 0"
proof -
  let ?H = "\<lambda>i. frechet_derivative F (at x) (axis i 1)"
  let ?r = "Determinants.det (F x)"
  let ?rho = "\<lambda>y. Determinants.det (F y)"
  let ?V = "\<lambda>y. G y *v axis j 1"
  have drho: "?rho differentiable (at x)"
    by (rule matrix_det_differentiable[OF dF])
  have dV: "?V differentiable (at x)"
    by (rule matrix_column_field_differentiable[OF dG])
  have det_term: "frechet_derivative ?rho (at x) (axis i 1) *
      ?V x $ i =
    ?r * (\<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G x $ b $ a * ?H i $ a $ b * G x $ i $ j)"
    for i
    by (simp add: matrix_det_field_derivative[OF dF left_inverse]
      piola_trace_component)
  have inv_term: "frechet_derivative ?V (at x) (axis i 1) $ i =
    - (\<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G x $ i $ a * ?H i $ a $ b * G x $ b $ j)"
    for i
    by (simp add: matrix_column_field_derivative[OF dG]
      inverse_dG
      matrix_vector_mul_minus_stokes piola_inverse_component)
  have pos: "(\<Sum>i\<in>UNIV.
      frechet_derivative ?rho (at x) (axis i 1) * ?V x $ i) =
    ?r * (\<Sum>i\<in>UNIV. \<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G x $ b $ a * ?H i $ a $ b * G x $ i $ j)"
    by (simp add: det_term sum_distrib_left)
  have neg: "exterior_top ?V x =
    - (\<Sum>i\<in>UNIV. \<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G x $ i $ a * ?H i $ a $ b * G x $ b $ j)"
    by (simp add: exterior_top_coordinate inv_term sum_negf)
  have cancel: "(\<Sum>i\<in>UNIV. \<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G x $ b $ a * ?H i $ a $ b * G x $ i $ j) =
    (\<Sum>i\<in>UNIV. \<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV.
      G x $ i $ a * ?H i $ a $ b * G x $ b $ j)"
    by (rule piola_coordinate_cancellation[OF mixed])
  have "exterior_top
    (\<lambda>y. Determinants.det (F y) *\<^sub>R
      (G y *v axis j 1)) x =
    ?r * exterior_top ?V x +
      (\<Sum>i\<in>UNIV.
        frechet_derivative ?rho (at x) (axis i 1) * ?V x $ i)"
    by (rule exterior_top_scale[OF drho dV])
  then show ?thesis
    by (simp add: pos neg cancel)
qed

theorem piola_matrix_field_closed:
  fixes F G :: "real ^ 'n::finite \<Rightarrow> real ^ 'n ^ 'n"
  assumes openU: "open U" and xU: "x \<in> U"
    and inverse: "\<And>y. y \<in> U \<Longrightarrow> F y ** G y = mat 1"
    and left_inverse: "G x ** F x = mat 1"
    and dF: "F differentiable (at x)"
    and dG: "G differentiable (at x)"
    and mixed: "\<And>i a b.
      frechet_derivative F (at x) (axis i 1) $ a $ b =
      frechet_derivative F (at x) (axis b 1) $ a $ i"
  shows "exterior_top
    (\<lambda>y. Determinants.det (F y) *\<^sub>R
      (G y *v axis j 1)) x = 0"
  by (rule piola_matrix_field_closed_from_inverse_derivative
      [OF left_inverse dF dG mixed])
    (rule matrix_inverse_field_derivative
      [OF openU xU inverse left_inverse dF dG])

theorem cofactor_column_closed_if_mixed:
  fixes f g :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes openU: "open U" and xU: "x \<in> U"
    and df: "f differentiable (at x)"
    and dJf: "(\<lambda>y. jacobian f (at y)) differentiable (at x)"
    and dJg: "(\<lambda>y. jacobian g (at y))
      differentiable (at (f x))"
    and inverse: "\<And>y. y \<in> U \<Longrightarrow>
      jacobian f (at y) ** jacobian g (at (f y)) = mat 1"
    and mixed: "\<And>i a b.
      frechet_derivative (\<lambda>y. jacobian f (at y))
        (at x) (axis i 1) $ a $ b =
      frechet_derivative (\<lambda>y. jacobian f (at y))
        (at x) (axis b 1) $ a $ i"
  shows "exterior_top (cofactor_column f g j) x = 0"
proof -
  let ?F = "\<lambda>y. jacobian f (at y)"
  let ?G = "\<lambda>y. jacobian g (at (f y))"
  have dG: "?G differentiable (at x)"
    using differentiable_chain_at[OF df dJg]
    by (simp add: comp_def)
  have left: "?G x ** ?F x = mat 1"
    using inverse[OF xU] by (rule matrix_left_right_inverse1)
  have "exterior_top
      (\<lambda>y. Determinants.det (?F y) *\<^sub>R
        (?G y *v axis j 1)) x = 0"
    by (rule piola_matrix_field_closed
        [OF openU xU inverse left dJf dG mixed])
  moreover have "cofactor_column f g j =
      (\<lambda>y. Determinants.det (?F y) *\<^sub>R
        (?G y *v axis j 1))"
    by (rule ext) (simp add: cofactor_column_def)
  ultimately show ?thesis by simp
qed

lemma jacobian_component_gradient:
  fixes f :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes df: "f differentiable (at x)"
  shows "jacobian f (at x) $ a $ b =
    \<nabla> (\<lambda>y. f y $ a) x $ b"
proof -
  let ?fa = "\<lambda>y. f y $ a"
  have lin: "linear (\<lambda>v::real ^ 'n. v $ a)"
    by (simp add: linear_iff)
  have dfa: "?fa differentiable (at x)"
    using differentiable_chain_at
      [OF df linear_imp_differentiable[OF lin]]
    by (simp add: comp_def)
  obtain ga where ga: "GDERIV ?fa x :> ga"
    using Fr_diff_imp_gradient_exists[OF dfa] by blast
  have grad: "GDERIV ?fa x :> \<nabla> ?fa x"
    by (rule grad_fun_satisfies_GDERIV[OF ga])
  have Dfa: "(?fa has_derivative frechet_derivative ?fa (at x)) (at x)"
    using dfa by (simp add: frechet_derivative_works)
  have "jacobian f (at x) $ a $ b =
      frechet_derivative ?fa (at x) (axis b 1)"
    by (rule jacobian_component[OF df])
  also have "\<dots> = axis b 1 \<bullet> \<nabla> ?fa x"
    by (rule frechet_eq_inner_gradient[OF Dfa grad])
  also have "\<dots> = \<nabla> ?fa x $ b"
    by (simp add: cart_eq_inner_axis inner_commute)
  finally show ?thesis .
qed

lemma scalar_partial_eq_grad:
  fixes f :: "real ^ 'n::finite \<Rightarrow> real"
  assumes df: "f differentiable (at x)"
  shows "frechet_derivative f (at x) (axis i 1) =
    \<nabla> f x $ i"
proof -
  obtain g where g: "GDERIV f x :> g"
    using Fr_diff_imp_gradient_exists[OF df] by blast
  have grad: "GDERIV f x :> \<nabla> f x"
    by (rule grad_fun_satisfies_GDERIV[OF g])
  have Df: "(f has_derivative frechet_derivative f (at x)) (at x)"
    using df by (simp add: frechet_derivative_works)
  have "frechet_derivative f (at x) (axis i 1) =
    axis i 1 \<bullet> \<nabla> f x"
    by (rule frechet_eq_inner_gradient[OF Df grad])
  then show ?thesis
    by (simp add: cart_eq_inner_axis inner_commute)
qed

lemma Ck_on_2_grad_component_differentiable:
  fixes f :: "real ^ 'n::finite \<Rightarrow> real"
  assumes C2: "Ck_on 2 f U" and xU: "x \<in> U"
  shows "(\<lambda>y. \<nabla> f y $ b) differentiable (at x)"
proof -
  have openU: "open U" by (rule Ck_on_open[OF C2])
  have C2': "Ck_on (Suc 1) f U"
    using C2 by (metis Suc_1)
  have df_on: "f differentiable (at y)" if "y \<in> U" for y
    using Ck_on_Suc_iff[of 1 f U, THEN iffD1, OF C2']
      that by blast
  have C1: "Ck_on 1
      (\<lambda>y. frechet_derivative f (at y) (axis b 1)) U"
    using Ck_on_Suc_iff[of 1 f U, THEN iffD1, OF C2']
    by blast
  have dD: "(\<lambda>y. frechet_derivative f (at y) (axis b 1))
      differentiable (at x)"
    using Ck_onD[OF C1 xU] by simp
  have eq_on: "frechet_derivative f (at y) (axis b 1) =
      \<nabla> f y $ b" if "y \<in> U" for y
    by (rule scalar_partial_eq_grad[OF df_on[OF that]])
  show ?thesis
    by (rule differentiable_transform_within_open
        [OF dD openU xU]) (rule eq_on)
qed

lemma Ck_on_2_jacobian_entry_differentiable:
  fixes f :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes C2: "Ck_on 2 f U" and xU: "x \<in> U"
  shows "(\<lambda>y. jacobian f (at y) $ a $ b)
    differentiable (at x)"
proof -
  let ?fa = "\<lambda>y. f y $ a"
  have openU: "open U" by (rule Ck_on_open[OF C2])
  have C2a: "Ck_on 2 ?fa U"
    by (rule Ck_on_component[OF C2])
  have dgrad: "(\<lambda>y. \<nabla> ?fa y $ b)
    differentiable (at x)"
    by (rule Ck_on_2_grad_component_differentiable[OF C2a xU])
  have C2': "Ck_on (Suc 1) f U"
    using C2 by (metis Suc_1)
  have df_on: "f differentiable (at y)" if "y \<in> U" for y
    using Ck_on_Suc_iff[of 1 f U, THEN iffD1, OF C2']
      that by blast
  have eq_on: "\<nabla> ?fa y $ b =
      jacobian f (at y) $ a $ b" if "y \<in> U" for y
    using jacobian_component_gradient[OF df_on[OF that]]
    by simp
  show ?thesis
    by (rule differentiable_transform_within_open
        [OF dgrad openU xU]) (rule eq_on)
qed

lemma Ck_on_2_jacobian_differentiable:
  fixes f :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes C2: "Ck_on 2 f U" and xU: "x \<in> U"
  shows "(\<lambda>y. jacobian f (at y)) differentiable (at x)"
proof -
  have "\<forall>a\<in>(Basis :: (real ^ 'n ^ 'n) set).
      (\<lambda>y. jacobian f (at y) \<bullet> a)
        differentiable (at x within UNIV)"
    using Ck_on_2_jacobian_entry_differentiable[OF C2 xU]
    by (auto simp: Basis_vec_def inner_axis)
  then show ?thesis
    using differentiable_componentwise_within
      [of "(\<lambda>y. jacobian f (at y))" x UNIV]
    by simp
qed

lemma matrix_field_entry_derivative:
  fixes F :: "'a::euclidean_space \<Rightarrow> real ^ 'n::finite ^ 'n"
  assumes dF: "F differentiable (at x)"
  shows "frechet_derivative (\<lambda>y. F y $ a $ b)
      (at x) h =
    frechet_derivative F (at x) h $ a $ b"
proof -
  have DF: "(F has_derivative frechet_derivative F (at x)) (at x)"
    using dF by (simp add: frechet_derivative_works)
  have entry: "((\<lambda>M::real ^ 'n ^ 'n. M $ a $ b)
    has_derivative (\<lambda>K. K $ a $ b)) (at (F x))"
    by (rule matrix_entry_has_derivative)
  have chain: "((\<lambda>y. F y $ a $ b)
    has_derivative
      (\<lambda>h. frechet_derivative F (at x) h $ a $ b)) (at x)"
    by (rule has_derivative_compose[OF DF entry])
  show ?thesis
    using frechet_derivative_at[OF chain]
    by (simp add: fun_eq_iff)
qed

lemma Ck_on_2_jacobian_mixed:
  fixes f :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes C2: "Ck_on 2 f U" and xU: "x \<in> U"
  shows "frechet_derivative (\<lambda>y. jacobian f (at y))
      (at x) (axis i 1) $ a $ b =
    frechet_derivative (\<lambda>y. jacobian f (at y))
      (at x) (axis b 1) $ a $ i"
proof -
  let ?fa = "\<lambda>y. f y $ a"
  let ?J = "\<lambda>y. jacobian f (at y)"
  have openU: "open U" by (rule Ck_on_open[OF C2])
  have C2a: "Ck_on 2 ?fa U"
    by (rule Ck_on_component[OF C2])
  have dJ: "?J differentiable (at x)"
    by (rule Ck_on_2_jacobian_differentiable[OF C2 xU])
  have C2': "Ck_on (Suc 1) f U"
    using C2 by (metis Suc_1)
  have df_on: "f differentiable (at y)" if "y \<in> U" for y
    using Ck_on_Suc_iff[of 1 f U, THEN iffD1, OF C2']
      that by blast
  have dgrad_b: "(\<lambda>y. \<nabla> ?fa y $ b) differentiable (at x)"
    by (rule Ck_on_2_grad_component_differentiable[OF C2a xU])
  have dgrad_i: "(\<lambda>y. \<nabla> ?fa y $ i) differentiable (at x)"
    by (rule Ck_on_2_grad_component_differentiable[OF C2a xU])
  have eq_b: "frechet_derivative
      (\<lambda>y. ?J y $ a $ b) (at x) =
    frechet_derivative
      (\<lambda>y. \<nabla> ?fa y $ b) (at x)"
    by (rule frechet_derivative_transform_within_open
        [OF openU xU])
       (use df_on in \<open>auto simp: jacobian_component_gradient\<close>)
  have eq_i: "frechet_derivative
      (\<lambda>y. ?J y $ a $ i) (at x) =
    frechet_derivative
      (\<lambda>y. \<nabla> ?fa y $ i) (at x)"
    by (rule frechet_derivative_transform_within_open
        [OF openU xU])
       (use df_on in \<open>auto simp: jacobian_component_gradient\<close>)
  have L: "frechet_derivative
      (\<lambda>y. ?J y $ a $ b) (at x) (axis i 1) =
    \<nabla> (\<lambda>y. \<nabla> ?fa y $ b) x $ i"
    using eq_b scalar_partial_eq_grad[OF dgrad_b] by simp
  have R: "frechet_derivative
      (\<lambda>y. ?J y $ a $ i) (at x) (axis b 1) =
    \<nabla> (\<lambda>y. \<nabla> ?fa y $ i) x $ b"
    using eq_i scalar_partial_eq_grad[OF dgrad_i] by simp
  have swap: "\<nabla> (\<lambda>y. \<nabla> ?fa y $ b) x $ i =
    \<nabla> (\<lambda>y. \<nabla> ?fa y $ i) x $ b"
    by (rule mixed_coordinate_second_derivative_eq[OF openU xU C2a])
  show ?thesis
    using L R swap matrix_field_entry_derivative[OF dJ]
    by simp
qed

lemma jacobian_local_inverse:
  fixes f g :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes openU: "open U" and xU: "x \<in> U"
    and df: "f differentiable (at x)"
    and dg: "g differentiable (at (f x))"
    and inverse: "\<And>y. y \<in> U \<Longrightarrow> g (f y) = y"
  shows "jacobian f (at x) ** jacobian g (at (f x)) = mat 1"
proof -
  have derivative_eq:
    "frechet_derivative (g \<circ> f) (at x) =
      frechet_derivative id (at x)"
    by (rule frechet_derivative_transform_within_open
        [OF openU xU])
       (simp add: inverse comp_def)
  have "jacobian g (at (f x)) ** jacobian f (at x) = mat 1"
    using jacobian_compose_at[OF df dg] derivative_eq
    by (simp add: jacobian_def matrix_id_mat_1)
  then show ?thesis by (rule matrix_left_right_inverse1)
qed

theorem cofactor_column_closed_C2:
  fixes f g :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes C2f: "Ck_on 2 f U" and xU: "x \<in> U"
    and C2g: "Ck_on 2 g V"
    and image: "\<And>y. y \<in> U \<Longrightarrow> f y \<in> V"
    and inverse: "\<And>y. y \<in> U \<Longrightarrow> g (f y) = y"
  shows "exterior_top (cofactor_column f g j) x = 0"
proof -
  have openU: "open U" by (rule Ck_on_open[OF C2f])
  have C2f': "Ck_on (Suc 1) f U"
    using C2f by (metis Suc_1)
  have C2g': "Ck_on (Suc 1) g V"
    using C2g by (metis Suc_1)
  have df_on: "f differentiable (at y)" if "y \<in> U" for y
    using Ck_on_Suc_iff[of 1 f U, THEN iffD1, OF C2f']
      that by blast
  have dg_on: "g differentiable (at z)" if "z \<in> V" for z
    using Ck_on_Suc_iff[of 1 g V, THEN iffD1, OF C2g']
      that by blast
  have invJ: "jacobian f (at y) **
      jacobian g (at (f y)) = mat 1" if "y \<in> U" for y
    by (rule jacobian_local_inverse
        [OF openU that df_on[OF that] dg_on[OF image[OF that]]])
       (rule inverse)
  have dJf: "(\<lambda>y. jacobian f (at y)) differentiable (at x)"
    by (rule Ck_on_2_jacobian_differentiable[OF C2f xU])
  have dJg: "(\<lambda>y. jacobian g (at y))
      differentiable (at (f x))"
    by (rule Ck_on_2_jacobian_differentiable
        [OF C2g image[OF xU]])
  show ?thesis
  proof (rule cofactor_column_closed_if_mixed
      [OF openU xU df_on[OF xU] dJf dJg])
    show "\<And>y. y \<in> U \<Longrightarrow>
      jacobian f (at y) ** jacobian g (at (f y)) = mat 1"
      by (rule invJ)
    show "\<And>i a b.
      frechet_derivative (\<lambda>y. jacobian f (at y))
        (at x) (axis i 1) $ a $ b =
      frechet_derivative (\<lambda>y. jacobian f (at y))
        (at x) (axis b 1) $ a $ i"
      by (rule Ck_on_2_jacobian_mixed[OF C2f xU])
  qed
qed

lemma cofactor_column_differentiable:
  fixes f g :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes "f differentiable (at x)"
    and "(\<lambda>y. jacobian f (at y)) differentiable (at x)"
    and "(\<lambda>y. jacobian g (at y))
      differentiable (at (f x))"
  shows "cofactor_column f g j differentiable (at x)"
proof -
  have ddet: "(\<lambda>y. Determinants.det (jacobian f (at y)))
      differentiable (at x)"
    by (rule matrix_det_differentiable[OF assms(2)])
  have dJg: "(\<lambda>y. jacobian g (at (f y)))
      differentiable (at x)"
    using differentiable_chain_at[OF assms(1,3)]
    by (simp add: comp_def)
  have lin: "linear (\<lambda>M::real ^ 'n ^ 'n. M *v axis j 1)"
    by (simp add: linear_iff matrix_vector_mult_add_rdistrib
      scaleR_matrix_vector_assoc)
  have dvec: "(\<lambda>y. jacobian g (at (f y)) *v axis j 1)
      differentiable (at x)"
    using differentiable_chain_at[OF dJg
      linear_imp_differentiable[OF lin]]
    by (simp add: comp_def)
  show ?thesis
    unfolding cofactor_column_def
    by (rule differentiable_scaleR[OF ddet dvec])
qed

lemma pull_near_top_differentiable:
  fixes f g A :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes df: "f differentiable (at x)"
    and dA: "A differentiable (at (f x))"
    and dJf: "(\<lambda>y. jacobian f (at y)) differentiable (at x)"
    and dJg: "(\<lambda>y. jacobian g (at y))
      differentiable (at (f x))"
  shows "pull_near_top f g A differentiable (at x)"
proof -
  have dC: "cofactor_column f g j differentiable (at x)" for j
    by (rule cofactor_column_differentiable
        [OF df dJf dJg])
  have dterm: "(\<lambda>y. A (f y) $ j *\<^sub>R
      cofactor_column f g j y) differentiable (at x)" for j
    by (rule differentiable_scaleR
        [OF pullback_component_differentiable[OF df dA] dC])
  have eq: "pull_near_top f g A =
      (\<lambda>y. \<Sum>j\<in>UNIV. A (f y) $ j *\<^sub>R
        cofactor_column f g j y)"
    by (rule ext) (rule pull_near_top_cofactor_sum)
  show ?thesis
    unfolding eq
    by (rule differentiable_sum)
       (auto intro: dterm)
qed

lemma pull_near_top_differentiable_C2:
  fixes f g A :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes C2f: "Ck_on 2 f U" and xU: "x \<in> U"
    and C2g: "Ck_on 2 g V" and image: "f x \<in> V"
    and dA: "A differentiable (at (f x))"
  shows "pull_near_top f g A differentiable (at x)"
proof -
  have C2f': "Ck_on (Suc 1) f U"
    using C2f by (metis Suc_1)
  have df: "f differentiable (at x)"
    using Ck_on_Suc_iff[of 1 f U, THEN iffD1, OF C2f']
      xU by blast
  have dJf: "(\<lambda>y. jacobian f (at y)) differentiable (at x)"
    by (rule Ck_on_2_jacobian_differentiable[OF C2f xU])
  have dJg: "(\<lambda>y. jacobian g (at y))
      differentiable (at (f x))"
    by (rule Ck_on_2_jacobian_differentiable[OF C2g image])
  show ?thesis
    by (rule pull_near_top_differentiable[OF df dA dJf dJg])
qed

theorem exterior_top_pull_near_top_if_piola:
  fixes f g A :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes "f differentiable (at x)"
    and "A differentiable (at (f x))"
    and "jacobian f (at x) ** jacobian g (at (f x)) = mat 1"
    and "(\<lambda>y. jacobian f (at y)) differentiable (at x)"
    and "(\<lambda>y. jacobian g (at y))
      differentiable (at (f x))"
    and "\<And>j. exterior_top (cofactor_column f g j) x = 0"
  shows "exterior_top (pull_near_top f g A) x =
    pull_top f (exterior_top A) x"
  by (rule exterior_top_pull_near_top_if_cofactor_closed)
     (use assms in \<open>auto intro: cofactor_column_differentiable\<close>)

theorem exterior_top_pull_near_top_C2:
  fixes f g A :: "real ^ 'n::finite \<Rightarrow> real ^ 'n"
  assumes C2f: "Ck_on 2 f U" and xU: "x \<in> U"
    and C2g: "Ck_on 2 g V"
    and image: "\<And>y. y \<in> U \<Longrightarrow> f y \<in> V"
    and inverse: "\<And>y. y \<in> U \<Longrightarrow> g (f y) = y"
    and dA: "A differentiable (at (f x))"
  shows "exterior_top (pull_near_top f g A) x =
    pull_top f (exterior_top A) x"
proof -
  have openU: "open U" by (rule Ck_on_open[OF C2f])
  have C2f': "Ck_on (Suc 1) f U"
    using C2f by (metis Suc_1)
  have C2g': "Ck_on (Suc 1) g V"
    using C2g by (metis Suc_1)
  have df: "f differentiable (at x)"
    using Ck_on_Suc_iff[of 1 f U, THEN iffD1, OF C2f']
      xU by blast
  have dg: "g differentiable (at (f x))"
    using Ck_on_Suc_iff[of 1 g V, THEN iffD1, OF C2g']
      image[OF xU] by blast
  have inverse_J:
    "jacobian f (at x) ** jacobian g (at (f x)) = mat 1"
    by (rule jacobian_local_inverse[OF openU xU df dg])
       (rule inverse)
  have dJf: "(\<lambda>y. jacobian f (at y)) differentiable (at x)"
    by (rule Ck_on_2_jacobian_differentiable[OF C2f xU])
  have dJg: "(\<lambda>y. jacobian g (at y))
      differentiable (at (f x))"
    by (rule Ck_on_2_jacobian_differentiable
        [OF C2g image[OF xU]])
  have piola: "exterior_top (cofactor_column f g j) x = 0"
    for j
    by (rule cofactor_column_closed_C2
        [OF C2f xU C2g image inverse])
  show ?thesis
    by (rule exterior_top_pull_near_top_if_piola
        [OF df dA inverse_J dJf dJg piola])
qed

lemma trace_matrix_conjugate:
  fixes F G M :: "real ^ 'n::finite ^ 'n"
  assumes "F ** G = mat 1"
  shows "trace (G ** M ** F) = trace M"
proof -
  have "trace (G ** M ** F) = trace (G ** (M ** F))"
    by (simp add: matrix_mul_assoc)
  also have "\<dots> = trace ((M ** F) ** G)"
    by (rule trace_mul_sym)
  also have "\<dots> = trace (M ** (F ** G))"
    by (simp add: matrix_mul_assoc)
  also have "\<dots> = trace M"
    by (simp add: assms)
  finally show ?thesis .
qed

lemma trace_mat_left:
  fixes M :: "real ^ 'n::finite ^ 'n"
  shows "trace (mat r ** M) = r * trace M"
proof -
  have inner: "(\<Sum>k\<in>UNIV. (if i = k then r else 0) * M $ k $ i) =
      r * M $ i $ i" for i
  proof -
    have "(\<Sum>k\<in>UNIV. (if i = k then r else 0) * M $ k $ i) =
        (\<Sum>k\<in>UNIV. if k = i then r * M $ i $ i else 0)"
      by (rule sum.cong) auto
    also have "\<dots> = r * M $ i $ i"
      by simp
    finally show ?thesis .
  qed
  show ?thesis
    by (simp add: trace_def matrix_matrix_mult_def mat_def
      inner sum_distrib_left)
qed

lemma affine_map_frechet_derivative:
  fixes F :: "real ^ 'n::finite ^ 'n"
  shows "frechet_derivative (\<lambda>y. F *v y + c) (at x) =
    (\<lambda>h. F *v h)"
proof (rule frechet_derivative_at[symmetric])
  have d: "((\<lambda>y. F *v y) has_derivative (\<lambda>h. F *v h))
      (at x)"
    by (rule linear_imp_has_derivative) simp
  show "((\<lambda>y. F *v y + c) has_derivative
      (\<lambda>h. F *v h)) (at x)"
    by (rule has_derivative_add_const[OF d])
qed

lemma jacobian_affine_map [simp]:
  fixes F :: "real ^ 'n::finite ^ 'n"
  shows "jacobian (\<lambda>y. F *v y + c) (at x) = F"
  by (simp add: jacobian_def affine_map_frechet_derivative)

lemma jacobian_affine_inverse_map [simp]:
  fixes G :: "real ^ 'n::finite ^ 'n"
  shows "jacobian (\<lambda>y. G *v (y - c)) (at x) = G"
proof -
  have eq: "(\<lambda>y. G *v (y - c)) =
      (\<lambda>y. G *v y + -(G *v c))"
    by (rule ext) (simp add: matrix_vector_mult_diff_distrib)
  show ?thesis unfolding eq
    by (rule jacobian_affine_map)
qed

lemma cofactor_column_affine_closed:
  fixes F G :: "real ^ 'n::finite ^ 'n"
  shows "exterior_top
    (cofactor_column (\<lambda>y. F *v y + c)
      (\<lambda>y. G *v (y - c)) j) x = 0"
proof -
  have eq: "cofactor_column (\<lambda>y. F *v y + c)
      (\<lambda>y. G *v (y - c)) j =
    (\<lambda>y. Determinants.det F *\<^sub>R (G *v axis j 1))"
    by (rule ext) (simp add: cofactor_column_def)
  show ?thesis unfolding eq by simp
qed

lemma pull_top_affine_eq_pull_top:
  fixes F :: "real ^ 'n::finite ^ 'n"
  shows "pull_top_affine F c T =
    pull_top (\<lambda>y. F *v y + c) T"
  by (rule ext) (simp add: pull_top_affine_def pull_top_def)

lemma pull_near_top_affine_eq_pull_near_top:
  fixes F G :: "real ^ 'n::finite ^ 'n"
  shows "pull_near_top_affine F G c A =
    pull_near_top (\<lambda>y. F *v y + c)
      (\<lambda>y. G *v (y - c)) A"
  by (rule ext)
     (simp add: pull_near_top_affine_def pull_near_top_def)

lemma pull_near_top_affine_frechet_derivative:
  fixes F G :: "real ^ 'n::finite ^ 'n"
  assumes diff_A: "A differentiable (at (F *v x + c))"
  shows "frechet_derivative (pull_near_top_affine F G c A) (at x) =
    (\<lambda>h. Determinants.det F *\<^sub>R
      (G *v frechet_derivative A (at (F *v x + c)) (F *v h)))"
proof -
  let ?phi = "\<lambda>y. F *v y + c"
  let ?S = "\<lambda>v. Determinants.det F *\<^sub>R (G *v v)"
  have dphi: "(?phi has_derivative (\<lambda>h. F *v h)) (at x)"
    by (rule has_derivative_add_const)
       (rule linear_imp_has_derivative, simp)
  have dA: "(A has_derivative frechet_derivative A (at (?phi x)))
      (at (?phi x))"
    using diff_A by (simp add: frechet_derivative_works)
  have dAphi: "((A \<circ> ?phi) has_derivative
      (frechet_derivative A (at (?phi x)) \<circ> (\<lambda>h. F *v h)))
      (at x)"
    by (rule diff_chain_at[OF dphi dA])
  have linear_S: "linear ?S"
    by (simp add: linear_iff matrix_vector_right_distrib
      matrix_vector_mult_scaleR scaleR_right_distrib scaleR_scaleR)
  have dS: "(?S has_derivative ?S) (at (A (?phi x)))"
    by (rule linear_imp_has_derivative[OF linear_S])
  have d: "((?S \<circ> (A \<circ> ?phi)) has_derivative
      (?S \<circ> (frechet_derivative A (at (?phi x)) \<circ>
        (\<lambda>h. F *v h)))) (at x)"
    by (rule diff_chain_at[OF dAphi]) (simp add: dS)
  have eq: "pull_near_top_affine F G c A = ?S \<circ> (A \<circ> ?phi)"
    by (rule ext) (simp add: pull_near_top_affine_def)
  show ?thesis
    unfolding eq
    using frechet_derivative_at[OF d] by (simp add: comp_def)
qed

lemma matrix_linear_pullback:
  fixes F G :: "real ^ 'n::finite ^ 'n"
    and D :: "real ^ 'n \<Rightarrow> real ^ 'n"
  assumes "linear D"
  shows "matrix (\<lambda>h. r *\<^sub>R (G *v D (F *v h))) =
    mat r ** G ** matrix D ** F"
proof -
  let ?g = "\<lambda>v. G *v v"
  let ?f = "\<lambda>h. F *v h"
  let ?s = "(*\<^sub>R) r"
  have lg: "linear ?g" by simp
  have lf: "linear ?f" by simp
  have ls: "linear ?s" by simp
  have "matrix (\<lambda>h. r *\<^sub>R (G *v D (F *v h))) =
      matrix (?s \<circ> (?g \<circ> (D \<circ> ?f)))"
    by (simp add: comp_def)
  also have "\<dots> = matrix ?s ** matrix ?g ** matrix D ** matrix ?f"
    by (simp add: matrix_compose[OF lf assms]
      matrix_compose[OF _ lg] matrix_compose[OF _ ls]
      linear_compose lf lg assms matrix_mul_assoc)
  also have "\<dots> = mat r ** G ** matrix D ** F"
    by (simp add: matrix_scaleR)
  finally show ?thesis .
qed

theorem exterior_top_pull_near_top_affine:
  fixes F G :: "real ^ 'n::finite ^ 'n"
  assumes "F ** G = mat 1"
    and "A differentiable (at (F *v x + c))"
  shows "exterior_top (pull_near_top_affine F G c A) x =
    pull_top_affine F c (exterior_top A) x"
proof -
  let ?D = "frechet_derivative A (at (F *v x + c))"
  let ?M = "matrix ?D"
  have linD: "linear ?D"
    using assms(2) by (rule linear_frechet_derivative)
  have "exterior_top (pull_near_top_affine F G c A) x =
      trace (mat (Determinants.det F) ** G ** ?M ** F)"
    unfolding exterior_top_def
    by (simp add: pull_near_top_affine_frechet_derivative[OF assms(2)]
      matrix_linear_pullback[OF linD])
  also have "\<dots> = Determinants.det F * trace ?M"
  proof -
    have "trace (mat (Determinants.det F) ** G ** ?M ** F) =
        trace (mat (Determinants.det F) ** (G ** ?M ** F))"
      by (simp add: matrix_mul_assoc)
    also have "\<dots> =
        Determinants.det F * trace (G ** ?M ** F)"
      by (rule trace_mat_left)
    also have "\<dots> = Determinants.det F * trace ?M"
      by (simp add: trace_matrix_conjugate[OF assms(1)])
    finally show ?thesis .
  qed
  also have "\<dots> = pull_top_affine F c (exterior_top A) x"
    by (simp add: pull_top_affine_def exterior_top_def)
  finally show ?thesis .
qed

end
