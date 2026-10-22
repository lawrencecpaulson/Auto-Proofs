theory Product_Forms
  imports Form_Bridge
begin

text \<open>
  A near-top form on product coordinates is represented by its
  volume-contracted vector field.  The normal coordinate comes first.
\<close>

definition product_exterior_top ::
    "(real \<times> 'a::euclidean_space \<Rightarrow> real \<times> 'a) \<Rightarrow>
      real \<times> 'a \<Rightarrow> real"
  where "product_exterior_top A p =
    fst (frechet_derivative A (at p) (1,0)) +
      (\<Sum>b\<in>Basis. snd (frechet_derivative A (at p) (0,b)) \<bullet> b)"

definition product_normal_coeff ::
    "(real \<times> 'a::euclidean_space \<Rightarrow> real \<times> 'a) \<Rightarrow>
      real \<Rightarrow> 'a \<Rightarrow> real"
  where "product_normal_coeff A t y = fst (A (t,y))"

definition product_tangential_coeff ::
    "(real \<times> 'a::euclidean_space \<Rightarrow> real \<times> 'a) \<Rightarrow>
      'a \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real"
  where "product_tangential_coeff A b t y =
    - (snd (A (t,y)) \<bullet> b)"

definition product_boundary_coeff ::
    "(real \<times> 'a::euclidean_space \<Rightarrow> real \<times> 'a) \<Rightarrow>
      'a \<Rightarrow> real"
  where "product_boundary_coeff A y = - product_normal_coeff A 0 y"

definition product_normal_derivative ::
    "(real \<times> 'a::euclidean_space \<Rightarrow> real \<times> 'a) \<Rightarrow>
      real \<Rightarrow> 'a \<Rightarrow> real"
  where "product_normal_derivative A t y =
    fst (frechet_derivative A (at (t,y)) (1,0))"

definition product_tangential_derivative ::
    "(real \<times> 'a::euclidean_space \<Rightarrow> real \<times> 'a) \<Rightarrow>
      'a \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real"
  where "product_tangential_derivative A b t y =
    - (snd (frechet_derivative A (at (t,y)) (0,b)) \<bullet> b)"

definition product_restrict_near_top ::
    "(real \<times> 'a::euclidean_space) set \<Rightarrow>
      (real \<times> 'a \<Rightarrow> real \<times> 'a) \<Rightarrow>
      real \<times> 'a \<Rightarrow> real \<times> 'a"
  where "product_restrict_near_top U A p =
    (if p \<in> U then A p else 0)"

definition halfspace_form_eq ::
    "(real \<times> 'a::euclidean_space) set \<Rightarrow>
      (real \<times> 'a \<Rightarrow> real \<times> 'a) \<Rightarrow>
      (real \<times> 'a \<Rightarrow> real \<times> 'a) \<Rightarrow> bool"
  where "halfspace_form_eq U A B \<longleftrightarrow>
    (\<forall>p\<in>U. 0 \<le> fst p \<longrightarrow> A p = B p)"

lemma product_boundary_coeff_orientation:
  "product_boundary_coeff A y = - product_normal_coeff A 0 y"
  by (simp add: product_boundary_coeff_def)

lemma product_exterior_top_coordinate:
  "product_exterior_top A (t,y) =
    product_normal_derivative A t y -
      (\<Sum>b\<in>Basis. product_tangential_derivative A b t y)"
  by (simp add: product_exterior_top_def
    product_normal_derivative_def product_tangential_derivative_def
    sum_negf)

lemma product_exterior_top_zero [simp]:
  "product_exterior_top (\<lambda>p. 0) p = 0"
  by (simp add: product_exterior_top_def)

lemma product_exterior_top_add:
  fixes A B :: "real \<times> 'a::euclidean_space \<Rightarrow> real \<times> 'a"
  assumes dA: "A differentiable (at p)"
    and dB: "B differentiable (at p)"
  shows "product_exterior_top (\<lambda>q. A q + B q) p =
    product_exterior_top A p + product_exterior_top B p"
  by (simp add: product_exterior_top_def
    frechet_derivative_add[OF dA dB] sum.distrib
    inner_add_left algebra_simps)

lemma product_exterior_top_scale:
  fixes A :: "real \<times> 'a::euclidean_space \<Rightarrow> real \<times> 'a"
    and rho :: "real \<times> 'a \<Rightarrow> real"
  assumes drho: "rho differentiable (at p)"
    and dA: "A differentiable (at p)"
  shows "product_exterior_top (\<lambda>q. rho q *\<^sub>R A q) p =
    rho p * product_exterior_top A p +
      frechet_derivative rho (at p) (1,0) * fst (A p) +
      (\<Sum>b\<in>Basis.
        frechet_derivative rho (at p) (0,b) *
          (snd (A p) \<bullet> b))"
  by (simp add: product_exterior_top_def
    frechet_derivative_bilinear
      [OF bounded_bilinear_scaleR drho dA]
    sum.distrib sum_distrib_left algebra_simps)

lemma product_exterior_top_sum:
  fixes A :: "'i \<Rightarrow>
      real \<times> 'a::euclidean_space \<Rightarrow> real \<times> 'a"
  assumes finite: "finite I"
    and dA: "\<And>i. i \<in> I \<Longrightarrow> A i differentiable (at p)"
  shows "product_exterior_top (\<lambda>q. \<Sum>i\<in>I. A i q) p =
    (\<Sum>i\<in>I. product_exterior_top (A i) p)"
  using finite dA
proof (induction I rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert i I)
  have di: "A i differentiable (at p)"
    using insert.prems by simp
  have dI: "(\<lambda>q. \<Sum>j\<in>I. A j q) differentiable (at p)"
    by (rule differentiable_sum)
       (use insert.hyps insert.prems in auto)
  have "product_exterior_top
      (\<lambda>q. \<Sum>j\<in>insert i I. A j q) p =
      product_exterior_top
        (\<lambda>q. A i q + (\<Sum>j\<in>I. A j q)) p"
    using insert.hyps by simp
  also have "\<dots> = product_exterior_top (A i) p +
      product_exterior_top (\<lambda>q. \<Sum>j\<in>I. A j q) p"
    by (rule product_exterior_top_add[OF di dI])
  also have "\<dots> =
      (\<Sum>j\<in>insert i I. product_exterior_top (A j) p)"
    using insert by simp
  finally show ?case .
qed

lemma product_scale_support:
  fixes A :: "real \<times> 'a::euclidean_space \<Rightarrow> real \<times> 'a"
    and rho :: "real \<times> 'a \<Rightarrow> real"
  shows "support_on U (\<lambda>p. rho p *\<^sub>R A p) \<subseteq>
    support_on U A"
  by (auto simp: support_on_def)

lemma product_scale_compact_support:
  fixes A :: "real \<times> 'a::euclidean_space \<Rightarrow> real \<times> 'a"
    and rho :: "real \<times> 'a \<Rightarrow> real"
  assumes "compact (closure (support_on U A))"
  shows "compact (closure
    (support_on U (\<lambda>p. rho p *\<^sub>R A p)))"
proof -
  have "bounded (support_on U A)"
    by (rule bounded_subset
      [OF compact_imp_bounded[OF assms] closure_subset])
  then have "bounded (support_on U
      (\<lambda>p. rho p *\<^sub>R A p))"
    by (rule bounded_subset[OF _ product_scale_support])
  then show ?thesis by simp
qed

lemma basis_coordinate_line_has_vector_derivative:
  fixes v :: "'a::euclidean_space \<Rightarrow> real"
  assumes b: "b \<in> Basis"
  shows "((\<lambda>u. \<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j)
      has_vector_derivative b) (at s)"
proof -
  let ?C = "(\<Sum>j\<in>Basis - {b}. v j *\<^sub>R j)"
  have eq: "(\<lambda>u. \<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j) =
      (\<lambda>u. u *\<^sub>R b + ?C)"
  proof (rule ext)
    fix u
    show "(\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j) =
        u *\<^sub>R b + ?C"
      using b by (simp add: sum.remove)
  qed
  have der: "((\<lambda>u::real. u *\<^sub>R b)
      has_derivative (\<lambda>h. h *\<^sub>R b)) (at s)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_scaleR_left])
       simp
  have dC: "((\<lambda>u::real. ?C) has_derivative (\<lambda>h. 0)) (at s)"
    by (rule has_derivative_const)
  have dsum: "((\<lambda>u::real. u *\<^sub>R b + ?C)
      has_derivative (\<lambda>h. h *\<^sub>R b + 0)) (at s)"
    by (rule has_derivative_add[OF der dC])
  show ?thesis
    unfolding eq has_vector_derivative_def
    using dsum by simp
qed

lemma frechet_derivative_along_line:
  fixes F :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and l :: "real \<Rightarrow> 'a"
  assumes dF: "F differentiable (at (l s))"
    and dl: "(l has_vector_derivative v) (at s)"
  shows "((\<lambda>u. F (l u)) has_vector_derivative
      frechet_derivative F (at (l s)) v) (at s)"
proof -
  let ?D = "frechet_derivative F (at (l s))"
  have dl': "(l has_derivative (\<lambda>r. r *\<^sub>R v)) (at s)"
    using dl by (simp add: has_vector_derivative_def)
  have dF': "(F has_derivative ?D) (at (l s))"
    using dF by (simp add: frechet_derivative_works)
  have comp: "((F \<circ> l) has_derivative
      (?D \<circ> (\<lambda>r. r *\<^sub>R v))) (at s)"
    by (rule diff_chain_at[OF dl' dF'])
  have eq: "(?D \<circ> (\<lambda>r. r *\<^sub>R v)) =
      (\<lambda>r. r *\<^sub>R ?D v)"
    by (rule ext)
       (simp add: linear.scaleR[OF linear_frechet_derivative[OF dF]])
  have comp': "((F \<circ> l) has_derivative
      (\<lambda>r. r *\<^sub>R ?D v)) (at s)"
    using comp unfolding eq .
  show ?thesis
    using comp'
    by (simp add: comp_def has_vector_derivative_def)
qed

lemma product_normal_line_derivative:
  fixes F :: "real \<times> 'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes dF: "F differentiable (at (t,y))"
  shows "((\<lambda>s. F (s,y)) has_vector_derivative
      frechet_derivative F (at (t,y)) (1,0)) (at t)"
proof -
  have line: "((\<lambda>s::real. (s,y)) has_vector_derivative
      (1,0)) (at t)"
    by (auto intro!: derivative_intros)
  show ?thesis
    by (rule frechet_derivative_along_line[OF dF line])
qed

lemma product_tangential_line_derivative:
  fixes F :: "real \<times> 'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
    and v :: "'a \<Rightarrow> real"
  assumes dF: "F differentiable
      (at (t, \<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j))"
    and b: "b \<in> Basis"
  shows "((\<lambda>u. F (t, \<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
      has_vector_derivative
        frechet_derivative F
          (at (t, \<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (0,b))
      (at s)"
proof -
  have line: "((\<lambda>u. (t, \<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
      has_vector_derivative (0,b)) (at s)"
    by (intro has_vector_derivative_Pair
        has_vector_derivative_const
        basis_coordinate_line_has_vector_derivative[OF b])
  show ?thesis
    by (rule frechet_derivative_along_line[OF dF line])
qed

lemma bounded_linear_after_vector_derivative:
  fixes F :: "real \<Rightarrow> 'a::real_normed_vector"
    and L :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes dF: "(F has_vector_derivative v) (at s)"
    and L: "bounded_linear L"
  shows "((\<lambda>u. L (F u)) has_vector_derivative L v) (at s)"
proof -
  have dF': "(F has_derivative (\<lambda>r. r *\<^sub>R v)) (at s)"
    using dF by (simp add: has_vector_derivative_def)
  have dL: "(L has_derivative L) (at (F s))"
    by (rule bounded_linear.has_derivative[OF L]) simp
  have comp: "((L \<circ> F) has_derivative
      (L \<circ> (\<lambda>r. r *\<^sub>R v))) (at s)"
    by (rule diff_chain_at[OF dF' dL])
  have eq: "(L \<circ> (\<lambda>r. r *\<^sub>R v)) =
      (\<lambda>r. r *\<^sub>R L v)"
    by (rule ext) (simp add: linear.scaleR[OF bounded_linear.linear[OF L]])
  have comp': "((L \<circ> F) has_derivative
      (\<lambda>r. r *\<^sub>R L v)) (at s)"
    using comp unfolding eq .
  show ?thesis
    using comp' by (simp add: comp_def has_vector_derivative_def)
qed

lemma product_normal_coeff_derivative:
  fixes A :: "real \<times> 'a::euclidean_space \<Rightarrow> real \<times> 'a"
  assumes dA: "A differentiable (at (t,y))"
  shows "((\<lambda>s. product_normal_coeff A s y)
      has_vector_derivative product_normal_derivative A t y) (at t)"
  unfolding product_normal_coeff_def product_normal_derivative_def
  by (rule bounded_linear_after_vector_derivative
      [OF product_normal_line_derivative[OF dA] bounded_linear_fst])

lemma product_tangential_coeff_derivative:
  fixes A :: "real \<times> 'a::euclidean_space \<Rightarrow> real \<times> 'a"
    and v :: "'a \<Rightarrow> real"
  assumes dA: "A differentiable
      (at (t, \<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j))"
    and b: "b \<in> Basis"
  shows "((\<lambda>u. product_tangential_coeff A b t
        (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
      has_vector_derivative
        product_tangential_derivative A b t
          (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j))
      (at s)"
proof -
  have inner: "bounded_linear
      (\<lambda>p::real \<times> 'a. snd p \<bullet> b)"
    by (rule bounded_linear_compose
        [OF bounded_linear_inner_left bounded_linear_snd])
  have L: "bounded_linear
      (\<lambda>p::real \<times> 'a. - (snd p \<bullet> b))"
    by (rule bounded_linear_minus[OF inner])
  show ?thesis
    unfolding product_tangential_coeff_def
      product_tangential_derivative_def
    by (rule bounded_linear_after_vector_derivative
        [OF product_tangential_line_derivative[OF dA b] L])
qed

lemma halfspace_ambient_derivative_unique:
  fixes F G :: "real \<times> 'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes t: "0 \<le> t"
    and dF: "F differentiable (at (t,y))"
    and dG: "G differentiable (at (t,y))"
    and eq: "\<And>p. 0 \<le> fst p \<Longrightarrow> F p = G p"
  shows "frechet_derivative F (at (t,y)) =
    frechet_derivative G (at (t,y))"
proof -
  let ?H = "{p::real \<times> 'a. 0 \<le> fst p}"
  let ?x = "(t,y)"
  have near: "\<And>i e. i \<in> (Basis::(real \<times> 'a) set) \<Longrightarrow>
      e > 0 \<Longrightarrow>
      \<exists>d::real. 0 < \<bar>d\<bar> \<and> \<bar>d\<bar> < e \<and>
        ?x + d *\<^sub>R i \<in> ?H"
  proof -
    fix i :: "real \<times> 'a" and e :: real
    assume i: "i \<in> Basis" and e: "0 < e"
    show "\<exists>d::real. 0 < \<bar>d\<bar> \<and> \<bar>d\<bar> < e \<and>
        ?x + d *\<^sub>R i \<in> ?H"
      by (rule exI[of _ "e/2"])
         (use i e t in \<open>auto simp: Basis_prod_def\<close>)
  qed
  have Fh: "(F has_derivative
      frechet_derivative F (at ?x)) (at ?x within ?H)"
    by (rule has_derivative_at_withinI
        [OF frechet_derivative_works[THEN iffD1, OF dF]])
  have Gh: "(G has_derivative
      frechet_derivative G (at ?x)) (at ?x within ?H)"
    by (rule has_derivative_at_withinI
        [OF frechet_derivative_works[THEN iffD1, OF dG]])
  have Gf: "(G has_derivative
      frechet_derivative F (at ?x)) (at ?x within ?H)"
    by (rule has_derivative_transform_within[OF Fh, of 1])
       (use t eq in auto)
  show ?thesis
    by (rule frechet_derivative_unique_within[OF Gf Gh near])
qed

lemma halfspace_ambient_derivative_unique_local:
  fixes F G :: "real \<times> 'a::euclidean_space \<Rightarrow>
      'b::real_normed_vector"
  assumes openU: "open U" and pU: "(t,y) \<in> U"
    and t: "0 \<le> t"
    and dF: "F differentiable (at (t,y))"
    and dG: "G differentiable (at (t,y))"
    and eq: "\<And>p. p \<in> U \<Longrightarrow>
      0 \<le> fst p \<Longrightarrow> F p = G p"
  shows "frechet_derivative F (at (t,y)) =
    frechet_derivative G (at (t,y))"
proof -
  let ?H = "{p::real \<times> 'a. 0 \<le> fst p}"
  let ?S = "U \<inter> ?H"
  let ?x = "(t,y)"
  obtain r where r: "0 < r" "ball ?x r \<subseteq> U"
    using openE[OF openU pU] by blast
  have near: "\<And>i e. i \<in> (Basis::(real \<times> 'a) set) \<Longrightarrow>
      e > 0 \<Longrightarrow>
      \<exists>d::real. 0 < \<bar>d\<bar> \<and> \<bar>d\<bar> < e \<and>
        ?x + d *\<^sub>R i \<in> ?S"
  proof -
    fix i :: "real \<times> 'a" and e :: real
    assume i: "i \<in> Basis" and e: "0 < e"
    let ?d = "min e r / 2"
    have d: "0 < ?d" "?d < e" "?d < r"
      using e r by auto
    have nonneg: "0 \<le> fst i"
      using i by (auto simp: Basis_prod_def)
    have n: "norm i = 1"
      using i by simp
    have h: "?x + ?d *\<^sub>R i \<in> ?H"
      using t nonneg d
      by (simp add: add_nonneg_nonneg mult_nonneg_nonneg)
    have u: "?x + ?d *\<^sub>R i \<in> U"
      using r d n
      by (auto simp: dist_norm intro: subsetD[OF r(2)])
    show "\<exists>d::real. 0 < \<bar>d\<bar> \<and> \<bar>d\<bar> < e \<and>
        ?x + d *\<^sub>R i \<in> ?S"
      by (rule exI[of _ ?d])
         (use d h u in auto)
  qed
  have Fh: "(F has_derivative
      frechet_derivative F (at ?x)) (at ?x within ?S)"
    by (rule has_derivative_at_withinI
        [OF frechet_derivative_works[THEN iffD1, OF dF]])
  have Gh: "(G has_derivative
      frechet_derivative G (at ?x)) (at ?x within ?S)"
    by (rule has_derivative_at_withinI
        [OF frechet_derivative_works[THEN iffD1, OF dG]])
  have Gf: "(G has_derivative
      frechet_derivative F (at ?x)) (at ?x within ?S)"
    by (rule has_derivative_transform_within[OF Fh, of 1])
       (use pU t eq in auto)
  show ?thesis
    by (rule frechet_derivative_unique_within[OF Gf Gh near])
qed

lemma product_exterior_top_halfspace_extension:
  fixes F G :: "real \<times> 'a::euclidean_space \<Rightarrow> real \<times> 'a"
  assumes "0 \<le> t" "F differentiable (at (t,y))"
    "G differentiable (at (t,y))"
    "\<And>p. 0 \<le> fst p \<Longrightarrow> F p = G p"
  shows "product_exterior_top F (t,y) =
    product_exterior_top G (t,y)"
  using halfspace_ambient_derivative_unique[OF assms]
  by (simp add: product_exterior_top_def)

lemma product_exterior_top_halfspace_local_extension:
  fixes F G :: "real \<times> 'a::euclidean_space \<Rightarrow>
      real \<times> 'a"
  assumes "open U" "(t,y) \<in> U" "0 \<le> t"
    "F differentiable (at (t,y))"
    "G differentiable (at (t,y))"
    "\<And>p. p \<in> U \<Longrightarrow>
      0 \<le> fst p \<Longrightarrow> F p = G p"
  shows "product_exterior_top F (t,y) =
    product_exterior_top G (t,y)"
  using halfspace_ambient_derivative_unique_local[OF assms]
  by (simp add: product_exterior_top_def)

lemma halfspace_form_eq_refl [simp]:
  "halfspace_form_eq U A A"
  by (simp add: halfspace_form_eq_def)

lemma halfspace_form_eq_sym:
  "halfspace_form_eq U A B \<Longrightarrow> halfspace_form_eq U B A"
  by (auto simp: halfspace_form_eq_def)

lemma halfspace_form_eq_trans:
  "halfspace_form_eq U A B \<Longrightarrow>
    halfspace_form_eq U B C \<Longrightarrow>
    halfspace_form_eq U A C"
  by (auto simp: halfspace_form_eq_def)

lemma halfspace_form_eq_add:
  assumes "halfspace_form_eq U A B"
    and "halfspace_form_eq U C D"
  shows "halfspace_form_eq U
    (\<lambda>p. A p + C p) (\<lambda>p. B p + D p)"
  using assms by (auto simp: halfspace_form_eq_def)

lemma halfspace_form_eq_scale:
  assumes "halfspace_form_eq U A B"
  shows "halfspace_form_eq U
    (\<lambda>p. rho p *\<^sub>R A p)
    (\<lambda>p. rho p *\<^sub>R B p)"
  using assms by (auto simp: halfspace_form_eq_def)

lemma halfspace_form_eq_restrict:
  assumes "halfspace_form_eq U A B"
  shows "halfspace_form_eq U
    (product_restrict_near_top W A)
    (product_restrict_near_top W B)"
  using assms
  by (auto simp: halfspace_form_eq_def
    product_restrict_near_top_def)

lemma halfspace_form_eq_exterior:
  fixes A B :: "real \<times> 'a::euclidean_space \<Rightarrow>
    real \<times> 'a"
  assumes openU: "open U" and pU: "(t,y) \<in> U"
    and t: "0 \<le> t"
    and dA: "A differentiable (at (t,y))"
    and dB: "B differentiable (at (t,y))"
    and eq: "halfspace_form_eq U A B"
  shows "product_exterior_top A (t,y) =
    product_exterior_top B (t,y)"
  by (rule product_exterior_top_halfspace_local_extension
      [OF openU pU t dA dB])
     (use eq in \<open>auto simp: halfspace_form_eq_def\<close>)

lemma product_restrict_near_top_in [simp]:
  "p \<in> U \<Longrightarrow> product_restrict_near_top U A p = A p"
  by (simp add: product_restrict_near_top_def)

lemma product_exterior_top_restrict:
  assumes "open U" "p \<in> U"
  shows "product_exterior_top (product_restrict_near_top U A) p =
    product_exterior_top A p"
proof -
  have D: "frechet_derivative (product_restrict_near_top U A) (at p) =
      frechet_derivative A (at p)"
    by (rule frechet_derivative_transform_within_open[OF assms])
       simp
  show ?thesis
    by (simp add: product_exterior_top_def D)
qed

theorem Stokes_product_form_chart_C1:
  fixes A :: "real \<times> 'a::euclidean_space \<Rightarrow> real \<times> 'a"
    and K_P :: "(real \<times> 'a) set"
    and K_Q :: "'a \<Rightarrow> (real \<times> 'a) set"
    and U :: "(real \<times> 'a) set"
  defines "V \<equiv> ({0..} \<times> UNIV) \<inter> U"
  assumes open_U: "open U"
    and dA: "\<And>p. p \<in> V \<Longrightarrow> A differentiable (at p)"
    and compact_P: "compact K_P"
    and K_P_chart: "K_P \<subseteq> V"
    and zero_P: "\<And>p. p \<in> V \<Longrightarrow>
      p \<notin> K_P \<Longrightarrow> fst (A p) = 0"
    and cont_P: "continuous_on V
      (case_prod (product_normal_derivative A))"
    and compact_Q: "\<And>b. b \<in> Basis \<Longrightarrow> compact (K_Q b)"
    and K_Q_chart: "\<And>b. b \<in> Basis \<Longrightarrow> K_Q b \<subseteq> V"
    and zero_Q: "\<And>b p. b \<in> Basis \<Longrightarrow> p \<in> V \<Longrightarrow>
      p \<notin> K_Q b \<Longrightarrow> snd (A p) \<bullet> b = 0"
    and cont_Q: "\<And>b. b \<in> Basis \<Longrightarrow>
      continuous_on V
        (case_prod (product_tangential_derivative A b))"
  shows "(LINT p : V | lborel. product_exterior_top A p) =
    (LINT y : {y. (0,y) \<in> U} | lborel.
      product_boundary_coeff A y)"
proof -
  have normal: "\<And>t y. 0 \<le> t \<Longrightarrow> (t,y) \<in> U \<Longrightarrow>
      ((\<lambda>s. product_normal_coeff A s y)
        has_vector_derivative product_normal_derivative A t y)
        (at t within {0..})"
  proof -
    fix t y
    assume t: "0 \<le> t" and pU: "(t,y) \<in> U"
    have "(t,y) \<in> V"
      using t pU by (simp add: V_def)
    then have d: "A differentiable (at (t,y))"
      by (rule dA)
    show "((\<lambda>s. product_normal_coeff A s y)
        has_vector_derivative product_normal_derivative A t y)
        (at t within {0..})"
      by (rule has_vector_derivative_at_within
          [OF product_normal_coeff_derivative[OF d]])
  qed
  have tangential: "\<And>b t v s. b \<in> Basis \<Longrightarrow>
      0 \<le> t \<Longrightarrow>
      (t, \<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j) \<in> U \<Longrightarrow>
      ((\<lambda>u. product_tangential_coeff A b t
          (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          product_tangential_derivative A b t
            (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j))
        (at s)"
  proof -
    fix b t v s
    assume b: "b \<in> Basis" and t: "0 \<le> t"
      and pU: "(t, \<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j) \<in> U"
    have "(t, \<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j) \<in> V"
      using t pU by (simp add: V_def)
    then have d: "A differentiable
        (at (t, \<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j))"
      by (rule dA)
    show "((\<lambda>u. product_tangential_coeff A b t
          (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          product_tangential_derivative A b t
            (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j))
        (at s)"
      by (rule product_tangential_coeff_derivative[OF d b])
  qed
  show ?thesis
    unfolding V_def
    by (rule Stokes_chart_form_interface
        [where B=Basis
          and P="product_normal_coeff A"
          and P_t="product_normal_derivative A"
          and Q="product_tangential_coeff A"
          and Q_b="product_tangential_derivative A"
          and d_coeff="product_exterior_top A"
          and boundary_coeff="product_boundary_coeff A"
          and K_P=K_P and K_Q=K_Q,
          OF subset_refl open_U compact_P])
       (use K_P_chart zero_P normal cont_P compact_Q
          K_Q_chart zero_Q tangential cont_Q
        in \<open>auto simp: V_def product_normal_coeff_def
          product_tangential_coeff_def
          product_exterior_top_coordinate
          product_boundary_coeff_orientation
          split: prod.splits\<close>)
qed

end
