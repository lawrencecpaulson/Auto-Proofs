theory Stokes_Basis_Fubini
  imports Stokes_Local
begin

text \<open>
  Isolate any chosen Euclidean basis coordinate in a Lebesgue integral.
  The outer integral is over the remaining coordinates of the finite
  product measure.
\<close>

lemma lborel_integral_basis_slice:
  fixes h :: "'a::euclidean_space \<Rightarrow> real"
    and b :: 'a
  assumes b: "b \<in> Basis"
    and h_int: "integrable lborel h"
    and h_borel: "h \<in> borel_measurable borel"
  shows "(\<integral>x. h x \<partial>lborel) =
    (\<integral>v. \<integral>t.
      h (\<Sum>j\<in>Basis. (v(b:=t)) j *\<^sub>R j) \<partial>lborel
      \<partial>Pi\<^sub>M (Basis - {b}) (\<lambda>_. lborel))"
proof -
  let ?B = "Basis :: 'a set"
  let ?M = "Pi\<^sub>M ?B (\<lambda>_. lborel)"
  let ?T = "\<lambda>v. \<Sum>j\<in>?B. v j *\<^sub>R j"
  interpret P: product_sigma_finite "\<lambda>_::'a. lborel"
    by standard
  have T_meas: "?T \<in> measurable ?M borel"
    by measurable
  have distr_eq: "(lborel :: 'a measure) = distr ?M borel ?T"
    by (rule lborel_eq)
  have intT: "integrable ?M (\<lambda>v. h (?T v))"
    by (rule integrable_distr[OF T_meas]) (use h_int distr_eq in simp)
  have insert_B: "insert b (?B - {b}) = ?B"
    using b by auto
  have int_insert: "integrable (Pi\<^sub>M (insert b (?B - {b})) (\<lambda>_. lborel))
      (\<lambda>v. h (?T v))"
    by (subst insert_B, rule intT)
  have finite_rest: "finite (?B - {b})"
    by simp
  have b_not_rest: "b \<notin> ?B - {b}"
    by simp
  have "(\<integral>x. h x \<partial>lborel) = (\<integral>v. h (?T v) \<partial>?M)"
    using integral_distr[OF T_meas h_borel] distr_eq by simp
  also have "\<dots> =
    (\<integral>v. \<integral>t. h (?T (v(b:=t))) \<partial>lborel
      \<partial>Pi\<^sub>M (?B - {b}) (\<lambda>_. lborel))"
    using P.product_integral_insert[OF finite_rest b_not_rest int_insert]
      insert_B by simp
  finally show ?thesis .
qed

text \<open>
  A directional derivative integrates to zero when its primitive
  vanishes at both ends of every line parallel to a basis vector.
  The assumptions give an explicit common strip containing the
  derivative, so the inner integral can be evaluated by FTC.
\<close>

lemma lborel_integral_basis_derivative_zero:
  fixes F g :: "'a::euclidean_space \<Rightarrow> real"
    and b :: 'a
  assumes b: "b \<in> Basis"
    and R: "0 \<le> R"
    and g_int: "integrable lborel g"
    and g_borel: "g \<in> borel_measurable borel"
    and deriv: "\<And>v t. t \<in> {-R..R} \<Longrightarrow>
      ((\<lambda>s. F (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j))
        has_vector_derivative
          g (\<Sum>j\<in>Basis. (v(b:=t)) j *\<^sub>R j))
        (at t within {-R..R})"
    and cont: "\<And>v. continuous_on {-R..R}
      (\<lambda>t. g (\<Sum>j\<in>Basis. (v(b:=t)) j *\<^sub>R j))"
    and faces: "\<And>v. F (\<Sum>j\<in>Basis. (v(b:= -R)) j *\<^sub>R j) = 0 \<and>
      F (\<Sum>j\<in>Basis. (v(b:=R)) j *\<^sub>R j) = 0"
    and outside: "\<And>v t. t \<notin> {-R..R} \<Longrightarrow>
      g (\<Sum>j\<in>Basis. (v(b:=t)) j *\<^sub>R j) = 0"
  shows "(\<integral>x. g x \<partial>lborel) = 0"
proof -
  let ?T = "\<lambda>v. \<Sum>j\<in>Basis. v j *\<^sub>R j"
  have inner: "\<And>v. (\<integral>t. g (?T (v(b:=t))) \<partial>lborel) = 0"
  proof -
    fix v
    have "(\<integral>t. g (?T (v(b:=t))) \<partial>lborel) =
      (LINT t : {-R..R} | lborel. g (?T (v(b:=t))))"
      unfolding set_lebesgue_integral_def
    proof (rule Bochner_Integration.integral_cong[OF refl])
      fix t :: real
      show "g (?T (v(b:=t))) =
          indicator {-R..R} t *\<^sub>R g (?T (v(b:=t)))"
      proof (cases "t \<in> {-R..R}")
        case True
        then show ?thesis by simp
      next
        case False
        then have "g (?T (v(b:=t))) = 0"
          by (rule outside)
        then show ?thesis using False by simp
      qed
    qed
    also have "\<dots> =
      F (?T (v(b:=R))) - F (?T (v(b:= -R)))"
      unfolding set_lebesgue_integral_def
      by (rule integral_FTC_atLeastAtMost)
         (use R deriv cont in auto)
    also have "\<dots> = 0"
      using faces[of v] by simp
    finally show "(\<integral>t. g (?T (v(b:=t))) \<partial>lborel) = 0" .
  qed
  have "(\<integral>x. g x \<partial>lborel) =
      (\<integral>v. \<integral>t. g (?T (v(b:=t))) \<partial>lborel
        \<partial>Pi\<^sub>M (Basis - {b}) (\<lambda>_. lborel))"
    by (rule lborel_integral_basis_slice[OF b g_int g_borel])
  also have "\<dots> = 0"
  proof -
    have "(\<lambda>v. \<integral>t. g (?T (v(b:=t))) \<partial>lborel) = (\<lambda>v. 0)"
      by (rule ext, rule inner)
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma basis_slice_coordinate:
  fixes b :: "'a::euclidean_space"
  assumes b: "b \<in> Basis"
  shows "(\<Sum>j\<in>Basis. (v(b:=t)) j *\<^sub>R j) \<bullet> b = t"
  using b by (simp add: sum_if_inner)

lemma basis_slice_continuous:
  fixes b :: "'a::euclidean_space"
  assumes b: "b \<in> Basis"
  shows "continuous_on UNIV
    (\<lambda>s. \<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)"
proof -
  have eq: "\<And>s. (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j) =
      (\<Sum>j\<in>Basis - {b}. v j *\<^sub>R j) + s *\<^sub>R b"
    using b by (simp add: sum.remove[OF finite_Basis b] ac_simps)
  have fun_eq:
    "(\<lambda>s. \<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j) =
      (\<lambda>s. (\<Sum>j\<in>Basis - {b}. v j *\<^sub>R j) + s *\<^sub>R b)"
    by (rule ext, rule eq)
  have affine:
    "continuous_on UNIV
      (\<lambda>s. (\<Sum>j\<in>Basis - {b}. v j *\<^sub>R j) + s *\<^sub>R b)"
    by (rule continuous_on_add[OF continuous_on_const])
       (rule continuous_on_scaleR[OF continuous_on_id continuous_on_const])
  show ?thesis by (subst fun_eq, rule affine)
qed

theorem lborel_integral_basis_derivative_zero_compact:
  fixes F g :: "'a::euclidean_space \<Rightarrow> real"
    and b :: 'a
  assumes b: "b \<in> Basis"
    and support: "compact (closure {x. F x \<noteq> 0})"
    and g_int: "integrable lborel g"
    and g_borel: "g \<in> borel_measurable borel"
    and deriv: "\<And>v t.
      ((\<lambda>s. F (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j))
        has_vector_derivative
          g (\<Sum>j\<in>Basis. (v(b:=t)) j *\<^sub>R j)) (at t)"
    and cont: "\<And>v. continuous_on UNIV
      (\<lambda>t. g (\<Sum>j\<in>Basis. (v(b:=t)) j *\<^sub>R j))"
  shows "(\<integral>x. g x \<partial>lborel) = 0"
proof -
  let ?S = "{x::'a. F x \<noteq> 0}"
  let ?T = "\<lambda>v. \<Sum>j\<in>Basis. v j *\<^sub>R j"
  have bounded: "bounded (closure ?S)"
    by (rule compact_imp_bounded[OF support])
  obtain R where R: "0 < R" and bound: "closure ?S \<subseteq> ball 0 R"
    using bounded_subset_ballD[OF bounded, of 0] by auto
  have zero_norm: "\<And>x. R \<le> norm x \<Longrightarrow> F x = 0"
  proof -
    fix x :: 'a assume large: "R \<le> norm x"
    show "F x = 0"
    proof (rule ccontr)
      assume "F x \<noteq> 0"
      then have "x \<in> closure ?S"
        using closure_subset[of ?S] by auto
      then have "x \<in> ball 0 R" using bound by auto
      with large show False by simp
    qed
  qed
  have zero_line: "\<And>v t. R \<le> \<bar>t\<bar> \<Longrightarrow> F (?T (v(b:=t))) = 0"
  proof -
    fix v t assume large: "R \<le> \<bar>t\<bar>"
    have coord: "?T (v(b:=t)) \<bullet> b = t"
      by (rule basis_slice_coordinate[OF b])
    have "\<bar>t\<bar> \<le> norm (?T (v(b:=t)))"
      using Basis_le_norm[OF b, of "?T (v(b:=t))"] coord by simp
    then have "R \<le> norm (?T (v(b:=t)))"
      using large by linarith
    then show "F (?T (v(b:=t))) = 0"
      by (rule zero_norm)
  qed
  have faces: "\<And>v. F (?T (v(b:= -R))) = 0 \<and> F (?T (v(b:=R))) = 0"
    using zero_line R by auto
  have outside: "\<And>v t. t \<notin> {-R..R} \<Longrightarrow> g (?T (v(b:=t))) = 0"
  proof -
    fix v t assume out: "t \<notin> {-R..R}"
    have D: "((\<lambda>s. F (?T (v(b:=s)))) has_vector_derivative
        g (?T (v(b:=t)))) (at t)"
      by (rule deriv)
    have zero: "\<And>s. s \<notin> {-R..R} \<Longrightarrow> F (?T (v(b:=s))) = 0"
      using zero_line by auto
    show "g (?T (v(b:=t))) = 0"
      by (rule vector_derivative_zero_off_closed_interval[OF D out zero])
  qed
  have deriv_box: "\<And>v t. t \<in> {-R..R} \<Longrightarrow>
      ((\<lambda>s. F (?T (v(b:=s)))) has_vector_derivative
        g (?T (v(b:=t)))) (at t within {-R..R})"
    using deriv by (auto intro: has_vector_derivative_at_within)
  have cont_box: "\<And>v. continuous_on {-R..R}
      (\<lambda>t. g (?T (v(b:=t))))"
    by (rule continuous_on_subset[OF cont]) auto
  show ?thesis
    by (rule lborel_integral_basis_derivative_zero
        [OF b less_imp_le[OF R] g_int g_borel
            deriv_box cont_box faces outside])
qed

lemma lborel_halfspace_integral_fst:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes int: "set_integrable lborel ({0..} \<times> UNIV) (case_prod g)"
  shows "(LINT p : {0..} \<times> UNIV | lborel. case_prod g p) =
    (LINT t : {0..} | lborel. \<integral>y. g t y \<partial>lborel)"
proof -
  let ?h = "\<lambda>(t,y). indicator ({0..} \<times> UNIV) (t,y) *\<^sub>R g t y"
  have intp: "integrable (lborel \<Otimes>\<^sub>M lborel) ?h"
    using int unfolding set_integrable_def
    by (simp add: lborel_prod split_def)
  have inner: "\<And>t. (\<integral>y. ?h (t,y) \<partial>lborel) =
      indicator {0..} t *\<^sub>R (\<integral>y. g t y \<partial>lborel)"
  proof -
    fix t
    show "(\<integral>y. ?h (t,y) \<partial>lborel) =
      indicator {0..} t *\<^sub>R (\<integral>y. g t y \<partial>lborel)"
      by (cases "t \<in> {0..}") (simp_all add: indicator_def)
  qed
  have "(LINT p : {0..} \<times> UNIV | lborel. case_prod g p) =
      (\<integral>t. \<integral>y. ?h (t,y) \<partial>lborel \<partial>lborel)"
    using lborel_pair.integral_fst[OF intp]
    by (simp add: set_lebesgue_integral_def lborel_prod split_def)
  also have "\<dots> = (LINT t : {0..} | lborel. \<integral>y. g t y \<partial>lborel)"
    unfolding set_lebesgue_integral_def
    by (rule Bochner_Integration.integral_cong) (use inner in auto)
  finally show ?thesis .
qed

lemma compact_halfspace_support_slice:
  fixes F :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes support: "compact (closure
    {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod F p \<noteq> 0})"
    and t: "0 \<le> t"
  shows "compact (closure {y. F t y \<noteq> 0})"
proof -
  have ex: "\<exists>R. \<forall>u y. 0 \<le> u \<longrightarrow>
      y \<notin> ball 0 R \<longrightarrow> F u y = 0"
  proof (rule compact_halfspace_support_bound[OF support])
    fix R assume "0 < R"
      and "\<And>u y. R \<le> u \<Longrightarrow> F u y = 0"
      and side: "\<And>u y. 0 \<le> u \<Longrightarrow>
        y \<notin> ball 0 R \<Longrightarrow> F u y = 0"
    show ?thesis by (rule exI[where x=R]) (use side in auto)
  qed
  then obtain R where side: "\<And>u y. 0 \<le> u \<Longrightarrow>
      y \<notin> ball 0 R \<Longrightarrow> F u y = 0"
    by auto
  have sub: "{y. F t y \<noteq> 0} \<subseteq> ball 0 R"
  proof
    fix y assume "y \<in> {y. F t y \<noteq> 0}"
    then have "F t y \<noteq> 0" by simp
    then show "y \<in> ball 0 R"
      using side[OF t, of y] by blast
  qed
  have "bounded {y. F t y \<noteq> 0}"
    by (rule bounded_subset[OF bounded_ball sub])
  then have "bounded (closure {y. F t y \<noteq> 0})"
    by (rule bounded_closure)
  then show ?thesis
    by (simp add: compact_eq_bounded_closed)
qed

theorem tangential_halfspace_integral_zero_basis:
  fixes F g :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
    and b :: 'a
  assumes b: "b \<in> Basis"
    and int: "set_integrable lborel ({0..} \<times> UNIV) (case_prod g)"
    and support: "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod F p \<noteq> 0})"
    and slice_int: "\<And>t. 0 \<le> t \<Longrightarrow> integrable lborel (g t)"
    and slice_borel: "\<And>t. 0 \<le> t \<Longrightarrow>
      g t \<in> borel_measurable borel"
    and deriv: "\<And>t v s. 0 \<le> t \<Longrightarrow>
      ((\<lambda>u. F t (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          g t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (at s)"
    and cont: "\<And>t v. 0 \<le> t \<Longrightarrow> continuous_on UNIV
      (\<lambda>s. g t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j))"
  shows "(LINT p : {0..} \<times> UNIV | lborel. case_prod g p) = 0"
proof -
  have slice_zero: "\<And>t. 0 \<le> t \<Longrightarrow> (\<integral>y. g t y \<partial>lborel) = 0"
  proof -
    fix t :: real assume t: "0 \<le> t"
    show "(\<integral>y. g t y \<partial>lborel) = 0"
      by (rule lborel_integral_basis_derivative_zero_compact
          [OF b compact_halfspace_support_slice[OF support t]
              slice_int[OF t] slice_borel[OF t]])
         (use deriv[OF t] cont[OF t] in auto)
  qed
  have "(LINT p : {0..} \<times> UNIV | lborel. case_prod g p) =
      (LINT t : {0..} | lborel. \<integral>y. g t y \<partial>lborel)"
    by (rule lborel_halfspace_integral_fst[OF int])
  also have "\<dots> = 0"
  proof -
    have "(\<lambda>t. indicator {0..} t *\<^sub>R
        (\<integral>y. g t y \<partial>lborel)) = (\<lambda>t. 0)"
      by (rule ext) (use slice_zero in \<open>auto simp: indicator_def\<close>)
    then show ?thesis by (simp add: set_lebesgue_integral_def)
  qed
  finally show ?thesis .
qed

lemma integrable_lborel_continuous_compact_support:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes support: "compact (closure {x. f x \<noteq> 0})"
    and cont: "continuous_on UNIV f"
  shows "integrable lborel f"
proof -
  let ?S = "{x. f x \<noteq> 0}"
  let ?D = "closure ?S"
  have contD: "continuous_on ?D f"
    by (rule continuous_on_subset[OF cont]) auto
  have zero: "\<And>x. x \<notin> ?D \<Longrightarrow> f x = 0"
  proof -
    fix x :: 'a assume out: "x \<notin> ?D"
    show "f x = 0"
    proof (rule ccontr)
      assume "f x \<noteq> 0"
      then have "x \<in> ?S" by simp
      then have "x \<in> ?D"
        using closure_subset[of ?S] by blast
      with out show False by simp
    qed
  qed
  have "set_integrable lborel UNIV f"
  proof (rule set_integrable_continuous_compact_support
      [OF support _ contD])
    show "?D \<subseteq> UNIV" by simp
    fix x :: 'a
    assume "x \<in> UNIV" and out: "x \<notin> ?D"
    show "f x = 0" by (rule zero[OF out])
  qed
  then show ?thesis by (simp add: set_integrable_def)
qed

theorem tangential_halfspace_integral_zero_basis_with_derivative_support:
  fixes F g :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
    and b :: 'a
  assumes b: "b \<in> Basis"
    and support_F: "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod F p \<noteq> 0})"
    and support_g: "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod g p \<noteq> 0})"
    and deriv: "\<And>t v s. 0 \<le> t \<Longrightarrow>
      ((\<lambda>u. F t (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          g t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (at s)"
    and cont: "continuous_on ({0..} \<times> UNIV) (case_prod g)"
  shows "(LINT p : {0..} \<times> UNIV | lborel. case_prod g p) = 0"
proof -
  let ?H = "{0..} \<times> UNIV :: (real \<times> 'a) set"
  let ?S = "{p::real \<times> 'a. 0 \<le> fst p \<and> case_prod g p \<noteq> 0}"
  let ?D = "closure ?S"
  have closedH: "closed ?H"
    by (intro closed_Times) auto
  have DH: "?D \<subseteq> ?H"
    by (rule closure_minimal) (use closedH in auto)
  have contD: "continuous_on ?D (case_prod g)"
    by (rule continuous_on_subset[OF cont DH])
  have zeroD: "\<And>p. p \<in> ?H \<Longrightarrow> p \<notin> ?D \<Longrightarrow>
      case_prod g p = 0"
  proof -
    fix p :: "real \<times> 'a"
    assume H: "p \<in> ?H" and out: "p \<notin> ?D"
    show "case_prod g p = 0"
    proof (rule ccontr)
      assume nz: "case_prod g p \<noteq> 0"
      have "p \<in> ?S" using H nz by (cases p) auto
      then have "p \<in> ?D"
        using closure_subset[of ?S] by blast
      with out show False by simp
    qed
  qed
  have int: "set_integrable lborel ?H (case_prod g)"
    by (rule set_integrable_continuous_compact_support
        [OF support_g DH contD zeroD])
  have slice_cont: "\<And>t. 0 \<le> t \<Longrightarrow> continuous_on UNIV (g t)"
  proof -
    fix t :: real assume t: "0 \<le> t"
    have pair_cont: "continuous_on UNIV (\<lambda>y::'a. (t,y))"
      by (intro continuous_intros)
    have image: "(\<lambda>y::'a. (t,y)) ` UNIV \<subseteq> ?H"
      using t by auto
    have "continuous_on UNIV (\<lambda>y. case_prod g (t,y))"
      by (rule continuous_on_compose2[OF cont pair_cont image])
    then show "continuous_on UNIV (g t)" by simp
  qed
  have slice_int: "\<And>t. 0 \<le> t \<Longrightarrow> integrable lborel (g t)"
  proof -
    fix t :: real assume t: "0 \<le> t"
    have sup: "compact (closure {y. g t y \<noteq> 0})"
      by (rule compact_halfspace_support_slice[OF support_g t])
    show "integrable lborel (g t)"
      by (rule integrable_lborel_continuous_compact_support
          [OF sup slice_cont[OF t]])
  qed
  have slice_borel: "\<And>t. 0 \<le> t \<Longrightarrow> g t \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI) (rule slice_cont)
  have line_cont: "\<And>t v. 0 \<le> t \<Longrightarrow> continuous_on UNIV
      (\<lambda>s. g t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j))"
  proof -
    fix t :: real and v :: "'a \<Rightarrow> real"
    assume t: "0 \<le> t"
    show "continuous_on UNIV
        (\<lambda>s. g t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j))"
      by (rule continuous_on_compose2
          [OF slice_cont[OF t] basis_slice_continuous[OF b]]) auto
  qed
  show ?thesis
    by (rule tangential_halfspace_integral_zero_basis
        [OF b int support_F slice_int slice_borel deriv line_cont])
qed

lemma vector_derivative_zero_on_open:
  fixes F :: "real \<Rightarrow> real"
  assumes deriv: "(F has_vector_derivative f) (at t)"
    and op: "open U"
    and t: "t \<in> U"
    and zero: "\<And>s. s \<in> U \<Longrightarrow> F s = 0"
  shows "f = 0"
proof -
  have const: "((\<lambda>s::real. 0::real) has_vector_derivative 0) (at t)"
    by (rule has_vector_derivative_const)
  have zero_deriv: "(F has_vector_derivative 0) (at t)"
    by (rule has_vector_derivative_transform_within_open
        [OF const op t]) (use zero in auto)
  show ?thesis
    by (rule vector_derivative_unique_at[OF deriv zero_deriv])
qed

lemma tangential_halfspace_derivative_support_basis:
  fixes F g :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
    and b :: 'a
  assumes b: "b \<in> Basis"
    and support_F: "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod F p \<noteq> 0})"
    and deriv: "\<And>t v s. 0 \<le> t \<Longrightarrow>
      ((\<lambda>u. F t (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          g t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (at s)"
  shows "compact (closure
    {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod g p \<noteq> 0})"
proof -
  have ex: "\<exists>R. 0 < R \<and>
    (\<forall>t y. R \<le> t \<longrightarrow> F t y = 0) \<and>
    (\<forall>t y. 0 \<le> t \<longrightarrow>
      y \<notin> ball 0 R \<longrightarrow> F t y = 0)"
  proof (rule compact_halfspace_support_bound[OF support_F])
    fix R assume R: "0 < R"
      and upper: "\<And>t y. R \<le> t \<Longrightarrow> F t y = 0"
      and side: "\<And>t y. 0 \<le> t \<Longrightarrow>
        y \<notin> ball 0 R \<Longrightarrow> F t y = 0"
    show ?thesis
      by (rule exI[where x=R]) (use R upper side in auto)
  qed
  then obtain R where R: "0 < R"
    and upper: "\<And>t y. R \<le> t \<Longrightarrow> F t y = 0"
    and side: "\<And>t y. 0 \<le> t \<Longrightarrow>
      y \<notin> ball 0 R \<Longrightarrow> F t y = 0"
    by auto
  let ?T = "\<lambda>v. \<Sum>j\<in>Basis. v j *\<^sub>R j"
  have g_tail: "\<And>t y. R < t \<Longrightarrow> g t y = 0"
  proof -
    fix t :: real and y :: 'a
    assume rt: "R < t"
    let ?v = "\<lambda>j. y \<bullet> j"
    let ?s = "y \<bullet> b"
    have point: "?T (?v(b:=?s)) = y"
      by (simp add: euclidean_representation)
    have D: "((\<lambda>u. F t (?T (?v(b:=u)))) has_vector_derivative
      g t y) (at ?s)"
      using deriv[of t ?v ?s] R rt
      by (simp add: euclidean_representation)
    have zero: "\<And>u. F t (?T (?v(b:=u))) = 0"
      using upper R rt by auto
    show "g t y = 0"
      by (rule vector_derivative_zero_if_function_zero[OF D zero])
  qed
  have g_side: "\<And>t y. 0 \<le> t \<Longrightarrow>
      y \<notin> cball 0 R \<Longrightarrow> g t y = 0"
  proof -
    fix t :: real and y :: 'a
    assume t: "0 \<le> t" and out: "y \<notin> cball 0 R"
    let ?v = "\<lambda>j. y \<bullet> j"
    let ?s = "y \<bullet> b"
    let ?line = "\<lambda>u. ?T (?v(b:=u))"
    let ?U = "?line -` (- cball 0 R)"
    have update: "(?v(b:=?s)) = ?v" by auto
    have point: "?line ?s = y"
      by (simp add: update euclidean_representation)
    have rep: "(\<Sum>j\<in>Basis.
        (if j = b then y \<bullet> b else y \<bullet> j) *\<^sub>R j) = y"
    proof -
      have "(\<Sum>j\<in>Basis.
        (if j = b then y \<bullet> b else y \<bullet> j) *\<^sub>R j) =
          (\<Sum>j\<in>Basis. (y \<bullet> j) *\<^sub>R j)"
        by (rule sum.cong) auto
      then show ?thesis by (simp add: euclidean_representation)
    qed
    have op: "open ?U"
      using continuous_open_preimage
        [OF basis_slice_continuous[OF b] open_UNIV
          open_Compl[OF closed_cball]]
      by simp
    have sin: "?s \<in> ?U"
      using out rep by simp
    have zero: "\<And>u. u \<in> ?U \<Longrightarrow> F t (?line u) = 0"
    proof -
      fix u assume "u \<in> ?U"
      then have "?line u \<notin> ball 0 R" by auto
      then show "F t (?line u) = 0"
        by (rule side[OF t])
    qed
    have D: "((\<lambda>u. F t (?line u)) has_vector_derivative
      g t y) (at ?s)"
      using deriv[OF t, of ?v ?s]
      by (simp add: euclidean_representation)
    show "g t y = 0"
      by (rule vector_derivative_zero_on_open[OF D op sin zero])
  qed
  let ?D = "{0..R} \<times> cball 0 R :: (real \<times> 'a) set"
  let ?S = "{p::real \<times> 'a. 0 \<le> fst p \<and> case_prod g p \<noteq> 0}"
  have compactD: "compact ?D"
    by (intro compact_Times compact_Icc compact_cball)
  have sub: "?S \<subseteq> ?D"
  proof
    fix p :: "real \<times> 'a"
    assume S: "p \<in> ?S"
    obtain t y where p: "p = (t,y)" by (cases p) auto
    have t: "0 \<le> t" and nz: "g t y \<noteq> 0"
      using S p by auto
    have tr: "t \<le> R" using g_tail[of t y] nz by force
    have yr: "y \<in> cball 0 R"
      using g_side[OF t, of y] nz by blast
    show "p \<in> ?D" using p t tr yr by auto
  qed
  have "bounded ?S"
    by (rule bounded_subset[OF compact_imp_bounded[OF compactD] sub])
  then show ?thesis by simp
qed

theorem tangential_halfspace_integral_zero_basis_C1:
  fixes F g :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
    and b :: 'a
  assumes b: "b \<in> Basis"
    and support_F: "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod F p \<noteq> 0})"
    and deriv: "\<And>t v s. 0 \<le> t \<Longrightarrow>
      ((\<lambda>u. F t (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          g t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (at s)"
    and cont: "continuous_on ({0..} \<times> UNIV) (case_prod g)"
  shows "(LINT p : {0..} \<times> UNIV | lborel. case_prod g p) = 0"
proof -
  have support_g: "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod g p \<noteq> 0})"
    by (rule tangential_halfspace_derivative_support_basis
        [OF b support_F deriv])
  show ?thesis
    by (rule tangential_halfspace_integral_zero_basis_with_derivative_support
        [OF b support_F support_g deriv cont])
qed

lemma set_integrable_halfspace_continuous_compact_support:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes support: "compact (closure
    {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod f p \<noteq> 0})"
    and cont: "continuous_on ({0..} \<times> UNIV) (case_prod f)"
  shows "set_integrable lborel ({0..} \<times> UNIV) (case_prod f)"
proof -
  let ?H = "{0..} \<times> UNIV :: (real \<times> 'a) set"
  let ?S = "{p::real \<times> 'a. 0 \<le> fst p \<and> case_prod f p \<noteq> 0}"
  let ?D = "closure ?S"
  have closedH: "closed ?H"
    by (intro closed_Times) auto
  have DH: "?D \<subseteq> ?H"
    by (rule closure_minimal) (use closedH in auto)
  have contD: "continuous_on ?D (case_prod f)"
    by (rule continuous_on_subset[OF cont DH])
  have zeroD: "\<And>p. p \<in> ?H \<Longrightarrow> p \<notin> ?D \<Longrightarrow>
      case_prod f p = 0"
  proof -
    fix p :: "real \<times> 'a"
    assume H: "p \<in> ?H" and out: "p \<notin> ?D"
    show "case_prod f p = 0"
    proof (rule ccontr)
      assume nz: "case_prod f p \<noteq> 0"
      have "p \<in> ?S" using H nz by (cases p) auto
      then have "p \<in> ?D"
        using closure_subset[of ?S] by blast
      with out show False by simp
    qed
  qed
  show ?thesis
    by (rule set_integrable_continuous_compact_support
        [OF support DH contD zeroD])
qed

lemma tangential_halfspace_derivative_integrable_basis:
  fixes F g :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
    and b :: 'a
  assumes b: "b \<in> Basis"
    and support_F: "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod F p \<noteq> 0})"
    and deriv: "\<And>t v s. 0 \<le> t \<Longrightarrow>
      ((\<lambda>u. F t (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          g t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (at s)"
    and cont: "continuous_on ({0..} \<times> UNIV) (case_prod g)"
  shows "set_integrable lborel ({0..} \<times> UNIV) (case_prod g)"
proof -
  have support_g: "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod g p \<noteq> 0})"
    by (rule tangential_halfspace_derivative_support_basis
        [OF b support_F deriv])
  show ?thesis
    by (rule set_integrable_halfspace_continuous_compact_support
        [OF support_g cont])
qed

theorem Stokes_halfspace_one_tangential_basis_C1:
  fixes P P_t Q Q_b :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
    and b :: 'a
  assumes b: "b \<in> Basis"
    and support_P: "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod P p \<noteq> 0})"
    and deriv_P: "\<And>t y. 0 \<le> t \<Longrightarrow>
      ((\<lambda>s. P s y) has_vector_derivative P_t t y) (at t)"
    and cont_P: "continuous_on ({0..} \<times> UNIV) (case_prod P_t)"
    and support_Q: "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod Q p \<noteq> 0})"
    and deriv_Q: "\<And>t v s. 0 \<le> t \<Longrightarrow>
      ((\<lambda>u. Q t (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          Q_b t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (at s)"
    and cont_Q: "continuous_on ({0..} \<times> UNIV) (case_prod Q_b)"
  shows "(LINT p : {0..} \<times> UNIV | lborel.
    case_prod (\<lambda>t y. P_t t y - Q_b t y) p) =
    - (\<integral>y. P 0 y \<partial>lborel)"
proof -
  let ?H = "{0..} \<times> UNIV"
  have int_P: "set_integrable lborel ?H (case_prod P_t)"
    by (rule normal_halfspace_derivative_integrable
        [OF support_P deriv_P cont_P])
  have int_Q: "set_integrable lborel ?H (case_prod Q_b)"
    by (rule tangential_halfspace_derivative_integrable_basis
        [OF b support_Q deriv_Q cont_Q])
  have split: "(LINT p : ?H | lborel.
      case_prod (\<lambda>t y. P_t t y - Q_b t y) p) =
    (LINT p : ?H | lborel. case_prod P_t p) -
    (LINT p : ?H | lborel. case_prod Q_b p)"
    using int_P int_Q
    by (simp add: set_lebesgue_integral_def set_integrable_def
      algebra_simps split_def)
  have normal: "(LINT p : ?H | lborel. case_prod P_t p) =
      - (\<integral>y. P 0 y \<partial>lborel)"
    by (rule normal_halfspace_FTC_C1[OF support_P deriv_P cont_P])
  have tangent: "(LINT p : ?H | lborel. case_prod Q_b p) = 0"
    by (rule tangential_halfspace_integral_zero_basis_C1
        [OF b support_Q deriv_Q cont_Q])
  show ?thesis using split normal tangent by simp
qed

theorem Stokes_halfspace_basis_sum_C1:
  fixes P P_t :: "real \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
    and Q Q_b :: "'a \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real"
  assumes B: "B \<subseteq> Basis"
    and support_P: "compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod P p \<noteq> 0})"
    and deriv_P: "\<And>t y. 0 \<le> t \<Longrightarrow>
      ((\<lambda>s. P s y) has_vector_derivative P_t t y) (at t)"
    and cont_P: "continuous_on ({0..} \<times> UNIV) (case_prod P_t)"
    and support_Q: "\<And>b. b \<in> B \<Longrightarrow> compact (closure
      {p::real \<times> 'a. 0 \<le> fst p \<and> case_prod (Q b) p \<noteq> 0})"
    and deriv_Q: "\<And>b t v s. b \<in> B \<Longrightarrow> 0 \<le> t \<Longrightarrow>
      ((\<lambda>u. Q b t (\<Sum>j\<in>Basis. (v(b:=u)) j *\<^sub>R j))
        has_vector_derivative
          Q_b b t (\<Sum>j\<in>Basis. (v(b:=s)) j *\<^sub>R j)) (at s)"
    and cont_Q: "\<And>b. b \<in> B \<Longrightarrow>
      continuous_on ({0..} \<times> UNIV) (case_prod (Q_b b))"
  shows "(LINT p : {0..} \<times> UNIV | lborel.
    case_prod (\<lambda>t y. P_t t y - (\<Sum>b\<in>B. Q_b b t y)) p) =
    - (\<integral>y. P 0 y \<partial>lborel)"
proof -
  let ?H = "{0..} \<times> UNIV"
  let ?S = "\<lambda>t y. \<Sum>b\<in>B. Q_b b t y"
  let ?h = "\<lambda>b p. indicator ?H p *\<^sub>R case_prod (Q_b b) p"
  have basis: "\<And>b. b \<in> B \<Longrightarrow> b \<in> Basis"
    using B by auto
  have int_P: "set_integrable lborel ?H (case_prod P_t)"
    by (rule normal_halfspace_derivative_integrable
        [OF support_P deriv_P cont_P])
  have int_Q: "\<And>b. b \<in> B \<Longrightarrow>
      set_integrable lborel ?H (case_prod (Q_b b))"
  proof -
    fix b assume bB: "b \<in> B"
    show "set_integrable lborel ?H (case_prod (Q_b b))"
      by (rule tangential_halfspace_derivative_integrable_basis
          [OF basis[OF bB] support_Q[OF bB]])
         (use deriv_Q[OF bB] cont_Q[OF bB] in auto)
  qed
  have h_int: "\<And>b. b \<in> B \<Longrightarrow> integrable lborel (?h b)"
    using int_Q by (simp add: set_integrable_def)
  have fun_eq: "(\<lambda>p. indicator ?H p *\<^sub>R case_prod ?S p) =
      (\<lambda>p. \<Sum>b\<in>B. ?h b p)"
    by (rule ext) (auto simp: split_def sum_distrib_left)
  have int_S: "set_integrable lborel ?H (case_prod ?S)"
    unfolding set_integrable_def fun_eq
    by (rule Bochner_Integration.integrable_sum[OF h_int])
  have sum_zero: "(LINT p : ?H | lborel. case_prod ?S p) = 0"
  proof -
    have "(LINT p : ?H | lborel. case_prod ?S p) =
        (\<Sum>b\<in>B. \<integral>p. ?h b p \<partial>lborel)"
      unfolding set_lebesgue_integral_def fun_eq
      by (rule Bochner_Integration.integral_sum[OF h_int])
    also have "\<dots> = 0"
    proof -
      have each: "\<And>b. b \<in> B \<Longrightarrow>
          (\<integral>p. ?h b p \<partial>lborel) = 0"
      proof -
        fix b assume bB: "b \<in> B"
        show "(\<integral>p. ?h b p \<partial>lborel) = 0"
          using tangential_halfspace_integral_zero_basis_C1
            [OF basis[OF bB] support_Q[OF bB]]
            deriv_Q[OF bB] cont_Q[OF bB]
          by (simp add: set_lebesgue_integral_def)
      qed
      show ?thesis
        by (rule sum.neutral) (intro ballI, rule each)
    qed
    finally show ?thesis .
  qed
  have split: "(LINT p : ?H | lborel.
      case_prod (\<lambda>t y. P_t t y - ?S t y) p) =
    (LINT p : ?H | lborel. case_prod P_t p) -
    (LINT p : ?H | lborel. case_prod ?S p)"
    using int_P int_S
    by (simp add: set_lebesgue_integral_def set_integrable_def
      algebra_simps split_def)
  have normal: "(LINT p : ?H | lborel. case_prod P_t p) =
      - (\<integral>y. P 0 y \<partial>lborel)"
    by (rule normal_halfspace_FTC_C1[OF support_P deriv_P cont_P])
  show ?thesis using split normal sum_zero by simp
qed

end
