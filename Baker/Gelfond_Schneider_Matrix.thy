(*  Title:      Baker/Gelfond_Schneider_Matrix.thy
    Author:     OpenAI Codex

Matrix packaging for the indexed Gelfond-Schneider linear system. This gives
an AFP-matrix representation of the derivative-vanishing constraints and
bridges matrix-kernel equalities to the functional hypotheses used by the
auxiliary-function / zorder layer.
*)

theory Gelfond_Schneider_Matrix
  imports
    Gelfond_Schneider_Vanishing
    "Jordan_Normal_Form.Matrix_Kernel"
begin

section \<open>Matrix Form of the Indexed Linear System\<close>

definition gs_system_mat ::
  "gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex mat"
  where
    "gs_system_mat d m n q =
      mat (m * n) (q * q) (\<lambda>(u,t). gs_system_coeff_idx d n q u t)"

definition gs_coeff_vec :: "nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> complex vec"
  where
    "gs_coeff_vec q \<xi> = vec (q * q) \<xi>"

lemma gs_system_mat_carrier [simp]:
  "gs_system_mat d m n q \<in> carrier_mat (m * n) (q * q)"
  unfolding gs_system_mat_def by simp

lemma gs_coeff_vec_carrier [simp]:
  "gs_coeff_vec q \<xi> \<in> carrier_vec (q * q)"
  unfolding gs_coeff_vec_def by simp

lemma exists_nonzero_kernel_vec_rectangular:
  fixes A :: "'a :: idom mat"
  assumes A: "A \<in> carrier_mat p q"
  assumes hpq: "p < q"
  shows "\<exists>x. x \<in> carrier_vec q \<and> x \<noteq> 0\<^sub>v q \<and> A *\<^sub>v x = 0\<^sub>v p"
proof -
  define B where "B = A @\<^sub>r 0\<^sub>m (q - p) q"
  have B: "B \<in> carrier_mat q q"
    unfolding B_def using A
    by (metis add_diff_cancel_left' carrier_append_rows hpq less_imp_add_positive
        zero_carrier_mat)
  have row0: "row B p = 0\<^sub>v q"
  proof (rule eq_vecI)
    show "dim_vec (row B p) = dim_vec (0\<^sub>v q)"
      using B hpq by simp
  next
    fix j
    assume j: "j < dim_vec (0\<^sub>v q)"
    then have jq: "j < q"
      by simp
    have pq: "p < p + (q - p)"
      using hpq by simp
    have "(row B p) $ j = B $$ (p, j)"
      using B hpq jq by simp
    also have "\<dots> = 0"
      unfolding B_def append_rows_def using A hpq jq pq by simp
    finally show "(row B p) $ j = (0\<^sub>v q) $ j"
      using jq by simp
  qed
  have detB0: "det B = 0"
  proof -
    have rows: "(\<lambda>i. row B i) \<in> {0..<q} \<rightarrow> carrier_vec q"
      using B by auto
    let ?B0 = "mat\<^sub>r q q (\<lambda>i. if i = p then 0\<^sub>v q else row B i)"
    have eqB: "B = ?B0"
      by (rule eq_rowI) (use B hpq row0 in auto)
    have detB0': "det ?B0 = 0"
      by (rule det_row_0[OF hpq rows])
    show ?thesis
      using eqB detB0' by simp
  qed
  from det_0_iff_vec_prod_zero[OF B] detB0
  obtain x where x: "x \<in> carrier_vec q" "x \<noteq> 0\<^sub>v q" "B *\<^sub>v x = 0\<^sub>v q"
    by auto
  have Ax0: "A *\<^sub>v x = 0\<^sub>v p"
  proof -
    have Ax: "A *\<^sub>v x \<in> carrier_vec p"
      using A x by auto
    have "A *\<^sub>v x = vec_first (A *\<^sub>v x @\<^sub>v (0\<^sub>m (q - p) q *\<^sub>v x)) p"
    proof (rule eq_vecI)
      show "dim_vec (A *\<^sub>v x) = dim_vec (vec_first (A *\<^sub>v x @\<^sub>v (0\<^sub>m (q - p) q *\<^sub>v x)) p)"
        using A x by simp
    next
      fix i
      assume i: "i < dim_vec (vec_first (A *\<^sub>v x @\<^sub>v (0\<^sub>m (q - p) q *\<^sub>v x)) p)"
      then have ip: "i < p"
        by simp
      have i_append: "i < dim_vec (A *\<^sub>v x) + dim_vec (0\<^sub>m (q - p) q *\<^sub>v x)"
        using ip A x by simp
      have append_idx: "(A *\<^sub>v x @\<^sub>v (0\<^sub>m (q - p) q *\<^sub>v x)) $ i = (A *\<^sub>v x) $ i"
      proof -
        have "(A *\<^sub>v x @\<^sub>v (0\<^sub>m (q - p) q *\<^sub>v x)) $ i =
            (if i < dim_vec (A *\<^sub>v x) then (A *\<^sub>v x) $ i
             else (0\<^sub>m (q - p) q *\<^sub>v x) $ (i - dim_vec (A *\<^sub>v x)))"
          by (rule index_append_vec(1)[OF i_append])
        then show ?thesis
          using ip A x by simp
      qed
      show "(A *\<^sub>v x) $ i = vec_first (A *\<^sub>v x @\<^sub>v (0\<^sub>m (q - p) q *\<^sub>v x)) p $ i"
        unfolding vec_first_def using append_idx i by simp
    qed
    also have "\<dots> = vec_first (B *\<^sub>v x) p"
      unfolding B_def by (simp add: mat_mult_append[OF A zero_carrier_mat x(1)])
    also have "\<dots> = 0\<^sub>v p"
    proof -
      have "vec_first (B *\<^sub>v x) p = vec_first (0\<^sub>v q) p"
        using x(3) by simp
      also have "\<dots> = 0\<^sub>v p"
      proof (rule eq_vecI)
        show "dim_vec (vec_first (0\<^sub>v q) p) = dim_vec (0\<^sub>v p)"
          by simp
      next
        fix i
        assume i: "i < dim_vec (0\<^sub>v p)"
        then show "vec_first (0\<^sub>v q) p $ i = (0\<^sub>v p) $ i"
          using hpq by (simp add: vec_first_def)
      qed
      finally show ?thesis .
    qed
    finally show ?thesis .
  qed
  show ?thesis
    using x Ax0 by blast
qed

lemma gs_coeff_vec_eqI:
  assumes v: "v \<in> carrier_vec (q * q)"
  shows "gs_coeff_vec q (\<lambda>t. v $ t) = v"
proof (rule eq_vecI)
  show "dim_vec (gs_coeff_vec q (\<lambda>t. v $ t)) = dim_vec v"
    using v unfolding gs_coeff_vec_def by simp
next
  fix t
  assume t: "t < dim_vec v"
  then have "t < q * q"
    using v by simp
  then show "gs_coeff_vec q (\<lambda>t. v $ t) $ t = v $ t"
    unfolding gs_coeff_vec_def by simp
qed

lemma gs_system_mat_mult_component:
  assumes ult: "u < m * n"
  shows "((gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi>) $ u) =
    (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t)"
proof -
  have urow: "u < dim_row (gs_system_mat d m n q)"
    using ult unfolding gs_system_mat_def by simp
  have h1: "((gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi>) $ u) =
      row (gs_system_mat d m n q) u \<bullet> gs_coeff_vec q \<xi>"
    by (rule index_mult_mat_vec[OF urow])
  have h2: "row (gs_system_mat d m n q) u \<bullet> gs_coeff_vec q \<xi> =
      (\<Sum>i = 0..<q * q. \<xi> i * gs_system_coeff_idx d n q u i)"
    using ult
    unfolding scalar_prod_def gs_system_mat_def gs_coeff_vec_def
    by (simp add: index_mat index_vec mult.commute)
  have h3: "(\<Sum>i = 0..<q * q. \<xi> i * gs_system_coeff_idx d n q u i) =
      (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t)"
    by (simp add: atLeast0LessThan)
  show ?thesis
    using h1 h2 h3 by simp
qed

lemma gs_system_mat_kernel_iff:
  "gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n) \<longleftrightarrow>
    (\<forall>u<m * n. (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0)"
proof
  assume ker: "gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
  show "\<forall>u<m * n. (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
  proof
    fix u
    show "u < m * n \<longrightarrow> (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
    proof
      assume ult: "u < m * n"
      have "((gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi>) $ u) = (0\<^sub>v (m * n) :: complex vec) $ u"
        using ker by simp
      then show "(\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
        using ult by (simp add: gs_system_mat_mult_component)
    qed
  qed
next
  assume sys0: "\<forall>u<m * n. (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
  show "gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
  proof (rule eq_vecI)
    show "dim_vec (gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi>) = dim_vec (0\<^sub>v (m * n))"
      unfolding gs_system_mat_def by simp
  next
    fix u
    assume ult: "u < dim_vec (0\<^sub>v (m * n))"
    then have "u < m * n"
      by simp
    then have "(\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
      using sys0 by blast
    then show "(gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi>) $ u = (0\<^sub>v (m * n)) $ u"
      using ult by (simp add: gs_system_mat_mult_component)
  qed
qed

corollary gs_aux_fun_vec_deriv_vanish_at_node_of_kernel:
  assumes d: "is_gelfond_schneider_data d"
  assumes npos: "n > 0"
  assumes ker: "gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
  assumes llt: "l < m"
  assumes klt: "k < n"
  shows "((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat (Suc l)) = 0"
proof -
  have sys0: "\<And>u. u < m * n \<Longrightarrow> (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
    using gs_system_mat_kernel_iff[of d m n q \<xi>] ker by blast
  show ?thesis
    by (rule gs_aux_fun_vec_deriv_vanish_at_node[OF d npos sys0 llt klt])
qed

corollary gs_min_order_ge_of_kernel_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes mpos: "m > 0"
  assumes npos: "n > 0"
  assumes coeff_nz: "\<exists>t<q * q. \<xi> t \<noteq> 0"
  assumes ker: "gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
  shows "gs_min_order m d q \<xi> \<ge> n"
proof -
  have sys0: "\<And>u. u < m * n \<Longrightarrow> (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
    using gs_system_mat_kernel_iff[of d m n q \<xi>] ker by blast
  show ?thesis
    by (rule gs_min_order_ge_of_coeff_nonzero[OF d qpos mpos npos coeff_nz sys0])
qed

corollary gs_system_mat_exists_nonzero_coeffs:
  assumes mnq: "m * n < q * q"
  obtains \<xi> where "\<exists>t<q * q. \<xi> t \<noteq> 0"
    and "gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
proof -
  have ex_v: "\<exists>v. v \<in> carrier_vec (q * q) \<and> v \<noteq> 0\<^sub>v (q * q) \<and>
    gs_system_mat d m n q *\<^sub>v v = 0\<^sub>v (m * n)"
    by (rule exists_nonzero_kernel_vec_rectangular[OF gs_system_mat_carrier mnq])
  then obtain v where v: "v \<in> carrier_vec (q * q)" "v \<noteq> 0\<^sub>v (q * q)"
    "gs_system_mat d m n q *\<^sub>v v = 0\<^sub>v (m * n)"
    by blast
  obtain t where t: "t < q * q" "v $ t \<noteq> 0"
    using v by force
  define \<xi> where "\<xi> = (\<lambda>t. v $ t)"
  have nz: "\<exists>t<q * q. \<xi> t \<noteq> 0"
    using t unfolding \<xi>_def by blast
  have ker: "gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
    unfolding \<xi>_def by (simp add: gs_coeff_vec_eqI[OF v(1)] v(3))
  show thesis
    by (rule that[OF nz ker])
qed

corollary gs_exists_auxiliary_coeffs_with_min_order:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes mpos: "m > 0"
  assumes npos: "n > 0"
  assumes mnq: "m * n < q * q"
  obtains \<xi> where "\<exists>t<q * q. \<xi> t \<noteq> 0"
    and "gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
    and "gs_min_order m d q \<xi> \<ge> n"
proof -
  obtain \<xi> where nz: "\<exists>t<q * q. \<xi> t \<noteq> 0"
    and ker: "gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
    by (rule gs_system_mat_exists_nonzero_coeffs[OF mnq])
  have ord: "gs_min_order m d q \<xi> \<ge> n"
    by (rule gs_min_order_ge_of_kernel_nonzero[OF d qpos mpos npos nz ker])
  show thesis
    by (rule that[OF nz ker ord])
qed

corollary gs_exists_auxiliary_coeffs_with_min_order_witness:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes mpos: "m > 0"
  assumes npos: "n > 0"
  assumes mnq: "m * n < q * q"
  obtains \<xi> r where "\<exists>t<q * q. \<xi> t \<noteq> 0"
    and "gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
    and "gs_min_order m d q \<xi> \<ge> n"
    and "r = nat (gs_min_order m d q \<xi>)"
    and "((deriv ^^ r) (gs_aux_fun_vec d q \<xi>)) (gs_min_order_node m d q \<xi>) \<noteq> 0"
proof -
  obtain \<xi> where nz: "\<exists>t<q * q. \<xi> t \<noteq> 0"
    and ker: "gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
    and ord: "gs_min_order m d q \<xi> \<ge> n"
    by (rule gs_exists_auxiliary_coeffs_with_min_order[OF d qpos mpos npos mnq])
  define r where "r = nat (gs_min_order m d q \<xi>)"
  have deriv_nz0:
      "((deriv ^^ nat (gs_min_order m d q \<xi>)) (gs_aux_fun_vec d q \<xi>))
        (gs_min_order_node m d q \<xi>) \<noteq> 0"
    by (rule gs_min_order_deriv_nonzero_of_coeff_nonzero[OF d qpos nz])
  have deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec d q \<xi>)) (gs_min_order_node m d q \<xi>) \<noteq> 0"
    using deriv_nz0 by (simp add: r_def)
  show thesis
  proof (rule that[of \<xi> r])
    show "\<exists>t<q * q. \<xi> t \<noteq> 0"
      by (rule nz)
    show "gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
      by (rule ker)
    show "gs_min_order m d q \<xi> \<ge> n"
      by (rule ord)
    show "r = nat (gs_min_order m d q \<xi>)"
      by (simp add: r_def)
    show "((deriv ^^ r) (gs_aux_fun_vec d q \<xi>)) (gs_min_order_node m d q \<xi>) \<noteq> 0"
      by (rule deriv_nz)
  qed
qed

section \<open>Algebraic Kernel Vectors\<close>

definition algebraic_mat :: "complex mat \<Rightarrow> bool"
  where "algebraic_mat A \<longleftrightarrow> (\<forall>i<dim_row A. \<forall>j<dim_col A. algebraic (A $$ (i, j)))"

definition algebraic_vec :: "complex vec \<Rightarrow> bool"
  where "algebraic_vec v \<longleftrightarrow> (\<forall>i<dim_vec v. algebraic (v $ i))"

lemma gs_system_mat_algebraic:
  assumes d: "is_gelfond_schneider_data d"
  shows "algebraic_mat (gs_system_mat d m n q)"
proof (unfold algebraic_mat_def, intro allI impI)
  fix i j
  assume ij: "i < dim_row (gs_system_mat d m n q)" "j < dim_col (gs_system_mat d m n q)"
  then have ij': "i < m * n" "j < q * q"
    unfolding gs_system_mat_def by simp_all
  show "algebraic (gs_system_mat d m n q $$ (i, j))"
    unfolding gs_system_mat_def
    using ij' by (simp add: gelfond_schneider_data_system_coeff_idx_algebraic[OF d])
qed

lemma algebraic_matD:
  assumes "algebraic_mat A"
  assumes "i < dim_row A"
  assumes "j < dim_col A"
  shows "algebraic (A $$ (i, j))"
  using assms unfolding algebraic_mat_def by blast

lemma algebraic_vecD:
  fixes v :: "complex vec"
  assumes "algebraic_vec v"
  assumes "i < dim_vec v"
  shows "algebraic (v $ i)"
  using assms unfolding algebraic_vec_def by blast

lemma algebraic_mat_swaprows:
  assumes A: "A \<in> carrier_mat nr nc"
  assumes ij: "i < nr" "j < nr"
  assumes algA: "algebraic_mat A"
  shows "algebraic_mat (swaprows i j A)"
proof (unfold algebraic_mat_def, intro allI impI)
  fix r c
  assume rc: "r < dim_row (swaprows i j A)" "c < dim_col (swaprows i j A)"
  then have rcA: "r < nr" "c < nc"
    using A by simp_all
  have "swaprows i j A $$ (r, c) =
      (if i = r then A $$ (j, c) else if j = r then A $$ (i, c) else A $$ (r, c))"
    using rc A ij by simp
  then show "algebraic (swaprows i j A $$ (r, c))"
    using algA rcA ij algebraic_matD assms(1) by force
qed

lemma algebraic_mat_multrow:
  assumes A: "A \<in> carrier_mat nr nc"
  assumes i: "i < nr"
  assumes alga: "algebraic a"
  assumes algA: "algebraic_mat A"
  shows "algebraic_mat (multrow i a A)"
proof (unfold algebraic_mat_def, intro allI impI)
  fix r c
  assume rc: "r < dim_row (multrow i a A)" "c < dim_col (multrow i a A)"
  then have rcA: "r < nr" "c < nc"
    using A by simp_all
  have "multrow i a A $$ (r, c) = (if i = r then a * A $$ (r, c) else A $$ (r, c))"
    using rc A i by simp
  then show "algebraic (multrow i a A $$ (r, c))"
    using algA rcA alga algebraic_matD rc by auto
qed

lemma algebraic_mat_addrow:
  assumes A: "A \<in> carrier_mat nr nc"
  assumes kl: "k < nr" "l < nr"
  assumes alga: "algebraic a"
  assumes algA: "algebraic_mat A"
  shows "algebraic_mat (addrow a k l A)"
proof (unfold algebraic_mat_def, intro allI impI)
  fix r c
  assume rc: "r < dim_row (addrow a k l A)" "c < dim_col (addrow a k l A)"
  then have rcA: "r < nr" "c < nc"
    using A by simp_all
  have "addrow a k l A $$ (r, c) =
      (if k = r then a * A $$ (l, c) + A $$ (r, c) else A $$ (r, c))"
    using rc A kl by simp
  then show "algebraic (addrow a k l A $$ (r, c))"
    using algA rcA kl alga
    by (metis algebraic_matD algebraic_plus algebraic_times assms(1) carrier_matD)
qed

lemma algebraic_mat_eliminate_entries:
  assumes A: "A \<in> carrier_mat nr nc"
  assumes B: "B \<in> carrier_mat nr nc'"
  assumes IJ: "I < nr" "J < nc"
  assumes algA: "algebraic_mat A"
  assumes algB: "algebraic_mat B"
  shows "algebraic_mat (eliminate_entries (\<lambda>i. A $$ (i, J)) B I J)"
proof (unfold algebraic_mat_def eliminate_entries_gen_def, intro allI impI)
  fix r c
  assume rc:
      "r < dim_row (mat (dim_row B) (dim_col B)
        (\<lambda>(i, j). if i \<noteq> I then B $$ (i, j) - A $$ (i, J) * B $$ (I, j) else B $$ (i, j)))"
      "c < dim_col (mat (dim_row B) (dim_col B)
        (\<lambda>(i, j). if i \<noteq> I then B $$ (i, j) - A $$ (i, J) * B $$ (I, j) else B $$ (i, j)))"
  then have rcB: "r < nr" "c < nc'"
    using B by simp_all
  have "algebraic (A $$ (r, J))"
    using A IJ(2) algebraic_matD assms(5) rcB(1) by blast
  moreover have "algebraic (B $$ (I, c))"
    using B IJ(1) algebraic_matD assms(6) rcB(2) by blast
  moreover have "algebraic (B $$ (r, c))"
    using B algebraic_matD assms(6) rcB(1,2) by blast
  ultimately
  show "algebraic
            (Matrix.mat (dim_row B) (dim_col B)
              (\<lambda>(i, j).
                  if i \<noteq> I then B $$ (i, j) - A $$ (i, J) * B $$ (I, j)
                  else B $$ (i, j)) $$
             (r, c))"
    using rc by auto
qed

lemma gauss_jordan_main_fst_algebraic:
  assumes algA: "algebraic_mat A"
  shows "algebraic_mat (fst (gauss_jordan_main A B i j))"
  using algA
proof (induct A B i j rule: gauss_jordan_main.induct)
  case (1 A B i j)
  note IH0 = 1(1-4)
  note algA = 1(5)
  show ?case
  proof (cases "i < dim_row A \<and> j < dim_col A")
    case False
    from False algA show ?thesis
      by (smt (verit, best) fst_eqD gauss_jordan_main.simps)
  next
    case True
    then have ij: "i < dim_row A" "j < dim_col A"
      by auto
    show ?thesis
    proof (cases "A $$ (i, j) = 0")
      case zero: True
      let ?is = "concat (map (\<lambda>i'. if A $$ (i', j) \<noteq> 0 then [i'] else []) [Suc i..<dim_row A])"
      show ?thesis
      proof (cases ?is)
        case Nil
        have rec: "algebraic_mat (fst (gauss_jordan_main A B i (Suc j)))"
          by (rule IH0(1)[OF refl refl True refl zero Nil algA])
        have eq: "fst (gauss_jordan_main A B i j) =
            fst (gauss_jordan_main A B i (Suc j))"
          unfolding gauss_jordan_main.simps[of A B i j] Let_def
          using True zero by (simp add: local.Nil)
        from rec eq show ?thesis
          by simp
      next
        case (Cons i' rest)
        then have is_eq: "?is = i' # rest"
          by simp
        have i'_in: "i' \<in> set ?is"
          using is_eq by auto
        then have i': "i' < dim_row A"
          by auto
        have algS: "algebraic_mat (swaprows i i' A)"
          by (rule algebraic_mat_swaprows) (use algA ij i' in auto)
        have rec:
          "algebraic_mat (fst (gauss_jordan_main (swaprows i i' A) (swaprows i i' B) i j))"
          by (rule IH0(2)[OF refl refl True refl zero is_eq algS])
        have eq: "fst (gauss_jordan_main A B i j) =
            fst (gauss_jordan_main (swaprows i i' A) (swaprows i i' B) i j)"
          unfolding gauss_jordan_main.simps[of A B i j] Let_def
          using True zero is_eq by simp
        from rec eq show ?thesis
          by simp
      qed
    next
      case nonzero: False
      show ?thesis
      proof (cases "A $$ (i, j) = 1")
        case one: True
        let ?v = "\<lambda>k. A $$ (k, j)"
        have algE: "algebraic_mat (eliminate_entries ?v A i j)"
          by (rule algebraic_mat_eliminate_entries) (use algA ij in auto)
        have rec:
          "algebraic_mat
            (fst (gauss_jordan_main (eliminate_entries ?v A i j) (eliminate_entries ?v B i j)
              (Suc i) (Suc j)))"
          by (rule IH0(3)[OF refl refl True refl nonzero one refl algE])
        have eq: "fst (gauss_jordan_main A B i j) =
            fst (gauss_jordan_main (eliminate_entries ?v A i j) (eliminate_entries ?v B i j)
              (Suc i) (Suc j))"
          unfolding gauss_jordan_main.simps[of A B i j] Let_def
          using True nonzero one by simp
        from rec eq show ?thesis
          by simp
      next
        case not_one: False
        let ?a = "inverse (A $$ (i, j))"
        have algInv: "algebraic ?a"
        proof (rule algebraic_inverse)
          show "algebraic (A $$ (i, j))"
            by (rule algebraic_matD[OF algA ij])
        qed
        have algM: "algebraic_mat (multrow i ?a A)"
          by (rule algebraic_mat_multrow[of A "dim_row A" "dim_col A" i ?a])
            (use ij algInv algA in auto)
        have rec:
          "algebraic_mat (fst (gauss_jordan_main (multrow i ?a A) (multrow i ?a B) i j))"
          by (rule IH0(4)[OF refl refl True refl nonzero not_one refl algM])
        have eq: "fst (gauss_jordan_main A B i j) =
            fst (gauss_jordan_main (multrow i ?a A) (multrow i ?a B) i j)"
          unfolding gauss_jordan_main.simps[of A B i j] Let_def
          using True nonzero not_one by simp
        from rec eq show ?thesis
          by simp
      qed
    qed
  qed
qed

lemma gauss_jordan_single_algebraic:
  assumes "A \<in> carrier_mat nr nc"
  assumes "algebraic_mat A"
  shows "algebraic_mat (gauss_jordan_single A)"
  unfolding gauss_jordan_single_def gauss_jordan_def
  by (rule gauss_jordan_main_fst_algebraic[OF assms(2)])

lemma find_base_vector_algebraic:
  assumes row: "row_echelon_form A"
  assumes A: "A \<in> carrier_mat nr nc"
  assumes neq: "snd ` set (pivot_positions A) \<noteq> {0..<nc}"
  assumes algA: "algebraic_mat A"
  shows "algebraic_vec (find_base_vector A)"
proof -
  define cands where "cands = filter (\<lambda>j. j \<notin> snd ` set (pivot_positions A)) [0..<nc]"
  from A have dim: "dim_row A = nr" "dim_col A = nc"
    by auto
  from row[unfolded row_echelon_form_def] obtain p where pivot: "pivot_fun A p nc"
    using dim by auto
  note piv = pivot_positions[OF A pivot]
  have pivot_cols_subset: "snd ` set (pivot_positions A) \<subseteq> {0..<nc}"
  proof
    fix j
    assume j: "j \<in> snd ` set (pivot_positions A)"
    then obtain i where ij: "(i, j) \<in> set (pivot_positions A)"
      by auto
    from ij piv obtain k where k: "k < nr" "p k \<noteq> nc" "j = p k"
      by auto
    have "p k \<le> nc"
      using pivot k(1) dim(1) unfolding pivot_fun_def Let_def by blast
    with k show "j \<in> {0..<nc}"
      by auto
  qed
  have "set cands \<noteq> {}"
    using neq pivot_cols_subset unfolding cands_def by auto
  then obtain c cs where cands: "cands = c # cs"
    by (cases cands) auto
  hence fv: "find_base_vector A = non_pivot_base A (pivot_positions A) c"
    unfolding find_base_vector_def Let_def cands_def dim by auto
  have c_lt: "c < nc"
  proof -
    have "c \<in> set cands"
      using cands by simp
    then show ?thesis
      unfolding cands_def by auto
  qed
  show ?thesis
  proof (unfold algebraic_vec_def, intro allI impI)
    fix i
    assume i: "i < dim_vec (find_base_vector A)"
    then have i_lt: "i < nc"
      using find_base_vector[OF row A neq] by simp
    have idx:
        "find_base_vector A $ i =
          (if i = c then 1 else
            (case map_of (map prod.swap (pivot_positions A)) i of
              Some j => - A $$ (j, c) | None => 0))"
      unfolding fv non_pivot_base_def Let_def using i_lt by (simp add: dim(2))
    show "algebraic (find_base_vector A $ i)"
    proof (cases "i = c")
      case True
      with idx show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "map_of (map prod.swap (pivot_positions A)) i")
        case None
        with False idx show ?thesis by simp
      next
        case (Some j)
        then have "(j, i) \<in> set (pivot_positions A)"
          by (auto dest: map_of_SomeD)
        then have j_lt: "j < nr"
          using piv(1) by auto
        have "algebraic (A $$ (j, c))"
          using algebraic_mat_def assms(4) c_lt dim j_lt by blast
        with False Some idx show ?thesis
          by simp
      qed
    qed
  qed
qed

lemma exists_nonzero_algebraic_kernel_vec_rectangular:
  fixes A :: "complex mat"
  assumes A: "A \<in> carrier_mat p q"
  assumes hpq: "p < q"
  assumes algA: "algebraic_mat A"
  shows "\<exists>v. v \<in> carrier_vec q \<and> v \<noteq> 0\<^sub>v q \<and> A *\<^sub>v v = 0\<^sub>v p \<and> algebraic_vec v"
proof -
  obtain P Q where C_eq: "gauss_jordan_single A = P * A"
    and QP: "Q * P = 1\<^sub>m p"
    and P: "P \<in> carrier_mat p p"
    and Q: "Q \<in> carrier_mat p p"
    and C: "gauss_jordan_single A \<in> carrier_mat p q"
    and rowC: "row_echelon_form (gauss_jordan_single A)"
    using gauss_jordan_single[OF A refl] by blast
  have algC: "algebraic_mat (gauss_jordan_single A)"
    by (rule gauss_jordan_single_algebraic[OF A algA])
  obtain piv where piv: "pivot_fun (gauss_jordan_single A) piv q"
    using rowC C unfolding row_echelon_form_def by auto
  note pp = pivot_positions[OF C piv]
  have len_pp_le: "length (pivot_positions (gauss_jordan_single A)) \<le> p"
  proof -
    have subset:
      "{i. i < p \<and> Matrix.row (gauss_jordan_single A) i \<noteq> 0\<^sub>v q} \<subseteq> {0..<p}"
      by auto
    have "card {i. i < p \<and> Matrix.row (gauss_jordan_single A) i \<noteq> 0\<^sub>v q} \<le> card {0..<p}"
      using subset card_atLeastLessThan minus_nat.diff_0 subset_eq_atLeast0_lessThan_card by presburger
    then show ?thesis
      using pp(4) by simp
  qed
  have card_pp: "card (snd ` set (pivot_positions (gauss_jordan_single A))) =
      length (pivot_positions (gauss_jordan_single A))"
    using distinct_card pp(3) by fastforce
  have neq: "snd ` set (pivot_positions (gauss_jordan_single A)) \<noteq> {0..<q}"
  proof
    assume eqp: "snd ` set (pivot_positions (gauss_jordan_single A)) = {0..<q}"
    have "q = card (snd ` set (pivot_positions (gauss_jordan_single A)))"
      unfolding eqp by simp
    also have "\<dots> = length (pivot_positions (gauss_jordan_single A))"
      by (rule card_pp)
    also have "\<dots> \<le> p"
      by (rule len_pp_le)
    finally show False
      using hpq by simp
  qed
  from find_base_vector[OF rowC C neq]
  have v: "find_base_vector (gauss_jordan_single A) \<in> carrier_vec q"
    "find_base_vector (gauss_jordan_single A) \<noteq> 0\<^sub>v q"
    "gauss_jordan_single A *\<^sub>v find_base_vector (gauss_jordan_single A) = 0\<^sub>v p"
    by auto
  have algv: "algebraic_vec (find_base_vector (gauss_jordan_single A))"
    by (rule find_base_vector_algebraic[OF rowC C neq algC])
  have ker_eq: "mat_kernel (gauss_jordan_single A) = mat_kernel A"
    unfolding C_eq by (rule mat_kernel_mult_eq[OF A P Q QP])
  have "find_base_vector (gauss_jordan_single A) \<in> mat_kernel (gauss_jordan_single A)"
    by (rule mat_kernelI[OF C v(1) v(3)])
  then have "find_base_vector (gauss_jordan_single A) \<in> mat_kernel A"
    unfolding ker_eq by simp
  from A and this
  have Av0: "A *\<^sub>v find_base_vector (gauss_jordan_single A) = 0\<^sub>v p"
    by (rule mat_kernelD(2))
  show ?thesis
    using v(1-2) Av0 algv by blast
qed

lemma exists_nonzero_algebraic_int_kernel_vec_rectangular:
  fixes A :: "complex mat"
  assumes A: "A \<in> carrier_mat p q"
  assumes hpq: "p < q"
  assumes algA: "algebraic_mat A"
  shows "\<exists>v. v \<in> carrier_vec q \<and> v \<noteq> 0\<^sub>v q \<and> A *\<^sub>v v = 0\<^sub>v p \<and>
    (\<forall>i<q. algebraic_int (v $ i))"
proof -
  obtain v where v: "v \<in> carrier_vec q" "v \<noteq> 0\<^sub>v q" "A *\<^sub>v v = 0\<^sub>v p" "algebraic_vec v"
    using exists_nonzero_algebraic_kernel_vec_rectangular[OF A hpq algA] by blast
  define c :: int where "c = (\<Prod>i<q. gs_c0 (v $ i))"
  have c_nz: "c \<noteq> 0"
  proof
    assume c0: "c = 0"
    have "\<exists>i\<in>{..<q}. gs_c0 (v $ i) = 0"
      using c0 unfolding c_def by (simp add: prod_zero_iff)
    then obtain i where i: "i < q" "gs_c0 (v $ i) = 0"
      by auto
    have alg_i: "algebraic (v $ i)"
      by (rule algebraic_vecD[OF v(4)]) (use v i in auto)
    from gs_c0_nonzero[OF alg_i] i show False
      by simp
  qed
  define w where "w = of_int c \<cdot>\<^sub>v v"
  have w: "w \<in> carrier_vec q"
    unfolding w_def using v by auto
  have Aw0: "A *\<^sub>v w = 0\<^sub>v p"
  proof -
    have "A *\<^sub>v w = of_int c \<cdot>\<^sub>v (A *\<^sub>v v)"
      unfolding w_def by (rule Matrix.mult_mat_vec[OF A v(1)])
    also have "\<dots> = 0\<^sub>v p"
      using v(3) by auto
    finally show ?thesis .
  qed
  obtain j where j: "j < q" "v $ j \<noteq> 0"
    using v by force
  have w_nz: "w \<noteq> 0\<^sub>v q"
  proof
    assume "w = 0\<^sub>v q"
    then have "w $ j = 0"
      using j by simp
    then have "of_int c * (v $ j) = 0"
      unfolding w_def using j v(1) by (simp add: Matrix.index_smult_vec)
    then have "of_int c = 0"
      using j by simp
    with c_nz show False
      by fastforce
  qed
  have wint: "\<forall>i<q. algebraic_int (w $ i)"
  proof
    fix i
    show "i < q \<longrightarrow> algebraic_int (w $ i)"
    proof
      assume i: "i < q"
      have alg_i: "algebraic (v $ i)"
        by (rule algebraic_vecD[OF v(4)]) (use v i in auto)
      have ai0: "algebraic_int (of_int (gs_c0 (v $ i)) * (v $ i))"
        by (rule gs_c0_algebraic_int[OF alg_i])
      have ai1: "algebraic_int
          (of_int (\<Prod>k\<in>{..<q} - {i}. gs_c0 (v $ k)) * (of_int (gs_c0 (v $ i)) * (v $ i)))"
        by (rule algebraic_int_of_int_scale[OF ai0])
      have eqc:
          "of_int (\<Prod>k\<in>{..<q} - {i}. gs_c0 (v $ k)) * (of_int (gs_c0 (v $ i)) * (v $ i)) =
            of_int c * (v $ i)"
        unfolding c_def using i by (simp add: algebra_simps prod.remove)
      have ai2: "algebraic_int (of_int c * (v $ i))"
        using ai1 by (simp add: eqc[symmetric])
      show "algebraic_int (w $ i)"
        unfolding w_def using i v(1) ai2 by (simp add: Matrix.index_smult_vec)
    qed
  qed
  show ?thesis
    using w w_nz Aw0 wint by blast
qed

end
