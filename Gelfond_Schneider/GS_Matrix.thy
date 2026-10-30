(*  Title:      Gelfond_Schneider/GS_Matrix.thy
    Author:     OpenAI Codex

Matrix packaging for the indexed Gelfond-Schneider linear system. This gives
an AFP-matrix representation of the derivative-vanishing constraints and
bridges matrix-kernel equalities to the functional hypotheses used by the
auxiliary-function / zorder layer.
*)

theory GS_Matrix
  imports
    GS_Vanishing
    "Jordan_Normal_Form.Matrix_Kernel"
begin

section \<open>Matrix Form of the Indexed Linear System\<close>

definition gs_system_mat ::
  "gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex mat"
  where
    "gs_system_mat d m n q \<equiv> mat (m * n) (q * q) (\<lambda>(u,t). gs_system_coeff_idx d n q u t)"

definition gs_coeff_vec :: "nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> complex vec"
  where "gs_coeff_vec q \<xi> \<equiv> vec (q * q) \<xi>"

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
  define B where "B \<equiv> A @\<^sub>r 0\<^sub>m (q - p) q"
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
    have "(row B p) $ j = B $$ (p, j)"
      using B hpq jq by simp
    also have "\<dots> = 0"
      unfolding B_def append_rows_def using A hpq jq hpq by simp
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
      have append_idx: "(A *\<^sub>v x @\<^sub>v (0\<^sub>m (q - p) q *\<^sub>v x)) $ i = (A *\<^sub>v x) $ i"
        using ip A x by (simp add: index_append_vec(1))
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
        using hpq by (intro eq_vecI) (auto simp add: vec_first_def)
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
  using assms
  by (metis Matrix.vec_eq_iff carrier_vecD dim_vec gs_coeff_vec_def index_vec)

lemma gs_system_mat_mult_component:
  assumes ult: "u < m * n"
  shows "((gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi>) $ u) =
    (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t)"
proof -
  have urow: "u < dim_row (gs_system_mat d m n q)"
    using ult unfolding gs_system_mat_def by simp
  have "((gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi>) $ u) = row (gs_system_mat d m n q) u \<bullet> gs_coeff_vec q \<xi>"
    by (rule index_mult_mat_vec[OF urow])
  also have "\<dots> = (\<Sum>i = 0..<q * q. \<xi> i * gs_system_coeff_idx d n q u i)"
    using ult
    unfolding scalar_prod_def gs_system_mat_def gs_coeff_vec_def
    by (simp add: index_mat index_vec mult.commute)
  also have "\<dots> = (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t)"
    by (simp add: atLeast0LessThan)
  finally show ?thesis .
qed

lemma gs_system_mat_kernel_iff:
  "gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n) \<longleftrightarrow>
    (\<forall>u<m * n. (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0)"
proof
  assume ker: "gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
  show "\<forall>u<m * n. (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
    by (metis (lifting) gs_system_mat_mult_component index_zero_vec(1) ker)
next
  assume sys0: "\<forall>u<m * n. (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
  show "gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
  proof (rule eq_vecI)
    show "dim_vec (gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi>) = dim_vec (0\<^sub>v (m * n))"
      unfolding gs_system_mat_def by simp
  next
    fix u
    assume ult: "u < dim_vec (0\<^sub>v (m * n))"
    then have "(\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
      using sys0 by force
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
  obtain v where v: "v \<in> carrier_vec (q * q)" "v \<noteq> 0\<^sub>v (q * q)"
                   "gs_system_mat d m n q *\<^sub>v v = 0\<^sub>v (m * n)"
    using exists_nonzero_kernel_vec_rectangular[OF gs_system_mat_carrier mnq]
    by blast
  then obtain t where "t < q * q" "v $ t \<noteq> 0"
    by force
  then show thesis
    using that v by (metis gs_coeff_vec_eqI)
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
  using assms
  by (metis gs_min_order_ge_of_kernel_nonzero gs_system_mat_exists_nonzero_coeffs)

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
  have deriv_nz: "((deriv ^^ r) (gs_aux_fun_vec d q \<xi>)) (gs_min_order_node m d q \<xi>) \<noteq> 0"
    using deriv_nz0 by (simp add: r_def)
  show thesis
    using deriv_nz ker local.ord nz r_def that by metis
qed

section \<open>Algebraic Kernel Vectors\<close>

definition algebraic_mat :: "complex mat \<Rightarrow> bool"
  where "algebraic_mat A \<equiv> (\<forall>i<dim_row A. \<forall>j<dim_col A. algebraic (A $$ (i, j)))"

definition algebraic_vec :: "complex vec \<Rightarrow> bool"
  where "algebraic_vec v \<equiv> (\<forall>i<dim_vec v. algebraic (v $ i))"

lemma gs_system_mat_algebraic:
  assumes d: "is_gelfond_schneider_data d"
  shows "algebraic_mat (gs_system_mat d m n q)"
  unfolding algebraic_mat_def
proof (intro allI impI)
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
  unfolding algebraic_mat_def
proof (intro allI impI)
  fix r c
  assume "r < dim_row (swaprows i j A)" "c < dim_col (swaprows i j A)"
  then have "r < nr" "c < nc"
       and "swaprows i j A $$ (r, c) =
              (if i = r then A $$ (j, c) else if j = r then A $$ (i, c) else A $$ (r, c))"
    using A ij by simp_all
  then show "algebraic (swaprows i j A $$ (r, c))"
    using algA ij algebraic_matD A by force
qed

lemma algebraic_mat_multrow:
  assumes A: "A \<in> carrier_mat nr nc"
  assumes i: "i < nr"
  assumes alga: "algebraic a"
  assumes algA: "algebraic_mat A"
  shows "algebraic_mat (multrow i a A)"
  unfolding algebraic_mat_def
proof (intro allI impI)
  fix r c
  assume rc: "r < dim_row (multrow i a A)" "c < dim_col (multrow i a A)"
  then have "r < nr" "c < nc" 
       and "multrow i a A $$ (r, c) = (if i = r then a * A $$ (r, c) else A $$ (r, c))"
    using A i by simp_all
  then show "algebraic (multrow i a A $$ (r, c))"
    using algA alga algebraic_matD rc by auto
qed

lemma algebraic_mat_addrow:
  assumes A: "A \<in> carrier_mat nr nc"
  assumes kl: "k < nr" "l < nr"
  assumes alga: "algebraic a"
  assumes algA: "algebraic_mat A"
  shows "algebraic_mat (addrow a k l A)"
  unfolding algebraic_mat_def
proof (intro allI impI)
  fix r c
  assume "r < dim_row (addrow a k l A)" "c < dim_col (addrow a k l A)"
  then have "r < nr" "c < nc"
       and "addrow a k l A $$ (r,c) = (if k = r then a * A $$ (l,c) + A $$ (r,c) else A $$ (r,c))"
    using A kl by simp_all
  then show "algebraic (addrow a k l A $$ (r, c))"
    using algA kl alga
    by (metis algebraic_matD algebraic_plus algebraic_times A carrier_matD)
qed

lemma algebraic_mat_eliminate_entries:
  assumes A: "A \<in> carrier_mat nr nc"
  assumes B: "B \<in> carrier_mat nr nc'"
  assumes IJ: "I < nr" "J < nc"
  assumes algA: "algebraic_mat A"
  assumes algB: "algebraic_mat B"
  shows "algebraic_mat (eliminate_entries (\<lambda>i. A $$ (i, J)) B I J)"
  unfolding algebraic_mat_def
proof (intro allI impI)
  fix r c
  assume \<section>: "r < dim_row (eliminate_entries (\<lambda>i. A $$ (i, J)) B I J)"
            "c < dim_col (eliminate_entries (\<lambda>i. A $$ (i, J)) B I J)"
  then have *: "r < nr" "c < nc'"
    using B by simp_all
  have "algebraic (A $$ (r, J))"
    using A IJ(2) algebraic_matD assms(5) * by blast
  moreover have "algebraic (B $$ (I, c))"
    using B IJ(1) algebraic_matD assms(6) * by blast
  moreover have "algebraic (B $$ (r, c))"
    using B algebraic_matD assms(6) * by blast
  ultimately
  show "algebraic (eliminate_entries (\<lambda>i. A $$ (i, J)) B I J $$ (r, c))"
    using \<section> by auto
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
        have "algebraic_mat (fst (gauss_jordan_main A B i (Suc j)))"
          by (rule IH0(1)[OF refl refl True refl zero Nil algA])
        then show ?thesis
          unfolding gauss_jordan_main.simps[of A B i j] Let_def
          using True zero by (simp add: local.Nil)
      next
        case (Cons i' rest)
        then have is_eq: "?is = i' # rest"
          by simp
        have i'_in: "i' \<in> set ?is"
          using is_eq by auto
        have algS: "algebraic_mat (swaprows i i' A)"
          by (rule algebraic_mat_swaprows) (use algA ij i'_in in auto)
        have "algebraic_mat (fst (gauss_jordan_main (swaprows i i' A) (swaprows i i' B) i j))"
          by (rule IH0(2)[OF refl refl True refl zero is_eq algS])
        then show ?thesis
          unfolding gauss_jordan_main.simps[of A B i j] Let_def
          using True zero is_eq by simp
      qed
    next
      case nonzero: False
      show ?thesis
      proof (cases "A $$ (i, j) = 1")
        case one: True
        let ?v = "\<lambda>k. A $$ (k, j)"
        have algE: "algebraic_mat (eliminate_entries ?v A i j)"
          by (rule algebraic_mat_eliminate_entries) (use algA ij in auto)
        have "algebraic_mat
            (fst (gauss_jordan_main (eliminate_entries ?v A i j) (eliminate_entries ?v B i j)
              (Suc i) (Suc j)))"
          using IH0(3) True algE one nonzero by metis
        then show ?thesis
          unfolding gauss_jordan_main.simps[of A B i j] Let_def
          using True nonzero one by simp
      next
        case not_one: False
        let ?a = "inverse (A $$ (i, j))"
        have algInv: "algebraic ?a"
          by (blast intro: algebraic_matD[OF algA ij])
        have algM: "algebraic_mat (multrow i ?a A)"
          using ij algInv algA by (intro algebraic_mat_multrow) auto
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
  from A have dim: "dim_row A = nr" "dim_col A = nc"
    by auto
  from row[unfolded row_echelon_form_def] obtain p where pivot: "pivot_fun A p nc"
    using dim by auto
  note piv = pivot_positions[OF A pivot]
  have pivot_cols_subset: "snd ` set (pivot_positions A) \<subseteq> {0..<nc}"
  proof
    fix j
    assume j: "j \<in> snd ` set (pivot_positions A)"
    with piv obtain i k where ij: "(i, j) \<in> set (pivot_positions A)"
      and k: "k < nr" "p k \<noteq> nc" "j = p k"
      by auto
    with k show "j \<in> {0..<nc}"
      using pivot k(1) dim(1) by (auto simp: pivot_fun_def Let_def)  
  qed
  define cands where "cands \<equiv> filter (\<lambda>j. j \<notin> snd ` set (pivot_positions A)) [0..<nc]"
  have "set cands \<noteq> {}"
    using neq pivot_cols_subset unfolding cands_def by auto
  then obtain c cs where cands: "cands = c # cs" and c: "c \<in> set cands"
    by (cases cands) auto
  hence fv: "find_base_vector A = non_pivot_base A (pivot_positions A) c"
    unfolding find_base_vector_def Let_def cands_def dim by auto
  have c_lt: "c < nc"
    using c by (auto simp: cands_def)
  show ?thesis
    unfolding algebraic_vec_def
  proof (intro strip)
    fix i
    assume "i < dim_vec (find_base_vector A)"
    then have "i < nc"
      using find_base_vector[OF row A neq] by simp
    then have idx:
        "find_base_vector A $ i =
          (if i = c then 1 else
            (case map_of (map prod.swap (pivot_positions A)) i of
              Some j => - A $$ (j, c) | None => 0))"
      unfolding fv non_pivot_base_def Let_def by (simp add: dim(2))
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
        with False Some idx show ?thesis
          using piv(1) algebraic_mat_def assms(4) c_lt dim by auto
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
  obtain piv where piv: "pivot_fun (gauss_jordan_single A) piv q"
    using rowC C unfolding row_echelon_form_def by auto
  note pp = pivot_positions[OF C piv]
  have len_pp_le: "length (pivot_positions (gauss_jordan_single A)) \<le> p"
  proof -
    have subset:
      "{i. i < p \<and> Matrix.row (gauss_jordan_single A) i \<noteq> 0\<^sub>v q} \<subseteq> {0..<p}"
      by auto
    then have "card {i. i < p \<and> Matrix.row (gauss_jordan_single A) i \<noteq> 0\<^sub>v q} \<le> card {0..<p}"  
      by (intro card_mono) auto
    then show ?thesis
      using pp(4) by simp
  qed
  have card_pp: "card (snd ` set (pivot_positions (gauss_jordan_single A))) =
      length (pivot_positions (gauss_jordan_single A))"
    using distinct_card pp(3) by fastforce
  have neq: "snd ` set (pivot_positions (gauss_jordan_single A)) \<noteq> {0..<q}"
  proof
    assume eqp: "snd ` set (pivot_positions (gauss_jordan_single A)) = {0..<q}"
    then have "q = length (pivot_positions (gauss_jordan_single A))"
      by (simp flip: card_pp)
    then show False
      using len_pp_le hpq by simp
  qed
  from find_base_vector[OF rowC C neq]
  have v: "find_base_vector (gauss_jordan_single A) \<in> carrier_vec q"
    "find_base_vector (gauss_jordan_single A) \<noteq> 0\<^sub>v q"
    "gauss_jordan_single A *\<^sub>v find_base_vector (gauss_jordan_single A) = 0\<^sub>v p"
    by auto
  have algC: "algebraic_mat (gauss_jordan_single A)"
    by (rule gauss_jordan_single_algebraic[OF A algA])
  have algv: "algebraic_vec (find_base_vector (gauss_jordan_single A))"
    by (rule find_base_vector_algebraic[OF rowC C neq algC])
  have ker_eq: "mat_kernel (gauss_jordan_single A) = mat_kernel A"
    unfolding C_eq by (rule mat_kernel_mult_eq[OF A P Q QP])
  with mat_kernelI[OF C v(1) v(3)] 
  have "find_base_vector (gauss_jordan_single A) \<in> mat_kernel A"
    by metis
  with A show ?thesis
    using v(1-2) algv by (metis mat_kernelD(2))
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
  define c :: int where "c \<equiv> (\<Prod>i<q. gs_c0 (v $ i))"
  have c_nz: "c \<noteq> 0"
  proof
    assume c0: "c = 0"
    then obtain i where  "i < q" "gs_c0 (v $ i) = 0"
      using c0 unfolding c_def by (auto simp: prod_zero_iff)
    with algebraic_vecD v gs_c0_nonzero show False by (metis carrier_vecD)
  qed
  define w where "w \<equiv> of_int c \<cdot>\<^sub>v v"
  have w: "w \<in> carrier_vec q" and Aw0: "A *\<^sub>v w = 0\<^sub>v p"
    using Matrix.mult_mat_vec[OF A] v A by (auto simp: w_def mat_kernel_def)
  obtain j where j: "j < q" "v $ j \<noteq> 0"
    using v by force
  have w_nz: "w \<noteq> 0\<^sub>v q"
  proof
    assume "w = 0\<^sub>v q"
    then have "of_int c * (v $ j) = 0"
      unfolding w_def using j v(1)
      by (metis index_smult_vec index_zero_vec)
    with j c_nz show False
      by fastforce
  qed
  have wint: "algebraic_int (w $ i)" if i: "i < q" for i
  proof -
    have ai0: "algebraic_int (of_int (gs_c0 (v $ i)) * (v $ i))"
      using algebraic_vecD carrier_vecD gs_c0_algebraic_int i v by blast
    have "of_int (\<Prod>k\<in>{..<q} - {i}. gs_c0 (v $ k)) * (of_int (gs_c0 (v $ i)) * (v $ i)) =
          of_int c * (v $ i)"
      unfolding c_def using i by (simp add: algebra_simps prod.remove)
    then have ai2: "algebraic_int (of_int c * (v $ i))"
      using algebraic_int_of_int_scale[OF ai0] i c_def by metis
    show "algebraic_int (w $ i)"
      unfolding w_def using i v(1) ai2 by (simp add: Matrix.index_smult_vec)
  qed
  show ?thesis
    using w w_nz Aw0 wint by blast
qed

end
