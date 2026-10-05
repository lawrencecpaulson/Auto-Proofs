(*  Title:      Integer_Kernels/Integer_Kernel_Bounds.thy
    Author:     OpenAI Codex

Quantitative nonzero integer kernel vectors for underdetermined matrices.
Uses Jordan_Normal_Form and Linear_Inequalities from the AFP.
*)

theory Integer_Kernel_Bounds
  imports
    "Jordan_Normal_Form.Determinant"
    "Linear_Inequalities.Mixed_Integer_Solutions"
begin

section \<open>Bounded integer kernels\<close>

lemma det_zero_of_zero_row:
  fixes A :: "'a :: comm_ring_1 mat"
  assumes A: "A \<in> carrier_mat n n"
  assumes k: "k < n"
  assumes row0: "row A k = 0\<^sub>v n"
  shows "det A = 0"
proof -
  have rows: "(\<lambda>i. row A i) \<in> {0..<n} \<rightarrow> carrier_vec n"
    using A by auto
  have eqA: "A = mat\<^sub>r n n (\<lambda>i. if i = k then 0\<^sub>v n else row A i)"
    by (rule eq_rowI) (use A k row0 in auto)
  show ?thesis
    using eqA det_row_0[OF k rows] by presburger
qed

lemma exists_nonzero_int_kernel_vec_rectangular:
  fixes A :: "int mat"
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
    by (rule det_zero_of_zero_row[OF B hpq row0])
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

lemma le_zero_and_neg_le_zero_imp_zero:
  fixes v :: "int vec"
  assumes v: "v \<in> carrier_vec n"
  assumes le0: "v \<le> 0\<^sub>v n"
  assumes neg_le0: "- v \<le> 0\<^sub>v n"
  shows "v = 0\<^sub>v n"
proof (rule eq_vecI)
  show "dim_vec v = dim_vec (0\<^sub>v n)"
    using v by auto
next
  fix i
  assume i: "i < dim_vec (0\<^sub>v n)"
  then have i': "i < n"
    by simp
  have vi_le: "v $ i \<le> 0"
    using le0 i' by (simp add: less_eq_vec_def)
  have neg_vi_le': "- (v $ i) \<le> 0"
    using neg_le0 i' by (auto simp: less_eq_vec_def)
  have ge0: "0 \<le> v $ i"
    using neg_vi_le' by linarith
  have eq0: "v $ i = 0"
    using vi_le ge0 by (meson order_antisym)
  show "v $ i = (0\<^sub>v n) $ i"
    using eq0 i' by simp
qed

lemma inj_on_vec_of_list_fixed_length:
  "inj_on (vec_of_list :: 'a list \<Rightarrow> 'a vec) {xs. length xs = n}"
proof (rule inj_onI)
  fix xs ys :: "'a list"
  assume xs: "xs \<in> {xs. length xs = n}"
  assume ys: "ys \<in> {xs. length xs = n}"
  assume eq: "vec_of_list xs = vec_of_list ys"
  then have len: "length xs = length ys"
    using xs ys by simp
  show "xs = ys"
  proof (rule nth_equalityI)
    show "length xs = length ys"
      by (rule len)
  next
    fix i
    assume i: "i < length xs"
    then have iy: "i < length ys"
      using len by simp
    have "xs ! i = (vec_of_list xs :: 'a vec) $ i"
      using i by (simp add: vec_of_list_index)
    also have "\<dots> = (vec_of_list ys :: 'a vec) $ i"
      using eq by simp
    also have "\<dots> = ys ! i"
      using iy by (simp add: vec_of_list_index)
    finally show "xs ! i = ys ! i" .
  qed
qed

theorem exists_ne_zero_int_vec_bounded_kernel:
  fixes A :: "int mat"
  assumes A: "A \<in> carrier_mat p q"
  assumes hpq: "p < q"
  assumes ABnd: "A \<in> Bounded_mat Bnd"
  shows "\<exists>x. x \<in> carrier_vec q \<and> x \<noteq> 0\<^sub>v q \<and> A *\<^sub>v x = 0\<^sub>v p \<and>
    x \<in> Bounded_vec (int (q + 1) * det_bound_hadamard q (max 1 Bnd))"
proof -
  from exists_nonzero_int_kernel_vec_rectangular[OF A hpq]
  obtain w where w: "w \<in> carrier_vec q" "w \<noteq> 0\<^sub>v q" "A *\<^sub>v w = 0\<^sub>v p"
    by blast
  then obtain i where i: "i < q" "w $ i \<noteq> 0"
    by force
  have ABnd': "A \<in> Bounded_mat (max 1 Bnd)"
  proof -
    have "Bounded_mat Bnd \<subseteq> Bounded_mat (max 1 Bnd)"
      by (rule Bounded_mat_mono) simp
    with ABnd show ?thesis
      by blast
  qed
  have negA: "- A \<in> carrier_mat p q"
    using A by auto
  have A1Bnd: "A @\<^sub>r - A \<in> Bounded_mat (max 1 Bnd)"
    using A ABnd'
    by (auto simp: Bounded_mat_elements_mat elements_mat_append_rows)
  have b1Bnd: "(0\<^sub>v p @\<^sub>v 0\<^sub>v p :: int vec) \<in> Bounded_vec (max 1 Bnd)"
  proof -
    have "0 \<le> max 1 Bnd"
      by simp
    then show ?thesis
      by (auto simp: Bounded_vec_def)
  qed
  have A1: "A @\<^sub>r - A \<in> carrier_mat (p + p) q"
    using A negA by auto
  have b1: "(0\<^sub>v p @\<^sub>v 0\<^sub>v p :: int vec) \<in> carrier_vec (p + p)"
    by auto
  have sol_nonstrict:
      "(A @\<^sub>r - A) *\<^sub>v w \<le> (0\<^sub>v p @\<^sub>v 0\<^sub>v p :: int vec)"
  proof -
    have "(A @\<^sub>r - A) *\<^sub>v w = A *\<^sub>v w @\<^sub>v ((- A) *\<^sub>v w)"
      by (simp add: mat_mult_append[OF A negA w(1)])
    also have "\<dots> = (A *\<^sub>v w) @\<^sub>v (- (A *\<^sub>v w))"
      using A w(1) by simp
    also have "\<dots> = (0\<^sub>v p @\<^sub>v 0\<^sub>v p :: int vec)"
      using w(3) by simp
    finally show ?thesis
      by simp
  qed
  show ?thesis
  proof (cases "0 < w $ i")
    case True
    have A2: "mat_of_row (- unit_vec q i :: int vec) \<in> carrier_mat 1 q"
      using i by auto
    have A2Bnd: "mat_of_row (- unit_vec q i :: int vec) \<in> Bounded_mat (max 1 Bnd)"
      using i by (auto simp: Bounded_mat_def mat_of_row_def)
    have b2: "(0\<^sub>v 1 :: int vec) \<in> carrier_vec 1"
      by auto
    have b2Bnd: "(0\<^sub>v 1 :: int vec) \<in> Bounded_vec (max 1 Bnd)"
      by (simp add: Bounded_vec_def)
    have sol_strict:
        "mat_of_row (- unit_vec q i :: int vec) *\<^sub>v w <\<^sub>v (0\<^sub>v 1 :: int vec)"
    proof (rule less_vecI)
      show "mat_of_row (- unit_vec q i :: int vec) *\<^sub>v w \<in> carrier_vec 1"
        by (rule mult_mat_vec_carrier[OF A2 w(1)])
      show "0\<^sub>v 1 \<in> carrier_vec 1"
        by auto
      fix j :: nat
      assume j: "j < 1"
      have "j = (0::nat)"
        using j by simp
      moreover have "(mat_of_row (- unit_vec q i :: int vec) *\<^sub>v w) $ 0 = - (w $ i)"
        using i w by simp
      ultimately show "(mat_of_row (- unit_vec q i :: int vec) *\<^sub>v w) $ j < (0\<^sub>v 1 :: int vec) $ j"
        using True by simp
    qed
    have nondeg: "p + p \<noteq> 0 \<or> 1 \<noteq> 0 \<or> max 1 Bnd \<ge> 0"
      by (rule disjI2, rule disjI2, simp)
    obtain x where x:
        "x \<in> carrier_vec q"
        "(A @\<^sub>r - A) *\<^sub>v x \<le> (0\<^sub>v p @\<^sub>v 0\<^sub>v p :: int vec)"
        "mat_of_row (- unit_vec q i :: int vec) *\<^sub>v x <\<^sub>v (0\<^sub>v 1 :: int vec)"
        "x \<in> Bounded_vec (int (q + 1) * det_bound_hadamard q (max 1 Bnd))"
      using small_integer_solution[OF det_bound_hadamard A1 A2 b1 b2 A1Bnd b1Bnd A2Bnd b2Bnd
        w(1) sol_nonstrict sol_strict nondeg]
      by auto
    have Ax_le: "A *\<^sub>v x \<le> 0\<^sub>v p" and neg_Ax_le: "- A *\<^sub>v x \<le> 0\<^sub>v p"
      using x(1-2) A negA
      by (auto simp: append_rows_le)
    have Ax0: "A *\<^sub>v x = 0\<^sub>v p"
    proof (rule le_zero_and_neg_le_zero_imp_zero)
      show "A *\<^sub>v x \<in> carrier_vec p"
        using A x by auto
      show "A *\<^sub>v x \<le> 0\<^sub>v p"
        by fact
      show "- (A *\<^sub>v x) \<le> 0\<^sub>v p"
        using neg_Ax_le A x by simp
    qed
    have xi_neg: "(mat_of_row (- unit_vec q i :: int vec) *\<^sub>v x) $ 0 < 0"
      using less_vecD[OF x(3) b2, of 0] by simp
    then have xi_pos: "0 < x $ i"
      using i x by simp
    have x0: "x \<noteq> 0\<^sub>v q"
      using i xi_pos x(1) by force
    show ?thesis
      using x x0 Ax0 by blast
  next
    case False
    then have wi_neg: "w $ i < 0"
      using i by linarith
    have A2: "mat_of_row (unit_vec q i :: int vec) \<in> carrier_mat 1 q"
      using i by auto
    have A2Bnd: "mat_of_row (unit_vec q i :: int vec) \<in> Bounded_mat (max 1 Bnd)"
      using i by (auto simp: Bounded_mat_def mat_of_row_def)
    have b2: "(0\<^sub>v 1 :: int vec) \<in> carrier_vec 1"
      by auto
    have b2Bnd: "(0\<^sub>v 1 :: int vec) \<in> Bounded_vec (max 1 Bnd)"
      by (simp add: Bounded_vec_def)
    have sol_strict:
        "mat_of_row (unit_vec q i :: int vec) *\<^sub>v w <\<^sub>v (0\<^sub>v 1 :: int vec)"
    proof (rule less_vecI)
      show "mat_of_row (unit_vec q i :: int vec) *\<^sub>v w \<in> carrier_vec 1"
        by (rule mult_mat_vec_carrier[OF A2 w(1)])
      show "0\<^sub>v 1 \<in> carrier_vec 1"
        by auto
      fix j :: nat
      assume j: "j < 1"
      have "j = (0::nat)"
        using j by simp
      moreover have "(mat_of_row (unit_vec q i :: int vec) *\<^sub>v w) $ 0 = w $ i"
        using i w by simp
      ultimately show "(mat_of_row (unit_vec q i :: int vec) *\<^sub>v w) $ j < (0\<^sub>v 1 :: int vec) $ j"
        using wi_neg by simp
    qed
    have nondeg: "p + p \<noteq> 0 \<or> 1 \<noteq> 0 \<or> max 1 Bnd \<ge> 0"
      by (rule disjI2, rule disjI2, simp)
    obtain x where x:
        "x \<in> carrier_vec q"
        "(A @\<^sub>r - A) *\<^sub>v x \<le> (0\<^sub>v p @\<^sub>v 0\<^sub>v p :: int vec)"
        "mat_of_row (unit_vec q i :: int vec) *\<^sub>v x <\<^sub>v (0\<^sub>v 1 :: int vec)"
        "x \<in> Bounded_vec (int (q + 1) * det_bound_hadamard q (max 1 Bnd))"
      using small_integer_solution[OF det_bound_hadamard A1 A2 b1 b2 A1Bnd b1Bnd A2Bnd b2Bnd
        w(1) sol_nonstrict sol_strict nondeg]
      by auto
    have Ax_le: "A *\<^sub>v x \<le> 0\<^sub>v p" and neg_Ax_le: "- A *\<^sub>v x \<le> 0\<^sub>v p"
      using x(1-2) A negA
      by (auto simp: append_rows_le)
    have Ax0: "A *\<^sub>v x = 0\<^sub>v p"
    proof (rule le_zero_and_neg_le_zero_imp_zero)
      show "A *\<^sub>v x \<in> carrier_vec p"
        using A x by auto
      show "A *\<^sub>v x \<le> 0\<^sub>v p"
        by fact
      show "- (A *\<^sub>v x) \<le> 0\<^sub>v p"
        using neg_Ax_le A x by simp
    qed
    have xi_neg: "(mat_of_row (unit_vec q i :: int vec) *\<^sub>v x) $ 0 < 0"
      using less_vecD[OF x(3) b2, of 0] by simp
    have x0: "x \<noteq> 0\<^sub>v q"
      using i xi_neg x(1) by force
    show ?thesis
      using x x0 Ax0 by blast
  qed
qed

theorem exists_ne_zero_int_vec_bounded_kernel_linear:
  fixes A :: "int mat"
  assumes A: "A \<in> carrier_mat p q"
  assumes ppos: "0 < p"
  assumes hpq: "2 * p \<le> q"
  assumes ABnd: "A \<in> Bounded_mat Bnd"
  shows "\<exists>x. x \<in> carrier_vec q \<and> x \<noteq> 0\<^sub>v q \<and> A *\<^sub>v x = 0\<^sub>v p \<and>
    x \<in> Bounded_vec (2 * int q * max 1 Bnd)"
proof -
  define B where "B = nat (max 1 Bnd)"
  define C where "C = 2 * q * B"
  define M where "M = int q * int B * int C"

  let ?L = "{xs :: int list. set xs \<subseteq> {0..int C} \<and> length xs = q}"
  let ?S = "vec_of_list ` ?L"
  let ?K = "{ys :: int list. set ys \<subseteq> {-M..M} \<and> length ys = p}"
  let ?R = "vec_of_list ` ?K"
  let ?f = "\<lambda>x. A *\<^sub>v x"

  have B_int: "int B = max 1 Bnd"
    unfolding B_def by simp
  have B_pos: "0 < B"
    unfolding B_def by simp
  have qpos: "0 < q"
    using ppos hpq by linarith
  have C_pos: "0 < C"
    unfolding C_def using qpos B_pos by simp
  have M_nonneg: "0 \<le> M"
    unfolding M_def by simp
  have card_C_interval: "card {0..int C} = Suc C"
  proof -
    have "card {0..int C} = nat (int C - 0 + 1)"
      by simp
    also have "\<dots> = Suc C"
      by simp
    finally show ?thesis .
  qed

  have finL: "finite ?L"
    by (rule finite_lists_length_eq) simp
  have injL: "inj_on vec_of_list ?L"
  proof (rule inj_onI)
    fix xs ys
    assume xs: "xs \<in> ?L"
    assume ys: "ys \<in> ?L"
    assume eq: "vec_of_list xs = vec_of_list ys"
    show "xs = ys"
      by (rule inj_onD[OF inj_on_vec_of_list_fixed_length]) (use xs ys eq in auto)
  qed
  have cardL: "card ?L = Suc C ^ q"
    using card_C_interval by (simp add: card_lists_length_eq)
  have finS: "finite ?S"
    using finL by simp
  have cardS: "card ?S = Suc C ^ q"
    using cardL injL by (simp add: card_image)

  have M_twice: "2 * M + 1 = int (C ^ 2 + 1)"
    unfolding M_def C_def by (simp add: B_int algebra_simps power2_eq_square)
  have M_card: "card {-M..M} = Suc (C ^ 2)"
  proof -
    have "card {-M..M} = nat (2 * M + 1)"
      using M_nonneg by simp
    also have "\<dots> = nat (int (Suc (C ^ 2)))"
      using M_twice by simp
    also have "\<dots> = Suc (C ^ 2)"
    proof -
      have "nat (int (Suc (C ^ 2))) = nat (int 1 + int (C ^ 2))"
        by simp
      also have "\<dots> = 1 + C ^ 2"
        by (rule nat_int_add)
      finally show ?thesis
        by simp
    qed
    finally show ?thesis .
  qed
  have finK: "finite ?K"
    by (rule finite_lists_length_eq) simp
  have injK: "inj_on vec_of_list ?K"
  proof (rule inj_onI)
    fix xs ys
    assume xs: "xs \<in> ?K"
    assume ys: "ys \<in> ?K"
    assume eq: "vec_of_list xs = vec_of_list ys"
    show "xs = ys"
      by (rule inj_onD[OF inj_on_vec_of_list_fixed_length]) (use xs ys eq in auto)
  qed
  have cardK: "card ?K = Suc (C ^ 2) ^ p"
  proof -
    have "card ?K = card {-M..M} ^ p"
      by (simp add: card_lists_length_eq)
    also have "\<dots> = Suc (C ^ 2) ^ p"
      by (subst M_card) simp
    finally show ?thesis .
  qed
  have finR: "finite ?R"
    using finK by simp
  have cardR: "card ?R = Suc (C ^ 2) ^ p"
    using cardK injK by (simp add: card_image)

  have S_props:
    "x \<in> ?S \<Longrightarrow> x \<in> carrier_vec q \<and> (\<forall>j<q. 0 \<le> x $ j \<and> x $ j \<le> int C)" for x
  proof -
    assume xS: "x \<in> ?S"
    then obtain xs where xs: "xs \<in> ?L" and x_def: "x = vec_of_list xs"
      by blast
    have xs_len: "length xs = q"
      using xs by auto
    have x_carrier: "x \<in> carrier_vec q"
    proof -
      have "vec_of_list xs \<in> carrier_vec (length xs)"
        by simp
      then show ?thesis
        unfolding x_def using xs_len by simp
    qed
    have x_bounds: "\<forall>j<q. 0 \<le> x $ j \<and> x $ j \<le> int C"
    proof
      fix j
      show "j < q \<longrightarrow> 0 \<le> x $ j \<and> x $ j \<le> int C"
      proof
        assume jlt: "j < q"
        have xj: "x $ j = xs ! j"
          using xs jlt x_def by (simp add: vec_of_list_index)
        moreover have "xs ! j \<in> {0..int C}"
        proof -
          have "xs ! j \<in> set xs"
            using xs_len jlt by (simp add: nth_mem)
          moreover have "set xs \<subseteq> {0..int C}"
            using xs by auto
          ultimately show ?thesis
            by blast
        qed
        ultimately show "0 \<le> x $ j \<and> x $ j \<le> int C"
          by auto
      qed
    qed
    show ?thesis
      using x_carrier x_bounds by blast
  qed

  have image_sub: "?f ` ?S \<subseteq> ?R"
  proof
    fix y
    assume ymem: "y \<in> ?f ` ?S"
    then obtain x where xS: "x \<in> ?S" and y_def: "y = ?f x"
      by blast
    from S_props[OF xS] have x_carrier: "x \<in> carrier_vec q" and
      x_bounds: "\<forall>j<q. 0 \<le> x $ j \<and> x $ j \<le> int C"
      by blast+
    have y_carrier: "y \<in> carrier_vec p"
      unfolding y_def by (rule mult_mat_vec_carrier[OF A x_carrier])
    have y_bounds: "\<forall>u<p. y $ u \<in> {-M..M}"
    proof
      fix u
      show "u < p \<longrightarrow> y $ u \<in> {-M..M}"
      proof
        assume up: "u < p"
        have rowlt: "u < dim_row A"
          using A up by simp
        have y_expand: "y $ u = (\<Sum>j<q. A $$ (u,j) * x $ j)"
        proof -
          have "y $ u = row A u \<bullet> x"
            unfolding y_def by (rule index_mult_mat_vec[OF rowlt])
          also have "\<dots> = (\<Sum>i = 0..<q. row A u $ i * x $ i)"
            using x_carrier by (simp add: scalar_prod_def)
          also have "\<dots> = (\<Sum>j<q. A $$ (u,j) * x $ j)"
            using A up x_carrier by (simp add: atLeast0LessThan)
          finally show ?thesis .
        qed
        have A_bound: "abs (A $$ (u,j)) \<le> int B" if j: "j < q" for j
        proof -
          have "abs (A $$ (u,j)) \<le> Bnd"
            using ABnd A up j unfolding Bounded_mat_def by auto
          then show ?thesis
            by (simp add: B_int)
        qed
        have x_bound: "abs (x $ j) \<le> int C" if j: "j < q" for j
          using x_bounds[rule_format, OF j] by auto
        have "abs (y $ u) \<le> (\<Sum>j<q. abs (A $$ (u,j) * x $ j))"
          unfolding y_expand by (rule sum_abs)
        also have "\<dots> = (\<Sum>j<q. abs (A $$ (u,j)) * abs (x $ j))"
          by (simp add: abs_mult)
        also have "\<dots> \<le> (\<Sum>j<q. int B * int C)"
        proof (rule sum_mono)
          fix j
          assume j: "j \<in> {..<q}"
          have "abs (A $$ (u,j)) \<le> int B"
            by (rule A_bound) (use j in simp)
          moreover have "abs (x $ j) \<le> int C"
            by (rule x_bound) (use j in simp)
          ultimately show "abs (A $$ (u,j)) * abs (x $ j) \<le> int B * int C"
            by (intro mult_mono) auto
        qed
        also have "\<dots> = int q * int B * int C"
          by simp
        finally have abs_y: "abs (y $ u) \<le> M"
          unfolding M_def by simp
        then show "y $ u \<in> {-M..M}"
          by auto
      qed
    qed
    define ys where "ys = map (\<lambda>u. y $ u) [0..<p]"
    have ys_mem: "ys \<in> ?K"
      unfolding ys_def using y_bounds by auto
    have y_vec: "vec_of_list ys = y"
    proof (rule eq_vecI)
      show "dim_vec (vec_of_list ys) = dim_vec y"
        unfolding ys_def using y_carrier by simp
    next
      fix i
      assume i: "i < dim_vec y"
      then have ip: "i < p"
        using y_carrier by simp
      show "vec_of_list ys $ i = y $ i"
        unfolding ys_def using ip by (simp add: vec_of_list_index)
    qed
    show "y \<in> ?R"
      using ys_mem y_vec by blast
  qed

  have count_lt: "card (?f ` ?S) < card ?S"
  proof -
    have C_sq_lt: "Suc (C ^ 2) < Suc C ^ 2"
      using C_pos by (simp add: power2_eq_square)
    have "Suc (C ^ 2) ^ p < (Suc C ^ 2) ^ p"
      using C_sq_lt ppos by (intro power_strict_mono) auto
    also have "\<dots> = Suc C ^ (2 * p)"
      by (simp add: power_mult)
    also have "\<dots> \<le> Suc C ^ q"
      using hpq C_pos by (intro power_increasing) auto
    finally have cardR_lt: "card ?R < card ?S"
      using cardR cardS by simp
    have "card (?f ` ?S) \<le> card ?R"
      by (rule card_mono[OF finR image_sub])
    also have "\<dots> < card ?S"
      by (rule cardR_lt)
    finally show ?thesis .
  qed

  then have "\<not> inj_on ?f ?S"
    by (rule pigeonhole)
  then obtain x y where
      xS: "x \<in> ?S"
    and yS: "y \<in> ?S"
    and xy: "x \<noteq> y"
    and img_eq: "?f x = ?f y"
    unfolding inj_on_def by blast

  from S_props[OF xS] have x_carrier: "x \<in> carrier_vec q" and
    x_bounds: "\<forall>j<q. 0 \<le> x $ j \<and> x $ j \<le> int C"
    by blast+
  from S_props[OF yS] have y_carrier: "y \<in> carrier_vec q" and
    y_bounds: "\<forall>j<q. 0 \<le> y $ j \<and> y $ j \<le> int C"
    by blast+

  obtain i where i: "i < q" "x $ i \<noteq> y $ i"
    using x_carrier y_carrier xy by force
  define z where "z = x - y"
  have z_carrier: "z \<in> carrier_vec q"
    unfolding z_def using x_carrier y_carrier by auto
  have z_nz: "z \<noteq> 0\<^sub>v q"
  proof
    assume z0: "z = 0\<^sub>v q"
    have zi0: "z $ i = 0"
      using z0 i z_carrier by simp
    have xy0: "(x - y) $ i = 0"
      using zi0 unfolding z_def by simp
    have "x $ i - y $ i = 0"
      using xy0 i x_carrier y_carrier by simp
    then show False
      using i by simp
  qed
  have Ay_carrier: "A *\<^sub>v y \<in> carrier_vec p"
    by (rule mult_mat_vec_carrier[OF A y_carrier])
  have Az0: "A *\<^sub>v z = 0\<^sub>v p"
  proof -
    have "A *\<^sub>v z = A *\<^sub>v x - A *\<^sub>v y"
      unfolding z_def by (simp add: mult_minus_distrib_mat_vec[OF A x_carrier y_carrier])
    also have "\<dots> = A *\<^sub>v y - A *\<^sub>v y"
      using img_eq by simp
    also have "\<dots> = 0\<^sub>v p"
      using Ay_carrier by simp
    finally show ?thesis .
  qed
  have z_bnd: "z \<in> Bounded_vec (int C)"
  proof -
    have "\<forall>j<dim_vec z. abs (z $ j) \<le> int C"
    proof
      fix j
      show "j < dim_vec z \<longrightarrow> abs (z $ j) \<le> int C"
      proof
        assume jlt: "j < dim_vec z"
        then have jq: "j < q"
          using z_carrier by simp
        have xj0: "0 \<le> x $ j" and xjC: "x $ j \<le> int C"
          using x_bounds jq by blast+
        have yj0: "0 \<le> y $ j" and yjC: "y $ j \<le> int C"
          using y_bounds jq by blast+
        have zj: "z $ j = x $ j - y $ j"
          unfolding z_def using jq x_carrier y_carrier by simp
        have lo: "- int C \<le> z $ j"
          using zj xj0 yjC by linarith
        have hi: "z $ j \<le> int C"
          using zj xjC yj0 by linarith
        show "abs (z $ j) \<le> int C"
          using lo hi by linarith
      qed
    qed
    then show ?thesis
      unfolding Bounded_vec_def by simp
  qed
  have z_bnd': "z \<in> Bounded_vec (2 * int q * max 1 Bnd)"
    using z_bnd unfolding C_def by (simp add: B_int)

  show ?thesis
    using z_carrier z_nz Az0 z_bnd' by blast
qed

end
