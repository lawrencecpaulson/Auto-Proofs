(*  Title:      Baker/Gelfond_Schneider_Siegel.thy
    Author:     OpenAI Codex

AFP-backed Siegel-style kernel bounds for the standalone Gelfond-Schneider
port. The main result packages an underdetermined integer matrix into a
non-zero bounded integer kernel vector, matching the role played by Lean's
`Int.Matrix.exists_ne_zero_int_vec_norm_le'` in the Mathlib proof.
*)

theory Gelfond_Schneider_Siegel
  imports
    Gelfond_Schneider_Matrix
    "Jordan_Normal_Form.Determinant"
    "Linear_Inequalities.Mixed_Integer_Solutions"
begin

declare [[apply_timeout = 10]]

section \<open>Siegel-Type Integer Kernel Bounds\<close>

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

lemma vec_of_list_carrier [simp]:
  "vec_of_list xs \<in> carrier_vec (length xs)"
proof -
  have "dim_vec (vec_of_list xs) = length xs"
    by (rule dim_vec_of_list)
  then show ?thesis
    unfolding carrier_vec_def by simp
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

definition sg_pair_idx :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "sg_pair_idx d i j = i * d + j"

lemma sg_div_lt_of_lt_mult:
  fixes u m n :: nat
  assumes npos: "n > 0"
  assumes ult: "u < m * n"
  shows "u div n < m"
proof (rule ccontr)
  assume "\<not> u div n < m"
  then have m_le: "m \<le> u div n"
    by simp
  have mn_le: "m * n \<le> (u div n) * n"
    using m_le by simp
  also have "\<dots> \<le> u"
    using npos by (simp add: div_mult_mod_eq mult.commute)
  finally show False
    using ult by simp
qed

lemma sg_pair_idx_lt:
  assumes dpos: "d > 0"
  assumes i: "i < q"
  assumes j: "j < d"
  shows "sg_pair_idx d i j < q * d"
proof -
  have h1: "sg_pair_idx d i j < Suc i * d"
    unfolding sg_pair_idx_def using j by simp
  have "Suc i \<le> q"
    using i by simp
  then have h2: "Suc i * d \<le> q * d"
  proof (rule mult_right_mono)
    show "0 \<le> d"
      using dpos by simp
  qed
  from h1 h2 show ?thesis
    by (rule less_le_trans)
qed

lemma sum_upto_sg_pair_idx:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> 'a::{comm_monoid_add}"
  assumes dpos: "d > 0"
  shows "(\<Sum>n<q * d. f (n div d) (n mod d)) = (\<Sum>t<q. \<Sum>j<d. f t j)"
proof -
  let ?S = "({..<q} :: nat set) \<times> ({..<d} :: nat set)"
  let ?T = "{..<q * d}"
  let ?h = "case_prod (sg_pair_idx d)"
  have bij: "bij_betw ?h ?S ?T"
  proof (rule bij_betw_byWitness[where f' = "\<lambda>n::nat. (n div d, n mod d)"])
    show "\<forall>a\<in>?S. (\<lambda>n::nat. (n div d, n mod d)) (?h a) = a"
      using dpos by (auto simp: sg_pair_idx_def)
  next
    show "\<forall>n\<in>?T. ?h ((\<lambda>n::nat. (n div d, n mod d)) n) = n"
      using dpos by (auto simp: sg_pair_idx_def)
  next
    show "?h ` ?S \<subseteq> ?T"
      using dpos by (auto intro: sg_pair_idx_lt)
  next
    show "(\<lambda>n::nat. (n div d, n mod d)) ` ?T \<subseteq> ?S"
      using dpos by (auto intro: sg_div_lt_of_lt_mult)
  qed
  have "(\<Sum>t<q. \<Sum>j<d. f t j) = (\<Sum>ij\<in>?S. case_prod f ij)"
    by (simp add: sum.cartesian_product)
  also have "\<dots> = (\<Sum>ij\<in>?S. case_prod f (?h ij div d, ?h ij mod d))"
  proof (rule sum.cong[OF refl])
    fix a
    assume a: "a \<in> ?S"
    then obtain t j where a_def: "a = (t, j)" and j: "j < d"
      by auto
    show "case_prod f a = case_prod f (?h a div d, ?h a mod d)"
      unfolding a_def using dpos j by (simp add: sg_pair_idx_def)
  qed
  also have "\<dots> = (\<Sum>n\<in>?T. case_prod f (n div d, n mod d))"
    using bij by (rule sum.reindex_bij_betw)
  also have "\<dots> = (\<Sum>n<q * d. f (n div d) (n mod d))"

    by simp
  finally show ?thesis by simp
qed

theorem exists_nonzero_bounded_kernel_vec_of_structure_constants:
  fixes A :: "complex mat"
  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes A: "A \<in> carrier_mat p q"
  assumes dpos: "d > 0"
  assumes hpq: "p < q"
  assumes mult_repr:
    "\<And>u t j. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow>
      A $$ (u,t) * basis j = (\<Sum>k<d. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < p \<Longrightarrow> t < q \<Longrightarrow> k < d \<Longrightarrow> j < d \<Longrightarrow> abs (C u t k j) \<le> Bnd"
  assumes basis_indep:
    "\<And>c. (\<Sum>j<d. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<d. c j = 0)"
  obtains eta :: "complex vec" and x :: "int vec" where
      "eta \<in> carrier_vec q"
    and "eta \<noteq> 0\<^sub>v q"
    and "x \<in> carrier_vec (q * d)"
    and "x \<noteq> 0\<^sub>v (q * d)"
    and "A *\<^sub>v eta = 0\<^sub>v p"
    and "\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)"
    and "x \<in> Bounded_vec (int (q * d + 1) * det_bound_hadamard (q * d) (max 1 Bnd))"
proof -
  define M :: "int mat" where
    "M = mat (p * d) (q * d)
      (\<lambda>(uk,tj). C (uk div d) (tj div d) (uk mod d) (tj mod d))"
  have M: "M \<in> carrier_mat (p * d) (q * d)"
    unfolding M_def by simp
  have M_bnd: "M \<in> Bounded_mat Bnd"
    unfolding Bounded_mat_def M_def
    by (auto intro!: C_bnd sg_div_lt_of_lt_mult simp: dpos)
  have pdqd: "p * d < q * d"
    using hpq dpos by simp
  obtain x :: "int vec" where
      x_carrier: "x \<in> carrier_vec (q * d)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * d)"
    and Mx0: "M *\<^sub>v x = 0\<^sub>v (p * d)"
    and x_bnd: "x \<in> Bounded_vec (int (q * d + 1) * det_bound_hadamard (q * d) (max 1 Bnd))"
    using exists_ne_zero_int_vec_bounded_kernel[OF M pdqd M_bnd] by blast
  define eta :: "complex vec" where
    "eta = vec q (\<lambda>t. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)"
  have eta_carrier: "eta \<in> carrier_vec q"
    unfolding eta_def by simp
  have eta_coord: "eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)" if "t < q" for t
    using that x_carrier unfolding eta_def by simp
  have eta_nz: "eta \<noteq> 0\<^sub>v q"
  proof
    assume eta0: "eta = 0\<^sub>v q"
    have block_zero: "x $ sg_pair_idx d t j = 0" if t: "t < q" and j: "j < d" for t j
    proof -
      have "eta $ t = 0"
        using eta0 t eta_carrier by simp
      then have "(\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j) = 0"
        using eta_coord[OF t] by simp
      from basis_indep[OF this] j show ?thesis
        by blast
    qed
    obtain n where n: "n < q * d" "x $ n \<noteq> 0"
      using x_carrier x_nz by force
    have tlt: "n div d < q"
      by (rule sg_div_lt_of_lt_mult[OF dpos n(1)])
    have jlt: "n mod d < d"
      using dpos by simp
    have n_eq: "n = sg_pair_idx d (n div d) (n mod d)"
      unfolding sg_pair_idx_def using dpos by simp
    have "x $ sg_pair_idx d (n div d) (n mod d) = 0"
      by (rule block_zero[OF tlt jlt])
    then have "x $ n = 0"
      using n_eq by simp
    with n show False
      by simp
  qed
  have Aeta_component: "(A *\<^sub>v eta) $ u = 0" if up: "u < p" for u
  proof -
    have rowlt: "u < dim_row A"
      using A up by simp
    have row_zero: "(\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j)) = 0" if k: "k < d" for k
    proof -
      have uklt: "sg_pair_idx d u k < p * d"
        by (rule sg_pair_idx_lt[OF dpos up k])
      have ukrow: "sg_pair_idx d u k < dim_row M"
        using uklt M by simp
      have comp0: "(M *\<^sub>v x) $ sg_pair_idx d u k = 0"
        using Mx0 uklt by simp
      have comp1: "(M *\<^sub>v x) $ sg_pair_idx d u k = row M (sg_pair_idx d u k) \<bullet> x"
        by (rule index_mult_mat_vec[OF ukrow])
      have comp2: "row M (sg_pair_idx d u k) \<bullet> x =
          (\<Sum>n<q * d. M $$ (sg_pair_idx d u k, n) * x $ n)"
      proof -
        have "row M (sg_pair_idx d u k) \<bullet> x =
            (\<Sum>i = 0..<q * d. row M (sg_pair_idx d u k) $ i * x $ i)"
          using x_carrier by (simp add: scalar_prod_def)
        also have "\<dots> = (\<Sum>n<q * d. M $$ (sg_pair_idx d u k, n) * x $ n)"
          using uklt M x_carrier by (simp add: atLeast0LessThan)
        finally show ?thesis .
      qed
      have comp3: "(\<Sum>n<q * d. M $$ (sg_pair_idx d u k, n) * x $ n) =
          (\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ n)"
      proof (rule sum.cong[OF refl])
        fix n
        assume n_mem: "n \<in> {..<q * d}"
        have nlt: "n < q * d"
          using n_mem by simp
        have idx_div: "sg_pair_idx d u k div d = u"
          using dpos k by (simp add: sg_pair_idx_def)
        have idx_mod: "sg_pair_idx d u k mod d = k"
          using dpos k by (simp add: sg_pair_idx_def)
        have entry_eq: "M $$ (sg_pair_idx d u k, n) = C u (n div d) k (n mod d)"
          unfolding M_def using uklt nlt idx_div idx_mod by simp
        show "M $$ (sg_pair_idx d u k, n) * x $ n = C u (n div d) k (n mod d) * x $ n"
          using entry_eq by simp
      qed
      have comp4a: "(\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ n) =
          (\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ sg_pair_idx d (n div d) (n mod d))"
      proof (rule sum.cong[OF refl])
        fix n
        assume n_mem: "n \<in> {..<q * d}"
        have nlt: "n < q * d"
          using n_mem by simp
        have "n = sg_pair_idx d (n div d) (n mod d)"
          unfolding sg_pair_idx_def using dpos by simp
        then show "C u (n div d) k (n mod d) * x $ n = C u (n div d) k (n mod d) * x $ sg_pair_idx d (n div d) (n mod d)"
          by simp
      qed
      have comp4b: "(\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ sg_pair_idx d (n div d) (n mod d)) =
          (\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j))"
        by (rule sum_upto_sg_pair_idx[OF dpos])
      have "0 = (\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j))"
        using comp0 comp1 comp2 comp3 comp4a comp4b by simp
      then show ?thesis by simp
    qed
    have row_zero_complex:
      "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) = 0" if k: "k < d" for k
    proof -
      have "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) =
          of_int (\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j))"
        by simp
      also have "\<dots> = 0"
        using row_zero[OF k] by simp
      finally show ?thesis .
    qed
    have h1: "(A *\<^sub>v eta) $ u = (\<Sum>t<q. A $$ (u,t) * eta $ t)"
    proof -
      have "(A *\<^sub>v eta) $ u = row A u \<bullet> eta"
        by (rule index_mult_mat_vec[OF rowlt])
      also have "\<dots> = (\<Sum>i = 0..<dim_vec eta. row A u $ i * eta $ i)"
        by (simp add: scalar_prod_def)
      also have "\<dots> = (\<Sum>t<q. A $$ (u,t) * eta $ t)"
        using A eta_carrier up by (simp add: atLeast0LessThan)
      finally show ?thesis .
    qed
    have h2: "(\<Sum>t<q. A $$ (u,t) * eta $ t) =
        (\<Sum>t<q. A $$ (u,t) * (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j))"
      by (rule sum.cong[OF refl]) (simp add: eta_coord)
    have h3: "(\<Sum>t<q. A $$ (u,t) * (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)) =
        (\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j))"
      by (simp add: sum_distrib_left algebra_simps)
    have h4: "(\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j)) =
        (\<Sum>t<q. \<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
    proof (rule sum.cong[OF refl])
      fix t
      assume t_mem: "t \<in> {..<q}"
      have t: "t < q"
        using t_mem by simp
      show "(\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j)) =
          (\<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
      proof (rule sum.cong[OF refl])
        fix j
        assume j_mem: "j \<in> {..<d}"
        have j: "j < d"
          using j_mem by simp
        have "A $$ (u,t) * basis j = (\<Sum>k<d. of_int (C u t k j) * basis k)"
          by (rule mult_repr[OF up t j])
        then show "of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j) =
            (\<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
          by (simp add: sum_distrib_left algebra_simps)
      qed
    qed
    have h5a: "(\<Sum>t<q. \<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
        (\<Sum>t<q. \<Sum>k<d. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
    proof (rule sum.cong[OF refl])
      fix t
      assume "t \<in> {..<q}"
      show "(\<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
          (\<Sum>k<d. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
        by (rule sum.swap)
    qed
    have h5b: "(\<Sum>t<q. \<Sum>k<d. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
        (\<Sum>k<d. \<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
      by (rule sum.swap)
    have h5c: "(\<Sum>k<d. \<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
        (\<Sum>k<d. (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k)"
    proof (rule sum.cong[OF refl])
      fix k
      assume "k \<in> {..<d}"
      have h5c1: "(\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
          (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k)"
      proof (rule sum.cong[OF refl])
        fix t
        assume "t \<in> {..<q}"
        show "(\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
            (\<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k)"
        proof (rule sum.cong[OF refl])
          fix j
          assume "j \<in> {..<d}"
          have "of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k) =
              (of_int (x $ sg_pair_idx d t j) * of_int (C u t k j)) * basis k"
            by (simp add: mult.assoc)
          also have "... = of_int ((x $ sg_pair_idx d t j) * C u t k j) * basis k"
            by (simp only: of_int_mult[symmetric])
          also have "... = of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k"
            by simp
          finally show "of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k) =
              of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k" .
        qed
      qed
      have h5c2: "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k) =
          (\<Sum>t<q. (\<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k)"
        by (simp add: sum_distrib_right)
      have h5c3: "(\<Sum>t<q. (\<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k) =
          (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k"
        by (simp add: sum_distrib_right)
      from h5c1 h5c2 h5c3 show "(\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
          (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k"
        by simp
    qed
    have h6: "(\<Sum>k<d. (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k) = 0"
    proof -
      have "(\<Sum>k<d. (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k) =
          (\<Sum>k<d. 0 * basis k)"
      proof (rule sum.cong[OF refl])
        fix k
        assume k_mem: "k \<in> {..<d}"
        have k: "k < d"
          using k_mem by simp
        have coeff0: "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) = 0"
          using row_zero_complex[OF k] .
        show "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k = 0 * basis k"
          by (subst coeff0) simp
      qed
      then show ?thesis by simp
    qed
    have "(A *\<^sub>v eta) $ u = 0"
      using h1 h2 h3 h4 h5a h5b h5c h6 by simp
    then show ?thesis .
  qed
  have Aeta0: "A *\<^sub>v eta = 0\<^sub>v p"
  proof (rule eq_vecI)
    show "dim_vec (A *\<^sub>v eta) = dim_vec (0\<^sub>v p)"
      using A eta_carrier by simp
  next
    fix u
    assume u: "u < dim_vec (0\<^sub>v p)"
    then have up: "u < p"
      by simp
    show "(A *\<^sub>v eta) $ u = (0\<^sub>v p) $ u"
      using Aeta_component[OF up] u by simp
  qed
  show thesis
    by (rule that[OF eta_carrier eta_nz x_carrier x_nz Aeta0])
       (use eta_coord x_bnd in auto)
qed

theorem exists_nonzero_bounded_kernel_vec_of_structure_constants_linear:
  fixes A :: "complex mat"
  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes A: "A \<in> carrier_mat p q"
  assumes ppos: "p > 0"
  assumes dpos: "d > 0"
  assumes hpq: "2 * p \<le> q"
  assumes mult_repr:
    "\<And>u t j. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow>
      A $$ (u,t) * basis j = (\<Sum>k<d. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < p \<Longrightarrow> t < q \<Longrightarrow> k < d \<Longrightarrow> j < d \<Longrightarrow> abs (C u t k j) \<le> Bnd"
  assumes basis_indep:
    "\<And>c. (\<Sum>j<d. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<d. c j = 0)"
  obtains eta :: "complex vec" and x :: "int vec" where
      "eta \<in> carrier_vec q"
    and "eta \<noteq> 0\<^sub>v q"
    and "x \<in> carrier_vec (q * d)"
    and "x \<noteq> 0\<^sub>v (q * d)"
    and "A *\<^sub>v eta = 0\<^sub>v p"
    and "\<forall>t<q. eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)"
    and "x \<in> Bounded_vec (2 * int (q * d) * max 1 Bnd)"
proof -
  define M :: "int mat" where
    "M = mat (p * d) (q * d)
      (\<lambda>(uk,tj). C (uk div d) (tj div d) (uk mod d) (tj mod d))"
  have M: "M \<in> carrier_mat (p * d) (q * d)"
    unfolding M_def by simp
  have M_bnd: "M \<in> Bounded_mat Bnd"
    unfolding Bounded_mat_def M_def
    by (auto intro!: C_bnd sg_div_lt_of_lt_mult simp: dpos)
  have pd_pos: "p * d > 0"
    using ppos dpos by simp
  have pdqd: "2 * (p * d) \<le> q * d"
    using hpq dpos by simp
  obtain x :: "int vec" where
      x_carrier: "x \<in> carrier_vec (q * d)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * d)"
    and Mx0: "M *\<^sub>v x = 0\<^sub>v (p * d)"
    and x_bnd: "x \<in> Bounded_vec (2 * int (q * d) * max 1 Bnd)"
    using exists_ne_zero_int_vec_bounded_kernel_linear[OF M pd_pos pdqd M_bnd] by blast
  define eta :: "complex vec" where
    "eta = vec q (\<lambda>t. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)"
  have eta_carrier: "eta \<in> carrier_vec q"
    unfolding eta_def by simp
  have eta_coord: "eta $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)" if "t < q" for t
    using that x_carrier unfolding eta_def by simp
  have eta_nz: "eta \<noteq> 0\<^sub>v q"
  proof
    assume eta0: "eta = 0\<^sub>v q"
    have block_zero: "x $ sg_pair_idx d t j = 0" if t: "t < q" and j: "j < d" for t j
    proof -
      have "eta $ t = 0"
        using eta0 t eta_carrier by simp
      then have "(\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j) = 0"
        using eta_coord[OF t] by simp
      from basis_indep[OF this] j show ?thesis
        by blast
    qed
    obtain n where n: "n < q * d" "x $ n \<noteq> 0"
      using x_carrier x_nz by force
    have tlt: "n div d < q"
      by (rule sg_div_lt_of_lt_mult[OF dpos n(1)])
    have jlt: "n mod d < d"
      using dpos by simp
    have n_eq: "n = sg_pair_idx d (n div d) (n mod d)"
      unfolding sg_pair_idx_def using dpos by simp
    have "x $ sg_pair_idx d (n div d) (n mod d) = 0"
      by (rule block_zero[OF tlt jlt])
    then have "x $ n = 0"
      using n_eq by simp
    with n show False
      by simp
  qed
  have Aeta_component: "(A *\<^sub>v eta) $ u = 0" if up: "u < p" for u
  proof -
    have rowlt: "u < dim_row A"
      using A up by simp
    have row_zero: "(\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j)) = 0" if k: "k < d" for k
    proof -
      have uklt: "sg_pair_idx d u k < p * d"
        by (rule sg_pair_idx_lt[OF dpos up k])
      have ukrow: "sg_pair_idx d u k < dim_row M"
        using uklt M by simp
      have comp0: "(M *\<^sub>v x) $ sg_pair_idx d u k = 0"
        using Mx0 uklt by simp
      have comp1: "(M *\<^sub>v x) $ sg_pair_idx d u k = row M (sg_pair_idx d u k) \<bullet> x"
        by (rule index_mult_mat_vec[OF ukrow])
      have comp2: "row M (sg_pair_idx d u k) \<bullet> x =
          (\<Sum>n<q * d. M $$ (sg_pair_idx d u k, n) * x $ n)"
      proof -
        have "row M (sg_pair_idx d u k) \<bullet> x =
            (\<Sum>i = 0..<q * d. row M (sg_pair_idx d u k) $ i * x $ i)"
          using x_carrier by (simp add: scalar_prod_def)
        also have "\<dots> = (\<Sum>n<q * d. M $$ (sg_pair_idx d u k, n) * x $ n)"
          using uklt M x_carrier by (simp add: atLeast0LessThan)
        finally show ?thesis .
      qed
      have comp3: "(\<Sum>n<q * d. M $$ (sg_pair_idx d u k, n) * x $ n) =
          (\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ n)"
      proof (rule sum.cong[OF refl])
        fix n
        assume n_mem: "n \<in> {..<q * d}"
        have nlt: "n < q * d"
          using n_mem by simp
        have idx_div: "sg_pair_idx d u k div d = u"
          using dpos k by (simp add: sg_pair_idx_def)
        have idx_mod: "sg_pair_idx d u k mod d = k"
          using dpos k by (simp add: sg_pair_idx_def)
        have entry_eq: "M $$ (sg_pair_idx d u k, n) = C u (n div d) k (n mod d)"
          unfolding M_def using uklt nlt idx_div idx_mod by simp
        show "M $$ (sg_pair_idx d u k, n) * x $ n = C u (n div d) k (n mod d) * x $ n"
          using entry_eq by simp
      qed
      have comp4a: "(\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ n) =
          (\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ sg_pair_idx d (n div d) (n mod d))"
      proof (rule sum.cong[OF refl])
        fix n
        assume n_mem: "n \<in> {..<q * d}"
        have nlt: "n < q * d"
          using n_mem by simp
        have "n = sg_pair_idx d (n div d) (n mod d)"
          unfolding sg_pair_idx_def using dpos by simp
        then show "C u (n div d) k (n mod d) * x $ n = C u (n div d) k (n mod d) * x $ sg_pair_idx d (n div d) (n mod d)"
          by simp
      qed
      have comp4b: "(\<Sum>n<q * d. C u (n div d) k (n mod d) * x $ sg_pair_idx d (n div d) (n mod d)) =
          (\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j))"
        by (rule sum_upto_sg_pair_idx[OF dpos])
      have "0 = (\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j))"
        using comp0 comp1 comp2 comp3 comp4a comp4b by simp
      then show ?thesis by simp
    qed
    have row_zero_complex:
      "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) = 0" if k: "k < d" for k
    proof -
      have "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) =
          of_int (\<Sum>t<q. \<Sum>j<d. C u t k j * (x $ sg_pair_idx d t j))"
        by simp
      also have "\<dots> = 0"
        using row_zero[OF k] by simp
      finally show ?thesis .
    qed
    have h1: "(A *\<^sub>v eta) $ u = (\<Sum>t<q. A $$ (u,t) * eta $ t)"
    proof -
      have "(A *\<^sub>v eta) $ u = row A u \<bullet> eta"
        by (rule index_mult_mat_vec[OF rowlt])
      also have "\<dots> = (\<Sum>i = 0..<dim_vec eta. row A u $ i * eta $ i)"
        by (simp add: scalar_prod_def)
      also have "\<dots> = (\<Sum>t<q. A $$ (u,t) * eta $ t)"
        using A eta_carrier up by (simp add: atLeast0LessThan)
      finally show ?thesis .
    qed
    have h2: "(\<Sum>t<q. A $$ (u,t) * eta $ t) =
        (\<Sum>t<q. A $$ (u,t) * (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j))"
      by (rule sum.cong[OF refl]) (simp add: eta_coord)
    have h3: "(\<Sum>t<q. A $$ (u,t) * (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)) =
        (\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j))"
      by (simp add: sum_distrib_left algebra_simps)
    have h4: "(\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j)) =
        (\<Sum>t<q. \<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
    proof (rule sum.cong[OF refl])
      fix t
      assume t_mem: "t \<in> {..<q}"
      have t: "t < q"
        using t_mem by simp
      show "(\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j)) =
          (\<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
      proof (rule sum.cong[OF refl])
        fix j
        assume j_mem: "j \<in> {..<d}"
        have j: "j < d"
          using j_mem by simp
        have "A $$ (u,t) * basis j = (\<Sum>k<d. of_int (C u t k j) * basis k)"
          by (rule mult_repr[OF up t j])
        then show "of_int (x $ sg_pair_idx d t j) * (A $$ (u,t) * basis j) =
            (\<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
          by (simp add: sum_distrib_left algebra_simps)
      qed
    qed
    have h5a: "(\<Sum>t<q. \<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
        (\<Sum>t<q. \<Sum>k<d. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
    proof (rule sum.cong[OF refl])
      fix t
      assume "t \<in> {..<q}"
      show "(\<Sum>j<d. \<Sum>k<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
          (\<Sum>k<d. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
        by (rule sum.swap)
    qed
    have h5b: "(\<Sum>t<q. \<Sum>k<d. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
        (\<Sum>k<d. \<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k))"
      by (rule sum.swap)
    have h5c: "(\<Sum>k<d. \<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
        (\<Sum>k<d. (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k)"
    proof (rule sum.cong[OF refl])
      fix k
      assume "k \<in> {..<d}"
      have h5c1: "(\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
          (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k)"
      proof (rule sum.cong[OF refl])
        fix t
        assume "t \<in> {..<q}"
        show "(\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
            (\<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k)"
        proof (rule sum.cong[OF refl])
          fix j
          assume "j \<in> {..<d}"
          have "of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k) =
              (of_int (x $ sg_pair_idx d t j) * of_int (C u t k j)) * basis k"
            by (simp add: mult.assoc)
          also have "... = of_int ((x $ sg_pair_idx d t j) * C u t k j) * basis k"
            by (simp only: of_int_mult[symmetric])
          also have "... = of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k"
            by simp
          finally show "of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k) =
              of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k" .
        qed
      qed
      have h5c2: "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j)) * basis k) =
          (\<Sum>t<q. (\<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k)"
        by (simp add: sum_distrib_right)
      have h5c3: "(\<Sum>t<q. (\<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k) =
          (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k"
        by (simp add: sum_distrib_right)
      from h5c1 h5c2 h5c3 show "(\<Sum>t<q. \<Sum>j<d. of_int (x $ sg_pair_idx d t j) * (of_int (C u t k j) * basis k)) =
          (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k"
        by simp
    qed
    have h6: "(\<Sum>k<d. (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k) = 0"
    proof -
      have "(\<Sum>k<d. (\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k) =
          (\<Sum>k<d. 0 * basis k)"
      proof (rule sum.cong[OF refl])
        fix k
        assume k_mem: "k \<in> {..<d}"
        have k: "k < d"
          using k_mem by simp
        have coeff0: "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) = 0"
          using row_zero_complex[OF k] .
        show "(\<Sum>t<q. \<Sum>j<d. of_int (C u t k j * (x $ sg_pair_idx d t j))) * basis k = 0 * basis k"
          by (subst coeff0) simp
      qed
      then show ?thesis by simp
    qed
    have "(A *\<^sub>v eta) $ u = 0"
      using h1 h2 h3 h4 h5a h5b h5c h6 by simp
    then show ?thesis .
  qed
  have Aeta0: "A *\<^sub>v eta = 0\<^sub>v p"
  proof (rule eq_vecI)
    show "dim_vec (A *\<^sub>v eta) = dim_vec (0\<^sub>v p)"
      using A eta_carrier by simp
  next
    fix u
    assume u: "u < dim_vec (0\<^sub>v p)"
    then have up: "u < p"
      by simp
    show "(A *\<^sub>v eta) $ u = (0\<^sub>v p) $ u"
      using Aeta_component[OF up] u by simp
  qed
  show thesis
    by (rule that[OF eta_carrier eta_nz x_carrier x_nz Aeta0])
       (use eta_coord x_bnd in auto)
qed

theorem gs_system_mat_exists_bounded_algebraic_int_kernel:

  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes dpos: "D > 0"
  assumes mnq: "m * n < q * q"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j)"
  assumes basis_indep: "\<And>c. (\<Sum>j<D. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes mult_repr:
    "\<And>u t j. u < m * n \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow>
      gs_system_mat d m n q $$ (u,t) * basis j = (\<Sum>k<D. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < m * n \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow> abs (C u t k j) \<le> Bnd"
  obtains v :: "complex vec" and x :: "int vec" where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_system_mat d m n q *\<^sub>v v = 0\<^sub>v (m * n)"
    and "\<forall>i<q * q. algebraic_int (v $ i)"
    and "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and "x \<in> carrier_vec (q * q * D)"
    and "x \<noteq> 0\<^sub>v (q * q * D)"
    and "x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd))"
proof -
  obtain v :: "complex vec" and x :: "int vec" where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and ker: "gs_system_mat d m n q *\<^sub>v v = 0\<^sub>v (m * n)"
    and repr: "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and x_bnd: "x \<in> Bounded_vec (int (q * q * D + 1) * det_bound_hadamard (q * q * D) (max 1 Bnd))"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants[OF gs_system_mat_carrier dpos mnq mult_repr C_bnd basis_indep])
  have vint: "\<forall>i<q * q. algebraic_int (v $ i)"
  proof
    fix i
    show "i < q * q \<longrightarrow> algebraic_int (v $ i)"
    proof
      assume i: "i < q * q"
      have sum_int: "algebraic_int (\<Sum>j<D. of_int (x $ sg_pair_idx D i j) * basis j)"
      proof (rule algebraic_int_sum)
        fix j
        assume j: "j \<in> {..<D}"
        have "algebraic_int (of_int (x $ sg_pair_idx D i j))"
          by simp
        moreover have "algebraic_int (basis j)"
          using basis_int j by simp
        ultimately show "algebraic_int (of_int (x $ sg_pair_idx D i j) * basis j)"
          by (rule algebraic_int_times)
      qed
      show "algebraic_int (v $ i)"
        using repr i sum_int by simp
    qed
  qed
  show thesis
    by (rule that[OF v_carrier v_nz ker vint repr x_carrier x_nz x_bnd])
qed

theorem gs_system_mat_exists_bounded_algebraic_int_kernel_linear:

  fixes basis :: "nat \<Rightarrow> complex"
  fixes C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes dpos: "D > 0"
  assumes mnpos: "m * n > 0"
  assumes mnq: "2 * (m * n) \<le> q * q"
  assumes basis_int: "\<And>j. j < D \<Longrightarrow> algebraic_int (basis j)"
  assumes basis_indep: "\<And>c. (\<Sum>j<D. of_int (c j) * basis j) = 0 \<Longrightarrow> (\<forall>j<D. c j = 0)"
  assumes mult_repr:
    "\<And>u t j. u < m * n \<Longrightarrow> t < q * q \<Longrightarrow> j < D \<Longrightarrow>
      gs_system_mat d m n q $$ (u,t) * basis j = (\<Sum>k<D. of_int (C u t k j) * basis k)"
  assumes C_bnd:
    "\<And>u t k j. u < m * n \<Longrightarrow> t < q * q \<Longrightarrow> k < D \<Longrightarrow> j < D \<Longrightarrow> abs (C u t k j) \<le> Bnd"
  obtains v :: "complex vec" and x :: "int vec" where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_system_mat d m n q *\<^sub>v v = 0\<^sub>v (m * n)"
    and "\<forall>i<q * q. algebraic_int (v $ i)"
    and "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and "x \<in> carrier_vec (q * q * D)"
    and "x \<noteq> 0\<^sub>v (q * q * D)"
    and "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd)"
proof -
  obtain v :: "complex vec" and x :: "int vec" where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and ker: "gs_system_mat d m n q *\<^sub>v v = 0\<^sub>v (m * n)"
    and repr: "\<forall>t<q * q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * basis j)"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec (2 * int (q * q * D) * max 1 Bnd)"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants_linear[OF gs_system_mat_carrier mnpos dpos mnq mult_repr C_bnd basis_indep])
  have vint: "\<forall>i<q * q. algebraic_int (v $ i)"
  proof
    fix i
    show "i < q * q \<longrightarrow> algebraic_int (v $ i)"
    proof
      assume i: "i < q * q"
      have sum_int: "algebraic_int (\<Sum>j<D. of_int (x $ sg_pair_idx D i j) * basis j)"
      proof (rule algebraic_int_sum)
        fix j
        assume j: "j \<in> {..<D}"
        have "algebraic_int (of_int (x $ sg_pair_idx D i j))"
          by simp
        moreover have "algebraic_int (basis j)"
          using basis_int j by simp
        ultimately show "algebraic_int (of_int (x $ sg_pair_idx D i j) * basis j)"
          by (rule algebraic_int_times)
      qed
      show "algebraic_int (v $ i)"
        using repr i sum_int by simp
    qed
  qed
  show thesis
    by (rule that[OF v_carrier v_nz ker vint repr x_carrier x_nz x_bnd])
qed

end
