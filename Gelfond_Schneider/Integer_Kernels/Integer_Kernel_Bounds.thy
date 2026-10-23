(*  Title:      Gelfond_Schneider/Integer_Kernels/Integer_Kernel_Bounds.thy
    Author:     OpenAI Codex

Quantitative nonzero integer kernel vectors for underdetermined matrices.
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
  define B where "B \<equiv> A @\<^sub>r 0\<^sub>m (q - p) q"
  have B: "B \<in> carrier_mat q q"
    unfolding B_def using A
    by (metis add_diff_cancel_left' carrier_append_rows hpq less_imp_add_positive
        zero_carrier_mat)
  have row0: "row B p = 0\<^sub>v q"
    using A B hpq by (intro eq_vecI) (auto simp: B_def append_rows_def)
  have detB0: "det B = 0"
    by (rule det_zero_of_zero_row[OF B hpq row0])
  from det_0_iff_vec_prod_zero[OF B] detB0
  obtain x where x: "x \<in> carrier_vec q" "x \<noteq> 0\<^sub>v q" "B *\<^sub>v x = 0\<^sub>v q"
    by auto
  have Ax0: "A *\<^sub>v x = 0\<^sub>v p"
  proof -
    have "A *\<^sub>v x = vec_first (A *\<^sub>v x @\<^sub>v (0\<^sub>m (q - p) q *\<^sub>v x)) p"
      using A x by (force simp: vec_first_def)
    also have "\<dots> = vec_first (B *\<^sub>v x) p"
      unfolding B_def by (simp add: mat_mult_append[OF A zero_carrier_mat x(1)])
    also have "\<dots> = 0\<^sub>v p"
      using x(3) by (simp add: hpq order_less_imp_le)
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
  using assms by (intro eq_vecI; force simp add: less_eq_vec_def)

lemma inj_on_vec_of_list_fixed_length:
  "inj_on (vec_of_list :: 'a list \<Rightarrow> 'a vec) {xs. length xs = n}"
  by (meson inj_on_inverseI list_vec)

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
    using ABnd Bounded_mat_mono max.cobounded2 by blast
  have negA: "- A \<in> carrier_mat p q"
    using A by auto
  have A1Bnd: "A @\<^sub>r - A \<in> Bounded_mat (max 1 Bnd)"
    using A ABnd'
    by (auto simp: Bounded_mat_elements_mat elements_mat_append_rows)
  have b1Bnd: "(0\<^sub>v p @\<^sub>v 0\<^sub>v p :: int vec) \<in> Bounded_vec (max 1 Bnd)"
    by (auto simp: Bounded_vec_def)
  have A1: "A @\<^sub>r - A \<in> carrier_mat (p + p) q"
    using A negA by auto
  have b1: "(0\<^sub>v p @\<^sub>v 0\<^sub>v p :: int vec) \<in> carrier_vec (p + p)"
    by auto
  have sol_nonstrict: "(A @\<^sub>r - A) *\<^sub>v w \<le> (0\<^sub>v p @\<^sub>v 0\<^sub>v p :: int vec)"
    using w A by (simp add: mat_mult_append[OF A negA])
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
    have "mat_of_row (- unit_vec q i :: int vec) *\<^sub>v w <\<^sub>v (0\<^sub>v 1 :: int vec)"
      using less_vec_def True i(1) w(1) by fastforce
    then obtain x where x: "x \<in> carrier_vec q" "(A @\<^sub>r - A) *\<^sub>v x \<le> (0\<^sub>v p @\<^sub>v 0\<^sub>v p)" 
                "mat_of_row (- unit_vec q i) *\<^sub>v x <\<^sub>v (0\<^sub>v 1)"
                "x \<in> Bounded_vec (int (q + 1) * det_bound_hadamard q (max 1 Bnd))"
      using small_integer_solution[OF det_bound_hadamard A1 A2 b1 b2 A1Bnd b1Bnd A2Bnd b2Bnd
        w(1) sol_nonstrict]
      by auto
    have Ax_le: "A *\<^sub>v x \<le> 0\<^sub>v p" and neg_Ax_le: "- A *\<^sub>v x \<le> 0\<^sub>v p"
      using x(1-2) A negA
      by (auto simp: append_rows_le)
    have Ax0: "A *\<^sub>v x = 0\<^sub>v p"
      using A Ax_le le_zero_and_neg_le_zero_imp_zero neg_Ax_le x(1) by force
    have xi_neg: "(mat_of_row (- unit_vec q i :: int vec) *\<^sub>v x) $ 0 < 0"
      using less_vecD x(3) by force
    then have x0: "x \<noteq> 0\<^sub>v q"
      using i x by force
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
    have "mat_of_row (unit_vec q i :: int vec) *\<^sub>v w <\<^sub>v (0\<^sub>v 1 :: int vec)"
      using less_vec_def False i(1) w wi_neg by fastforce
    then obtain x where x: "x \<in> carrier_vec q" "(A @\<^sub>r - A) *\<^sub>v x \<le> (0\<^sub>v p @\<^sub>v 0\<^sub>v p)"
                "mat_of_row (unit_vec q i) *\<^sub>v x <\<^sub>v (0\<^sub>v 1)"
                "x \<in> Bounded_vec (int (q + 1) * det_bound_hadamard q (max 1 Bnd))"
      using small_integer_solution[OF det_bound_hadamard A1 A2 b1 b2 A1Bnd b1Bnd A2Bnd b2Bnd
        w(1) sol_nonstrict]
      by auto
    have Ax_le: "A *\<^sub>v x \<le> 0\<^sub>v p" and neg_Ax_le: "- A *\<^sub>v x \<le> 0\<^sub>v p"
      using x A negA by (auto simp: append_rows_le)
    have Ax0: "A *\<^sub>v x = 0\<^sub>v p"
      using A Ax_le neg_Ax_le x(1) 
      by (intro le_zero_and_neg_le_zero_imp_zero) auto
    have xi_neg: "(mat_of_row (unit_vec q i :: int vec) *\<^sub>v x) $ 0 < 0"
      using less_vecD[OF x(3) b2, of 0] by simp
    have x0: "x \<noteq> 0\<^sub>v q"
      using i xi_neg x(1) by force
    show ?thesis
      using x x0 Ax0 by blast
  qed
qed

text \<open>A counting form of Siegel's lemma. The bound can be selected to suit
  a particular auxiliary-polynomial construction.\<close>

theorem exists_ne_zero_int_vec_bounded_kernel_card:
  fixes A :: "int mat"
  assumes A: "A \<in> carrier_mat p q"
  assumes ppos: "0 < p"
  assumes hpq: "p < q"
  assumes ABnd: "A \<in> Bounded_mat Bnd"
  assumes count: "Suc (2 * q * nat (max 1 Bnd) * C) ^ p < Suc C ^ q"
  shows "\<exists>x. x \<in> carrier_vec q \<and> x \<noteq> 0\<^sub>v q \<and> A *\<^sub>v x = 0\<^sub>v p \<and>
    x \<in> Bounded_vec (int C)"
proof -
  define B where "B = nat (max 1 Bnd)"
  define M where "M = int q * int B * int C"

  let ?L = "{xs :: int list. set xs \<subseteq> {0..int C} \<and> length xs = q}"
  let ?S = "vec_of_list ` ?L"
  let ?K = "{ys :: int list. set ys \<subseteq> {-M..M} \<and> length ys = p}"
  let ?R = "vec_of_list ` ?K"
  let ?f = "\<lambda>x. A *\<^sub>v x"

  have B_int: "int B = max 1 Bnd"
    unfolding B_def by simp
  have C_pos: "0 < C"
    using count unfolding B_def by (cases C) auto
  have M_nonneg: "0 \<le> M"
    unfolding M_def by simp
  have card_C_interval: "card {0..int C} = Suc C"
    by simp
  have finL: "finite ?L"
    by (rule finite_lists_length_eq) simp
  have injL: "inj_on vec_of_list ?L"
    by (meson inj_on_inverseI list_vec)
  have cardL: "card ?L = Suc C ^ q"
    using card_C_interval by (simp add: card_lists_length_eq)
  have finS: "finite ?S"
    using finL by simp
  have cardS: "card ?S = Suc C ^ q"
    using cardL injL by (simp add: card_image)

  have M_twice: "2 * M + 1 = int (Suc (2 * q * B * C))"
    unfolding M_def by (simp add: algebra_simps)
  have M_card: "card {-M..M} = Suc (2 * q * B * C)"
  proof -
    have "card {-M..M} = nat (2 * M + 1)"
      using M_nonneg by simp
    also have "\<dots> = nat (int (Suc (2 * q * B * C)))"
      using M_twice by simp
    also have "\<dots> = Suc (2 * q * B * C)"
      by (simp only: nat_int)
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
  have cardK: "card ?K = Suc (2 * q * B * C) ^ p"
  proof -
    have "card ?K = card {-M..M} ^ p"
      by (simp add: card_lists_length_eq)
    also have "\<dots> = Suc (2 * q * B * C) ^ p"
      by (subst M_card) simp
    finally show ?thesis .
  qed
  have finR: "finite ?R"
    using finK by simp
  have cardR: "card ?R = Suc (2 * q * B * C) ^ p"
    using cardK injK by (simp add: card_image)

  have S_props:
    "x \<in> carrier_vec q \<and> (\<forall>j<q. 0 \<le> x $ j \<and> x $ j \<le> int C)" if xS: "x \<in> ?S" for x
  proof -
    obtain xs where xs: "xs \<in> ?L" and x_def: "x = vec_of_list xs"
      using xS by blast
    have xs_len: "length xs = q"
      using xs by auto
    have x_carrier: "x \<in> carrier_vec q"
      using x_def xs_len by force
    have x_bounds: "\<forall>j<q. 0 \<le> x $ j \<and> x $ j \<le> int C" 
      using x_def xs by force
    show ?thesis
      using x_carrier x_bounds by blast
  qed

  have image_sub: "?f ` ?S \<subseteq> ?R"
  proof
    fix y
    assume ymem: "y \<in> ?f ` ?S"
    then obtain x where xS: "x \<in> ?S" and y_def: "y = ?f x"
      by blast
    then have x_carrier: "x \<in> carrier_vec q" and x_bounds: "\<forall>j<q. 0 \<le> x $ j \<and> x $ j \<le> int C"
      using S_props[OF xS] by blast+
    have y_carrier: "y \<in> carrier_vec p"
      unfolding y_def by (rule mult_mat_vec_carrier[OF A x_carrier])
    have y_bounds: "y $ u \<in> {-M..M}" if up: "u < p" for u
    proof -
      have y_expand: "y $ u = (\<Sum>j<q. A $$ (u,j) * x $ j)"
      proof -
        have "y $ u = row A u \<bullet> x"
          using A up y_def by fastforce
        also have "\<dots> = (\<Sum>j<q. A $$ (u,j) * x $ j)"
          using A up x_carrier by (simp add: atLeast0LessThan scalar_prod_def)
        finally show ?thesis .
      qed
      have A_bound: "abs (A $$ (u,j)) \<le> int B" if j: "j < q" for j
        using ABnd A up j by (force simp: Bounded_mat_def B_int) 
      have x_bound: "abs (x $ j) \<le> int C" if j: "j < q" for j
        using x_bounds[rule_format, OF j] by auto
      have "abs (y $ u) \<le> (\<Sum>j<q. abs (A $$ (u,j) * x $ j))"
        unfolding y_expand by (rule sum_abs)
      also have "\<dots> = (\<Sum>j<q. abs (A $$ (u,j)) * abs (x $ j))"
        by (simp add: abs_mult)
      also have "\<dots> \<le> (\<Sum>j<q. int B * int C)"
        by (intro sum_mono A_bound x_bound mult_mono) auto
      also have "\<dots> = int q * int B * int C"
        by simp
      finally have abs_y: "abs (y $ u) \<le> M"
        unfolding M_def by simp
      then show "y $ u \<in> {-M..M}"
        by auto
    qed
    define ys where "ys \<equiv> map (\<lambda>u. y $ u) [0..<p]"
    have ys_mem: "ys \<in> ?K"
      unfolding ys_def using y_bounds by auto
    have y_vec: "vec_of_list ys = y"
      using y_carrier ys_def by auto
    show "y \<in> ?R"
      using ys_mem y_vec by blast
  qed
  have count_lt: "card (?f ` ?S) < card ?S"
  proof -
    have cardR_lt: "card ?R < card ?S"
      using count cardR cardS unfolding B_def by simp
    have "card (?f ` ?S) \<le> card ?R"
      by (rule card_mono[OF finR image_sub])
    with cardR_lt show ?thesis by linarith
  qed
  with pigeonhole obtain x y 
    where xS: "x \<in> ?S" and yS: "y \<in> ?S" and "x \<noteq> y" and img_eq: "?f x = ?f y"
    unfolding inj_on_def by blast
  have x_carrier: "x \<in> carrier_vec q" 
    and x_bounds: "\<forall>j<q. 0 \<le> x $ j \<and> x $ j \<le> int C"
    and y_carrier: "y \<in> carrier_vec q" 
    and y_bounds: "\<forall>j<q. 0 \<le> y $ j \<and> y $ j \<le> int C"
  using S_props xS yS by blast+
  obtain i where i: "i < q" "x $ i \<noteq> y $ i"
    using x_carrier y_carrier \<open>x \<noteq> y\<close> by force
  define z where "z \<equiv> x - y"
  have z_carrier: "z \<in> carrier_vec q"
    unfolding z_def using x_carrier y_carrier by auto
  have z_nz: "z \<noteq> 0\<^sub>v q"
    using i z_def by (metis index_minus_vec index_zero_vec right_minus_eq)
  have"A *\<^sub>v y \<in> carrier_vec p"
    by (rule mult_mat_vec_carrier[OF A y_carrier])
  then have Az0: "A *\<^sub>v z = 0\<^sub>v p"
    by (simp add: z_def img_eq mult_minus_distrib_mat_vec[OF A x_carrier y_carrier])
  have z_bnd: "z \<in> Bounded_vec (int C)"
    unfolding Bounded_vec_def z_def using x_bounds y_bounds y_carrier by fastforce
  show ?thesis
    using z_carrier z_nz Az0 z_bnd by blast
qed

corollary exists_ne_zero_int_vec_bounded_kernel_linear:
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
  have B_pos: "0 < B"
    unfolding B_def by simp
  have B_int: "int B = max 1 Bnd"
    unfolding B_def by simp
  have q_pos: "0 < q"
    using ppos hpq by linarith
  have C_pos: "0 < C"
    unfolding C_def using q_pos B_pos by simp
  have C_sq_lt: "Suc (C ^ 2) < Suc C ^ 2"
    using C_pos by (simp add: power2_eq_square)
  with ppos have "Suc (C ^ 2) ^ p < (Suc C ^ 2) ^ p"
    by (intro power_strict_mono) auto
  also have "\<dots> = Suc C ^ (2 * p)"
    by (simp add: power_mult)
  also have "\<dots> \<le> Suc C ^ q"
    using hpq C_pos by (intro power_increasing) auto
  finally have count: "Suc (2 * q * nat (max 1 Bnd) * C) ^ p < Suc C ^ q"
    unfolding C_def B_def by (simp add: power2_eq_square algebra_simps)
  have pq: "p < q"
    using hpq ppos by linarith
  from exists_ne_zero_int_vec_bounded_kernel_card[OF A ppos pq ABnd count]
  show ?thesis
    unfolding C_def using B_int by simp
qed

end
