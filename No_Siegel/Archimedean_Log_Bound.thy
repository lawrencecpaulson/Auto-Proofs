theory Archimedean_Log_Bound
  imports Archimedean_Conjugate
begin

text \<open>Green, Section 4: summing the two-embedding estimate across
  the evaluation grid gives the squared feature-row norm.\<close>

lemma green_gram_feature_sq_norm_as_sum:
  assumes idxs: "distinct idxs" "set idxs = I"
  shows "sq_norm (green_gram_feature d idxs f k) =
    (\<Sum>i\<in>I. real_of_int (green_quad_coeff_pair d (f k i) (f k i)))"
  using green_gram_feature_dot[OF idxs, of d f k k]
  by (simp add: sq_norm_vec_as_cscalar_prod green_gram_entry_def)

lemma green_gram_feature_sq_norm_bound:
  assumes idxs: "distinct idxs" "set idxs = I"
    and finiteI: "finite I"
    and bound: "\<And>i. i \<in> I \<Longrightarrow>
      real_of_int (green_quad_coeff_pair d (f k i) (f k i)) \<le> M"
  shows "sq_norm (green_gram_feature d idxs f k) \<le> real (card I) * M"
proof -
  have "sq_norm (green_gram_feature d idxs f k) =
      (\<Sum>i\<in>I. real_of_int
        (green_quad_coeff_pair d (f k i) (f k i)))"
    by (rule green_gram_feature_sq_norm_as_sum[OF idxs])
  also have "... \<le> (\<Sum>i\<in>I. M)"
    by (rule sum_mono) (rule bound)
  also have "... = real (card I) * M"
    using finiteI by simp
  finally show ?thesis .
qed

lemma (in green_quadratic_character) green_paper_row_coeff_pair_bound:
  assumes Npos: "0 < N" and rR: "r < R" and jJ: "j \<le> J"
    and p: "p \<in> diagonal_grid (cpx_sqrt d) (natural_grid N)"
  shows "real_of_int
    (green_quad_coeff_pair d
      (green_quad_coeff d (green_row_value (r,s) j p))
      (green_quad_coeff d (green_row_value (r,s) j p))) \<le>
    2 * (real R ^ J *
      (2 * real N * sqrt (real q)) ^ (r+s)) ^ 2"
proof -
  obtain x y :: nat where x: "x < N" and y: "y < N"
    and peq: "p = diagonal_point (cpx_sqrt d) (of_nat x, of_nat y)"
    using p by (auto simp: diagonal_grid_def natural_grid_def)
  let ?B = "2 * real N * sqrt (real q)"
  have B1: "1 \<le> ?B" by (rule green_paper_box_ge_one[OF Npos])
  have z: "green_quadratic_integer d (fst p)"
    by (simp add: peq green_lattice_coordinates_quadratic_integer)
  have w: "green_quadratic_integer d (snd p)"
    by (simp add: peq green_lattice_coordinates_quadratic_integer)
  have swap1: "green_quad_galois d (fst p) = snd p"
    using green_quad_galois_diagonal_coordinates(1)
      [OF lattice_slope_irrational, of x y] by (simp add: peq)
  have swap2: "green_quad_galois d (snd p) = fst p"
    using green_quad_galois_diagonal_coordinates(2)
      [OF lattice_slope_irrational, of x y] by (simp add: peq)
  have zb: "norm (fst p) \<le> ?B"
    using green_paper_coordinate_norm_bound(1)[OF x y]
    by (simp add: peq)
  have wb: "norm (snd p) \<le> ?B"
    using green_paper_coordinate_norm_bound(2)[OF x y]
    by (simp add: peq)
  show ?thesis
    by (rule green_row_coeff_pair_bound
      [OF lattice_slope_irrational z w swap1 swap2 rR jJ B1 zb wb])
qed

lemma (in green_quadratic_character) green_paper_feature_sq_norm_bound:
  assumes Npos: "0 < N" and rR: "r < R"
    and idxs: "distinct idxs"
      "set idxs = diagonal_grid (cpx_sqrt d) (natural_grid N) \<times> {..<J}"
  shows "sq_norm
    (green_gram_feature d idxs (green_row_gram_coeff d) (r,s)) \<le>
    real (N * N * J) *
      (2 * (real R ^ J *
        (2 * real N * sqrt (real q)) ^ (r+s)) ^ 2)"
proof -
  let ?P = "diagonal_grid (cpx_sqrt d) (natural_grid N)"
  let ?I = "?P \<times> {..<J}"
  have finiteP: "finite ?P"
    by (simp add: diagonal_grid_def natural_grid_finite)
  have finiteI: "finite ?I"
    by (simp add: finiteP)
  have injective: "inj_on (diagonal_point (cpx_sqrt d))
      (natural_grid N \<times> natural_grid N)"
    using natural_diagonal_second_distinct[OF lattice_slope_irrational]
    by (auto simp: inj_on_def)
  have cardP: "card ?P = N * N"
    unfolding diagonal_grid_def
    by (simp add: card_image[OF injective] natural_grid_card
      natural_grid_finite)
  have cardI: "card ?I = N * N * J"
    by (simp add: cardP finiteP)
  have entry: "real_of_int
      (green_quad_coeff_pair d
        (green_row_gram_coeff d (r,s) ij)
        (green_row_gram_coeff d (r,s) ij)) \<le>
      2 * (real R ^ J *
        (2 * real N * sqrt (real q)) ^ (r+s)) ^ 2"
    if ij: "ij \<in> ?I" for ij
  proof -
    obtain p j where peq: "ij = (p,j)" by (cases ij) auto
    have p: "p \<in> ?P" and j: "j \<le> J"
      using ij by (auto simp: peq)
    show ?thesis
      using green_paper_row_coeff_pair_bound[OF Npos rR j p]
      by (simp add: peq green_row_gram_coeff_def)
  qed
  have "sq_norm
      (green_gram_feature d idxs (green_row_gram_coeff d) (r,s))
      \<le> real (card ?I) *
        (2 * (real R ^ J *
          (2 * real N * sqrt (real q)) ^ (r+s)) ^ 2)"
  proof (rule green_gram_feature_sq_norm_bound[where I="?I"])
    show "distinct idxs" by (rule idxs(1))
    show "set idxs = ?I" by (rule idxs(2))
    show "finite ?I" by (rule finiteI)
    fix ij assume "ij \<in> ?I"
    then show "real_of_int
      (green_quad_coeff_pair d
        (green_row_gram_coeff d (r,s) ij)
        (green_row_gram_coeff d (r,s) ij)) \<le>
      2 * (real R ^ J *
        (2 * real N * sqrt (real q)) ^ (r+s)) ^ 2"
      by (rule entry)
  qed
  then show ?thesis by (simp add: cardI)
qed

text \<open>Green, Section 4: an explicit archimedean product bound for
  the integer Gram determinant at the paper's parameters.\<close>

lemma (in green_quadratic_character) green_paper_gram_archimedean_product:
  assumes even: "even cparam" and cparam: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
    and idxs: "distinct idxs"
      "set idxs = diagonal_grid (cpx_sqrt d)
        (natural_grid (green_N q cparam)) \<times> {..<green_J q cparam}"
  shows "real_of_int (green_row_gram_determinant d
      (diagonal_grid (cpx_sqrt d) (natural_grid (green_N q cparam)))
      (green_J q cparam) (green_X q cparam) (green_J q cparam))
    \<le> prod_list (map
      (\<lambda>(r,s). real (green_N q cparam * green_N q cparam *
        green_J q cparam) *
        (2 * (real (green_X q cparam) ^ (green_J q cparam) *
          (2 * real (green_N q cparam) * sqrt (real q)) ^ (r+s)) ^ 2))
      (green_row_order (green_X q cparam) (green_J q cparam)))"
proof -
  let ?N = "green_N q cparam"
  let ?J = "green_J q cparam"
  let ?R = "green_X q cparam"
  let ?P = "diagonal_grid (cpx_sqrt d) (natural_grid ?N)"
  let ?ks = "green_row_order ?R ?J"
  let ?f = "\<lambda>k. sq_norm
    (green_gram_feature d idxs (green_row_gram_coeff d) k)"
  let ?g = "\<lambda>(r,s). real (?N * ?N * ?J) *
    (2 * (real ?R ^ ?J *
      (2 * real ?N * sqrt (real q)) ^ (r+s)) ^ 2)"
  have Npos: "0 < ?N"
    using conductor_pos by (simp add: green_N_def)
  have bound: "?f k \<le> ?g k" if k: "k \<in> set ?ks" for k
  proof -
    obtain r s where keq: "k = (r,s)" by (cases k) auto
    have rR: "r < ?R"
      using k by (auto simp: keq green_row_indices_def)
    have "sq_norm
      (green_gram_feature d idxs (green_row_gram_coeff d) (r,s)) \<le>
      real (?N * ?N * ?J) *
        (2 * (real ?R ^ ?J *
          (2 * real ?N * sqrt (real q)) ^ (r+s)) ^ 2)"
      by (rule green_paper_feature_sq_norm_bound[OF Npos rR idxs])
    then show ?thesis by (simp add: keq)
  qed
  have point: "0 \<le> (map ?f ?ks) ! i \<and>
      (map ?f ?ks) ! i \<le> (map ?g ?ks) ! i"
    if i: "i < length ?ks" for i
  proof -
    have mem: "?ks ! i \<in> set ?ks" by (rule nth_mem[OF i])
    have upper: "?f (?ks ! i) \<le> ?g (?ks ! i)"
      by (rule bound[OF mem])
    show ?thesis using i upper by (simp add: sq_norm_vec_ge_0)
  qed
  have prod_bound: "prod_list (map ?f ?ks) \<le>
      prod_list (map ?g ?ks)"
    using prod_list_le_mono[of "map ?f ?ks" "map ?g ?ks"]
      point by simp
  have det_bound': "real_of_int (green_row_gram_determinant d
      ?P ?J ?R ?J) \<le>
      prod_list (map sq_norm
        (map (green_gram_feature d idxs (green_row_gram_coeff d)) ?ks))"
    by (rule green_paper_gram_hadamard[OF even cparam large idxs])
  have det_bound: "real_of_int (green_row_gram_determinant d
      ?P ?J ?R ?J) \<le> prod_list (map ?f ?ks)"
    using det_bound' by (simp add: o_def)
  show ?thesis using det_bound prod_bound by simp
qed

text \<open>Green, Section 4: summing the row exponents is the arithmetic
  step in the logarithmic determinant estimate.\<close>

lemma green_real_index_sum:
  "(\<Sum>i<R. real i) = real R * (real R - 1) / 2"
proof (induction R)
  case 0
  then show ?case by simp
next
  case (Suc R)
  then show ?case
    by (simp add: sum.lessThan_Suc algebra_simps)
qed

lemma green_row_order_exponent_sum:
  "sum_list (map (\<lambda>k. real (fst k + snd k))
      (green_row_order R S)) =
    real (R * S) * (real (R + S) - 2) / 2"
proof -
  have as_set: "sum_list (map (\<lambda>k. real (fst k + snd k))
      (green_row_order R S)) =
      (\<Sum>k\<in>green_row_indices R S. real (fst k + snd k))"
    by (simp add: sum_list_distinct_conv_sum_set)
  have inner: "(\<Sum>s<S. real (r+s)) =
      real S * real r + (\<Sum>s<S. real s)" for r
    by (simp add: sum.distrib sum_distrib_left)
  have double: "(\<Sum>r<R. \<Sum>s<S. real (r+s)) =
      real S * (\<Sum>r<R. real r) +
        real R * (\<Sum>s<S. real s)"
    by (simp add: inner sum.distrib sum_distrib_left)
  have "(\<Sum>k\<in>green_row_indices R S.
      real (fst k + snd k)) =
      (\<Sum>r<R. \<Sum>s<S. real (r+s))"
    unfolding green_row_indices_def
    by (subst sum.cartesian_product)
      (simp add: case_prod_unfold)
  also have "... = real (R * S) * (real (R + S) - 2) / 2"
    unfolding double green_real_index_sum
    by (simp add: algebra_simps)
  finally show ?thesis using as_set by simp
qed

lemma green_prod_list_map_pos:
  fixes f :: "'a \<Rightarrow> real"
  assumes positive: "\<And>k. k \<in> set ks \<Longrightarrow> 0 < f k"
  shows "0 < prod_list (map f ks)"
  using positive
proof (induction ks)
  case Nil
  then show ?case by simp
next
  case (Cons k ks)
  have fk: "0 < f k" using Cons.prems by simp
  have tail: "0 < prod_list (map f ks)"
    by (rule Cons.IH) (use Cons.prems in auto)
  show ?case using fk tail by simp
qed

lemma green_ln_prod_list_map:
  fixes f :: "'a \<Rightarrow> real"
  assumes positive: "\<And>k. k \<in> set ks \<Longrightarrow> 0 < f k"
  shows "ln (prod_list (map f ks)) =
    sum_list (map (\<lambda>k. ln (f k)) ks)"
  using positive
proof (induction ks)
  case Nil
  then show ?case by simp
next
  case (Cons k ks)
  have fk: "0 < f k" using Cons.prems by simp
  have tail: "\<And>x. x \<in> set ks \<Longrightarrow> 0 < f x"
    using Cons.prems by simp
  have prod: "0 < prod_list (map f ks)"
    by (rule green_prod_list_map_pos[OF tail])
  have step: "ln (f k * prod_list (map f ks)) =
      ln (f k) + ln (prod_list (map f ks))"
    by (rule ln_mult_pos[OF fk prod])
  show ?case using step Cons.IH[OF tail] by simp
qed

lemma green_sum_list_affine:
  fixes a b :: real
  shows "sum_list (map (\<lambda>k. a + b * f k) ks) =
    real (length ks) * a + b * sum_list (map f ks)"
  by (induction ks) (simp_all add: algebra_simps)

lemma green_row_order_product_log:
  fixes A B :: real
  assumes Apos: "0 < A" and Bpos: "0 < B"
  shows "ln (prod_list (map
      (\<lambda>k. A * B ^ (2 * (fst k + snd k)))
      (green_row_order R S))) =
    real (R * S) * ln A +
      real (R * S) * (real (R + S) - 2) * ln B"
proof -
  let ?ks = "green_row_order R S"
  let ?f = "\<lambda>k. A * B ^ (2 * (fst k + snd k))"
  have pos: "0 < ?f k" for k
    using Apos Bpos by simp
  have point: "ln (?f k) =
      ln A + 2 * real (fst k + snd k) * ln B" for k
    using Apos Bpos by (simp add: ln_mult ln_realpow)
  have "ln (prod_list (map ?f ?ks)) =
      sum_list (map (\<lambda>k. ln (?f k)) ?ks)"
    by (rule green_ln_prod_list_map) (use pos in simp)
  also have "... =
      real (length ?ks) * ln A +
        2 * ln B *
          sum_list (map (\<lambda>k. real (fst k + snd k)) ?ks)"
  proof -
    have per: "ln (?f k) =
        ln A + (2 * ln B) * real (fst k + snd k)" for k
      using point[of k] by (simp add: mult_ac)
    have "sum_list (map (\<lambda>k. ln (?f k)) ?ks) =
        sum_list (map (\<lambda>k. ln A +
          (2 * ln B) * real (fst k + snd k)) ?ks)"
      by (simp only: per)
    also have "... = real (length ?ks) * ln A +
        (2 * ln B) *
          sum_list (map (\<lambda>k. real (fst k + snd k)) ?ks)"
      by (rule green_sum_list_affine)
    finally show ?thesis by (simp add: mult_ac)
  qed
  also have "... =
      real (R * S) * ln A +
        real (R * S) * (real (R + S) - 2) * ln B"
  proof -
    have "real (length ?ks) * ln A +
        2 * ln B *
          sum_list (map (\<lambda>k. real (fst k + snd k)) ?ks) =
        real (R * S) * ln A +
          2 * ln B * (real (R * S) * (real (R + S) - 2) / 2)"
      by (simp only: green_row_order_length
        green_row_order_exponent_sum)
    also have "... = real (R * S) * ln A +
        real (R * S) * (real (R + S) - 2) * ln B"
      by (simp add: mult_ac)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma (in green_quadratic_character) green_paper_gram_archimedean_log:
  assumes even: "even cparam" and cparam: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
    and idxs: "distinct idxs"
      "set idxs = diagonal_grid (cpx_sqrt d)
        (natural_grid (green_N q cparam)) \<times> {..<green_J q cparam}"
  shows "ln (real_of_int (green_row_gram_determinant d
      (diagonal_grid (cpx_sqrt d) (natural_grid (green_N q cparam)))
      (green_J q cparam) (green_X q cparam) (green_J q cparam)))
    \<le> real (green_X q cparam * green_J q cparam) *
        ln (2 * real (green_N q cparam * green_N q cparam *
          green_J q cparam)) +
      2 * real (green_J q cparam) *
        real (green_X q cparam * green_J q cparam) *
        ln (real (green_X q cparam)) +
      real (green_X q cparam * green_J q cparam) *
        real (green_X q cparam + green_J q cparam) *
        ln (2 * real (green_N q cparam) * sqrt (real q))"
proof -
  let ?N = "green_N q cparam"
  let ?J = "green_J q cparam"
  let ?R = "green_X q cparam"
  let ?B = "2 * real ?N * sqrt (real q)"
  let ?A = "2 * real (?N * ?N * ?J) * real ?R ^ (2 * ?J)"
  let ?P = "diagonal_grid (cpx_sqrt d) (natural_grid ?N)"
  let ?ks = "green_row_order ?R ?J"
  let ?g = "\<lambda>(r,s). real (?N * ?N * ?J) *
    (2 * (real ?R ^ ?J * ?B ^ (r+s)) ^ 2)"
  have Npos: "0 < ?N"
    using conductor_pos by (simp add: green_N_def)
  have Jge: "?N \<le> ?J"
    by (rule green_paper_row_parameters(1)[OF even cparam large])
  have Jpos: "0 < ?J" using Npos Jge by linarith
  have Rpos: "0 < ?R"
    using conductor_pos by (simp add: green_X_def)
  have B1: "1 \<le> ?B" by (rule green_paper_box_ge_one[OF Npos])
  have Bpos: "0 < ?B" using B1 by linarith
  have Cpos: "0 < 2 * real (?N * ?N * ?J)"
    using Npos Jpos by simp
  have Apos: "0 < ?A" using Cpos Rpos by simp
  have cap: "?g k = ?A * ?B ^ (2 * (fst k + snd k))" for k
  proof (cases k)
    case (Pair r s)
    have powR: "(real ?R ^ ?J) ^ 2 = real ?R ^ (2 * ?J)"
      by (simp add: power_mult[symmetric] mult.commute)
    have powB: "(?B ^ (r+s)) ^ 2 = ?B ^ (2 * (r+s))"
      by (simp add: power_mult[symmetric] mult.commute)
    have pow: "(real ?R ^ ?J * ?B ^ (r+s)) ^ 2 =
        real ?R ^ (2 * ?J) * ?B ^ (2 * (r+s))"
      by (simp only:
        power_mult_distrib[of "real ?R ^ ?J" "?B ^ (r+s)" 2]
        powR powB)
    have "?g (r,s) =
        2 * real (?N * ?N * ?J) *
          (real ?R ^ ?J * ?B ^ (r+s)) ^ 2"
      by (simp add: mult_ac)
    also have "... = ?A * ?B ^ (2 * (r+s))"
      by (subst pow) (simp add: mult_ac)
    finally show ?thesis using Pair by simp
  qed
  have Rpow: "0 < real ?R ^ (2 * ?J)"
    using Rpos by simp
  have lnA: "ln ?A =
      ln (2 * real (?N * ?N * ?J)) +
        2 * real ?J * ln (real ?R)"
  proof -
    have "ln ?A = ln (2 * real (?N * ?N * ?J)) +
        ln (real ?R ^ (2 * ?J))"
      by (rule ln_mult_pos[OF Cpos Rpow])
    then show ?thesis by (simp add: ln_realpow)
  qed
  have log_product: "ln (prod_list (map ?g ?ks)) =
      real (?R * ?J) * ln (2 * real (?N * ?N * ?J)) +
      2 * real ?J * real (?R * ?J) * ln (real ?R) +
      real (?R * ?J) * (real (?R + ?J) - 2) * ln ?B"
  proof -
    have map_eq: "map ?g ?ks =
        map (\<lambda>k. ?A * ?B ^ (2 * (fst k + snd k))) ?ks"
    proof (rule map_cong)
      show "?ks = ?ks" by simp
      fix k assume "k \<in> set ?ks"
      show "?g k = ?A * ?B ^ (2 * (fst k + snd k))"
        by (rule cap)
    qed
    have "ln (prod_list (map ?g ?ks)) =
        ln (prod_list (map
          (\<lambda>k. ?A * ?B ^ (2 * (fst k + snd k))) ?ks))"
      by (simp only: map_eq)
    also have "... =
        real (?R * ?J) * ln ?A +
          real (?R * ?J) * (real (?R + ?J) - 2) * ln ?B"
      by (rule green_row_order_product_log[OF Apos Bpos])
    also have "... =
        real (?R * ?J) * ln (2 * real (?N * ?N * ?J)) +
        2 * real ?J * real (?R * ?J) * ln (real ?R) +
        real (?R * ?J) * (real (?R + ?J) - 2) * ln ?B"
      by (simp only: lnA; simp add: algebra_simps)
    finally show ?thesis .
  qed
  have detpos: "0 < real_of_int (green_row_gram_determinant d
      ?P ?J ?R ?J)"
    using green_paper_gram_determinant_positive
      [OF even cparam large] by simp
  have detprod: "real_of_int (green_row_gram_determinant d
      ?P ?J ?R ?J) \<le> prod_list (map ?g ?ks)"
    using green_paper_gram_archimedean_product
      [OF even cparam large idxs]
    by simp
  have log_le: "ln (real_of_int (green_row_gram_determinant d
      ?P ?J ?R ?J)) \<le> ln (prod_list (map ?g ?ks))"
    by (rule ln_mono[OF detprod detpos])
  have logB: "0 \<le> ln ?B" using B1 by simp
  have surplus: "0 \<le> 2 * real (?R * ?J) * ln ?B"
    using logB by simp
  show ?thesis using log_le log_product surplus
    by (simp add: algebra_simps; linarith)
qed

end
