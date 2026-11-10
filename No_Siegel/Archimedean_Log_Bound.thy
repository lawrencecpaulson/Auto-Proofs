theory Archimedean_Log_Bound
  imports Archimedean_Determinant_Bound
begin

text \<open>Green, Section 4: summing the row exponents is the arithmetic
  step in the logarithmic determinant estimate.\<close>

declare [[apply_timeout = 20]]

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

declare [[apply_timeout = 0]]

end
