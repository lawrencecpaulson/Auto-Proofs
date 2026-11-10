theory Archimedean_Determinant_Bound
  imports Archimedean_Feature_Bound
begin

text \<open>Green, Section 4: an explicit archimedean product bound for
  the integer Gram determinant at the paper's parameters.\<close>

declare [[apply_timeout = 20]]

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

declare [[apply_timeout = 0]]

end
