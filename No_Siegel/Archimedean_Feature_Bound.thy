theory Archimedean_Feature_Bound
  imports Archimedean_Conjugate
begin

text \<open>Green, Section 4: summing the two-embedding estimate across
  the evaluation grid gives the squared feature-row norm.\<close>

declare [[apply_timeout = 20]]

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

declare [[apply_timeout = 0]]

end
