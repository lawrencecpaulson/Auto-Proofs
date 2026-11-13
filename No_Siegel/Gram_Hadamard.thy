theory Gram_Hadamard
  imports Gram_Determinant LLL_Basis_Reduction.Gram_Schmidt_2
    Jordan_Normal_Form.DL_Rank_Submatrix
begin

text \<open>The matrix inequality behind Green's archimedean estimate. The
  independence premise will be supplied by the positive Gram form.\<close>

lemma green_prod_list_upt:
  "prod_list (map f [0..<n]) = (\<Prod>i<n. f i)"
  by (induction n) simp_all

lemma green_real_gram_hadamard:
  fixes fs :: "real vec list"
  assumes carrier: "set fs \<subseteq> carrier_vec m"
    and independent: "LinearCombinations.module.lin_indpt class_ring
      (module_vec TYPE(real) m) (set fs)"
    and distinct: "distinct fs"
  shows "det (mat_of_rows m fs * (mat_of_rows m fs)\<^sup>T)
    \<le> prod_list (map sq_norm fs)"
proof -
  interpret gs: gram_schmidt_fs_lin_indpt m fs
    by (standard) (use carrier independent distinct in auto)
  have gram: "gs.Gramian_matrix fs (length fs) =
    mat_of_rows m fs * (mat_of_rows m fs)\<^sup>T"
    using gs.Gramian_matrix_alt_def[of "length fs" fs]
    by (simp add: Let_def)
  have det: "det (mat_of_rows m fs * (mat_of_rows m fs)\<^sup>T) =
    (\<Prod>i<length fs. sq_norm (gs.gso i))"
    using gs.Gramian_determinant(1)[of "length fs"]
    by (simp add: gs.Gramian_determinant_def gram)
  have le: "(\<Prod>i<length fs. sq_norm (gs.gso i)) \<le>
    (\<Prod>i<length fs. sq_norm (fs ! i))"
    by (intro prod_mono) (auto intro: gs.sq_norm_gso_le_f)
  have fs_map: "map (\<lambda>i. sq_norm (fs ! i)) [0..<length fs] =
    map sq_norm fs"
  proof -
    have "map (\<lambda>i. sq_norm (fs ! i)) [0..<length fs] =
      map sq_norm (map (nth fs) [0..<length fs])"
      by simp
    also have "... = map sq_norm fs" by (simp add: map_nth)
    finally show ?thesis .
  qed
  have "(\<Prod>i<length fs. sq_norm (fs ! i)) =
    prod_list (map sq_norm fs)"
    by (simp add: green_prod_list_upt[symmetric] fs_map)
  with det le show ?thesis by simp
qed

lemma green_real_gram_rows_independent:
  fixes M :: "real mat"
  assumes nonzero: "det (M * M\<^sup>T) \<noteq> 0"
  shows "distinct (rows M)"
    and "LinearCombinations.module.lin_indpt class_ring
      (module_vec TYPE(real) (dim_col M)) (set (rows M))"
proof -
  let ?n = "dim_row M"
  let ?m = "dim_col M"
  obtain J where J: "J \<subseteq> {0..< ?m}" "card J = ?n"
    and detB: "det (submatrix M UNIV J) \<noteq> 0"
    by (rule green_real_gram_nonzero_minor[OF nonzero])
  let ?B = "submatrix M UNIV J"
  have Jset: "{j. j < ?m \<and> j \<in> J} = J"
    using J(1) by auto
  have Bcar: "?B \<in> carrier_mat ?n ?n"
    using J(2) by (simp add: submatrix_def Jset)
  interpret W: idom_vec ?n "TYPE(real)" .
  have independent_B: "LinearCombinations.module.lin_indpt class_ring
    (module_vec TYPE(real) ?n) (set (rows ?B))"
    by (rule W.det_not_0_imp_lin_indpt_rows[OF Bcar detB])
  have distinct_B: "distinct (rows ?B)"
  proof (rule ccontr)
    assume "\<not> distinct (rows ?B)"
    then obtain i j where i: "i < ?n" and j: "j < ?n"
      and ne: "i \<noteq> j" and same: "row ?B i = row ?B j"
      using Bcar
      by (metis carrier_matD(1) distinct_conv_nth length_rows nth_rows)
    have "det ?B = 0"
      by (rule Determinant.det_identical_rows[OF Bcar ne i j same])
    with detB show False by simp
  qed
  let ?A = "M\<^sup>T"
  have Acar: "?A \<in> carrier_mat ?m ?n" by simp
  have subA: "submatrix ?A J UNIV = ?B\<^sup>T"
    by (rule green_submatrix_transpose)
  have distinct_sub: "distinct (cols (submatrix ?A J UNIV))"
    using distinct_B by (simp add: subA)
  have distinct_A: "distinct (cols ?A)"
    by (rule distinct_cols_submatrix_UNIV[OF distinct_sub])
  interpret V: vec_space "TYPE(real)" ?m .
  have independent_A: "LinearCombinations.module.lin_indpt class_ring
    (module_vec TYPE(real) ?m) (set (cols ?A))"
  proof (rule ccontr)
    assume dependent: "\<not> LinearCombinations.module.lin_indpt class_ring
      (module_vec TYPE(real) ?m) (set (cols ?A))"
    have dep_sub: "LinearCombinations.module.lin_dep class_ring
      (module_vec TYPE(real) (card {i. i < ?m \<and> i \<in> J}))
      (set (cols (submatrix ?A J UNIV)))"
      by (rule V.lin_dep_submatrix_UNIV[OF Acar _ distinct_sub])
        (use dependent in simp)
    with independent_B show False
      by (simp add: subA Jset J(2))
  qed
  show "distinct (rows M)" using distinct_A by simp
  show "LinearCombinations.module.lin_indpt class_ring
      (module_vec TYPE(real) (dim_col M)) (set (rows M))"
    using independent_A by simp
qed

lemma green_real_gram_hadamard_nonzero:
  fixes M :: "real mat"
  assumes nonzero: "det (M * M\<^sup>T) \<noteq> 0"
  shows "det (M * M\<^sup>T) \<le> prod_list (map sq_norm (rows M))"
proof -
  have carrier: "set (rows M) \<subseteq> carrier_vec (dim_col M)"
    by auto
  have independent:
    "LinearCombinations.module.lin_indpt class_ring
      (module_vec TYPE(real) (dim_col M)) (set (rows M))"
    by (rule green_real_gram_rows_independent(2)[OF nonzero])
  have distinct: "distinct (rows M)"
    by (rule green_real_gram_rows_independent(1)[OF nonzero])
  have "mat_of_rows (dim_col M) (rows M) = M" by simp
  from green_real_gram_hadamard[OF carrier independent distinct]
  show ?thesis by simp
qed

lemma green_gram_determinant_hadamard:
  assumes idxs: "distinct idxs" "set idxs = I"
    and nonzero: "green_gram_determinant d I f ks \<noteq> 0"
  shows "real_of_int (green_gram_determinant d I f ks) \<le>
    prod_list (map sq_norm
      (map (green_gram_feature d idxs f) ks))"
proof -
  let ?fs = "map (green_gram_feature d idxs f) ks"
  let ?M = "mat_of_rows (2 * length idxs) ?fs"
  have fs_carrier: "set ?fs \<subseteq> carrier_vec (2 * length idxs)"
    by auto
  have real_det: "real_of_int (green_gram_determinant d I f ks) =
      det (?M * ?M\<^sup>T)"
    by (simp add: Let_def green_gram_determinant_real
      green_gram_matrix_as_real_gram[OF idxs])
  have det_nonzero: "det (?M * ?M\<^sup>T) \<noteq> 0"
    using nonzero real_det by simp
  have rows: "rows ?M = ?fs" using fs_carrier by simp
  from green_real_gram_hadamard_nonzero[OF det_nonzero]
  show ?thesis by (simp add: real_det rows)
qed

lemma (in green_quadratic_character) green_paper_gram_hadamard:
  assumes even: "even cparam" and cparam: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
    and idxs: "distinct idxs"
      "set idxs = diagonal_grid (cpx_sqrt d)
        (natural_grid (green_N q cparam)) \<times> {..<green_J q cparam}"
  shows "real_of_int (green_row_gram_determinant d
      (diagonal_grid (cpx_sqrt d) (natural_grid (green_N q cparam)))
      (green_J q cparam) (green_X q cparam) (green_J q cparam))
    \<le> prod_list (map sq_norm
      (map (green_gram_feature d idxs (green_row_gram_coeff d))
        (green_row_order (green_X q cparam) (green_J q cparam))))"
proof -
  have positive: "0 < green_row_gram_determinant d
    (diagonal_grid (cpx_sqrt d) (natural_grid (green_N q cparam)))
    (green_J q cparam) (green_X q cparam) (green_J q cparam)"
    by (rule green_paper_gram_determinant_positive[OF even cparam large])
  have nonzero: "green_gram_determinant d
    (diagonal_grid (cpx_sqrt d)
      (natural_grid (green_N q cparam)) \<times> {..<green_J q cparam})
    (green_row_gram_coeff d)
    (green_row_order (green_X q cparam) (green_J q cparam)) \<noteq> 0"
    using positive by (simp add: green_row_gram_determinant_def)
  from green_gram_determinant_hadamard[OF idxs nonzero]
  show ?thesis by (simp add: green_row_gram_determinant_def)
qed

end
