theory Gram_Determinant
  imports Quadratic_Gram Jordan_Normal_Form.Determinant
    Smith_Normal_Form.Cauchy_Binet
begin

text \<open>The finite integer Gram matrix uses Green's derivative rows; the real
  feature vectors give its two quadratic coordinate blocks.\<close>

definition green_gram_matrix ::
  "int \<Rightarrow> 'i set \<Rightarrow> ('k \<Rightarrow> 'i \<Rightarrow> int \<times> int) \<Rightarrow>
    'k list \<Rightarrow> int mat" where
  "green_gram_matrix d I f ks =
    mat (length ks) (length ks)
      (\<lambda>(a,b). green_gram_entry d I f (ks ! a) (ks ! b))"

lemma green_gram_matrix_carrier [simp]:
  "green_gram_matrix d I f ks \<in> carrier_mat (length ks) (length ks)"
  by (simp add: green_gram_matrix_def)

lemma green_gram_matrix_entry:
  assumes "a < length ks" and "b < length ks"
  shows "green_gram_matrix d I f ks $$ (a,b) =
    green_gram_entry d I f (ks ! a) (ks ! b)"
  using assms by (simp add: green_gram_matrix_def)

lemma green_gram_matrix_symmetric:
  "transpose_mat (green_gram_matrix d I f ks) = green_gram_matrix d I f ks"
  by (rule eq_matI) (auto simp: green_gram_matrix_def green_gram_entry_sym)

definition green_gram_determinant ::
  "int \<Rightarrow> 'i set \<Rightarrow> ('k \<Rightarrow> 'i \<Rightarrow> int \<times> int) \<Rightarrow>
    'k list \<Rightarrow> int" where
  "green_gram_determinant d I f ks = det (green_gram_matrix d I f ks)"

lemma green_gram_determinant_real:
  "of_int (green_gram_determinant d I f ks) =
    det (map_mat real_of_int (green_gram_matrix d I f ks))"
  by (simp add: green_gram_determinant_def)

definition green_row_order :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "green_row_order R S = List.product [0..<R] [0..<S]"

lemma green_row_order_distinct [simp]: "distinct (green_row_order R S)"
  by (simp add: green_row_order_def distinct_product)

lemma green_row_order_set [simp]: "set (green_row_order R S) = green_row_indices R S"
  by (auto simp: green_row_order_def green_row_indices_def)

lemma green_row_order_length [simp]: "length (green_row_order R S) = R * S"
  by (simp add: green_row_order_def green_row_indices_def)

definition green_row_gram_determinant ::
  "int \<Rightarrow> (complex \<times> complex) set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "green_row_gram_determinant d P J R S =
    green_gram_determinant d (P \<times> {..<J}) (green_row_gram_coeff d)
      (green_row_order R S)"

definition green_gram_feature ::
  "int \<Rightarrow> 'i list \<Rightarrow> ('k \<Rightarrow> 'i \<Rightarrow> int \<times> int) \<Rightarrow>
    'k \<Rightarrow> real vec" where
  "green_gram_feature d is f k =
    vec (length is) (\<lambda>j. sqrt 2 * real_of_int (fst (f k (is ! j))))
    @\<^sub>v vec (length is)
      (\<lambda>j. sqrt (2 * real_of_int (abs d)) *
        real_of_int (snd (f k (is ! j))))"

lemma green_gram_feature_carrier [simp]:
  "green_gram_feature d is f k \<in> carrier_vec (2 * length is)"
  proof -
    have "green_gram_feature d is f k \<in> carrier_vec (length is + length is)"
      by (simp add: green_gram_feature_def)
    then show ?thesis by (simp add: mult_2)
  qed

lemma green_gram_feature_dot:
  assumes "distinct is" and "set is = I"
  shows "green_gram_feature d is f k \<bullet> green_gram_feature d is f l =
    real_of_int (green_gram_entry d I f k l)"
proof -
  let ?m = "length is"
  let ?A = "\<lambda>j. sqrt 2 * real_of_int (fst (f k (is ! j)))"
  let ?B = "\<lambda>j. sqrt (2 * real_of_int (abs d)) * real_of_int (snd (f k (is ! j)))"
  let ?C = "\<lambda>j. sqrt 2 * real_of_int (fst (f l (is ! j)))"
  let ?D = "\<lambda>j. sqrt (2 * real_of_int (abs d)) * real_of_int (snd (f l (is ! j)))"
  let ?h = "\<lambda>i. 2 * (fst (f k i) * fst (f l i) +
    abs d * snd (f k i) * snd (f l i))"
  have sum: "(\<Sum>j<?m. real_of_int (?h (is ! j))) =
      real_of_int (green_gram_entry d I f k l)"
  proof -
    have "(\<Sum>j<?m. ?h (is ! j)) = sum_list (map ?h is)"
      by (simp add: sum_list_sum_nth atLeast0LessThan)
    also have "... = (\<Sum>i\<in>I. ?h i)"
      using assms by (simp add: sum_list_distinct_conv_sum_set)
    finally have hsum: "(\<Sum>j<?m. ?h (is ! j)) = green_gram_entry d I f k l"
      by (simp only: green_gram_entry_def green_quad_coeff_pair_def)
    have co: "(\<Sum>j<?m. real_of_int (?h (is ! j))) =
      real_of_int (\<Sum>j<?m. ?h (is ! j))"
      by (simp only: of_int_sum)
    show ?thesis unfolding co hsum ..
  qed
  have "green_gram_feature d is f k \<bullet> green_gram_feature d is f l =
    (\<Sum>j<?m. ?A j * ?C j) + (\<Sum>j<?m. ?B j * ?D j)"
    unfolding green_gram_feature_def
    by (subst scalar_prod_append; simp add: scalar_prod_def atLeast0LessThan)
  also have "... = (\<Sum>j<?m. real_of_int (?h (is ! j)))"
  proof -
    have sq2: "sqrt (2::real) * sqrt 2 = 2" by simp
    have sqd: "sqrt (2 * real_of_int (abs d)) *
      sqrt (2 * real_of_int (abs d)) = 2 * real_of_int (abs d)" by simp
    have point: "?A j * ?C j + ?B j * ?D j =
      real_of_int (?h (is ! j))" for j
      using sq2 sqd by (simp add: algebra_simps mult_ac)
    show ?thesis
      by (simp only: sum.distrib[symmetric]; rule sum.cong; (rule refl | rule point))
  qed
  also have "... = real_of_int (green_gram_entry d I f k l)" by (rule sum)
  finally show ?thesis .
qed

lemma green_gram_matrix_as_real_gram:
  assumes idxs: "distinct idxs" "set idxs = I"
  shows "map_mat real_of_int (green_gram_matrix d I f ks) =
    (let M = mat_of_rows (2 * length idxs)
      (map (green_gram_feature d idxs f) ks) in M * M\<^sup>T)"
proof -
  let ?n = "length ks"
  let ?m = "2 * length idxs"
  let ?fs = "map (green_gram_feature d idxs f) ks"
  let ?M = "mat_of_rows ?m ?fs"
  have carrier: "set ?fs \<subseteq> carrier_vec ?m" by auto
  have row: "row ?M a = green_gram_feature d idxs f (ks ! a)" if a: "a < ?n" for a
    using a by simp
  have dim: "?M \<in> carrier_mat ?n ?m" by (simp add: mat_of_rows_def)
  show ?thesis
  proof (rule eq_matI)
    show "dim_row (map_mat real_of_int (green_gram_matrix d I f ks)) =
      dim_row (let M = ?M in M * M\<^sup>T)" using dim by (simp add: green_gram_matrix_def mat_of_rows_def Let_def)
    show "dim_col (map_mat real_of_int (green_gram_matrix d I f ks)) =
      dim_col (let M = ?M in M * M\<^sup>T)" using dim by (simp add: green_gram_matrix_def mat_of_rows_def Let_def)
    fix a b
    assume ab: "a < dim_row (let M = ?M in M * M\<^sup>T)"
      "b < dim_col (let M = ?M in M * M\<^sup>T)"
    have a: "a < ?n" and b: "b < ?n" using ab dim by (auto simp: Let_def)
    have "(let M = ?M in M * M\<^sup>T) $$ (a,b) =
      row ?M a \<bullet> row ?M b"
      using a b dim by (simp add: Let_def)
    also have "... = real_of_int (green_gram_entry d I f (ks ! a) (ks ! b))"
      by (simp add: row[OF a] row[OF b] green_gram_feature_dot[OF idxs])
    also have "... = map_mat real_of_int (green_gram_matrix d I f ks) $$ (a,b)"
      using a b by (simp add: green_gram_matrix_def)
    finally show "map_mat real_of_int (green_gram_matrix d I f ks) $$ (a,b) =
      (let M = ?M in M * M\<^sup>T) $$ (a,b)" by simp
  qed
qed

lemma green_gram_determinant_nonzero:
  assumes distinct: "distinct ks"
    and positive: "\<And>c. (\<exists>k\<in>set ks. c k \<noteq> 0) \<Longrightarrow>
      0 < green_gram_form d I f (set ks) c"
  shows "green_gram_determinant d I f ks \<noteq> 0"
proof
  let ?n = "length ks"
  let ?A = "map_mat real_of_int (green_gram_matrix d I f ks)"
  assume zero: "green_gram_determinant d I f ks = 0"
  have A: "?A \<in> carrier_mat ?n ?n" by simp
  have dimA: "dim_row ?A = ?n" "dim_col ?A = ?n"
    by (simp_all add: green_gram_matrix_def)
  have "det ?A = of_int (green_gram_determinant d I f ks)"
    using green_gram_determinant_real[of d I f ks] by simp
  also have "... = 0" using zero by simp
  finally have detA: "det ?A = 0" .
  then obtain v :: "real vec" where
    v: "v \<in> carrier_vec ?n" "v \<noteq> 0\<^sub>v ?n" "?A *\<^sub>v v = 0\<^sub>v ?n"
    using det_0_iff_vec_prod_zero_field[OF A] by blast
  let ?c = "\<lambda>k. \<Sum>j<?n. if ks ! j = k then v $ j else 0"
  have c_index: "?c (ks ! i) = v $ i" if i: "i < ?n" for i
  proof -
    have "?c (ks ! i) = (\<Sum>j<?n. if j = i then v $ j else 0)"
      by (rule sum.cong) (use nth_eq_iff_index_eq[OF distinct] i in auto)
    then show ?thesis using i by simp
  qed
  have nonzero: "\<exists>k\<in>set ks. ?c k \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (\<exists>k\<in>set ks. ?c k \<noteq> 0)"
    then have vi: "v $ i = 0" if "i < ?n" for i
      using c_index[OF that] that by simp
    have "v = 0\<^sub>v ?n"
      by (rule eq_vecI) (use v(1) vi in auto)
    with v(2) show False by contradiction
  qed
  have reindex: "(\<Sum>k\<in>set ks. h k) = (\<Sum>i<?n. h (ks ! i))"
    for h
    by (simp add: sum_list_distinct_conv_sum_set[OF distinct, symmetric]
      sum_list_sum_nth atLeast0LessThan)
  have A_entry: "?A $$ (i,j) =
      real_of_int (green_gram_entry d I f (ks ! i) (ks ! j))"
    if "i < ?n" "j < ?n" for i j
    using that by (simp add: green_gram_matrix_def)
  have form:
    "green_gram_form d I f (set ks) ?c =
      (\<Sum>i<?n. \<Sum>j<?n.
        v $ i * v $ j * ?A $$ (i,j))"
    unfolding green_gram_form_def
    by (simp add: reindex c_index A_entry)
  have row_zero: "(\<Sum>j<?n. ?A $$ (i,j) * v $ j) = 0"
    if i: "i < ?n" for i
  proof -
    have " (?A *\<^sub>v v) $ i = 0"
      using v(3) i by simp
    then show ?thesis
      using i v(1) dimA by (simp add: scalar_prod_def atLeast0LessThan)
  qed
  have each_zero: "(\<Sum>j<?n. v $ i * v $ j * ?A $$ (i,j)) = 0"
    if i: "i < ?n" for i
  proof -
    have "(\<Sum>j<?n. v $ i * v $ j * ?A $$ (i,j)) =
      v $ i * (\<Sum>j<?n. ?A $$ (i,j) * v $ j)"
      by (simp add: sum_distrib_left algebra_simps)
    also have "... = 0" using row_zero[OF i] by simp
    finally show ?thesis .
  qed
  have "green_gram_form d I f (set ks) ?c = 0"
    unfolding form using each_zero by simp
  moreover have "0 < green_gram_form d I f (set ks) ?c"
    by (rule positive[OF nonzero])
  ultimately show False by simp
qed

lemma green_submatrix_transpose:
  "submatrix (M\<^sup>T) J UNIV = (submatrix M UNIV J)\<^sup>T"
proof -
  have bound: "pick J i < dim_col M"
    if i: "i < card {j. j < dim_col M \<and> j \<in> J}" for i
  proof -
    have "pick J i = pick {j. j < dim_col M \<and> j \<in> J} i"
      by (rule pick_reduce_set[OF i])
    also have "... \<in> {j. j < dim_col M \<and> j \<in> J}"
      by (rule pick_in_set_le[OF i])
    finally show ?thesis by simp
  qed
  show ?thesis
  proof (rule eq_matI)
    show "dim_row (submatrix (M\<^sup>T) J UNIV) =
      dim_row ((submatrix M UNIV J)\<^sup>T)"
      by (simp add: submatrix_def)
    show "dim_col (submatrix (M\<^sup>T) J UNIV) =
      dim_col ((submatrix M UNIV J)\<^sup>T)"
      by (simp add: submatrix_def)
    fix i j
    assume ij: "i < dim_row ((submatrix M UNIV J)\<^sup>T)"
      "j < dim_col ((submatrix M UNIV J)\<^sup>T)"
    have i: "i < card {x. x < dim_col M \<and> x \<in> J}"
      using ij by (simp add: submatrix_def)
    have j: "j < dim_row M"
      using ij by (simp add: submatrix_def)
    show "submatrix (M\<^sup>T) J UNIV $$ (i,j) =
      (submatrix M UNIV J)\<^sup>T $$ (i,j)"
      using i j bound[OF i]
      by (simp add: submatrix_def pick_UNIV)
  qed
qed

lemma green_real_gram_determinant_as_sum_squares:
  fixes M :: "real mat"
  shows "det (M * M\<^sup>T) =
    (\<Sum>J\<in>{J. J \<subseteq> {0..<dim_col M} \<and> card J = dim_row M}.
      (det (submatrix M UNIV J))\<^sup>2)"
proof -
  let ?n = "dim_row M"
  let ?m = "dim_col M"
  let ?S = "{J. J \<subseteq> {0..< ?m} \<and> card J = ?n}"
  have A: "M \<in> carrier_mat ?n ?m" by simp
  have B: "M\<^sup>T \<in> carrier_mat ?m ?n" by simp
  have cb: "det (M * M\<^sup>T) =
    (\<Sum>J\<in>?S. det (submatrix M UNIV J) *
      det (submatrix (M\<^sup>T) J UNIV))"
    by (rule Cauchy_Binet[OF A B])
  have square_term: "det (submatrix M UNIV J) *
      det (submatrix (M\<^sup>T) J UNIV) =
      (det (submatrix M UNIV J))\<^sup>2"
    if J: "J \<in> ?S" for J
  proof -
    have Jset: "{j. j < ?m \<and> j \<in> J} = J"
      using J by auto
    have square: "submatrix M UNIV J \<in> carrier_mat ?n ?n"
      using J by (simp add: submatrix_def Jset)
    have "det (submatrix (M\<^sup>T) J UNIV) =
      det (submatrix M UNIV J)"
      by (simp add: green_submatrix_transpose Determinant.det_transpose[OF square])
    then show ?thesis by (simp add: power2_eq_square)
  qed
  show ?thesis unfolding cb
    by (rule sum.cong) (auto intro: square_term)
qed

lemma green_real_gram_determinant_nonnegative:
  fixes M :: "real mat"
  shows "0 \<le> det (M * M\<^sup>T)"
  unfolding green_real_gram_determinant_as_sum_squares
  by (rule sum_nonneg) simp

lemma green_real_gram_nonzero_minor:
  fixes M :: "real mat"
  assumes nonzero: "det (M * M\<^sup>T) \<noteq> 0"
  obtains J where "J \<subseteq> {0..<dim_col M}"
    "card J = dim_row M"
    "det (submatrix M UNIV J) \<noteq> 0"
proof -
  let ?S = "{J. J \<subseteq> {0..<dim_col M} \<and> card J = dim_row M}"
  have "\<exists>J\<in>?S. det (submatrix M UNIV J) \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (\<exists>J\<in>?S. det (submatrix M UNIV J) \<noteq> 0)"
    then have "(\<Sum>J\<in>?S. (det (submatrix M UNIV J))\<^sup>2) = 0"
      by simp
    with nonzero show False
      by (simp add: green_real_gram_determinant_as_sum_squares)
  qed
  then show ?thesis using that by blast
qed

lemma green_gram_determinant_nonnegative:
  assumes finiteI: "finite I"
  shows "0 \<le> green_gram_determinant d I f ks"
proof -
  obtain idxs where idxs: "distinct idxs" "set idxs = I"
    using finiteI finite_distinct_list by blast
  let ?M = "mat_of_rows (2 * length idxs)
    (map (green_gram_feature d idxs f) ks)"
  have "of_int (green_gram_determinant d I f ks) =
    det (?M * ?M\<^sup>T)"
    by (simp add: Let_def green_gram_determinant_real
      green_gram_matrix_as_real_gram[OF idxs])
  moreover have "0 \<le> det (?M * ?M\<^sup>T)"
    by (rule green_real_gram_determinant_nonnegative)
  ultimately show ?thesis by simp
qed

lemma (in green_quadratic_character) green_paper_gram_determinant_positive:
  assumes even: "even cparam" and cparam: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
  shows "0 < green_row_gram_determinant d
    (diagonal_grid (cpx_sqrt d) (natural_grid (green_N q cparam)))
    (green_J q cparam) (green_X q cparam) (green_J q cparam)"
proof -
  let ?P = "diagonal_grid (cpx_sqrt d) (natural_grid (green_N q cparam))"
  let ?J = "green_J q cparam"
  let ?R = "green_X q cparam"
  let ?ks = "green_row_order ?R ?J"
  have finiteP: "finite ?P"
    by (simp add: diagonal_grid_def natural_grid_finite)
  have nonzero: "green_gram_determinant d (?P \<times> {..< ?J})
    (green_row_gram_coeff d) ?ks \<noteq> 0"
  proof (rule green_gram_determinant_nonzero)
    show "distinct ?ks" by simp
    fix c :: "nat \<times> nat \<Rightarrow> real"
    assume "\<exists>k\<in>set ?ks. c k \<noteq> 0"
    then have "\<exists>k\<in>green_row_indices ?R ?J. c k \<noteq> 0"
      by simp
    from green_paper_gram_form_positive[OF even cparam large this]
    show "0 < green_gram_form d (?P \<times> {..< ?J})
      (green_row_gram_coeff d) (set ?ks) c"
      by (simp add: green_row_gram_form_def)
  qed
  have nonnegative: "0 \<le> green_gram_determinant d
    (?P \<times> {..< ?J}) (green_row_gram_coeff d) ?ks"
    by (rule green_gram_determinant_nonnegative) (use finiteP in simp)
  show ?thesis
    using nonzero nonnegative
    by (simp add: green_row_gram_determinant_def)
qed

end
