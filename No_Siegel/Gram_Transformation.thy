theory Gram_Transformation
  imports Inert_Rows
begin

declare [[apply_timeout = 20]]

lemma green_bilinear_double_sum:
  fixes alpha beta :: "nat \<Rightarrow> int"
    and x y :: "nat \<Rightarrow> 'i \<Rightarrow> int"
  shows "(\<Sum>t\<in>I. (\<Sum>c<n. alpha c * x c t) *
      (\<Sum>e<n. beta e * y e t)) =
    (\<Sum>c<n. \<Sum>e<n. alpha c * beta e *
      (\<Sum>t\<in>I. x c t * y e t))"
proof -
  have point: "(\<Sum>c<n. alpha c * x c t) *
      (\<Sum>e<n. beta e * y e t) =
      (\<Sum>c<n. \<Sum>e<n. alpha c * beta e * (x c t * y e t))"
    for t
  proof -
    have "(\<Sum>c<n. alpha c * x c t) *
        (\<Sum>e<n. beta e * y e t) =
        (\<Sum>c<n. (alpha c * x c t) *
          (\<Sum>e<n. beta e * y e t))"
      by (simp only: sum_distrib_right)
    also have "... = (\<Sum>c<n. \<Sum>e<n.
        (alpha c * x c t) * (beta e * y e t))"
      by (simp only: sum_distrib_left)
    also have "... = (\<Sum>c<n. \<Sum>e<n.
        alpha c * beta e * (x c t * y e t))"
      by (intro sum.cong) (auto simp: algebra_simps)
    finally show ?thesis .
  qed
  have "(\<Sum>t\<in>I. (\<Sum>c<n. alpha c * x c t) *
      (\<Sum>e<n. beta e * y e t)) =
    (\<Sum>t\<in>I. \<Sum>c<n. \<Sum>e<n.
      alpha c * beta e * (x c t * y e t))"
    by (rule sum.cong[OF refl]) (rule point)
  also have "... = (\<Sum>c<n. \<Sum>t\<in>I. \<Sum>e<n.
      alpha c * beta e * (x c t * y e t))"
    by (rule sum.swap)
  also have "... = (\<Sum>c<n. \<Sum>e<n. \<Sum>t\<in>I.
      alpha c * beta e * (x c t * y e t))"
    by (rule sum.cong[OF refl]) (rule sum.swap)
  also have "... = (\<Sum>c<n. \<Sum>e<n.
      alpha c * beta e * (\<Sum>t\<in>I. x c t * y e t))"
    by (intro sum.cong) (auto simp: sum_distrib_left)
  finally show ?thesis .
qed

lemma green_gram_entry_linear_transform:
  fixes U :: "int mat"
    and f f' :: "nat \<Rightarrow> 'i \<Rightarrow> int \<times> int"
  assumes left: "\<And>t. t \<in> I \<Longrightarrow>
      fst (f' a t) = (\<Sum>c<n. U $$ (a,c) * fst (f c t))"
    "\<And>t. t \<in> I \<Longrightarrow>
      snd (f' a t) = (\<Sum>c<n. U $$ (a,c) * snd (f c t))"
    and right: "\<And>t. t \<in> I \<Longrightarrow>
      fst (f' b t) = (\<Sum>e<n. U $$ (b,e) * fst (f e t))"
    "\<And>t. t \<in> I \<Longrightarrow>
      snd (f' b t) = (\<Sum>e<n. U $$ (b,e) * snd (f e t))"
  shows "green_gram_entry d I f' a b =
    (\<Sum>c<n. \<Sum>e<n. U $$ (a,c) * U $$ (b,e) *
      green_gram_entry d I f c e)"
proof -
  have coordinate:
    "(\<Sum>t\<in>I. q (f' a t) * q (f' b t)) =
      (\<Sum>c<n. \<Sum>e<n. U $$ (a,c) * U $$ (b,e) *
        (\<Sum>t\<in>I. q (f c t) * q (f e t)))"
    if qa: "\<And>t. t \<in> I \<Longrightarrow>
        q (f' a t) = (\<Sum>c<n. U $$ (a,c) * q (f c t))"
      and qb: "\<And>t. t \<in> I \<Longrightarrow>
        q (f' b t) = (\<Sum>e<n. U $$ (b,e) * q (f e t))"
    for q :: "int \<times> int \<Rightarrow> int"
  proof -
    have shifted:
      "(\<Sum>t\<in>I. q (f' a t) * q (f' b t)) =
        (\<Sum>t\<in>I. (\<Sum>c<n. U $$ (a,c) * q (f c t)) *
          (\<Sum>e<n. U $$ (b,e) * q (f e t)))"
      by (rule sum.cong[OF refl]) (use qa qb in simp)
    show ?thesis
      unfolding shifted by (rule green_bilinear_double_sum)
  qed
  have xx: "(\<Sum>t\<in>I. fst (f' a t) * fst (f' b t)) =
    (\<Sum>c<n. \<Sum>e<n. U $$ (a,c) * U $$ (b,e) *
      (\<Sum>t\<in>I. fst (f c t) * fst (f e t)))"
    by (rule coordinate[OF left(1) right(1)])
  have yy: "(\<Sum>t\<in>I. snd (f' a t) * snd (f' b t)) =
    (\<Sum>c<n. \<Sum>e<n. U $$ (a,c) * U $$ (b,e) *
      (\<Sum>t\<in>I. snd (f c t) * snd (f e t)))"
    by (rule coordinate[OF left(2) right(2)])
  have entry: "green_gram_entry d I f c e =
      2 * ((\<Sum>t\<in>I. fst (f c t) * fst (f e t)) +
        abs d * (\<Sum>t\<in>I. snd (f c t) * snd (f e t)))"
    for c e
    by (simp add: green_gram_entry_def green_quad_coeff_pair_def
      sum.distrib sum_distrib_left algebra_simps)
  have entry': "green_gram_entry d I f' a b =
      2 * ((\<Sum>t\<in>I. fst (f' a t) * fst (f' b t)) +
        abs d * (\<Sum>t\<in>I. snd (f' a t) * snd (f' b t)))"
    by (simp add: green_gram_entry_def green_quad_coeff_pair_def
      sum.distrib sum_distrib_left algebra_simps)
  show ?thesis
    unfolding entry' xx yy
    by (simp add: entry sum.distrib sum_distrib_left algebra_simps)
qed

lemma green_matrix_mult_entry:
  fixes A B :: "int mat"
  assumes A: "A \<in> carrier_mat m n"
    and B: "B \<in> carrier_mat n r"
    and i: "i < m" and j: "j < r"
  shows "(A*B) $$ (i,j) = (\<Sum>k<n. A $$ (i,k) * B $$ (k,j))"
proof -
  have ar: "dim_row A = m" and ac: "dim_col A = n"
    using A unfolding carrier_mat_def by auto
  have br: "dim_row B = n" and bc: "dim_col B = r"
    using B unfolding carrier_mat_def by auto
  have dot: "(A*B) $$ (i,j) = row A i \<bullet> col B j"
    using ar bc i j by simp
  have cv: "dim_vec (col B j) = n" using br by simp
  have sum0: "row A i \<bullet> col B j =
      (\<Sum>k=0..<n. row A i $ k * col B j $ k)"
    unfolding scalar_prod_def cv by simp
  have sum: "row A i \<bullet> col B j =
      (\<Sum>k<n. A $$ (i,k) * B $$ (k,j))"
    unfolding sum0
    using ar ac br bc i j
    by (simp add: atLeast0LessThan)
  show ?thesis using dot sum by simp
qed

lemma green_matrix_congruence_entry:
  fixes U G :: "int mat"
  assumes U: "U \<in> carrier_mat n n"
    and G: "G \<in> carrier_mat n n"
    and a: "a < n" and b: "b < n"
  shows "(U*G*transpose_mat U) $$ (a,b) =
    (\<Sum>c<n. \<Sum>e<n. U $$ (a,c) * U $$ (b,e) * G $$ (c,e))"
proof -
  have UG: "U*G \<in> carrier_mat n n" using U G by simp
  have UT: "transpose_mat U \<in> carrier_mat n n" using U by simp
  have first0: "(U*G*transpose_mat U) $$ (a,b) =
      (\<Sum>e<n. (U*G) $$ (a,e) * (transpose_mat U) $$ (e,b))"
    by (rule green_matrix_mult_entry[OF UG UT a b])
  have first: "(U*G*transpose_mat U) $$ (a,b) =
      (\<Sum>e<n. (U*G) $$ (a,e) * U $$ (b,e))"
    unfolding first0
    by (rule sum.cong[OF refl]) (use U b in auto)
  have second: "(U*G) $$ (a,e) =
      (\<Sum>c<n. U $$ (a,c) * G $$ (c,e))" if "e < n" for e
    by (rule green_matrix_mult_entry[OF U G a that])
  have "(U*G*transpose_mat U) $$ (a,b) =
      (\<Sum>e<n. (\<Sum>c<n. U $$ (a,c) * G $$ (c,e)) * U $$ (b,e))"
    unfolding first by (rule sum.cong[OF refl]) (use second in auto)
  also have "... = (\<Sum>e<n. \<Sum>c<n.
      (U $$ (a,c) * G $$ (c,e)) * U $$ (b,e))"
    by (simp only: sum_distrib_right)
  also have "... = (\<Sum>e<n. \<Sum>c<n.
      U $$ (a,c) * U $$ (b,e) * G $$ (c,e))"
    by (intro sum.cong) (auto simp: mult_ac)
  also have "... = (\<Sum>c<n. \<Sum>e<n.
      U $$ (a,c) * U $$ (b,e) * G $$ (c,e))"
    by (rule sum.swap)
  finally show ?thesis .
qed

lemma green_indexed_gram_matrix_congruence:
  fixes U :: "int mat"
    and f f' :: "nat \<Rightarrow> 'i \<Rightarrow> int \<times> int"
  assumes U: "U \<in> carrier_mat n n"
    and fst: "\<And>a t. a < n \<Longrightarrow> t \<in> I \<Longrightarrow>
      fst (f' a t) = (\<Sum>c<n. U $$ (a,c) * fst (f c t))"
    and snd: "\<And>a t. a < n \<Longrightarrow> t \<in> I \<Longrightarrow>
      snd (f' a t) = (\<Sum>c<n. U $$ (a,c) * snd (f c t))"
  shows "green_gram_matrix d I f' [0..<n] =
    U * green_gram_matrix d I f [0..<n] * transpose_mat U"
proof -
  let ?G = "green_gram_matrix d I f [0..<n]"
  let ?G' = "green_gram_matrix d I f' [0..<n]"
  have G0: "?G \<in> carrier_mat (length [0..<n]) (length [0..<n])"
    by (rule green_gram_matrix_carrier)
  have G: "?G \<in> carrier_mat n n"
    using G0 by (simp only: length_upt diff_zero)
  have G'0: "?G' \<in> carrier_mat (length [0..<n]) (length [0..<n])"
    by (rule green_gram_matrix_carrier)
  have G': "?G' \<in> carrier_mat n n"
    using G'0 by (simp only: length_upt diff_zero)
  have UG: "U * ?G \<in> carrier_mat n n" using U G by simp
  have UT: "transpose_mat U \<in> carrier_mat n n" using U by simp
  have rhs: "U * ?G * transpose_mat U \<in> carrier_mat n n"
    using UG UT by simp
  show ?thesis
  proof (rule eq_matI)
    fix a b
    assume a: "a < dim_row (U * ?G * transpose_mat U)"
      and b: "b < dim_col (U * ?G * transpose_mat U)"
    have an: "a < n" and bn: "b < n"
      using a b rhs unfolding carrier_mat_def by auto
    have left: "?G' $$ (a,b) = green_gram_entry d I f' a b"
      using an bn by (simp add: green_gram_matrix_entry)
    have entry: "green_gram_entry d I f' a b =
      (\<Sum>c<n. \<Sum>e<n. U $$ (a,c) * U $$ (b,e) *
        green_gram_entry d I f c e)"
      by (rule green_gram_entry_linear_transform)
        (use fst[OF an] snd[OF an] fst[OF bn] snd[OF bn] in auto)
    have right: "(U * ?G * transpose_mat U) $$ (a,b) =
      (\<Sum>c<n. \<Sum>e<n. U $$ (a,c) * U $$ (b,e) *
        green_gram_entry d I f c e)"
      unfolding green_matrix_congruence_entry[OF U G an bn]
      by (intro sum.cong; simp add: green_gram_matrix_entry)
    show "?G' $$ (a,b) =
      (U * ?G * transpose_mat U) $$ (a,b)"
      using left entry right by simp
  next
    show "dim_row ?G' = dim_row (U * ?G * transpose_mat U)"
      using G' rhs unfolding carrier_mat_def by auto
  next
    show "dim_col ?G' = dim_col (U * ?G * transpose_mat U)"
      using G' rhs unfolding carrier_mat_def by auto
  qed
qed

lemma green_indexed_gram_determinant_congruence:
  fixes U :: "int mat"
    and f f' :: "nat \<Rightarrow> 'i \<Rightarrow> int \<times> int"
  assumes U: "U \<in> carrier_mat n n"
    and fst: "\<And>a t. a < n \<Longrightarrow> t \<in> I \<Longrightarrow>
      fst (f' a t) = (\<Sum>c<n. U $$ (a,c) * fst (f c t))"
    and snd: "\<And>a t. a < n \<Longrightarrow> t \<in> I \<Longrightarrow>
      snd (f' a t) = (\<Sum>c<n. U $$ (a,c) * snd (f c t))"
    and determinant: "det U = 1"
  shows "green_gram_determinant d I f' [0..<n] =
    green_gram_determinant d I f [0..<n]"
proof -
  let ?G = "green_gram_matrix d I f [0..<n]"
  have G0: "?G \<in> carrier_mat (length [0..<n]) (length [0..<n])"
    by (rule green_gram_matrix_carrier)
  have G: "?G \<in> carrier_mat n n"
    using G0 by (simp only: length_upt diff_zero)
  have UT: "transpose_mat U \<in> carrier_mat n n" using U by simp
  have UG: "U*?G \<in> carrier_mat n n" using U G by simp
  have "green_gram_determinant d I f' [0..<n] =
      det (U*?G*transpose_mat U)"
    by (simp add: green_gram_determinant_def
      green_indexed_gram_matrix_congruence[OF U fst snd])
  also have "... = det U * det ?G * det (transpose_mat U)"
    by (simp only: Determinant.det_mult[OF UG UT]
      Determinant.det_mult[OF U G])
  also have "... = det ?G"
    by (simp add: Determinant.det_transpose[OF U] determinant)
  finally show ?thesis
    by (simp add: green_gram_determinant_def)
qed

lemma green_gram_matrix_reindex_nth:
  "green_gram_matrix d I (\<lambda>a t. f (ks ! a) t)
      [0..<length ks] = green_gram_matrix d I f ks"
proof (rule eq_matI)
  fix a b
  assume a: "a < dim_row (green_gram_matrix d I f ks)"
    and b: "b < dim_col (green_gram_matrix d I f ks)"
  have al: "a < length ks" and bl: "b < length ks"
    using a b by (auto simp: green_gram_matrix_def)
  have al': "a < length [0..<length ks]" using al by simp
  have bl': "b < length [0..<length ks]" using bl by simp
  have left: "green_gram_matrix d I (\<lambda>a t. f (ks ! a) t)
      [0..<length ks] $$ (a,b) =
    green_gram_entry d I f (ks ! a) (ks ! b)"
  proof -
    have entry: "green_gram_matrix d I (\<lambda>a t. f (ks ! a) t)
        [0..<length ks] $$ (a,b) =
      green_gram_entry d I (\<lambda>a t. f (ks ! a) t)
        ([0..<length ks] ! a) ([0..<length ks] ! b)"
      by (rule green_gram_matrix_entry[OF al' bl'])
    show ?thesis using entry al bl
      by (simp add: green_gram_entry_def)
  qed
  have right: "green_gram_matrix d I f ks $$ (a,b) =
    green_gram_entry d I f (ks ! a) (ks ! b)"
    by (rule green_gram_matrix_entry[OF al bl])
  show "green_gram_matrix d I (\<lambda>a t. f (ks ! a) t)
      [0..<length ks] $$ (a,b) =
    green_gram_matrix d I f ks $$ (a,b)"
    using left right by simp
next
  show "dim_row (green_gram_matrix d I (\<lambda>a t. f (ks ! a) t)
      [0..<length ks]) = dim_row (green_gram_matrix d I f ks)"
    by (simp add: green_gram_matrix_def)
next
  show "dim_col (green_gram_matrix d I (\<lambda>a t. f (ks ! a) t)
      [0..<length ks]) = dim_col (green_gram_matrix d I f ks)"
    by (simp add: green_gram_matrix_def)
qed

lemma green_gram_determinant_reindex_nth:
  "green_gram_determinant d I (\<lambda>a t. f (ks ! a) t)
      [0..<length ks] = green_gram_determinant d I f ks"
  by (simp add: green_gram_determinant_def
    green_gram_matrix_reindex_nth)

declare [[apply_timeout = 0]]

end
