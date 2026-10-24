theory Tensor_Indexed
  imports
    Tensor_Determinant
begin

section \<open>Tensor determinant factorization\<close>

lemma roth_hasse_tensor_entry:
  fixes \<mu> :: "(nat,nat) poly_mapping"
    and \<phi> \<psi> :: "nat \<Rightarrow> rat mpoly"
  assumes mi: "Poly_Mapping.keys \<mu> \<subseteq> {..<n}"
    and pv: "\<And>l. l<k \<Longrightarrow> vars (\<phi> l) \<subseteq> {..<n}"
    and qv: "\<And>l. l<k \<Longrightarrow> vars (\<psi> l) \<subseteq> {n}"
  shows "roth_hasse (\<mu> + Poly_Mapping.single n j)
    (\<Sum>l<k. \<phi> l * \<psi> l) =
    (\<Sum>l<k. roth_hasse \<mu> (\<phi> l) *
      roth_hasse (Poly_Mapping.single n j) (\<psi> l))"
  by (simp add: roth_hasse_sum
    roth_hasse_disjoint_product[OF mi] pv qv)

lemma roth_tensor_matrix_product:
  fixes \<mu> :: "nat \<Rightarrow> (nat,nat) poly_mapping"
    and \<phi> \<psi> :: "nat \<Rightarrow> rat mpoly"
  assumes mi: "\<And>i. i<k \<Longrightarrow>
      Poly_Mapping.keys (\<mu> i) \<subseteq> {..<n}"
    and pv: "\<And>l. l<k \<Longrightarrow> vars (\<phi> l) \<subseteq> {..<n}"
    and qv: "\<And>l. l<k \<Longrightarrow> vars (\<psi> l) \<subseteq> {n}"
  shows "mat k k (\<lambda>(i,j).
      roth_hasse (\<mu> i + Poly_Mapping.single n j)
        (\<Sum>l<k. \<phi> l * \<psi> l)) =
    mat k k (\<lambda>(i,l). roth_hasse (\<mu> i) (\<phi> l)) *
    mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (\<psi> l))"
  by (auto simp: mat_eq_iff scalar_prod_def atLeast0LessThan
    roth_hasse_tensor_entry[OF _ pv qv] mi)

lemma roth_det_mat_mult:
  fixes A B :: "nat \<times> nat \<Rightarrow> rat mpoly"
  shows "det (mat k k A * mat k k B) =
    det (mat k k A) * det (mat k k B)"
  by (rule det_mult[where n=k]) simp_all

lemma roth_det_mat_product:
  fixes C :: "rat mpoly mat"
    and A B :: "nat \<times> nat \<Rightarrow> rat mpoly"
  assumes eq: "C = mat k k A * mat k k B"
  shows "det C = det (mat k k A) * det (mat k k B)"
  using arg_cong[OF eq, of det] roth_det_mat_mult[of k A B]
  by simp

theorem roth_tensor_det_factorization:
  fixes \<mu> :: "nat \<Rightarrow> (nat,nat) poly_mapping"
    and \<phi> \<psi> :: "nat \<Rightarrow> rat mpoly"
  assumes mi: "\<And>i. i<k \<Longrightarrow>
      Poly_Mapping.keys (\<mu> i) \<subseteq> {..<n}"
    and pv: "\<And>l. l<k \<Longrightarrow> vars (\<phi> l) \<subseteq> {..<n}"
    and qv: "\<And>l. l<k \<Longrightarrow> vars (\<psi> l) \<subseteq> {n}"
  shows "det (mat k k (\<lambda>(i,j).
      roth_hasse (\<mu> i + Poly_Mapping.single n j)
        (\<Sum>l<k. \<phi> l * \<psi> l))) =
    det (mat k k (\<lambda>(i,l).
      roth_hasse (\<mu> i) (\<phi> l))) *
    det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (\<psi> l)))"
  by (rule roth_det_mat_product)
    (rule roth_tensor_matrix_product[OF mi pv qv])

section \<open>The final-variable Wronskian\<close>

lemma roth_univariate_hasse_at:
  fixes p :: "rat poly"
  shows "mpoly_to_poly v
    (roth_hasse (Poly_Mapping.single v k) (poly_to_mpoly v p)) =
    roth_hderiv k p"
  by (rule poly_eqI)
    (simp add: roth_univariate_hasse_coeff)

lemma roth_hasse_to_hderiv_at:
  fixes \<psi> :: "rat mpoly"
  assumes qv: "vars \<psi> \<subseteq> {v}"
  shows "mpoly_to_poly v
    (roth_hasse (Poly_Mapping.single v k) \<psi>) =
    roth_hderiv k (mpoly_to_poly v \<psi>)"
  using roth_univariate_hasse_at
    [of v k "mpoly_to_poly v \<psi>"]
    mpoly_to_poly_inverse[OF qv] by simp

lemma roth_right_entry_eval:
  fixes \<psi> :: "rat mpoly"
  assumes qv: "vars \<psi> \<subseteq> {n}"
  shows "insertion (\<lambda>_. t)
    (roth_hasse (Poly_Mapping.single n j) \<psi>) =
    poly (roth_hderiv j (mpoly_to_poly n \<psi>)) t"
proof -
  have hv: "vars (roth_hasse
      (Poly_Mapping.single n j) \<psi>) \<subseteq> {n}"
    using roth_hasse_vars_subset qv by auto
  have eq: "poly (mpoly_to_poly n
      (roth_hasse (Poly_Mapping.single n j) \<psi>)) t =
    insertion (\<lambda>_. t)
      (roth_hasse (Poly_Mapping.single n j) \<psi>)"
    by (rule poly_eq_insertion[OF hv])
  show ?thesis
    using eq roth_hasse_to_hderiv_at[OF qv] by simp
qed

lemma roth_right_eval_matrix:
  fixes \<psi> :: "nat \<Rightarrow> rat mpoly"
  assumes qv: "\<And>l. l<k \<Longrightarrow> vars (\<psi> l) \<subseteq> {n}"
  shows "mat k k (\<lambda>(l,j).
      insertion (\<lambda>_. t)
        (roth_hasse (Poly_Mapping.single n j) (\<psi> l))) =
    transpose_mat (mat k k (\<lambda>(j,l).
      poly (roth_hderiv j (mpoly_to_poly n (\<psi> l))) t))"
  by (auto simp: mat_eq_iff roth_right_entry_eval qv)

lemma roth_right_det_eval:
  fixes \<psi> :: "nat \<Rightarrow> rat mpoly"
  assumes qv: "\<And>l. l<k \<Longrightarrow> vars (\<psi> l) \<subseteq> {n}"
  shows "insertion (\<lambda>_. t)
    (det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (\<psi> l)))) =
    poly (roth_hwronskian k
      (\<lambda>l. mpoly_to_poly n (\<psi> l))) t"
  by (simp add: roth_insertion_det
    roth_right_eval_matrix[OF qv] det_transpose[where n=k]
    roth_poly_det roth_hwronskian_def)

theorem roth_right_det_nonzero:
  fixes \<psi> :: "nat \<Rightarrow> rat mpoly"
  assumes qv: "\<And>l. l<k \<Longrightarrow> vars (\<psi> l) \<subseteq> {n}"
    and ind: "roth_poly_indep k
      (\<lambda>l. mpoly_to_poly n (\<psi> l))"
  shows "det (mat k k (\<lambda>(l,j).
    roth_hasse (Poly_Mapping.single n j) (\<psi> l))) \<noteq> 0"
proof -
  have wr: "roth_hwronskian k
    (\<lambda>l. mpoly_to_poly n (\<psi> l)) \<noteq> 0"
    by (rule roth_wr_independent[OF ind])
  obtain t :: rat where nz: "poly (roth_hwronskian k
      (\<lambda>l. mpoly_to_poly n (\<psi> l))) t \<noteq> 0"
    using roth_poly_nonzero_eval[OF wr] by blast
  have ev: "insertion (\<lambda>_. t)
    (det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (\<psi> l)))) =
    poly (roth_hwronskian k
      (\<lambda>l. mpoly_to_poly n (\<psi> l))) t"
    by (rule roth_right_det_eval[OF qv])
  show ?thesis using nz ev by auto
qed

lemma roth_box_vars:
  fixes P :: "rat mpoly"
  assumes "roth_poly_in_box n r P"
  shows "vars P \<subseteq> {..<n}"
  using assms
  by (auto simp: roth_poly_in_box_def vars_def
    dest: roth_exponent_boxD(1))

lemma roth_tensor_box_vars:
  fixes \<phi> :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>l<k. roth_poly_in_box n r (\<phi> l)"
    and lk: "l<k"
  shows "vars (\<phi> l) \<subseteq> {..<n}"
proof -
  have "roth_poly_in_box n r (\<phi> l)"
    using box lk by simp
  then show ?thesis by (rule roth_box_vars)
qed

theorem roth_tensor_det_nonzero:
  fixes \<phi> \<psi> :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>l<k. roth_poly_in_box n r (\<phi> l)"
    and li: "roth_mpoly_indep k \<phi>"
    and qv: "\<And>l. l<k \<Longrightarrow> vars (\<psi> l) \<subseteq> {n}"
    and ri: "roth_poly_indep k
      (\<lambda>l. mpoly_to_poly n (\<psi> l))"
  shows "\<exists>\<mu>.
    (\<forall>i<k. Poly_Mapping.keys (\<mu> i) \<subseteq> {..<n} \<and>
      roth_total_order n (\<mu> i) \<le> i) \<and>
    det (mat k k (\<lambda>(i,j).
      roth_hasse (\<mu> i + Poly_Mapping.single n j)
        (\<Sum>l<k. \<phi> l * \<psi> l))) \<noteq> 0"
proof -
  obtain \<mu> where mb: "\<forall>i<k.
      Poly_Mapping.keys (\<mu> i) \<subseteq> {..<n} \<and>
      roth_total_order n (\<mu> i) \<le> i"
    and lnz: "det (mat k k (\<lambda>(i,l).
      roth_hasse (\<mu> i) (\<phi> l))) \<noteq> 0"
    using roth_generalized_wronskian[OF box li] by auto
  have mn: "\<And>i. i<k \<Longrightarrow>
    Poly_Mapping.keys (\<mu> i) \<subseteq> {..<n}"
    using mb by auto
  have rnz: "det (mat k k (\<lambda>(l,j).
    roth_hasse (Poly_Mapping.single n j) (\<psi> l))) \<noteq> 0"
    by (rule roth_right_det_nonzero[OF qv ri])
  have fac: "det (mat k k (\<lambda>(i,j).
      roth_hasse (\<mu> i + Poly_Mapping.single n j)
        (\<Sum>l<k. \<phi> l * \<psi> l))) =
    det (mat k k (\<lambda>(i,l).
      roth_hasse (\<mu> i) (\<phi> l))) *
    det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (\<psi> l)))"
    by (rule roth_tensor_det_factorization
      [OF mn roth_tensor_box_vars[OF box] qv])
  have nz: "det (mat k k (\<lambda>(i,j).
      roth_hasse (\<mu> i + Poly_Mapping.single n j)
        (\<Sum>l<k. \<phi> l * \<psi> l))) \<noteq> 0"
    using fac lnz rnz by simp
  show ?thesis using mb nz by auto
qed

section \<open>Indexing a finite tensor basis\<close>

lemma roth_set_indep_coeff:
  fixes B :: "rat mpoly set"
  assumes fin: "finite B"
    and ind: "roth_vs.independent B"
    and z: "(\<Sum>b\<in>B. MPoly_Type.smult (c b) b) = 0"
    and b: "b\<in>B"
  shows "c b=0"
  using fin ind z b
  by (auto simp: roth_vs.independent_explicit_finite_subsets)

lemma roth_bij_sum_coeff:
  fixes f :: "nat \<Rightarrow> rat mpoly"
  assumes bij: "bij_betw f {..<k} B"
  shows "(\<Sum>j<k. MPoly_Type.smult (c j) (f j)) =
    (\<Sum>b\<in>B. MPoly_Type.smult
      (c (inv_into {..<k} f b)) b)"
proof -
  have "(\<Sum>j<k. MPoly_Type.smult
      (c (inv_into {..<k} f (f j))) (f j)) =
    (\<Sum>b\<in>B. MPoly_Type.smult
      (c (inv_into {..<k} f b)) b)"
    by (rule sum.reindex_bij_betw[OF bij])
  then show ?thesis using bij by (simp add: bij_betw_def)
qed

lemma roth_indexed_set_indep:
  fixes f :: "nat \<Rightarrow> rat mpoly"
  assumes bij: "bij_betw f {..<k} B"
    and ind: "roth_vs.independent B"
  shows "roth_mpoly_indep k f"
  unfolding roth_mpoly_indep_def
proof (intro allI impI)
  fix c j
  assume z: "(\<Sum>i<k. MPoly_Type.smult (c i) (f i)) = 0"
    and j: "j<k"
  have fin: "finite B" using bij
    by (auto simp: bij_betw_def)
  have zj: "(\<Sum>b\<in>B. MPoly_Type.smult
      (c (inv_into {..<k} f b)) b) = 0"
    using z roth_bij_sum_coeff[OF bij, of c] by simp
  have fj: "f j \<in> B" using bij j
    by (auto simp: bij_betw_def)
  have cz: "c (inv_into {..<k} f (f j)) = 0"
    by (rule roth_set_indep_coeff[OF fin ind zj fj])
  show "c j=0" using cz bij j
    by (simp add: bij_betw_def)
qed

lemma roth_bij_sum_poly_coeff:
  fixes f :: "nat \<Rightarrow> rat mpoly"
    and g :: "rat mpoly \<Rightarrow> rat poly"
  assumes bij: "bij_betw f {..<k} B"
  shows "(\<Sum>j<k. Polynomial.smult (c j) (g (f j))) =
    (\<Sum>b\<in>B. Polynomial.smult
      (c (inv_into {..<k} f b)) (g b))"
proof -
  have "(\<Sum>j<k. Polynomial.smult
      (c (inv_into {..<k} f (f j))) (g (f j))) =
    (\<Sum>b\<in>B. Polynomial.smult
      (c (inv_into {..<k} f b)) (g b))"
    by (rule sum.reindex_bij_betw[OF bij])
  then show ?thesis using bij by (simp add: bij_betw_def)
qed

lemma roth_indexed_right_indep:
  fixes f :: "nat \<Rightarrow> rat mpoly"
  assumes bij: "bij_betw f {..<k} B"
    and sub: "B \<subseteq> roth_last_coeff P n ` {..d}"
    and ind: "roth_vs.independent B"
    and fin: "finite B"
  shows "roth_poly_indep k
    (\<lambda>j. mpoly_to_poly n
      (roth_right_factor P n d B (f j)))"
  unfolding roth_poly_indep_def
proof (intro allI impI)
  fix c j
  assume z: "(\<Sum>i<k. Polynomial.smult (c i)
      (mpoly_to_poly n (roth_right_factor P n d B (f i)))) = 0"
    and j: "j<k"
  have zB: "(\<Sum>b\<in>B. Polynomial.smult
      (c (inv_into {..<k} f b))
      (mpoly_to_poly n (roth_right_factor P n d B b))) = 0"
    using z roth_bij_sum_poly_coeff
      [OF bij, of c
        "\<lambda>b. mpoly_to_poly n (roth_right_factor P n d B b)"]
    by simp
  have fj: "f j\<in>B" using bij j
    by (auto simp: bij_betw_def)
  have cz: "c (inv_into {..<k} f (f j)) = 0"
    by (rule roth_right_factor_univ_indep
      [OF sub ind fin zB fj])
  show "c j=0" using cz bij j
    by (simp add: bij_betw_def)
qed

lemma roth_indexed_tensor_split:
  fixes P :: "rat mpoly"
    and f :: "nat \<Rightarrow> rat mpoly"
  assumes bij: "bij_betw f {..<k} B"
    and spl: "P = (\<Sum>b\<in>B.
      b * roth_right_factor P n d B b)"
  shows "P = (\<Sum>j<k.
    f j * roth_right_factor P n d B (f j))"
  using spl sum.reindex_bij_betw
    [OF bij, of "\<lambda>b.
      b * roth_right_factor P n d B b"]
  by simp

lemma roth_basis_det_nonzero:
  fixes P :: "rat mpoly"
  assumes fin: "finite B"
    and sub: "B \<subseteq> roth_last_coeff P n ` {..r n}"
    and ind: "roth_vs.independent B"
    and boxB: "\<forall>b\<in>B. roth_poly_in_box n r b"
    and spl: "P = (\<Sum>b\<in>B.
      b * roth_right_factor P n (r n) B b)"
  shows "\<exists>\<mu>.
    (\<forall>i<card B.
      Poly_Mapping.keys (\<mu> i) \<subseteq> {..<n} \<and>
      roth_total_order n (\<mu> i) \<le> i) \<and>
    det (mat (card B) (card B) (\<lambda>(i,j).
      roth_hasse (\<mu> i + Poly_Mapping.single n j) P))
      \<noteq> 0"
proof -
  let ?k = "card B"
  let ?f = "from_nat_into B"
  have bij: "bij_betw ?f {..<?k} B"
    by (rule Countable_Set.bij_betw_from_nat_into_finite[OF fin])
  have boxf: "\<forall>l<?k. roth_poly_in_box n r (?f l)"
    using bij boxB by (auto simp: bij_betw_def)
  have li: "roth_mpoly_indep ?k ?f"
    by (rule roth_indexed_set_indep[OF bij ind])
  have qv: "\<And>l. l<?k \<Longrightarrow>
      vars (roth_right_factor P n (r n) B (?f l))
        \<subseteq> {n}"
    by (rule roth_right_factor_vars)
  have ri: "roth_poly_indep ?k
    (\<lambda>l. mpoly_to_poly n
      (roth_right_factor P n (r n) B (?f l)))"
    by (rule roth_indexed_right_indep[OF bij sub ind fin])
  have peq: "P = (\<Sum>l<?k.
    ?f l * roth_right_factor P n (r n) B (?f l))"
    by (rule roth_indexed_tensor_split[OF bij spl])
  have ex: "\<exists>\<mu>.
      (\<forall>i<?k.
        Poly_Mapping.keys (\<mu> i) \<subseteq> {..<n} \<and>
        roth_total_order n (\<mu> i) \<le> i) \<and>
      det (mat ?k ?k (\<lambda>(i,j).
        roth_hasse (\<mu> i + Poly_Mapping.single n j)
          (\<Sum>l<?k.
            ?f l * roth_right_factor P n (r n) B (?f l))))
        \<noteq> 0"
    by (rule roth_tensor_det_nonzero[OF boxf li qv ri])
  show ?thesis using ex peq by simp
qed

theorem roth_box_tensor_det_nonzero:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box (Suc n) r P"
    and nz: "P \<noteq> 0"
  shows "\<exists>k \<mu>.
    0<k \<and> k\<le>Suc (r n) \<and>
    (\<forall>i<k.
      Poly_Mapping.keys (\<mu> i) \<subseteq> {..<n} \<and>
      roth_total_order n (\<mu> i) \<le> i) \<and>
    det (mat k k (\<lambda>(i,j).
      roth_hasse (\<mu> i + Poly_Mapping.single n j) P))
      \<noteq> 0"
proof -
  obtain B where
    sub: "B \<subseteq> roth_last_coeff P n ` {..r n}"
    and ne: "B\<noteq>{}"
    and bd: "card B\<le>Suc (r n)"
    and ind: "roth_vs.independent B"
    and boxB: "\<forall>b\<in>B. roth_poly_in_box n r b"
    and spl: "P = (\<Sum>b\<in>B.
      b * roth_right_factor P n (r n) B b)"
    using roth_tensor_basis_exists[OF box nz] by blast
  have fin: "finite B" using sub
    by (meson finite_subset finite_imageI finite_atMost)
  have pos: "0<card B" using ne fin
    by (simp add: card_gt_0_iff)
  obtain \<mu> where
    mb: "\<forall>i<card B.
      Poly_Mapping.keys (\<mu> i) \<subseteq> {..<n} \<and>
      roth_total_order n (\<mu> i) \<le> i"
    and det: "det (mat (card B) (card B) (\<lambda>(i,j).
      roth_hasse (\<mu> i + Poly_Mapping.single n j) P))
        \<noteq> 0"
    using roth_basis_det_nonzero[OF fin sub ind boxB spl]
    by auto
  show ?thesis using pos bd mb det by auto
qed

end
