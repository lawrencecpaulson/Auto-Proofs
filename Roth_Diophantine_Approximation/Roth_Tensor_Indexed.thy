theory Roth_Tensor_Indexed
  imports Roth_Tensor_Wronskian
begin

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
