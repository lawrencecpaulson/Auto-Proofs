theory Roth_Tensor_Split
  imports Roth_Kronecker_Minor
begin

section \<open>Separating the last variable\<close>

lemma roth_monom_last_split:
  fixes c :: rat
  shows "MPoly_Type.monom I c =
    MPoly_Type.monom (remove_key v I) c *
      MPoly_Type.monom
        (Poly_Mapping.single v (Poly_Mapping.lookup I v)) 1"
  by (simp add: MPoly_Type.mult_monom remove_key_sum)

definition roth_last_coeff ::
  "rat mpoly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rat mpoly"
  where "roth_last_coeff P v e =
    (\<Sum>I\<in>{I\<in>Poly_Mapping.keys (mapping_of P).
        Poly_Mapping.lookup I v = e}.
      MPoly_Type.monom (remove_key v I) (MPoly_Type.coeff P I))"

lemma roth_last_coeff_mul:
  "roth_last_coeff P v e *
      MPoly_Type.monom (Poly_Mapping.single v e) 1 =
    (\<Sum>I\<in>{I\<in>Poly_Mapping.keys (mapping_of P).
        Poly_Mapping.lookup I v = e}.
      MPoly_Type.monom I (MPoly_Type.coeff P I))"
  unfolding roth_last_coeff_def sum_distrib_right
  by (rule sum.cong)
    (auto simp: roth_monom_last_split[symmetric])

lemma roth_last_split_support:
  "P = (\<Sum>e\<in>(\<lambda>I. Poly_Mapping.lookup I v) `
      Poly_Mapping.keys (mapping_of P).
      roth_last_coeff P v e *
        MPoly_Type.monom (Poly_Mapping.single v e) 1)"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of P)"
  let ?T = "(\<lambda>I. Poly_Mapping.lookup I v) ` ?S"
  have group: "(\<Sum>e\<in>?T.
      \<Sum>I\<in>{I\<in>?S. Poly_Mapping.lookup I v=e}.
        MPoly_Type.monom I (MPoly_Type.coeff P I)) =
      (\<Sum>I\<in>?S. MPoly_Type.monom I (MPoly_Type.coeff P I))"
    by (rule sum.group) auto
  show ?thesis using group roth_sum_monom[of P]
    by (simp add: roth_last_coeff_mul)
qed

lemma roth_last_coeff_outside_box:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and vm: "v<m" and er: "r v < e"
  shows "roth_last_coeff P v e = 0"
proof -
  have empty: "{I\<in>Poly_Mapping.keys (mapping_of P).
      Poly_Mapping.lookup I v = e} = {}"
  proof (rule ccontr)
    assume "{I\<in>Poly_Mapping.keys (mapping_of P).
        Poly_Mapping.lookup I v = e} \<noteq> {}"
    then obtain I where I: "I\<in>Poly_Mapping.keys (mapping_of P)"
      and eq: "Poly_Mapping.lookup I v = e"
      by blast
    have mem: "I\<in>roth_exponent_box m r"
      using box I by (auto simp: roth_poly_in_box_def)
    have bd: "Poly_Mapping.lookup I v \<le> r v"
      by (rule roth_exponent_boxD(2)[OF mem vm])
    show False using er bd eq by simp
  qed
  show ?thesis by (simp add: roth_last_coeff_def empty)
qed

lemma roth_last_coeff_not_in_support:
  assumes "e \<notin> (\<lambda>I. Poly_Mapping.lookup I v) `
      Poly_Mapping.keys (mapping_of P)"
  shows "roth_last_coeff P v e = 0"
proof -
  have empty: "{I\<in>Poly_Mapping.keys (mapping_of P).
      Poly_Mapping.lookup I v=e} = {}"
    using assms by auto
  show ?thesis by (simp add: roth_last_coeff_def empty)
qed

lemma roth_last_split_box:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P" and vm: "v<m"
  shows "P = (\<Sum>e\<le>r v.
    roth_last_coeff P v e *
      MPoly_Type.monom (Poly_Mapping.single v e) 1)"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of P)"
  let ?T = "(\<lambda>I. Poly_Mapping.lookup I v) ` ?S"
  have sub: "?T \<subseteq> {..r v}"
  proof
    fix e
    assume "e\<in>?T"
    then obtain I where I: "I\<in>?S"
      and eq: "e=Poly_Mapping.lookup I v" by blast
    have mem: "I\<in>roth_exponent_box m r"
      using box I by (auto simp: roth_poly_in_box_def)
    show "e\<in>{..r v}"
      using roth_exponent_boxD(2)[OF mem vm] eq by simp
  qed
  have ext: "(\<Sum>e\<le>r v.
      roth_last_coeff P v e *
        MPoly_Type.monom (Poly_Mapping.single v e) 1) =
    (\<Sum>e\<in>?T.
      roth_last_coeff P v e *
        MPoly_Type.monom (Poly_Mapping.single v e) 1)"
  proof (rule sum.mono_neutral_right)
    show "finite {..r v}" by simp
    show "?T \<subseteq> {..r v}" by (rule sub)
    show "\<forall>e\<in>{..r v} - ?T.
      roth_last_coeff P v e *
        MPoly_Type.monom (Poly_Mapping.single v e) 1 = 0"
      by (auto simp: roth_last_coeff_not_in_support)
  qed
  show ?thesis using roth_last_split_support[of P v] ext
    by simp
qed

lemma roth_remove_last_box:
  assumes mem: "I \<in> roth_exponent_box (Suc n) r"
  shows "remove_key n I \<in> roth_exponent_box n r"
proof (rule roth_exponent_boxI)
  show "Poly_Mapping.keys (remove_key n I) \<subseteq> {..<n}"
    using roth_exponent_boxD(1)[OF mem]
    by (auto simp: remove_key_keys[symmetric])
  fix v
  assume vn: "v<n"
  have vs: "v<Suc n" using vn by simp
  have bd: "Poly_Mapping.lookup I v \<le> r v"
    by (rule roth_exponent_boxD(2)[OF mem vs])
  show "Poly_Mapping.lookup (remove_key n I) v \<le> r v"
    using vn bd by (simp add: remove_key_lookup when_def)
qed

lemma roth_last_coeff_box:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box (Suc n) r P"
  shows "roth_poly_in_box n r (roth_last_coeff P n e)"
  unfolding roth_last_coeff_def
proof (rule roth_poly_in_box_sum)
  show "finite {I\<in>Poly_Mapping.keys (mapping_of P).
      Poly_Mapping.lookup I n = e}" by simp
  fix I
  assume I: "I\<in>{I\<in>Poly_Mapping.keys (mapping_of P).
      Poly_Mapping.lookup I n = e}"
  have mem: "I\<in>roth_exponent_box (Suc n) r"
    using box I by (auto simp: roth_poly_in_box_def)
  have rem: "remove_key n I \<in> roth_exponent_box n r"
    by (rule roth_remove_last_box[OF mem])
  show "roth_poly_in_box n r
      (MPoly_Type.monom (remove_key n I) (MPoly_Type.coeff P I))"
    by (rule roth_poly_in_box_monom[OF rem])
qed

lemma roth_last_coeff_some_nonzero:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and vm: "v<m" and nz: "P\<noteq>0"
  shows "\<exists>e\<le>r v. roth_last_coeff P v e \<noteq> 0"
proof (rule ccontr)
  assume "\<not> (\<exists>e\<le>r v. roth_last_coeff P v e \<noteq> 0)"
  then have z: "(\<Sum>e\<le>r v.
      roth_last_coeff P v e *
        MPoly_Type.monom (Poly_Mapping.single v e) 1) = 0"
    by simp
  show False using roth_last_split_box[OF box vm] nz z
    by simp
qed

section \<open>Finite coefficient bases\<close>

lemma roth_mpoly_vector_space:
  "vector_space (MPoly_Type.smult :: rat \<Rightarrow> rat mpoly \<Rightarrow> rat mpoly)"
  by unfold_locales
    (simp_all add: MPoly_Type.smult_conv_mult
      MPoly_Type.monom_add MPoly_Type.mult_monom algebra_simps)

interpretation roth_vs: vector_space
  "MPoly_Type.smult :: rat \<Rightarrow> rat mpoly \<Rightarrow> rat mpoly"
  by (rule roth_mpoly_vector_space)

lemma roth_mpoly_finite_basis:
  assumes fin: "finite (S::rat mpoly set)"
  shows "\<exists>B. B \<subseteq> S \<and> roth_vs.independent B \<and>
    S \<subseteq> roth_vs.span B \<and> card B \<le> card S"
proof -
  obtain B where B: "B \<subseteq> S" "roth_vs.independent B"
    "S \<subseteq> roth_vs.span B" "card B = roth_vs.dim S"
    by (rule roth_vs.basis_exists[of S])
  have bd: "card B \<le> card S"
    by (rule card_mono[OF fin B(1)])
  show ?thesis using B(1-3) bd by auto
qed

lemma roth_last_coeff_basis:
  assumes box: "roth_poly_in_box (Suc n) r (P::rat mpoly)"
  shows "\<exists>B. B \<subseteq> roth_last_coeff P n ` {..r n} \<and>
    roth_vs.independent B \<and>
    roth_last_coeff P n ` {..r n} \<subseteq> roth_vs.span B \<and>
    card B \<le> Suc (r n) \<and>
    (\<forall>b\<in>B. roth_poly_in_box n r b)"
proof -
  let ?S = "roth_last_coeff P n ` {..r n}"
  have fin: "finite ?S" by simp
  obtain B where B: "B \<subseteq> ?S" "roth_vs.independent B"
    "?S \<subseteq> roth_vs.span B" "card B \<le> card ?S"
    using roth_mpoly_finite_basis[OF fin] by auto
  have im: "card ?S \<le> Suc (r n)"
    using card_image_le[of "{..r n}" "roth_last_coeff P n"] by simp
  have bd: "card B \<le> Suc (r n)"
    using B(4) im by linarith
  have bx: "\<forall>b\<in>B. roth_poly_in_box n r b"
    using B(1) roth_last_coeff_box[OF box] by auto
  show ?thesis using B(1-3) bd bx by blast
qed

lemma roth_last_coeff_basis_nonempty:
  assumes box: "roth_poly_in_box (Suc n) r (P::rat mpoly)"
    and nz: "P \<noteq> 0"
    and spans: "roth_last_coeff P n ` {..r n} \<subseteq> roth_vs.span B"
  shows "B \<noteq> {}"
proof -
  obtain e where e: "e \<le> r n" "roth_last_coeff P n e \<noteq> 0"
    using roth_last_coeff_some_nonzero[OF box _ nz, of n] by auto
  have mem: "roth_last_coeff P n e \<in> roth_vs.span B"
    using spans e(1) by auto
  show ?thesis using mem e(2) by auto
qed

lemma roth_last_coeff_representation:
  assumes ind: "roth_vs.independent B"
    and spans: "roth_last_coeff P n ` {..r n} \<subseteq> roth_vs.span B"
    and fin: "finite B" and e: "e \<le> r n"
  shows "roth_last_coeff P n e =
    (\<Sum>b\<in>B. MPoly_Type.smult
      (roth_vs.representation B (roth_last_coeff P n e) b) b)"
proof -
  have mem: "roth_last_coeff P n e \<in> roth_vs.span B"
    using spans e by auto
  show ?thesis
    using roth_vs.sum_representation_eq[OF ind mem fin subset_refl] by simp
qed

lemma roth_last_coeff_basis_coordinates:
  assumes sub: "B \<subseteq> roth_last_coeff P n ` {..r n}"
    and ind: "roth_vs.independent B" and b: "b \<in> B"
  shows "\<exists>e\<le>r n. \<forall>c\<in>B.
    roth_vs.representation B (roth_last_coeff P n e) c =
      (if c=b then 1 else 0)"
proof -
  obtain e where e: "e \<le> r n" "roth_last_coeff P n e=b"
    using sub b by auto
  show ?thesis
    using roth_vs.representation_basis[OF ind b] e by auto
qed

lemma roth_smult_monom_move:
  "MPoly_Type.smult (a::rat) (b::rat mpoly) *
    MPoly_Type.monom I 1 = b * MPoly_Type.monom I a"
  by (simp add: MPoly_Type.smult_conv_mult
    MPoly_Type.mult_monom algebra_simps)

lemma roth_tensor_sums_swap:
  "(\<Sum>e\<in>(E::nat set). (\<Sum>b\<in>(B::rat mpoly set).
      MPoly_Type.smult (c e b) b) *
      MPoly_Type.monom (Poly_Mapping.single n e) 1) =
    (\<Sum>b\<in>B. b * (\<Sum>e\<in>E.
      MPoly_Type.monom (Poly_Mapping.single n e) (c e b)))"
proof -
  have "(\<Sum>e\<in>E. (\<Sum>b\<in>B. MPoly_Type.smult (c e b) b) *
      MPoly_Type.monom (Poly_Mapping.single n e) 1) =
    (\<Sum>e\<in>E. \<Sum>b\<in>B. b *
      MPoly_Type.monom (Poly_Mapping.single n e) (c e b))"
    by (rule sum.cong)
      (simp_all only: sum_distrib_right roth_smult_monom_move)
  also have "... = (\<Sum>b\<in>B. \<Sum>e\<in>E. b *
      MPoly_Type.monom (Poly_Mapping.single n e) (c e b))"
    by (rule sum.swap)
  also have "... = (\<Sum>b\<in>B. b * (\<Sum>e\<in>E.
      MPoly_Type.monom (Poly_Mapping.single n e) (c e b)))"
    by (simp only: sum_distrib_left)
  finally show ?thesis .
qed

lemma roth_tensor_basis_split:
  assumes box: "roth_poly_in_box (Suc n) r (P::rat mpoly)"
    and ind: "roth_vs.independent B"
    and spans: "roth_last_coeff P n ` {..r n} \<subseteq> roth_vs.span B"
    and fin: "finite B"
  shows "P = (\<Sum>b\<in>B. b * (\<Sum>e\<le>r n.
    MPoly_Type.monom (Poly_Mapping.single n e)
      (roth_vs.representation B (roth_last_coeff P n e) b)))"
proof -
  have eq: "roth_last_coeff P n e =
    (\<Sum>b\<in>B. MPoly_Type.smult
      (roth_vs.representation B (roth_last_coeff P n e) b) b)"
    if "e\<le>r n" for e
    by (rule roth_last_coeff_representation
      [where B=B and P=P and n=n and r=r and e=e,
        OF ind spans fin that])
  have "P = (\<Sum>e\<le>r n. roth_last_coeff P n e *
      MPoly_Type.monom (Poly_Mapping.single n e) 1)"
    by (rule roth_last_split_box[OF box]) simp
  also have "... = (\<Sum>e\<le>r n. (\<Sum>b\<in>B. MPoly_Type.smult
      (roth_vs.representation B (roth_last_coeff P n e) b) b) *
      MPoly_Type.monom (Poly_Mapping.single n e) 1)"
    by (rule sum.cong) (auto simp: eq)
  also have "... = (\<Sum>b\<in>B. b * (\<Sum>e\<le>r n.
      MPoly_Type.monom (Poly_Mapping.single n e)
        (roth_vs.representation B (roth_last_coeff P n e) b)))"
    by (rule roth_tensor_sums_swap)
  finally show ?thesis .
qed

definition roth_right_factor ::
  "rat mpoly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rat mpoly set \<Rightarrow> rat mpoly \<Rightarrow> rat mpoly"
  where "roth_right_factor P n d B b = (\<Sum>e\<le>d.
    MPoly_Type.monom (Poly_Mapping.single n e)
      (roth_vs.representation B (roth_last_coeff P n e) b))"

lemma roth_single_inj:
  "Poly_Mapping.single n e = Poly_Mapping.single n j \<longleftrightarrow> e=j"
proof safe
  fix e j
  assume h: "Poly_Mapping.single n e = Poly_Mapping.single n j"
  have "Poly_Mapping.lookup (Poly_Mapping.single n e) n =
    Poly_Mapping.lookup (Poly_Mapping.single n j) n"
    using h by simp
  then show "e=j" by (simp add: lookup_single when_def)
qed

lemma roth_single_monom_coeff:
  assumes j: "j\<le>d"
  shows "MPoly_Type.coeff
    (\<Sum>e\<le>d. MPoly_Type.monom (Poly_Mapping.single n e) (c e))
    (Poly_Mapping.single n j) = (c j::rat)"
  by (simp add: roth_coeff_sum More_MPoly_Type.coeff_monom
    when_def roth_single_inj sum.delta j)

lemma roth_right_factor_coeff:
  assumes e: "e\<le>d"
  shows "MPoly_Type.coeff (roth_right_factor P n d B b)
    (Poly_Mapping.single n e) =
    roth_vs.representation B (roth_last_coeff P n e) b"
  by (simp add: roth_right_factor_def roth_single_monom_coeff e)

lemma roth_coeff_smult_sum:
  fixes \<psi> :: "rat mpoly \<Rightarrow> rat mpoly"
  assumes fin: "finite (B::rat mpoly set)"
  shows "MPoly_Type.coeff
    (\<Sum>b\<in>B. MPoly_Type.smult (c b) (\<psi> b)) I =
    (\<Sum>b\<in>B. c b * MPoly_Type.coeff (\<psi> b) I)"
  unfolding roth_coeff_sum[OF fin]
  by (rule sum.cong) (simp_all add: roth_coeff_smult_rat)

lemma roth_sum_coordinate:
  assumes fin: "finite (B::rat mpoly set)" and b: "b\<in>B"
  shows "(\<Sum>u\<in>B. (c u::rat) * (if u=b then 1 else 0)) = c b"
  by (simp add: sum.If_cases fin b if_distrib)

lemma roth_right_factor_indep:
  assumes sub: "B \<subseteq> roth_last_coeff P n ` {..d}"
    and ind: "roth_vs.independent B" and fin: "finite B"
    and z: "(\<Sum>u\<in>B. MPoly_Type.smult (c u)
      (roth_right_factor P n d B u)) = 0"
    and b: "b\<in>B"
  shows "c b = 0"
proof -
  obtain e where e: "e\<le>d" and
    coord: "\<forall>u\<in>B. roth_vs.representation B
      (roth_last_coeff P n e) u = (if u=b then 1 else 0)"
    using roth_last_coeff_basis_coordinates[OF sub ind b] by blast
  have val: "MPoly_Type.coeff
      (\<Sum>u\<in>B. MPoly_Type.smult (c u)
        (roth_right_factor P n d B u))
      (Poly_Mapping.single n e) = c b"
    by (simp add: roth_coeff_smult_sum[OF fin]
      roth_right_factor_coeff[OF e] coord
      roth_sum_coordinate[OF fin b])
  show ?thesis using z val
    by (simp add: MPoly_Type.coeff_def zero_mpoly.rep_eq)
qed

lemma roth_right_factor_inj:
  assumes sub: "B \<subseteq> roth_last_coeff P n ` {..d}"
    and ind: "roth_vs.independent B"
  shows "inj_on (roth_right_factor P n d B) B"
proof (rule inj_onI)
  fix b c
  assume b: "b\<in>B" and c: "c\<in>B" and
    eq: "roth_right_factor P n d B b =
      roth_right_factor P n d B c"
  obtain e where e: "e\<le>d" and
    coord: "\<forall>u\<in>B. roth_vs.representation B
      (roth_last_coeff P n e) u = (if u=b then 1 else 0)"
    using roth_last_coeff_basis_coordinates[OF sub ind b] by blast
  have h: "roth_vs.representation B (roth_last_coeff P n e) b =
    roth_vs.representation B (roth_last_coeff P n e) c"
    using arg_cong[OF eq, of
      "\<lambda>F. MPoly_Type.coeff F (Poly_Mapping.single n e)"]
    by (simp add: roth_right_factor_coeff[OF e])
  show "b=c" using h coord b c by (cases "b=c") auto
qed

lemma roth_right_factor_image_indep:
  assumes sub: "B \<subseteq> roth_last_coeff P n ` {..d}"
    and ind: "roth_vs.independent B" and fin: "finite B"
  shows "roth_vs.independent (roth_right_factor P n d B ` B)"
proof (rule roth_vs.independent_if_scalars_zero)
  show "finite (roth_right_factor P n d B ` B)"
    using fin by simp
  fix c x
  assume z: "(\<Sum>x\<in>roth_right_factor P n d B ` B.
    MPoly_Type.smult (c x) x) = 0"
    and x: "x\<in>roth_right_factor P n d B ` B"
  obtain b where b: "b\<in>B" "x=roth_right_factor P n d B b"
    using x by auto
  have inj: "inj_on (roth_right_factor P n d B) B"
    by (rule roth_right_factor_inj[OF sub ind])
  have zb: "(\<Sum>b\<in>B. MPoly_Type.smult
    (c (roth_right_factor P n d B b))
    (roth_right_factor P n d B b))=0"
    using z by (simp add: sum.reindex[OF inj] comp_def)
  show "c x=0"
    using roth_right_factor_indep[OF sub ind fin zb b(1)] b(2)
    by simp
qed

lemma roth_single_in_box:
  assumes e: "e\<le>r n"
  shows "Poly_Mapping.single n e \<in> roth_exponent_box (Suc n) r"
  by (rule roth_exponent_boxI)
    (auto simp: Poly_Mapping.keys_single lookup_single when_def e)

lemma roth_right_factor_box:
  "roth_poly_in_box (Suc n) r (roth_right_factor P n (r n) B b)"
  unfolding roth_right_factor_def
  by (rule roth_poly_in_box_sum)
    (auto intro: roth_poly_in_box_monom roth_single_in_box)

lemma roth_right_factor_vars:
  "vars (roth_right_factor P n d B b) \<subseteq> {n}"
proof -
  have h: "vars (\<Sum>e\<le>d.
      MPoly_Type.monom (Poly_Mapping.single n e)
        (roth_vs.representation B (roth_last_coeff P n e) b))
    \<subseteq> (\<Union>e\<le>d. vars (MPoly_Type.monom
      (Poly_Mapping.single n e)
      (roth_vs.representation B (roth_last_coeff P n e) b)))"
    by (rule vars_setsum) simp
  have t: "(\<Union>e\<le>d. vars (MPoly_Type.monom
      (Poly_Mapping.single n e)
      (roth_vs.representation B (roth_last_coeff P n e) b)))
    \<subseteq> {n}"
    by (auto simp: vars_monom_single_cases)
  show ?thesis using h t by (simp add: roth_right_factor_def)
qed

lemma roth_right_factor_univ_indep:
  assumes sub: "B \<subseteq> roth_last_coeff P n ` {..d}"
    and ind: "roth_vs.independent B" and fin: "finite B"
    and z: "(\<Sum>u\<in>B. Polynomial.smult (c u)
      (mpoly_to_poly n (roth_right_factor P n d B u))) = 0"
    and b: "b\<in>B"
  shows "c b=0"
proof -
  obtain e where e: "e\<le>d" and
    coord: "\<forall>u\<in>B. roth_vs.representation B
      (roth_last_coeff P n e) u = (if u=b then 1 else 0)"
    using roth_last_coeff_basis_coordinates[OF sub ind b] by blast
  have val: "Polynomial.coeff
    (\<Sum>u\<in>B. Polynomial.smult (c u)
      (mpoly_to_poly n (roth_right_factor P n d B u))) e = c b"
    by (simp add: Polynomial.coeff_sum coeff_smult
      roth_right_factor_coeff[OF e] coord
      roth_sum_coordinate[OF fin b])
  show ?thesis using z val by simp
qed

theorem roth_tensor_basis_exists:
  assumes box: "roth_poly_in_box (Suc n) r (P::rat mpoly)"
    and nz: "P\<noteq>0"
  shows "\<exists>B. B \<subseteq> roth_last_coeff P n ` {..r n} \<and>
    B\<noteq>{} \<and> card B \<le> Suc (r n) \<and>
    roth_vs.independent B \<and>
    (\<forall>b\<in>B. roth_poly_in_box n r b) \<and>
    P = (\<Sum>b\<in>B. b * roth_right_factor P n (r n) B b) \<and>
    (\<forall>c. (\<Sum>b\<in>B. MPoly_Type.smult (c b)
      (roth_right_factor P n (r n) B b))=0 \<longrightarrow>
      (\<forall>b\<in>B. c b=0))"
proof -
  let ?S = "roth_last_coeff P n ` {..r n}"
  obtain B where B: "B\<subseteq>?S" "roth_vs.independent B"
    "?S\<subseteq>roth_vs.span B" "card B\<le>Suc (r n)"
    "\<forall>b\<in>B. roth_poly_in_box n r b"
    using roth_last_coeff_basis[OF box] by blast
  have fin: "finite B"
    using B(1) by (meson finite_subset finite_imageI finite_atMost)
  have bn: "B\<noteq>{}"
    by (rule roth_last_coeff_basis_nonempty[OF box nz B(3)])
  have spl: "P = (\<Sum>b\<in>B.
      b * roth_right_factor P n (r n) B b)"
    using roth_tensor_basis_split[OF box B(2) B(3) fin]
    by (simp add: roth_right_factor_def)
  have ri: "\<forall>c. (\<Sum>b\<in>B. MPoly_Type.smult (c b)
      (roth_right_factor P n (r n) B b))=0 \<longrightarrow>
      (\<forall>b\<in>B. c b=0)"
    using roth_right_factor_indep[OF B(1) B(2) fin] by blast
  show ?thesis using B(1,2,4,5) bn spl ri by blast
qed

end
