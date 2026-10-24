theory Roth_Kronecker
  imports Roth_Wronskian
begin

section \<open>Kronecker encoding of bounded exponent vectors\<close>

definition roth_digits :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat" where
  "roth_digits n B f = (\<Sum>i<n. f i * B^i)"

lemma roth_digits_Suc:
  "roth_digits (Suc n) B f = f 0 + B * roth_digits n B (f \<circ> Suc)"
  unfolding roth_digits_def sum.lessThan_Suc_shift
  by (simp add: sum_distrib_left algebra_simps)

lemma roth_digits_head_eq:
  assumes B: "0 < B" and f: "f 0 < B" and g: "g 0 < B"
    and eq: "roth_digits (Suc n) B f = roth_digits (Suc n) B g"
  shows "f 0 = g 0"
  using eq f g
  by (simp add: roth_digits_Suc)
    (metis mod_mult_self2 mod_less)

lemma roth_digits_inj:
  assumes B: "0 < B"
    and f: "\<forall>i<n. f i < B"
    and g: "\<forall>i<n. g i < B"
    and eq: "roth_digits n B f = roth_digits n B g"
  shows "\<forall>i<n. f i = g i"
  using f g eq
proof (induction n arbitrary: f g)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have hd: "f 0 = g 0"
    by (rule roth_digits_head_eq[OF B _ _ Suc.prems(3)])
      (use Suc.prems in auto)
  have tail: "roth_digits n B (f \<circ> Suc) =
      roth_digits n B (g \<circ> Suc)"
    using Suc.prems(3) hd B by (simp add: roth_digits_Suc)
  have fb: "\<forall>i<n. (f \<circ> Suc) i < B"
    using Suc.prems by auto
  have gb: "\<forall>i<n. (g \<circ> Suc) i < B"
    using Suc.prems by auto
  have teq: "\<forall>i<n. f (Suc i) = g (Suc i)"
    using Suc.IH[OF fb gb tail] by simp
  show ?case using hd teq by (metis less_Suc_eq_0_disj)
qed

definition roth_kronecker where
  "roth_kronecker m B I =
    roth_digits m B (Poly_Mapping.lookup I)"

lemma roth_kronecker_add:
  "roth_kronecker m B (I + J) =
    roth_kronecker m B I + roth_kronecker m B J"
  by (simp add: roth_kronecker_def roth_digits_def
    lookup_add sum.distrib algebra_simps)

lemma roth_kronecker_single:
  assumes v: "v<m"
  shows "roth_kronecker m B (Poly_Mapping.single v n) = n * B^v"
  using v by (simp add: roth_kronecker_def roth_digits_def
    lookup_single when_def sum.remove[of "{..<m}" v])

lemma roth_kronecker_inj:
  assumes pos: "0 < B" and B: "\<forall>v<m. r v < B"
    and I: "I \<in> roth_exponent_box m r"
    and J: "J \<in> roth_exponent_box m r"
    and eq: "roth_kronecker m B I = roth_kronecker m B J"
  shows "I = J"
proof (rule Poly_Mapping.poly_mapping_eqI)
  fix v
  have ib: "\<forall>u<m. Poly_Mapping.lookup I u < B"
    using I B roth_exponent_boxD(2) by (meson le_less_trans)
  have jb: "\<forall>u<m. Poly_Mapping.lookup J u < B"
    using J B roth_exponent_boxD(2) by (meson le_less_trans)
  have inside: "\<forall>u<m. Poly_Mapping.lookup I u =
      Poly_Mapping.lookup J u"
    by (rule roth_digits_inj[OF pos ib jb])
      (use eq in \<open>simp add: roth_kronecker_def\<close>)
  show "Poly_Mapping.lookup I v = Poly_Mapping.lookup J v"
  proof (cases "v<m")
    case True
    then show ?thesis using inside by auto
  next
    case False
    have vi: "v \<notin> Poly_Mapping.keys I"
      using roth_exponent_boxD(1)[OF I] False by auto
    have vj: "v \<notin> Poly_Mapping.keys J"
      using roth_exponent_boxD(1)[OF J] False by auto
    show ?thesis using vi vj
      by (simp add: not_in_keys_iff_lookup_eq_zero)
  qed
qed

definition roth_ksubst where
  "roth_ksubst m B P =
    (\<Sum>I\<in>Poly_Mapping.keys (mapping_of P).
      Polynomial.monom (MPoly_Type.coeff P I)
        (roth_kronecker m B I))"

lemma roth_ksubst_box:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "roth_ksubst m B P =
    (\<Sum>I\<in>roth_exponent_box m r.
      Polynomial.monom (MPoly_Type.coeff P I)
        (roth_kronecker m B I))"
  unfolding roth_ksubst_def
proof (rule sum.mono_neutral_cong_left)
  show "finite (roth_exponent_box m r)" by simp
  show "Poly_Mapping.keys (mapping_of P) \<subseteq>
      roth_exponent_box m r"
    using box by (simp add: roth_poly_in_box_def)
  show "\<forall>I\<in>roth_exponent_box m r -
      Poly_Mapping.keys (mapping_of P).
      Polynomial.monom (MPoly_Type.coeff P I)
        (roth_kronecker m B I) = 0"
    by (simp add: coeff_keys)
qed simp

lemma roth_ksubst_add:
  fixes P Q :: "rat mpoly"
  assumes P: "roth_poly_in_box m r P"
    and Q: "roth_poly_in_box m r Q"
  shows "roth_ksubst m B (P+Q) =
    roth_ksubst m B P + roth_ksubst m B Q"
  by (simp add: roth_ksubst_box[OF roth_poly_in_box_add[OF P Q]]
    roth_ksubst_box[OF P] roth_ksubst_box[OF Q]
    MPoly_Type.coeff_def plus_mpoly.rep_eq lookup_add
    Polynomial.add_monom[symmetric] sum.distrib)

lemma roth_box_smult:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "roth_poly_in_box m r (MPoly_Type.smult c P)"
  using box by (auto simp: roth_poly_in_box_def in_keys_iff
    MPoly_Type.coeff_def[symmetric] roth_coeff_smult_rat)

lemma roth_poly_smult_sum:
  fixes f :: "'a \<Rightarrow> rat poly"
  assumes fin: "finite S"
  shows "Polynomial.smult c (\<Sum>i\<in>S. f i) =
    (\<Sum>i\<in>S. Polynomial.smult c (f i))"
  using fin by (induction S rule: finite_induct)
    (simp_all add: smult_distribs)

lemma roth_ksubst_smult:
  fixes P :: "rat mpoly"
  assumes P: "roth_poly_in_box m r P"
  shows "roth_ksubst m B (MPoly_Type.smult c P) =
    Polynomial.smult c (roth_ksubst m B P)"
  by (simp add: roth_ksubst_box[OF roth_box_smult[OF P]]
    roth_ksubst_box[OF P] roth_coeff_smult_rat
    Polynomial.smult_monom roth_poly_smult_sum)

lemma roth_ksubst_zero [simp]:
  "roth_ksubst m B (0::rat mpoly) = 0"
  by (simp add: roth_ksubst_def zero_mpoly.rep_eq)

lemma roth_ksubst_sum:
  fixes P :: "'a \<Rightarrow> rat mpoly"
  assumes fin: "finite S"
    and box: "\<And>i. i\<in>S \<Longrightarrow> roth_poly_in_box m r (P i)"
  shows "roth_ksubst m B (\<Sum>i\<in>S. P i) =
    (\<Sum>i\<in>S. roth_ksubst m B (P i))"
  using fin box
proof (induction S rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x S)
  have xb: "roth_poly_in_box m r (P x)"
    using insert.prems by auto
  have sb: "roth_poly_in_box m r (\<Sum>i\<in>S. P i)"
    by (rule roth_poly_in_box_sum)
      (use insert.hyps insert.prems in auto)
  have ih: "roth_ksubst m B (\<Sum>i\<in>S. P i) =
      (\<Sum>i\<in>S. roth_ksubst m B (P i))"
    using insert.IH insert.prems by blast
  show ?case using ih insert.hyps
    by (simp add: roth_ksubst_add[OF xb sb])
qed

lemma roth_ksubst_coeff:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and pos: "0 < B" and B: "\<forall>v<m. r v < B"
    and I: "I \<in> roth_exponent_box m r"
  shows "Polynomial.coeff (roth_ksubst m B P)
    (roth_kronecker m B I) = MPoly_Type.coeff P I"
proof -
  let ?K = "Poly_Mapping.keys (mapping_of P)"
  have kij: "\<And>J. J \<in> ?K \<Longrightarrow>
      roth_kronecker m B J = roth_kronecker m B I \<longleftrightarrow> J = I"
    using roth_kronecker_inj[OF pos B _ I] box
    by (auto simp: roth_poly_in_box_def)
  show ?thesis using kij
    by (simp add: roth_ksubst_def coeff_sum coeff_monom
      sum.delta coeff_def not_in_keys_iff_lookup_eq_zero)
qed

lemma roth_ksubst_reflect_zero:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and pos: "0 < B" and B: "\<forall>v<m. r v < B"
    and z: "roth_ksubst m B P = 0"
  shows "P = 0"
proof (rule coeff_all_0)
  fix I
  show "MPoly_Type.coeff P I = 0"
  proof (cases "I \<in> roth_exponent_box m r")
    case True
    then show ?thesis
      using roth_ksubst_coeff[OF box pos B True] z by simp
  next
    case False
    then show ?thesis
      using roth_coeff_zero_outside_box[OF box False] by simp
  qed
qed

definition roth_mpoly_indep ::
  "nat \<Rightarrow> (nat \<Rightarrow> rat mpoly) \<Rightarrow> bool" where
  "roth_mpoly_indep k p \<longleftrightarrow>
    (\<forall>c. (\<Sum>j<k. MPoly_Type.smult (c j) (p j)) = 0 \<longrightarrow>
      (\<forall>j<k. c j = 0))"

lemma roth_ksubst_indep:
  fixes p :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>j<k. roth_poly_in_box m r (p j)"
    and pos: "0 < B" and B: "\<forall>v<m. r v < B"
    and ind: "roth_mpoly_indep k p"
  shows "roth_poly_indep k (\<lambda>j. roth_ksubst m B (p j))"
  unfolding roth_poly_indep_def
proof (intro allI impI)
  fix c j
  assume z: "(\<Sum>i<k. Polynomial.smult (c i)
      (roth_ksubst m B (p i))) = 0"
    and j: "j<k"
  let ?U = "\<lambda>i. MPoly_Type.smult (c i) (p i)"
  have ub: "\<And>i. i<k \<Longrightarrow> roth_poly_in_box m r (?U i)"
    using box by (auto intro: roth_box_smult)
  have sb: "roth_poly_in_box m r (\<Sum>i<k. ?U i)"
    by (rule roth_poly_in_box_sum) (use ub in auto)
  have hom0: "roth_ksubst m B (\<Sum>i<k. ?U i) =
      (\<Sum>i<k. roth_ksubst m B (?U i))"
    by (rule roth_ksubst_sum) (use ub in auto)
  have hom1: "(\<Sum>i<k. roth_ksubst m B (?U i)) =
      (\<Sum>i<k. Polynomial.smult (c i)
        (roth_ksubst m B (p i)))"
    by (rule sum.cong)
      (use box in \<open>auto simp: roth_ksubst_smult\<close>)
  have mz: "(\<Sum>i<k. ?U i) = 0"
    by (rule roth_ksubst_reflect_zero[OF sb pos B])
      (use z hom0 hom1 in simp)
  show "c j = 0"
    using ind mz j by (auto simp: roth_mpoly_indep_def)
qed

lemma roth_kronecker_wr_nonzero:
  fixes p :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>j<k. roth_poly_in_box m r (p j)"
    and pos: "0<B" and B: "\<forall>v<m. r v<B"
    and ind: "roth_mpoly_indep k p"
  shows "roth_hwronskian k (\<lambda>j. roth_ksubst m B (p j)) \<noteq> 0"
  by (rule roth_wr_independent)
    (rule roth_ksubst_indep[OF box pos B ind])

end
