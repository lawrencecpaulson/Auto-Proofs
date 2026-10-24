theory Kronecker_Evaluation
  imports
    Roth_Wronskian
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

section \<open>The first derivative of Kronecker substitution\<close>

lemma roth_ksubst_monom:
  fixes c :: rat
  shows "roth_ksubst m B (MPoly_Type.monom I c) =
    Polynomial.monom c (roth_kronecker m B I)"
  by (cases "c=0")
    (simp_all add: roth_ksubst_def mapping_of_monom keys_single
      MPoly_Type.coeff_def lookup_single when_def)

lemma roth_ksubst_monom_deriv:
  fixes c :: rat
  shows "pderiv (roth_ksubst m B (MPoly_Type.monom I c)) =
    (\<Sum>v<m. Polynomial.monom
      (of_nat (Poly_Mapping.lookup I v * B^v) * c)
      (roth_kronecker m B I - 1))"
  by (simp add: roth_ksubst_monom pderiv_monom
    Polynomial.monom_sum[symmetric] roth_kronecker_def
    roth_digits_def sum_distrib_right[symmetric] of_nat_sum)

lemma roth_mchoose_single_one:
  "roth_mchoose I (Poly_Mapping.single v 1) =
    Poly_Mapping.lookup I v"
  by (simp add: roth_mchoose_def keys_single
    prod.remove[of "insert v (Poly_Mapping.keys I)" v]
    lookup_single when_def)

lemma roth_single_sub_add:
  fixes I :: "(nat,nat) poly_mapping"
  assumes h: "0 < Poly_Mapping.lookup I v"
  shows "I - Poly_Mapping.single v 1 + Poly_Mapping.single v 1 = I"
  by (rule Poly_Mapping.poly_mapping_eqI)
    (use h in \<open>auto simp: lookup_add lookup_minus
      lookup_single when_def; presburger\<close>)

lemma roth_hasse_monom_single_one:
  fixes c :: rat
  shows "roth_hasse (Poly_Mapping.single v 1)
      (MPoly_Type.monom I c) =
    MPoly_Type.monom (I - Poly_Mapping.single v 1)
      (c * of_nat (Poly_Mapping.lookup I v))"
  using roth_mchoose_single_one[of I v]
  by (simp add: roth_hasse_monom_exact)

lemma roth_monom_zero [simp]:
  "MPoly_Type.monom I (0::rat) = 0"
  by (simp add: mapping_of_inject[symmetric]
    mapping_of_monom zero_mpoly.rep_eq)

lemma roth_kronecker_sub_single:
  assumes v: "v<m" and h: "0<Poly_Mapping.lookup I v"
  shows "roth_kronecker m B (I - Poly_Mapping.single v 1)
    + B^v = roth_kronecker m B I"
  using roth_kronecker_add[of m B
      "I - Poly_Mapping.single v 1" "Poly_Mapping.single v 1"]
    roth_single_sub_add[OF h]
    roth_kronecker_single[OF v, of B 1]
  by simp

lemma roth_kronecker_sub_power:
  assumes v: "v<m" and B: "0<B"
    and h: "0<Poly_Mapping.lookup I v"
  shows "B^v - 1 + roth_kronecker m B
      (I - Poly_Mapping.single v 1) =
    roth_kronecker m B I - 1"
  using roth_kronecker_sub_single[OF v h, of B] B by simp

lemma roth_ksubst_monom_chain_term:
  fixes c :: rat
  assumes v: "v<m" and B: "0<B"
  shows "Polynomial.monom (of_nat (B^v)) (B^v-1) *
      roth_ksubst m B
        (roth_hasse (Poly_Mapping.single v 1)
          (MPoly_Type.monom I c)) =
    Polynomial.monom
      (of_nat (Poly_Mapping.lookup I v * B^v) * c)
      (roth_kronecker m B I - 1)"
proof (cases "Poly_Mapping.lookup I v = 0")
  case True
  then show ?thesis
    using roth_hasse_monom_single_one[of v I c] True by simp
next
  case False
  then have h: "0<Poly_Mapping.lookup I v" by simp
  show ?thesis
    using roth_hasse_monom_single_one[of v I c]
      roth_kronecker_sub_power[OF v B h]
    by (simp add: roth_ksubst_monom
      Polynomial.mult_monom algebra_simps)
qed

lemma roth_ksubst_monom_chain:
  fixes c :: rat
  assumes B: "0<B"
  shows "pderiv (roth_ksubst m B (MPoly_Type.monom I c)) =
    (\<Sum>v<m. Polynomial.monom (of_nat (B^v)) (B^v-1) *
      roth_ksubst m B
        (roth_hasse (Poly_Mapping.single v 1)
          (MPoly_Type.monom I c)))"
proof -
  have eqs: "(\<Sum>v<m. Polynomial.monom (of_nat (B^v)) (B^v-1) *
      roth_ksubst m B
        (roth_hasse (Poly_Mapping.single v 1)
          (MPoly_Type.monom I c))) =
    (\<Sum>v<m. Polynomial.monom
      (of_nat (Poly_Mapping.lookup I v * B^v) * c)
      (roth_kronecker m B I - 1))"
  proof (rule sum.cong)
    show "{..<m} = {..<m}" by simp
    fix v
    assume "v \<in> {..<m}"
    then have vm: "v<m" by simp
    show "Polynomial.monom (of_nat (B^v)) (B^v-1) *
        roth_ksubst m B
          (roth_hasse (Poly_Mapping.single v 1)
            (MPoly_Type.monom I c)) =
      Polynomial.monom
        (of_nat (Poly_Mapping.lookup I v * B^v) * c)
        (roth_kronecker m B I - 1)"
      by (rule roth_ksubst_monom_chain_term[OF vm B])
  qed
  show ?thesis
    using roth_ksubst_monom_deriv[of m B I c] eqs by simp
qed

lemma roth_box_mono:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and le: "\<forall>v<m. r v \<le> s v"
  shows "roth_poly_in_box m s P"
  unfolding roth_poly_in_box_def
proof (intro subsetI)
  fix I
  assume "I \<in> Poly_Mapping.keys (mapping_of P)"
  then have ib: "I \<in> roth_exponent_box m r"
    using box by (auto simp: roth_poly_in_box_def)
  show "I \<in> roth_exponent_box m s"
    using ib le by (auto simp: roth_exponent_box_iff intro: order_trans)
qed

lemma roth_hasse_preserves_box:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "roth_poly_in_box m r (roth_hasse J P)"
  by (rule roth_box_mono[OF roth_hasse_in_box[OF box]]) simp

lemma roth_poly_pderiv_sum:
  fixes f :: "'a \<Rightarrow> rat poly"
  assumes "finite S"
  shows "pderiv (\<Sum>i\<in>S. f i) =
    (\<Sum>i\<in>S. pderiv (f i))"
  using assms by (induction S rule: finite_induct)
    (simp_all add: pderiv_add)

lemma roth_ksubst_hasse_sum:
  fixes P :: "'a \<Rightarrow> rat mpoly"
  assumes fin: "finite S"
    and box: "\<And>i. i\<in>S \<Longrightarrow> roth_poly_in_box m r (P i)"
  shows "roth_ksubst m B (roth_hasse J (\<Sum>i\<in>S. P i)) =
    (\<Sum>i\<in>S. roth_ksubst m B (roth_hasse J (P i)))"
  unfolding roth_hasse_sum[OF fin]
  by (rule roth_ksubst_sum[OF fin])
    (use box in \<open>auto intro: roth_hasse_preserves_box\<close>)

lemma roth_poly_weighted_sum_swap:
  fixes f :: "'a \<Rightarrow> nat \<Rightarrow> rat poly"
    and w :: "nat \<Rightarrow> rat poly"
  assumes fin: "finite S"
  shows "(\<Sum>I\<in>S. \<Sum>v<m. w v * f I v) =
    (\<Sum>v<m. w v * (\<Sum>I\<in>S. f I v))"
  by (subst sum.swap) (simp add: sum_distrib_left)

lemma roth_ksubst_chain_sum:
  fixes P :: "'a \<Rightarrow> rat mpoly"
  assumes fin: "finite S"
    and box: "\<And>i. i\<in>S \<Longrightarrow> roth_poly_in_box m r (P i)"
    and chain: "\<And>i. i\<in>S \<Longrightarrow>
      pderiv (roth_ksubst m B (P i)) =
      (\<Sum>v<m. Polynomial.monom (of_nat (B^v)) (B^v-1) *
        roth_ksubst m B
          (roth_hasse (Poly_Mapping.single v 1) (P i)))"
  shows "pderiv (roth_ksubst m B (\<Sum>i\<in>S. P i)) =
    (\<Sum>v<m. Polynomial.monom (of_nat (B^v)) (B^v-1) *
      roth_ksubst m B
        (roth_hasse (Poly_Mapping.single v 1) (\<Sum>i\<in>S. P i)))"
proof -
  let ?w = "\<lambda>v. Polynomial.monom (of_nat (B^v)) (B^v-1)"
  have a: "roth_ksubst m B (\<Sum>i\<in>S. P i) =
      (\<Sum>i\<in>S. roth_ksubst m B (P i))"
    by (rule roth_ksubst_sum[OF fin box])
  have b: "pderiv (roth_ksubst m B (\<Sum>i\<in>S. P i)) =
      (\<Sum>i\<in>S. pderiv (roth_ksubst m B (P i)))"
    by (simp add: a roth_poly_pderiv_sum[OF fin])
  have c: "(\<Sum>i\<in>S. pderiv (roth_ksubst m B (P i))) =
      (\<Sum>i\<in>S. \<Sum>v<m. ?w v *
        roth_ksubst m B (roth_hasse (Poly_Mapping.single v 1) (P i)))"
    by (rule sum.cong) (use chain in auto)
  have d: "(\<Sum>i\<in>S. \<Sum>v<m. ?w v *
      roth_ksubst m B (roth_hasse (Poly_Mapping.single v 1) (P i))) =
    (\<Sum>v<m. ?w v *
      (\<Sum>i\<in>S. roth_ksubst m B
        (roth_hasse (Poly_Mapping.single v 1) (P i))))"
    by (rule roth_poly_weighted_sum_swap[OF fin])
  have e: "(\<Sum>v<m. ?w v *
      (\<Sum>i\<in>S. roth_ksubst m B
        (roth_hasse (Poly_Mapping.single v 1) (P i)))) =
    (\<Sum>v<m. ?w v *
      roth_ksubst m B
        (roth_hasse (Poly_Mapping.single v 1) (\<Sum>i\<in>S. P i)))"
    using roth_ksubst_hasse_sum[OF fin box] by simp
  show ?thesis using b c d e by simp
qed

lemma roth_ksubst_chain:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P" and B: "0<B"
  shows "pderiv (roth_ksubst m B P) =
    (\<Sum>v<m. Polynomial.monom (of_nat (B^v)) (B^v-1) *
      roth_ksubst m B
        (roth_hasse (Poly_Mapping.single v 1) P))"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of P)"
  let ?Q = "\<lambda>I. MPoly_Type.monom I (MPoly_Type.coeff P I)"
  have pe: "P = (\<Sum>I\<in>?S. ?Q I)"
    by (rule roth_sum_monom)
  have qb: "\<And>I. I\<in>?S \<Longrightarrow> roth_poly_in_box m r (?Q I)"
    using box by (auto intro: roth_poly_in_box_monom
      simp: roth_poly_in_box_def)
  have ch: "\<And>I. I\<in>?S \<Longrightarrow>
      pderiv (roth_ksubst m B (?Q I)) =
      (\<Sum>v<m. Polynomial.monom (of_nat (B^v)) (B^v-1) *
        roth_ksubst m B
          (roth_hasse (Poly_Mapping.single v 1) (?Q I)))"
    by (rule roth_ksubst_monom_chain[OF B])
  have h: "pderiv (roth_ksubst m B (\<Sum>I\<in>?S. ?Q I)) =
    (\<Sum>v<m. Polynomial.monom (of_nat (B^v)) (B^v-1) *
      roth_ksubst m B
        (roth_hasse (Poly_Mapping.single v 1) (\<Sum>I\<in>?S. ?Q I)))"
    by (rule roth_ksubst_chain_sum[OF finite_keys qb ch])
  show ?thesis using pe h by metis
qed

section \<open>Iteration of the Kronecker chain rule\<close>

lemma roth_hasse_first_comp:
  fixes P :: "rat mpoly"
  shows "roth_hasse (Poly_Mapping.single v 1) (roth_hasse J P) =
    Const (of_nat (Suc (Poly_Mapping.lookup J v))) *
      roth_hasse (J + Poly_Mapping.single v 1) P"
proof -
  have e: "roth_mchoose (J + Poly_Mapping.single v 1)
      (Poly_Mapping.single v 1) = Suc (Poly_Mapping.lookup J v)"
    by (simp only: roth_mchoose_single_one)
      (simp add: lookup_add lookup_single when_def)
  show ?thesis
    using roth_hasse_comp[of "Poly_Mapping.single v 1" J P] e
    by (simp add: add.commute)
qed

lemma roth_ksubst_Const_mult:
  fixes P :: "rat mpoly"
  assumes "roth_poly_in_box m r P"
  shows "roth_ksubst m B (Const c * P) =
    Polynomial.smult c (roth_ksubst m B P)"
  using roth_ksubst_smult[OF assms, of B c]
  by (simp add: smult_conv_mult roth_Const_monom)

lemma roth_monom_smult_swap:
  fixes q :: "rat poly"
  shows "Polynomial.monom c n * Polynomial.smult d q =
    Polynomial.monom (c*d) n * q"
proof -
  have "Polynomial.monom c n * Polynomial.smult d q =
      Polynomial.smult d (Polynomial.monom c n * q)"
    by (rule mult_smult_right)
  also have "\<dots> = Polynomial.smult d (Polynomial.monom c n) * q"
    by (simp only: mult_smult_left)
  also have "\<dots> = Polynomial.monom (c*d) n * q"
    by (simp add: smult_monom mult.commute)
  finally show ?thesis .
qed

lemma roth_ksubst_hasse_first:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P" and B: "0<B"
  shows "pderiv (roth_ksubst m B (roth_hasse J P)) =
    (\<Sum>v<m. Polynomial.monom
      (of_nat (B^v * Suc (Poly_Mapping.lookup J v))) (B^v-1) *
      roth_ksubst m B
        (roth_hasse (J + Poly_Mapping.single v 1) P))"
proof -
  have hb: "roth_poly_in_box m r (roth_hasse J P)"
    by (rule roth_hasse_preserves_box[OF box])
  have h: "pderiv (roth_ksubst m B (roth_hasse J P)) =
    (\<Sum>v<m. Polynomial.monom (of_nat (B^v)) (B^v-1) *
      roth_ksubst m B
        (roth_hasse (Poly_Mapping.single v 1) (roth_hasse J P)))"
    by (rule roth_ksubst_chain[OF hb B])
  show ?thesis
    unfolding h
  proof (rule sum.cong)
    show "{..<m} = {..<m}" by simp
    fix v
    assume "v \<in> {..<m}"
    have hb2: "roth_poly_in_box m r
      (roth_hasse (J + Poly_Mapping.single v 1) P)"
      by (rule roth_hasse_preserves_box[OF box])
    show "Polynomial.monom (of_nat (B ^ v)) (B ^ v - 1) *
        roth_ksubst m B
          (roth_hasse (Poly_Mapping.single v 1) (roth_hasse J P)) =
      Polynomial.monom
        (of_nat (B ^ v * Suc (Poly_Mapping.lookup J v)))
        (B ^ v - 1) *
        roth_ksubst m B
          (roth_hasse (J + Poly_Mapping.single v 1) P)"
      by (simp only: roth_hasse_first_comp
        roth_ksubst_Const_mult[OF hb2] roth_monom_smult_swap)
        (simp add: algebra_simps)
  qed
qed

lemma roth_ksubst_hasse_weighted_deriv:
  fixes P :: "rat mpoly" and a :: "rat poly"
  assumes box: "roth_poly_in_box m r P" and B: "0<B"
  shows "pderiv (a * roth_ksubst m B (roth_hasse J P)) =
    pderiv a * roth_ksubst m B (roth_hasse J P) +
    (\<Sum>v<m. (a * Polynomial.monom
        (of_nat (B^v * Suc (Poly_Mapping.lookup J v))) (B^v-1)) *
      roth_ksubst m B
        (roth_hasse (J + Poly_Mapping.single v 1) P))"
  by (simp add: pderiv_mult roth_ksubst_hasse_first[OF box B]
    sum_distrib_left algebra_simps)

section \<open>Uniform expansion of higher substituted derivatives\<close>

definition roth_total_order :: "nat \<Rightarrow> (nat,nat) poly_mapping \<Rightarrow> nat" where
  "roth_total_order m J = (\<Sum>v<m. Poly_Mapping.lookup J v)"

lemma roth_total_order_add:
  "roth_total_order m (I+J) =
    roth_total_order m I + roth_total_order m J"
  by (simp add: roth_total_order_def lookup_add sum.distrib)

lemma roth_total_order_single:
  assumes "v<m"
  shows "roth_total_order m (Poly_Mapping.single v 1) = 1"
  using assms
  by (simp add: roth_total_order_def lookup_single when_def
    sum.remove[of "{..<m}" v])

fun roth_jet_index :: "nat option list \<Rightarrow> (nat,nat) poly_mapping" where
  "roth_jet_index [] = 0"
| "roth_jet_index (None # xs) = roth_jet_index xs"
| "roth_jet_index (Some v # xs) =
    roth_jet_index xs + Poly_Mapping.single v 1"

definition roth_jet_alphabet :: "nat \<Rightarrow> nat option set" where
  "roth_jet_alphabet m = insert None (Some ` {..<m})"

definition roth_jet_words :: "nat \<Rightarrow> nat \<Rightarrow> nat option list set" where
  "roth_jet_words m i =
    {xs. set xs \<subseteq> roth_jet_alphabet m \<and> length xs = i}"

lemma finite_roth_jet_words [simp]:
  "finite (roth_jet_words m i)"
  by (simp add: roth_jet_words_def roth_jet_alphabet_def
    finite_lists_length_eq)

lemma roth_jet_words_zero [simp]:
  "roth_jet_words m 0 = {[]}"
  by (auto simp: roth_jet_words_def)

lemma roth_jet_index_order:
  assumes "set xs \<subseteq> roth_jet_alphabet m"
  shows "roth_total_order m (roth_jet_index xs) \<le> length xs"
  using assms
proof (induction xs)
  case Nil
  then show ?case by (simp add: roth_total_order_def)
next
  case (Cons a xs)
  show ?case
  proof (cases a)
    case None
    then show ?thesis using Cons
      by (simp add: roth_jet_alphabet_def)
  next
    case (Some v)
    then have vm: "v<m"
      using Cons.prems by (auto simp: roth_jet_alphabet_def)
    have t: "roth_total_order m (Poly_Mapping.single v 1) = 1"
      by (rule roth_total_order_single[OF vm])
    show ?thesis using Cons.IH Cons.prems t Some
      by (simp add: roth_total_order_add roth_jet_alphabet_def)
  qed
qed

lemma roth_nat_keys_add:
  fixes I J :: "(nat,nat) poly_mapping"
  shows "Poly_Mapping.keys (I+J) \<subseteq>
    Poly_Mapping.keys I \<union> Poly_Mapping.keys J"
proof (rule subsetI)
  fix v
  assume h: "v \<in> Poly_Mapping.keys (I+J)"
  show "v \<in> Poly_Mapping.keys I \<union> Poly_Mapping.keys J"
  proof (rule ccontr)
    assume "v \<notin> Poly_Mapping.keys I \<union> Poly_Mapping.keys J"
    then have a: "Poly_Mapping.lookup I v = 0"
      and b: "Poly_Mapping.lookup J v = 0"
      by (simp_all add: not_in_keys_iff_lookup_eq_zero)
    have "Poly_Mapping.lookup (I+J) v = 0"
      by (simp add: lookup_add a b)
    then show False using h by (simp add: in_keys_iff)
  qed
qed

lemma roth_jet_index_support:
  assumes "set xs \<subseteq> roth_jet_alphabet m"
  shows "Poly_Mapping.keys (roth_jet_index xs) \<subseteq> {..<m}"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (cases a)
      (auto simp: roth_jet_alphabet_def
        dest: subsetD[OF roth_nat_keys_add])
qed

lemma roth_jet_word_bounds:
  assumes h: "xs \<in> roth_jet_words m i"
  shows "Poly_Mapping.keys (roth_jet_index xs) \<subseteq> {..<m}"
    "roth_total_order m (roth_jet_index xs) \<le> i"
proof -
  have s: "set xs \<subseteq> roth_jet_alphabet m"
    and len: "length xs = i"
    using h by (auto simp: roth_jet_words_def)
  show "Poly_Mapping.keys (roth_jet_index xs) \<subseteq> {..<m}"
    by (rule roth_jet_index_support[OF s])
  show "roth_total_order m (roth_jet_index xs) \<le> i"
    using roth_jet_index_order[OF s] len by simp
qed

lemma roth_jet_words_Suc:
  "roth_jet_words m (Suc i) =
    ((#) None ` roth_jet_words m i) \<union>
      ((\<lambda>(xs,v). Some v # xs) ` (roth_jet_words m i \<times> {..<m}))"
  by (auto simp: roth_jet_words_def roth_jet_alphabet_def
    length_Suc_conv)

lemma roth_sum_jet_words:
  fixes f :: "nat option list \<Rightarrow> rat poly"
  shows "(\<Sum>ys\<in>roth_jet_words m (Suc i). f ys) =
    (\<Sum>xs\<in>roth_jet_words m i. f (None#xs)) +
    (\<Sum>xs\<in>roth_jet_words m i. \<Sum>v<m. f (Some v#xs))"
proof -
  let ?S = "roth_jet_words m i"
  let ?A = "((#) None ` ?S)"
  let ?C = "((\<lambda>(xs,v). Some v#xs) ` (?S \<times> {..<m}))"
  have disj: "?A \<inter> ?C = {}" by auto
  have a: "(\<Sum>ys\<in>?A. f ys) = (\<Sum>xs\<in>?S. f (None#xs))"
    by (subst sum.reindex) (auto simp: inj_on_def)
  have c: "(\<Sum>ys\<in>?C. f ys) =
    (\<Sum>xs\<in>?S. \<Sum>v<m. f (Some v#xs))"
    by (subst sum.reindex)
      (auto simp: inj_on_def sum.cartesian_product split_def)
  show ?thesis using a c disj
    by (simp add: roth_jet_words_Suc sum.union_disjoint)
qed

fun roth_jet_coeff :: "nat \<Rightarrow> nat \<Rightarrow> nat option list \<Rightarrow> rat poly"
  where
  "roth_jet_coeff B 0 xs = (if xs=[] then 1 else 0)"
| "roth_jet_coeff B (Suc i) [] = 0"
| "roth_jet_coeff B (Suc i) (None#xs) =
    pderiv (roth_jet_coeff B i xs)"
| "roth_jet_coeff B (Suc i) (Some v#xs) =
    roth_jet_coeff B i xs *
      Polynomial.monom
        (of_nat (B^v * Suc (Poly_Mapping.lookup (roth_jet_index xs) v)))
        (B^v-1)"

lemma roth_jet_expansion:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P" and B: "0<B"
  shows "(pderiv ^^ i) (roth_ksubst m B P) =
    (\<Sum>xs\<in>roth_jet_words m i.
      roth_jet_coeff B i xs *
        roth_ksubst m B (roth_hasse (roth_jet_index xs) P))"
  using box B
proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  then show ?case
    by (simp add: funpow_Suc_right roth_poly_pderiv_sum
      roth_ksubst_hasse_weighted_deriv roth_sum_jet_words
      sum.distrib)
qed

section \<open>Evaluation of Kronecker substitution\<close>

lemma roth_insertion_Const:
  fixes c :: rat and f :: "nat \<Rightarrow> rat"
  shows "insertion f (Const c) = c"
  by (simp add: roth_Const_monom[symmetric]
    insertion_single[of f 0 0 c])

lemma roth_insertion_Var:
  fixes f :: "nat \<Rightarrow> rat"
  shows "insertion f (Var v) = f v"
  by (simp add: roth_Var_monom insertion_single)

lemma roth_monom_var_prod:
  fixes c :: rat
  shows "MPoly_Type.monom I c =
    Const c *
      (\<Prod>v\<in>Poly_Mapping.keys I. Var v ^ Poly_Mapping.lookup I v)"
  using roth_hasse_monom_product[of 0 I c] by simp

lemma roth_insertion_prod:
  fixes f :: "nat \<Rightarrow> rat" and P :: "'a \<Rightarrow> rat mpoly"
  assumes "finite S"
  shows "insertion f (\<Prod>v\<in>S. P v) =
    (\<Prod>v\<in>S. insertion f (P v))"
  using assms by (induction S rule: finite_induct)
    (simp_all add: insertion_mult)

lemma roth_insertion_power:
  fixes f :: "nat \<Rightarrow> rat" and P :: "rat mpoly"
  shows "insertion f (P^n) = insertion f P ^ n"
  by (induction n) (simp_all add: power_Suc insertion_mult)

lemma roth_insertion_monom:
  fixes c :: rat and f :: "nat \<Rightarrow> rat"
  shows "insertion f (MPoly_Type.monom I c) =
    c * (\<Prod>v\<in>Poly_Mapping.keys I.
      f v ^ Poly_Mapping.lookup I v)"
  by (simp add: roth_monom_var_prod insertion_mult
    roth_insertion_Const roth_insertion_prod
    roth_insertion_power roth_insertion_Var)

lemma roth_kronecker_keys:
  assumes h: "Poly_Mapping.keys I \<subseteq> {..<m}"
  shows "roth_kronecker m B I =
    (\<Sum>v\<in>Poly_Mapping.keys I. Poly_Mapping.lookup I v * B^v)"
proof -
  have z: "\<forall>v\<in>{..<m} - Poly_Mapping.keys I.
    Poly_Mapping.lookup I v * B^v = 0"
    by (simp add: not_in_keys_iff_lookup_eq_zero)
  have eq: "(\<Sum>v\<in>Poly_Mapping.keys I.
      Poly_Mapping.lookup I v * B^v) =
    (\<Sum>v<m. Poly_Mapping.lookup I v * B^v)"
    by (rule sum.mono_neutral_left[OF _ h z]) simp
  show ?thesis using eq
    by (simp add: roth_kronecker_def roth_digits_def)
qed

lemma roth_power_swap:
  fixes t :: rat
  shows "(t^a)^b = (t^b)^a"
  by (simp add: power_mult[symmetric] mult.commute)

lemma roth_kronecker_power_prod:
  fixes t :: rat
  shows "(\<Prod>v\<in>S. (t^(B^v))^(Poly_Mapping.lookup I v)) =
    t^(\<Sum>v\<in>S. Poly_Mapping.lookup I v * B^v)"
  by (simp add: power_sum roth_power_swap power_mult[symmetric])

lemma roth_insertion_kronecker_monom:
  fixes c t :: rat
  assumes supp: "Poly_Mapping.keys I \<subseteq> {..<m}"
  shows "insertion (\<lambda>v. t^(B^v)) (MPoly_Type.monom I c) =
    c * t^(roth_kronecker m B I)"
  by (simp add: roth_insertion_monom roth_kronecker_keys[OF supp]
    roth_kronecker_power_prod)

lemma roth_insertion_sum:
  fixes f :: "nat \<Rightarrow> rat" and P :: "'a \<Rightarrow> rat mpoly"
  assumes "finite S"
  shows "insertion f (\<Sum>x\<in>S. P x) =
    (\<Sum>x\<in>S. insertion f (P x))"
  using assms by (induction S rule: finite_induct)
    (simp_all add: insertion_add)

lemma roth_insertion_monom_sum:
  fixes P :: "rat mpoly"
  shows "insertion f P =
    (\<Sum>I\<in>Poly_Mapping.keys (mapping_of P).
      insertion f (MPoly_Type.monom I (MPoly_Type.coeff P I)))"
  using roth_sum_monom[of P]
    roth_insertion_sum[of "Poly_Mapping.keys (mapping_of P)"
      f "\<lambda>I. MPoly_Type.monom I (MPoly_Type.coeff P I)"]
  by simp

lemma roth_poly_ksubst_eval_sum:
  fixes P :: "rat mpoly"
  shows "poly (roth_ksubst m B P) t =
    (\<Sum>I\<in>Poly_Mapping.keys (mapping_of P).
      MPoly_Type.coeff P I * t^(roth_kronecker m B I))"
  by (simp add: roth_ksubst_def poly_sum poly_monom)

lemma roth_box_monom_support:
  assumes box: "roth_poly_in_box m r P"
    and I: "I\<in>Poly_Mapping.keys (mapping_of P)"
  shows "Poly_Mapping.keys I \<subseteq> {..<m}"
  using box I
  by (auto simp: roth_poly_in_box_def
    dest: roth_exponent_boxD(1))

lemma roth_box_support_all:
  assumes box: "roth_poly_in_box m r P"
  shows "\<forall>I\<in>Poly_Mapping.keys (mapping_of P).
    Poly_Mapping.keys I \<subseteq> {..<m}"
  using box by (auto dest: roth_box_monom_support)

lemma roth_ksubst_eval_insertion:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "poly (roth_ksubst m B P) t =
    insertion (\<lambda>v. t^(B^v)) P"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of P)"
  have s: "\<forall>I\<in>?S. Poly_Mapping.keys I \<subseteq> {..<m}"
    by (rule roth_box_support_all[OF box])
  have a: "poly (roth_ksubst m B P) t =
    (\<Sum>I\<in>?S. MPoly_Type.coeff P I * t^(roth_kronecker m B I))"
    by (rule roth_poly_ksubst_eval_sum)
  have b: "insertion (\<lambda>v. t^(B^v)) P =
    (\<Sum>I\<in>?S. insertion (\<lambda>v. t^(B^v))
      (MPoly_Type.monom I (MPoly_Type.coeff P I)))"
    by (rule roth_insertion_monom_sum)
  have c: "(\<Sum>I\<in>?S. insertion (\<lambda>v. t^(B^v))
      (MPoly_Type.monom I (MPoly_Type.coeff P I))) =
    (\<Sum>I\<in>?S. MPoly_Type.coeff P I * t^(roth_kronecker m B I))"
  proof (rule sum.cong)
    show "?S = ?S" by simp
    fix I
    assume i: "I\<in>?S"
    have "Poly_Mapping.keys I \<subseteq> {..<m}"
      using s i by blast
    then show "insertion (\<lambda>v. t^(B^v))
        (MPoly_Type.monom I (MPoly_Type.coeff P I)) =
      MPoly_Type.coeff P I * t^(roth_kronecker m B I)"
      by (rule roth_insertion_kronecker_monom)
  qed
  show ?thesis using a b c by simp
qed

lemma roth_mpoly_neg_one:
  "(-1::rat mpoly) = Const (-1::rat)"
  by (simp add: roth_Const_uminus)

lemma roth_insertion_signof:
  fixes f :: "nat \<Rightarrow> rat"
  shows "insertion f (signof q :: rat mpoly) = (signof q :: rat)"
  by (simp add: sign_def roth_mpoly_neg_one roth_insertion_Const)

lemma roth_insertion_det:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat mpoly"
    and f :: "nat \<Rightarrow> rat"
  shows "insertion f (det (mat k k (\<lambda>(i,j). A i j))) =
    det (mat k k (\<lambda>(i,j). insertion f (A i j)))"
proof -
  let ?S = "{q. q permutes {..<k}}"
  have fin: "finite ?S" by (rule finite_permutations) simp
  have a: "insertion f (det (mat k k (\<lambda>(i,j). A i j))) =
    (\<Sum>q\<in>?S. (signof q :: rat) *
      (\<Prod>i<k. insertion f (A i (q i))))"
    by (simp add: roth_det_mat_expansion
      roth_insertion_sum[OF fin] insertion_mult
      roth_insertion_signof roth_insertion_prod)
  have b: "det (mat k k (\<lambda>(i,j). insertion f (A i j))) =
    (\<Sum>q\<in>?S. (signof q :: rat) *
      (\<Prod>i<k. insertion f (A i (q i))))"
    by (simp add: roth_det_mat_expansion)
  show ?thesis using a b by simp
qed

end
