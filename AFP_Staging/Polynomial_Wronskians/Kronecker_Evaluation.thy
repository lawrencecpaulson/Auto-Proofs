theory Kronecker_Evaluation
  imports
    Polynomial_Wronskians
    "Multivariate_Hasse_Derivatives.MPoly_Hasse_Support"
begin

section \<open>Kronecker encoding of bounded exponent vectors\<close>

definition mwr_digits :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat" where
  "mwr_digits n B f = (\<Sum>i<n. f i * B^i)"

lemma mwr_digits_Suc:
  "mwr_digits (Suc n) B f = f 0 + B * mwr_digits n B (f \<circ> Suc)"
  unfolding mwr_digits_def sum.lessThan_Suc_shift
  by (simp add: sum_distrib_left algebra_simps)

lemma mwr_digits_head_eq:
  assumes "0 < B" and "f 0 < B" and "g 0 < B"
    and eq: "mwr_digits (Suc n) B f = mwr_digits (Suc n) B g"
  shows "f 0 = g 0"
  using assms
  by (metis mod_less mod_mult_self2 mwr_digits_Suc)

lemma mwr_digits_inj:
  assumes B: "0 < B"
    and f: "\<forall>i<n. f i < B"
    and g: "\<forall>i<n. g i < B"
    and eq: "mwr_digits n B f = mwr_digits n B g"
    and "i<n"
  shows "f i = g i"
  using f g eq `i<n`
proof (induction n arbitrary: f g i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have hd: "f 0 = g 0"
    using B Suc.prems mwr_digits_head_eq by blast
  have tail: "mwr_digits n B (f \<circ> Suc) = mwr_digits n B (g \<circ> Suc)"
    using Suc.prems(3) hd B by (simp add: mwr_digits_Suc)
  then show ?case
    using Suc hd tail by (smt (cvc5, best) comp_apply less_Suc_eq_0_disj)
qed

definition mwr_kronecker where
  "mwr_kronecker m B I \<equiv>
    mwr_digits m B (Poly_Mapping.lookup I)"

lemma mwr_kronecker_add:
  "mwr_kronecker m B (I + J) = mwr_kronecker m B I + mwr_kronecker m B J"
  by (simp add: mwr_kronecker_def mwr_digits_def lookup_add sum.distrib algebra_simps)

lemma mwr_kronecker_single:
  assumes v: "v<m"
  shows "mwr_kronecker m B (Poly_Mapping.single v n) = n * B^v"
  using v by (simp add: mwr_kronecker_def mwr_digits_def
    lookup_single when_def sum.remove[of "{..<m}" v])

lemma mwr_kronecker_inj:
  assumes pos: "0 < B" and B: "\<forall>v<m. r v < B"
    and I: "I \<in> pjet_exponent_box m r"
    and J: "J \<in> pjet_exponent_box m r"
    and eq: "mwr_kronecker m B I = mwr_kronecker m B J"
  shows "I = J"
proof (rule Poly_Mapping.poly_mapping_eqI)
  fix v
  have ib: "\<forall>u<m. Poly_Mapping.lookup I u < B"
    using I B pjet_exponent_boxD(2) by (meson le_less_trans)
  have jb: "\<forall>u<m. Poly_Mapping.lookup J u < B"
    using J B pjet_exponent_boxD(2) by (meson le_less_trans)
  show "Poly_Mapping.lookup I v = Poly_Mapping.lookup J v"
  proof (cases "v<m")
    case True
    with eq ib jb pos mwr_digits_inj mwr_kronecker_def show ?thesis
      by auto
  next
    case False
    then obtain "v \<notin> Poly_Mapping.keys I" "v \<notin> Poly_Mapping.keys J"
      using pjet_exponent_boxD(1) I J by force
    then show ?thesis
      by (simp add: not_in_keys_iff_lookup_eq_zero)
  qed
qed

definition mwr_ksubst where
  "mwr_ksubst m B P \<equiv>
    (\<Sum>I\<in>Poly_Mapping.keys (mapping_of P).
      Polynomial.monom (MPoly_Type.coeff P I)
        (mwr_kronecker m B I))"

lemma mwr_ksubst_box:
  fixes P :: "rat mpoly"
  assumes box: "pjet_poly_in_box m r P"
  shows "mwr_ksubst m B P =
    (\<Sum>I\<in>pjet_exponent_box m r. Polynomial.monom (MPoly_Type.coeff P I) (mwr_kronecker m B I))"
  unfolding mwr_ksubst_def
proof (intro sum.mono_neutral_cong_left)
  show "Poly_Mapping.keys (mapping_of P) \<subseteq> pjet_exponent_box m r"
    using box by (simp add: pjet_poly_in_box_def)
qed (auto simp: coeff_keys)

lemma mwr_ksubst_add:
  fixes P Q :: "rat mpoly"
  assumes P: "pjet_poly_in_box m r P"
    and Q: "pjet_poly_in_box m r Q"
  shows "mwr_ksubst m B (P+Q) = mwr_ksubst m B P + mwr_ksubst m B Q"
  by (simp add: mwr_ksubst_box[OF pjet_poly_in_box_add[OF P Q]]
    mwr_ksubst_box[OF P] mwr_ksubst_box[OF Q]
    MPoly_Type.coeff_def plus_mpoly.rep_eq lookup_add
    Polynomial.add_monom[symmetric] sum.distrib)

lemma mwr_box_smult:
  fixes P :: "rat mpoly"
  assumes box: "pjet_poly_in_box m r P"
  shows "pjet_poly_in_box m r (MPoly_Type.smult c P)"
  using box by (auto simp: pjet_poly_in_box_def in_keys_iff
    MPoly_Type.coeff_def[symmetric] pjet_coeff_smult_rat)

lemma mwr_sum_smult:
  fixes f :: "'a \<Rightarrow> rat poly"
  shows "Polynomial.smult c (\<Sum>x\<in>S. f x) = (\<Sum>x\<in>S. Polynomial.smult c (f x))"
proof -
  have cv: "Polynomial.smult c P = [:c:] * P"
    for c :: rat and P :: "rat poly" by simp
  show ?thesis by (simp only: cv sum_distrib_left)
qed

lemma mwr_ksubst_smult:
  fixes P :: "rat mpoly"
  assumes P: "pjet_poly_in_box m r P"
  shows "mwr_ksubst m B (MPoly_Type.smult c P) = Polynomial.smult c (mwr_ksubst m B P)"
  by (simp add: mwr_ksubst_box[OF mwr_box_smult[OF P]]
    mwr_ksubst_box[OF P] pjet_coeff_smult_rat
    Polynomial.smult_monom mwr_sum_smult)

lemma mwr_ksubst_zero [simp]:
  "mwr_ksubst m B (0::rat mpoly) = 0"
  by (simp add: mwr_ksubst_def zero_mpoly.rep_eq)

lemma mwr_ksubst_sum:
  fixes P :: "'a \<Rightarrow> rat mpoly"
  assumes fin: "finite S"
    and box: "\<And>i. i\<in>S \<Longrightarrow> pjet_poly_in_box m r (P i)"
  shows "mwr_ksubst m B (\<Sum>i\<in>S. P i) = (\<Sum>i\<in>S. mwr_ksubst m B (P i))"
  using fin box
proof (induction S rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x S)
  then have "pjet_poly_in_box m r (\<Sum>i\<in>S. P i)"
    by (simp add: pjet_poly_in_box_sum)
  then show ?case using insert
    by (force simp: mwr_ksubst_add)
qed

lemma mwr_ksubst_coeff:
  fixes P :: "rat mpoly"
  assumes box: "pjet_poly_in_box m r P"
    and pos: "0 < B" and B: "\<forall>v<m. r v < B"
    and I: "I \<in> pjet_exponent_box m r"
  shows "Polynomial.coeff (mwr_ksubst m B P) (mwr_kronecker m B I) = MPoly_Type.coeff P I"
proof -
  let ?K = "Poly_Mapping.keys (mapping_of P)"
  have "\<And>J. J \<in> ?K \<Longrightarrow>
      mwr_kronecker m B J = mwr_kronecker m B I \<longleftrightarrow> J = I"
    using mwr_kronecker_inj[OF pos B _ I] box
    by (auto simp: pjet_poly_in_box_def)
  then show ?thesis
    by (simp add: mwr_ksubst_def coeff_sum coeff_def not_in_keys_iff_lookup_eq_zero)
qed

lemma mwr_ksubst_reflect_zero:
  fixes P :: "rat mpoly"
  assumes "pjet_poly_in_box m r P"
    and "0 < B" and B: "\<forall>v<m. r v < B"
    and "mwr_ksubst m B P = 0"
  shows "P = 0"
proof (rule coeff_all_0)
  fix I
  show "MPoly_Type.coeff P I = 0"
  using assms by (metis pjet_coeff_zero_outside_box mwr_ksubst_coeff zero_poly.rep_eq)
qed

definition mwr_mpoly_indep ::
  "nat \<Rightarrow> (nat \<Rightarrow> rat mpoly) \<Rightarrow> bool" where
  "mwr_mpoly_indep k p \<equiv>
    (\<forall>c. (\<Sum>j<k. MPoly_Type.smult (c j) (p j)) = 0 \<longrightarrow> (\<forall>j<k. c j = 0))"

lemma mwr_ksubst_indep:
  fixes p :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>j<k. pjet_poly_in_box m r (p j)"
    and pos: "0 < B" and B: "\<forall>v<m. r v < B"
    and ind: "mwr_mpoly_indep k p"
  shows "poly_indep k (\<lambda>j. mwr_ksubst m B (p j))"
  unfolding poly_indep_def
proof (intro allI impI)
  fix c j
  assume z: "(\<Sum>i<k. Polynomial.smult (c i) (mwr_ksubst m B (p i))) = 0"
    and j: "j<k"
  let ?U = "\<lambda>i. MPoly_Type.smult (c i) (p i)"
  have ub: "\<And>i. i<k \<Longrightarrow> pjet_poly_in_box m r (?U i)"
    using box by (auto intro: mwr_box_smult)
  have sb: "pjet_poly_in_box m r (\<Sum>i<k. ?U i)"
    by (rule pjet_poly_in_box_sum) (use ub in auto)
  have hom0: "mwr_ksubst m B (\<Sum>i<k. ?U i) = (\<Sum>i<k. mwr_ksubst m B (?U i))"
    by (rule mwr_ksubst_sum) (use ub in auto)
  have hom1: "(\<Sum>i<k. mwr_ksubst m B (?U i)) =
      (\<Sum>i<k. Polynomial.smult (c i) (mwr_ksubst m B (p i)))"
    by (rule sum.cong)
      (use box in \<open>auto simp: mwr_ksubst_smult\<close>)
  have mz: "(\<Sum>i<k. ?U i) = 0"
    by (rule mwr_ksubst_reflect_zero[OF sb pos B])
      (use z hom0 hom1 in simp)
  show "c j = 0"
    using ind mz j by (auto simp: mwr_mpoly_indep_def)
qed

lemma mwr_kronecker_wr_nonzero:
  fixes p :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>j<k. pjet_poly_in_box m r (p j)"
    and pos: "0<B" and B: "\<forall>v<m. r v<B"
    and ind: "mwr_mpoly_indep k p"
  shows "hwronskian k (\<lambda>j. mwr_ksubst m B (p j)) \<noteq> 0"
using B box ind pos mwr_ksubst_indep wr_independent by presburger

section \<open>The first derivative of Kronecker substitution\<close>

lemma mwr_ksubst_monom:
  fixes c :: rat
  shows "mwr_ksubst m B (MPoly_Type.monom I c) = Polynomial.monom c (mwr_kronecker m B I)"
  by (simp add: mwr_ksubst_def MPoly_Type.coeff_def lookup_single when_def)

lemma mwr_ksubst_monom_deriv:
  fixes c :: rat
  shows "pderiv (mwr_ksubst m B (MPoly_Type.monom I c)) =
    (\<Sum>v<m. Polynomial.monom
      (of_nat (Poly_Mapping.lookup I v * B^v) * c)
      (mwr_kronecker m B I - 1))"
  by (simp add: mwr_ksubst_monom pderiv_monom
    Polynomial.monom_sum[symmetric] mwr_kronecker_def
    mwr_digits_def sum_distrib_right[symmetric])

lemma mwr_mchoose_single_one:
  "pjet_mchoose I (Poly_Mapping.single v 1) = Poly_Mapping.lookup I v"
  by (simp add: pjet_mchoose_def prod.remove[of "insert v (Poly_Mapping.keys I)" v]
    lookup_single when_def)

lemma mwr_single_sub_add:
  fixes I :: "(nat,nat) poly_mapping"
  assumes h: "0 < Poly_Mapping.lookup I v"
  shows "I - Poly_Mapping.single v 1 + Poly_Mapping.single v 1 = I"
  by (rule Poly_Mapping.poly_mapping_eqI)
    (use h in \<open>auto simp: lookup_add lookup_minus
      lookup_single when_def; presburger\<close>)

lemma mwr_hasse_monom_single_one:
  fixes c :: rat
  shows "pjet_hasse (Poly_Mapping.single v 1) (MPoly_Type.monom I c) =
    MPoly_Type.monom (I - Poly_Mapping.single v 1) (c * of_nat (Poly_Mapping.lookup I v))"
  using mwr_mchoose_single_one[of I v]
  by (simp add: pjet_hasse_monom_exact)

lemma mwr_monom_zero [simp]: "MPoly_Type.monom I (0::rat) = 0"
  by (simp add: mapping_of_inject[symmetric] zero_mpoly.rep_eq)

lemma mwr_kronecker_sub_single:
  assumes v: "v<m" and h: "0<Poly_Mapping.lookup I v"
  shows "mwr_kronecker m B (I - Poly_Mapping.single v 1) + B^v = mwr_kronecker m B I"
  using mwr_kronecker_add[of m B
      "I - Poly_Mapping.single v 1" "Poly_Mapping.single v 1"]
    mwr_single_sub_add[OF h] mwr_kronecker_single[OF v, of B 1]
  by simp

lemma mwr_kronecker_sub_power:
  assumes v: "v<m" and B: "0<B"
    and h: "0<Poly_Mapping.lookup I v"
  shows "B^v - 1 + mwr_kronecker m B (I - Poly_Mapping.single v 1) = mwr_kronecker m B I - 1"
  using mwr_kronecker_sub_single[OF v h, of B] B by simp

lemma mwr_ksubst_monom_chain_term:
  fixes c :: rat
  assumes v: "v<m" and B: "0<B"
  shows "Polynomial.monom (of_nat (B^v)) (B^v-1) *
      mwr_ksubst m B
        (pjet_hasse (Poly_Mapping.single v 1)
          (MPoly_Type.monom I c)) =
    Polynomial.monom
      (of_nat (Poly_Mapping.lookup I v * B^v) * c)
      (mwr_kronecker m B I - 1)"
proof (cases "Poly_Mapping.lookup I v = 0")
  case True
  then show ?thesis
    using mwr_hasse_monom_single_one[of v I c] True by simp
next
  case False
  then have h: "0<Poly_Mapping.lookup I v" by simp
  show ?thesis
    using mwr_hasse_monom_single_one[of v I c] mwr_kronecker_sub_power[OF v B h]
    by (simp add: mwr_ksubst_monom Polynomial.mult_monom algebra_simps)
qed

lemma mwr_ksubst_monom_chain:
  fixes c :: rat
  assumes B: "0<B"
  shows "pderiv (mwr_ksubst m B (MPoly_Type.monom I c)) =
    (\<Sum>v<m. Polynomial.monom (of_nat (B^v)) (B^v-1) *
      mwr_ksubst m B
        (pjet_hasse (Poly_Mapping.single v 1)
          (MPoly_Type.monom I c)))"
  using mwr_ksubst_monom_chain_term mwr_ksubst_monom_deriv[of m B I c] assms
  by auto

lemma mwr_poly_pderiv_sum:
  fixes f :: "'a \<Rightarrow> rat poly"
  assumes "finite S"
  shows "pderiv (\<Sum>i\<in>S. f i) = (\<Sum>i\<in>S. pderiv (f i))"
  using assms by (induction S rule: finite_induct) (simp_all add: pderiv_add)

lemma mwr_ksubst_hasse_sum:
  fixes P :: "'a \<Rightarrow> rat mpoly"
  assumes fin: "finite S"
    and box: "\<And>i. i\<in>S \<Longrightarrow> pjet_poly_in_box m r (P i)"
  shows "mwr_ksubst m B (pjet_hasse J (\<Sum>i\<in>S. P i)) =
    (\<Sum>i\<in>S. mwr_ksubst m B (pjet_hasse J (P i)))"
using box fin by (metis pjet_hasse_preserves_box pjet_hasse_sum mwr_ksubst_sum)

lemma mwr_poly_weighted_sum_swap:
  fixes f :: "'a \<Rightarrow> nat \<Rightarrow> rat poly"
    and w :: "nat \<Rightarrow> rat poly"
  assumes fin: "finite S"
  shows "(\<Sum>I\<in>S. \<Sum>v<m. w v * f I v) = (\<Sum>v<m. w v * (\<Sum>I\<in>S. f I v))"
  by (subst sum.swap) (simp add: sum_distrib_left)

lemma mwr_ksubst_chain_sum:
  fixes P :: "'a \<Rightarrow> rat mpoly"
  assumes fin: "finite S"
    and box: "\<And>i. i\<in>S \<Longrightarrow> pjet_poly_in_box m r (P i)"
    and chain: "\<And>i. i\<in>S \<Longrightarrow>
      pderiv (mwr_ksubst m B (P i)) =
      (\<Sum>v<m. Polynomial.monom (of_nat (B^v)) (B^v-1) *
        mwr_ksubst m B (pjet_hasse (Poly_Mapping.single v 1) (P i)))"
  shows "pderiv (mwr_ksubst m B (\<Sum>i\<in>S. P i)) =
    (\<Sum>v<m. Polynomial.monom (of_nat (B^v)) (B^v-1) *
      mwr_ksubst m B
        (pjet_hasse (Poly_Mapping.single v 1) (\<Sum>i\<in>S. P i)))"
proof -
  let ?w = "\<lambda>v. Polynomial.monom (of_nat (B^v)) (B^v-1)"
  have "pderiv (mwr_ksubst m B (\<Sum>i\<in>S. P i)) =
      (\<Sum>i\<in>S. pderiv (mwr_ksubst m B (P i)))"
    by (simp add: mwr_ksubst_sum[OF fin box] mwr_poly_pderiv_sum[OF fin])
  also have "\<dots> = (\<Sum>i\<in>S. \<Sum>v<m. ?w v *
        mwr_ksubst m B (pjet_hasse (Poly_Mapping.single v 1) (P i)))"
    by (use chain in auto)
  finally show ?thesis using mwr_poly_weighted_sum_swap[OF fin] mwr_ksubst_hasse_sum[OF fin box]
    by simp
qed

lemma mwr_ksubst_chain:
  fixes P :: "rat mpoly"
  assumes box: "pjet_poly_in_box m r P" and B: "0<B"
  shows "pderiv (mwr_ksubst m B P) =
    (\<Sum>v<m. Polynomial.monom (of_nat (B^v)) (B^v-1) *
      mwr_ksubst m B (pjet_hasse (Poly_Mapping.single v 1) P))"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of P)"
  let ?Q = "\<lambda>I. MPoly_Type.monom I (MPoly_Type.coeff P I)"
  have pe: "P = (\<Sum>I\<in>?S. ?Q I)"
    by (rule pjet_sum_monom)
  have qb: "\<And>I. I\<in>?S \<Longrightarrow> pjet_poly_in_box m r (?Q I)"
    using box by (auto intro: pjet_poly_in_box_monom
      simp: pjet_poly_in_box_def)
  show ?thesis using pe mwr_ksubst_chain_sum[OF finite_keys qb] mwr_ksubst_monom_chain[OF B]
  by fastforce
qed

section \<open>Iteration of the Kronecker chain rule\<close>

lemma mwr_hasse_first_comp:
  fixes P :: "rat mpoly"
  shows "pjet_hasse (Poly_Mapping.single v 1) (pjet_hasse J P) =
    Const (of_nat (Suc (Poly_Mapping.lookup J v))) *
      pjet_hasse (J + Poly_Mapping.single v 1) P"
proof -
  have e: "pjet_mchoose (J + Poly_Mapping.single v 1)
      (Poly_Mapping.single v 1) = Suc (Poly_Mapping.lookup J v)"
    unfolding mwr_mchoose_single_one
    by (simp add: lookup_add lookup_single when_def)
  show ?thesis
    using pjet_hasse_comp[of "Poly_Mapping.single v 1" J P] e
    by (simp add: add.commute)
qed

lemma mwr_ksubst_Const_mult:
  fixes P :: "rat mpoly"
  assumes "pjet_poly_in_box m r P"
  shows "mwr_ksubst m B (Const c * P) = Polynomial.smult c (mwr_ksubst m B P)"
  using mwr_ksubst_smult[OF assms, of B c]
  by (simp add: smult_conv_mult pjet_Const_monom)

lemma mwr_monom_smult_swap:
  fixes q :: "rat poly"
  shows "Polynomial.monom c n * Polynomial.smult d q = Polynomial.monom (c*d) n * q"
  by (simp add: monom_altdef mult.commute)

lemma mwr_ksubst_hasse_first:
  fixes P :: "rat mpoly"
  assumes box: "pjet_poly_in_box m r P" and B: "0<B"
  shows "pderiv (mwr_ksubst m B (pjet_hasse J P)) =
    (\<Sum>v<m. Polynomial.monom
      (of_nat (B^v * Suc (Poly_Mapping.lookup J v))) (B^v-1) *
      mwr_ksubst m B
        (pjet_hasse (J + Poly_Mapping.single v 1) P))"
proof -
  have hb: "pjet_poly_in_box m r (pjet_hasse J P)"
    by (rule pjet_hasse_preserves_box[OF box])
  have h: "pderiv (mwr_ksubst m B (pjet_hasse J P)) =
    (\<Sum>v<m. Polynomial.monom (of_nat (B^v)) (B^v-1) *
      mwr_ksubst m B
        (pjet_hasse (Poly_Mapping.single v 1) (pjet_hasse J P)))"
    by (rule mwr_ksubst_chain[OF hb B])
  show ?thesis
    unfolding h
  proof (rule sum.cong)
    show "{..<m} = {..<m}" by simp
    fix v
    assume "v \<in> {..<m}"
    have hb2: "pjet_poly_in_box m r
      (pjet_hasse (J + Poly_Mapping.single v 1) P)"
      by (rule pjet_hasse_preserves_box[OF box])
    show "Polynomial.monom (of_nat (B ^ v)) (B ^ v - 1) *
        mwr_ksubst m B
          (pjet_hasse (Poly_Mapping.single v 1) (pjet_hasse J P)) =
      Polynomial.monom
        (of_nat (B ^ v * Suc (Poly_Mapping.lookup J v)))
        (B ^ v - 1) *
        mwr_ksubst m B
          (pjet_hasse (J + Poly_Mapping.single v 1) P)"
      by (simp only: mwr_hasse_first_comp
        mwr_ksubst_Const_mult[OF hb2] mwr_monom_smult_swap)
        (simp add: algebra_simps)
  qed
qed

lemma mwr_ksubst_hasse_weighted_deriv:
  fixes P :: "rat mpoly" and a :: "rat poly"
  assumes box: "pjet_poly_in_box m r P" and B: "0<B"
  shows "pderiv (a * mwr_ksubst m B (pjet_hasse J P)) =
    pderiv a * mwr_ksubst m B (pjet_hasse J P) +
    (\<Sum>v<m. (a * Polynomial.monom
        (of_nat (B^v * Suc (Poly_Mapping.lookup J v))) (B^v-1)) *
      mwr_ksubst m B
        (pjet_hasse (J + Poly_Mapping.single v 1) P))"
  by (simp add: pderiv_mult mwr_ksubst_hasse_first[OF box B]
    sum_distrib_left algebra_simps)

section \<open>Uniform expansion of higher substituted derivatives\<close>

definition mwr_total_order :: "nat \<Rightarrow> (nat,nat) poly_mapping \<Rightarrow> nat" where
  "mwr_total_order m J \<equiv> (\<Sum>v<m. Poly_Mapping.lookup J v)"

lemma mwr_total_order_add:
  "mwr_total_order m (I+J) = mwr_total_order m I + mwr_total_order m J"
  by (simp add: mwr_total_order_def lookup_add sum.distrib)

lemma mwr_total_order_single:
  assumes "v<m"
  shows "mwr_total_order m (Poly_Mapping.single v 1) = 1"
  using assms
  by (simp add: mwr_total_order_def lookup_single when_def sum.remove)

fun mwr_jet_index :: "nat option list \<Rightarrow> (nat,nat) poly_mapping" where
  "mwr_jet_index [] = 0"
| "mwr_jet_index (None # xs) = mwr_jet_index xs"
| "mwr_jet_index (Some v # xs) =
    mwr_jet_index xs + Poly_Mapping.single v 1"

definition mwr_jet_alphabet :: "nat \<Rightarrow> nat option set" where
  "mwr_jet_alphabet m = insert None (Some ` {..<m})"

definition mwr_jet_words :: "nat \<Rightarrow> nat \<Rightarrow> nat option list set" where
  "mwr_jet_words m i \<equiv> {xs. set xs \<subseteq> mwr_jet_alphabet m \<and> length xs = i}"

lemma finite_mwr_jet_words [simp]: "finite (mwr_jet_words m i)"
  by (simp add: mwr_jet_words_def mwr_jet_alphabet_def finite_lists_length_eq)

lemma mwr_jet_words_zero [simp]: "mwr_jet_words m 0 = {[]}"
  by (auto simp: mwr_jet_words_def)

lemma mwr_jet_index_order:
  assumes "set xs \<subseteq> mwr_jet_alphabet m"
  shows "mwr_total_order m (mwr_jet_index xs) \<le> length xs"
  using assms
proof (induction xs)
  case Nil
  then show ?case by (simp add: mwr_total_order_def)
next
  case (Cons a xs)
  show ?case
  proof (cases a)
    case None
    then show ?thesis using Cons
      by (simp add: mwr_jet_alphabet_def)
  next
    case (Some v)
    then have vm: "v<m"
      using Cons.prems by (auto simp: mwr_jet_alphabet_def)
    show ?thesis using Cons mwr_total_order_single[OF vm] Some
      by (simp add: mwr_total_order_add mwr_jet_alphabet_def)
  qed
qed

lemma mwr_nat_keys_add:
  fixes I J :: "(nat,nat) poly_mapping"
  shows "Poly_Mapping.keys (I+J) \<subseteq> Poly_Mapping.keys I \<union> Poly_Mapping.keys J"
proof (rule subsetI)
  fix v
  assume h: "v \<in> Poly_Mapping.keys (I+J)"
  show "v \<in> Poly_Mapping.keys I \<union> Poly_Mapping.keys J"
  proof (rule ccontr)
    assume "v \<notin> Poly_Mapping.keys I \<union> Poly_Mapping.keys J"
    then show False
      using h by (simp add: not_in_keys_iff_lookup_eq_zero lookup_add in_keys_iff)
  qed
qed

lemma mwr_jet_index_support:
  assumes "set xs \<subseteq> mwr_jet_alphabet m"
  shows "Poly_Mapping.keys (mwr_jet_index xs) \<subseteq> {..<m}"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (cases a) (auto simp: mwr_jet_alphabet_def dest: subsetD[OF mwr_nat_keys_add])
qed

lemma mwr_jet_word_bounds:
  assumes h: "xs \<in> mwr_jet_words m i"
  shows "Poly_Mapping.keys (mwr_jet_index xs) \<subseteq> {..<m}"
    "mwr_total_order m (mwr_jet_index xs) \<le> i"
proof -
  have s: "set xs \<subseteq> mwr_jet_alphabet m"
    and len: "length xs = i"
    using h by (auto simp: mwr_jet_words_def)
  show "Poly_Mapping.keys (mwr_jet_index xs) \<subseteq> {..<m}"
    by (rule mwr_jet_index_support[OF s])
  show "mwr_total_order m (mwr_jet_index xs) \<le> i"
    using mwr_jet_index_order[OF s] len by simp
qed

lemma mwr_jet_words_Suc:
  "mwr_jet_words m (Suc i) =
    ((#) None ` mwr_jet_words m i) \<union> ((\<lambda>(xs,v). Some v # xs) ` (mwr_jet_words m i \<times> {..<m}))"
  by (auto simp: mwr_jet_words_def mwr_jet_alphabet_def length_Suc_conv)

lemma mwr_sum_jet_words:
  fixes f :: "nat option list \<Rightarrow> rat poly"
  shows "(\<Sum>ys\<in>mwr_jet_words m (Suc i). f ys) =
    (\<Sum>xs\<in>mwr_jet_words m i. f (None#xs)) + (\<Sum>xs\<in>mwr_jet_words m i. \<Sum>v<m. f (Some v#xs))"
proof -
  let ?S = "mwr_jet_words m i"
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
    by (simp add: mwr_jet_words_Suc sum.union_disjoint)
qed

fun mwr_jet_coeff :: "nat \<Rightarrow> nat \<Rightarrow> nat option list \<Rightarrow> rat poly"
  where
  "mwr_jet_coeff B 0 xs = (if xs=[] then 1 else 0)"
| "mwr_jet_coeff B (Suc i) [] = 0"
| "mwr_jet_coeff B (Suc i) (None#xs) =
    pderiv (mwr_jet_coeff B i xs)"
| "mwr_jet_coeff B (Suc i) (Some v#xs) =
    mwr_jet_coeff B i xs *
      Polynomial.monom
        (of_nat (B^v * Suc (Poly_Mapping.lookup (mwr_jet_index xs) v)))
        (B^v-1)"

lemma mwr_jet_expansion:
  fixes P :: "rat mpoly"
  assumes box: "pjet_poly_in_box m r P" and B: "0<B"
  shows "(pderiv ^^ i) (mwr_ksubst m B P) =
    (\<Sum>xs\<in>mwr_jet_words m i.
      mwr_jet_coeff B i xs *
        mwr_ksubst m B (pjet_hasse (mwr_jet_index xs) P))"
  using box B
proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  then show ?case
    by (simp add: funpow_Suc_right mwr_poly_pderiv_sum
      mwr_ksubst_hasse_weighted_deriv mwr_sum_jet_words sum.distrib)
qed

section \<open>Evaluation of Kronecker substitution\<close>

lemma mwr_kronecker_keys:
  assumes h: "Poly_Mapping.keys I \<subseteq> {..<m}"
  shows "mwr_kronecker m B I = (\<Sum>v\<in>Poly_Mapping.keys I. Poly_Mapping.lookup I v * B^v)"
proof -
  have z: "\<forall>v\<in>{..<m} - Poly_Mapping.keys I.
    Poly_Mapping.lookup I v * B^v = 0"
    by (simp add: not_in_keys_iff_lookup_eq_zero)
  have eq: "(\<Sum>v\<in>Poly_Mapping.keys I. Poly_Mapping.lookup I v * B^v) =
    (\<Sum>v<m. Poly_Mapping.lookup I v * B^v)"
    by (rule sum.mono_neutral_left[OF _ h z]) simp
  show ?thesis using eq
    by (simp add: mwr_kronecker_def mwr_digits_def)
qed

lemma mwr_kronecker_power_prod:
  fixes t :: rat
  shows "(\<Prod>v\<in>S. (t^(B^v))^(Poly_Mapping.lookup I v)) = t^(\<Sum>v\<in>S. Poly_Mapping.lookup I v * B^v)"
  by (simp add: power_sum mult.commute power_mult[symmetric])

lemma mwr_insertion_kronecker_monom:
  fixes c t :: rat
  assumes supp: "Poly_Mapping.keys I \<subseteq> {..<m}"
  shows "insertion (\<lambda>v. t^(B^v)) (MPoly_Type.monom I c) = c * t^(mwr_kronecker m B I)"
  by (simp add: pjet_insertion_monom mwr_kronecker_keys[OF supp] mwr_kronecker_power_prod)

lemma mwr_insertion_monom_sum:
  fixes P :: "rat mpoly"
  shows "insertion f P =
    (\<Sum>I\<in>Poly_Mapping.keys (mapping_of P).
      insertion f (MPoly_Type.monom I (MPoly_Type.coeff P I)))"
  by (metis pjet_insertion_sum finite_keys pjet_sum_monom)

lemma mwr_poly_ksubst_eval_sum:
  fixes P :: "rat mpoly"
  shows "poly (mwr_ksubst m B P) t =
    (\<Sum>I\<in>Poly_Mapping.keys (mapping_of P). MPoly_Type.coeff P I * t^(mwr_kronecker m B I))"
  by (simp add: mwr_ksubst_def poly_sum poly_monom)

lemma mwr_box_monom_support:
  assumes box: "pjet_poly_in_box m r P"
    and I: "I\<in>Poly_Mapping.keys (mapping_of P)"
  shows "Poly_Mapping.keys I \<subseteq> {..<m}"
  using box I
  by (auto simp: pjet_poly_in_box_def dest: pjet_exponent_boxD)

lemma mwr_box_support_all:
  assumes box: "pjet_poly_in_box m r P"
  shows "\<forall>I\<in>Poly_Mapping.keys (mapping_of P). Poly_Mapping.keys I \<subseteq> {..<m}"
  using box by (auto dest: mwr_box_monom_support)

lemma mwr_ksubst_eval_insertion:
  fixes P :: "rat mpoly"
  assumes box: "pjet_poly_in_box m r P"
  shows "poly (mwr_ksubst m B P) t =
    insertion (\<lambda>v. t^(B^v)) P"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of P)"
  have s: "\<forall>I\<in>?S. Poly_Mapping.keys I \<subseteq> {..<m}"
    by (rule mwr_box_support_all[OF box])
  have c: "(\<Sum>I\<in>?S. insertion (\<lambda>v. t^(B^v)) (MPoly_Type.monom I (MPoly_Type.coeff P I))) =
    (\<Sum>I\<in>?S. MPoly_Type.coeff P I * t^(mwr_kronecker m B I))"
    using s mwr_insertion_kronecker_monom by (intro sum.cong) auto
  show ?thesis using mwr_poly_ksubst_eval_sum mwr_insertion_monom_sum[of "\<lambda>v. t^(B^v)" P] c
    by simp
qed

lemma mwr_mpoly_neg_one: "(-1::rat mpoly) = Const (-1::rat)"
  by (simp add: pjet_Const_uminus)

lemma mwr_insertion_signof:
  fixes f :: "nat \<Rightarrow> rat"
  shows "insertion f (signof q :: rat mpoly) = (signof q :: rat)"
  by (simp add: sign_def mwr_mpoly_neg_one pjet_insertion_Const)

lemma mwr_insertion_det:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat mpoly"
    and f :: "nat \<Rightarrow> rat"
  shows "insertion f (det (mat k k (\<lambda>(i,j). A i j))) =
    det (mat k k (\<lambda>(i,j). insertion f (A i j)))"
proof -
  let ?S = "{q. q permutes {..<k}}"
  have fin: "finite ?S" by (rule finite_permutations) simp
  show ?thesis
    by (simp add: det_mat_expansion
          pjet_insertion_sum[OF fin] insertion_mult
          mwr_insertion_signof pjet_insertion_prod)
qed

end
