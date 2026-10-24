theory Roth_Kronecker_Chain
  imports Roth_Kronecker
begin

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

end
