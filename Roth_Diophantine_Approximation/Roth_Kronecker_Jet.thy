theory Roth_Kronecker_Jet
  imports Roth_Kronecker_Chain
begin

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

end
