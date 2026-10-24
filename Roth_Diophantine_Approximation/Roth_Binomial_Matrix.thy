theory Roth_Binomial_Matrix
  imports Jordan_Normal_Form.Determinant
begin

section \<open>The binomial matrix at distinct natural arguments\<close>

definition roth_binpoly :: "nat \<Rightarrow> rat poly" where
  "roth_binpoly i =
    Polynomial.smult (inverse (of_nat (fact i)))
      (\<Prod>j<i. [:-of_nat j, 1:])"

lemma roth_binpoly_degree [simp]: "degree (roth_binpoly i) = i"
  by (simp add: roth_binpoly_def degree_prod_sum_eq)

lemma roth_binpoly_lead_coeff [simp]:
  "lead_coeff (roth_binpoly i) = inverse (of_nat (fact i))"
  by (simp add: roth_binpoly_def lead_coeff_smult lead_coeff_prod)

lemma roth_binpoly_eval_nat [simp]:
  "poly (roth_binpoly i) (of_nat d) = of_nat (d choose i)"
proof -
  have eq: "(\<Prod>j<i. (of_nat d::rat) - of_nat j) =
    of_nat (fact i) * ((of_nat d::rat) gchoose i)"
    using gbinomial_mult_fact[of i "of_nat d::rat"]
    by (simp add: atLeast0LessThan)
  show ?thesis
    by (simp add: roth_binpoly_def poly_prod eq binomial_gbinomial)
qed

lemma roth_binpoly_combination_zero:
  assumes z: "(\<Sum>i<k. Polynomial.smult (c i) (roth_binpoly i)) = 0"
  shows "\<forall>i<k. c i = 0"
  using z
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have coefftop: "Polynomial.coeff (roth_binpoly k) k =
    inverse (of_nat (fact k))"
    using roth_binpoly_lead_coeff[of k] by simp
  have topcoeff:
    "Polynomial.coeff
      (\<Sum>i<Suc k. Polynomial.smult (c i) (roth_binpoly i)) k =
      c k * inverse (of_nat (fact k))"
    by (simp add: sum.lessThan_Suc coeff_sum coeff_smult
      coeff_eq_0 coefftop)
  have ck: "c k = 0"
    using Suc.prems topcoeff by simp
  have small:
    "(\<Sum>i<k. Polynomial.smult (c i) (roth_binpoly i)) = 0"
    using Suc.prems ck by (simp add: sum.lessThan_Suc)
  show ?case using Suc.IH[OF small] ck
    by (auto simp: less_Suc_eq)
qed

lemma roth_binpoly_combination_degree:
  assumes k: "0 < k"
  shows "degree
    (\<Sum>i<k. Polynomial.smult (c i) (roth_binpoly i)) < k"
  using k by (intro degree_sum_less)
    (auto simp: degree_smult_eq)

lemma roth_binomial_moment_zero:
  assumes inj: "inj_on d {..<k}"
    and z: "\<forall>j<k. (\<Sum>i<k. c i * of_nat (d j choose i)) =
      (0::rat)"
  shows "\<forall>i<k. c i = 0"
proof (cases "k=0")
  case True
  then show ?thesis by simp
next
  case False
  let ?F = "\<Sum>i<k. Polynomial.smult (c i) (roth_binpoly i)"
  let ?A = "(\<lambda>j. of_nat (d j)::rat) ` {..<k}"
  have injrat: "inj_on (\<lambda>j. of_nat (d j)::rat) {..<k}"
    using inj by (auto simp: inj_on_def)
  have cardA: "card ?A = k"
    using injrat by (simp add: card_image)
  have roots: "poly ?F x = 0" if "x \<in> ?A" for x
    using that z by (auto simp: poly_sum)
  have deg: "degree ?F < k"
    using False by (intro roth_binpoly_combination_degree) simp
  have F0: "?F = 0"
    by (rule poly_eqI_degree[where A="?A"])
      (use roots cardA deg False in auto)
  show ?thesis
    using roth_binpoly_combination_zero[OF F0] by simp
qed

lemma roth_binomial_det_nonzero:
  assumes inj: "inj_on d {..<k}"
  shows "det (mat k k
    (\<lambda>(i,j). (of_nat (d i choose j)::rat))) \<noteq> 0"
proof
  let ?B = "mat k k (\<lambda>(i,j). (of_nat (d i choose j)::rat))"
  assume det0: "det ?B = 0"
  have B: "?B \<in> carrier_mat k k" by simp
  obtain v where v: "v \<in> carrier_vec k"
    and vnz: "v \<noteq> zero_vec k"
    and Av: "mult_mat_vec ?B v = zero_vec k"
    using det_0_iff_vec_prod_zero_field[OF B] det0 by blast
  have z:
    "\<forall>j<k. (\<Sum>i<k. (v $ i) * of_nat (d j choose i)) =
      (0::rat)"
  proof (intro allI impI)
    fix j
    assume j: "j<k"
    have aj: "(mult_mat_vec ?B v) $ j = 0"
      using Av j by simp
    show "(\<Sum>i<k. (v $ i) * of_nat (d j choose i)) = (0::rat)"
      using aj j v
      by (simp add: scalar_prod_def atLeast0LessThan mult.commute)
  qed
  have vz: "\<forall>i<k. v $ i = 0"
    by (rule roth_binomial_moment_zero[OF inj z])
  show False using v vnz vz by (auto simp: vec_eq_iff)
qed

lemma roth_binomial_det_nonzero_transpose:
  assumes inj: "inj_on d {..<k}"
  shows "det (mat k k
    (\<lambda>(i,j). (of_nat (d j choose i)::rat))) \<noteq> 0"
proof -
  have tr:
    "transpose_mat (mat k k
      (\<lambda>(i,j). (of_nat (d i choose j)::rat))) =
    mat k k (\<lambda>(i,j). of_nat (d j choose i))"
    by (intro eq_matI) auto
  show ?thesis
    using tr
      det_transpose[of
        "mat k k (\<lambda>(i,j). (of_nat (d i choose j)::rat))" k]
      roth_binomial_det_nonzero[OF inj]
    by simp
qed

end
