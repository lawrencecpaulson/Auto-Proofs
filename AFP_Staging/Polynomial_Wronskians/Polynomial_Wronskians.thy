theory Polynomial_Wronskians
  imports Jordan_Normal_Form.Determinant
begin

section \<open>The binomial matrix at distinct natural arguments\<close>

definition binpoly :: "nat \<Rightarrow> rat poly" where
  "binpoly i =
    Polynomial.smult (inverse (of_nat (fact i)))
      (\<Prod>j<i. [:-of_nat j, 1:])"

lemma binpoly_degree [simp]: "degree (binpoly i) = i"
  by (simp add: binpoly_def degree_prod_sum_eq)

lemma binpoly_lead_coeff [simp]:
  "lead_coeff (binpoly i) = inverse (of_nat (fact i))"
  by (simp add: binpoly_def lead_coeff_smult lead_coeff_prod)

lemma binpoly_eval_nat [simp]:
  "poly (binpoly i) (of_nat d) = of_nat (d choose i)"
proof -
  have eq: "(\<Prod>j<i. (of_nat d::rat) - of_nat j) =
    of_nat (fact i) * ((of_nat d::rat) gchoose i)"
    using gbinomial_mult_fact[of i "of_nat d::rat"]
    by (simp add: atLeast0LessThan)
  show ?thesis
    by (simp add: binpoly_def poly_prod eq binomial_gbinomial)
qed

lemma binpoly_combination_zero:
  assumes z: "(\<Sum>i<k. Polynomial.smult (c i) (binpoly i)) = 0"
  shows "\<forall>i<k. c i = 0"
  using z
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have coefftop: "Polynomial.coeff (binpoly k) k =
    inverse (of_nat (fact k))"
    using binpoly_lead_coeff[of k] by simp
  have topcoeff:
    "Polynomial.coeff
      (\<Sum>i<Suc k. Polynomial.smult (c i) (binpoly i)) k =
      c k * inverse (of_nat (fact k))"
    by (simp add: coeff_sum coeff_eq_0 coefftop)
  have ck: "c k = 0"
    using Suc.prems topcoeff by simp
  have small: "(\<Sum>i<k. Polynomial.smult (c i) (binpoly i)) = 0"
    using Suc.prems ck by simp
  show ?case using Suc.IH[OF small] ck
    by (auto simp: less_Suc_eq)
qed

lemma binpoly_combination_degree:
  assumes k: "0 < k"
  shows "degree (\<Sum>i<k. Polynomial.smult (c i) (binpoly i)) < k"
  using k by (intro degree_sum_less) auto

lemma binomial_moment_zero:
  fixes c :: "nat \<Rightarrow> rat"
  assumes inj: "inj_on d {..<k}"
    and z: "\<forall>j<k. (\<Sum>i<k. c i * of_nat (d j choose i)) = 0"
  shows "\<forall>i<k. c i = 0"
proof (cases "k=0")
  case True
  then show ?thesis by simp
next
  case False
  let ?F = "\<Sum>i<k. Polynomial.smult (c i) (binpoly i)"
  let ?A = "(\<lambda>j. of_nat (d j)::rat) ` {..<k}"
  have injrat: "inj_on (\<lambda>j. of_nat (d j)::rat) {..<k}"
    using inj by (auto simp: inj_on_def)
  have cardA: "card ?A = k"
    using injrat by (simp add: card_image)
  have roots: "poly ?F x = 0" if "x \<in> ?A" for x
    using that z by (auto simp: poly_sum)
  have deg: "degree ?F < k"
    using False by (intro binpoly_combination_degree) simp
  have F0: "?F = 0"
    by (rule poly_eqI_degree[where A="?A"])
      (use roots cardA deg False in auto)
  show ?thesis
    using binpoly_combination_zero[OF F0] by simp
qed

lemma binomial_det_nonzero:
  assumes inj: "inj_on d {..<k}"
  shows "det (mat k k (\<lambda>(i,j). (of_nat (d i choose j)::rat))) \<noteq> 0"
proof
  let ?B = "mat k k (\<lambda>(i,j). (of_nat (d i choose j)::rat))"
  assume det0: "det ?B = 0"
  have B: "?B \<in> carrier_mat k k" by simp
  obtain v where v: "v \<in> carrier_vec k"
    and vnz: "v \<noteq> zero_vec k"
    and Av: "mult_mat_vec ?B v = zero_vec k"
    using det_0_iff_vec_prod_zero_field[OF B] det0 by blast
  have z: "\<forall>j<k. (\<Sum>i<k. (v $ i) * of_nat (d j choose i)) = 0"
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
    by (rule binomial_moment_zero[OF inj z])
  show False using v vnz vz by (auto simp: vec_eq_iff)
qed

lemma binomial_det_nonzero_transpose:
  assumes inj: "inj_on d {..<k}"
  shows "det (mat k k
    (\<lambda>(i,j). (of_nat (d j choose i)::rat))) \<noteq> 0"
proof -
  have tr:
    "transpose_mat (mat k k
      (\<lambda>(i,j). (of_nat (d i choose j)::rat))) = mat k k (\<lambda>(i,j). of_nat (d j choose i))"
    by (intro eq_matI) auto
  show ?thesis
    using tr
      det_transpose[of
        "mat k k (\<lambda>(i,j). (of_nat (d i choose j)::rat))" k]
      binomial_det_nonzero[OF inj]
    by simp
qed

section \<open>Hasse derivatives and Wronskians of rational polynomials\<close>

definition hderiv :: "nat \<Rightarrow> rat poly \<Rightarrow> rat poly" where
  "hderiv k p = Polynomial.smult (inverse (of_nat (fact k))) ((pderiv ^^ k) p)"

lemma hderiv_coeff [simp]:
  "Polynomial.coeff (hderiv k p) n =
    Polynomial.coeff p (n + k) * of_nat ((n + k) choose k)"
proof -
  have binom: "(of_nat ((n + k) choose k)::rat) =
    pochhammer (of_nat (Suc n)) k / of_nat (fact k)"
    using gbinomial_pochhammer'[of "of_nat (n + k)::rat" k]
    by (simp add: binomial_gbinomial add.commute)
  show ?thesis
    by (simp add: hderiv_def coeff_higher_pderiv binom divide_inverse mult_ac)
qed

lemma hderiv_zero [simp]: "hderiv 0 p = p"
  by (rule poly_eqI) simp

lemma hderiv_one [simp]: "hderiv 1 p = pderiv p"
  by (rule poly_eqI) (simp add: coeff_pderiv)

lemma hderiv_add [simp]:
  "hderiv k (p + q) = hderiv k p + hderiv k q"
  by (rule poly_eqI) (simp add: algebra_simps)

lemma hderiv_smult [simp]:
  "hderiv k (Polynomial.smult c p) =
    Polynomial.smult c (hderiv k p)"
  by (rule poly_eqI) auto

lemma hderiv_monom:
  "hderiv k (monom c n) =
    (if k \<le> n then monom (c * of_nat (n choose k)) (n-k) else 0)"
  by (rule poly_eqI) auto

lemma hderiv_degree_le:
  "degree (hderiv k p) \<le> degree p - k"
  by (rule degree_le) (auto simp: coeff_eq_0)

lemma hderiv_gt_degree [simp]:
  assumes "degree p < k"
  shows "hderiv k p = 0"
    using assms by (intro poly_eqI) (simp add: coeff_eq_0)

lemma hderiv_degree:
  assumes p: "p \<noteq> 0" and k: "k \<le> degree p"
  shows "degree (hderiv k p) = degree p - k"
proof (rule antisym)
  show "degree (hderiv k p) \<le> degree p - k"
    by (rule hderiv_degree_le)
  have nz: "Polynomial.coeff (hderiv k p) (degree p - k) \<noteq> 0"
    using p k by simp
  then show "degree p - k \<le> degree (hderiv k p)"
    by (rule le_degree)
qed

lemma hderiv_nonzero:
  assumes p: "p \<noteq> 0" and i: "i \<le> degree p"
  shows "hderiv i p \<noteq> 0"
proof -
  have c: "Polynomial.coeff (hderiv i p) (degree p - i) \<noteq> 0"
    using p i by simp
  show ?thesis using c by (metis coeff_0)
qed

lemma hderiv_lead_coeff:
  assumes p: "p \<noteq> 0" and k: "k \<le> degree p"
  shows "lead_coeff (hderiv k p) =
    lead_coeff p * of_nat (degree p choose k)"
  using p k by (simp add: hderiv_degree)

lemma coeff_prod_top:
  fixes f :: "'i \<Rightarrow> rat poly"
  assumes "\<forall>i\<in>S. f i \<noteq> 0"
  shows "Polynomial.coeff (\<Prod>i\<in>S. f i) (\<Sum>i\<in>S. degree (f i)) = (\<Prod>i\<in>S. lead_coeff (f i))"
  using degree_prod_eq_sum_degree[of S f] lead_coeff_prod[of f S] assms by force

lemma permutes_bounded:
  assumes q: "q permutes {..<k}" and i: "i<k"
  shows "q i < k"
  using permutes_image[OF q] i by blast

lemma permutes_degree_diff:
  assumes q: "q permutes {..<k}"
    and good: "\<forall>i<k. i \<le> degree (p (q i))"
  shows "(\<Sum>i<k. degree (p (q i)) - i) = (\<Sum>i<k. degree (p i)) - (\<Sum>i<k. i)"
proof -
  have "(\<Sum>i<k. degree (p (q i)) - i) =
    (\<Sum>i<k. degree (p (q i))) - (\<Sum>i<k. i)"
    by (rule sum_subtractf_nat) (use good in auto)
  also have "\<dots> = (\<Sum>i<k. degree (p i)) - (\<Sum>i<k. i)"
  proof -
    have "(\<Sum>i<k. degree (p (q i))) = (\<Sum>i<k. degree (p i))"
      by (rule sum.permutes_inv[OF q])
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma wr_lead_good:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes q: "q permutes {..<k}"
    and pnz: "\<forall>j<k. p j \<noteq> 0"
    and good: "\<forall>i<k. i \<le> degree (p (q i))"
  shows "(\<Prod>i<k. lead_coeff (hderiv i (p (q i)))) = (\<Prod>i<k. lead_coeff (p (q i)) * of_nat (degree (p (q i)) choose i))"
proof (rule prod.cong)
  fix i
  assume i: "i\<in>{..<k}"
  have pq: "p (q i) \<noteq> 0"
    using pnz permutes_bounded[OF q] i by auto
  show "lead_coeff (hderiv i (p (q i))) =
    lead_coeff (p (q i)) * of_nat (degree (p (q i)) choose i)"
    by (rule hderiv_lead_coeff[OF pq]) (use good i in auto)
qed simp

lemma wr_term_good:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes q: "q permutes {..<k}"
    and pnz: "\<forall>j<k. p j \<noteq> 0"
    and good: "\<forall>i<k. i \<le> degree (p (q i))"
  shows "Polynomial.coeff (\<Prod>i<k. hderiv i (p (q i))) ((\<Sum>j<k. degree (p j)) - (\<Sum>i<k. i)) =
    (\<Prod>i<k. lead_coeff (p (q i)) * of_nat (degree (p (q i)) choose i))"
proof -
  have nz: "\<forall>i<k. hderiv i (p (q i)) \<noteq> 0"
    by (simp add: good pnz q hderiv_nonzero permutes_bounded)
  have deg: "(\<Sum>j<k. degree (p j)) - (\<Sum>i<k. i) = (\<Sum>i<k. degree (hderiv i (p (q i))))"
    using nz good pnz q
    by (simp add: hderiv_degree permutes_degree_diff
      permutes_bounded)
  have top: "Polynomial.coeff (\<Prod>i<k. hderiv i (p (q i))) ((\<Sum>j<k. degree (p j)) - (\<Sum>i<k. i)) =
             (\<Prod>i<k. lead_coeff (hderiv i (p (q i))))"
    unfolding deg
    by (rule coeff_prod_top) (use nz in auto)
  show ?thesis using top wr_lead_good[OF q pnz good] by simp
qed

lemma wr_term_bad:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes "\<exists>i<k. degree (p (q i)) < i"
  shows "(\<Prod>i<k. hderiv i (p (q i))) = 0 \<and>
    (\<Prod>i<k. of_nat (degree (p (q i)) choose i)::rat) = 0"
using assms by force

lemma wr_term_bad_coeff:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes "\<exists>i<k. degree (p (q i)) < i"
  shows "Polynomial.coeff (\<Prod>i<k. hderiv i (p (q i))) M =
         (\<Prod>j<k. lead_coeff (p j)) * (\<Prod>i<k. of_nat (degree (p (q i)) choose i))"
by (simp add: assms wr_term_bad)

lemma wr_term:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes q: "q permutes {..<k}" and pnz: "\<forall>j<k. p j \<noteq> 0"
  shows "Polynomial.coeff
    (\<Prod>i<k. hderiv i (p (q i))) ((\<Sum>j<k. degree (p j)) - (\<Sum>i<k. i)) =
    (\<Prod>j<k. lead_coeff (p j)) * (\<Prod>i<k. of_nat (degree (p (q i)) choose i))"
proof (cases "\<forall>i<k. i \<le> degree (p (q i))")
  case True
  have eq: "(\<Prod>i<k. lead_coeff (p (q i))) = (\<Prod>i<k. lead_coeff (p i))"
    by (rule prod.permutes_inv[OF q])
  with True wr_term_good[OF q pnz True]
  show ?thesis
    by (auto simp add: prod.distrib)
next
  case False then show ?thesis
    using not_le_imp_less wr_term_bad_coeff by fastforce
qed

definition hwronskian :: "nat \<Rightarrow> (nat \<Rightarrow> rat poly) \<Rightarrow> rat poly"
  where "hwronskian k p \<equiv>
    det (mat k k (\<lambda>(i,j). hderiv i (p j)))"

lemma det_mat_expansion:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> 'a::comm_ring_1"
  shows "det (mat k k (\<lambda>(i,j). f i j)) =
    (\<Sum>q\<in>{q. q permutes {..<k}}. signof q * (\<Prod>i<k. f i (q i)))"
    (is "det ?A = _")
    using det_def'[of ?A k] by (simp add: permutes_bounded atLeast0LessThan)

lemma coeff_signof_mult:
  fixes F :: "rat poly"
  shows "Polynomial.coeff ((signof q) * F) n = (signof q::rat) * Polynomial.coeff F n"
  by (simp add: sign_def)

lemma wr_top_coeff:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes "\<forall>j<k. p j \<noteq> 0"
  shows "Polynomial.coeff (hwronskian k p)
    ((\<Sum>j<k. degree (p j)) - (\<Sum>i<k. i)) =
    (\<Prod>j<k. lead_coeff (p j)) * det (mat k k (\<lambda>(i,j). (of_nat (degree (p j) choose i)::rat)))"
  using assms
  by (simp add: hwronskian_def det_mat_expansion
    coeff_sum coeff_signof_mult wr_term
    sum_distrib_left algebra_simps)

lemma wr_distinct_degrees:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes pnz: "\<forall>j<k. p j \<noteq> 0"
    and inj: "inj_on (\<lambda>j. degree (p j)) {..<k}"
  shows "hwronskian k p \<noteq> 0"
proof -
  have c: "Polynomial.coeff (hwronskian k p)
      ((\<Sum>j<k. degree (p j)) - (\<Sum>i<k. i)) \<noteq> 0"
    using wr_top_coeff[OF pnz]  binomial_det_nonzero_transpose[OF inj] pnz by simp
  show ?thesis using c by (metis coeff_0)
qed

section \<open>Column elimination for independent families\<close>

lemma wr_addcol:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes a: "a<k" and b: "b<k" and ne: "a\<noteq>b"
  shows "hwronskian k
      (\<lambda>j. if j=b then p b + Polynomial.smult c (p a) else p j) =
    hwronskian k p"
proof -
  let ?A = "mat k k (\<lambda>(i,j). hderiv i (p j))"
  have eq: "mat k k
      (\<lambda>(i,j). hderiv i
        (if j=b then p b + Polynomial.smult c (p a) else p j)) =
    addcol [:c:] b a ?A"
    using a b by (intro eq_matI) (auto simp: mat_addcol_def)
  show ?thesis unfolding hwronskian_def eq
    by (rule det_addcol[OF a ne[symmetric]]) simp
qed

lemma poly_eliminate_degree:
  fixes P Q :: "rat poly"
  assumes P: "P \<noteq> 0" and deq: "degree P = degree Q"
  defines "c \<equiv> - lead_coeff Q / lead_coeff P"
  shows "Q + Polynomial.smult c P = 0 \<or>
    degree (Q + Polynomial.smult c P) < degree P"
proof -
  have lc: "lead_coeff P \<noteq> 0" using P by simp
  have bound: "degree (Q + Polynomial.smult c P) \<le> degree P"
    using deq by (simp add: degree_add_le)
  have top: "Polynomial.coeff (Q + Polynomial.smult c P) (degree P) = 0"
    using deq lc by (simp add: c_def field_simps)
  show ?thesis using eq_zero_or_degree_less[OF bound top] .
qed

definition poly_indep ::
  "nat \<Rightarrow> (nat \<Rightarrow> rat poly) \<Rightarrow> bool" where
  "poly_indep k p \<equiv>
    (\<forall>c. (\<Sum>j<k. Polynomial.smult (c j) (p j)) = 0 \<longrightarrow> (\<forall>j<k. c j = 0))"

lemma poly_indepD:
  assumes "poly_indep k p"
    and "(\<Sum>j<k. Polynomial.smult (c j) (p j)) = 0"
  shows "\<forall>j<k. c j = 0"
  using assms unfolding poly_indep_def by (metis (no_types))

lemma poly_indep_nonzero:
  assumes ind: "poly_indep k p" and j: "j<k"
  shows "p j \<noteq> 0"
proof
  assume z: "p j = 0"
  let ?c = "\<lambda>i. if i=j then (1::rat) else 0"
  have eq: "(\<Sum>i<k. Polynomial.smult (?c i) (p i)) =
    (\<Sum>i<k. if i=j then p j else 0)"
    by (rule sum.cong) auto
  have s: "(\<Sum>i<k. Polynomial.smult (?c i) (p i)) = 0"
    using z eq j by auto
  have "\<forall>i<k. ?c i = 0"
    by (rule poly_indepD[OF ind s])
  then show False using j by auto
qed

lemma poly_sum_addcol:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes b: "b<k"
  shows "(\<Sum>j<k. Polynomial.smult (c j)
      (if j=b then p b + Polynomial.smult t (p a) else p j)) =
    (\<Sum>j<k. Polynomial.smult (c j) (p j)) +
      Polynomial.smult (c b * t) (p a)"
  using b by (simp add: sum.remove[of "{..<k}" b]
    smult_add_right algebra_simps)

lemma poly_sum_addcoeff:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes a: "a<k"
  shows "(\<Sum>j<k. Polynomial.smult
      (if j=a then c a + c b*t else c j) (p j)) =
    (\<Sum>j<k. Polynomial.smult (c j) (p j)) +
      Polynomial.smult (c b*t) (p a)"
  using a by (simp add: sum.remove[of "{..<k}" a]
    smult_add_left algebra_simps)

lemma coeff_update_zero:
  fixes c :: "nat \<Rightarrow> rat"
  assumes dz: "\<forall>j<k. (if j=a then c a + c b*t else c j) = 0"
    and a: "a<k" and b: "b<k" and ne: "a\<noteq>b"
  shows "\<forall>j<k. c j = 0"
using assms by (metis add_cancel_right_left mult_eq_0_iff)

lemma poly_indep_addcol:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes ind: "poly_indep k p"
    and a: "a<k" and b: "b<k" and ne: "a\<noteq>b"
  shows "poly_indep k
    (\<lambda>j. if j=b then p b + Polynomial.smult t (p a) else p j)"
  unfolding poly_indep_def
proof (intro allI impI)
  fix c j
  assume z: "(\<Sum>i<k. Polynomial.smult (c i) (if i=b then p b + Polynomial.smult t (p a) else p i)) = 0"
    and j: "j<k"
  let ?d = "\<lambda>i. if i=a then c a + c b*t else c i"
  have eq: "(\<Sum>i<k. Polynomial.smult (?d i) (p i)) =
    (\<Sum>i<k. Polynomial.smult (c i)
      (if i=b then p b + Polynomial.smult t (p a) else p i))"
    using poly_sum_addcol[OF b]
      poly_sum_addcoeff[OF a] by simp
  have sz: "(\<Sum>i<k. Polynomial.smult (?d i) (p i)) = 0"
    using eq z by simp
  have dz: "\<forall>i<k. ?d i = 0"
    by (rule poly_indepD[OF ind sz])
  have "\<forall>i<k. c i = 0"
    by (rule coeff_update_zero[OF dz a b ne])
  then show "c j = 0" using j by blast
qed

lemma degree_sum_update_strict:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes b: "b<k" and dec: "degree Q < degree (p b)"
  shows "(\<Sum>j<k. degree (if j=b then Q else p j)) < (\<Sum>j<k. degree (p j))"
  by (rule sum_strict_mono_ex1) (use b dec in auto)

lemma wr_independent:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes ind: "poly_indep k p"
  shows "hwronskian k p \<noteq> 0"
  using ind
proof (induction p rule: measure_induct_rule
    [of "\<lambda>p. \<Sum>j<k. degree (p j)"])
  case (less p)
  have pnz: "\<forall>j<k. p j \<noteq> 0"
    using less.prems by (metis poly_indep_nonzero)
  show ?case
  proof (cases "inj_on (\<lambda>j. degree (p j)) {..<k}")
    case True
    then show ?thesis
      by (rule wr_distinct_degrees[OF pnz])
  next
    case False
    obtain a b where a: "a<k" and b: "b<k" and ne: "a\<noteq>b"
      and deq: "degree (p a) = degree (p b)"
      using False by (auto simp: inj_on_def)
    let ?t = "- lead_coeff (p b) / lead_coeff (p a)"
    let ?Q = "p b + Polynomial.smult ?t (p a)"
    let ?q = "\<lambda>j. if j=b then ?Q else p j"
    have qi: "poly_indep k ?q"
      by (rule poly_indep_addcol[OF less.prems a b ne])
    have Qnz: "?Q \<noteq> 0"
      using poly_indep_nonzero[OF qi b] by simp
    have Qdec: "degree ?Q < degree (p b)"
      using poly_eliminate_degree deq pnz a Qnz deq by auto
    have sumdec: "(\<Sum>j<k. degree (?q j)) < (\<Sum>j<k. degree (p j))"
      by (rule degree_sum_update_strict)
        (use b Qdec in auto)
    then show ?thesis
      using a b less.IH ne qi wr_addcol by fastforce
  qed
qed

end
