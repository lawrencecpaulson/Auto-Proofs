theory Roth_Wronskian
  imports
    Jordan_Normal_Form.Determinant
    Univariate_Index
    Hasse_Support
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

section \<open>Univariate Hasse derivatives and Wronskians\<close>

lemma roth_mchoose_single [simp]:
  "roth_mchoose (Poly_Mapping.single v n) (Poly_Mapping.single v k) =
    (n choose k)"
  by (simp add: roth_mchoose_on_set[of "{v}"])

lemma roth_univariate_hasse_coeff:
  fixes p :: "rat poly"
  shows "MPoly_Type.coeff
      (roth_hasse (Poly_Mapping.single v k) (poly_to_mpoly v p))
      (Poly_Mapping.single v n) =
    Polynomial.coeff p (n + k) * of_nat ((n + k) choose k)"
  by (simp add: roth_hasse_coeff_exact
    Poly_Mapping.single_add[symmetric] coeff_poly_to_mpoly)

lemma roth_hasse_vars_subset:
  fixes P :: "rat mpoly"
  shows "vars (roth_hasse J P) \<subseteq> vars P"
  by (auto simp: vars_def in_keys_iff coeff_def[symmetric]
    roth_hasse_coeff_exact lookup_add)

lemma roth_univariate_hasse_one:
  fixes p :: "rat poly"
  shows "roth_hasse (Poly_Mapping.single v 1) (poly_to_mpoly v p) =
    poly_to_mpoly v (pderiv p)"
proof -
  have vl: "vars (roth_hasse (Poly_Mapping.single v 1)
      (poly_to_mpoly v p)) \<subseteq> {v}"
    using roth_hasse_vars_subset roth_vars_poly_to_mpoly by blast
  have peq: "mpoly_to_poly v
      (roth_hasse (Poly_Mapping.single v 1) (poly_to_mpoly v p)) =
    pderiv p"
    by (rule poly_eqI)
      (simp add: roth_univariate_hasse_coeff coeff_pderiv)
  show ?thesis using peq mpoly_to_poly_inverse[OF vl] by simp
qed

definition roth_hderiv :: "nat \<Rightarrow> rat poly \<Rightarrow> rat poly" where
  "roth_hderiv k p =
    mpoly_to_poly 0 (roth_hasse (Poly_Mapping.single 0 k)
      (poly_to_mpoly 0 p))"

lemma roth_hderiv_coeff [simp]:
  "Polynomial.coeff (roth_hderiv k p) n =
    Polynomial.coeff p (n + k) * of_nat ((n + k) choose k)"
  by (simp add: roth_hderiv_def roth_univariate_hasse_coeff)

lemma roth_hderiv_zero [simp]: "roth_hderiv 0 p = p"
  by (rule poly_eqI) simp

lemma roth_hderiv_one [simp]: "roth_hderiv 1 p = pderiv p"
  by (rule poly_eqI) (simp add: coeff_pderiv)

lemma roth_hderiv_add [simp]:
  "roth_hderiv k (p + q) = roth_hderiv k p + roth_hderiv k q"
  by (rule poly_eqI) (simp add: algebra_simps)

lemma roth_hderiv_smult [simp]:
  "roth_hderiv k (Polynomial.smult c p) =
    Polynomial.smult c (roth_hderiv k p)"
  by (rule poly_eqI) (simp add: coeff_smult)

lemma roth_hderiv_monom:
  "roth_hderiv k (monom c n) =
    (if k \<le> n then monom (c * of_nat (n choose k)) (n-k) else 0)"
  by (rule poly_eqI) (auto simp: coeff_monom)

lemma roth_hderiv_degree_le:
  "degree (roth_hderiv k p) \<le> degree p - k"
  by (rule degree_le) (auto simp: coeff_eq_0)

lemma roth_hderiv_gt_degree [simp]:
  assumes "degree p < k"
  shows "roth_hderiv k p = 0"
proof (rule poly_eqI)
  fix n
  show "Polynomial.coeff (roth_hderiv k p) n = Polynomial.coeff 0 n"
    using assms by (simp add: coeff_eq_0)
qed

lemma roth_hderiv_degree:
  assumes p: "p \<noteq> 0" and k: "k \<le> degree p"
  shows "degree (roth_hderiv k p) = degree p - k"
proof (rule antisym)
  show "degree (roth_hderiv k p) \<le> degree p - k"
    by (rule roth_hderiv_degree_le)
  have nz: "Polynomial.coeff (roth_hderiv k p) (degree p - k) \<noteq> 0"
    using p k by simp
  then show "degree p - k \<le> degree (roth_hderiv k p)"
    by (rule le_degree)
qed

lemma roth_hderiv_nonzero:
  assumes p: "p \<noteq> 0" and i: "i \<le> degree p"
  shows "roth_hderiv i p \<noteq> 0"
proof -
  have c: "Polynomial.coeff (roth_hderiv i p) (degree p - i) \<noteq> 0"
    using p i by simp
  show ?thesis using c by (metis coeff_0)
qed

lemma roth_hderiv_lead_coeff:
  assumes p: "p \<noteq> 0" and k: "k \<le> degree p"
  shows "lead_coeff (roth_hderiv k p) =
    lead_coeff p * of_nat (degree p choose k)"
  using p k by (simp add: roth_hderiv_degree)

lemma roth_coeff_prod_top:
  fixes f :: "'i \<Rightarrow> rat poly"
  assumes nz: "\<forall>i\<in>S. f i \<noteq> 0"
  shows "Polynomial.coeff (\<Prod>i\<in>S. f i)
    (\<Sum>i\<in>S. degree (f i)) =
    (\<Prod>i\<in>S. lead_coeff (f i))"
proof -
  have deg: "degree (\<Prod>i\<in>S. f i) =
    (\<Sum>i\<in>S. degree (f i))"
    using nz by (simp add: degree_prod_sum_eq)
  show ?thesis unfolding deg[symmetric] by (rule lead_coeff_prod)
qed

lemma roth_permutes_sum:
  assumes q: "q permutes {..<k}"
  shows "(\<Sum>i<k. f (q i)::'a::comm_monoid_add) = (\<Sum>i<k. f i)"
proof -
  have inj: "inj_on q {..<k}"
    using q permutes_inj by (blast intro: inj_on_subset)
  have img: "q ` {..<k} = {..<k}"
    using permutes_image[OF q] .
  show ?thesis using sum.reindex[OF inj, of f] img
    by (simp add: o_def)
qed

lemma roth_permutes_prod:
  assumes q: "q permutes {..<k}"
  shows "(\<Prod>i<k. f (q i)::rat) = (\<Prod>i<k. f i)"
proof -
  have inj: "inj_on q {..<k}"
    using q permutes_inj by (blast intro: inj_on_subset)
  have img: "q ` {..<k} = {..<k}"
    using permutes_image[OF q] .
  show ?thesis using prod.reindex[OF inj, of f] img
    by (simp add: o_def)
qed

lemma roth_permutes_bounded:
  assumes q: "q permutes {..<k}" and i: "i<k"
  shows "q i < k"
  using permutes_image[OF q] i by blast

lemma roth_permutes_degree_diff:
  assumes q: "q permutes {..<k}"
    and good: "\<forall>i<k. i \<le> degree (p (q i))"
  shows "(\<Sum>i<k. degree (p (q i)) - i) =
    (\<Sum>i<k. degree (p i)) - (\<Sum>i<k. i)"
proof -
  have "(\<Sum>i<k. degree (p (q i)) - i) =
    (\<Sum>i<k. degree (p (q i))) - (\<Sum>i<k. i)"
    by (rule sum_subtractf_nat) (use good in auto)
  also have "\<dots> = (\<Sum>i<k. degree (p i)) - (\<Sum>i<k. i)"
    using roth_permutes_sum[OF q, of "\<lambda>j. degree (p j)"] by simp
  finally show ?thesis .
qed

lemma roth_wr_factors_nz:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes q: "q permutes {..<k}"
    and pnz: "\<forall>j<k. p j \<noteq> 0"
    and good: "\<forall>i<k. i \<le> degree (p (q i))"
  shows "\<forall>i<k. roth_hderiv i (p (q i)) \<noteq> 0"
proof (intro allI impI)
  fix i
  assume i: "i<k"
  have pq: "p (q i) \<noteq> 0"
    using pnz roth_permutes_bounded[OF q i] by auto
  show "roth_hderiv i (p (q i)) \<noteq> 0"
    by (rule roth_hderiv_nonzero[OF pq]) (use good i in auto)
qed

lemma roth_wr_lead_good:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes q: "q permutes {..<k}"
    and pnz: "\<forall>j<k. p j \<noteq> 0"
    and good: "\<forall>i<k. i \<le> degree (p (q i))"
  shows "(\<Prod>i<k. lead_coeff (roth_hderiv i (p (q i)))) =
    (\<Prod>i<k. lead_coeff (p (q i)) *
      of_nat (degree (p (q i)) choose i))"
proof (rule prod.cong)
  fix i
  assume i: "i\<in>{..<k}"
  have pq: "p (q i) \<noteq> 0"
    using pnz roth_permutes_bounded[OF q] i by auto
  show "lead_coeff (roth_hderiv i (p (q i))) =
    lead_coeff (p (q i)) * of_nat (degree (p (q i)) choose i)"
    by (rule roth_hderiv_lead_coeff[OF pq]) (use good i in auto)
qed simp

lemma roth_wr_term_good:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes q: "q permutes {..<k}"
    and pnz: "\<forall>j<k. p j \<noteq> 0"
    and good: "\<forall>i<k. i \<le> degree (p (q i))"
  shows "Polynomial.coeff
    (\<Prod>i<k. roth_hderiv i (p (q i)))
    ((\<Sum>j<k. degree (p j)) - (\<Sum>i<k. i)) =
    (\<Prod>i<k. lead_coeff (p (q i)) *
      of_nat (degree (p (q i)) choose i))"
proof -
  have nz: "\<forall>i<k. roth_hderiv i (p (q i)) \<noteq> 0"
    by (rule roth_wr_factors_nz[OF q pnz good])
  have deg: "(\<Sum>i<k. degree (roth_hderiv i (p (q i)))) =
    (\<Sum>j<k. degree (p j)) - (\<Sum>i<k. i)"
    using nz good pnz q
    by (simp add: roth_hderiv_degree roth_permutes_degree_diff
      roth_permutes_bounded)
  have top: "Polynomial.coeff
    (\<Prod>i<k. roth_hderiv i (p (q i)))
    ((\<Sum>j<k. degree (p j)) - (\<Sum>i<k. i)) =
    (\<Prod>i<k. lead_coeff (roth_hderiv i (p (q i))))"
    unfolding deg[symmetric]
    by (rule roth_coeff_prod_top) (use nz in auto)
  show ?thesis using top roth_wr_lead_good[OF q pnz good] by simp
qed

lemma roth_wr_term_bad:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes bad: "\<exists>i<k. degree (p (q i)) < i"
  shows "(\<Prod>i<k. roth_hderiv i (p (q i))) = 0 \<and>
    (\<Prod>i<k. of_nat (degree (p (q i)) choose i)::rat) = 0"
proof -
  obtain i where i: "i<k" "degree (p (q i)) < i"
    using bad by blast
  have h: "roth_hderiv i (p (q i)) = 0"
    by (rule roth_hderiv_gt_degree[OF i(2)])
  have b: "(of_nat (degree (p (q i)) choose i)::rat) = 0"
    using i by simp
  have hp: "(\<Prod>i<k. roth_hderiv i (p (q i))) = 0"
    by (rule prod_zero) (use i h in blast)+
  have bp: "(\<Prod>i<k. of_nat (degree (p (q i)) choose i)::rat) = 0"
    by (rule prod_zero) (use i b in blast)+
  show ?thesis using hp bp by simp
qed

lemma roth_wr_term_bad_coeff:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes bad: "\<exists>i<k. degree (p (q i)) < i"
  shows "Polynomial.coeff
    (\<Prod>i<k. roth_hderiv i (p (q i))) M =
    (\<Prod>j<k. lead_coeff (p j)) *
    (\<Prod>i<k. of_nat (degree (p (q i)) choose i)::rat)"
proof -
  have hp: "(\<Prod>i<k. roth_hderiv i (p (q i))) = 0"
    and bp: "(\<Prod>i<k. of_nat (degree (p (q i)) choose i)::rat) = 0"
    using roth_wr_term_bad[where p=p and q=q and k=k, OF bad] by auto
  show ?thesis unfolding hp bp by simp
qed

lemma roth_wr_term:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes q: "q permutes {..<k}" and pnz: "\<forall>j<k. p j \<noteq> 0"
  shows "Polynomial.coeff
    (\<Prod>i<k. roth_hderiv i (p (q i)))
    ((\<Sum>j<k. degree (p j)) - (\<Sum>i<k. i)) =
    (\<Prod>j<k. lead_coeff (p j)) *
    (\<Prod>i<k. of_nat (degree (p (q i)) choose i)::rat)"
proof (cases "\<forall>i<k. i \<le> degree (p (q i))")
  case True
  note t = roth_wr_term_good[OF q pnz True]
  have r: "(\<Prod>i<k. lead_coeff (p (q i)) *
      of_nat (degree (p (q i)) choose i)) =
    (\<Prod>j<k. lead_coeff (p j)) *
    (\<Prod>i<k. of_nat (degree (p (q i)) choose i)::rat)"
    using roth_permutes_prod[OF q, of "\<lambda>j. lead_coeff (p j)"]
    by (simp add: prod.distrib)
  show ?thesis using t r by simp
next
  case False
  have bad: "\<exists>i<k. degree (p (q i)) < i"
    using False by auto
  show ?thesis by (rule roth_wr_term_bad_coeff) (rule bad)
qed

definition roth_hwronskian :: "nat \<Rightarrow> (nat \<Rightarrow> rat poly) \<Rightarrow> rat poly"
  where "roth_hwronskian k p =
    det (mat k k (\<lambda>(i,j). roth_hderiv i (p j)))"

lemma roth_det_mat_expansion:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> 'a::comm_ring_1"
  shows "det (mat k k (\<lambda>(i,j). f i j)) =
    (\<Sum>q\<in>{q. q permutes {..<k}}.
      signof q * (\<Prod>i<k. f i (q i)))"
proof -
  let ?A = "mat k k (\<lambda>(i,j). f i j)"
  have d: "det ?A =
    (\<Sum>q\<in>{q. q permutes {..<k}}.
      signof q * (\<Prod>i<k. ?A $$ (i,q i)))"
    using det_def'[of ?A k] by (simp add: atLeast0LessThan)
  show ?thesis unfolding d
    by (rule sum.cong)
      (auto intro!: prod.cong simp: roth_permutes_bounded)
qed

lemma roth_coeff_signof_mult:
  fixes F :: "rat poly"
  shows "Polynomial.coeff ((signof q) * F) n =
    (signof q::rat) * Polynomial.coeff F n"
  by (simp add: sign_def)

lemma roth_wr_top_coeff:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes pnz: "\<forall>j<k. p j \<noteq> 0"
  shows "Polynomial.coeff (roth_hwronskian k p)
    ((\<Sum>j<k. degree (p j)) - (\<Sum>i<k. i)) =
    (\<Prod>j<k. lead_coeff (p j)) *
      det (mat k k
        (\<lambda>(i,j). (of_nat (degree (p j) choose i)::rat)))"
  using pnz
  by (simp add: roth_hwronskian_def roth_det_mat_expansion
    coeff_sum roth_coeff_signof_mult roth_wr_term
    sum_distrib_left algebra_simps)

lemma roth_wr_distinct_degrees:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes pnz: "\<forall>j<k. p j \<noteq> 0"
    and inj: "inj_on (\<lambda>j. degree (p j)) {..<k}"
  shows "roth_hwronskian k p \<noteq> 0"
proof -
  have dnz: "det (mat k k
      (\<lambda>(i,j). (of_nat (degree (p j) choose i)::rat))) \<noteq> 0"
    by (rule roth_binomial_det_nonzero_transpose[OF inj])
  have lnz: "(\<Prod>j<k. lead_coeff (p j)) \<noteq> (0::rat)"
    using pnz by (simp add: prod_zero_iff)
  have c: "Polynomial.coeff (roth_hwronskian k p)
      ((\<Sum>j<k. degree (p j)) - (\<Sum>i<k. i)) \<noteq> 0"
    using roth_wr_top_coeff[OF pnz] dnz lnz by simp
  show ?thesis using c by (metis coeff_0)
qed

section \<open>Column elimination for independent families\<close>

lemma roth_wr_addcol:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes a: "a<k" and b: "b<k" and ne: "a\<noteq>b"
  shows "roth_hwronskian k
      (\<lambda>j. if j=b then p b + Polynomial.smult c (p a) else p j) =
    roth_hwronskian k p"
proof -
  let ?A = "mat k k (\<lambda>(i,j). roth_hderiv i (p j))"
  have eq: "mat k k
      (\<lambda>(i,j). roth_hderiv i
        (if j=b then p b + Polynomial.smult c (p a) else p j)) =
    addcol [:c:] b a ?A"
    using a b by (intro eq_matI) (auto simp: mat_addcol_def)
  show ?thesis unfolding roth_hwronskian_def eq
    by (rule det_addcol[OF a ne[symmetric]]) simp
qed

lemma roth_poly_eliminate_degree:
  fixes P Q :: "rat poly"
  assumes P: "P \<noteq> 0" and deq: "degree P = degree Q"
  defines "c \<equiv> - lead_coeff Q / lead_coeff P"
  shows "Q + Polynomial.smult c P = 0 \<or>
    degree (Q + Polynomial.smult c P) < degree P"
proof -
  have lc: "lead_coeff P \<noteq> 0" using P by simp
  have bound: "degree (Q + Polynomial.smult c P) \<le> degree P"
    using deq by (simp add: degree_add_le)
  have top: "Polynomial.coeff (Q + Polynomial.smult c P)
      (degree P) = 0"
    using deq lc by (simp add: c_def field_simps)
  show ?thesis using eq_zero_or_degree_less[OF bound top] .
qed

definition roth_poly_indep ::
  "nat \<Rightarrow> (nat \<Rightarrow> rat poly) \<Rightarrow> bool" where
  "roth_poly_indep k p \<longleftrightarrow>
    (\<forall>c. (\<Sum>j<k. Polynomial.smult (c j) (p j)) = 0 \<longrightarrow>
      (\<forall>j<k. c j = 0))"

lemma roth_poly_indepD:
  assumes "roth_poly_indep k p"
    and "(\<Sum>j<k. Polynomial.smult (c j) (p j)) = 0"
  shows "\<forall>j<k. c j = 0"
  using assms unfolding roth_poly_indep_def by (metis (no_types))

lemma roth_poly_indep_nonzero:
  assumes ind: "roth_poly_indep k p" and j: "j<k"
  shows "p j \<noteq> 0"
proof
  assume z: "p j = 0"
  let ?c = "\<lambda>i. if i=j then (1::rat) else 0"
  have eq: "(\<Sum>i<k. Polynomial.smult (?c i) (p i)) =
    (\<Sum>i<k. if i=j then p j else 0)"
    by (rule sum.cong) auto
  have s: "(\<Sum>i<k. Polynomial.smult (?c i) (p i)) = 0"
    using z eq j by (simp add: sum.delta)
  have h: "\<forall>i<k. ?c i = 0"
    by (rule roth_poly_indepD[OF ind s])
  show False using h j by auto
qed

lemma roth_poly_sum_addcol:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes b: "b<k"
  shows "(\<Sum>j<k. Polynomial.smult (c j)
      (if j=b then p b + Polynomial.smult t (p a) else p j)) =
    (\<Sum>j<k. Polynomial.smult (c j) (p j)) +
      Polynomial.smult (c b * t) (p a)"
  using b by (simp add: sum.remove[of "{..<k}" b]
    smult_add_right algebra_simps)

lemma roth_poly_sum_addcoeff:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes a: "a<k"
  shows "(\<Sum>j<k. Polynomial.smult
      (if j=a then c a + c b*t else c j) (p j)) =
    (\<Sum>j<k. Polynomial.smult (c j) (p j)) +
      Polynomial.smult (c b*t) (p a)"
  using a by (simp add: sum.remove[of "{..<k}" a]
    smult_add_left algebra_simps)

lemma roth_coeff_update_zero:
  fixes c :: "nat \<Rightarrow> rat"
  assumes dz: "\<forall>j<k. (if j=a then c a + c b*t else c j) = 0"
    and a: "a<k" and b: "b<k" and ne: "a\<noteq>b"
  shows "\<forall>j<k. c j = 0"
proof -
  have cb: "c b = 0" using dz b ne by auto
  have ca: "c a = 0" using dz a cb by auto
  show ?thesis using dz ca by (metis (mono_tags, lifting))
qed

lemma roth_poly_indep_addcol:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes ind: "roth_poly_indep k p"
    and a: "a<k" and b: "b<k" and ne: "a\<noteq>b"
  shows "roth_poly_indep k
    (\<lambda>j. if j=b then p b + Polynomial.smult t (p a) else p j)"
  unfolding roth_poly_indep_def
proof (intro allI impI)
  fix c j
  assume z: "(\<Sum>i<k. Polynomial.smult (c i)
      (if i=b then p b + Polynomial.smult t (p a) else p i)) = 0"
    and j: "j<k"
  let ?d = "\<lambda>i. if i=a then c a + c b*t else c i"
  have eq: "(\<Sum>i<k. Polynomial.smult (?d i) (p i)) =
    (\<Sum>i<k. Polynomial.smult (c i)
      (if i=b then p b + Polynomial.smult t (p a) else p i))"
    using roth_poly_sum_addcol[OF b]
      roth_poly_sum_addcoeff[OF a] by simp
  have sz: "(\<Sum>i<k. Polynomial.smult (?d i) (p i)) = 0"
    using eq z by simp
  have dz: "\<forall>i<k. ?d i = 0"
    by (rule roth_poly_indepD[OF ind sz])
  have cz: "\<forall>i<k. c i = 0"
    by (rule roth_coeff_update_zero[OF dz a b ne])
  show "c j = 0" using cz j by blast
qed

lemma roth_degree_sum_update_strict:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes b: "b<k" and dec: "degree Q < degree (p b)"
  shows "(\<Sum>j<k. degree (if j=b then Q else p j)) <
    (\<Sum>j<k. degree (p j))"
  by (rule sum_strict_mono_ex1) (use b dec in auto)

lemma roth_wr_independent:
  fixes p :: "nat \<Rightarrow> rat poly"
  assumes ind: "roth_poly_indep k p"
  shows "roth_hwronskian k p \<noteq> 0"
  using ind
proof (induction p rule: measure_induct_rule
    [of "\<lambda>p. \<Sum>j<k. degree (p j)"])
  case (less p)
  have pnz: "\<forall>j<k. p j \<noteq> 0"
    using less.prems by (metis roth_poly_indep_nonzero)
  show ?case
  proof (cases "inj_on (\<lambda>j. degree (p j)) {..<k}")
    case True
    then show ?thesis
      by (rule roth_wr_distinct_degrees[OF pnz])
  next
    case False
    obtain a b where a: "a<k" and b: "b<k" and ne: "a\<noteq>b"
      and deq: "degree (p a) = degree (p b)"
      using False by (auto simp: inj_on_def)
    let ?t = "- lead_coeff (p b) / lead_coeff (p a)"
    let ?Q = "p b + Polynomial.smult ?t (p a)"
    let ?q = "\<lambda>j. if j=b then ?Q else p j"
    have pa: "p a \<noteq> 0" using pnz a by auto
    have qi: "roth_poly_indep k ?q"
      by (rule roth_poly_indep_addcol[OF less.prems a b ne])
    have Qnz: "?Q \<noteq> 0"
      using roth_poly_indep_nonzero[OF qi b] by simp
    have Qdec: "degree ?Q < degree (p b)"
      using roth_poly_eliminate_degree[OF pa deq] Qnz deq by auto
    have sumdec: "(\<Sum>j<k. degree (?q j)) <
      (\<Sum>j<k. degree (p j))"
      by (rule roth_degree_sum_update_strict)
        (use b Qdec in auto)
    have qnz: "roth_hwronskian k ?q \<noteq> 0"
      by (rule less.IH[OF sumdec qi])
    have wr: "roth_hwronskian k ?q = roth_hwronskian k p"
      by (rule roth_wr_addcol[OF a b ne])
    show ?thesis using qnz wr by simp
  qed
qed

end
