theory Roth_Kronecker_Wronskian
  imports Roth_Kronecker_Det
begin

section \<open>Ordinary and Hasse Wronskians\<close>

lemma roth_binomial_step_nat:
  "Suc n * (Suc (n+i) choose i) =
    Suc i * (Suc (n+i) choose Suc i)"
proof -
  have a: "Suc n * (Suc (n+i) choose i) =
      Suc (n+i) * (n+i choose i)"
    using binomial_absorb_comp[of "Suc (n+i)" i] by simp
  have b: "Suc i * (Suc (n+i) choose Suc i) =
      Suc (n+i) * (n+i choose i)"
    using binomial_absorption[of i "Suc (n+i)"] by simp
  show ?thesis using a b by simp
qed

lemma roth_binomial_step_rat:
  "(of_nat (Suc n)::rat) * of_nat (Suc (n+i) choose i) =
    of_nat (Suc i) * of_nat (Suc (n+i) choose Suc i)"
  using roth_binomial_step_nat[of n i] by (metis of_nat_mult)

lemma roth_mult_exchange:
  fixes a b c d e :: rat
  assumes "a*b = c*d"
  shows "a*(e*b)=c*(e*d)"
  using assms by (simp add: mult.left_commute)

lemma roth_hderiv_pderiv:
  "pderiv (roth_hderiv i p) =
    Polynomial.smult (of_nat (Suc i)) (roth_hderiv (Suc i) p)"
  by (rule poly_eqI)
    (simp only: coeff_pderiv roth_hderiv_coeff coeff_smult
      add_Suc_shift add_Suc_right;
      rule roth_mult_exchange; rule roth_binomial_step_rat)

lemma roth_pderiv_iter_hderiv:
  "(pderiv ^^ i) p =
    Polynomial.smult (of_nat (fact i)) (roth_hderiv i p)"
  by (induction i)
    (simp_all add: funpow_Suc_right roth_hderiv_pderiv
      pderiv_smult fact_Suc smult_smult algebra_simps)

lemma roth_sum_smult:
  fixes f :: "'a \<Rightarrow> rat poly"
  shows "Polynomial.smult c (\<Sum>x\<in>S. f x) =
    (\<Sum>x\<in>S. Polynomial.smult c (f x))"
proof -
  have cv: "Polynomial.smult c P = [:c:] * P"
    for c :: rat and P :: "rat poly" by simp
  show ?thesis by (simp only: cv sum_distrib_left)
qed

lemma roth_det_row_smult:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat poly"
    and c :: "nat \<Rightarrow> rat"
  shows "det (mat k k
      (\<lambda>(i,j). Polynomial.smult (c i) (A i j))) =
    Polynomial.smult (\<Prod>i<k. c i)
      (det (mat k k (\<lambda>(i,j). A i j)))"
  by (simp add: roth_det_mat_expansion prod_smult
    roth_sum_smult[symmetric] algebra_simps)

definition roth_pwronskian ::
  "nat \<Rightarrow> (nat \<Rightarrow> rat poly) \<Rightarrow> rat poly"
  where "roth_pwronskian k p =
    det (mat k k (\<lambda>(i,j). (pderiv ^^ i) (p j)))"

lemma roth_pwronskian_eq:
  "roth_pwronskian k p =
    Polynomial.smult (\<Prod>i<k. of_nat (fact i))
      (roth_hwronskian k p)"
  by (simp add: roth_pwronskian_def roth_pderiv_iter_hderiv
    roth_det_row_smult roth_hwronskian_def)

lemma roth_pwronskian_nonzero:
  assumes "roth_poly_indep k p"
  shows "roth_pwronskian k p \<noteq> 0"
  using roth_wr_independent[OF assms]
  by (simp add: roth_pwronskian_eq)

section \<open>Expansion of determinant rows\<close>

lemma roth_sum_swap_scale:
  fixes c :: "'a \<Rightarrow> rat poly"
    and F :: "'a \<Rightarrow> 'b \<Rightarrow> rat poly"
  shows "(\<Sum>q\<in>Q. c q * (\<Sum>g\<in>G. F q g)) =
    (\<Sum>g\<in>G. \<Sum>q\<in>Q. c q * F q g)"
  by (simp only: sum_distrib_left) (rule sum.swap)

lemma roth_det_sum_rows_first:
  fixes B :: "nat \<Rightarrow> 'a set"
    and F :: "nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> rat poly"
  assumes fin: "\<And>i. i<k \<Longrightarrow> finite (B i)"
  shows "det (mat k k
      (\<lambda>(i,j). \<Sum>x\<in>B i. F i x j)) =
    (\<Sum>q\<in>{q. q permutes {..<k}}.
      signof q *
        (\<Sum>g\<in>PiE {..<k} B.
          \<Prod>i<k. F i (g i) (q i)))"
proof -
  have prod: "(\<Prod>i<k. \<Sum>x\<in>B i. F i x (q i)) =
      (\<Sum>g\<in>PiE {..<k} B.
        \<Prod>i<k. F i (g i) (q i))" for q
    by (rule prod_sum_PiE) (use fin in auto)
  show ?thesis by (simp add: roth_det_mat_expansion prod)
qed

lemma roth_det_sum_rows:
  fixes B :: "nat \<Rightarrow> 'a set"
    and F :: "nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> rat poly"
  assumes fin: "\<And>i. i<k \<Longrightarrow> finite (B i)"
  shows "det (mat k k
      (\<lambda>(i,j). \<Sum>x\<in>B i. F i x j)) =
    (\<Sum>g\<in>PiE {..<k} B.
      det (mat k k (\<lambda>(i,j). F i (g i) j)))"
proof -
  have "det (mat k k
      (\<lambda>(i,j). \<Sum>x\<in>B i. F i x j)) =
    (\<Sum>q\<in>{q. q permutes {..<k}}.
      signof q *
        (\<Sum>g\<in>PiE {..<k} B.
          \<Prod>i<k. F i (g i) (q i)))"
    by (rule roth_det_sum_rows_first[OF fin])
  also have "\<dots> =
    (\<Sum>g\<in>PiE {..<k} B.
      \<Sum>q\<in>{q. q permutes {..<k}}.
        signof q * (\<Prod>i<k. F i (g i) (q i)))"
    by (rule roth_sum_swap_scale)
  also have "\<dots> =
    (\<Sum>g\<in>PiE {..<k} B.
      det (mat k k (\<lambda>(i,j). F i (g i) j)))"
    by (simp add: roth_det_mat_expansion)
  finally show ?thesis .
qed

lemma roth_hasse_box_monotone:
  fixes P :: "rat mpoly"
  assumes "roth_poly_in_box m r P"
  shows "roth_poly_in_box m r (roth_hasse J P)"
proof -
  have h: "roth_poly_in_box m
      (\<lambda>v. r v - Poly_Mapping.lookup J v)
      (roth_hasse J P)"
    by (rule roth_hasse_in_box[OF assms])
  have mono: "roth_exponent_box m
      (\<lambda>v. r v - Poly_Mapping.lookup J v)
      \<subseteq> roth_exponent_box m r"
    by (auto simp: roth_exponent_box_iff)
      (meson le_trans diff_le_self)
  show ?thesis using h mono
    by (auto simp: roth_poly_in_box_def)
qed

lemma roth_det_row_mult:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat poly"
    and c :: "nat \<Rightarrow> rat poly"
  shows "det (mat k k (\<lambda>(i,j). c i * A i j)) =
    (\<Prod>i<k. c i) *
      det (mat k k (\<lambda>(i,j). A i j))"
  by (simp add: roth_det_mat_expansion prod.distrib
    sum_distrib_left algebra_simps)

lemma roth_kronecker_pwronskian_expansion:
  fixes p :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>j<k. roth_poly_in_box m r (p j)"
    and pos: "0<B"
  shows "roth_pwronskian k
      (\<lambda>j. roth_ksubst m B (p j)) =
    (\<Sum>g\<in>PiE {..<k} (roth_jet_words m).
      det (mat k k
        (\<lambda>(i,j). roth_jet_coeff B i (g i) *
          roth_ksubst m B
            (roth_hasse (roth_jet_index (g i)) (p j)))))"
proof -
  have row: "mat k k
      (\<lambda>(i,j). (pderiv ^^ i) (roth_ksubst m B (p j))) =
    mat k k
      (\<lambda>(i,j). \<Sum>xs\<in>roth_jet_words m i.
        roth_jet_coeff B i xs *
          roth_ksubst m B
            (roth_hasse (roth_jet_index xs) (p j)))"
    using box pos
    by (auto simp: mat_eq_iff roth_jet_expansion)
  show ?thesis unfolding roth_pwronskian_def row
    by (rule roth_det_sum_rows) simp
qed

end
