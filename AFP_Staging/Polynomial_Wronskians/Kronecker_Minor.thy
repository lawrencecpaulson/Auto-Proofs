theory Kronecker_Minor
  imports
    Kronecker_Evaluation
begin

section \<open>Reflection of nonzero determinants\<close>

lemma mwr_poly_det:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat poly"
  shows "poly (det (mat k k (\<lambda>(i,j). A i j))) t =
    det (mat k k (\<lambda>(i,j). poly (A i j) t))"
  by (simp add: det_mat_expansion poly_sum poly_prod sign_def)

lemma mwr_poly_nonzero_eval:
  fixes Q :: "rat poly"
  assumes "Q\<noteq>0"
  shows "\<exists>t::rat. poly Q t \<noteq> 0"
  using assms poly_all_0_iff_0[of Q] by blast

lemma mwr_ksubst_eval_mat:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat mpoly"
  assumes "\<forall>i<k. \<forall>j<k. pjet_poly_in_box m r (A i j)"
  shows "mat k k (\<lambda>(i,j). poly (mwr_ksubst m B (A i j)) t) =
    mat k k (\<lambda>(i,j). insertion (\<lambda>v. t^(B^v)) (A i j))"
  using assms
  by (auto simp: mat_eq_iff dest: mwr_ksubst_eval_insertion)

lemma mwr_det_ksubst_reflect_nonzero:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>i<k. \<forall>j<k.
    pjet_poly_in_box m r (A i j)"
    and nz: "det (mat k k (\<lambda>(i,j).
      mwr_ksubst m B (A i j))) \<noteq> 0"
  shows "det (mat k k (\<lambda>(i,j). A i j)) \<noteq> 0"
proof -
  obtain t :: rat where h:
    "poly (det (mat k k (\<lambda>(i,j).
      mwr_ksubst m B (A i j)))) t \<noteq> 0"
    using mwr_poly_nonzero_eval[OF nz] by blast
  have d: "poly (det (mat k k (\<lambda>(i,j). mwr_ksubst m B (A i j)))) t =
    insertion (\<lambda>v. t^(B^v)) (det (mat k k (\<lambda>(i,j). A i j)))"
    by (simp add: mwr_poly_det mwr_ksubst_eval_mat[OF box] mwr_insertion_det)
  show ?thesis using h d by auto
qed

section \<open>Ordinary and Hasse Wronskians\<close>

lemma mwr_binomial_step_nat:
  "Suc n * (Suc (n+i) choose i) = Suc i * (Suc (n+i) choose Suc i)"
  by (metis Suc_times_binomial_add add.commute)

lemma mwr_binomial_step_rat:
  "(of_nat (Suc n)::rat) * of_nat (Suc (n+i) choose i) =
    of_nat (Suc i) * of_nat (Suc (n+i) choose Suc i)"
  using mwr_binomial_step_nat[of n i] by (metis of_nat_mult)

lemma mwr_mult_exchange:
  fixes a b c d e :: rat
  assumes "a*b = c*d"
  shows "a*(e*b)=c*(e*d)"
  using assms by (simp add: mult.left_commute)

lemma mwr_hderiv_pderiv:
  "pderiv (hderiv i p) =
    Polynomial.smult (of_nat (Suc i)) (hderiv (Suc i) p)"
  by (rule poly_eqI)
    (simp only: coeff_pderiv hderiv_coeff coeff_smult
      add_Suc_shift add_Suc_right;
      rule mwr_mult_exchange; rule mwr_binomial_step_rat)

lemma mwr_pderiv_iter_hderiv:
  "(pderiv ^^ i) p =
    Polynomial.smult (of_nat (fact i)) (hderiv i p)"
  by (induction i)
    (simp_all add: funpow_Suc_right mwr_hderiv_pderiv
      pderiv_smult algebra_simps)

lemma mwr_det_row_smult:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat poly"
    and c :: "nat \<Rightarrow> rat"
  shows "det (mat k k
      (\<lambda>(i,j). Polynomial.smult (c i) (A i j))) =
    Polynomial.smult (\<Prod>i<k. c i)
      (det (mat k k (\<lambda>(i,j). A i j)))"
  by (simp add: det_mat_expansion prod_smult
    mwr_sum_smult[symmetric] algebra_simps)

definition mwr_pwronskian ::
  "nat \<Rightarrow> (nat \<Rightarrow> rat poly) \<Rightarrow> rat poly"
  where "mwr_pwronskian k p =
    det (mat k k (\<lambda>(i,j). (pderiv ^^ i) (p j)))"

lemma mwr_pwronskian_eq:
  "mwr_pwronskian k p =
    Polynomial.smult (\<Prod>i<k. of_nat (fact i))
      (hwronskian k p)"
  by (simp add: mwr_pwronskian_def mwr_pderiv_iter_hderiv
    mwr_det_row_smult hwronskian_def)

lemma mwr_pwronskian_nonzero:
  assumes "poly_indep k p"
  shows "mwr_pwronskian k p \<noteq> 0"
  using wr_independent[OF assms]
  by (simp add: mwr_pwronskian_eq)

section \<open>Expansion of determinant rows\<close>

lemma mwr_det_sum_rows_first:
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
  show ?thesis by (simp add: det_mat_expansion prod)
qed

lemma mwr_det_sum_rows:
  fixes B :: "nat \<Rightarrow> 'a set"
    and F :: "nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> rat poly"
  assumes fin: "\<And>i. i<k \<Longrightarrow> finite (B i)"
  shows "det (mat k k (\<lambda>(i,j). \<Sum>x\<in>B i. F i x j)) =
    (\<Sum>g\<in>PiE {..<k} B.
      det (mat k k (\<lambda>(i,j). F i (g i) j)))"
proof -
  have "det (mat k k (\<lambda>(i,j). \<Sum>x\<in>B i. F i x j)) =
    (\<Sum>g\<in>PiE {..<k} B. \<Sum>q\<in>{q. q permutes {..<k}}.
        signof q * (\<Prod>i<k. F i (g i) (q i)))"
    by (simp add: mwr_det_sum_rows_first[OF fin] sum_distrib_left) (rule sum.swap)
  also have "\<dots> =
    (\<Sum>g\<in>PiE {..<k} B.
      det (mat k k (\<lambda>(i,j). F i (g i) j)))"
    by (simp add: det_mat_expansion)
  finally show ?thesis .
qed

lemma mwr_det_row_mult:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat poly"
    and c :: "nat \<Rightarrow> rat poly"
  shows "det (mat k k (\<lambda>(i,j). c i * A i j)) =
    (\<Prod>i<k. c i) * det (mat k k (\<lambda>(i,j). A i j))"
  by (simp add: det_mat_expansion prod.distrib
    sum_distrib_left algebra_simps)

lemma mwr_kronecker_pwronskian_expansion:
  fixes p :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>j<k. pjet_poly_in_box m r (p j)"
    and pos: "0<B"
  shows "mwr_pwronskian k
      (\<lambda>j. mwr_ksubst m B (p j)) =
    (\<Sum>g\<in>PiE {..<k} (mwr_jet_words m).
      det (mat k k
        (\<lambda>(i,j). mwr_jet_coeff B i (g i) *
          mwr_ksubst m B
            (pjet_hasse (mwr_jet_index (g i)) (p j)))))"
proof -
  have row: "mat k k
      (\<lambda>(i,j). (pderiv ^^ i) (mwr_ksubst m B (p j))) =
    mat k k
      (\<lambda>(i,j). \<Sum>xs\<in>mwr_jet_words m i.
        mwr_jet_coeff B i xs *
          mwr_ksubst m B
            (pjet_hasse (mwr_jet_index xs) (p j)))"
    using box pos
    by (auto simp: mat_eq_iff mwr_jet_expansion)
  show ?thesis unfolding mwr_pwronskian_def row
    by (rule mwr_det_sum_rows) simp
qed

section \<open>A nonzero multivariate Hasse minor\<close>

lemma mwr_weighted_minor_nonzero:
  fixes p :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>j<k. pjet_poly_in_box m r (p j)"
    and pos: "0<B"
    and B: "\<forall>v<m. r v<B"
    and ind: "mwr_mpoly_indep k p"
  shows "\<exists>g\<in>PiE {..<k} (mwr_jet_words m).
    det (mat k k
      (\<lambda>(i,j). mwr_jet_coeff B i (g i) *
        mwr_ksubst m B
          (pjet_hasse (mwr_jet_index (g i)) (p j)))) \<noteq> 0"
proof -
  have u: "poly_indep k (\<lambda>j. mwr_ksubst m B (p j))"
    by (rule mwr_ksubst_indep[OF box pos B ind])
  have h: "(\<Sum>g\<in>PiE {..<k} (mwr_jet_words m).
      det (mat k k
        (\<lambda>(i,j). mwr_jet_coeff B i (g i) *
          mwr_ksubst m B
            (pjet_hasse (mwr_jet_index (g i)) (p j))))) \<noteq> 0"
    using mwr_pwronskian_nonzero[OF u] mwr_kronecker_pwronskian_expansion[OF box pos]
    by simp
  show ?thesis
    by (rule sum.not_neutral_contains_not_neutral[OF h])
      blast
qed

lemma mwr_kronecker_hasse_minor:
  fixes p :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>j<k. pjet_poly_in_box m r (p j)"
    and pos: "0<B"
    and B: "\<forall>v<m. r v<B"
    and ind: "mwr_mpoly_indep k p"
  shows "\<exists>g\<in>PiE {..<k} (mwr_jet_words m).
    det (mat k k
      (\<lambda>(i,j). pjet_hasse
        (mwr_jet_index (g i)) (p j))) \<noteq> 0"
proof -
  obtain g where g: "g\<in>PiE {..<k} (mwr_jet_words m)"
    and gnz: "det (mat k k
      (\<lambda>(i,j). mwr_jet_coeff B i (g i) * mwr_ksubst m B (pjet_hasse (mwr_jet_index (g i)) (p j)))) \<noteq> 0"
    using mwr_weighted_minor_nonzero[OF box pos B ind]
    by blast
  have hnz: "det (mat k k
      (\<lambda>(i,j). mwr_ksubst m B
        (pjet_hasse (mwr_jet_index (g i)) (p j)))) \<noteq> 0"
    using gnz by (simp add: mwr_det_row_mult)
  have Abox: "\<forall>i<k. \<forall>j<k.
      pjet_poly_in_box m r
        (pjet_hasse (mwr_jet_index (g i)) (p j))"
    using box by (auto intro: pjet_hasse_preserves_box)
  show ?thesis using g mwr_det_ksubst_reflect_nonzero[OF Abox hnz] by blast
qed

theorem mwr_kronecker_hasse_minor_bounded:
  fixes p :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>j<k. pjet_poly_in_box m r (p j)"
    and pos: "0<B"
    and B: "\<forall>v<m. r v<B"
    and ind: "mwr_mpoly_indep k p"
  shows "\<exists>J. (\<forall>i<k. Poly_Mapping.keys (J i) \<subseteq> {..<m} \<and> mwr_total_order m (J i) \<le> i) \<and>
    det (mat k k
      (\<lambda>(i,j). pjet_hasse (J i) (p j))) \<noteq> 0"
proof -
  obtain g where g: "g\<in>PiE {..<k} (mwr_jet_words m)"
    and d: "det (mat k k
      (\<lambda>(i,j). pjet_hasse (mwr_jet_index (g i)) (p j))) \<noteq> 0"
    using mwr_kronecker_hasse_minor[OF box pos B ind]
    by blast
  have "\<forall>i<k. Poly_Mapping.keys (mwr_jet_index (g i)) \<subseteq> {..<m} \<and>
      mwr_total_order m (mwr_jet_index (g i)) \<le> i"
    using g by (auto simp: PiE_def dest: mwr_jet_word_bounds)
  with d show ?thesis
    by (intro exI[where x="\<lambda>i. mwr_jet_index (g i)"]) auto
qed

theorem mwr_generalized_wronskian:
  fixes p :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>j<k. pjet_poly_in_box m r (p j)"
    and ind: "mwr_mpoly_indep k p"
  shows "\<exists>J.
    (\<forall>i<k.
      Poly_Mapping.keys (J i) \<subseteq> {..<m} \<and>
      mwr_total_order m (J i) \<le> i) \<and>
    det (mat k k (\<lambda>(i,j). pjet_hasse (J i) (p j))) \<noteq> 0"
proof -
  let ?B = "Suc (Max (r ` {..<m}))"
  have bound: "\<forall>v<m. r v < ?B"
    by (auto simp: less_Suc_eq_le intro: Max_ge)
  show ?thesis
    by (rule mwr_kronecker_hasse_minor_bounded
      [OF box _ bound ind]) simp
qed

end
