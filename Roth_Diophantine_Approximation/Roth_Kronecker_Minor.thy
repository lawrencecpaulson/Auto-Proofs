theory Roth_Kronecker_Minor
  imports Roth_Kronecker_Wronskian
begin

section \<open>A nonzero multivariate Hasse minor\<close>

lemma roth_weighted_minor_nonzero:
  fixes p :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>j<k. roth_poly_in_box m r (p j)"
    and pos: "0<B"
    and B: "\<forall>v<m. r v<B"
    and ind: "roth_mpoly_indep k p"
  shows "\<exists>g\<in>PiE {..<k} (roth_jet_words m).
    det (mat k k
      (\<lambda>(i,j). roth_jet_coeff B i (g i) *
        roth_ksubst m B
          (roth_hasse (roth_jet_index (g i)) (p j)))) \<noteq> 0"
proof -
  have u: "roth_poly_indep k
      (\<lambda>j. roth_ksubst m B (p j))"
    by (rule roth_ksubst_indep[OF box pos B ind])
  have nz: "roth_pwronskian k
      (\<lambda>j. roth_ksubst m B (p j)) \<noteq> 0"
    by (rule roth_pwronskian_nonzero[OF u])
  have h: "(\<Sum>g\<in>PiE {..<k} (roth_jet_words m).
      det (mat k k
        (\<lambda>(i,j). roth_jet_coeff B i (g i) *
          roth_ksubst m B
            (roth_hasse (roth_jet_index (g i)) (p j))))) \<noteq> 0"
    using nz roth_kronecker_pwronskian_expansion[OF box pos]
    by simp
  show ?thesis
    by (rule sum.not_neutral_contains_not_neutral[OF h])
      blast
qed

lemma roth_kronecker_hasse_minor:
  fixes p :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>j<k. roth_poly_in_box m r (p j)"
    and pos: "0<B"
    and B: "\<forall>v<m. r v<B"
    and ind: "roth_mpoly_indep k p"
  shows "\<exists>g\<in>PiE {..<k} (roth_jet_words m).
    det (mat k k
      (\<lambda>(i,j). roth_hasse
        (roth_jet_index (g i)) (p j))) \<noteq> 0"
proof -
  obtain g where g: "g\<in>PiE {..<k} (roth_jet_words m)"
    and gnz: "det (mat k k
      (\<lambda>(i,j). roth_jet_coeff B i (g i) *
        roth_ksubst m B
          (roth_hasse (roth_jet_index (g i)) (p j)))) \<noteq> 0"
    using roth_weighted_minor_nonzero[OF box pos B ind]
    by blast
  have hnz: "det (mat k k
      (\<lambda>(i,j). roth_ksubst m B
        (roth_hasse (roth_jet_index (g i)) (p j)))) \<noteq> 0"
    using gnz by (simp add: roth_det_row_mult)
  have Abox: "\<forall>i<k. \<forall>j<k.
      roth_poly_in_box m r
        (roth_hasse (roth_jet_index (g i)) (p j))"
    using box by (auto intro: roth_hasse_box_monotone)
  have d: "det (mat k k
      (\<lambda>(i,j). roth_hasse
        (roth_jet_index (g i)) (p j))) \<noteq> 0"
    by (rule roth_det_ksubst_reflect_nonzero[OF Abox hnz])
  show ?thesis using g d by blast
qed

lemma roth_jet_bounds_PiE:
  assumes "g\<in>PiE {..<k} (roth_jet_words m)"
  shows "\<forall>i<k.
    Poly_Mapping.keys (roth_jet_index (g i)) \<subseteq> {..<m} \<and>
    roth_total_order m (roth_jet_index (g i)) \<le> i"
  using assms
  by (auto simp: PiE_def dest: roth_jet_word_bounds)

theorem roth_kronecker_hasse_minor_bounded:
  fixes p :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>j<k. roth_poly_in_box m r (p j)"
    and pos: "0<B"
    and B: "\<forall>v<m. r v<B"
    and ind: "roth_mpoly_indep k p"
  shows "\<exists>J.
    (\<forall>i<k.
      Poly_Mapping.keys (J i) \<subseteq> {..<m} \<and>
      roth_total_order m (J i) \<le> i) \<and>
    det (mat k k
      (\<lambda>(i,j). roth_hasse (J i) (p j))) \<noteq> 0"
proof -
  obtain g where g: "g\<in>PiE {..<k} (roth_jet_words m)"
    and d: "det (mat k k
      (\<lambda>(i,j). roth_hasse
        (roth_jet_index (g i)) (p j))) \<noteq> 0"
    using roth_kronecker_hasse_minor[OF box pos B ind]
    by blast
  have bounds: "\<forall>i<k.
      Poly_Mapping.keys (roth_jet_index (g i)) \<subseteq> {..<m} \<and>
      roth_total_order m (roth_jet_index (g i)) \<le> i"
    by (rule roth_jet_bounds_PiE[OF g])
  show ?thesis
    by (rule exI[where x="\<lambda>i. roth_jet_index (g i)"])
      (use bounds d in simp)
qed

theorem roth_generalized_wronskian:
  fixes p :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>j<k. roth_poly_in_box m r (p j)"
    and ind: "roth_mpoly_indep k p"
  shows "\<exists>J.
    (\<forall>i<k.
      Poly_Mapping.keys (J i) \<subseteq> {..<m} \<and>
      roth_total_order m (J i) \<le> i) \<and>
    det (mat k k
      (\<lambda>(i,j). roth_hasse (J i) (p j))) \<noteq> 0"
proof -
  let ?B = "Suc (Max (r ` {..<m}))"
  have bound: "\<forall>v<m. r v < ?B"
    by (auto simp: less_Suc_eq_le intro: Max_ge)
  show ?thesis
    by (rule roth_kronecker_hasse_minor_bounded
      [OF box _ bound ind]) simp
qed

end
