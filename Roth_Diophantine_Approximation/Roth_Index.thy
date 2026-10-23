theory Roth_Index
  imports
    Roth_Hasse
    "HOL-Library.Extended_Real"
begin

section \<open>Weighted index of a multivariate polynomial\<close>

definition roth_weight ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> real" where
  "roth_weight m r I =
    (\<Sum>v<m. real (Poly_Mapping.lookup I v) / real (r v))"

definition roth_index ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
    (nat \<Rightarrow> 'a::comm_ring_1) \<Rightarrow> 'a mpoly \<Rightarrow> ereal" where
  "roth_index m r a P =
    Inf {ereal (roth_weight m r I) | I. roth_taylor_coeff a I P \<noteq> 0}"

lemma roth_weight_add:
  "roth_weight m r (I + J) = roth_weight m r I + roth_weight m r J"
  by (simp add: roth_weight_def lookup_add sum.distrib
    add_divide_distrib)

lemma roth_weight_nonneg:
  "0 \<le> roth_weight m r I"
  unfolding roth_weight_def
  by (intro sum_nonneg divide_nonneg_nonneg; simp)

lemma roth_inf_iff:
  "(theta::ereal) \<le> Inf S \<longleftrightarrow> (\<forall>x\<in>S. theta \<le> x)"
  by (metis Inf_greatest Inf_lower order_trans)

lemma roth_index_ge_iff:
  "(theta::ereal) \<le> roth_index m r a P \<longleftrightarrow>
    (\<forall>I. ereal (roth_weight m r I) < theta \<longrightarrow>
      roth_taylor_coeff a I P = 0)"
  by (auto simp: roth_index_def roth_inf_iff linorder_not_less)

lemma roth_index_translate:
  "roth_index m r a (roth_translate b P) =
    roth_index m r (\<lambda>v. a v + b v) P"
  by (simp add: roth_index_def roth_taylor_coeff_translate)

lemma roth_index_vanish_self:
  assumes "ereal (roth_weight m r I) < roth_index m r a P"
  shows "roth_taylor_coeff a I P = 0"
  using assms roth_index_ge_iff[of "roth_index m r a P" m r a P]
  by simp

lemma roth_index_add:
  "min (roth_index m r a P) (roth_index m r a Q) \<le>
    roth_index m r a (P + Q)"
  by (auto simp: roth_index_ge_iff roth_taylor_coeff_add
    roth_index_vanish_self)

lemma roth_index_le_coeff:
  assumes "roth_taylor_coeff a I P \<noteq> 0"
  shows "roth_index m r a P \<le> ereal (roth_weight m r I)"
  using assms by (auto simp: roth_index_def intro: Inf_lower)

lemma roth_index_mult_coeff:
  assumes c: "roth_taylor_coeff a I (P * Q) \<noteq> 0"
  shows "roth_index m r a P + roth_index m r a Q \<le>
    ereal (roth_weight m r I)"
proof -
  obtain J K where j: "roth_taylor_coeff a J P \<noteq> 0"
    and k: "roth_taylor_coeff a K Q \<noteq> 0"
    and i: "I = J + K"
    using roth_taylor_coeff_mult_support[OF c] by blast
  have h1: "roth_index m r a P \<le> ereal (roth_weight m r J)"
    using j by (rule roth_index_le_coeff)
  have h2: "roth_index m r a Q \<le> ereal (roth_weight m r K)"
    using k by (rule roth_index_le_coeff)
  have "roth_index m r a P + roth_index m r a Q \<le>
      ereal (roth_weight m r J) + ereal (roth_weight m r K)"
    by (rule add_mono[OF h1 h2])
  also have "\<dots> = ereal (roth_weight m r I)"
    by (simp add: i roth_weight_add)
  finally show ?thesis .
qed

lemma roth_index_mult:
  "roth_index m r a P + roth_index m r a Q \<le>
    roth_index m r a (P * Q)"
  by (auto simp: roth_index_ge_iff)
    (meson roth_index_mult_coeff linorder_not_less)

lemma roth_index_infty_iff:
  "roth_index m r a P = (\<infinity>::ereal) \<longleftrightarrow> P = 0"
  using roth_index_ge_iff[of "\<infinity>" m r a P]
  by (simp add: roth_taylor_coeff_all_zero)

lemma roth_index_zero [simp]:
  "roth_index m r a 0 = (\<infinity>::ereal)"
  by (simp add: roth_index_infty_iff)

lemma roth_index_nonneg:
  "(0::ereal) \<le> roth_index m r a P"
  by (auto simp: roth_index_ge_iff)
    (meson roth_weight_nonneg not_less)

lemma finite_roth_index_terms:
  "finite {ereal (roth_weight m r I) | I.
    roth_taylor_coeff a I P \<noteq> 0}"
  by (simp add: roth_taylor_coeff_key setcompr_eq_image)

lemma roth_index_attained:
  assumes p: "P \<noteq> 0"
  obtains I where
    "roth_taylor_coeff a I P \<noteq> 0"
    "roth_index m r a P = ereal (roth_weight m r I)"
proof -
  let ?S = "{ereal (roth_weight m r I) | I.
    roth_taylor_coeff a I P \<noteq> 0}"
  have fin: "finite ?S"
    by (rule finite_roth_index_terms)
  have ne: "?S \<noteq> {}"
    using p roth_taylor_coeff_all_zero by auto
  have "Min ?S \<in> ?S"
    by (rule Min_in[OF fin ne])
  then obtain I where c: "roth_taylor_coeff a I P \<noteq> 0"
    and e: "Min ?S = ereal (roth_weight m r I)"
    by auto
  have "roth_index m r a P = ereal (roth_weight m r I)"
    by (simp add: roth_index_def cInf_eq_Min[OF fin ne] e)
  then show ?thesis
    using that c by blast
qed

end
