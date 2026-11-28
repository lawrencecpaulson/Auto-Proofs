theory Disjoint_Index
  imports "Multivariate_Hasse_Derivatives.MPoly_Taylor"
begin

section \<open>Weighted index of a multivariate polynomial\<close>

definition roth_weight ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> real" where
  "roth_weight m r I \<equiv>
    (\<Sum>v<m. real (Poly_Mapping.lookup I v) / real (r v))"

definition roth_index ::
  "[nat, nat \<Rightarrow> nat, nat \<Rightarrow> 'a::comm_ring_1, 'a mpoly] \<Rightarrow> ereal" where
  "roth_index m r a P \<equiv>
    Inf {ereal (roth_weight m r I) | I. pjet_taylor_coeff a I P \<noteq> 0}"

lemma roth_weight_add:
  "roth_weight m r (I + J) = roth_weight m r I + roth_weight m r J"
  by (simp add: roth_weight_def lookup_add sum.distrib add_divide_distrib)

lemma roth_weight_nonneg:
  "0 \<le> roth_weight m r I"
  unfolding roth_weight_def
  by (intro sum_nonneg divide_nonneg_nonneg; simp)

lemma roth_index_ge_iff:
  "(\<theta>::ereal) \<le> roth_index m r a P \<longleftrightarrow>
    (\<forall>I. ereal (roth_weight m r I) < \<theta> \<longrightarrow> pjet_taylor_coeff a I P = 0)"
  by (auto simp: roth_index_def le_Inf_iff linorder_not_less)

lemma roth_index_translate:
  "roth_index m r a (pjet_translate b P) = roth_index m r (\<lambda>v. a v + b v) P"
  by (simp add: roth_index_def pjet_taylor_coeff_translate)

lemma roth_index_vanish_self:
  assumes "ereal (roth_weight m r I) < roth_index m r a P"
  shows "pjet_taylor_coeff a I P = 0"
  using assms roth_index_ge_iff[of "roth_index m r a P" m r a P]
  by simp

lemma roth_index_add:
  "min (roth_index m r a P) (roth_index m r a Q) \<le> roth_index m r a (P + Q)"
  by (auto simp: roth_index_ge_iff pjet_taylor_coeff_add
    roth_index_vanish_self)

lemma roth_index_le_coeff:
  assumes "pjet_taylor_coeff a I P \<noteq> 0"
  shows "roth_index m r a P \<le> ereal (roth_weight m r I)"
  using assms by (auto simp: roth_index_def intro: Inf_lower)

lemma roth_index_mult_coeff:
  assumes c: "pjet_taylor_coeff a I (P * Q) \<noteq> 0"
  shows "roth_index m r a P + roth_index m r a Q \<le> ereal (roth_weight m r I)"
proof -
  obtain J K where j: "pjet_taylor_coeff a J P \<noteq> 0"
    and k: "pjet_taylor_coeff a K Q \<noteq> 0"
    and i: "I = J + K"
    using pjet_taylor_coeff_mult_support[OF c] by blast
  obtain h1: "roth_index m r a P \<le> ereal (roth_weight m r J)"
     and h2: "roth_index m r a Q \<le> ereal (roth_weight m r K)"
    using j k by (metis roth_index_le_coeff)
  have "roth_index m r a P + roth_index m r a Q \<le>
      ereal (roth_weight m r J) + ereal (roth_weight m r K)"
    by (rule add_mono[OF h1 h2])
  also have "\<dots> = ereal (roth_weight m r I)"
    by (simp add: i roth_weight_add)
  finally show ?thesis .
qed

lemma roth_index_mult:
  "roth_index m r a P + roth_index m r a Q \<le> roth_index m r a (P * Q)"
  unfolding roth_index_ge_iff
  by (meson roth_index_mult_coeff linorder_not_less)

lemma roth_index_infty_iff:
  "roth_index m r a P = (\<infinity>::ereal) \<longleftrightarrow> P = 0"
  using roth_index_ge_iff[of "\<infinity>" m r a P]
  by (simp add: pjet_taylor_coeff_all_zero)

lemma roth_index_zero [simp]: "roth_index m r a 0 = (\<infinity>::ereal)"
  by (simp add: roth_index_infty_iff)

lemma roth_index_nonneg: "(0::ereal) \<le> roth_index m r a P"
  unfolding roth_index_ge_iff
  by (meson ereal_less(1) linorder_not_less roth_weight_nonneg)

lemma finite_roth_index_terms:
  "finite {ereal (roth_weight m r I) | I. pjet_taylor_coeff a I P \<noteq> 0}"
  by (simp add: pjet_taylor_coeff_key setcompr_eq_image)

lemma roth_index_attained:
  assumes p: "P \<noteq> 0"
  obtains I where
    "pjet_taylor_coeff a I P \<noteq> 0"
    "roth_index m r a P = ereal (roth_weight m r I)"
proof -
  let ?S = "{ereal (roth_weight m r I) | I. pjet_taylor_coeff a I P \<noteq> 0}"
  have "finite ?S"
    by (rule finite_roth_index_terms)
  have "?S \<noteq> {}"
    using p pjet_taylor_coeff_all_zero by auto
  obtain I where c: "pjet_taylor_coeff a I P \<noteq> 0"
    and e: "Min ?S = ereal (roth_weight m r I)"
    using Min_in[OF \<open>finite ?S\<close> \<open>?S \<noteq> {}\<close>] by auto
  have "roth_index m r a P = ereal (roth_weight m r I)"
    by (simp add: roth_index_def cInf_eq_Min[OF \<open>finite ?S\<close> \<open>?S \<noteq> {}\<close>] e)
  then show ?thesis
    using that c by blast
qed

lemma roth_disjoint_index_mult_nonzero:
  fixes P Q :: "'a::idom mpoly"
  assumes disj: "vars P \<inter> vars Q = {}"
    and p: "P \<noteq> 0"
    and q: "Q \<noteq> 0"
  shows "roth_index m r a (P * Q) = roth_index m r a P + roth_index m r a Q"
proof (intro antisym roth_index_mult)
  obtain I where i: "pjet_taylor_coeff a I P \<noteq> 0"
    and ie: "roth_index m r a P = ereal (roth_weight m r I)"
    using roth_index_attained[OF p] by blast
  obtain J where j: "pjet_taylor_coeff a J Q \<noteq> 0"
    and je: "roth_index m r a Q = ereal (roth_weight m r J)"
    using roth_index_attained[OF q] by blast
  have cij: "pjet_taylor_coeff a (I + J) (P * Q) \<noteq> 0"
    using pjet_disjoint_taylor_coeff[OF disj i j] i j by simp
  show "roth_index m r a (P * Q) \<le> roth_index m r a P + roth_index m r a Q"
    using roth_index_le_coeff[OF cij] by (simp add: ie je roth_weight_add)
qed

lemma roth_disjoint_index_mult:
  fixes P Q :: "'a::idom mpoly"
  assumes "vars P \<inter> vars Q = {}"
  shows "roth_index m r a (P * Q) = roth_index m r a P + roth_index m r a Q"
  using roth_disjoint_index_mult_nonzero[OF assms] by force

end
