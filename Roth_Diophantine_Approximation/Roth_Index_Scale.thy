theory Roth_Index_Scale
  imports Roth_Univariate_Any_Index
begin

lemma roth_weight_scale:
  assumes kp: "0 < k"
  shows "roth_weight m r I =
    real k * roth_weight m (\<lambda>v. k*r v) I"
proof -
  have eq: "real (Poly_Mapping.lookup I v) / real (r v) =
      real k * (real (Poly_Mapping.lookup I v) / real (k*r v))"
    for v
  proof (cases "r v=0")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using kp
      by (simp add: field_simps)
  qed
  have "roth_weight m r I =
    (\<Sum>v<m. real (Poly_Mapping.lookup I v) / real (r v))"
    by (simp add: roth_weight_def)
  also have "... =
    (\<Sum>v<m. real k *
      (real (Poly_Mapping.lookup I v) / real (k*r v)))"
    by (rule sum.cong) (use eq in auto)
  also have "... = real k * roth_weight m (\<lambda>v. k*r v) I"
    by (simp add: roth_weight_def sum_distrib_left)
  finally show ?thesis .
qed

lemma roth_index_scale_bound:
  fixes P :: "rat mpoly"
  assumes kp: "0 < k" and pn: "P \<noteq> 0"
    and bound: "roth_index m (\<lambda>v. k*r v) a P \<le> ereal C"
  shows "roth_index m r a P \<le> ereal (real k * C)"
proof -
  obtain I where tc: "roth_taylor_coeff a I P \<noteq> 0"
    and ie: "roth_index m (\<lambda>v. k*r v) a P =
      ereal (roth_weight m (\<lambda>v. k*r v) I)"
    using roth_index_attained[OF pn, where m=m and r="\<lambda>v. k*r v"
      and a=a] by blast
  have w: "roth_weight m (\<lambda>v. k*r v) I \<le> C"
    using ie bound by simp
  have ml: "real k * roth_weight m (\<lambda>v. k*r v) I \<le>
    real k * C"
    by (rule mult_left_mono[OF w]) simp
  have wr: "roth_weight m r I \<le> real k * C"
    using roth_weight_scale[OF kp, of m r I] ml by simp
  have le: "roth_index m r a P \<le> ereal (roth_weight m r I)"
    by (rule roth_index_le_coeff[OF tc])
  show ?thesis by (rule order_trans[OF le]) (use wr in simp)
qed

end
