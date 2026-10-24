theory Roth_Index_Dimension
  imports Roth_Det_Factor_Bounds
begin

lemma roth_taylor_support_vars:
  assumes tc: "roth_taylor_coeff a I P \<noteq> 0"
  shows "Poly_Mapping.keys I \<subseteq> vars P"
proof -
  have "Poly_Mapping.keys I \<subseteq> vars (roth_translate a P)"
    using tc by (auto simp: roth_taylor_coeff_key vars_def)
  then show ?thesis using roth_vars_translate_subset by blast
qed

lemma roth_index_extend_dimension:
  fixes P :: "rat mpoly"
  assumes pv: "vars P \<subseteq> {..<n}"
  shows "roth_index (Suc n) r a P = roth_index n r a P"
proof (cases "P=0")
  case True
  then show ?thesis by simp
next
  case False
  obtain I where ic: "roth_taylor_coeff a I P \<noteq> 0"
    and ie: "roth_index n r a P = ereal (roth_weight n r I)"
    using roth_index_attained[OF False, where m=n and r=r and a=a]
    by blast
  have ik: "Poly_Mapping.keys I \<subseteq> {..<n}"
    using roth_taylor_support_vars[OF ic] pv by blast
  have iw: "roth_weight (Suc n) r I = roth_weight n r I"
    by (rule roth_weight_extend_zero[OF ik])
  have le: "roth_index (Suc n) r a P \<le> roth_index n r a P"
    using roth_index_le_coeff[OF ic, of "Suc n" r] ie iw by simp
  obtain J where jc: "roth_taylor_coeff a J P \<noteq> 0"
    and je: "roth_index (Suc n) r a P =
      ereal (roth_weight (Suc n) r J)"
    using roth_index_attained[OF False, where m="Suc n" and r=r and a=a]
    by blast
  have jk: "Poly_Mapping.keys J \<subseteq> {..<n}"
    using roth_taylor_support_vars[OF jc] pv by blast
  have jw: "roth_weight (Suc n) r J = roth_weight n r J"
    by (rule roth_weight_extend_zero[OF jk])
  have ge: "roth_index n r a P \<le> roth_index (Suc n) r a P"
    using roth_index_le_coeff[OF jc, of n r] je jw by simp
  show ?thesis by (rule antisym[OF le ge])
qed

end
