theory Roth_Lemma_Int
  imports Roth_Lemma
begin

lemma roth_proj_log_height_cast_bound:
  fixes Q :: "int mpoly"
  shows "roth_proj_log_height (replace_coeff of_int Q) \<le>
    ln (real (roth_int_coeff_sup Q))"
proof -
  have le: "roth_proj_height (replace_coeff of_int Q) \<le>
      roth_int_coeff_sup Q"
    by (rule roth_proj_height_cast)
  have lreal: "real (roth_proj_height (replace_coeff of_int Q)) \<le>
    real (roth_int_coeff_sup Q)" using le by simp
  have ppos: "0 < real (roth_proj_height (replace_coeff of_int Q))"
    using roth_proj_height_ge_one[of "replace_coeff of_int Q"] by simp
  show ?thesis unfolding roth_proj_log_height_def
    by (rule ln_mono[OF lreal ppos])
qed

lemma roth_cast_int_nonzero:
  fixes Q :: "int mpoly"
  assumes q: "Q \<noteq> 0"
  shows "(replace_coeff of_int Q :: rat mpoly) \<noteq> 0"
proof
  assume z: "(replace_coeff of_int Q :: rat mpoly) = 0"
  have eq: "replace_coeff of_int Q =
      MPoly_Type.smult (of_int 0::rat) (replace_coeff of_int Q)"
    using z by simp
  have "Q = MPoly_Type.smult (0::int) Q"
    by (rule roth_cast_smult_inject[OF eq])
  then show False using q by simp
qed

theorem roth_lemma_integer:
  fixes Q :: "int mpoly" and eta :: real
  assumes mp: "0 < m" and q: "Q \<noteq> 0"
    and box: "roth_poly_in_box m r Q"
    and rp: "\<And>v. v<m \<Longrightarrow> 0<r v"
    and ep: "0<eta" and eb: "eta\<le>1/2"
    and ratio: "\<And>v. Suc v<m \<Longrightarrow>
      real (r (Suc v)) \<le> eta^(2^(m-1))*real (r v)"
    and height: "\<And>v. v<m \<Longrightarrow>
      ln (real (roth_int_coeff_sup Q)) + 4*real m*real (r 0) \<le>
        eta^(2^(m-1))*real (r v)*roth_rat_log_height (a v)"
  shows "roth_index m r a (replace_coeff of_int Q) \<le>
    ereal (2*real m*eta)"
proof (rule roth_lemma[OF mp roth_cast_int_nonzero[OF q]])
  show "roth_poly_in_box m r (replace_coeff of_int Q :: rat mpoly)"
    using box by (simp add: roth_box_cast_iff)
  show "0 < r v" if "v<m" for v by (rule rp[OF that])
  show "0 < eta" by (rule ep)
  show "eta \<le> 1/2" by (rule eb)
  show "real (r (Suc v)) \<le> eta^(2^(m-1))*real (r v)"
    if "Suc v<m" for v by (rule ratio[OF that])
  show "roth_proj_log_height (replace_coeff of_int Q) +
      4*real m*real (r 0) \<le>
      eta^(2^(m-1))*real (r v)*roth_rat_log_height (a v)"
    if "v<m" for v
    using roth_proj_log_height_cast_bound[of Q] height[OF that]
    by linarith
qed

end
