theory Roth_Hancl_Rucki
  imports
    "Roth_Diophantine_Approximation.Roth_Algebraic_Integer"
    "Transcendence_Series_Hancl_Rucki.Transcendence_Series"
begin

lemma roth_classical_exponent_bound:
  "\<forall>alpha kappa. algebraic alpha \<and> alpha \<notin> \<rat> \<and>
    infinite (roth_good_pairs alpha kappa) \<longrightarrow> kappa \<le> 2"
proof -
  have fin: "\<forall>alpha delta. algebraic alpha \<and> alpha \<notin> \<rat> \<and>
      delta > 0 \<longrightarrow> finite (roth_good_pairs alpha (2+delta))"
    using roth_real_algebraic_finite by blast
  show ?thesis using roth_finite_exponent_iff fin by blast
qed

interpretation roth: RothsTheorem
  by standard (use roth_classical_exponent_bound in
    \<open>simp add: roth_good_pairs_def\<close>)

lemmas roth_hancl_rucki_1 = roth.HanclRucki1
lemmas roth_hancl_rucki_2 = roth.HanclRucki2

end
