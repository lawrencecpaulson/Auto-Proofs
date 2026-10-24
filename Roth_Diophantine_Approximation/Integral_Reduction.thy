theory Integral_Reduction
  imports
    Roth_Approximation
    "Hermite_Lindemann.More_Algebraic_Numbers_HLW"
begin

section \<open>Reduction to algebraic integers\<close>

lemma roth_algebraic_integral_scale:
  fixes \<alpha> :: real
  assumes "algebraic \<alpha>"
  obtains c :: int where "c > 0" "algebraic_int (of_int c * \<alpha>)"
proof -
  obtain p :: "int poly" where root: "ipoly p \<alpha> = 0" and p0: "p \<noteq> 0"
    using assms by (auto simp: algebraic_altdef_ipoly)
  let ?c = "\<bar>Polynomial.lead_coeff p\<bar>"
  have cpos: "?c > 0"
    using p0 by simp
  have "algebraic_int (of_int ?c * \<alpha>)"
    by (rule algebraic_imp_algebraic_int'[OF root p0]) simp
  then show thesis
    using that cpos by blast
qed

lemma roth_irrational_scaled:
  fixes c :: int and \<alpha> :: real
  assumes "c > 0" "\<alpha> \<notin> \<rat>"
  shows "of_int c * \<alpha> \<notin> \<rat>"
proof
  assume scaled: "of_int c * \<alpha> \<in> \<rat>"
  have "(of_int c * \<alpha>) / of_int c \<in> \<rat>"
    by (rule Rats_divide[OF scaled]) simp
  moreover have "(of_int c * \<alpha>) / of_int c = \<alpha>"
    using assms(1) by simp
  ultimately have "\<alpha> \<in> \<rat>"
    by simp
  then show False
    using assms by simp
qed

theorem roth_reduction_to_integral:
  assumes integral:
    "\<And>\<beta> \<delta>::real. algebraic_int \<beta> \<Longrightarrow> \<beta> \<notin> \<rat> \<Longrightarrow>
      \<delta> > 0 \<Longrightarrow> finite (roth_good_pairs \<beta> (2 + \<delta>))"
  shows "\<And>\<alpha> \<epsilon>::real. algebraic \<alpha> \<Longrightarrow> \<alpha> \<notin> \<rat> \<Longrightarrow>
    \<epsilon> > 0 \<Longrightarrow> finite (roth_good_pairs \<alpha> (2 + \<epsilon>))"
proof -
  fix \<alpha> \<epsilon> :: real
  assume alg: "algebraic \<alpha>" and irr: "\<alpha> \<notin> \<rat>" and eps: "\<epsilon> > 0"
  obtain c :: int where c: "c > 0" and ci: "algebraic_int (of_int c * \<alpha>)"
    using roth_algebraic_integral_scale[OF alg] by blast
  have irr': "of_int c * \<alpha> \<notin> \<rat>"
    using roth_irrational_scaled[OF c irr] .
  have dpos: "\<epsilon> / 2 > 0"
    using eps by simp
  have fin: "finite (roth_good_pairs (of_int c * \<alpha>) (2 + \<epsilon> / 2))"
    by (rule integral[OF ci irr' dpos])
  show "finite (roth_good_pairs \<alpha> (2 + \<epsilon>))"
    by (rule finite_roth_good_pairs_of_scaled[OF c _ dpos fin]) (use eps in simp)
qed

end
