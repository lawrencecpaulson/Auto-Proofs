(*  Title:      Gelfond_Schneider/GS_Preliminaries.thy
    Author:     OpenAI Codex

Set-valued logarithms and powers, with bridge lemmas from the existing
Hermite-Lindemann development.
*)

theory GS_Preliminaries
  imports
    "HOL-Analysis.Complex_Transcendental"
    "Hermite_Lindemann.Hermite_Lindemann"
    "Algebraic_Numbers.Complex_Algebraic_Numbers"
begin

section \<open>Set-Valued Logarithms and Powers\<close>

definition log_values :: "complex \<Rightarrow> complex set"
  where "log_values a \<equiv> {z. exp z = a}"

definition power_values :: "complex \<Rightarrow> complex \<Rightarrow> complex set"
  where "power_values a b \<equiv> {w. \<exists>z\<in>log_values a. w = exp (b * z)}"

lemma mem_log_values_iff [simp]:
  "z \<in> log_values a \<longleftrightarrow> exp z = a"
  by (simp add: log_values_def)

lemma mem_power_values_iff:
  "w \<in> power_values a b \<longleftrightarrow> (\<exists>z. z \<in> log_values a \<and> w = exp (b * z))"
  by (auto simp: power_values_def)

lemma zero_in_log_values_iff [simp]:
  "0 \<in> log_values a \<longleftrightarrow> a = 1"
  by (simp add: log_values_def)

lemma Ln_in_log_values [intro]:
  assumes "a \<noteq> 0"
  shows "Ln a \<in> log_values a"
  using assms by (simp add: log_values_def)

lemma log_values_nonempty_iff [simp]:
  "log_values a \<noteq> {} \<longleftrightarrow> a \<noteq> 0"
proof
  assume "a \<noteq> 0"
  then show "log_values a \<noteq> {}"
    using Ln_in_log_values by blast
qed (auto simp: log_values_def)

lemma power_values_nonempty_iff [simp]:
  "power_values a b \<noteq> {} \<longleftrightarrow> a \<noteq> 0"
  by (auto simp: power_values_def)

lemma principal_power_value_mem [intro]:
  assumes "a \<noteq> 0"
  shows "exp (b * Ln a) \<in> power_values a b"
  using assms by (auto simp: power_values_def)

lemma power_values_nonzero:
  assumes "w \<in> power_values a b"
  shows "w \<noteq> 0"
  using assms by (auto simp: power_values_def)

section \<open>Preliminaries\<close>

lemma algebraic_log_value_transcendental:
  assumes "algebraic a"
  assumes "a \<noteq> 0"
  assumes "a \<noteq> 1"
  assumes "z \<in> log_values a"
  shows "\<not> algebraic z"
proof
  assume algz: "algebraic z"
  from assms have expz: "exp z = a"
    by (simp add: log_values_def)
  have "\<not> algebraic z"
    by (rule transcendental_complex_logarithm) (use assms expz in auto)
  with algz show False
    by contradiction
qed

lemma algebraic_log_value_eq_zero:
  assumes "algebraic a"
  assumes "z \<in> log_values a"
  assumes "algebraic z"
  shows "z = 0"
  using assms by (metis algebraic_exp_complex_iff mem_log_values_iff)

lemma algebraic_powi [intro]:
  assumes "algebraic (x :: complex)"
  shows "algebraic (x powi n)"
proof (cases "n \<ge> 0")
  case True then show ?thesis
    using assms by (metis algebraic_power power_int_def)
next
  case False
  have "x powi n = inverse (x ^ nat (-n))"
    using False by (simp add: power_int_def field_simps)
  moreover have "algebraic (inverse (x ^ nat (-n)))"
    by (intro algebraic_inverse algebraic_power assms)
  ultimately show ?thesis
    by simp
qed

lemma algebraic_power_value_rational:
  fixes a q w :: complex
  assumes "algebraic a"
  assumes "q \<in> \<rat>"
  assumes "w \<in> power_values a q"
  shows "algebraic w"
proof -
  from assms(2) obtain p d where d: "d > 0" and q: "q = of_int p / of_int d"
    by (elim Rats_cases') blast
  from assms(3) obtain z where z: "z \<in> log_values a" "w = exp (q * z)"
    by (auto simp: power_values_def)
  have "w ^ nat d = exp (of_nat (nat d) * (q * z))"
    using z(2) d by (simp flip: exp_of_nat_mult)
  also have "... = exp (of_int p * z)"
    unfolding q using d by (simp add: field_simps algebra_simps)
  finally have wpow: "w ^ nat d = exp (of_int p * z)" .
  have "exp (of_int p * z) = a powi p"
    using z(1) by (metis exp_power_int mem_log_values_iff)
  then show ?thesis
    using d \<open>algebraic a\<close> algebraic_powi wpow
    by (metis algebraic_power_iff zero_less_nat_eq)
qed

lemma power_valueE:
  assumes "w \<in> power_values a b"
  obtains z where "z \<in> log_values a" and "w = exp (b * z)"
  using assms by (auto simp: power_values_def)

lemma power_value_log_valueE:
  assumes "w \<in> power_values a b"
  obtains z where "z \<in> log_values a" and "b * z \<in> log_values w"
  using assms by (auto simp: power_values_def)

lemma lead_coeff_min_int_poly_eq_1_of_algebraic_int:
  fixes x::complex
  assumes algint: "algebraic_int x"
  shows "Polynomial.lead_coeff (min_int_poly x) = 1"
proof -
  obtain q :: "int poly" where qx: "ipoly q x = 0" and monic_q: "Polynomial.lead_coeff q = 1"
    using algint unfolding algebraic_int_altdef_ipoly by blast
  have q0: "q \<noteq> 0"
    using monic_q by auto
  have q_nu: "\<not> q dvd 1"
    using qx by (metis of_int_poly_hom.hom_dvd_1 poly_zero_imp_not_unit)
  obtain F where F: "mset_factors F q" and qF: "q = prod_mset F"
    using mset_factors_exist[OF q0 q_nu] by blast
  have qxF: "poly (prod_mset (image_mset of_int_poly F)) x = 0"
    using qF qx by (metis of_int_poly_hom.hom_prod_mset)
  from qxF[unfolded poly_prod_mset_zero_iff]
  obtain f where fF: "f \<in># F" and fx: "ipoly f x = 0"
    by auto
  have irr_f: "irreducible f" and f0: "f \<noteq> 0"
    using F fF by auto
  have f_rep: "f represents x"
    by (rule representsI[OF fx f0])
  let ?g = "cf_pos_poly f"
  have g_rep: "?g represents x"
    using f_rep by simp
  have deg_f_ne0: "Polynomial.degree f \<noteq> 0"
    using f_rep by (auto dest: represents_imp_degree)
  have irr_g: "irreducible ?g"
    by (rule irreducible_cf_pos_poly[OF irr_f deg_f_ne0])
  have lc_g_pos: "Polynomial.lead_coeff ?g > 0"
    using lead_coeff_cf_pos_poly[of f] f0 by simp
  have prim_f: "primitive f"
    using irreducible_content[OF irr_f] deg_f_ne0 by auto
  have f_prim: "Polynomial.content f = 1"
    using prim_f by (simp add: primitive_iff_content_eq_1)
  have f_eq: "f = Polynomial.smult (sgn (Polynomial.lead_coeff f)) ?g"
    using cf_pos_poly_main[of f] f_prim by simp
  have f_dvd_q: "f dvd q"
    using F fF by (auto dest: mset_factors_imp_dvd)
  obtain h where q_eq: "q = ?g * h"
    using dvd_trans[OF cf_pos_poly_dvd f_dvd_q] by (elim dvdE)
  have "Polynomial.lead_coeff (?g * h) = Polynomial.lead_coeff ?g * Polynomial.lead_coeff h"
    by (rule Polynomial.lead_coeff_mult)
  then have "Polynomial.lead_coeff ?g dvd Polynomial.lead_coeff q"
    unfolding q_eq by auto
  with lc_g_pos monic_q have lc_g_1: "Polynomial.lead_coeff ?g = 1"
    by (auto elim!: dvdE)
  then show ?thesis
    by (metis g_rep irr_g lc_g_pos min_int_poly_unique)
qed

end
