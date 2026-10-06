(*  Title:      Gelfond_Schneider/GS_Preliminaries.thy
    Author:     OpenAI Codex

Small bridge lemmas from the existing Hermite-Lindemann development to the
set-valued logarithm interface used by the standalone Gelfond-Schneider
formalization.
*)

theory GS_Preliminaries
  imports
    Log_Values
    "Hermite_Lindemann.Hermite_Lindemann"
    "Algebraic_Numbers.Complex_Algebraic_Numbers"
begin

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
    by (rule transcendental_complex_logarithm[of a z]) (use assms expz in auto)
  with algz show False
    by contradiction
qed

corollary transcendental_Ln_of_algebraic:
  assumes "algebraic a"
  assumes "a \<noteq> 0"
  assumes "a \<noteq> 1"
  shows "\<not> algebraic (Ln a)"
  by (rule algebraic_log_value_transcendental[of a "Ln a"]) (use assms in auto)

lemma algebraic_log_value_eq_zero:
  assumes "algebraic a"
  assumes "z \<in> log_values a"
  assumes "algebraic z"
  shows "z = 0"
proof -
  have "algebraic (exp z :: complex)"
    using assms by auto
  with assms(3) show ?thesis
    by (simp add: algebraic_exp_complex_iff)
qed

lemma algebraic_powi [intro]:
  assumes "algebraic (x :: complex)"
  shows "algebraic (x powi n)"
proof (cases "n \<ge> 0")
  case True
  have "x powi n = x ^ nat n"
    using True by (simp add: power_int_def)
  moreover have "algebraic (x ^ nat n)"
    by (rule algebraic_power[OF assms])
  ultimately show ?thesis
    by simp
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
  have wpow: "w ^ nat d = exp (of_int p * z)"
  proof -
    have "w ^ nat d = exp (of_nat (nat d) * (q * z))"
      using z(2) d by (simp add: exp_of_nat_mult [symmetric])
    also have "... = exp (of_int d * (q * z))"
      using d by simp
    also have "... = exp (of_int p * z)"
      unfolding q using d by (simp add: field_simps algebra_simps)
    finally show ?thesis .
  qed
  have alg_rhs: "algebraic (exp (of_int p * z))"
  proof -
    have exp_powi: "exp z powi p = exp (of_int p * z)"
      by (rule exp_power_int)
    then have "exp (of_int p * z) = exp z powi p"
      by simp
    also have "exp z = a"
      using z(1) by simp
    finally have eq_powi: "exp (of_int p * z) = a powi p" .
    have "algebraic (a powi p)"
      by (rule algebraic_powi[OF assms(1)])
    with eq_powi show ?thesis
      by simp
  qed
  have "algebraic (w ^ nat d)"
    using wpow alg_rhs by simp
  with d show ?thesis
    by simp
qed

lemma power_valueE:
  assumes "w \<in> power_values a b"
  obtains z where "z \<in> log_values a" and "w = exp (b * z)"
  using assms by (auto simp: power_values_def)

lemma power_value_log_valueE:
  assumes "w \<in> power_values a b"
  obtains z where "z \<in> log_values a" and "b * z \<in> log_values w"
proof -
  from assms obtain z where z: "z \<in> log_values a" "w = exp (b * z)"
    by (rule power_valueE)
  have "b * z \<in> log_values w"
    using z by (simp add: log_values_def)
  with z(1) show ?thesis
    using that by blast
qed

lemma principal_power_valueE:
  assumes "a \<noteq> 0"
  shows "exp (b * Ln a) \<in> power_values a b"
  using assms by (rule principal_power_value_mem)

lemma lead_coeff_min_int_poly_eq_1_of_algebraic_int:
  assumes algint: "algebraic_int (x :: complex)"
  shows "Polynomial.lead_coeff (min_int_poly x) = 1"
proof -
  obtain q :: "int poly" where qx: "ipoly q x = 0" and monic_q: "Polynomial.lead_coeff q = 1"
    using algint unfolding algebraic_int_altdef_ipoly by blast
  have q0: "q \<noteq> 0"
    using monic_q by auto
  have q_nu: "\<not> q dvd 1"
  proof
    assume q1: "q dvd 1"
    have qx': "poly (of_int_poly q) x = 0"
      using qx by simp
    from q1 have "of_int_poly q dvd (1 :: complex poly)"
      by (rule of_int_poly_hom.hom_dvd_1[where 'a = complex])
    with poly_zero_imp_not_unit[OF qx'] show False
      by contradiction
  qed
  obtain F where F: "mset_factors F q"
    using mset_factors_exist[OF q0 q_nu] by blast
  have qF: "q = prod_mset F"
    using F by auto
  have qxF: "poly (prod_mset (image_mset of_int_poly F)) x = 0"
  proof -
    have "poly (of_int_poly (prod_mset F)) x = 0"
      using qx qF by simp
    then show ?thesis
      by simp
  qed
  from qxF[unfolded poly_prod_mset_zero_iff]
  obtain f where fF: "f \<in># F" and fx: "ipoly f x = 0"
    by auto
  have irr_f: "irreducible f"
    using F fF by auto
  have f0: "f \<noteq> 0"
    using irr_f by auto
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
  have g_dvd_q: "?g dvd q"
    by (rule dvd_trans[OF cf_pos_poly_dvd f_dvd_q])
  then obtain h where q_eq: "q = ?g * h"
    by (elim dvdE)
  have h0: "h \<noteq> 0"
    using q0 q_eq by auto
  have lc_mult:
      "Polynomial.lead_coeff (?g * h) =
       Polynomial.lead_coeff ?g * Polynomial.lead_coeff h"
    by (rule Polynomial.lead_coeff_mult)
  have "Polynomial.lead_coeff q = Polynomial.lead_coeff ?g * Polynomial.lead_coeff h"
    unfolding q_eq using lc_mult by simp
  then have "Polynomial.lead_coeff ?g dvd Polynomial.lead_coeff q"
    by auto
  then have "Polynomial.lead_coeff ?g dvd 1"
    using monic_q by simp
  with lc_g_pos have lc_g_1: "Polynomial.lead_coeff ?g = 1"
    by (auto elim!: dvdE)
  have "min_int_poly x = ?g"
    by (rule min_int_poly_unique[OF g_rep irr_g]) (use lc_g_pos in auto)
  then show ?thesis
    using lc_g_1 by simp
qed

end
