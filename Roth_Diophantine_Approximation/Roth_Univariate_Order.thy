theory Roth_Univariate_Order
  imports
    Roth_Univariate_Bridge
    Berlekamp_Zassenhaus.Mahler_Measure
    Polynomial_Factorization.Kronecker_Factorization
begin

section \<open>Mahler measure of a rational point\<close>

lemma roth_linear_cast_complex:
  fixes p q :: int
  assumes q: "q \<noteq> 0"
  shows "(map_poly of_int [:-p,q:] :: complex poly) =
    smult (of_int q) [:- (of_int p / of_int q), 1:]"
  using q by (simp add: smult_pCons)

lemma roth_mahler_smult_linear:
  fixes c a :: complex
  shows "mahler_measure_poly (smult c [:-a,1:]) =
    cmod c * max 1 (cmod a)"
  using mahler_measure_poly_explicit[of c "[a]"] by simp

lemma roth_mahler_linear_pre:
  fixes p q :: int
  assumes q: "q \<noteq> 0"
  shows "mahler_measure [:-p,q:] =
    of_int (abs q) * max 1 (of_int (abs p) / of_int (abs q))"
proof -
  have e: "(map_poly of_int [:-p,q:] :: complex poly) =
    smult (of_int q) [:- (of_int p / of_int q), 1:]"
    by (rule roth_linear_cast_complex[OF q])
  show ?thesis
    unfolding mahler_measure_def e roth_mahler_smult_linear
    by (simp add: norm_divide)
qed

lemma roth_mahler_linear:
  fixes p q :: int
  assumes q: "q > 0"
  shows "mahler_measure [:-p,q:] = of_int (max (abs p) q)"
  using roth_mahler_linear_pre[of q p] q
  by (simp add: max_mult_distrib_left)

lemma roth_mahler_mult:
  fixes Q R :: "int poly"
  shows "mahler_measure (Q*R) =
    mahler_measure Q * mahler_measure R"
  unfolding mahler_measure_def of_int_poly_hom.hom_mult
  by (rule measure_eq_prod)

lemma roth_mahler_one:
  "mahler_measure (1::int poly) = 1"
  by (simp add: mahler_measure_def mahler_measure_poly_def)

lemma roth_mahler_power:
  fixes Q :: "int poly"
  shows "mahler_measure (Q^n) = mahler_measure Q ^n"
  by (induction n)
    (simp_all add: roth_mahler_one roth_mahler_mult)

lemma roth_linear_content:
  fixes p q :: int
  assumes cpq: "coprime p q"
  shows "Polynomial.content [:-p,q:] = 1"
  using cpq by (simp add: coprime_commute)

lemma roth_linear_cast_rat:
  fixes p q :: int
  assumes q: "q \<noteq> 0"
  shows "(map_poly of_int [:-p,q:] :: rat poly) =
    smult (of_int q) [:- Rat.Fract p q, 1:]"
  using q by (simp add: smult_pCons Rat.Fract_of_int_quotient)

lemma roth_linear_power_content:
  fixes p q :: int
  assumes cpq: "coprime p q"
  shows "Polynomial.content ([:-p,q:] ^ n) = 1"
  by (induction n)
    (simp_all only: power_0 power_Suc content_1 content_mult
      roth_linear_content[OF cpq] mult_1_left mult_1_right)

lemma roth_linear_power_cast_rat:
  fixes p q :: int
  assumes q: "q \<noteq> 0"
  shows "(map_poly of_int ([:-p,q:] ^ n) :: rat poly) =
    smult ((of_int q)^n) ([:- Rat.Fract p q,1:]^n)"
  unfolding of_int_poly_hom.hom_power
    roth_linear_cast_rat[OF q] smult_power by simp

lemma roth_int_poly_cast_nonzero:
  fixes Q :: "int poly"
  assumes "Q \<noteq> 0"
  shows "(map_poly of_int Q :: rat poly) \<noteq> 0"
  using assms by simp

lemma roth_linear_power_cast_dvd:
  fixes Q :: "int poly"
  assumes q: "q \<noteq> (0::int)"
  shows "((map_poly of_int ([:-p,q:] ^ n) :: rat poly)
      dvd map_poly of_int Q) =
    ([:-Rat.Fract p q,1:] ^ n dvd map_poly of_int Q)"
  unfolding roth_linear_power_cast_rat[OF q]
  using q by (simp add: smult_dvd_iff)

lemma roth_linear_power_dvd:
  fixes Q :: "int poly"
  assumes q: "q \<noteq> (0::int)"
    and cpq: "coprime p q"
    and Q: "Q \<noteq> 0"
  shows "[:-p,q:] ^ n dvd Q \<longleftrightarrow>
    n \<le> Polynomial.order (Rat.Fract p q)
      (map_poly of_int Q :: rat poly)"
proof -
  have e1: "([:-p,q:] ^ n dvd Q) =
    ((map_poly of_int ([:-p,q:] ^ n) :: rat poly)
      dvd map_poly of_int Q)"
    by (rule dvd_poly_int_content_1
      [OF roth_linear_power_content[OF cpq]])
  have e2: "((map_poly of_int ([:-p,q:] ^ n) :: rat poly)
      dvd map_poly of_int Q) =
    ([:-Rat.Fract p q,1:] ^ n dvd map_poly of_int Q)"
    by (rule roth_linear_power_cast_dvd[OF q])
  have e3: "([:-Rat.Fract p q,1:] ^ n dvd
      (map_poly of_int Q :: rat poly)) =
    (n \<le> Polynomial.order (Rat.Fract p q)
      (map_poly of_int Q))"
    using order_divides[of "Rat.Fract p q" n
      "map_poly of_int Q"] roth_int_poly_cast_nonzero[OF Q]
    by blast
  show ?thesis using e1 e2 e3 by simp
qed

lemma roth_mahler_order_le:
  fixes Q :: "int poly"
  assumes q: "q > (0::int)"
    and cpq: "coprime p q"
    and Q: "Q \<noteq> 0"
  shows "of_int (max (abs p) q) ^
      Polynomial.order (Rat.Fract p q)
        (map_poly of_int Q :: rat poly)
    \<le> mahler_measure Q"
proof -
  let ?l = "Polynomial.order (Rat.Fract p q)
    (map_poly of_int Q :: rat poly)"
  have dvd: "[:-p,q:] ^ ?l dvd Q"
    using roth_linear_power_dvd[of q p Q ?l]
      q cpq Q by simp
  have "mahler_measure ([:-p,q:] ^ ?l) \<le> mahler_measure Q"
    by (rule mahler_measure_dvd[OF Q dvd])
  then show ?thesis
    by (simp add: roth_mahler_linear[OF q] roth_mahler_power)
qed

lemma roth_coprime_bridge:
  fixes p q :: int
  assumes cpq: "coprime p q"
  shows "algebraic_semidom_class.coprime p q"
  using cpq by (simp add: coprime_iff_gcd_eq_1)

lemma roth_rat_height_order_le:
  fixes Q :: "int poly"
  assumes q: "q > (0::int)"
    and cpq: "coprime p q"
    and Q: "Q \<noteq> 0"
  shows "real (roth_rat_height (Rat.Fract p q)) ^
      Polynomial.order (Rat.Fract p q)
        (map_poly of_int Q :: rat poly)
    \<le> mahler_measure Q"
  using roth_mahler_order_le[OF q cpq Q]
    roth_rat_height_Fract[OF q roth_coprime_bridge[OF cpq]] q
  by simp

lemma roth_coeff_square_le:
  fixes Q :: "int poly"
  assumes a: "a \<in> set (Polynomial.coeffs Q)"
  shows "a*a \<le>
    int (roth_int_coeff_sup (poly_to_mpoly v Q)) ^ 2"
proof -
  have h: "abs a \<le>
    int (roth_int_coeff_sup (poly_to_mpoly v Q))"
    using roth_int_coeff_sup_poly_coeffs[OF a, of v] by simp
  have "(abs a)^2 \<le>
    int (roth_int_coeff_sup (poly_to_mpoly v Q))^2"
    by (rule power_mono[OF h]) simp
  then show ?thesis by (simp add: power2_eq_square)
qed

lemma roth_coeff_square_sum_le:
  fixes Q :: "int poly"
  shows "(\<Sum>a\<leftarrow>Polynomial.coeffs Q. a*a) \<le>
    int (length (Polynomial.coeffs Q)) *
      int (roth_int_coeff_sup (poly_to_mpoly v Q)) ^ 2"
proof -
  have "(\<Sum>a\<leftarrow>Polynomial.coeffs Q. a*a) \<le>
    (\<Sum>a\<leftarrow>Polynomial.coeffs Q.
      int (roth_int_coeff_sup (poly_to_mpoly v Q)) ^ 2)"
    by (rule sum_list_mono) (rule roth_coeff_square_le)
  also have "... =
    int (length (Polynomial.coeffs Q)) *
      int (roth_int_coeff_sup (poly_to_mpoly v Q)) ^ 2"
    by (simp add: map_replicate_const sum_list_replicate)
  finally show ?thesis .
qed

lemma roth_cast_square_id:
  "real_of_int (int n * int H^2) = real n * (real H)^2"
  by simp

lemma roth_coeff_square_sum_real_le:
  fixes Q :: "int poly"
  shows "real_of_int
      (\<Sum>a\<leftarrow>Polynomial.coeffs Q. a*a) \<le>
    real (length (Polynomial.coeffs Q)) *
      real (roth_int_coeff_sup (poly_to_mpoly v Q)) ^ 2"
proof -
  note h = roth_coeff_square_sum_le[of Q v]
  have hreal: "real_of_int
      (\<Sum>a\<leftarrow>Polynomial.coeffs Q. a*a) \<le>
    real_of_int (int (length (Polynomial.coeffs Q)) *
      int (roth_int_coeff_sup (poly_to_mpoly v Q)) ^ 2)"
    by (subst of_int_le_iff) (rule h)
  show ?thesis using hreal
    by (simp only: roth_cast_square_id)
qed

lemma roth_mahler_coeff_sup_le:
  fixes Q :: "int poly"
  shows "mahler_measure Q \<le>
    sqrt (real (length (Polynomial.coeffs Q))) *
      real (roth_int_coeff_sup (poly_to_mpoly v Q))"
proof -
  have "mahler_measure Q \<le> sqrt (real_of_int
      (\<Sum>a\<leftarrow>Polynomial.coeffs Q. a*a))"
    by (rule Landau_inequality_mahler_measure)
  also have "... \<le> sqrt
      (real (length (Polynomial.coeffs Q)) *
        real (roth_int_coeff_sup (poly_to_mpoly v Q)) ^ 2)"
    by (rule real_sqrt_le_mono[OF roth_coeff_square_sum_real_le])
  also have "... = sqrt
      (real (length (Polynomial.coeffs Q))) *
        real (roth_int_coeff_sup (poly_to_mpoly v Q))"
    by (simp add: real_sqrt_mult)
  finally show ?thesis .
qed

lemma roth_sqrt_suc_le_exp:
  "sqrt (real (Suc n)) \<le> exp (real n)"
proof -
  have h: "sqrt (real (Suc n)) \<le> real (Suc n)"
    by (rule real_le_lsqrt)
      (simp_all add: power2_eq_square mult_le_cancel_left2)
  have e: "real (Suc n) \<le> exp (real n)"
    using exp_ge_add_one_self[of "real n"] by simp
  show ?thesis using h e by linarith
qed

lemma roth_mahler_exp_degree_le:
  fixes Q :: "int poly"
  assumes Q: "Q \<noteq> 0"
  shows "mahler_measure Q \<le>
    exp (real (degree Q)) *
      real (roth_int_coeff_sup (poly_to_mpoly v Q))"
  using roth_mahler_coeff_sup_le[of Q v]
    roth_sqrt_suc_le_exp[of "degree Q"] Q
  by (simp add: length_coeffs_degree;
    meson mult_right_mono of_nat_0_le_iff order_trans)

lemma roth_univariate_log_order_bound:
  fixes Q :: "int poly"
  assumes q: "q > (0::int)"
    and cpq: "coprime p q"
    and Q: "Q \<noteq> 0"
  shows "real (Polynomial.order (Rat.Fract p q)
      (map_poly of_int Q :: rat poly)) *
      roth_rat_log_height (Rat.Fract p q)
    \<le> ln (real (roth_int_coeff_sup (poly_to_mpoly v Q))) +
      real (degree Q)"
proof -
  let ?H = "real (roth_rat_height (Rat.Fract p q))"
  let ?C = "real (roth_int_coeff_sup (poly_to_mpoly v Q))"
  let ?l = "Polynomial.order (Rat.Fract p q)
    (map_poly of_int Q :: rat poly)"
  have b: "?H ^ ?l \<le> exp (real (degree Q)) * ?C"
    using roth_rat_height_order_le[OF q cpq Q]
      roth_mahler_exp_degree_le[OF Q]
    by (rule order_trans)
  have log: "ln (?H ^ ?l) \<le>
    ln (exp (real (degree Q)) * ?C)"
    using b by simp
  show ?thesis using log
    by (simp add: ln_realpow ln_mult_pos
      roth_rat_log_height_def mult.commute)
qed

lemma roth_primitive_poly_log_height:
  fixes Q :: "int poly"
  assumes q: "Q \<noteq> 0" and prim: "Polynomial.content Q = 1"
  shows "roth_proj_log_height
      (replace_coeff of_int (poly_to_mpoly v Q) :: rat mpoly) =
    ln (real (roth_int_coeff_sup (poly_to_mpoly v Q)))"
  unfolding roth_proj_log_height_def
  by (simp add: roth_proj_height_poly_to_mpoly[OF q prim])

end
