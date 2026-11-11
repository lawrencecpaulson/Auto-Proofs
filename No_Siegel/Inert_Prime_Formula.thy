theory Inert_Prime_Formula
  imports Inert_Prime_Sums Quantitative_Finish
begin

declare [[apply_timeout = 20]]

definition green_odd_inert_theta :: "(nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> real" where
  "green_odd_inert_theta chi cutoff =
    (\<Sum>p\<in>green_odd_inert_primes chi cutoff. ln (real p))"

definition green_odd_inert_inverse_square_weight ::
  "(nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> real" where
  "green_odd_inert_inverse_square_weight chi cutoff =
    (\<Sum>p\<in>green_odd_inert_primes chi cutoff.
      ln (real p) / (real p)^2)"

lemma green_odd_inert_floor_main_formula:
  fixes R S cutoff :: nat
  shows "(\<Sum>p\<in>green_odd_inert_primes chi cutoff.
      2 * ln (real p) * real S * green_floor_main_term R p) =
    real S * ((real R)^2 - real R) *
      green_odd_inert_prime_weight chi cutoff -
    2 * real S * real R * green_odd_inert_theta chi cutoff"
proof -
  let ?I = "green_odd_inert_primes chi cutoff"
  have point: "2 * ln (real p) * real S * green_floor_main_term R p =
      real S * ((real R)^2 - real R) * (ln (real p) / real p) -
      2 * real S * real R * ln (real p)"
    if pI: "p \<in> ?I" for p
  proof -
    have prime: "prime p"
      using pI by (auto simp: green_odd_inert_primes_def green_inert_primes_def)
    have nonzero: "(real p) \<noteq> 0"
      using prime_gt_1_nat[OF prime] by simp
    show ?thesis
      using nonzero by (simp add: green_floor_main_term_def field_simps; algebra)
  qed
  have "(\<Sum>p\<in>?I. 2 * ln (real p) * real S * green_floor_main_term R p) =
      (\<Sum>p\<in>?I.
        real S * ((real R)^2 - real R) * (ln (real p) / real p) -
        2 * real S * real R * ln (real p))"
    by (rule sum.cong) (simp_all add: point)
  also have "... =
      real S * ((real R)^2 - real R) *
        green_odd_inert_prime_weight chi cutoff -
      2 * real S * real R * green_odd_inert_theta chi cutoff"
    by (simp only: green_odd_inert_prime_weight_def
      green_odd_inert_theta_def sum_subtractf sum_distrib_left[symmetric])
  finally show ?thesis .
qed

lemma green_odd_inert_floor_error_formula:
  fixes R cutoff :: nat
  shows "(\<Sum>p\<in>green_odd_inert_primes chi cutoff.
      2 * ln (real p) * green_floor_error R p) =
    2 * (real R)^3 * green_odd_inert_inverse_square_weight chi cutoff"
proof -
  let ?I = "green_odd_inert_primes chi cutoff"
  have point: "2 * ln (real p) * green_floor_error R p =
      2 * (real R)^3 * (ln (real p) / (real p)^2)"
    if pI: "p \<in> ?I" for p
  proof -
    show ?thesis
      by (simp add: green_floor_error_def power_divide
        power2_eq_square power3_eq_cube algebra_simps)
  qed
  have "(\<Sum>p\<in>?I. 2 * ln (real p) * green_floor_error R p) =
      (\<Sum>p\<in>?I.
        2 * (real R)^3 * (ln (real p) / (real p)^2))"
    by (rule sum.cong) (simp_all add: point)
  also have "... = 2 * (real R)^3 *
      green_odd_inert_inverse_square_weight chi cutoff"
    by (simp only: green_odd_inert_inverse_square_weight_def
      sum_distrib_left[symmetric])
  finally show ?thesis .
qed

lemma green_weighted_comparison_rearrange:
  fixes x s a ell w theta err :: real
  assumes x: "0 < x" and s: "0 < s"
    and comparison:
      "s * (x^2 - x) * w \<le>
        a * x^2 * s * ell + 2 * s * x * theta + 2 * x^3 * err"
  shows "w \<le> a * ell + w / x + 2 * theta / x + 2 * x / s * err"
proof -
  let ?b = "a * ell + w / x + 2 * theta / x + 2 * x / s * err - w"
  have identity:
    "s * x^2 * ?b =
      a * x^2 * s * ell + 2 * s * x * theta + 2 * x^3 * err -
        s * (x^2 - x) * w"
    using x s by (simp add: field_simps; algebra)
  have nonneg: "0 \<le> s * x^2 * ?b"
    using comparison identity by linarith
  have factor: "0 < s * x^2" using x s by simp
  have "0 \<le> ?b"
  proof (rule ccontr)
    assume "\<not> 0 \<le> ?b"
    then have negative: "?b < 0" by simp
    have "s * x^2 * ?b < 0"
      by (rule mult_pos_neg[OF factor negative])
    then show False using nonneg by linarith
  qed
  then show ?thesis by linarith
qed

lemma green_weighted_comparison_cap:
  fixes x s a ell w theta err :: real
  assumes x: "0 < x" and s: "0 < s"
    and comparison:
      "w \<le> a * ell + w / x + 2 * theta / x + 2 * x / s * err"
    and weight: "w \<le> ell + 2"
    and theta: "theta \<le> ln 4 * x"
    and error: "err \<le> 2"
  shows "w \<le> a * ell + (ell + 2) / x + 2 * ln 4 + 4 * x / s"
proof -
  have wcap: "w / x \<le> (ell + 2) / x"
    by (rule divide_right_mono[OF weight]) (use x in simp)
  have tcap: "2 * theta / x \<le> 2 * ln 4"
  proof -
    have "theta / x \<le> ln 4"
      using theta x by (simp add: pos_divide_le_eq)
    then show ?thesis by simp
  qed
  have ecap: "2 * x / s * err \<le> 4 * x / s"
  proof -
    have nonneg: "0 \<le> 2 * x / s" using x s by simp
    have "(2 * x / s) * err \<le> (2 * x / s) * 2"
      by (rule mult_left_mono[OF error nonneg])
    then show ?thesis by (simp add: algebra_simps)
  qed
  show ?thesis using comparison wcap tcap ecap by linarith
qed

lemma green_two_ln_four_less_three:
  "2 * ln (4::real) < 3"
proof -
  have lower: "(2::real) < (1 + (3/4) / real 5)^5"
    by (simp add: power_divide; linarith)
  have upper: "(1 + (3/4) / real 5)^5 \<le> exp (3/4)"
    by (rule exp_ge_one_plus_x_over_n_power_n) simp_all
  have ex: "exp (ln (2::real)) < exp (3/4)"
    using lower upper by simp
  have ln2: "ln (2::real) < 3/4"
    by (rule exp_less_cancel[OF ex])
  have logfour: "ln (4::real) = 2 * ln 2"
  proof -
    have "ln ((2::real)^2) = real (2::nat) * ln (2::real)"
      by (rule ln_realpow)
    then show ?thesis by simp
  qed
  show ?thesis using ln2 logfour by linarith
qed

lemma green_log_plus_two_div_le_one:
  fixes x :: real
  assumes x: "4 \<le> x"
  shows "(ln x + 2) / x \<le> 1"
proof -
  have xpos: "0 < x" using x by linarith
  have halfpos: "0 < x / 2" using xpos by simp
  have loghalf: "ln (x / 2) \<le> x / 2 - 1"
    by (rule ln_le_minus_one[OF halfpos])
  have logtwo: "ln (2::real) \<le> 1"
    using ln_le_minus_one[of 2] by simp
  have logeq: "ln x = ln (x / 2) + ln 2"
  proof -
    have "ln x = ln ((x / 2) * 2)" by simp
    also have "... = ln (x / 2) + ln 2"
      by (rule ln_mult_pos[OF halfpos]) simp
    finally show ?thesis .
  qed
  have "ln x + 2 \<le> x"
    using loghalf logtwo logeq x by linarith
  then show ?thesis using xpos by (simp add: pos_divide_le_eq)
qed

lemma green_weighted_comparison_constant:
  fixes x s c a w :: real
  assumes x: "4 \<le> x"
    and ratio: "x / s \<le> 2 * c"
    and bound:
      "w \<le> a * ln x + (ln x + 2) / x + 2 * ln 4 + 4 * x / s"
  shows "w \<le> a * ln x + 8 * c + 4"
proof -
  have logcap: "(ln x + 2) / x \<le> 1"
    by (rule green_log_plus_two_div_le_one[OF x])
  have logfour: "2 * ln (4::real) < 3"
    by (rule green_two_ln_four_less_three)
  show ?thesis using ratio bound logcap logfour by linarith
qed

lemma green_division_floor_ratio:
  fixes x c :: nat
  assumes c: "0 < c" and quotient: "0 < x div c"
  shows "real x / real (x div c) \<le> 2 * real c"
proof -
  let ?j = "x div c"
  have remainder: "x mod c < c" using c by simp
  have cap: "c \<le> c * ?j"
    using quotient by (cases ?j) auto
  have split: "x = c * ?j + x mod c"
    by (simp add: div_mult_mod_eq mult.commute)
  have nat_bound: "x \<le> 2 * c * ?j"
    using remainder cap split by (simp add: algebra_simps; linarith)
  have real_bound: "real x \<le> 2 * real c * real ?j"
    using of_nat_mono[OF nat_bound] by (simp add: algebra_simps)
  show ?thesis
    using real_bound quotient by (simp add: pos_divide_le_eq)
qed

declare [[apply_timeout = 0]]

end
