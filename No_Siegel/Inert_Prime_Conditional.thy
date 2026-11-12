theory Inert_Prime_Conditional
  imports Prime_Valuation_Log Inert_Determinant_Transfer Quantitative_Finish Archimedean_Parameter_Bound Inert_Prime_Formula
begin

lemma (in green_quadratic_character) green_odd_inert_valuation_log:
  fixes cutoff :: nat
  assumes grid: "P \<subseteq> diagonal_grid (cpx_sqrt d) (natural_grid N)"
    and positive: "0 < green_row_gram_determinant d P J R S"
  shows "(\<Sum>p\<in>green_odd_inert_primes chi cutoff.
      2 * green_min_mass R S p * ln (real p))
    \<le> ln (real_of_int (green_row_gram_determinant d P J R S))"
proof -
  let ?D = "green_row_gram_determinant d P J R S"
  let ?I = "green_odd_inert_primes chi cutoff"
  let ?h = "\<lambda>p. 2 * (\<Sum>r<R. \<Sum>s<S. min (r div p) (S-1-s))"
  have bound: "?h p \<le> multiplicity (int p) ?D"
    if p: "p \<in> ?I" for p
  proof -
    have prime: "prime p" and odd: "odd p" and inert: "chi p = -1"
      using p by (auto simp: green_odd_inert_primes_def green_inert_primes_def)
    have nonzero: "?D \<noteq> 0" using positive by simp
    show ?thesis
      by (rule green_inert_original_paper_valuation[
        OF prime odd inert grid nonzero])
  qed
  have estimate:
    "(\<Sum>p\<in>?I. real (?h p) * ln (real p)) \<le> ln (real_of_int ?D)"
  proof (rule green_weighted_integer_prime_valuation_log[OF positive])
    show "finite ?I" by simp
    show "prime p" if "p \<in> ?I" for p
      using that by (auto simp: green_odd_inert_primes_def green_inert_primes_def)
    show "?h p \<le> multiplicity (int p) ?D" if "p \<in> ?I" for p
      by (rule bound[OF that])
  qed
  show ?thesis
    using estimate by (simp add: green_min_mass_def algebra_simps)
qed

lemma (in green_quadratic_character) green_odd_inert_weighted_floor:
  fixes cutoff :: nat
  assumes grid: "P \<subseteq> diagonal_grid (cpx_sqrt d) (natural_grid N)"
    and positive: "0 < green_row_gram_determinant d P J R S"
  shows "(\<Sum>p\<in>green_odd_inert_primes chi cutoff.
      2 * ln (real p) * real S * green_floor_main_term R p)
    \<le> ln (real_of_int (green_row_gram_determinant d P J R S)) +
      (\<Sum>p\<in>green_odd_inert_primes chi cutoff.
        2 * ln (real p) * green_floor_error R p)"
proof -
  let ?I = "green_odd_inert_primes chi cutoff"
  let ?D = "green_row_gram_determinant d P J R S"
  have prime: "prime p" if "p \<in> ?I" for p
    using that by (auto simp: green_odd_inert_primes_def green_inert_primes_def)
  have ppos: "0 < p" if "p \<in> ?I" for p
    using prime[OF that] prime_gt_1_nat by (simp add: prime_gt_0_nat)
  have weight: "0 \<le> ln (real p)" if "p \<in> ?I" for p
    using prime_gt_1_nat[OF prime[OF that]] by simp
  have valuation:
    "(\<Sum>p\<in>?I. 2 * ln (real p) * green_min_mass R S p)
      \<le> ln (real_of_int ?D)"
    using green_odd_inert_valuation_log[OF grid positive,
      where cutoff=cutoff]
    by (simp add: mult.commute mult.left_commute)
  show ?thesis
    by (rule green_weighted_min_mass_bound[OF _ ppos weight valuation]) simp
qed

lemma (in green_quadratic_character) green_paper_odd_inert_weighted_floor:
  assumes even: "even cparam" and cge: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
    and idxs: "distinct idxs"
      "set idxs = diagonal_grid (cpx_sqrt d)
        (natural_grid (green_N q cparam)) \<times> {..<green_J q cparam}"
  shows "(\<Sum>p\<in>green_odd_inert_primes chi (green_X q cparam).
      2 * ln (real p) * real (green_J q cparam) *
        green_floor_main_term (green_X q cparam) p)
    \<le> (1 / 2 + 11 / real cparam) *
      (real (green_X q cparam)) ^ 2 * real (green_J q cparam) *
      ln (real (green_X q cparam)) +
      (\<Sum>p\<in>green_odd_inert_primes chi (green_X q cparam).
        2 * ln (real p) * green_floor_error (green_X q cparam) p)"
proof -
  let ?X = "green_X q cparam"
  let ?J = "green_J q cparam"
  let ?P = "diagonal_grid (cpx_sqrt d) (natural_grid (green_N q cparam))"
  let ?D = "green_row_gram_determinant d ?P ?J ?X ?J"
  let ?I = "green_odd_inert_primes chi ?X"
  have positive: "0 < ?D"
    by (rule green_paper_gram_determinant_positive[OF even cge large])
  have inert:
    "(\<Sum>p\<in>?I.
      2 * ln (real p) * real ?J * green_floor_main_term ?X p)
      \<le> ln (real_of_int ?D) +
        (\<Sum>p\<in>?I. 2 * ln (real p) * green_floor_error ?X p)"
    by (rule green_odd_inert_weighted_floor[
      OF _ positive, where cutoff="?X" and N="green_N q cparam"]) simp
  have arch:
    "ln (real_of_int ?D) \<le>
      (1 / 2 + 11 / real cparam) * (real ?X)^2 * real ?J *
        ln (real ?X)"
    by (rule green_paper_gram_archimedean_parameter[
      OF even cge large idxs])
  show ?thesis using inert arch by linarith
qed

lemma (in green_quadratic_character) green_paper_odd_inert_prime_comparison:
  assumes even: "even cparam" and cge: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
    and idxs: "distinct idxs"
      "set idxs = diagonal_grid (cpx_sqrt d)
        (natural_grid (green_N q cparam)) \<times> {..<green_J q cparam}"
  shows "real (green_J q cparam) *
      ((real (green_X q cparam))^2 - real (green_X q cparam)) *
      green_odd_inert_prime_weight chi (green_X q cparam)
    \<le> (1 / 2 + 11 / real cparam) *
      (real (green_X q cparam))^2 * real (green_J q cparam) *
      ln (real (green_X q cparam)) +
      2 * real (green_J q cparam) * real (green_X q cparam) *
        green_odd_inert_theta chi (green_X q cparam) +
      2 * (real (green_X q cparam))^3 *
        green_odd_inert_inverse_square_weight chi (green_X q cparam)"
proof -
  have floor:
    "(\<Sum>p\<in>green_odd_inert_primes chi (green_X q cparam).
        2 * ln (real p) * real (green_J q cparam) *
          green_floor_main_term (green_X q cparam) p)
      \<le> (1 / 2 + 11 / real cparam) *
        (real (green_X q cparam))^2 * real (green_J q cparam) *
        ln (real (green_X q cparam)) +
        (\<Sum>p\<in>green_odd_inert_primes chi (green_X q cparam).
          2 * ln (real p) *
            green_floor_error (green_X q cparam) p)"
    by (rule green_paper_odd_inert_weighted_floor[
      OF even cge large idxs])
  show ?thesis
    using floor
    by (simp only: green_odd_inert_floor_main_formula
      green_odd_inert_floor_error_formula; linarith)
qed

lemma (in green_quadratic_character) green_paper_odd_inert_rearranged:
  assumes even: "even cparam" and cge: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
    and idxs: "distinct idxs"
      "set idxs = diagonal_grid (cpx_sqrt d)
        (natural_grid (green_N q cparam)) \<times> {..<green_J q cparam}"
  shows "green_odd_inert_prime_weight chi (green_X q cparam)
    \<le> (1 / 2 + 11 / real cparam) * ln (real (green_X q cparam)) +
      green_odd_inert_prime_weight chi (green_X q cparam) /
        real (green_X q cparam) +
      2 * green_odd_inert_theta chi (green_X q cparam) /
        real (green_X q cparam) +
      2 * real (green_X q cparam) / real (green_J q cparam) *
        green_odd_inert_inverse_square_weight chi (green_X q cparam)"
proof -
  let ?X = "green_X q cparam"
  let ?J = "green_J q cparam"
  have xpositive: "0 < real ?X"
    using conductor_pos by (simp add: green_X_def)
  have npositive: "0 < green_N q cparam"
    using conductor_pos by (simp add: green_N_def)
  have jbound: "green_N q cparam \<le> ?J"
    by (rule green_paper_row_parameters(1)[OF even cge large])
  have jpositive: "0 < real ?J"
    using npositive jbound by simp
  have comparison:
    "real ?J * ((real ?X)^2 - real ?X) *
        green_odd_inert_prime_weight chi ?X
      \<le> (1 / 2 + 11 / real cparam) *
        (real ?X)^2 * real ?J * ln (real ?X) +
        2 * real ?J * real ?X * green_odd_inert_theta chi ?X +
        2 * (real ?X)^3 *
          green_odd_inert_inverse_square_weight chi ?X"
    by (rule green_paper_odd_inert_prime_comparison[
      OF even cge large idxs])
  show ?thesis
    by (rule green_weighted_comparison_rearrange[
      OF xpositive jpositive comparison])
qed

lemma (in green_quadratic_character) green_paper_odd_inert_conditional:
  assumes even: "even cparam" and cge: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
    and idxs: "distinct idxs"
      "set idxs = diagonal_grid (cpx_sqrt d)
        (natural_grid (green_N q cparam)) \<times> {..<green_J q cparam}"
    and weight: "green_odd_inert_prime_weight chi (green_X q cparam)
      \<le> ln (real (green_X q cparam)) + 2"
    and theta: "green_odd_inert_theta chi (green_X q cparam)
      \<le> ln 4 * real (green_X q cparam)"
    and error: "green_odd_inert_inverse_square_weight chi (green_X q cparam)
      \<le> 2"
  shows "green_odd_inert_prime_weight chi (green_X q cparam)
    \<le> (1 / 2 + 11 / real cparam) *
      ln (real (green_X q cparam)) + 8 * real cparam + 4"
proof -
  let ?X = "green_X q cparam"
  let ?J = "green_J q cparam"
  let ?t = "q ^ (cparam div 2)"
  have tge: "4 \<le> ?t" using cge large by linarith
  have square: "?X = ?t * ?t"
    by (rule green_even_exponent_square[OF even])
  have xge: "4 \<le> real ?X"
  proof -
    have nat_bound: "4 * 4 \<le> ?t * ?t"
      by (rule mult_mono[OF tge tge]) simp_all
    have "4 \<le> ?X" using nat_bound square by linarith
    then show ?thesis by simp
  qed
  have xpos: "0 < real ?X" using xge by linarith
  have npos: "0 < green_N q cparam"
    using conductor_pos by (simp add: green_N_def)
  have jbound: "green_N q cparam \<le> ?J"
    by (rule green_paper_row_parameters(1)[OF even cge large])
  have jpos: "0 < real ?J" using npos jbound by simp
  have ratio: "real ?X / real ?J \<le> 2 * real cparam"
    using green_division_floor_ratio[where x="?X" and c=cparam] cge jpos
    by (simp add: green_J_def)
  have rearranged:
    "green_odd_inert_prime_weight chi ?X \<le>
      (1 / 2 + 11 / real cparam) * ln (real ?X) +
      green_odd_inert_prime_weight chi ?X / real ?X +
      2 * green_odd_inert_theta chi ?X / real ?X +
      2 * real ?X / real ?J *
        green_odd_inert_inverse_square_weight chi ?X"
    by (rule green_paper_odd_inert_rearranged[
      OF even cge large idxs])
  have capped:
    "green_odd_inert_prime_weight chi ?X \<le>
      (1 / 2 + 11 / real cparam) * ln (real ?X) +
      (ln (real ?X) + 2) / real ?X +
      2 * ln 4 + 4 * real ?X / real ?J"
    by (rule green_weighted_comparison_cap[
      OF xpos jpos rearranged weight theta error])
  show ?thesis
    by (rule green_weighted_comparison_constant[OF xge ratio capped])
qed

lemma (in green_quadratic_character) green_paper_inert_conditional:
  assumes even: "even cparam" and cge: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
    and idxs: "distinct idxs"
      "set idxs = diagonal_grid (cpx_sqrt d)
        (natural_grid (green_N q cparam)) \<times> {..<green_J q cparam}"
    and weight: "green_odd_inert_prime_weight chi (green_X q cparam)
      \<le> ln (real (green_X q cparam)) + 2"
    and theta: "green_odd_inert_theta chi (green_X q cparam)
      \<le> ln 4 * real (green_X q cparam)"
    and error: "green_odd_inert_inverse_square_weight chi (green_X q cparam)
      \<le> 2"
  shows "green_inert_prime_weight chi (green_X q cparam)
    \<le> (1 / 2 + 11 / real cparam) *
      ln (real (green_X q cparam)) + 8 * real cparam + 5"
proof -
  have odd:
    "green_odd_inert_prime_weight chi (green_X q cparam)
      \<le> (1 / 2 + 11 / real cparam) *
        ln (real (green_X q cparam)) + 8 * real cparam + 4"
    by (rule green_paper_odd_inert_conditional[
      OF even cge large idxs weight theta error])
  have two:
    "green_inert_prime_weight chi (green_X q cparam) <
      green_odd_inert_prime_weight chi (green_X q cparam) + 1"
    by (rule green_inert_prime_weight_two_correction)
  show ?thesis using odd two by linarith
qed

end
