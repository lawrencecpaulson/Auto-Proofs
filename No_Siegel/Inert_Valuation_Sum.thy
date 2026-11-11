theory Inert_Valuation_Sum
  imports Prime_Valuation_Log Inert_Valuation Quantitative_Finish
begin

declare [[apply_timeout = 20]]

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

lemma (in green_quadratic_character) green_paper_odd_inert_valuation_log:
  assumes even: "even cparam" and cparam: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
  shows "(\<Sum>p\<in>green_odd_inert_primes chi (green_X q cparam).
      2 * green_min_mass (green_X q cparam) (green_J q cparam) p
        * ln (real p))
    \<le> ln (real_of_int
      (green_row_gram_determinant d
        (diagonal_grid (cpx_sqrt d)
          (natural_grid (green_N q cparam)))
        (green_J q cparam) (green_X q cparam)
        (green_J q cparam)))"
proof -
  have positive:
    "0 < green_row_gram_determinant d
      (diagonal_grid (cpx_sqrt d)
        (natural_grid (green_N q cparam)))
      (green_J q cparam) (green_X q cparam)
      (green_J q cparam)"
    by (rule green_paper_gram_determinant_positive[OF even cparam large])
  show ?thesis
    by (rule green_odd_inert_valuation_log[
      OF _ positive, where N="green_N q cparam"
        and cutoff="green_X q cparam"]) simp
qed

declare [[apply_timeout = 0]]

end
