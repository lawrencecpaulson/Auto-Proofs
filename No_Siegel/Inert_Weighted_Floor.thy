theory Inert_Weighted_Floor
  imports Inert_Valuation_Sum Archimedean_Parameter_Bound
begin

declare [[apply_timeout = 20]]

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

declare [[apply_timeout = 0]]

end
