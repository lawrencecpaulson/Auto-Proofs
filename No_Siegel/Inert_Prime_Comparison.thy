theory Inert_Prime_Comparison
  imports Inert_Prime_Formula Inert_Weighted_Floor
begin

declare [[apply_timeout = 20]]

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

declare [[apply_timeout = 0]]

end
