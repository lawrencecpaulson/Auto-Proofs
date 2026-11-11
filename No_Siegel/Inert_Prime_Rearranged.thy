theory Inert_Prime_Rearranged
  imports Inert_Prime_Comparison
begin

declare [[apply_timeout = 20]]

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

declare [[apply_timeout = 0]]

end
