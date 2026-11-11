theory Inert_Prime_Conditional
  imports Inert_Prime_Rearranged
begin

declare [[apply_timeout = 20]]

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

declare [[apply_timeout = 0]]

end
