theory Inert_Valuation
  imports Inert_Determinant_Transfer
begin

declare [[apply_timeout = 20]]

lemma (in green_quadratic_character) green_inert_original_paper_valuation:
  assumes prime: "prime p" and odd: "odd p" and inert: "chi p = -1"
    and P: "P \<subseteq> diagonal_grid (cpx_sqrt d) (natural_grid N)"
    and nonzero: "green_row_gram_determinant d P J R S \<noteq> 0"
  shows "2 * (\<Sum>r<R. \<Sum>s<S. min (r div p) (S-1-s)) \<le>
    multiplicity (int p) (green_row_gram_determinant d P J R S)"
proof -
  have gt: "1 < p" by (rule prime_gt_1_nat[OF prime])
  have pneq: "p \<noteq> 1" using gt by linarith
  have nonunit: "\<not> is_unit (int p)" using pneq by simp
  have dvd: "int p ^ (2 * (\<Sum>r<R. \<Sum>s<S.
      min (r div p) (S-1-s))) dvd
    green_row_gram_determinant d P J R S"
    by (rule green_inert_original_paper_determinant_divisible[
      OF prime odd inert P])
  show ?thesis
    by (rule multiplicity_geI[OF nonzero nonunit dvd])
qed

lemma (in green_quadratic_character) green_inert_paper_parameter_valuation:
  assumes prime: "prime p" and odd: "odd p" and inert: "chi p = -1"
    and even: "even cparam" and cparam: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
  shows "2 * (\<Sum>r<green_X q cparam.
      \<Sum>s<green_J q cparam.
        min (r div p) (green_J q cparam-1-s)) \<le>
    multiplicity (int p)
      (green_row_gram_determinant d
        (diagonal_grid (cpx_sqrt d)
          (natural_grid (green_N q cparam)))
        (green_J q cparam) (green_X q cparam)
        (green_J q cparam))"
proof -
  have pos: "0 < green_row_gram_determinant d
      (diagonal_grid (cpx_sqrt d)
        (natural_grid (green_N q cparam)))
      (green_J q cparam) (green_X q cparam)
      (green_J q cparam)"
    by (rule green_paper_gram_determinant_positive[OF even cparam large])
  have nonzero: "green_row_gram_determinant d
      (diagonal_grid (cpx_sqrt d)
        (natural_grid (green_N q cparam)))
      (green_J q cparam) (green_X q cparam)
      (green_J q cparam) \<noteq> 0"
    using pos by simp
  show ?thesis
    by (rule green_inert_original_paper_valuation[
      OF prime odd inert _ nonzero,
      where N="green_N q cparam"]) simp
qed

declare [[apply_timeout = 0]]

end
