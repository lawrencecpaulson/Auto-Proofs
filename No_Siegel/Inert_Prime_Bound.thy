theory Inert_Prime_Bound
  imports Inert_Prime_Conditional Inert_Prime_Analytic
begin

text \<open>Green, Section 6: the weighted inert-prime bound, with an
  explicit conductor threshold and the possible prime 2 included.\<close>

lemma (in green_quadratic_character) green_paper_inert_bound:
  assumes even: "even cparam" and cge: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
    and idxs: "distinct idxs"
      "set idxs = diagonal_grid (cpx_sqrt d)
        (natural_grid (green_N q cparam)) \<times> {..<green_J q cparam}"
  shows "green_inert_prime_weight chi (green_X q cparam)
    \<le> (1 / 2 + 11 / real cparam) *
      ln (real (green_X q cparam)) + 8 * real cparam + 5"
proof -
  have positive: "1 \<le> green_X q cparam"
  proof -
    have tge: "1 \<le> q ^ (cparam div 2)"
      using cge large by linarith
    have square:
      "green_X q cparam =
        q ^ (cparam div 2) * q ^ (cparam div 2)"
      by (rule green_even_exponent_square[OF even])
    have "1 * 1 \<le>
      q ^ (cparam div 2) * q ^ (cparam div 2)"
      by (rule mult_mono[OF tge tge]) simp_all
    then show ?thesis using square by simp
  qed
  show ?thesis
    by (rule green_paper_inert_conditional[OF even cge large idxs
      green_odd_inert_prime_weight_bound[OF positive]
      green_odd_inert_theta_bound[OF positive]
      green_odd_inert_inverse_square_weight_bound])
qed

corollary (in green_quadratic_character) green_paper_inert_bound_uniform:
  assumes even: "even cparam" and cge: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
  shows "green_inert_prime_weight chi (green_X q cparam)
    \<le> (1 / 2 + 11 / real cparam) *
      ln (real (green_X q cparam)) + 8 * real cparam + 5"
proof -
  let ?I = "diagonal_grid (cpx_sqrt d)
    (natural_grid (green_N q cparam)) \<times> {..<green_J q cparam}"
  have finiteI: "finite ?I"
    by (simp add: diagonal_grid_def natural_grid_finite)
  then obtain idxs where idxs: "distinct idxs" "set idxs = ?I"
    using finite_distinct_list[OF finiteI] by auto
  show ?thesis by (rule green_paper_inert_bound[OF even cge large idxs])
qed

corollary (in green_quadratic_character) green_paper_inert_bound_large_conductor:
  assumes even: "even cparam" and cge: "2 \<le> cparam"
    and qge: "2 * cparam \<le> q"
  shows "green_inert_prime_weight chi (green_X q cparam)
    \<le> (1 / 2 + 11 / real cparam) *
      ln (real (green_X q cparam)) + 8 * real cparam + 5"
proof -
  have exponent: "1 \<le> cparam div 2" using cge by simp
  have "q ^ 1 \<le> q ^ (cparam div 2)"
    by (intro power_increasing) (use exponent qge in auto)
  then have large: "2 * cparam \<le> q ^ (cparam div 2)"
    using qge by simp
  show ?thesis
    by (rule green_paper_inert_bound_uniform[OF even cge large])
qed

corollary (in green_quadratic_character) green_paper_inert_bound_64:
  "green_inert_prime_weight chi (q ^ 64) \<le> 43 * ln (real q) + 517"
proof -
  have qge: "2 \<le> q" using conductor_pos by linarith
  have large: "2 * (64::nat) \<le> q ^ (64 div 2)"
  proof -
    have upper: "2 ^ 32 \<le> q ^ 32"
      by (rule power_mono[OF qge]) simp
    have base: "128 \<le> (2::nat) ^ 32" by simp
    show ?thesis using upper base by (simp; linarith)
  qed
  have bound:
    "green_inert_prime_weight chi (green_X q 64)
      \<le> (1 / 2 + 11 / real (64::nat)) *
        ln (real (green_X q 64)) + 8 * real (64::nat) + 5"
    by (rule green_paper_inert_bound_uniform[OF _ _ large]) simp_all
  show ?thesis using bound
    by (simp add: green_X_def ln_realpow; linarith)
qed

theorem green_primitive_real_inert_bound:
  assumes character: "primitive_real_dcharacter q chi"
    and even: "even cparam" and cge: "2 \<le> cparam"
    and qge: "2 * cparam \<le> q"
  shows "green_inert_prime_weight chi (q ^ cparam)
    \<le> (1 / 2 + 11 / real cparam) *
      ln (real (q ^ cparam)) + 8 * real cparam + 5"
proof -
  obtain d where quad: "green_quadratic_character q chi d"
    by (rule primitive_real_character_fundamental_discriminant[OF character])
  interpret Q: green_quadratic_character q chi d by (rule quad)
  show ?thesis
    by (rule Q.green_paper_inert_bound_large_conductor[OF even cge qge,
      unfolded green_X_def])
qed

theorem green_primitive_real_inert_bound_64:
  assumes character: "primitive_real_dcharacter q chi"
  shows "green_inert_prime_weight chi (q ^ 64)
    \<le> 43 * ln (real q) + 517"
proof -
  obtain d where quad: "green_quadratic_character q chi d"
    by (rule primitive_real_character_fundamental_discriminant[OF character])
  interpret Q: green_quadratic_character q chi d by (rule quad)
  show ?thesis by (rule Q.green_paper_inert_bound_64)
qed

end
