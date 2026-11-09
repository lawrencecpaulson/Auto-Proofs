theory Paper_Parameters
  imports Parameter_Rows Quadratic_Character
begin

text \<open>Green, Section 2, parameter choice: the even exponent makes
  X a square, so N is twice its square root.\<close>

definition green_X :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "green_X q cparam = q ^ cparam"

definition green_N :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "green_N q cparam = 2 * q ^ (cparam div 2)"

definition green_J :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "green_J q cparam = green_X q cparam div cparam"

lemma green_even_exponent_square:
  assumes "even cparam"
  shows "green_X q cparam = q ^ (cparam div 2) * q ^ (cparam div 2)"
proof -
  have split: "cparam = cparam div 2 + cparam div 2"
    using even_two_times_div_two[OF assms] by (simp add: mult_2)
  show ?thesis
    unfolding green_X_def by (subst split) (rule power_add)
qed

lemma green_paper_row_parameters:
  assumes even: "even cparam"
    and cparam: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
  shows "green_N q cparam \<le> green_J q cparam"
    and "2 * green_X q cparam * green_J q cparam +
      green_J q cparam * (green_X q cparam + green_J q cparam) <
      green_J q cparam * (green_N q cparam * green_N q cparam)"
proof -
  let ?t = "q ^ (cparam div 2)"
  have square: "green_X q cparam = ?t * ?t"
    by (rule green_even_exponent_square[OF even])
  have base: "2 * ?t \<le> (?t * ?t) div cparam"
    "2 * (?t * ?t) * ((?t * ?t) div cparam) +
      ((?t * ?t) div cparam) * ((?t * ?t) + ((?t * ?t) div cparam)) <
      ((?t * ?t) div cparam) * ((2 * ?t) * (2 * ?t))"
    by (rule green_square_scale_parameters[OF cparam large]; simp)+
  show "green_N q cparam \<le> green_J q cparam"
    using base(1) by (simp add: green_N_def green_J_def square)
  show "2 * green_X q cparam * green_J q cparam +
      green_J q cparam * (green_X q cparam + green_J q cparam) <
      green_J q cparam * (green_N q cparam * green_N q cparam)"
    using base(2) by (simp add: green_N_def green_J_def square)
qed

lemma (in green_quadratic_character) green_paper_rows_independent:
  assumes even: "even cparam"
    and cparam: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
    and relation:
      "green_row_relation
        (diagonal_grid (cpx_sqrt d) (natural_grid (green_N q cparam)))
        (green_J q cparam) (green_X q cparam) (green_J q cparam) c"
  shows "\<And>k. k \<in> green_row_indices (green_X q cparam) (green_J q cparam)
    \<Longrightarrow> c k = 0"
proof -
  have tpos: "0 < q ^ (cparam div 2)"
    using cparam large by linarith
  have Npos: "0 < green_N q cparam"
    using tpos by (simp add: green_N_def)
  have Jbound: "green_N q cparam \<le> green_J q cparam"
    and dimension: "2 * green_X q cparam * green_J q cparam +
      green_J q cparam * (green_X q cparam + green_J q cparam) <
      green_J q cparam * (green_N q cparam * green_N q cparam)"
    by (rule green_paper_row_parameters[OF even cparam large])+
  fix k
  assume k: "k \<in> green_row_indices (green_X q cparam) (green_J q cparam)"
  show "c k = 0"
    by (rule natural_diagonal_rows_independent[OF Npos Jbound
      lattice_slope_irrational dimension relation k])
qed

end
