(*  Title:      Baker/Gelfond_Schneider_Growth.thy
    Author:     OpenAI Codex

Generic real-growth inequalities for the final standalone
Gelfond-Schneider contradiction. This isolates the last monotonicity
step from the Lean `statement` theorem, so that the remaining work can
focus on proving the analytic bound `use5`.
*)

theory Gelfond_Schneider_Growth
  imports Gelfond_Schneider_Preliminaries
begin

section \<open>Generic Growth Contradiction\<close>

lemma gs_exponent_le_four:
  fixes h r :: real
  assumes rpos: "0 < r"
  assumes six_h_le_r: "6 * h <= r"
  shows "(2 * r) / (r - 3 * h) <= 4"
proof -
  have denom_pos: "0 < r - 3 * h"
    using rpos six_h_le_r by linarith
  have aux: "2 * r <= 4 * r - 12 * h"
    using six_h_le_r by linarith
  have div_le: "2 * r / (r - 3 * h) <= (4 * r - 12 * h) / (r - 3 * h)"
    using aux denom_pos by (intro divide_right_mono) auto
  also have "(4 * r - 12 * h) / (r - 3 * h) = 4"
    using denom_pos by (simp add: field_simps)
  finally show ?thesis .
qed

lemma gs_powr_bound:
  fixes C :: real
  fixes h r :: nat
  assumes C_ge1: "1 <= C"
  assumes six_h_le_r: "6 * h <= r"
  assumes C4_le_r: "C powr 4 <= of_nat r"
  shows "C powr of_nat r <= of_nat r powr ((of_nat r - 3 * of_nat h) / 2)"
proof -
  have C4_ge1: "1 <= C powr 4"
    by (rule ge_one_powr_ge_zero[OF C_ge1]) simp
  have r_ge1: "1 <= real r"
    using C4_ge1 C4_le_r by linarith
  have rpos: "0 < real r"
    using r_ge1 by linarith
  have six_real: "6 * real h <= real r"
    using six_h_le_r by simp
  have denom_pos: "0 < real r - 3 * real h"
    using rpos six_real by linarith
  have e_nonneg: "0 <= (real r - 3 * real h) / 2"
    using denom_pos by simp
  have exp_le_four: "(2 * real r) / (real r - 3 * real h) <= 4"
    by (rule gs_exponent_le_four[OF rpos six_real])
  have base_le: "C powr ((2 * real r) / (real r - 3 * real h)) <= real r"
  proof -
    have "C powr ((2 * real r) / (real r - 3 * real h)) <= C powr 4"
      using exp_le_four C_ge1 by (intro powr_mono) auto
    also have "... <= real r"
      by (rule C4_le_r)
    finally show ?thesis .
  qed
  have exp_times_e:
    "((2 * real r) / (real r - 3 * real h)) * ((real r - 3 * real h) / 2) = real r"
    using denom_pos by (simp add: field_simps)
  have step_powr:
    "(C powr ((2 * real r) / (real r - 3 * real h))) powr ((real r - 3 * real h) / 2) <=
      real r powr ((real r - 3 * real h) / 2)"
    using e_nonneg base_le by (intro powr_mono2) auto
  have lhs_eq:
    "(C powr ((2 * real r) / (real r - 3 * real h))) powr ((real r - 3 * real h) / 2) =
      C powr real r"
  proof -
    have "(C powr ((2 * real r) / (real r - 3 * real h))) powr ((real r - 3 * real h) / 2) =
        C powr (((2 * real r) / (real r - 3 * real h)) * ((real r - 3 * real h) / 2))"
      by (rule powr_powr)
    also have "... = C powr real r"
      using exp_times_e by simp
    finally show ?thesis .
  qed
  from step_powr lhs_eq show ?thesis
    by simp
qed

lemma gs_powr_strict_bound:
  fixes C :: real
  fixes h r :: nat
  assumes C_ge1: "1 <= C"
  assumes six_h_le_r: "6 * h <= r"
  assumes C4_lt_r: "C powr 4 < of_nat r"
  shows "C powr of_nat r < of_nat r powr ((of_nat r - 3 * of_nat h) / 2)"
proof -
  have C4_ge1: "1 <= C powr 4"
    by (rule ge_one_powr_ge_zero[OF C_ge1]) simp
  have r_gt1: "1 < real r"
    using C4_ge1 C4_lt_r by linarith
  have rpos: "0 < real r"
    using r_gt1 by linarith
  have six_real: "6 * real h <= real r"
    using six_h_le_r by simp
  have denom_pos: "0 < real r - 3 * real h"
    using rpos six_real by linarith
  have e_pos: "0 < (real r - 3 * real h) / 2"
    using denom_pos by simp
  have exp_le_four: "(2 * real r) / (real r - 3 * real h) <= 4"
    by (rule gs_exponent_le_four[OF rpos six_real])
  have base_lt: "C powr ((2 * real r) / (real r - 3 * real h)) < real r"
  proof -
    have "C powr ((2 * real r) / (real r - 3 * real h)) <= C powr 4"
      using exp_le_four C_ge1 by (intro powr_mono) auto
    also have "... < real r"
      by (rule C4_lt_r)
    finally show ?thesis .
  qed
  have step_powr:
    "(C powr ((2 * real r) / (real r - 3 * real h))) powr ((real r - 3 * real h) / 2) <
      real r powr ((real r - 3 * real h) / 2)"
    using e_pos base_lt by (intro powr_less_mono2) auto
  have exp_times_e:
    "((2 * real r) / (real r - 3 * real h)) * ((real r - 3 * real h) / 2) = real r"
    using denom_pos by (simp add: field_simps)
  have lhs_eq:
    "(C powr ((2 * real r) / (real r - 3 * real h))) powr ((real r - 3 * real h) / 2) =
      C powr real r"
  proof -
    have "(C powr ((2 * real r) / (real r - 3 * real h))) powr ((real r - 3 * real h) / 2) =
        C powr (((2 * real r) / (real r - 3 * real h)) * ((real r - 3 * real h) / 2))"
      by (rule powr_powr)
    also have "... = C powr real r"
      using exp_times_e by simp
    finally show ?thesis .
  qed
  from lhs_eq step_powr show ?thesis
    by simp
qed

lemma gs_growth_contradiction:
  fixes C :: real
  fixes h r :: nat
  assumes C_ge1: "1 <= C"
  assumes six_h_le_r: "6 * h <= r"
  assumes C4_le_r: "C powr 4 <= of_nat r"
  assumes growth: "of_nat r powr ((of_nat r - 3 * of_nat h) / 2) < C powr of_nat r"
  shows False
proof -
  have "C powr of_nat r <= of_nat r powr ((of_nat r - 3 * of_nat h) / 2)"
    by (rule gs_powr_bound[OF C_ge1 six_h_le_r C4_le_r])
  with growth show False
    by linarith
qed

lemma gs_use5_bound:
  fixes c5 c14 rho_norm :: real
  fixes h r :: nat
  assumes rpos: "0 < r"
  assumes c14_ge1: "1 <= c14"
  assumes c5_nonneg: "0 <= c5"
  assumes rho_pos: "0 < rho_norm"
  assumes rho_upper:
    "rho_norm <=
      c14 powr of_nat r *
      of_nat r powr ((- of_nat r / 2 + 3 * of_nat h / 2) :: real)"
  assumes rho_inv_lt: "inverse rho_norm < c5 powr of_nat r"
  shows "of_nat r powr ((((of_nat r :: real) - 3 * of_nat h) / 2)) < (c14 * c5) powr of_nat r"
proof -
  let ?x = "of_nat r powr ((((of_nat r :: real) - 3 * of_nat h) / 2))"
  let ?y = "of_nat r powr (((- of_nat r / 2 + 3 * of_nat h / 2) :: real))"
  have x_nonneg: "0 <= ?x"
    by (intro powr_ge_zero)
  have mult_le: "rho_norm * ?x <= c14 powr of_nat r"
  proof -
    have "rho_norm * ?x <= (c14 powr of_nat r * ?y) * ?x"
      using rho_upper x_nonneg by (intro mult_right_mono) auto
    also have "... = c14 powr of_nat r * (?y * ?x)"
      by (simp add: algebra_simps)
    also have "... = c14 powr of_nat r * (of_nat r powr 0)"
      by (simp add: powr_add[symmetric] field_simps)
    also have "... = c14 powr of_nat r"
      using rpos by simp
    finally show ?thesis .
  qed
  have x_le: "?x <= inverse rho_norm * (c14 powr of_nat r)"
  proof -
    have "?x <= c14 powr of_nat r / rho_norm"
      using mult_le rho_pos by (simp only: pos_le_divide_eq[OF rho_pos] mult.commute)
    also have "... = c14 powr of_nat r * inverse rho_norm"
      by (simp only: divide_inverse)
    also have "... = inverse rho_norm * (c14 powr of_nat r)"
      by (simp add: mult.commute)
    finally show ?thesis .
  qed
  have c14r_pos: "0 < c14 powr of_nat r"
    using c14_ge1 by simp
  have "inverse rho_norm * (c14 powr of_nat r) < c5 powr of_nat r * (c14 powr of_nat r)"
    using rho_inv_lt c14r_pos by (intro mult_strict_right_mono)
  also have "... = (c14 * c5) powr of_nat r"
    by (simp add: powr_mult algebra_simps)
  finally have upper:
    "inverse rho_norm * (c14 powr of_nat r) < (c14 * c5) powr of_nat r" .
  from x_le upper show ?thesis
    by linarith
qed

lemma gs_growth_contradiction_from_norm_bounds:
  fixes c5 c14 rho_norm :: real
  fixes h r :: nat
  assumes rpos: "0 < r"
  assumes c14_ge1: "1 <= c14"
  assumes c5_ge1: "1 <= c5"
  assumes rho_pos: "0 < rho_norm"
  assumes rho_upper:
    "rho_norm <=
      c14 powr of_nat r *
      of_nat r powr ((- of_nat r / 2 + 3 * of_nat h / 2) :: real)"
  assumes rho_inv_lt: "inverse rho_norm < c5 powr of_nat r"
  assumes six_h_le_r: "6 * h <= r"
  assumes c15_4_le_r: "(c14 * c5) powr 4 <= of_nat r"
  shows False
proof -
  have growth: "of_nat r powr ((((of_nat r :: real) - 3 * of_nat h) / 2)) < (c14 * c5) powr of_nat r"
    by (rule gs_use5_bound[OF rpos c14_ge1 _ rho_pos rho_upper rho_inv_lt]) (use c5_ge1 in auto)
  show False
    by (rule gs_growth_contradiction[of "c14 * c5" h r])
       (use c14_ge1 c5_ge1 six_h_le_r c15_4_le_r growth in auto)
qed

end
