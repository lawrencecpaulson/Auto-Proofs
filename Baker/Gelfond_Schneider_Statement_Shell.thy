(*  Title:      Baker/Gelfond_Schneider_Statement_Shell.thy
    Author:     OpenAI Codex

Arithmetic shell for the final standalone Gelfond-Schneider contradiction.
This ports the outer `q`-choice bookkeeping from Lean's `statement` theorem,
leaving only the concrete analytic bounds on the distinguished quantity `rho`
as the remaining gap.
*)

theory Gelfond_Schneider_Statement_Shell
  imports
    Gelfond_Schneider_Preliminaries
    Gelfond_Schneider_System
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


section \<open>Choice of q\<close>

definition gs_q_choice :: "nat \<Rightarrow> real \<Rightarrow> nat"
  where "gs_q_choice h C = 2 * gs_m h * (6 * h * nat (ceiling (C powr 4)))"

lemma one_le_nat_ceiling_powr4:
  fixes C :: real
  assumes C_ge1: "1 \<le> C"
  shows "1 \<le> nat (ceiling (C powr 4))"
  by (metis C_ge1 ceiling_mono ceiling_one ge_one_powr_ge_zero nat_mono nat_one_as_int zero_le_numeral)

lemma gs_q_choice_pos:
  fixes C :: real
  assumes hpos: "h > 0"
  assumes C_ge1: "1 \<le> C"
  shows "gs_q_choice h C > 0"
  unfolding gs_q_choice_def
  using hpos C_ge1 one_le_nat_ceiling_powr4[OF C_ge1]
  by simp

lemma gs_q_choice_ge_four:
  fixes C :: real
  assumes hpos: "h > 0"
  assumes C_ge1: "1 \<le> C"
  shows "4 \<le> gs_q_choice h C"
proof -
  let ?X = "6 * h * nat (ceiling (C powr 4))"
  have Xone: "1 \<le> ?X"
    using hpos one_le_nat_ceiling_powr4[OF C_ge1] by simp
  have mfour: "4 \<le> 2 * gs_m h"
    unfolding gs_m_def by simp
  have mle: "2 * gs_m h \<le> 2 * gs_m h * ?X"
  proof -
    have "2 * gs_m h * 1 \<le> 2 * gs_m h * ?X"
      by (rule mult_left_mono[OF Xone]) simp
    then show ?thesis by simp
  qed
  show ?thesis
    unfolding gs_q_choice_def using mfour mle by linarith
qed

lemma gs_q_choice_dvd:
  fixes C :: real
  shows "2 * gs_m h dvd gs_q_choice h C ^ 2"
  unfolding gs_q_choice_def
  by (simp add: power2_eq_square ac_simps)

lemma square_multiple_div_self:
  fixes a b :: nat
  assumes apos: "a > 0"
  shows "((a * b) ^ 2) div a = a * b ^ 2"
proof -
  have "((a * b) ^ 2) div a = ((a * b) * (a * b)) div a"
    by (simp add: power2_eq_square)
  also have "... = a * (b * b)"
    using apos by (simp add: ac_simps)
  also have "... = a * b ^ 2"
    by (simp add: power2_eq_square)
  finally show ?thesis .
qed

lemma gs_n_q_choice_closed_form:
  fixes C :: real
  shows "gs_n h (gs_q_choice h C) =
    2 * gs_m h * (6 * h * nat (ceiling (C powr 4))) ^ 2"
  unfolding gs_n_def gs_q_choice_def
  by (rule square_multiple_div_self) simp

lemma gs_q_choice_factor_le_n:
  fixes C :: real
  assumes hpos: "h > 0"
  assumes C_ge1: "1 \<le> C"
  shows "6 * h * nat (ceiling (C powr 4)) \<le> gs_n h (gs_q_choice h C)"
proof -
  let ?X = "6 * h * nat (ceiling (C powr 4))"
  have one_le_X: "1 \<le> ?X"
    using hpos one_le_nat_ceiling_powr4[OF C_ge1] by simp
  have X_le_X2: "?X \<le> ?X ^ 2"
  proof -
    have "?X = ?X * 1" by simp
    also have "... \<le> ?X * ?X"
      using one_le_X by (intro mult_left_mono) simp_all
    also have "... = ?X ^ 2"
      by (simp add: power2_eq_square)
    finally show ?thesis .
  qed
  have X2_le: "?X ^ 2 \<le> 2 * gs_m h * ?X ^ 2"
    using one_le_gs_m[of h] by force
  have X_le_n_closed: "?X \<le> 2 * gs_m h * ?X ^ 2"
    by (rule order_trans[OF X_le_X2 X2_le])
  show ?thesis
    using X_le_n_closed by (simp add: gs_n_q_choice_closed_form)
qed

lemma gs_q_choice_six_h_le_n:
  fixes C :: real
  assumes hpos: "h > 0"
  assumes C_ge1: "1 \<le> C"
  shows "6 * h \<le> gs_n h (gs_q_choice h C)"
proof -
  have factor_ge: "6 * h \<le> 6 * h * nat (ceiling (C powr 4))"
    using one_le_nat_ceiling_powr4[OF C_ge1]
    by simp
  also have "... \<le> gs_n h (gs_q_choice h C)"
    by (rule gs_q_choice_factor_le_n[OF hpos C_ge1])
  finally show ?thesis .
qed

lemma gs_q_choice_powr4_le_n:
  fixes C :: real
  assumes hpos: "h > 0"
  assumes C_ge1: "1 \<le> C"
  shows "C powr 4 \<le> of_nat (gs_n h (gs_q_choice h C))"
proof -
  let ?N = "nat (ceiling (C powr 4))"
  let ?X = "6 * h * ?N"
  have pow_nonneg: "0 \<le> C powr 4"
    using C_ge1 by simp
  have ceil_nonneg: "0 \<le> ceiling (C powr 4)"
    using pow_nonneg le_of_int_ceiling[of "C powr 4"] by linarith
  have N_le_X: "?N \<le> ?X"
  proof -
    have "?N = 1 * ?N" by simp
    also have "... \<le> (6 * h) * ?N"
      using hpos by (intro mult_right_mono) simp_all
    finally show ?thesis by simp
  qed
  have X_le_n: "?X \<le> gs_n h (gs_q_choice h C)"
    by (rule gs_q_choice_factor_le_n[OF hpos C_ge1])
  have N_le_n: "?N \<le> gs_n h (gs_q_choice h C)"
    by (rule order_trans[OF N_le_X X_le_n])
  have ceil_le_n_real: "real_of_int (ceiling (C powr 4)) \<le> real (gs_n h (gs_q_choice h C))"
  proof -
    have ceil_le_int_n: "ceiling (C powr 4) \<le> int (gs_n h (gs_q_choice h C))"
    proof -
      have N_eq_int: "int ?N = ceiling (C powr 4)"
        using ceil_nonneg by simp
      have "int ?N \<le> int (gs_n h (gs_q_choice h C))"
        using N_le_n by presburger
      then show ?thesis
        using N_eq_int by simp
    qed
    then show ?thesis by simp
  qed
  have "C powr 4 \<le> real_of_int (ceiling (C powr 4))"
    by (rule le_of_int_ceiling)
  also have "... \<le> real (gs_n h (gs_q_choice h C))"
    by (rule ceil_le_n_real)
  finally show ?thesis .
qed

corollary gs_q_choice_six_h_le_r:
  fixes C :: real
  assumes hpos: "h > 0"
  assumes C_ge1: "1 \<le> C"
  assumes n_le_r: "gs_n h (gs_q_choice h C) \<le> r"
  shows "6 * h \<le> r"
  by (rule order_trans[OF gs_q_choice_six_h_le_n[OF hpos C_ge1] n_le_r])

corollary gs_q_choice_powr4_le_r:
  fixes C :: real
  assumes hpos: "h > 0"
  assumes C_ge1: "1 \<le> C"
  assumes n_le_r: "gs_n h (gs_q_choice h C) \<le> r"
  shows "C powr 4 \<le> of_nat r"
proof -
  have "C powr 4 \<le> of_nat (gs_n h (gs_q_choice h C))"
    by (rule gs_q_choice_powr4_le_n[OF hpos C_ge1])
  also have "... \<le> of_nat r"
    using n_le_r by simp
  finally show ?thesis .
qed

section \<open>Final Growth Shell\<close>

theorem gs_growth_contradiction_with_q_choice:
  fixes c5 c14 rho_norm :: real
  fixes h r :: nat
  assumes hpos: "h > 0"
  assumes n_le_r: "gs_n h (gs_q_choice h (c14 * c5)) \<le> r"
  assumes c14_ge1: "1 \<le> c14"
  assumes c5_ge1: "1 \<le> c5"
  assumes rho_pos: "0 < rho_norm"
  assumes rho_upper:
    "rho_norm \<le>
      c14 powr of_nat r *
      of_nat r powr ((- of_nat r / 2 + 3 * of_nat h / 2) :: real)"
  assumes rho_inv_lt: "inverse rho_norm < c5 powr of_nat r"
  shows False
proof -
  have c15_ge1: "1 \<le> c14 * c5"
  proof -
    have "1 * 1 \<le> c14 * c5"
      using c14_ge1 c5_ge1 by (intro mult_mono) simp_all
    then show ?thesis
      by simp
  qed
  have six_h_le_r: "6 * h \<le> r"
    by (rule gs_q_choice_six_h_le_r[OF hpos c15_ge1 n_le_r])
  have rpos: "0 < r"
  proof -
    have "0 < 6 * h"
      using hpos by simp
    also have "... \<le> r"
      by (rule six_h_le_r)
    finally show ?thesis .
  qed
  have c15_4_le_r: "(c14 * c5) powr 4 \<le> of_nat r"
    by (rule gs_q_choice_powr4_le_r[OF hpos c15_ge1 n_le_r])
  show False
    by (rule gs_growth_contradiction_from_norm_bounds[OF rpos c14_ge1 c5_ge1 rho_pos rho_upper rho_inv_lt six_h_le_r c15_4_le_r])
qed

end
