(*  Title:      Gelfond_Schneider/Rho_Bounds.thy
    Author:     OpenAI Codex

Bridge from the existing row-scaled witness package to the final q-choice growth
contradiction. This isolates the remaining Lean port to proving quantitative
bounds on the distinguished scalar rho.
*)

theory Rho_Bounds
  imports
    Scaled_Bounded
    Statement_Shell
begin

lemma gs_q_choice_circle_clearance:
  fixes C :: real
  assumes hpos: "h > 0"
  assumes C_ge1: "1 \<le> C"
  assumes nle: "gs_n h (gs_q_choice h C) \<le> r"
  shows "1 < (of_nat (gs_m h) * of_nat r / of_nat (gs_q_choice h C) :: real)"
proof -
  let ?q = "gs_q_choice h C"
  have qge: "4 \<le> ?q"
    by (rule gs_q_choice_ge_four[OF hpos C_ge1])
  have bal: "?q * ?q = 2 * gs_m h * gs_n h ?q"
    using gs_q_sq_eq_two_mn[OF gs_q_choice_dvd[of h C]]
    by (simp add: power2_eq_square)
  show ?thesis
    by (rule gs_circle_clearance_of_balanced_dimensions[OF qge bal nle])
qed

lemma gs_q_choice_le_two_mr:
  fixes C :: real
  assumes hpos: "h > 0"
  assumes C_ge1: "1 \<le> C"
  assumes nle: "gs_n h (gs_q_choice h C) \<le> r"
  shows "gs_q_choice h C \<le> 2 * gs_m h * r"
proof -
  let ?q = "gs_q_choice h C"
  have qge: "4 \<le> ?q"
    by (rule gs_q_choice_ge_four[OF hpos C_ge1])
  have bal: "?q * ?q = 2 * gs_m h * gs_n h ?q"
    using gs_q_sq_eq_two_mn[OF gs_q_choice_dvd[of h C]]
    by (simp add: power2_eq_square)
  have qle: "?q \<le> ?q * ?q"
  proof -
    have "?q * 1 \<le> ?q * ?q"
      using qge by (intro mult_left_mono) auto
    then show ?thesis by simp
  qed
  have mle: "2 * gs_m h * gs_n h ?q \<le> 2 * gs_m h * r"
    using nle by (intro mult_left_mono) auto
  show ?thesis using qle mle bal by linarith
qed

lemma gs_balanced_radius_ge_sqrt:
  assumes qpos: "q > 0"
  assumes mge: "2 \<le> m"
  assumes rpos: "r > 0"
  assumes qsq: "q * q \<le> 2 * m * r"
  shows "sqrt (of_nat r) \<le> (of_nat m * of_nat r / of_nat q :: real)"
proof -
  have mm: "2 * m \<le> m * m"
    using mge by (intro mult_right_mono) auto
  have mmr: "2 * m * r \<le> m * m * r"
    by (rule mult_right_mono[OF mm]) simp
  have qsq_le: "q * q \<le> m * m * r"
    using qsq mmr by linarith
  have qsq_real: "(of_nat q :: real) ^ 2 \<le> (of_nat m) ^ 2 * of_nat r"
  proof -
    have "(of_nat (q * q) :: real) \<le> of_nat (m * m * r)"
      using qsq_le by (simp only: of_nat_le_iff)
    then show ?thesis by (simp add: power2_eq_square of_nat_mult)
  qed
  have qsqrt: "(of_nat q :: real) \<le> of_nat m * sqrt (of_nat r)"
  proof -
    have "(of_nat q :: real) \<le> sqrt ((of_nat m) ^ 2 * of_nat r)"
      by (rule real_le_rsqrt[OF qsq_real])
    then show ?thesis by (simp add: real_sqrt_mult power2_eq_square)
  qed
  have "(of_nat q :: real) * sqrt (of_nat r) \<le>
      (of_nat m * sqrt (of_nat r)) * sqrt (of_nat r)"
    by (rule mult_right_mono[OF qsqrt]) simp
  then have "(of_nat q :: real) * sqrt (of_nat r) \<le> of_nat m * of_nat r"
    by (simp add: algebra_simps)
  then show ?thesis using qpos by (simp add: pos_le_divide_eq ac_simps)
qed

lemma gs_balanced_radius_power_ge:
  assumes qpos: "q > 0"
  assumes mge: "2 \<le> m"
  assumes rpos: "r > 0"
  assumes qsq: "q * q \<le> 2 * m * r"
  shows "of_nat r powr (of_nat m * of_nat r / 2) \<le>
    (of_nat m * of_nat r / of_nat q :: real) ^ (m * r)"
proof -
  have rad: "sqrt (of_nat r) \<le> (of_nat m * of_nat r / of_nat q :: real)"
    by (rule gs_balanced_radius_ge_sqrt[OF qpos mge rpos qsq])
  have pw: "sqrt (of_nat r) ^ (m * r) \<le>
      (of_nat m * of_nat r / of_nat q :: real) ^ (m * r)"
    by (rule power_mono[OF rad]) simp
  have eq: "sqrt (of_nat r) ^ (m * r) =
      of_nat r powr (of_nat m * of_nat r / 2)"
  proof -
    have sqrt_pos: "0 < sqrt (of_nat r)" using rpos by simp
    have "sqrt (of_nat r) ^ (m * r) =
        (of_nat r powr (1/2)) powr of_nat (m * r)"
      by (simp only: powr_half_sqrt powr_realpow[OF sqrt_pos])
    also have "... = of_nat r powr (of_nat m * of_nat r / 2)"
      by (simp add: powr_powr of_nat_mult algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis using pw by (simp only: eq)
qed

lemma gs_q_choice_radius_power_ge:
  fixes C :: real
  assumes hpos: "h > 0"
  assumes C_ge1: "1 \<le> C"
  assumes nle: "gs_n h (gs_q_choice h C) \<le> r"
  assumes rpos: "r > 0"
  shows "of_nat r powr (of_nat (gs_m h) * of_nat r / 2) \<le>
    (of_nat (gs_m h) * of_nat r / of_nat (gs_q_choice h C) :: real) ^
      (gs_m h * r)"
proof -
  let ?q = "gs_q_choice h C"
  have qpos: "?q > 0"
    using gs_q_choice_ge_four[OF hpos C_ge1] by simp
  have mge: "2 \<le> gs_m h"
    by (simp add: gs_m_def)
  have bal: "?q * ?q = 2 * gs_m h * gs_n h ?q"
    using gs_q_sq_eq_two_mn[OF gs_q_choice_dvd[of h C]]
    by (simp add: power2_eq_square)
  have nle_mult: "2 * gs_m h * gs_n h ?q \<le> 2 * gs_m h * r"
    by (rule mult_left_mono[OF nle]) simp
  have qsq: "?q * ?q \<le> 2 * gs_m h * r"
    using bal nle_mult by simp
  show ?thesis
    by (rule gs_balanced_radius_power_ge[OF qpos mge rpos qsq])
qed

lemma gs_q_power_le_r_power:
  fixes C :: real
  assumes mpos: "m > 0"
  assumes rpos: "r > 0"
  assumes nle: "n \<le> r"
  assumes qle: "q \<le> 2 * m * r"
  assumes Cone: "1 \<le> C"
  shows "(of_nat q * C) ^ n \<le>
    (2 * of_nat m * C) ^ r * (of_nat r :: real) ^ r"
proof -
  let ?U = "(2 * of_nat m * C) * of_nat r :: real"
  have qle_real: "(of_nat q :: real) \<le> 2 * of_nat m * of_nat r"
  proof -
    have "(of_nat q :: real) \<le> of_nat (2 * m * r)"
      using qle by (simp only: of_nat_le_iff)
    then show ?thesis by (simp add: of_nat_mult)
  qed
  have qC: "(of_nat q :: real) * C \<le> ?U"
  proof -
    have "(of_nat q :: real) * C \<le>
        (2 * of_nat m * of_nat r) * C"
      by (rule mult_right_mono[OF qle_real]) (use Cone in auto)
    then show ?thesis by (simp add: ac_simps)
  qed
  have Uone: "1 \<le> ?U"
  proof -
    have mone: "1 \<le> 2 * (of_nat m :: real)" using mpos by simp
    have rone: "1 \<le> (of_nat r :: real)" using rpos by simp
    have "(1::real) * 1 * 1 \<le> (2 * of_nat m) * C * of_nat r"
      by (intro mult_mono mone Cone rone) (use mpos Cone in auto)
    then show ?thesis by simp
  qed
  have "(of_nat q * C) ^ n \<le> ?U ^ n"
    by (rule power_mono[OF qC]) (use Cone in auto)
  also have "... \<le> ?U ^ r"
    by (rule power_increasing[OF nle Uone])
  also have "... = (2 * of_nat m * C) ^ r * (of_nat r :: real) ^ r"
    by (simp add: power_mult_distrib)
  finally show ?thesis .
qed

lemma gs_balanced_q_le_sqrt:
  assumes qsq: "q * q \<le> 2 * m * r"
  shows "(of_nat q :: real) \<le> sqrt (2 * of_nat m) * sqrt (of_nat r)"
proof -
  have sqr: "(of_nat q :: real) ^ 2 \<le> (2 * of_nat m) * of_nat r"
  proof -
    have "(of_nat (q * q) :: real) \<le> of_nat (2 * m * r)"
      using qsq by (simp only: of_nat_le_iff)
    then show ?thesis by (simp add: power2_eq_square of_nat_mult)
  qed
  have "(of_nat q :: real) \<le> sqrt ((2 * of_nat m) * of_nat r)"
    by (rule real_le_rsqrt[OF sqr])
  then show ?thesis by (simp add: real_sqrt_mult)
qed

lemma gs_balanced_q_power_le_r_half:
  fixes C :: real
  assumes mpos: "m > 0"
  assumes rpos: "r > 0"
  assumes nle: "n \<le> r"
  assumes qsq: "q * q \<le> 2 * m * r"
  assumes Cone: "1 \<le> C"
  shows "(of_nat q * C) ^ n \<le>
    (sqrt (2 * of_nat m) * C) ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
proof -
  let ?K = "sqrt (2 * of_nat m) * C :: real"
  let ?U = "?K * sqrt (of_nat r)"
  have qs: "(of_nat q :: real) \<le> sqrt (2 * of_nat m) * sqrt (of_nat r)"
    by (rule gs_balanced_q_le_sqrt[OF qsq])
  have qC: "(of_nat q :: real) * C \<le> ?U"
  proof -
    have "(of_nat q :: real) * C \<le>
        (sqrt (2 * of_nat m) * sqrt (of_nat r)) * C"
      by (rule mult_right_mono[OF qs]) (use Cone in auto)
    then show ?thesis by (simp add: ac_simps)
  qed
  have Kone: "1 \<le> ?K"
  proof -
    have sqone: "1 \<le> sqrt (2 * (of_nat m :: real))"
      using mpos by simp
    have "(1::real) * 1 \<le> sqrt (2 * of_nat m) * C"
      by (intro mult_mono sqone Cone) auto
    then show ?thesis by simp
  qed
  have Uone: "1 \<le> ?U"
  proof -
    have srone: "1 \<le> sqrt (of_nat r :: real)"
      using rpos by simp
    have "(1::real) * 1 \<le> ?K * sqrt (of_nat r)"
      by (intro mult_mono Kone srone) (use Kone in auto)
    then show ?thesis by simp
  qed
  have "(of_nat q * C) ^ n \<le> ?U ^ n"
    by (rule power_mono[OF qC]) (use Cone in auto)
  also have "... \<le> ?U ^ r"
    by (rule power_increasing[OF nle Uone])
  also have "... = ?K ^ r * (of_nat r :: real) powr (of_nat r / 2)"
  proof -
    have srpos: "0 < sqrt (of_nat r :: real)" using rpos by simp
    have "sqrt (of_nat r :: real) ^ r =
        (of_nat r powr (1/2)) powr of_nat r"
      by (simp only: powr_half_sqrt powr_realpow[OF srpos])
    also have "... = of_nat r powr (of_nat r / 2)"
      by (simp add: powr_powr)
    finally have sr: "sqrt (of_nat r :: real) ^ r =
        of_nat r powr (of_nat r / 2)" .
    show ?thesis by (simp add: power_mult_distrib sr)
  qed
  finally show ?thesis .
qed

lemma gs_mq_power_le_r_power:
  fixes C :: real
  assumes qle: "q \<le> 2 * m * r"
  assumes Cone: "1 \<le> C"
  shows "C ^ (m * q) \<le> (C ^ (2 * m * m)) ^ r"
proof -
  have exp_le: "m * q \<le> (2 * m * m) * r"
  proof -
    have "m * q \<le> m * (2 * m * r)"
      by (rule mult_left_mono[OF qle]) simp
    then show ?thesis by (simp add: ac_simps)
  qed
  have "C ^ (m * q) \<le> C ^ ((2 * m * m) * r)"
    by (rule power_increasing[OF exp_le Cone])
  also have "... = (C ^ (2 * m * m)) ^ r"
    by (simp add: power_mult)
  finally show ?thesis .
qed

lemma gs_entry_power_le_r_power:
  fixes C H :: real
  assumes mpos: "m > 0"
  assumes rpos: "r > 0"
  assumes nle: "n \<le> r"
  assumes qle: "q \<le> 2 * m * r"
  assumes Cone: "1 \<le> C"
  assumes Hone: "1 \<le> H"
  shows "C ^ n * C ^ (m * q) * C ^ (m * q) *
    (of_nat q * (1 + H)) ^ n * H ^ (m * q) * H ^ (m * q) \<le>
    (C * C ^ (2 * m * m) * C ^ (2 * m * m) *
      (2 * of_nat m * (1 + H)) * H ^ (2 * m * m) * H ^ (2 * m * m)) ^ r *
      (of_nat r :: real) ^ r"
proof -
  let ?k = "2 * m * m"
  have Cn: "C ^ n \<le> C ^ r"
    by (rule power_increasing[OF nle Cone])
  have Cmq: "C ^ (m * q) \<le> (C ^ ?k) ^ r"
    by (rule gs_mq_power_le_r_power[OF qle Cone])
  have Hmq: "H ^ (m * q) \<le> (H ^ ?k) ^ r"
    by (rule gs_mq_power_le_r_power[OF qle Hone])
  have qn: "(of_nat q * (1 + H)) ^ n \<le>
      (2 * of_nat m * (1 + H)) ^ r * (of_nat r :: real) ^ r"
    by (rule gs_q_power_le_r_power[OF mpos rpos nle qle]) (use Hone in auto)
  have all: "C ^ n * C ^ (m * q) * C ^ (m * q) *
    (of_nat q * (1 + H)) ^ n * H ^ (m * q) * H ^ (m * q) \<le>
    C ^ r * (C ^ ?k) ^ r * (C ^ ?k) ^ r *
    ((2 * of_nat m * (1 + H)) ^ r * (of_nat r :: real) ^ r) *
    (H ^ ?k) ^ r * (H ^ ?k) ^ r"
    by (intro mult_mono Cn Cmq qn Hmq) (use Cone Hone in auto)
  show ?thesis using all by (simp add: power_mult_distrib ac_simps)
qed

lemma gs_entry_power_le_r_half:
  fixes C H :: real
  assumes mpos: "m > 0"
  assumes rpos: "r > 0"
  assumes nle: "n \<le> r"
  assumes qle: "q \<le> 2 * m * r"
  assumes qsq: "q * q \<le> 2 * m * r"
  assumes Cone: "1 \<le> C"
  assumes Hone: "1 \<le> H"
  shows "C ^ n * C ^ (m * q) * C ^ (m * q) *
    (of_nat q * (1 + H)) ^ n * H ^ (m * q) * H ^ (m * q) \<le>
    (C * C ^ (2 * m * m) * C ^ (2 * m * m) *
      (sqrt (2 * of_nat m) * (1 + H)) * H ^ (2 * m * m) * H ^ (2 * m * m)) ^ r *
      (of_nat r :: real) powr (of_nat r / 2)"
proof -
  let ?k = "2 * m * m"
  have Cn: "C ^ n \<le> C ^ r"
    by (rule power_increasing[OF nle Cone])
  have Cmq: "C ^ (m * q) \<le> (C ^ ?k) ^ r"
    by (rule gs_mq_power_le_r_power[OF qle Cone])
  have Hmq: "H ^ (m * q) \<le> (H ^ ?k) ^ r"
    by (rule gs_mq_power_le_r_power[OF qle Hone])
  have qn: "(of_nat q * (1 + H)) ^ n \<le>
      (sqrt (2 * of_nat m) * (1 + H)) ^ r *
        (of_nat r :: real) powr (of_nat r / 2)"
    by (rule gs_balanced_q_power_le_r_half[OF mpos rpos nle qsq])
      (use Hone in auto)
  have all: "C ^ n * C ^ (m * q) * C ^ (m * q) *
    (of_nat q * (1 + H)) ^ n * H ^ (m * q) * H ^ (m * q) \<le>
    C ^ r * (C ^ ?k) ^ r * (C ^ ?k) ^ r *
    ((sqrt (2 * of_nat m) * (1 + H)) ^ r *
      (of_nat r :: real) powr (of_nat r / 2)) *
    (H ^ ?k) ^ r * (H ^ ?k) ^ r"
    by (intro mult_mono Cn Cmq qn Hmq) (use Cone Hone in auto)
  show ?thesis using all by (simp add: power_mult_distrib ac_simps)
qed

lemma gs_max_ceiling_le:
  fixes x :: real
  assumes xnonneg: "0 \<le> x"
  shows "(of_int (max 1 (ceiling x)) :: real) \<le> 1 + x"
proof -
  have ceil: "(of_int (ceiling x) :: real) \<le> 1 + x"
    using ceiling_correct[of x] by linarith
  show ?thesis using ceil xnonneg by (simp add: max_def)
qed

lemma gs_max_ceiling_mul_le:
  fixes A W G :: real
  assumes Anonneg: "0 \<le> A"
  assumes Wnonneg: "0 \<le> W"
  assumes Ale: "A \<le> G"
  assumes Gone: "1 \<le> G"
  shows "(of_int (max 1 (ceiling (W * A))) :: real) \<le> (1 + W) * G"
proof -
  have WA: "0 \<le> W * A" using Anonneg Wnonneg by simp
  have Wle: "W * A \<le> W * G"
    by (rule mult_left_mono[OF Ale Wnonneg])
  have "(of_int (max 1 (ceiling (W * A))) :: real) \<le> 1 + W * A"
    by (rule gs_max_ceiling_le[OF WA])
  also have "... \<le> G + W * G"
    using Wle Gone by linarith
  also have "... = (1 + W) * G"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma gs_witness_bound_le_growth:
  fixes A W G :: real
  assumes qsq: "q * q \<le> 2 * m * r"
  assumes Anonneg: "0 \<le> A"
  assumes Wnonneg: "0 \<le> W"
  assumes Ale: "A \<le> G"
  assumes Gone: "1 \<le> G"
  shows "(of_int (2 * int (q * q * D) * max 1 (ceiling (W * A))) :: real) \<le>
    (4 * of_nat m * of_nat D * (1 + W)) * of_nat r * G"
proof -
  let ?L = "(of_int (max 1 (ceiling (W * A))) :: real)"
  have Lnonneg: "0 \<le> ?L" by simp
  have Lle: "?L \<le> (1 + W) * G"
    by (rule gs_max_ceiling_mul_le[OF Anonneg Wnonneg Ale Gone])
  have qsq_real: "(of_nat (q * q) :: real) \<le> 2 * of_nat m * of_nat r"
  proof -
    have "(of_nat (q * q) :: real) \<le> of_nat (2 * m * r)"
      using qsq by (simp only: of_nat_le_iff)
    then show ?thesis by (simp add: of_nat_mult)
  qed
  have qfac: "2 * (of_nat (q * q) :: real) * of_nat D \<le>
      (4 * of_nat m * of_nat D) * of_nat r"
  proof -
    have "(2 * (of_nat (q * q) :: real) * of_nat D) \<le>
        (2 * (2 * of_nat m * of_nat r)) * of_nat D"
      by (intro mult_right_mono mult_left_mono qsq_real) simp_all
    then show ?thesis by (simp add: ac_simps)
  qed
  have "(of_int (2 * int (q * q * D) * max 1 (ceiling (W * A))) :: real) =
      (2 * of_nat (q * q) * of_nat D) * ?L"
    by (simp add: of_nat_mult ac_simps)
  also have "... \<le> ((4 * of_nat m * of_nat D) * of_nat r) * ?L"
    by (rule mult_right_mono[OF qfac Lnonneg])
  also have "... \<le> ((4 * of_nat m * of_nat D) * of_nat r) * ((1 + W) * G)"
    by (rule mult_left_mono[OF Lle]) simp
  also have "... = (4 * of_nat m * of_nat D * (1 + W)) * of_nat r * G"
    by (simp add: ac_simps)
  finally show ?thesis .
qed

lemma gs_half_growth_product:
  assumes rpos: "r > 0"
  shows "(of_nat r :: real) * of_nat r *
    (of_nat r powr (of_nat r / 2)) *
    (of_nat r powr (of_nat r / 2)) =
    of_nat r powr (of_nat r + 2)"
proof -
  have rrpos: "(0::real) < of_nat r" using rpos by simp
  have halves: "(of_nat r :: real) powr (of_nat r / 2) *
      (of_nat r powr (of_nat r / 2)) = of_nat r powr of_nat r"
    by (simp only: powr_add[symmetric]) simp
  show ?thesis using halves rrpos
    by (simp add: powr_add powr_realpow power2_eq_square ac_simps)
qed

lemma gs_house_growth_multiply:
  fixes B F W K E :: real
  assumes rpos: "r > 0"
  assumes qsq: "q * q \<le> 2 * m * r"
  assumes Bnonneg: "0 \<le> B"
  assumes Fnonneg: "0 \<le> F"
  assumes Wnonneg: "0 \<le> W"
  assumes Knonneg: "0 \<le> K"
  assumes Enonneg: "0 \<le> E"
  assumes Bbound: "B \<le> W * of_nat r * K ^ r *
    (of_nat r :: real) powr (of_nat r / 2)"
  assumes Fbound: "F \<le> K ^ r *
    (of_nat r :: real) powr (of_nat r / 2)"
  shows "(of_nat (q * q) :: real) * B * E * F \<le>
    (2 * of_nat m * W * E) * (K * K) ^ r *
      (of_nat r :: real) powr (of_nat r + 2)"
proof -
  let ?R = "(of_nat r :: real)"
  let ?P = "?R powr (?R / 2)"
  have qbound: "(of_nat (q * q) :: real) \<le> 2 * of_nat m * of_nat r"
  proof -
    have "(of_nat (q * q) :: real) \<le> of_nat (2 * m * r)"
      using qsq by (simp only: of_nat_le_iff)
    then show ?thesis by (simp add: of_nat_mult)
  qed
  have all: "(of_nat (q * q) :: real) * B * E * F \<le>
      (2 * of_nat m * ?R) * (W * ?R * K ^ r * ?P) * E * (K ^ r * ?P)"
    by (intro mult_mono qbound Bbound Fbound)
      (use Bnonneg Fnonneg Wnonneg Knonneg Enonneg in auto)
  have eq: "(2 * of_nat m * ?R) * (W * ?R * K ^ r * ?P) * E *
      (K ^ r * ?P) =
      (2 * of_nat m * W * E) * (K * K) ^ r *
        ?R powr (?R + 2)"
    using gs_half_growth_product[OF rpos]
    by (simp add: power_mult_distrib ac_simps)
  show ?thesis using all by (simp only: eq)
qed

lemma gs_nat_le_two_power:
  "(of_nat r :: real) \<le> 2 ^ r"
proof (induction r)
  case 0
  then show ?case by simp
next
  case (Suc r)
  have "(of_nat (Suc r) :: real) \<le> 2 ^ r + 1"
    using Suc.IH by simp
  also have "... \<le> 2 ^ r + 2 ^ r"
    by simp
  also have "... = 2 ^ (Suc r)"
    by simp
  finally show ?case .
qed

lemma gs_sqrt_nat_le_two_power:
  assumes rpos: "r > 0"
  shows "sqrt (of_nat r :: real) \<le> 2 ^ r"
proof -
  have rone: "1 \<le> (of_nat r :: real)" using rpos by simp
  have r_sq: "(of_nat r :: real) \<le> (of_nat r) ^ 2"
    by (rule self_le_power[OF rone]) simp
  have "sqrt (of_nat r :: real) \<le> of_nat r"
    by (rule real_le_lsqrt[OF _ r_sq]) simp
  also have "... \<le> 2 ^ r"
    by (rule gs_nat_le_two_power)
  finally show ?thesis .
qed

lemma gs_absorb_sqrt_growth:
  assumes rpos: "r > 0"
  shows "(of_nat r :: real) powr (of_nat r + 2) \<le>
    2 ^ r * of_nat r powr (of_nat r + 3 / 2)"
proof -
  let ?R = "(of_nat r :: real)"
  have eq: "?R + 2 = (?R + 3 / 2) + 1 / 2" by simp
  have "?R powr (?R + 2) =
      (?R powr (?R + 3 / 2)) * sqrt ?R"
    by (simp only: eq powr_add powr_half_sqrt)
  also have "... \<le> (?R powr (?R + 3 / 2)) * 2 ^ r"
    by (rule mult_left_mono[OF gs_sqrt_nat_le_two_power[OF rpos]]) simp
  also have "... = 2 ^ r * ?R powr (?R + 3 / 2)"
    by (simp add: ac_simps)
  finally show ?thesis .
qed

lemma gs_house_growth_absorb:
  fixes F K :: real
  assumes rpos: "r > 0"
  assumes Fnonneg: "0 \<le> F"
  assumes Knonneg: "0 \<le> K"
  shows "F * (K * K) ^ r * (of_nat r :: real) powr (of_nat r + 2) \<le>
    (2 * max 1 F * (K * K)) ^ r *
      (of_nat r :: real) powr (of_nat r + 3 / 2)"
proof -
  let ?R = "(of_nat r :: real)"
  have Fle: "F \<le> (max 1 F) ^ r"
  proof -
    have "F \<le> max 1 F" by simp
    also have "... \<le> (max 1 F) ^ r"
      by (rule self_le_power) (use rpos in auto)
    finally show ?thesis .
  qed
  have nonneg: "0 \<le> (K * K) ^ r * ?R powr (?R + 2)"
    using Knonneg by simp
  have "F * (K * K) ^ r * ?R powr (?R + 2) \<le>
      (max 1 F) ^ r * (K * K) ^ r * ?R powr (?R + 2)"
  proof -
    have "F * ((K * K) ^ r * ?R powr (?R + 2)) \<le>
        (max 1 F) ^ r * ((K * K) ^ r * ?R powr (?R + 2))"
      by (rule mult_right_mono[OF Fle nonneg])
    then show ?thesis by (simp add: ac_simps)
  qed
  also have "... \<le> (max 1 F) ^ r * (K * K) ^ r *
      (2 ^ r * ?R powr (?R + 3 / 2))"
    using gs_absorb_sqrt_growth[OF rpos]
    by (intro mult_left_mono) (use Knonneg in simp_all)
  also have "... = (2 * max 1 F * (K * K)) ^ r *
      ?R powr (?R + 3 / 2)"
    by (simp add: power_mult_distrib ac_simps)
  finally show ?thesis .
qed

lemma gs_scale_factor_le_r_power:
  fixes C :: real
  assumes qle: "q \<le> 2 * m * r"
  assumes Cone: "1 \<le> C"
  shows "C ^ r * C ^ (2 * m * q) \<le>
    (C * C ^ (4 * m * m)) ^ r"
proof -
  have exp_le: "2 * m * q \<le> (4 * m * m) * r"
  proof -
    have "2 * m * q \<le> 2 * m * (2 * m * r)"
      by (rule mult_left_mono[OF qle]) simp
    then show ?thesis by (simp add: ac_simps)
  qed
  have p_le: "C ^ (2 * m * q) \<le> C ^ ((4 * m * m) * r)"
    by (rule power_increasing[OF exp_le Cone])
  have "C ^ r * C ^ (2 * m * q) \<le> C ^ r * C ^ ((4 * m * m) * r)"
    by (rule mult_left_mono[OF p_le]) (use Cone in simp)
  also have "... = (C * C ^ (4 * m * m)) ^ r"
    by (simp add: power_mult_distrib power_mult)
  finally show ?thesis .
qed

lemma gs_negative_powi_norm:
  assumes znz: "z \<noteq> (0::complex)"
  shows "cmod (z powi (- int r)) = (inverse (cmod z)) ^ r"
  using znz by (simp add: power_int_def norm_power norm_inverse)

lemma gs_point_growth_power_identity:
  assumes rpos: "r > 0"
  shows "((of_nat r :: real) * of_nat r *
    (of_nat r powr (of_nat r / 2)) * of_nat r ^ r) /
    (of_nat r powr (of_nat m * of_nat r / 2)) =
    of_nat r powr (of_nat r * (3 - of_nat m) / 2 + 2)"
proof -
  let ?R = "(of_nat r :: real)"
  let ?M = "(of_nat m :: real)"
  have Rpos: "0 < ?R" using rpos by simp
  have exponent: "2 + ?R / 2 + ?R - ?M * ?R / 2 =
      ?R * (3 - ?M) / 2 + 2"
    by (simp add: field_simps algebra_simps)
  have "(?R * ?R * (?R powr (?R / 2)) * ?R ^ r) /
      (?R powr (?M * ?R / 2)) =
      ?R powr (2 + ?R / 2 + ?R - ?M * ?R / 2)"
    by (simp only: powr_add powr_diff powr_realpow[OF Rpos] powr_numeral[OF less_imp_le[OF Rpos]] power2_eq_square ac_simps)
  also have "... = ?R powr (?R * (3 - ?M) / 2 + 2)"
    by (simp only: exponent)
  finally show ?thesis .
qed

lemma gs_point_growth_multiply:
  fixes B G W K L radius :: real
  assumes rpos: "r > 0"
  assumes qsq: "q * q \<le> 2 * m * r"
  assumes Bnonneg: "0 \<le> B"
  assumes Gnonneg: "0 \<le> G"
  assumes Wnonneg: "0 \<le> W"
  assumes Knonneg: "0 \<le> K"
  assumes Lnonneg: "0 \<le> L"
  assumes Bbound: "B \<le> W * of_nat r * K ^ r *
    (of_nat r :: real) powr (of_nat r / 2)"
  assumes Gbound: "G \<le> L ^ r"
  assumes radius_bound: "(of_nat r :: real) powr (of_nat m * of_nat r / 2) \<le> radius"
  shows "((of_nat (q * q) :: real) * B * fact r * G) / radius \<le>
    (2 * of_nat m * W) * (K * L) ^ r *
      (of_nat r :: real) powr (of_nat r * (3 - of_nat m) / 2 + 2)"
proof -
  let ?R = "(of_nat r :: real)"
  let ?P = "?R powr (?R / 2)"
  let ?D = "?R powr (of_nat m * ?R / 2)"
  have Dpos: "0 < ?D" using rpos by simp
  have radius_pos: "0 < radius" using Dpos radius_bound by linarith
  have qbound: "(of_nat (q * q) :: real) \<le> 2 * of_nat m * ?R"
  proof -
    have "(of_nat (q * q) :: real) \<le> of_nat (2 * m * r)"
      using qsq by (simp only: of_nat_le_iff)
    then show ?thesis by (simp add: of_nat_mult)
  qed
  have factbound: "(fact r :: real) \<le> ?R ^ r"
    using fact_le_power[of r] by (simp add: of_nat_power)
  have all: "(of_nat (q * q) :: real) * B * fact r * G \<le>
      (2 * of_nat m * ?R) * (W * ?R * K ^ r * ?P) * ?R ^ r * L ^ r"
    by (intro mult_mono qbound Bbound factbound Gbound)
      (use Bnonneg Gnonneg Wnonneg Knonneg Lnonneg in auto)
  have Nnonneg: "0 \<le> (of_nat (q * q) :: real) * B * fact r * G"
    using Bnonneg Gnonneg by simp
  have "((of_nat (q * q) :: real) * B * fact r * G) / radius \<le>
      ((of_nat (q * q) :: real) * B * fact r * G) / ?D"
    by (rule divide_left_mono[OF radius_bound Nnonneg])
      (use radius_pos Dpos in auto)
  also have "... \<le>
      ((2 * of_nat m * ?R) * (W * ?R * K ^ r * ?P) * ?R ^ r * L ^ r) / ?D"
    by (rule divide_right_mono[OF all]) (use Dpos in auto)
  also have "... = (2 * of_nat m * W) * (K * L) ^ r *
      ?R powr (?R * (3 - of_nat m) / 2 + 2)"
  proof -
    have factor: "((2 * of_nat m * ?R) * (W * ?R * K ^ r * ?P) *
      ?R ^ r * L ^ r) / ?D =
      (2 * of_nat m * W) * (K * L) ^ r *
        ((?R * ?R * ?P * ?R ^ r) / ?D)"
      by (simp add: power_mult_distrib ac_simps)
    have id: "(?R * ?R * ?P * ?R ^ r) / ?D =
        ?R powr (?R * (3 - of_nat m) / 2 + 2)"
      by (rule gs_point_growth_power_identity[OF rpos])
    show ?thesis by (simp only: factor id)
  qed
  finally show ?thesis .
qed

lemma gs_absorb_sqrt_growth_general:
  fixes a :: real
  assumes rpos: "r > 0"
  shows "(of_nat r :: real) powr (a + 2) \<le>
    2 ^ r * of_nat r powr (a + 3 / 2)"
proof -
  let ?R = "(of_nat r :: real)"
  have eq: "a + 2 = (a + 3 / 2) + 1 / 2" by simp
  have "?R powr (a + 2) =
      (?R powr (a + 3 / 2)) * sqrt ?R"
    by (simp only: eq powr_add powr_half_sqrt)
  also have "... \<le> (?R powr (a + 3 / 2)) * 2 ^ r"
    by (rule mult_left_mono[OF gs_sqrt_nat_le_two_power[OF rpos]]) simp
  also have "... = 2 ^ r * ?R powr (a + 3 / 2)"
    by (simp add: ac_simps)
  finally show ?thesis .
qed

lemma gs_point_growth_absorb:
  fixes F K a :: real
  assumes rpos: "r > 0"
  assumes Fnonneg: "0 \<le> F"
  assumes Knonneg: "0 \<le> K"
  shows "F * K ^ r * (of_nat r :: real) powr (a + 2) \<le>
    (2 * max 1 F * K) ^ r *
      (of_nat r :: real) powr (a + 3 / 2)"
proof -
  let ?R = "(of_nat r :: real)"
  have Fle: "F \<le> (max 1 F) ^ r"
  proof -
    have "F \<le> max 1 F" by simp
    also have "... \<le> (max 1 F) ^ r"
      by (rule self_le_power) (use rpos in auto)
    finally show ?thesis .
  qed
  have factor_nonneg: "0 \<le> K ^ r * ?R powr (a + 2)"
    using Knonneg by simp
  have "F * K ^ r * ?R powr (a + 2) \<le>
      (max 1 F) ^ r * K ^ r * ?R powr (a + 2)"
  proof -
    have "F * (K ^ r * ?R powr (a + 2)) \<le>
        (max 1 F) ^ r * (K ^ r * ?R powr (a + 2))"
      by (rule mult_right_mono[OF Fle factor_nonneg])
    then show ?thesis by (simp add: ac_simps)
  qed
  also have "... \<le> (max 1 F) ^ r * K ^ r *
      (2 ^ r * ?R powr (a + 3 / 2))"
    using gs_absorb_sqrt_growth_general[OF rpos, of a]
    by (intro mult_left_mono) (use Knonneg in simp_all)
  also have "... = (2 * max 1 F * K) ^ r *
      ?R powr (a + 3 / 2)"
    by (simp add: power_mult_distrib ac_simps)
  finally show ?thesis .
qed

lemma gs_aux_exp_growth_le:
  assumes qpos: "q > 0"
  assumes qle: "q \<le> 2 * m * r"
  shows "exp ((of_nat q * (1 + cmod b) * cmod z) *
    (of_nat m * (1 + of_nat r / of_nat q))) \<le>
    exp (of_nat m * (2 * of_nat m + 1) * (1 + cmod b) * cmod z) ^ r"
proof -
  let ?L = "(1 + cmod b) * cmod z"
  let ?C = "of_nat m * ?L :: real"
  have qpos_real: "(of_nat q :: real) > 0" using qpos by simp
  have qeq: "(of_nat q :: real) * (1 + of_nat r / of_nat q) =
      of_nat q + of_nat r"
    using qpos_real by (simp add: field_simps)
  have eq: "(of_nat q * (1 + cmod b) * cmod z) *
      (of_nat m * (1 + of_nat r / of_nat q)) =
      ?C * (of_nat q + of_nat r)"
  proof -
    have "(of_nat q * (1 + cmod b) * cmod z) *
      (of_nat m * (1 + of_nat r / of_nat q)) =
      ?C * ((of_nat q :: real) * (1 + of_nat r / of_nat q))"
      by (simp only: ac_simps)
    also have "... = ?C * (of_nat q + of_nat r)"
      by (simp only: qeq)
    finally show ?thesis .
  qed
  have qle_real: "(of_nat q :: real) \<le> 2 * of_nat m * of_nat r"
  proof -
    have "(of_nat q :: real) \<le> of_nat (2 * m * r)"
      using qle by (simp only: of_nat_le_iff)
    then show ?thesis by (simp add: of_nat_mult)
  qed
  have sum_le: "(of_nat q :: real) + of_nat r \<le>
      (2 * of_nat m + 1) * of_nat r"
    using qle_real by (simp add: algebra_simps)
  have Cnonneg: "0 \<le> ?C" by simp
  have arg_le: "?C * (of_nat q + of_nat r) \<le>
      ?C * ((2 * of_nat m + 1) * of_nat r)"
    by (rule mult_left_mono[OF sum_le Cnonneg])
  have "exp ((of_nat q * (1 + cmod b) * cmod z) *
    (of_nat m * (1 + of_nat r / of_nat q))) \<le>
      exp (?C * ((2 * of_nat m + 1) * of_nat r))"
    using arg_le by (simp add: eq)
  also have "... = exp (of_nat m * (2 * of_nat m + 1) * (1 + cmod b) * cmod z) ^ r"
  proof -
    have arg_eq: "?C * ((2 * of_nat m + 1) * of_nat r) =
      (of_nat m * (2 * of_nat m + 1) * (1 + cmod b) * cmod z) * of_nat r"
      by (simp add: algebra_simps)
    show ?thesis by (simp only: arg_eq exp_of_nat2_mult)
  qed
  finally show ?thesis .
qed

end
