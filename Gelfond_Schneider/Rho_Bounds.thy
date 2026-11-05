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
  assumes "h > 0"
  assumes C_ge1: "1 \<le> C"
  assumes nle: "gs_n h (gs_q_choice h C) \<le> r"
  shows "1 < (of_nat (gs_m h) * of_nat r / of_nat (gs_q_choice h C) :: real)"
proof -
  let ?q = "gs_q_choice h C"
  have qge: "4 \<le> ?q"
    by (rule gs_q_choice_ge_four[OF \<open>h > 0\<close> C_ge1])
  have bal: "?q * ?q = 2 * gs_m h * gs_n h ?q"
    using gs_q_sq_eq_two_mn[OF gs_q_choice_dvd[of h C]]
    by (simp add: power2_eq_square)
  show ?thesis
    by (rule gs_circle_clearance_of_balanced_dimensions[OF qge bal nle])
qed

lemma gs_q_choice_le_two_mr:
  fixes C :: real
  assumes "h > 0"
  assumes C_ge1: "1 \<le> C"
  assumes nle: "gs_n h (gs_q_choice h C) \<le> r"
  shows "gs_q_choice h C \<le> 2 * gs_m h * r"
proof -
  let ?q = "gs_q_choice h C"
  have qge: "4 \<le> ?q"
    by (rule gs_q_choice_ge_four[OF \<open>h > 0\<close> C_ge1])
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
  assumes "q > 0"
  assumes mge: "2 \<le> m"
  assumes "r > 0"
  assumes qsq: "q * q \<le> 2 * m * r"
  shows "sqrt (of_nat r) \<le> (of_nat m * of_nat r / of_nat q :: real)"
proof -
  have mm: "2 * m \<le> m * m"
    using mge by (intro mult_right_mono) auto
  have mmr: "2 * m * r \<le> m * m * r"
    by (rule mult_right_mono[OF mm]) simp
  have qsq_le: "q * q \<le> m * m * r"
    using qsq mmr by linarith
  have qsq_real: "real q ^ 2 \<le> (of_nat m) ^ 2 * of_nat r"
  proof -
    have "real(q * q) \<le> of_nat (m * m * r)"
      using qsq_le by (simp only: of_nat_le_iff)
    then show ?thesis by (simp add: power2_eq_square of_nat_mult)
  qed
  have qsqrt: "real q \<le> of_nat m * sqrt (of_nat r)"
  proof -
    have "real q \<le> sqrt ((of_nat m) ^ 2 * of_nat r)"
      by (rule real_le_rsqrt[OF qsq_real])
    then show ?thesis by (simp add: real_sqrt_mult power2_eq_square)
  qed
  have "real q * sqrt (of_nat r) \<le>
      (of_nat m * sqrt (of_nat r)) * sqrt (of_nat r)"
    by (rule mult_right_mono[OF qsqrt]) simp
  then have "real q * sqrt (of_nat r) \<le> of_nat m * of_nat r"
    by (simp add: algebra_simps)
  then show ?thesis using \<open>q > 0\<close> by (simp add: pos_le_divide_eq ac_simps)
qed

lemma gs_balanced_radius_power_ge:
  assumes "q > 0"
  assumes mge: "2 \<le> m"
  assumes "r > 0"
  assumes qsq: "q * q \<le> 2 * m * r"
  shows "of_nat r powr (of_nat m * of_nat r / 2) \<le> (of_nat m * of_nat r / real q) ^ (m * r)"
proof -
  have "sqrt (real r) ^ (m * r) \<le> (real m * real r / real q) ^ (m * r)"
    using gs_balanced_radius_ge_sqrt[OF \<open>q > 0\<close> mge \<open>r > 0\<close> qsq]
    by (simp add: power_mono)
  then show ?thesis
    using \<open>r > 0\<close> by (simp flip: real_sqrt_power powr_realpow powr_half_sqrt_powr)
qed

lemma gs_q_choice_radius_power_ge:
  fixes C :: real
  assumes "h > 0"
  assumes C_ge1: "1 \<le> C"
  assumes nle: "gs_n h (gs_q_choice h C) \<le> r"
  assumes "r > 0"
  shows "r powr (of_nat (gs_m h) * r / 2) \<le>
    (real (gs_m h) * of_nat r / of_nat (gs_q_choice h C)) ^ (gs_m h * r)"
proof -
  let ?q = "gs_q_choice h C"
  have "?q > 0"
    using gs_q_choice_ge_four[OF \<open>h > 0\<close> C_ge1] by simp
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
    by (rule gs_balanced_radius_power_ge[OF \<open>?q > 0\<close> mge \<open>r > 0\<close> qsq])
qed

lemma gs_q_power_le_r_power:
  fixes C :: real
  assumes "m > 0"
  assumes "r > 0"
  assumes nle: "n \<le> r"
  assumes qle: "q \<le> 2 * m * r"
  assumes Cone: "1 \<le> C"
  shows "(of_nat q * C) ^ n \<le> (2 * of_nat m * C) ^ r * real r ^ r"
proof -
  let ?U = "(2 * of_nat m * C) * of_nat r :: real"
  have qle_real: "real q \<le> 2 * of_nat m * of_nat r"
    using qle by (metis of_nat_mult of_nat_le_iff of_nat_numeral)
  have qC: "real q * C \<le> ?U"
    using Cone qle_real by auto
  have Uone: "1 \<le> ?U"
    using assms mult_ge1_I by force
  have "(of_nat q * C) ^ n \<le> ?U ^ n"
    by (rule power_mono[OF qC]) (use Cone in auto)
  also have "\<dots> \<le> (2 * of_nat m * C) ^ r * real r ^ r"
    using Uone nle by (metis pow_mono_exp power_mult_distrib)
  finally show ?thesis .
qed

lemma gs_balanced_q_le_sqrt:
  assumes qsq: "q * q \<le> 2 * m * r"
  shows "real q \<le> sqrt (2 * of_nat m) * sqrt (of_nat r)"
proof -
  have sqr: "real q ^ 2 \<le> (2 * of_nat m) * of_nat r"
    using of_nat_mono [OF qsq] by (simp add: power2_eq_square)
  then show ?thesis
    by (metis real_le_rsqrt real_sqrt_mult)
qed

lemma gs_balanced_q_power_le_r_half:
  fixes C :: real
  assumes "m > 0"
  assumes "r > 0"
  assumes nle: "n \<le> r"
  assumes qsq: "q * q \<le> 2 * m * r"
  assumes Cone: "1 \<le> C"
  shows "(of_nat q * C) ^ n \<le> (sqrt (2 * of_nat m) * C) ^ r * real r powr (of_nat r / 2)"
proof -
  let ?K = "sqrt (2 * of_nat m) * C :: real"
  let ?U = "?K * sqrt (of_nat r)"
  have qC: "real q * C \<le> ?U"
    using Cone gs_balanced_q_le_sqrt qsq by auto
  have Kone: "1 \<le> ?K"
    using \<open>m > 0\<close> Cone by fastforce
  have Uone: "1 \<le> ?U"
    using Kone \<open>r > 0\<close> by auto
  have "(of_nat q * C) ^ n \<le> ?U ^ n"
    by (rule power_mono[OF qC]) (use Cone in auto)
  also have "\<dots> \<le> ?U ^ r"
    by (rule power_increasing[OF nle Uone])
  also have "\<dots> = ?K ^ r * real r powr (of_nat r / 2)"
    by (simp add: \<open>r > 0\<close> power_mult_distrib powr_half_sqrt_powr powr_realpow
        real_sqrt_power)
  finally show ?thesis .
qed

lemma gs_mq_power_le_r_power:
  fixes C :: real
  assumes qle: "q \<le> 2 * m * r"
  assumes Cone: "1 \<le> C"
  shows "C ^ (m * q) \<le> (C ^ (2 * m * m)) ^ r"
  using assms 
  by (metis mult.left_commute mult_le_mono2 power_increasing power_mult)

lemma gs_entry_power_le_r_half:
  fixes C H :: real
  assumes "m > 0"
  assumes "r > 0"
  assumes nle: "n \<le> r"
  assumes qle: "q \<le> 2 * m * r"
  assumes qsq: "q * q \<le> 2 * m * r"
  assumes Cone: "1 \<le> C"
  assumes Hone: "1 \<le> H"
  shows "C ^ n * C ^ (m * q) * C ^ (m * q) *
    (of_nat q * (1 + H)) ^ n * H ^ (m * q) * H ^ (m * q) \<le>
    (C * C ^ (2 * m * m) * C ^ (2 * m * m) *
      (sqrt (2 * of_nat m) * (1 + H)) * H ^ (2 * m * m) * H ^ (2 * m * m)) ^ r *
      real r powr (of_nat r / 2)"
proof -
  let ?k = "2 * m * m"
  have Cn: "C ^ n \<le> C ^ r"
    by (rule power_increasing[OF nle Cone])
  have Cmq: "C ^ (m * q) \<le> (C ^ ?k) ^ r"
    by (rule gs_mq_power_le_r_power[OF qle Cone])
  have Hmq: "H ^ (m * q) \<le> (H ^ ?k) ^ r"
    by (rule gs_mq_power_le_r_power[OF qle Hone])
  have qn: "(of_nat q * (1 + H)) ^ n \<le> (sqrt (2 * of_nat m) * (1 + H)) ^ r * real r powr (of_nat r / 2)"
    using assms gs_balanced_q_power_le_r_half qsq by auto
  have all: "C ^ n * C ^ (m * q) * C ^ (m * q) *
    (of_nat q * (1 + H)) ^ n * H ^ (m * q) * H ^ (m * q) \<le>
    C ^ r * (C ^ ?k) ^ r * (C ^ ?k) ^ r * ((sqrt (2 * of_nat m) * (1 + H)) ^ r *
      real r powr (of_nat r / 2)) * (H ^ ?k) ^ r * (H ^ ?k) ^ r"
    by (intro mult_mono Cn Cmq qn Hmq) (use Cone Hone in auto)
  show ?thesis using all by (simp add: power_mult_distrib ac_simps)
qed

lemma gs_max_ceiling_le:
  fixes x :: real
  assumes "0 \<le> x"
  shows "of_int (max 1 (\<lceil>x\<rceil>)) \<le> 1 + x"
  using assms by linarith

lemma gs_max_ceiling_mul_le:
  fixes A W G :: real
  assumes "0 \<le> A"
  assumes "0 \<le> W"
  assumes Ale: "A \<le> G"
  assumes Gone: "1 \<le> G"
  shows "of_int (max 1 (\<lceil>W * A\<rceil>)) \<le> (1 + W) * G"
proof -
  have WA: "0 \<le> W * A" using \<open>A \<ge> 0\<close> \<open>W \<ge> 0\<close> by simp
  show ?thesis
    using mult_left_mono[OF Ale \<open>W \<ge> 0\<close>] gs_max_ceiling_le[OF WA] Gone by argo
qed

lemma gs_witness_bound_le_growth:
  fixes A W G :: real
  assumes qsq: "q * q \<le> 2 * m * r"
  assumes "0 \<le> A"
  assumes "0 \<le> W"
  assumes Ale: "A \<le> G"
  assumes Gone: "1 \<le> G"
  shows "(of_int (2 * int (q * q * D) * max 1 (\<lceil>W * A\<rceil>)) :: real) \<le>
    (4 * of_nat m * of_nat D * (1 + W)) * of_nat r * G"
proof -
  let ?L = "(of_int (max 1 (\<lceil>W * A\<rceil>)) :: real)"
  have "0 \<le> ?L" by simp
  have Lle: "?L \<le> (1 + W) * G"
    by (rule gs_max_ceiling_mul_le[OF \<open>A \<ge> 0\<close> \<open>W \<ge> 0\<close> Ale Gone])
  have qsq_real: "real(q * q) \<le> 2 * of_nat m * of_nat r"
    using of_nat_mono qsq by fastforce
  then have qfac: "2 * real(q * q) * of_nat D \<le> (4 * of_nat m * of_nat D) * of_nat r"
    by (simp add: algebra_simps mult_left_mono)
  have "of_int (2 * int (q * q * D) * max 1 (\<lceil>W * A\<rceil>)) = (2 * real (q * q) * real D) * ?L"
    by (simp add: of_nat_mult ac_simps)
  also have "\<dots> \<le> ((4 * of_nat m * of_nat D) * of_nat r) * ?L"
    by (rule mult_right_mono[OF qfac \<open>?L \<ge> 0\<close>])
  also have "\<dots> \<le> ((4 * of_nat m * of_nat D) * of_nat r) * ((1 + W) * G)"
    by (rule mult_left_mono[OF Lle]) simp
  also have "\<dots> = (4 * of_nat m * of_nat D * (1 + W)) * of_nat r * G"
    by (simp add: ac_simps)
  finally show ?thesis .
qed

lemma gs_half_growth_product:
  assumes "r > 0"
  shows "real r * of_nat r * (r powr (r / 2)) * (r powr (r / 2)) = r powr (of_nat r + 2)"
  using assms
  by (simp add: power2_eq_square ac_simps powr_mult_base flip: powr_realpow powr_add)

lemma gs_house_growth_multiply:
  fixes B F W K E :: real
  assumes "r > 0"
  assumes qsq: "q * q \<le> 2 * m * r"
  assumes "0 \<le> B"
  assumes "0 \<le> F"
  assumes "0 \<le> W"
  assumes "0 \<le> K"
  assumes "0 \<le> E"
  assumes Bbound: "B \<le> W * of_nat r * K ^ r * r powr (r / 2)"
  assumes Fbound: "F \<le> K ^ r * real r powr (of_nat r / 2)"
  shows "real(q * q) * B * E * F
       \<le> (2 * of_nat m * W * E) * (K * K) ^ r * real r powr (of_nat r + 2)"
proof -
  let ?R = "real r"
  let ?P = "?R powr (?R / 2)"
  have qbound: "real(q * q) \<le> 2 * of_nat m * of_nat r"
    using of_nat_mono qsq by fastforce
  have all: "real(q * q) * B * E * F \<le>
      (2 * of_nat m * ?R) * (W * ?R * K ^ r * ?P) * E * (K ^ r * ?P)"
    using assms by (intro mult_mono qbound Bbound Fbound) auto
  have eq: "(2 * of_nat m * ?R) * (W * ?R * K ^ r * ?P) * E * (K ^ r * ?P) =
            (2 * of_nat m * W * E) * (K * K) ^ r * ?R powr (?R + 2)"
    using gs_half_growth_product[OF \<open>r > 0\<close>]
    by (simp add: power_mult_distrib ac_simps)
  show ?thesis using all by (simp only: eq)
qed

lemma gs_sqrt_nat_le_two_power:
  assumes "r > 0"
  shows "sqrt r \<le> 2 ^ r"
proof -
  have "sqrt r \<le> of_nat r"
    by (simp add: real_le_lsqrt power2_nat_le_imp_le)
  also have "\<dots> \<le> 2 ^ r"
    by simp
  finally show ?thesis .
qed

lemma gs_absorb_sqrt_growth:
  assumes "r > 0"
  shows "r powr (of_nat r + 2) \<le> 2 ^ r * r powr (r + 3 / 2)"
proof -
  have eq: "real r + 2 = (r + 3 / 2) + 1 / 2" by simp
  have "r powr (real r + 2) = (r powr (r + 3 / 2)) * sqrt r"
    by (simp only: eq powr_add powr_half_sqrt)
  also have "\<dots> \<le> (r powr (r + 3 / 2)) * 2 ^ r"
    by (rule mult_left_mono[OF gs_sqrt_nat_le_two_power[OF \<open>r > 0\<close>]]) simp
  also have "\<dots> = 2 ^ r * r powr (r + 3 / 2)"
    by (simp add: ac_simps)
  finally show ?thesis .
qed

lemma gs_house_growth_absorb:
  fixes F K :: real
  assumes "r > 0"
  assumes "0 \<le> F"
  assumes "0 \<le> K"
  shows "F * (K * K) ^ r * r powr (of_nat r + 2) \<le>
    (2 * max 1 F * (K * K)) ^ r * real r powr (r + 3 / 2)"
proof -
  have "F * (K * K) ^ r * r powr (real r + 2) \<le> (max 1 F) ^ r * (K * K) ^ r * r powr (real r + 2)"
    by (simp add: \<open>r > 0\<close> max_def mult_right_mono self_le_power)
  also have "\<dots> \<le> (max 1 F) ^ r * (K * K) ^ r * (2 ^ r * r powr (r + 3 / 2))"
    by (simp add: \<open>r > 0\<close> gs_absorb_sqrt_growth mult_left_mono)
  also have "\<dots> = (2 * max 1 F * (K * K)) ^ r * r powr (r + 3 / 2)"
    by (simp add: power_mult_distrib ac_simps)
  finally show ?thesis .
qed

lemma gs_scale_factor_le_r_power:
  fixes C :: real
  assumes qle: "q \<le> 2 * m * r"
  assumes Cone: "1 \<le> C"
  shows "C ^ r * C ^ (2 * m * q) \<le> (C * C ^ (4 * m * m)) ^ r"
proof -
  have exp_le: "2 * m * q \<le> (4 * m * m) * r"
    using qle by force
  then  have "C ^ r * C ^ (2 * m * q) \<le> C ^ r * C ^ ((4 * m * m) * r)"
    using Cone by (smt (verit) mult_mono one_le_power power_increasing)
  also have "\<dots> = (C * C ^ (4 * m * m)) ^ r"
    by (simp add: power_mult_distrib power_mult)
  finally show ?thesis .
qed

lemma gs_negative_powi_norm:
  assumes znz: "z \<noteq> (0::complex)"
  shows "cmod (z powi (- int r)) = (inverse (cmod z)) ^ r"
  using znz by (simp add: power_int_def norm_power norm_inverse)

lemma gs_point_growth_power_identity:
  assumes "r > 0"
  shows "(real r * of_nat r *
    (of_nat r powr (of_nat r / 2)) * of_nat r ^ r) /
    (of_nat r powr (of_nat m * of_nat r / 2)) =
    of_nat r powr (of_nat r * (3 - of_nat m) / 2 + 2)"
proof -
  let ?R = "real r"
  let ?M = "real m"
  have "(?R * ?R * (?R powr (?R / 2)) * ?R ^ r) / (?R powr (?M * ?R / 2)) =
      ?R powr (2 + ?R / 2 + ?R - ?M * ?R / 2)"
    using \<open>r > 0\<close>
    by (simp only: powr_add powr_diff powr_realpow powr_numeral[OF less_imp_le] power2_eq_square ac_simps)
  also have "(2 + ?R / 2 + ?R - ?M * ?R / 2) = (?R * (3 - ?M) / 2 + 2)"
    by (simp add: field_simps algebra_simps)
  finally show ?thesis .
qed

lemma gs_point_growth_multiply:
  fixes B G W K L radius :: real
  assumes "r > 0"
  assumes qsq: "q * q \<le> 2 * m * r"
  assumes "0 \<le> B"
  assumes "0 \<le> G"
  assumes "0 \<le> W"
  assumes "0 \<le> K"
  assumes "0 \<le> L"
  assumes Bbound: "B \<le> W * of_nat r * K ^ r *
    real r powr (of_nat r / 2)"
  assumes Gbound: "G \<le> L ^ r"
  assumes radius_bound: "real r powr (of_nat m * of_nat r / 2) \<le> radius"
  shows "(real(q * q) * B * fact r * G) / radius \<le>
    (2 * of_nat m * W) * (K * L) ^ r * r powr (r * (3 - of_nat m) / 2 + 2)"
proof -
  let ?P = "r powr (r / 2)"
  let ?D = "r powr (of_nat m * real r / 2)"
  have "0 < ?D" using \<open>r > 0\<close> by simp
  have qbound: "real(q * q) \<le> 2 * of_nat m * real r"
    using qsq by (simp add: mult.assoc flip: of_nat_mult of_nat_le_iff)
  have factbound: "fact r \<le> real r ^ r"
    using fact_le_power[of r] by (simp add: of_nat_power)
  have all: "real(q * q) * B * fact r * G \<le>
      (2 * of_nat m * real r) * (W * r * K ^ r * ?P) * real r ^ r * L ^ r"
    using assms by (intro mult_mono qbound Bbound factbound Gbound) auto
  have "0 \<le> real(q * q) * B * fact r * G"
    using \<open>B \<ge> 0\<close> \<open>G \<ge> 0\<close> by simp
  then have "(real(q * q) * B * fact r * G) / radius \<le> (real(q * q) * B * fact r * G) / ?D"
    using radius_bound frac_le \<open>?D > 0\<close> by blast
  also have "\<dots> \<le> ((2 * of_nat m * real r) * (W * r * K ^ r * ?P) * real r ^ r * L ^ r) / ?D"
    using all divide_le_cancel powr_non_neg by blast
  also have "\<dots> = (2 * of_nat m * W) * (K * L) ^ r *
      r powr (real r * (3 - of_nat m) / 2 + 2)"
    using gs_point_growth_power_identity[of r] \<open>r > 0\<close>
    by (simp add: algebra_simps divide_simps power_mult_distrib)
  finally show ?thesis .
qed

lemma gs_absorb_sqrt_growth_general:
  assumes "r > 0"
  shows "real r powr (a + 2) \<le> 2 ^ r * of_nat r powr (a + 3 / 2)"
proof -
  have eq: "a + 2 = (a + 3 / 2) + 1 / 2" by simp
  have "r powr (a + 2) = (r powr (a + 3 / 2)) * sqrt r"
    by (simp only: eq powr_add powr_half_sqrt)
  also have "\<dots> \<le> (r powr (a + 3 / 2)) * 2 ^ r"
    by (rule mult_left_mono[OF gs_sqrt_nat_le_two_power[OF \<open>r > 0\<close>]]) simp
  also have "\<dots> = 2 ^ r * r powr (a + 3 / 2)"
    by (simp add: ac_simps)
  finally show ?thesis .
qed

lemma gs_point_growth_absorb:
  fixes F K a :: real
  assumes "r > 0"
  assumes "0 \<le> F"
  assumes "K \<ge> 0"
  shows "F * K ^ r * real r powr (a + 2) \<le> (2 * max 1 F * K) ^ r * real r powr (a + 3 / 2)"
proof -
  have "F \<le> (max 1 F) ^ r"
    by (simp add: \<open>r > 0\<close> max_def self_le_power)
  then have "F * K ^ r * r powr (a + 2) \<le> (max 1 F) ^ r * K ^ r * r powr (a + 2)"
    by (simp add: \<open>K \<ge> 0\<close> mult_right_mono)
  also have "\<dots> \<le> (max 1 F) ^ r * K ^ r * (2 ^ r * r powr (a + 3 / 2))"
    using gs_absorb_sqrt_growth_general[OF \<open>r > 0\<close>]
    by (intro mult_left_mono) (use \<open>K \<ge> 0\<close> in simp_all)
  also have "\<dots> = (2 * max 1 F * K) ^ r * r powr (a + 3 / 2)"
    by (simp add: power_mult_distrib ac_simps)
  finally show ?thesis .
qed

lemma gs_aux_exp_growth_le:
  assumes "q > 0"
  assumes qle: "q \<le> 2 * m * r"
  shows "exp ((of_nat q * (1 + cmod b) * cmod z) *
    (of_nat m * (1 + of_nat r / of_nat q))) \<le>
    exp (of_nat m * (2 * of_nat m + 1) * (1 + cmod b) * cmod z) ^ r"
proof -
  let ?L = "(1 + cmod b) * cmod z"
  let ?C = "of_nat m * ?L :: real"
  have qpos_real: "real q > 0" using \<open>q > 0\<close> by simp
  have eq: "(of_nat q * (1 + cmod b) * cmod z) * (of_nat m * (1 + of_nat r / of_nat q)) =
      ?C * (of_nat q + of_nat r)"
    using qpos_real by (simp add: divide_simps)
  have sum_le: "real q + of_nat r \<le> (2 * of_nat m + 1) * of_nat r"
    using of_nat_mono qle by (force simp: algebra_simps)
  then have arg_le: "?C * (of_nat q + of_nat r) \<le> ?C * ((2 * of_nat m + 1) * of_nat r)"
    by (simp add: mult_left_mono)
  have "exp ((of_nat q * (1 + cmod b) * cmod z) * (of_nat m * (1 + of_nat r / of_nat q))) \<le>
      exp (?C * ((2 * of_nat m + 1) * of_nat r))"
    using arg_le by (simp add: eq)
  also have "\<dots> = exp (of_nat m * (2 * of_nat m + 1) * (1 + cmod b) * cmod z) ^ r"
    by (simp add: algebra_simps flip: exp_of_nat2_mult)
  finally show ?thesis .
qed

end
