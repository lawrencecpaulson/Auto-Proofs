(*  Title:      Baker/Gelfond_Schneider_Quantitative.thy
    Author:     OpenAI Codex

Arithmetic and indexing scaffolding for the quantitative part of the standalone
Gelfond-Schneider port. This mirrors the Lean `m`/`n`/`q` layer and the
finite-product index decoding used to package the linear system behind the
auxiliary function construction.
*)

theory Gelfond_Schneider_Quantitative
  imports Gelfond_Schneider_Auxiliary
begin

section \<open>Quantitative Parameters and Indexing\<close>

definition gs_m :: "nat \<Rightarrow> nat"
  where "gs_m h = 2 * h + 2"

definition gs_n :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "gs_n h q = q ^ 2 div (2 * gs_m h)"

definition gs_pair_of_idx :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat"
  where "gs_pair_of_idx q t = (t div q, t mod q)"

definition gs_idx_of_pair :: "nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat"
  where "gs_idx_of_pair q ab = q * fst ab + snd ab"

definition gs_a_idx :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "gs_a_idx q t = Suc (t div q)"

definition gs_b_idx :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "gs_b_idx q t = Suc (t mod q)"

definition gs_k_idx :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "gs_k_idx n u = u mod n"

definition gs_l_idx :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "gs_l_idx n u = Suc (u div n)"

definition gs_rho_idx :: "gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex"
  where "gs_rho_idx d q t = gs_rho d (gs_a_idx q t) (gs_b_idx q t)"

definition gs_system_coeff_idx ::
  "gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex"
  where
    "gs_system_coeff_idx d n q u t =
      gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) (gs_l_idx n u) (gs_k_idx n u)"

definition gs_c_coeffs_idx ::
  "gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  where
    "gs_c_coeffs_idx d n q u t =
      gs_c_coeffs d n (gs_a_idx q t) (gs_b_idx q t) (gs_l_idx n u)"

lemma one_le_gs_m [simp]: "1 \<le> gs_m h"
  unfolding gs_m_def by simp

lemma gs_m_pos [simp]: "gs_m h > 0"
  unfolding gs_m_def by simp

lemma gs_q_sq_eq_two_mn:
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  shows "q ^ 2 = 2 * gs_m h * gs_n h q"
proof -
  from dvd obtain k where k: "q ^ 2 = (2 * gs_m h) * k"
    by auto
  have "gs_n h q = k"
    unfolding gs_n_def k by simp
  then show ?thesis
    using k by simp
qed

lemma div_lt_of_lt_mult:
  fixes u m n :: nat
  assumes npos: "n > 0"
  assumes ult: "u < m * n"
  shows "u div n < m"
proof (rule ccontr)
  assume "\<not> u div n < m"
  then have m_le: "m \<le> u div n"
    by simp
  have mn_le: "m * n \<le> (u div n) * n"
    using m_le by simp
  also have "\<dots> \<le> u"
    using npos by (simp add: div_mult_mod_eq mult.commute)
  finally show False
    using ult by simp
qed

lemma gs_pair_of_idx_mem_grid:
  assumes qpos: "q > 0"
  assumes tlt: "t < q * q"
  shows "gs_pair_of_idx q t \<in> gs_grid q"
proof -
  have div_lt: "t div q < q"
    by (rule div_lt_of_lt_mult[OF qpos tlt])
  have mod_lt: "t mod q < q"
    using qpos by simp
  show ?thesis
    unfolding gs_pair_of_idx_def gs_grid_def using div_lt mod_lt by auto
qed

lemma gs_idx_of_pair_lt:
  assumes ab: "ab \<in> gs_grid q"
  shows "gs_idx_of_pair q ab < q * q"
proof -
  have a_lt: "fst ab < q" and b_lt: "snd ab < q"
    using ab unfolding gs_grid_def by auto
  have "q * fst ab + snd ab < q * fst ab + q"
    using b_lt by simp
  also have "\<dots> \<le> q * q"
  proof -
    have "q * fst ab + q = q * Suc (fst ab)"
      by simp
    also have "\<dots> \<le> q * q"
    proof -
      have "Suc (fst ab) \<le> q"
        using a_lt by simp
      then have "q * Suc (fst ab) \<le> q * q"
        by (rule mult_left_mono) simp
      then show ?thesis
        by simp
    qed
    finally show ?thesis .
  qed
  finally show ?thesis
    unfolding gs_idx_of_pair_def .
qed

lemma gs_pair_idx_inverse:
  assumes qpos: "q > 0"
  assumes ab: "ab \<in> gs_grid q"
  shows "gs_pair_of_idx q (gs_idx_of_pair q ab) = ab"
proof -
  have a_lt: "fst ab < q" and b_lt: "snd ab < q"
    using ab unfolding gs_grid_def by auto
  have div_eq: "(q * fst ab + snd ab) div q = fst ab"
    using qpos b_lt by (simp add: div_mult2_eq)
  have mod_eq: "(q * fst ab + snd ab) mod q = snd ab"
    using qpos b_lt by simp
  show ?thesis
    unfolding gs_pair_of_idx_def gs_idx_of_pair_def
    using div_eq mod_eq by simp
qed

lemma gs_idx_pair_inverse:
  assumes qpos: "q > 0"
  assumes tlt: "t < q * q"
  shows "gs_idx_of_pair q (gs_pair_of_idx q t) = t"
proof -
  have "t div q < q"
    by (rule div_lt_of_lt_mult[OF qpos tlt])
  then show ?thesis
    unfolding gs_idx_of_pair_def gs_pair_of_idx_def
    using qpos by (simp add: div_mult_mod_eq)
qed

lemma gs_a_idx_le:
  assumes qpos: "q > 0"
  assumes tlt: "t < q * q"
  shows "gs_a_idx q t \<le> q"
  unfolding gs_a_idx_def
  using div_lt_of_lt_mult[OF qpos tlt] by simp

lemma gs_b_idx_le:
  assumes qpos: "q > 0"
  shows "gs_b_idx q t \<le> q"
proof -
  have "t mod q < q"
    using qpos by simp
  then show ?thesis
    unfolding gs_b_idx_def by simp
qed

lemma gs_k_idx_le:
  assumes npos: "n > 0"
  shows "gs_k_idx n u \<le> n - 1"
proof -
  have "u mod n < n"
    using assms by simp
  then show ?thesis
    unfolding gs_k_idx_def by simp
qed

lemma gs_l_idx_le:
  assumes npos: "n > 0"
  assumes ult: "u < m * n"
  shows "gs_l_idx n u \<le> m"
  unfolding gs_l_idx_def
  using div_lt_of_lt_mult[OF npos ult] by simp

lemma gelfond_schneider_data_rho_idx_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes tlt: "t < q * q"
  shows "gs_rho_idx d q t \<noteq> 0"
proof -
  have apos: "gs_a_idx q t > 0"
    unfolding gs_a_idx_def by simp
  have bpos: "gs_b_idx q t > 0"
    unfolding gs_b_idx_def using qpos by simp
  show ?thesis
    unfolding gs_rho_idx_def
    by (rule gelfond_schneider_data_rho_nonzero[OF d]) (use apos bpos in auto)
qed

lemma gelfond_schneider_data_system_coeff_idx_algebraic:
  assumes d: "is_gelfond_schneider_data d"
  shows "algebraic (gs_system_coeff_idx d n q u t)"
  unfolding gs_system_coeff_idx_def
  by (rule gelfond_schneider_data_system_coeff_algebraic[OF d])

lemma gelfond_schneider_data_system_coeff_idx_scaled_algebraic_int:
  assumes d: "is_gelfond_schneider_data d"
  assumes kn: "gs_k_idx n u \<le> n - 1"
  shows "algebraic_int
    (of_int (gs_c_coeffs_idx d n q u t) * gs_system_coeff_idx d n q u t)"
  unfolding gs_c_coeffs_idx_def gs_system_coeff_idx_def
  by (rule gelfond_schneider_data_system_coeff_scaled_algebraic_int[OF d kn])

end
