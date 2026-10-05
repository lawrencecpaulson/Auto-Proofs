(*  Title:      Gelfond_Schneider/Gelfond_Schneider_System.thy
    Author:     OpenAI Codex

Vector-indexed auxiliary-function lemmas for the standalone Gelfond-Schneider
port. This mirrors the Lean layer where the finite exponential sum is viewed
as a function of a `q^2`-tuple of coefficients and its derivatives at the
interpolation nodes are rewritten into the indexed linear-system coefficients.
*)

theory Gelfond_Schneider_System
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

section \<open>Vector-Indexed Auxiliary Functions\<close>

definition gs_aux_fun_vec ::
  "gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> complex"
  where
    "gs_aux_fun_vec d q \<xi> x =
      (\<Sum>t<q * q. \<xi> t * exp (gs_rho_idx d q t * x))"

definition gs_matrix_entry ::
  "gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex"
  where
    "gs_matrix_entry d n q u t =
      of_int (gs_c_coeffs_idx d n q u t) * gs_system_coeff_idx d n q u t"

lemma gs_aux_fun_vec_iterated_deriv:
  "((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) x =
    (\<Sum>t<q * q. \<xi> t * gs_rho_idx d q t ^ k * exp (gs_rho_idx d q t * x))"
  unfolding gs_aux_fun_vec_def
  by (rule iterated_deriv_exp_sum) simp

lemma gs_aux_fun_vec_deriv_at_node:
  assumes d: "is_gelfond_schneider_data d"
  shows "gs_z d powi (- int (gs_k_idx n u)) *
      ((deriv ^^ gs_k_idx n u) (gs_aux_fun_vec d q \<xi>)) (of_nat (gs_l_idx n u)) =
    (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t)"
proof -
  have z_nz: "gs_z d \<noteq> 0"
    by (rule gelfond_schneider_data_z_nonzero[OF d])
  have "gs_z d powi (- int (gs_k_idx n u)) *
      ((deriv ^^ gs_k_idx n u) (gs_aux_fun_vec d q \<xi>)) (of_nat (gs_l_idx n u)) =
      (\<Sum>t<q * q.
        gs_z d powi (- int (gs_k_idx n u)) * (\<xi> t *
        gs_rho_idx d q t ^ gs_k_idx n u *
        exp (gs_rho_idx d q t * of_nat (gs_l_idx n u))))"
    by (simp add: gs_aux_fun_vec_iterated_deriv sum_distrib_left algebra_simps)
  also have "\<dots> = (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t)"
  proof (rule sum.cong[OF refl])
    fix t
    assume "t \<in> {..<q * q}"
    have rho_scale:
        "gs_rho_idx d q t * of_nat (gs_l_idx n u) =
          gs_rho d (gs_a_idx q t * gs_l_idx n u) (gs_b_idx q t * gs_l_idx n u)"
      unfolding gs_rho_idx_def gs_rho_def gs_affine_coeff_def
      by (simp add: algebra_simps)
    have exp_eq:
        "exp (gs_rho_idx d q t * of_nat (gs_l_idx n u)) =
          gs_a d ^ (gs_a_idx q t * gs_l_idx n u) *
          gs_w d ^ (gs_b_idx q t * gs_l_idx n u)"
    proof -
      have "exp (gs_rho_idx d q t * of_nat (gs_l_idx n u)) =
          exp (gs_rho d (gs_a_idx q t * gs_l_idx n u) (gs_b_idx q t * gs_l_idx n u))"
        unfolding rho_scale by simp
      also have "\<dots> =
          gs_a d ^ (gs_a_idx q t * gs_l_idx n u) *
          gs_w d ^ (gs_b_idx q t * gs_l_idx n u)"
        by (rule gelfond_schneider_data_rho_exp[OF d])
      finally show ?thesis .
    qed
    have coeff_eq:
        "gs_z d powi (- int (gs_k_idx n u)) *
          (gs_rho_idx d q t ^ gs_k_idx n u *
            exp (gs_rho_idx d q t * of_nat (gs_l_idx n u))) =
        gs_system_coeff_idx d n q u t"
    proof -
      have "gs_z d powi (- int (gs_k_idx n u)) *
          (gs_rho_idx d q t ^ gs_k_idx n u *
            exp (gs_rho_idx d q t * of_nat (gs_l_idx n u))) =
          (gs_z d powi (- int (gs_k_idx n u)) * gs_rho_idx d q t ^ gs_k_idx n u) *
            exp (gs_rho_idx d q t * of_nat (gs_l_idx n u))"
        by (simp add: algebra_simps)
      also have "\<dots> =
          gs_affine_coeff d (gs_a_idx q t) (gs_b_idx q t) ^ gs_k_idx n u *
            exp (gs_rho_idx d q t * of_nat (gs_l_idx n u))"
      proof -
        have "gs_z d powi (- int (gs_k_idx n u)) * gs_rho_idx d q t ^ gs_k_idx n u =
            gs_z d powi (- int (gs_k_idx n u)) *
              ((gs_affine_coeff d (gs_a_idx q t) (gs_b_idx q t) * gs_z d) ^ gs_k_idx n u)"
          unfolding gs_rho_idx_def gs_rho_def by simp
        also have "\<dots> =
            gs_affine_coeff d (gs_a_idx q t) (gs_b_idx q t) ^ gs_k_idx n u *
              (gs_z d powi (- int (gs_k_idx n u)) * gs_z d ^ gs_k_idx n u)"
          by (simp add: power_mult_distrib algebra_simps)
        also have "\<dots> =
            gs_affine_coeff d (gs_a_idx q t) (gs_b_idx q t) ^ gs_k_idx n u"
          using z_nz by (simp add: power_int_def field_simps)
        finally show ?thesis
          by simp
      qed
      also have "\<dots> = gs_system_coeff_idx d n q u t"
        unfolding gs_system_coeff_idx_def gs_system_coeff_def
        by (simp add: exp_eq)
      finally show ?thesis .
    qed
    show "gs_z d powi (- int (gs_k_idx n u)) *
        (\<xi> t * gs_rho_idx d q t ^ gs_k_idx n u *
          exp (gs_rho_idx d q t * of_nat (gs_l_idx n u))) =
      \<xi> t * gs_system_coeff_idx d n q u t"
      by (simp add: coeff_eq algebra_simps)
  qed
  finally show ?thesis .
qed

corollary gs_aux_fun_vec_deriv_at_node_eq_zeroI:
  assumes d: "is_gelfond_schneider_data d"
  assumes sys0: "(\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
  shows "((deriv ^^ gs_k_idx n u) (gs_aux_fun_vec d q \<xi>)) (of_nat (gs_l_idx n u)) = 0"
proof -
  have z0_nz: "gs_z d \<noteq> 0"
    by (rule gelfond_schneider_data_z_nonzero[OF d])
  have z_nz: "gs_z d powi (- int (gs_k_idx n u)) \<noteq> 0"
    using z0_nz
    by (simp add: power_int_def)
  have "gs_z d powi (- int (gs_k_idx n u)) *
      ((deriv ^^ gs_k_idx n u) (gs_aux_fun_vec d q \<xi>)) (of_nat (gs_l_idx n u)) = 0"
    by (simp add: gs_aux_fun_vec_deriv_at_node[OF d] sys0)
  with z_nz show ?thesis
    by (meson mult_eq_0_iff)
qed

lemma gelfond_schneider_data_rho_idx_inj_on:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  shows "inj_on (gs_rho_idx d q) {..<q * q}"
proof (rule inj_onI)
  fix s t
  assume s: "s \<in> {..<q * q}"
  assume t: "t \<in> {..<q * q}"
  assume eq: "gs_rho_idx d q s = gs_rho_idx d q t"
  have sgrid: "gs_pair_of_idx q s \<in> gs_grid q"
    by (rule gs_pair_of_idx_mem_grid[OF qpos]) (use s in simp)
  have tgrid: "gs_pair_of_idx q t \<in> gs_grid q"
    by (rule gs_pair_of_idx_mem_grid[OF qpos]) (use t in simp)
  have ab_eq:
      "gs_a_idx q s = gs_a_idx q t \<and> gs_b_idx q s = gs_b_idx q t"
  proof (rule gelfond_schneider_data_rho_injective[OF d])
    show "gs_rho d (gs_a_idx q s) (gs_b_idx q s) = gs_rho d (gs_a_idx q t) (gs_b_idx q t)"
      using eq unfolding gs_rho_idx_def .
  qed
  have pair_eq: "gs_pair_of_idx q s = gs_pair_of_idx q t"
    using ab_eq unfolding gs_pair_of_idx_def gs_a_idx_def gs_b_idx_def
    by auto
  have slt: "s < q * q"
    using s by simp
  have tlt: "t < q * q"
    using t by simp
  have "s = gs_idx_of_pair q (gs_pair_of_idx q s)"
    by (rule gs_idx_pair_inverse[OF qpos slt, symmetric])
  also have "\<dots> = gs_idx_of_pair q (gs_pair_of_idx q t)"
    using pair_eq by simp
  also have "\<dots> = t"
    by (rule gs_idx_pair_inverse[OF qpos tlt])
  finally show "s = t" .
qed

lemma gs_aux_fun_vec_eq_zero_imp_coeff_zero:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes zero: "gs_aux_fun_vec d q \<xi> = (\<lambda>_. 0)"
  shows "\<forall>t<q * q. \<xi> t = 0"
proof -
  have coeff0: "\<forall>t\<in>{..<q * q}. \<xi> t = 0"
  proof (rule finite_exp_sum_eq_zero_imp_coeff_zero)
    show "finite {..<q * q}"
      by simp
    show "inj_on (gs_rho_idx d q) {..<q * q}"
      by (rule gelfond_schneider_data_rho_idx_inj_on[OF d qpos])
    show "\<forall>x. (\<Sum>i\<in>{..<q * q}. \<xi> i * exp (gs_rho_idx d q i * x)) = 0"
    proof
      fix x
      have "(gs_aux_fun_vec d q \<xi>) x = (\<lambda>_. 0) x"
        using fun_cong[OF zero, of x] .
      then show "(\<Sum>i\<in>{..<q * q}. \<xi> i * exp (gs_rho_idx d q i * x)) = 0"
        unfolding gs_aux_fun_vec_def by simp
    qed
  qed
  show ?thesis
    using coeff0 by auto
qed

lemma gs_aux_fun_vec_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes nz: "\<exists>t<q * q. \<xi> t \<noteq> 0"
  shows "gs_aux_fun_vec d q \<xi> \<noteq> (\<lambda>_. 0)"
proof
  assume h0: "gs_aux_fun_vec d q \<xi> = (\<lambda>_. 0)"
  have "\<forall>t<q * q. \<xi> t = 0"
    by (rule gs_aux_fun_vec_eq_zero_imp_coeff_zero[OF d qpos h0])
  with nz show False
    by blast
qed

lemma gelfond_schneider_data_matrix_entry_algebraic_int:
  assumes d: "is_gelfond_schneider_data d"
  assumes npos: "n > 0"
  shows "algebraic_int (gs_matrix_entry d n q u t)"
proof -
  have "gs_k_idx n u \<le> n - 1"
    by (rule gs_k_idx_le[OF npos])
  then have "algebraic_int
      (of_int (gs_c_coeffs_idx d n q u t) * gs_system_coeff_idx d n q u t)"
    by (rule gelfond_schneider_data_system_coeff_idx_scaled_algebraic_int[OF d])
  then show ?thesis
    unfolding gs_matrix_entry_def .
qed

end
