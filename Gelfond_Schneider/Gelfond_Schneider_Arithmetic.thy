(*  Title:      Gelfond_Schneider/Gelfond_Schneider_Arithmetic.thy
    Author:     OpenAI Codex

Arithmetic lower-bound infrastructure for the standalone Gelfond-Schneider
port. This packages the first nonvanishing derivative into a scaled algebraic
integer, matching the algebraic half of the direct contradiction argument.
*)

theory Gelfond_Schneider_Arithmetic
  imports
    Gelfond_Schneider_Direct
    Gelfond_Schneider_House
begin

section \<open>Scaled Derivative Values\<close>

lemma gs_aux_fun_vec_deriv_at_nat:
  assumes d: "is_gelfond_schneider_data d"
  shows "gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l) =
    (\<Sum>t<q * q. \<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)"
proof -
  have z_nz: "gs_z d \<noteq> 0"
    by (rule gelfond_schneider_data_z_nonzero[OF d])
  have "gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l) =
      (\<Sum>t<q * q.
        gs_z d powi (- int k) * (\<xi> t * gs_rho_idx d q t ^ k *
          exp (gs_rho_idx d q t * of_nat l)))"
    by (simp add: gs_aux_fun_vec_iterated_deriv sum_distrib_left algebra_simps)
  also have "\<dots> = (\<Sum>t<q * q. \<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)"
  proof (rule sum.cong[OF refl])
    fix t
    assume tmem: "t \<in> {..<q * q}"
    have exp_eq:
        "exp (gs_rho_idx d q t * of_nat l) =
          gs_a d ^ (gs_a_idx q t * l) * gs_w d ^ (gs_b_idx q t * l)"
    proof -
      have "exp (gs_rho_idx d q t * of_nat l) =
          exp (gs_rho d (gs_a_idx q t * l) (gs_b_idx q t * l))"
        unfolding gs_rho_idx_def gs_rho_def gs_affine_coeff_def
        by (simp add: algebra_simps)
      also have "\<dots> = gs_a d ^ (gs_a_idx q t * l) * gs_w d ^ (gs_b_idx q t * l)"
        by (rule gelfond_schneider_data_rho_exp[OF d])
      finally show ?thesis .
    qed
    have coeff_eq:
        "gs_z d powi (- int k) *
          (gs_rho_idx d q t ^ k * exp (gs_rho_idx d q t * of_nat l)) =
          gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k"
    proof -
      have "gs_z d powi (- int k) *
          (gs_rho_idx d q t ^ k * exp (gs_rho_idx d q t * of_nat l)) =
          (gs_z d powi (- int k) * gs_rho_idx d q t ^ k) * exp (gs_rho_idx d q t * of_nat l)"
        by (simp add: algebra_simps)
      also have "\<dots> =
          gs_affine_coeff d (gs_a_idx q t) (gs_b_idx q t) ^ k *
          exp (gs_rho_idx d q t * of_nat l)"
      proof -
        have "gs_z d powi (- int k) * gs_rho_idx d q t ^ k =
            gs_z d powi (- int k) *
              ((gs_affine_coeff d (gs_a_idx q t) (gs_b_idx q t) * gs_z d) ^ k)"
          unfolding gs_rho_idx_def gs_rho_def by simp
        also have "\<dots> =
            gs_affine_coeff d (gs_a_idx q t) (gs_b_idx q t) ^ k *
              (gs_z d powi (- int k) * gs_z d ^ k)"
          by (simp add: algebra_simps)
        also have "\<dots> = gs_affine_coeff d (gs_a_idx q t) (gs_b_idx q t) ^ k"
          using z_nz by (simp add: power_int_def field_simps)
        finally show ?thesis
          by simp
      qed
      also have "\<dots> = gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k"
        unfolding gs_system_coeff_def
        by (simp add: exp_eq)
      finally show ?thesis .
    qed
    have "gs_z d powi (- int k) * (\<xi> t * gs_rho_idx d q t ^ k * exp (gs_rho_idx d q t * of_nat l)) =
        \<xi> t * (gs_z d powi (- int k) * (gs_rho_idx d q t ^ k * exp (gs_rho_idx d q t * of_nat l)))"
      by (simp add: algebra_simps)
    also have "\<dots> = \<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k"
      by (simp add: coeff_eq)
    finally show "gs_z d powi (- int k) * (\<xi> t * gs_rho_idx d q t ^ k * exp (gs_rho_idx d q t * of_nat l)) =
      \<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k" .
  qed
  finally show ?thesis .
qed

lemma gelfond_schneider_data_system_coeff_scaled_uniform_algebraic_int:
  assumes d: "is_gelfond_schneider_data d"
  assumes aq: "a \<le> q"
  assumes bq: "b \<le> q"
  assumes lm: "l \<le> m"
  shows "algebraic_int
    (of_int (gs_c1 d ^ k * gs_c1 d ^ (m * q) * gs_c1 d ^ (m * q)) * gs_system_coeff d a b l k)"
proof -
  have h1: "algebraic_int (of_int (gs_c1 d ^ k) * gs_affine_coeff d a b ^ k)"
    by (rule gelfond_schneider_data_c1_affine_power_algebraic_int[OF d]) simp
  have al: "a * l \<le> m * q"
  proof -
    have "a * l \<le> q * l"
      using aq by simp
    also have "\<dots> \<le> q * m"
      using lm by simp
    finally show ?thesis
      by (simp add: mult.commute)
  qed
  have bl: "b * l \<le> m * q"
  proof -
    have "b * l \<le> q * l"
      using bq by simp
    also have "\<dots> \<le> q * m"
      using lm by simp
    finally show ?thesis
      by (simp add: mult.commute)
  qed
  have h2: "algebraic_int (of_int (gs_c1 d ^ (m * q)) * gs_a d ^ (a * l))"
    by (rule gelfond_schneider_data_c1_a_power_bound_algebraic_int[OF d al])
  have h3: "algebraic_int (of_int (gs_c1 d ^ (m * q)) * gs_w d ^ (b * l))"
    by (rule gelfond_schneider_data_c1_w_power_bound_algebraic_int[OF d bl])
  have "algebraic_int
      ((of_int (gs_c1 d ^ k) * gs_affine_coeff d a b ^ k) *
       (of_int (gs_c1 d ^ (m * q)) * gs_a d ^ (a * l)) *
       (of_int (gs_c1 d ^ (m * q)) * gs_w d ^ (b * l)))"
    by (intro algebraic_int_times h1 h2 h3)
  then show ?thesis
    unfolding gs_system_coeff_def
    by (simp add: algebra_simps)
qed

lemma gs_scaled_deriv_at_nat_algebraic_int:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes coeff_int: "\<forall>t<q * q. algebraic_int (\<xi> t)"
  assumes lm: "l \<le> m"
  shows "algebraic_int
    (of_int (gs_c1 d ^ k * gs_c1 d ^ (m * q) * gs_c1 d ^ (m * q)) *
      (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l)))"
proof -
  define c :: int where "c = gs_c1 d ^ k * gs_c1 d ^ (m * q) * gs_c1 d ^ (m * q)"
  have sum_int: "algebraic_int
      (\<Sum>t<q * q. of_int c * (\<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k))"
  proof (rule algebraic_int_sum)
    fix t
    assume tmem: "t \<in> {..<q * q}"
    hence tlt: "t < q * q"
      by simp
    have xi_int: "algebraic_int (\<xi> t)"
      using coeff_int tlt by blast
    have aq: "gs_a_idx q t \<le> q"
      by (rule gs_a_idx_le[OF qpos tlt])
    have bq: "gs_b_idx q t \<le> q"
      by (rule gs_b_idx_le[OF qpos])
    have coeff_term_int:
        "algebraic_int
          (of_int c * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)"
      unfolding c_def
      by (rule gelfond_schneider_data_system_coeff_scaled_uniform_algebraic_int[OF d aq bq lm])
    have "algebraic_int (\<xi> t *
        (of_int c * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k))"
      by (rule algebraic_int_times[OF xi_int coeff_term_int])
    then show "algebraic_int (of_int c * (\<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k))"
      by (simp add: algebra_simps)
  qed
  also have "(\<Sum>t<q * q. of_int c * (\<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)) =
      of_int c * (\<Sum>t<q * q. \<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)"
    by (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> = of_int c *
      (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l))"
    by (simp add: gs_aux_fun_vec_deriv_at_nat[OF d] algebra_simps)
  finally show ?thesis
    unfolding c_def by simp
qed

corollary gs_scaled_min_deriv_algebraic_int:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes mpos: "m > 0"
  assumes coeff_int: "\<forall>t<q * q. algebraic_int (\<xi> t)"
  assumes coeff_nz: "\<exists>t<q * q. \<xi> t \<noteq> 0"
  shows "algebraic_int
    (of_int (gs_c1 d ^ nat (gs_min_order m d q \<xi>) * gs_c1 d ^ (2 * m * q)) *
      (gs_z d powi (- int (nat (gs_min_order m d q \<xi>))) *
        ((deriv ^^ nat (gs_min_order m d q \<xi>)) (gs_aux_fun_vec d q \<xi>))
          (gs_min_order_node m d q \<xi>)))"
proof -
  have nz: "gs_aux_fun_vec d q \<xi> \<noteq> (\<lambda>_. 0)"
    by (rule gs_aux_fun_vec_nonzero[OF d qpos coeff_nz])
  have ord_nonneg: "0 \<le> gs_min_order m d q \<xi>"
  proof -
    have "zorder (gs_aux_fun_vec d q \<xi>) (gs_min_order_node m d q \<xi>) \<ge> (0::nat)"
      by (rule holomorphic_nonzero_zorder_ge[OF gs_aux_fun_vec_holomorphic[of d q \<xi> UNIV] nz, of 0 "gs_min_order_node m d q \<xi>"])
         simp
    then show ?thesis
      unfolding gs_min_order_def by simp
  qed
  obtain l where llt: "l < m" and node: "gs_min_order_node m d q \<xi> = of_nat (Suc l)"
    by (rule gs_min_order_node_eq_nat[OF mpos])
  have l_le_m: "Suc l \<le> m"
    using llt by simp
  have scaled_nat_int:
      "algebraic_int
        (of_int (gs_c1 d ^ nat (gs_min_order m d q \<xi>) * gs_c1 d ^ (m * q) * gs_c1 d ^ (m * q)) *
          (gs_z d powi (- int (nat (gs_min_order m d q \<xi>))) *
            ((deriv ^^ nat (gs_min_order m d q \<xi>)) (gs_aux_fun_vec d q \<xi>)) (of_nat (Suc l))))"
    by (rule gs_scaled_deriv_at_nat_algebraic_int[OF d qpos coeff_int l_le_m])
  have coeff_scale_eq:
      "gs_c1 d ^ nat (gs_min_order m d q \<xi>) * gs_c1 d ^ (m * q) * gs_c1 d ^ (m * q) =
        gs_c1 d ^ nat (gs_min_order m d q \<xi>) * gs_c1 d ^ (2 * m * q)"
  proof -
    have bb_eq: "m * q + m * q = 2 * m * q"
      by simp
    have "gs_c1 d ^ nat (gs_min_order m d q \<xi>) * gs_c1 d ^ (m * q) * gs_c1 d ^ (m * q) =
        gs_c1 d ^ nat (gs_min_order m d q \<xi>) * (gs_c1 d ^ (m * q) * gs_c1 d ^ (m * q))"
      by (simp add: mult.assoc)
    also have "... = gs_c1 d ^ nat (gs_min_order m d q \<xi>) * gs_c1 d ^ (m * q + m * q)"
      by (simp add: power_add [symmetric])
    also have "... = gs_c1 d ^ nat (gs_min_order m d q \<xi>) * gs_c1 d ^ (2 * m * q)"
      by (simp add: bb_eq)
    finally show ?thesis .
  qed
  have scaled_node_int:
      "algebraic_int
        (of_int (gs_c1 d ^ nat (gs_min_order m d q \<xi>) * gs_c1 d ^ (2 * m * q)) *
          (gs_z d powi (- int (nat (gs_min_order m d q \<xi>))) *
            ((deriv ^^ nat (gs_min_order m d q \<xi>)) (gs_aux_fun_vec d q \<xi>)) (of_nat (Suc l))))"
    using scaled_nat_int by (simp add: coeff_scale_eq)
  show ?thesis
    using scaled_node_int node by simp
qed

lemma gs_scaled_rho_algebraic_int_nonzero:
  fixes v :: "complex vec"
  fixes rho :: complex
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes mpos: "m > 0"
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
  assumes r_eq: "r = nat (gs_min_order m d q (\<lambda>t. Matrix.vec_index v t))"
  assumes deriv_nz:
    "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
      (gs_min_order_node m d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
  assumes c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * m * q)"
  assumes rho_def:
    "rho = (of_int c :: complex) *
      (gs_z d powi (- int r) *
        ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
          (gs_min_order_node m d q (\<lambda>t. Matrix.vec_index v t)))"
  shows "algebraic_int rho" and "rho \<noteq> 0"
proof -
  have coeff_nz: "\<exists>t<q * q. Matrix.vec_index v t \<noteq> 0"
    using v_carrier v_nz by force
  have rho_int0:
    "algebraic_int
      ((of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node m d q (\<lambda>t. Matrix.vec_index v t))))"
  proof -
    have "algebraic_int
      (of_int (gs_c1 d ^ nat (gs_min_order m d q (\<lambda>t. Matrix.vec_index v t)) *
               gs_c1 d ^ (2 * m * q)) *
        (gs_z d powi (- int (nat (gs_min_order m d q (\<lambda>t. Matrix.vec_index v t)))) *
          ((deriv ^^ nat (gs_min_order m d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node m d q (\<lambda>t. Matrix.vec_index v t))))"
      by (rule gs_scaled_min_deriv_algebraic_int[OF d qpos mpos vint coeff_nz])
    then show ?thesis
      unfolding c_def using r_eq by simp
  qed
  have c_nz: "c \<noteq> 0"
    unfolding c_def using gelfond_schneider_data_c1_nonzero[OF d] by auto
  have zfac_nz: "gs_z d powi (- int r) \<noteq> 0"
    using gelfond_schneider_data_z_nonzero[OF d] by (simp add: power_int_def)
  have rho_core_nz:
    "gs_z d powi (- int r) *
      ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node m d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
    using zfac_nz deriv_nz by simp
  have rho_nz0:
    "(of_int c :: complex) *
      (gs_z d powi (- int r) *
        ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
          (gs_min_order_node m d q (\<lambda>t. Matrix.vec_index v t))) \<noteq> 0"
    using c_nz rho_core_nz by auto
  show "algebraic_int rho"
    using rho_int0 rho_def by simp
  show "rho \<noteq> 0"
    using rho_nz0 rho_def by simp
qed

theorem gs_exists_scaled_nonzero_algebraic_int_min_deriv:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  obtains v :: "complex vec" and r and c where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
    and "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
    and "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
    and "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    and "c \<noteq> 0"
    and "algebraic_int
          ((of_int c :: complex) *
            (gs_z d powi (- int r) *
              ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
                (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))))"
    and "(of_int c :: complex) *
          (gs_z d powi (- int r) *
            ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
              (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<noteq> 0"
proof -
  obtain v :: "complex vec" and r where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and v_ker: "gs_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
    and min_ord: "gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t) \<ge> gs_n h q"
    and r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
    and deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
    by (rule gs_exists_integral_auxiliary_data[OF d qpos npos dvd])
  define c :: int where "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
  have c_nz: "c \<noteq> 0"
    unfolding c_def using gelfond_schneider_data_c1_nonzero[OF d] by auto
  have rho_int:
      "algebraic_int
        ((of_int c :: complex) *
          (gs_z d powi (- int r) *
            ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
              (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))))"
    using gs_scaled_rho_algebraic_int_nonzero(1)[OF d qpos gs_m_pos v_carrier v_nz vint r_eq deriv_nz c_def]
    by simp
  have scaled_nz:
      "(of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<noteq> 0"
    using gs_scaled_rho_algebraic_int_nonzero(2)[OF d qpos gs_m_pos v_carrier v_nz vint r_eq deriv_nz c_def]
    by simp
  show thesis
    by (rule that[OF v_carrier v_nz v_ker vint r_eq deriv_nz])
       (use c_def c_nz rho_int scaled_nz in auto)
qed



theorem gs_exists_scaled_nonzero_algebraic_int_house_lower_bound:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  obtains v :: "complex vec" and r and c and rho :: complex where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
    and "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
    and "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
    and "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    and "rho = (of_int c :: complex) *
          (gs_z d powi (- int r) *
            ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
              (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
    and "algebraic_int rho"
    and "rho \<noteq> 0"
    and "1 \<le> cmod rho * gs_house rho ^
          (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
proof -
  obtain v :: "complex vec" and r and c where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and v_ker: "gs_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
    and r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
    and deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
    and c_def: "c = gs_c1 d ^ r * gs_c1 d ^ (2 * gs_m h * q)"
    and rho_int:
      "algebraic_int
        ((of_int c :: complex) *
          (gs_z d powi (- int r) *
            ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
              (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))))"
    and rho_nz:
      "(of_int c :: complex) *
        (gs_z d powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<noteq> 0"
    by (rule gs_exists_scaled_nonzero_algebraic_int_min_deriv[OF d qpos npos dvd])
  define rho :: complex where "rho = (of_int c :: complex) *
      (gs_z d powi (- int r) *
        ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
  have rho_lb:
      "1 \<le> cmod rho * gs_house rho ^
        (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
    unfolding rho_def by (rule one_le_self_mul_house_pow_of_nonzero_algebraic_int[OF rho_int rho_nz])
  show thesis
    using c_def deriv_nz r_eq rho_int rho_lb rho_nz that v_carrier v_ker v_nz vint
    unfolding rho_def by blast
qed

end
