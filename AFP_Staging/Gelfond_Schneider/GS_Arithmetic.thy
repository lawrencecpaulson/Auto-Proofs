(*  Title:      Gelfond_Schneider/GS_Arithmetic.thy
    Author:     OpenAI Codex

Arithmetic lower-bound infrastructure for the standalone Gelfond-Schneider
port. This packages the first nonvanishing derivative into a scaled algebraic
integer, matching the algebraic half of the direct contradiction argument.
*)

theory GS_Arithmetic
  imports GS_Direct GS_House
begin

section \<open>Scaled Derivative Values\<close>

context gs_normalized_data
begin

definition gs_auxiliary_multiplier ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  where "gs_auxiliary_multiplier m q r \<equiv> gs_c1 ^ r * gs_c1 ^ (2 * m * q)"

definition gs_auxiliary_scaled_value ::
  "nat \<Rightarrow> nat \<Rightarrow> complex vec \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> complex"
  where
  "gs_auxiliary_scaled_value m q v r c \<equiv>
    c *
      (zeta powi (- int r) *
        ((deriv ^^ r) (gs_aux_fun_vec q (\<lambda>t. v $ t)))
          (gs_min_order_node m q (\<lambda>t. v $ t)))"

text \<open>The scaled first derivative is the algebraic integer used in the
house lower bound.\<close>

definition gs_integral_scaled_auxiliary_value ::
  "nat \<Rightarrow> nat \<Rightarrow> complex vec \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> complex \<Rightarrow> bool"
  where
  "gs_integral_scaled_auxiliary_value m q v r c rho \<equiv>
    c = gs_auxiliary_multiplier m q r \<and> c \<noteq> 0 \<and>
    rho = gs_auxiliary_scaled_value m q v r c \<and> algebraic_int rho \<and> rho \<noteq> 0"

lemma gs_aux_fun_vec_deriv_at_nat:
  shows "zeta powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec q \<xi>)) (of_nat l) =
         (\<Sum>t<q * q. \<xi> t * gs_system_coeff (gs_a_idx q t) (gs_b_idx q t) l k)"
proof -
  have "zeta powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec q \<xi>)) (of_nat l) =
      (\<Sum>t<q * q.
         zeta powi (- int k) * (\<xi> t * gs_rho_idx q t ^ k *
          exp (gs_rho_idx q t * of_nat l)))"
    by (simp add: gs_aux_fun_vec_iterated_deriv sum_distrib_left algebra_simps)
  also have "\<dots> = (\<Sum>t<q * q. \<xi> t * gs_system_coeff (gs_a_idx q t) (gs_b_idx q t) l k)"
  proof (rule sum.cong[OF refl])
    fix t
    assume tmem: "t \<in> {..<q * q}"
    have exp_eq:
        "exp (gs_rho_idx q t * of_nat l) =
          alpha ^ (gs_a_idx q t * l) * omega ^ (gs_b_idx q t * l)"
      by (simp add: exp_of_nat2_mult gelfond_schneider_data_rho_exp gs_rho_idx_def
          power_mult power_mult_distrib)
    have coeff_eq:
        "zeta powi (- int k) *
          (gs_rho_idx q t ^ k * exp (gs_rho_idx q t * of_nat l)) =
          gs_system_coeff (gs_a_idx q t) (gs_b_idx q t) l k"
    proof -
      have "zeta powi (- int k) * (gs_rho_idx q t ^ k * exp (gs_rho_idx q t * of_nat l))
         = gs_affine_coeff (gs_a_idx q t) (gs_b_idx q t) ^ k *
           exp (gs_rho_idx q t * of_nat l)"
        using gelfond_schneider_data_z_nonzero
        apply (simp add: algebra_simps gs_rho_idx_def gs_rho_def)
        apply (simp flip: power_int_add power_int_of_nat)
        done
      also have "\<dots> = gs_system_coeff (gs_a_idx q t) (gs_b_idx q t) l k"
        unfolding gs_system_coeff_def
        by (simp add: exp_eq)
      finally show ?thesis .
    qed
     show "zeta powi (- int k) * (\<xi> t * gs_rho_idx q t ^ k * exp (gs_rho_idx q t * of_nat l)) =
           \<xi> t * gs_system_coeff (gs_a_idx q t) (gs_b_idx q t) l k" 
       using coeff_eq by (simp add:  algebra_simps)
  qed
  finally show ?thesis .
qed

lemma gelfond_schneider_data_system_coeff_scaled_uniform_algebraic_int:
  assumes aq: "a \<le> q"
  assumes bq: "b \<le> q"
  assumes lm: "l \<le> m"
  shows "algebraic_int
    (of_int (gs_c1 ^ k * gs_c1 ^ (m * q) * gs_c1 ^ (m * q)) * gs_system_coeff a b l k)"
proof -
  have h1: "algebraic_int (of_int (gs_c1 ^ k) * gs_affine_coeff a b ^ k)"
    by (rule gelfond_schneider_data_c1_affine_power_algebraic_int) simp
  obtain al: "a * l \<le> m * q" and bl: "b * l \<le> m * q"
    using assms by (metis mult.commute mult_le_mono)
  have h2: "algebraic_int (of_int (gs_c1 ^ (m * q)) * alpha ^ (a * l))"
    by (rule gelfond_schneider_data_c1_a_power_bound_algebraic_int[OF al])
  have h3: "algebraic_int (of_int (gs_c1 ^ (m * q)) * omega ^ (b * l))"
    by (rule gelfond_schneider_data_c1_w_power_bound_algebraic_int[OF bl])
  have "algebraic_int
      ((of_int (gs_c1 ^ k) * gs_affine_coeff a b ^ k) *
       (of_int (gs_c1 ^ (m * q)) * alpha ^ (a * l)) *
       (of_int (gs_c1 ^ (m * q)) * omega ^ (b * l)))"
    by (intro algebraic_int_times h1 h2 h3)
  then show ?thesis
    unfolding gs_system_coeff_def
    by (simp add: algebra_simps)
qed

lemma gs_scaled_deriv_at_nat_algebraic_int:
  assumes qpos: "q > 0"
  assumes coeff_int: "\<forall>t<q * q. algebraic_int (\<xi> t)"
  assumes lm: "l \<le> m"
  shows "algebraic_int
    (of_int (gs_c1 ^ k * gs_c1 ^ (m * q) * gs_c1 ^ (m * q)) *
      (zeta powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec q \<xi>)) (of_nat l)))"
proof -
  define c :: int where "c \<equiv> gs_c1 ^ k * gs_c1 ^ (m * q) * gs_c1 ^ (m * q)"
  have sum_int: "algebraic_int
      (\<Sum>t<q * q. of_int c * (\<xi> t * gs_system_coeff (gs_a_idx q t) (gs_b_idx q t) l k))"
  proof (rule algebraic_int_sum)
    fix t
    assume tmem: "t \<in> {..<q * q}"
    have xi_int: "algebraic_int (\<xi> t)"
      using coeff_int tmem by blast
    have aq: "gs_a_idx q t \<le> q"
      using qpos gs_a_idx_le tmem by blast
    have bq: "gs_b_idx q t \<le> q"
      by (rule gs_b_idx_le[OF qpos])
    have coeff_term_int:
        "algebraic_int (c * gs_system_coeff (gs_a_idx q t) (gs_b_idx q t) l k)"
      unfolding c_def
      by (rule gelfond_schneider_data_system_coeff_scaled_uniform_algebraic_int[OF aq bq lm])
    show "algebraic_int (of_int c * (\<xi> t * gs_system_coeff (gs_a_idx q t) (gs_b_idx q t) l k))"
      using algebraic_int_times[OF xi_int coeff_term_int]
      by (simp add: algebra_simps)
  qed
  also have "\<dots> = of_int c *
      (zeta powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec q \<xi>)) (of_nat l))"
    by (simp add: sum_distrib_left gs_aux_fun_vec_deriv_at_nat algebra_simps)
  finally show ?thesis
    unfolding c_def by simp
qed

corollary gs_scaled_min_deriv_algebraic_int:
  assumes qpos: "q > 0"
  assumes mpos: "m > 0"
  assumes coeff_int: "\<forall>t<q * q. algebraic_int (\<xi> t)"
  assumes coeff_nz: "\<exists>t<q * q. \<xi> t \<noteq> 0"
  shows "algebraic_int
    (of_int (gs_c1 ^ nat (gs_min_order m q \<xi>) * gs_c1 ^ (2 * m * q)) *
      (zeta powi (- int (nat (gs_min_order m q \<xi>))) *
        ((deriv ^^ nat (gs_min_order m q \<xi>)) (gs_aux_fun_vec q \<xi>))
          (gs_min_order_node m q \<xi>)))"
proof -
  have nz: "gs_aux_fun_vec q \<xi> \<noteq> (\<lambda>_. 0)"
    by (rule gs_aux_fun_vec_nonzero[OF qpos coeff_nz])
  have ord_nonneg: "0 \<le> gs_min_order m q \<xi>"
    using holomorphic_nonzero_zorder_ge[OF gs_aux_fun_vec_holomorphic nz]
    using gs_min_order_def by fastforce
  obtain l where llt: "l < m" and node: "gs_min_order_node m q \<xi> = of_nat (Suc l)"
    by (rule gs_min_order_node_eq_nat[OF mpos])
  have l_le_m: "Suc l \<le> m"
    using llt by simp
  have coeff_scale_eq:
      "gs_c1 ^ nat (gs_min_order m q \<xi>) * gs_c1 ^ (m * q) * gs_c1 ^ (m * q) =
        gs_c1 ^ nat (gs_min_order m q \<xi>) * gs_c1 ^ (2 * m * q)"
    by (simp add: power2_eq_square power_mult power_mult_distrib)
  show ?thesis
    using gs_scaled_deriv_at_nat_algebraic_int[OF qpos coeff_int l_le_m]
    using coeff_scale_eq node by metis 
qed

lemma gs_scaled_rho_algebraic_int_nonzero:
  fixes v :: "complex vec"
  fixes rho :: complex
  assumes qpos: "q > 0"
  assumes mpos: "m > 0"
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
  assumes r_eq: "r = nat (gs_min_order m q (\<lambda>t. Matrix.vec_index v t))"
  assumes deriv_nz:
    "((deriv ^^ r) (gs_aux_fun_vec q (\<lambda>t. Matrix.vec_index v t)))
      (gs_min_order_node m q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
  assumes c_def: "c = gs_auxiliary_multiplier m q r"
  assumes rho_def: "rho = gs_auxiliary_scaled_value m q v r c"
  shows "algebraic_int rho" and "rho \<noteq> 0"
proof -
  have coeff_nz: "\<exists>t<q * q. Matrix.vec_index v t \<noteq> 0"
    using v_carrier v_nz by force
  have rho_int0:
    "algebraic_int
      (c *
        (zeta powi (- int r) *
          ((deriv ^^ r) (gs_aux_fun_vec q (\<lambda>t. Matrix.vec_index v t)))
            (gs_min_order_node m q (\<lambda>t. Matrix.vec_index v t))))"
    using r_eq gs_scaled_min_deriv_algebraic_int[OF qpos mpos vint coeff_nz]
    by (simp add: c_def gs_auxiliary_multiplier_def)
  have c_nz: "c \<noteq> 0"
    unfolding c_def using gelfond_schneider_data_c1_nonzero
    by (auto simp: gs_auxiliary_multiplier_def)
  have zfac_nz: "zeta powi (- int r) \<noteq> 0"
    using gelfond_schneider_data_z_nonzero by (simp add: power_int_def)
  have rho_nz0:
    "c * (zeta powi (- int r) *
        ((deriv ^^ r) (gs_aux_fun_vec q (\<lambda>t. Matrix.vec_index v t)))
          (gs_min_order_node m q (\<lambda>t. Matrix.vec_index v t))) \<noteq> 0"
    using c_nz zfac_nz deriv_nz by auto
  show "algebraic_int rho" "rho \<noteq> 0"
    using rho_int0 rho_nz0 rho_def 
    by (simp_all add: gs_auxiliary_scaled_value_def)
qed

theorem gs_exists_scaled_nonzero_algebraic_int_min_deriv:
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  obtains v :: "complex vec" and r and c and rho :: complex where
      "gs_integral_auxiliary_witness (gs_m h) (gs_n h q) q v r"
    and "gs_integral_scaled_auxiliary_value (gs_m h) q v r c rho"
proof -
  obtain v :: "complex vec" and r where
      W: "gs_integral_auxiliary_witness (gs_m h) (gs_n h q) q v r"
    by (rule gs_exists_integral_auxiliary_data[OF qpos npos dvd])
  have v: "v \<in> carrier_vec (q * q)" "v \<noteq> 0\<^sub>v (q * q)"
          "\<forall>i<q * q. algebraic_int (v $ i)"
    and r_eq: "r = nat (gs_min_order (gs_m h) q (\<lambda>t. v $ t))"
    and deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec q (\<lambda>t. v $ t)))
        (gs_min_order_node (gs_m h) q (\<lambda>t. v $ t)) \<noteq> 0"
    using W unfolding gs_integral_auxiliary_witness_def by blast+
  define c :: int where "c = gs_auxiliary_multiplier (gs_m h) q r"
  have c_nz: "c \<noteq> 0"
    unfolding c_def using gelfond_schneider_data_c1_nonzero
    by (auto simp: gs_auxiliary_multiplier_def)
  define rho where "rho = gs_auxiliary_scaled_value (gs_m h) q v r c"
  obtain "algebraic_int rho" and "rho \<noteq> 0"
    using gs_scaled_rho_algebraic_int_nonzero
      [OF qpos gs_m_pos v r_eq deriv_nz c_def rho_def]
    by blast
  then show thesis 
    using that[OF W] c_def c_nz gs_integral_scaled_auxiliary_value_def rho_def
    by blast
qed

theorem gs_exists_scaled_nonzero_algebraic_int_house_lower_bound:
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  obtains v :: "complex vec" and r and c and rho :: complex where
      "gs_integral_auxiliary_witness (gs_m h) (gs_n h q) q v r"
    and "gs_integral_scaled_auxiliary_value (gs_m h) q v r c rho"
    and "1 \<le> cmod rho * gs_house rho ^
          (card (set (complex_roots_of_int_poly (min_int_poly rho))) - 1)"
proof -
  obtain v :: "complex vec" and r and c and rho :: complex where
      W: "gs_integral_auxiliary_witness (gs_m h) (gs_n h q) q v r"
    and S: "gs_integral_scaled_auxiliary_value (gs_m h) q v r c rho"
    by (rule gs_exists_scaled_nonzero_algebraic_int_min_deriv[OF qpos npos dvd])
  have rho_int: "algebraic_int rho" and rho_nz: "rho \<noteq> 0"
    using S unfolding gs_integral_scaled_auxiliary_value_def by blast+
  then show thesis
    using that[OF W S] one_le_self_mul_house_pow_of_nonzero_algebraic_int by blast
qed

end

end
