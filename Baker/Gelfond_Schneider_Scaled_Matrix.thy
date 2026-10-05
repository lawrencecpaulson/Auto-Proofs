(*  Title:      Baker/Gelfond_Schneider_Scaled_Matrix.thy
    Author:     OpenAI Codex

Row-scaled matrix packaging for the indexed Gelfond-Schneider linear system.
This targets the scaling already used in the arithmetic layer: each row is
multiplied by a nonzero integer depending on the derivative order at that
interpolation node. The resulting matrix has the same kernel constraints for
vanishing/min-order purposes, while matching the later quantitative scaling
more closely than the raw system matrix.
*)

theory Gelfond_Schneider_Scaled_Matrix
  imports Gelfond_Schneider_Matrix
begin

section \<open>Row-Scaled Matrix Form\<close>

definition gs_row_scale ::
  "gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  where
    "gs_row_scale d m n q u =
      gs_c1 d ^ (gs_k_idx n u) * gs_c1 d ^ (m * q) * gs_c1 d ^ (m * q)"

definition gs_row_scaled_system_mat ::
  "gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex mat"
  where
    "gs_row_scaled_system_mat d m n q =
      mat (m * n) (q * q)
        (\<lambda>(u,t). of_int (gs_row_scale d m n q u) * gs_system_coeff_idx d n q u t)"

lemma gs_row_scale_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  shows "gs_row_scale d m n q u \<noteq> 0"
proof -
  have c1_nz: "gs_c1 d \<noteq> 0"
    by (rule gelfond_schneider_data_c1_nonzero[OF d])
  show ?thesis
    unfolding gs_row_scale_def using c1_nz by auto
qed

lemma gs_row_scaled_system_mat_carrier [simp]:
  "gs_row_scaled_system_mat d m n q \<in> carrier_mat (m * n) (q * q)"
  unfolding gs_row_scaled_system_mat_def by simp

lemma gs_row_scaled_system_mat_mult_component:
  assumes ult: "u < m * n"
  shows "((gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi>) $ u) =
    of_int (gs_row_scale d m n q u) * (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t)"
proof -
  have urow: "u < dim_row (gs_row_scaled_system_mat d m n q)"
    using ult unfolding gs_row_scaled_system_mat_def by simp
  have h1: "((gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi>) $ u) =
      row (gs_row_scaled_system_mat d m n q) u \<bullet> gs_coeff_vec q \<xi>"
    by (rule index_mult_mat_vec[OF urow])
  have h2: "row (gs_row_scaled_system_mat d m n q) u \<bullet> gs_coeff_vec q \<xi> =
      (\<Sum>i = 0..<q * q. \<xi> i * (of_int (gs_row_scale d m n q u) * gs_system_coeff_idx d n q u i))"
    using ult
    unfolding scalar_prod_def gs_row_scaled_system_mat_def gs_coeff_vec_def
    by (simp add: index_mat index_vec mult.commute)
  have h3: "(\<Sum>i = 0..<q * q. \<xi> i * (of_int (gs_row_scale d m n q u) * gs_system_coeff_idx d n q u i)) =
      of_int (gs_row_scale d m n q u) * (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t)"
    by (simp add: sum_distrib_left algebra_simps atLeast0LessThan)
  show ?thesis
    using h1 h2 h3 by simp
qed

lemma gs_row_scaled_system_mat_kernel_iff:
  assumes d: "is_gelfond_schneider_data d"
  shows "gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n) \<longleftrightarrow>
    (\<forall>u<m * n. (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0)"
proof
  assume ker: "gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
  show "\<forall>u<m * n. (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
  proof
    fix u
    show "u < m * n \<longrightarrow> (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
    proof
      assume ult: "u < m * n"
      have comp0: "((gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi>) $ u) = 0"
        using ker ult by simp
      have scale_nz: "of_int (gs_row_scale d m n q u) \<noteq> (0 :: complex)"
        using gs_row_scale_nonzero[OF d, of m n q u] by simp
      have "of_int (gs_row_scale d m n q u) * (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
        using comp0 ult by (simp add: gs_row_scaled_system_mat_mult_component)
      with scale_nz show "(\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
        by auto
    qed
  qed
next
  assume sys0: "\<forall>u<m * n. (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
  show "gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
  proof (rule eq_vecI)
    show "dim_vec (gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi>) = dim_vec (0\<^sub>v (m * n))"
      unfolding gs_row_scaled_system_mat_def by simp
  next
    fix u
    assume ult: "u < dim_vec (0\<^sub>v (m * n))"
    then have umn: "u < m * n"
      by simp
    then have sum0: "(\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
      using sys0 by blast
    show "(gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi>) $ u = (0\<^sub>v (m * n)) $ u"
      using ult sum0 by (simp add: gs_row_scaled_system_mat_mult_component)
  qed
qed

corollary gs_aux_fun_vec_deriv_vanish_at_node_of_row_scaled_kernel:
  assumes d: "is_gelfond_schneider_data d"
  assumes npos: "n > 0"
  assumes ker: "gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
  assumes llt: "l < m"
  assumes klt: "k < n"
  shows "((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat (Suc l)) = 0"
proof -
  have sys0: "\<And>u. u < m * n \<Longrightarrow> (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
    using gs_row_scaled_system_mat_kernel_iff[OF d, of m n q \<xi>] ker by blast
  show ?thesis
    by (rule gs_aux_fun_vec_deriv_vanish_at_node[OF d npos sys0 llt klt])
qed

corollary gs_min_order_ge_of_row_scaled_kernel_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes mpos: "m > 0"
  assumes npos: "n > 0"
  assumes coeff_nz: "\<exists>t<q * q. \<xi> t \<noteq> 0"
  assumes ker: "gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
  shows "gs_min_order m d q \<xi> \<ge> n"
proof -
  have sys0: "\<And>u. u < m * n \<Longrightarrow> (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
    using gs_row_scaled_system_mat_kernel_iff[OF d, of m n q \<xi>] ker by blast
  show ?thesis
    by (rule gs_min_order_ge_of_coeff_nonzero[OF d qpos mpos npos coeff_nz sys0])
qed

corollary gs_row_scaled_system_mat_exists_nonzero_coeffs:
  assumes mnq: "m * n < q * q"
  obtains \<xi> where "\<exists>t<q * q. \<xi> t \<noteq> 0"
    and "gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
proof -
  obtain \<xi> where nz: "\<exists>t<q * q. \<xi> t \<noteq> 0"
    and raw_ker: "gs_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
    by (rule gs_system_mat_exists_nonzero_coeffs[OF mnq])
  have sys0: "\<forall>u<m * n. (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
    using gs_system_mat_kernel_iff[of d m n q \<xi>] raw_ker by blast
  have ker: "gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
  proof (rule eq_vecI)
    show "dim_vec (gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi>) = dim_vec (0\<^sub>v (m * n))"
      unfolding gs_row_scaled_system_mat_def by simp
  next
    fix u
    assume ult: "u < dim_vec (0\<^sub>v (m * n))"
    then have umn: "u < m * n"
      by simp
    then have sum0: "(\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
      using sys0 by blast
    show "(gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi>) $ u = (0\<^sub>v (m * n)) $ u"
      using ult sum0 by (simp add: gs_row_scaled_system_mat_mult_component)
  qed
  show thesis
    by (rule that[OF nz ker])
qed

corollary gs_exists_row_scaled_auxiliary_coeffs_with_min_order_witness:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes mpos: "m > 0"
  assumes npos: "n > 0"
  assumes mnq: "m * n < q * q"
  obtains \<xi> r where "\<exists>t<q * q. \<xi> t \<noteq> 0"
    and "gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
    and "gs_min_order m d q \<xi> \<ge> n"
    and "r = nat (gs_min_order m d q \<xi>)"
    and "((deriv ^^ r) (gs_aux_fun_vec d q \<xi>)) (gs_min_order_node m d q \<xi>) \<noteq> 0"
proof -
  obtain \<xi> where nz: "\<exists>t<q * q. \<xi> t \<noteq> 0"
    and ker: "gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
    by (rule gs_row_scaled_system_mat_exists_nonzero_coeffs[OF mnq])
  have ord: "gs_min_order m d q \<xi> \<ge> n"
    by (rule gs_min_order_ge_of_row_scaled_kernel_nonzero[OF d qpos mpos npos nz ker])
  define r where "r = nat (gs_min_order m d q \<xi>)"
  have deriv_nz0:
      "((deriv ^^ nat (gs_min_order m d q \<xi>)) (gs_aux_fun_vec d q \<xi>))
        (gs_min_order_node m d q \<xi>) \<noteq> 0"
    by (rule gs_min_order_deriv_nonzero_of_coeff_nonzero[OF d qpos nz])
  have deriv_nz:
      "((deriv ^^ r) (gs_aux_fun_vec d q \<xi>)) (gs_min_order_node m d q \<xi>) \<noteq> 0"
    using deriv_nz0 by (simp add: r_def)
  show thesis
  proof (rule that[of \<xi> r])
    show "\<exists>t<q * q. \<xi> t \<noteq> 0"
      by (rule nz)
    show "gs_row_scaled_system_mat d m n q *\<^sub>v gs_coeff_vec q \<xi> = 0\<^sub>v (m * n)"
      by (rule ker)
    show "gs_min_order m d q \<xi> \<ge> n"
      by (rule ord)
    show "r = nat (gs_min_order m d q \<xi>)"
      by (simp add: r_def)
    show "((deriv ^^ r) (gs_aux_fun_vec d q \<xi>)) (gs_min_order_node m d q \<xi>) \<noteq> 0"
      by (rule deriv_nz)
  qed
qed

lemma gs_row_scaled_system_mat_entry_algebraic_int:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "n > 0"
  assumes ult: "u < m * n"
  assumes tlt: "t < q * q"
  shows "algebraic_int (gs_row_scaled_system_mat d m n q $$ (u, t))"
proof -
  have k_le: "gs_k_idx n u \<le> n - 1"
    by (rule gs_k_idx_le[OF npos])
  have a_le: "gs_a_idx q t \<le> q"
    by (rule gs_a_idx_le[OF qpos tlt])
  have b_le: "gs_b_idx q t \<le> q"
    by (rule gs_b_idx_le[OF qpos])
  have l_le: "gs_l_idx n u \<le> m"
    by (rule gs_l_idx_le[OF npos ult])
  have al: "gs_a_idx q t * gs_l_idx n u \<le> m * q"
  proof -
    have "gs_a_idx q t * gs_l_idx n u \<le> q * gs_l_idx n u"
      using a_le by simp
    also have "... \<le> q * m"
      using l_le by simp
    finally show ?thesis
      by (simp add: mult.commute)
  qed
  have bl: "gs_b_idx q t * gs_l_idx n u \<le> m * q"
  proof -
    have "gs_b_idx q t * gs_l_idx n u \<le> q * gs_l_idx n u"
      using b_le by simp
    also have "... \<le> q * m"
      using l_le by simp
    finally show ?thesis
      by (simp add: mult.commute)
  qed
  have h1: "algebraic_int
      (of_int (gs_c1 d ^ gs_k_idx n u) *
        gs_affine_coeff d (gs_a_idx q t) (gs_b_idx q t) ^ gs_k_idx n u)"
    by (rule gelfond_schneider_data_c1_affine_power_algebraic_int[OF d]) simp

  have h2: "algebraic_int
      (of_int (gs_c1 d ^ (m * q)) * gs_a d ^ (gs_a_idx q t * gs_l_idx n u))"
    by (rule gelfond_schneider_data_c1_a_power_bound_algebraic_int[OF d al])
  have h3: "algebraic_int
      (of_int (gs_c1 d ^ (m * q)) * gs_w d ^ (gs_b_idx q t * gs_l_idx n u))"
    by (rule gelfond_schneider_data_c1_w_power_bound_algebraic_int[OF d bl])
  have eq_term:
      "gs_row_scaled_system_mat d m n q $$ (u, t) =
        (of_int (gs_c1 d ^ gs_k_idx n u) *
          gs_affine_coeff d (gs_a_idx q t) (gs_b_idx q t) ^ gs_k_idx n u) *
        (of_int (gs_c1 d ^ (m * q)) * gs_a d ^ (gs_a_idx q t * gs_l_idx n u)) *
        (of_int (gs_c1 d ^ (m * q)) * gs_w d ^ (gs_b_idx q t * gs_l_idx n u))"
    using ult tlt
    unfolding gs_row_scaled_system_mat_def gs_row_scale_def gs_system_coeff_idx_def gs_system_coeff_def
    by (simp add: algebra_simps)
  have "algebraic_int
      ((of_int (gs_c1 d ^ gs_k_idx n u) *
          gs_affine_coeff d (gs_a_idx q t) (gs_b_idx q t) ^ gs_k_idx n u) *
        (of_int (gs_c1 d ^ (m * q)) * gs_a d ^ (gs_a_idx q t * gs_l_idx n u)) *
        (of_int (gs_c1 d ^ (m * q)) * gs_w d ^ (gs_b_idx q t * gs_l_idx n u)))"
    by (intro algebraic_int_times h1 h2 h3)
  then show ?thesis
    by (simp only: eq_term)
qed

lemma gs_row_scaled_system_mat_algebraic:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "n > 0"
  shows "algebraic_mat (gs_row_scaled_system_mat d m n q)"
proof (unfold algebraic_mat_def, intro allI impI)
  fix i j
  assume ij: "i < dim_row (gs_row_scaled_system_mat d m n q)" "j < dim_col (gs_row_scaled_system_mat d m n q)"
  then have ij': "i < m * n" "j < q * q"
    unfolding gs_row_scaled_system_mat_def by simp_all
  have ai: "algebraic_int (gs_row_scaled_system_mat d m n q $$ (i, j))"
    by (rule gs_row_scaled_system_mat_entry_algebraic_int[OF d qpos npos ij'])
  show "algebraic (gs_row_scaled_system_mat d m n q $$ (i, j))"
    using ai by auto
qed

lemma cmod_gs_affine_coeff_le:
  assumes aq: "a \<le> q"
  assumes bq: "b \<le> q"
  shows "cmod (gs_affine_coeff d a b) \<le> of_nat q * (1 + cmod (gs_b d))"
proof -
  have "cmod (gs_affine_coeff d a b) \<le> cmod (of_nat a) + cmod (of_nat b * gs_b d)"
    unfolding gs_affine_coeff_def by (rule norm_triangle_ineq)
  also have "... = of_nat a + of_nat b * cmod (gs_b d)"
    by (simp add: norm_mult)
  also have "... \<le> of_nat q + of_nat q * cmod (gs_b d)"
    using aq bq by (intro add_mono mult_right_mono) auto
  also have "... = of_nat q * (1 + cmod (gs_b d))"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma cmod_gs_system_coeff_idx_le:
  assumes qpos: "q > 0"
  assumes npos: "n > 0"
  assumes ult: "u < m * n"
  assumes tlt: "t < q * q"
  shows "cmod (gs_system_coeff_idx d n q u t) \<le>
    (of_nat q * (1 + cmod (gs_b d))) ^ gs_k_idx n u *
    (max 1 (cmod (gs_a d))) ^ (gs_a_idx q t * gs_l_idx n u) *
    (max 1 (cmod (gs_w d))) ^ (gs_b_idx q t * gs_l_idx n u)"
proof -
  let ?B = "of_nat q * (1 + cmod (gs_b d))"
  let ?ea = "gs_a_idx q t * gs_l_idx n u"
  let ?eb = "gs_b_idx q t * gs_l_idx n u"
  have a_le: "gs_a_idx q t \<le> q"
    by (rule gs_a_idx_le[OF qpos tlt])
  have b_le: "gs_b_idx q t \<le> q"
    by (rule gs_b_idx_le[OF qpos])
  have aff_le: "cmod (gs_affine_coeff d (gs_a_idx q t) (gs_b_idx q t)) \<le> ?B"
    by (rule cmod_gs_affine_coeff_le[OF a_le b_le])
  have aff_pow_le:
      "cmod (gs_affine_coeff d (gs_a_idx q t) (gs_b_idx q t)) ^ gs_k_idx n u \<le>
        ?B ^ gs_k_idx n u"
    by (rule power_mono[OF aff_le]) auto
  have a_pow_le:
      "cmod (gs_a d) ^ ?ea \<le> (max 1 (cmod (gs_a d))) ^ ?ea"
    by (rule power_mono) auto
  have w_pow_le:
      "cmod (gs_w d) ^ ?eb \<le> (max 1 (cmod (gs_w d))) ^ ?eb"
    by (rule power_mono) auto
  have eq_term:
      "gs_system_coeff_idx d n q u t =
        gs_affine_coeff d (gs_a_idx q t) (gs_b_idx q t) ^ gs_k_idx n u *
        gs_a d ^ ?ea * gs_w d ^ ?eb"
    unfolding gs_system_coeff_idx_def gs_system_coeff_def by simp
  have "cmod (gs_system_coeff_idx d n q u t) =
      cmod (gs_affine_coeff d (gs_a_idx q t) (gs_b_idx q t)) ^ gs_k_idx n u *
      cmod (gs_a d) ^ ?ea * cmod (gs_w d) ^ ?eb"
    by (simp add: eq_term norm_mult norm_power mult.assoc)
  also have "... \<le> ?B ^ gs_k_idx n u *
      (max 1 (cmod (gs_a d))) ^ ?ea *
      (max 1 (cmod (gs_w d))) ^ ?eb"
    using aff_pow_le a_pow_le w_pow_le by (intro mult_mono) auto
  finally show ?thesis .
qed

lemma cmod_gs_row_scaled_system_mat_entry_le:
  assumes qpos: "q > 0"
  assumes npos: "n > 0"
  assumes ult: "u < m * n"
  assumes tlt: "t < q * q"
  shows "cmod (gs_row_scaled_system_mat d m n q $$ (u, t)) \<le>
    abs (gs_row_scale d m n q u) *
    ((of_nat q * (1 + cmod (gs_b d))) ^ gs_k_idx n u *
      (max 1 (cmod (gs_a d))) ^ (gs_a_idx q t * gs_l_idx n u) *
      (max 1 (cmod (gs_w d))) ^ (gs_b_idx q t * gs_l_idx n u))"
proof -
  have eq_term:
      "gs_row_scaled_system_mat d m n q $$ (u, t) =
        of_int (gs_row_scale d m n q u) * gs_system_coeff_idx d n q u t"
    using ult tlt unfolding gs_row_scaled_system_mat_def by simp
  have "cmod (gs_row_scaled_system_mat d m n q $$ (u, t)) =
      abs (gs_row_scale d m n q u) * cmod (gs_system_coeff_idx d n q u t)"
    by (simp add: eq_term norm_mult)
  also have "... \<le> abs (gs_row_scale d m n q u) *
      ((of_nat q * (1 + cmod (gs_b d))) ^ gs_k_idx n u *
        (max 1 (cmod (gs_a d))) ^ (gs_a_idx q t * gs_l_idx n u) *
        (max 1 (cmod (gs_w d))) ^ (gs_b_idx q t * gs_l_idx n u))"
    by (intro mult_left_mono cmod_gs_system_coeff_idx_le[OF qpos npos ult tlt]) auto
  finally show ?thesis .
qed

lemma cmod_gs_row_scaled_system_mat_entry_le_uniform:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "n > 0"
  assumes ult: "u < m * n"
  assumes tlt: "t < q * q"
  shows "cmod (gs_row_scaled_system_mat d m n q $$ (u, t)) \<le>
    (of_int (abs (gs_c1 d)) * (of_nat q * (1 + cmod (gs_b d)))) ^ (n - 1) *
    (of_int (abs (gs_c1 d)) * max 1 (cmod (gs_a d))) ^ (m * q) *
    (of_int (abs (gs_c1 d)) * max 1 (cmod (gs_w d))) ^ (m * q)"
proof -
  let ?c = "of_int (abs (gs_c1 d))"
  let ?B0 = "of_nat q * (1 + cmod (gs_b d))"
  let ?A0 = "max 1 (cmod (gs_a d))"
  let ?W0 = "max 1 (cmod (gs_w d))"
  let ?k = "gs_k_idx n u"
  let ?ea = "gs_a_idx q t * gs_l_idx n u"
  let ?eb = "gs_b_idx q t * gs_l_idx n u"
  have k_le: "?k \<le> n - 1"
    by (rule gs_k_idx_le[OF npos])
  have a_le: "gs_a_idx q t \<le> q"
    by (rule gs_a_idx_le[OF qpos tlt])
  have b_le: "gs_b_idx q t \<le> q"
    by (rule gs_b_idx_le[OF qpos])
  have l_le: "gs_l_idx n u \<le> m"
    by (rule gs_l_idx_le[OF npos ult])
  have ea_le: "?ea \<le> m * q"
  proof -
    have "?ea \<le> q * gs_l_idx n u"
      using a_le by simp
    also have "... \<le> q * m"
      using l_le by simp
    finally show ?thesis
      by (simp add: mult.commute)
  qed
  have eb_le: "?eb \<le> m * q"
  proof -
    have "?eb \<le> q * gs_l_idx n u"
      using b_le by simp
    also have "... \<le> q * m"
      using l_le by simp
    finally show ?thesis
      by (simp add: mult.commute)
  qed
  have c1_ge1: "1 \<le> gs_c1 d"
    using gelfond_schneider_data_c1_ge1[OF d] .
  have c_nonneg: "0 \<le> gs_c1 d"
    using c1_ge1 by linarith
  have c_abs_eq_int: "abs (gs_c1 d) = gs_c1 d"
    using c_nonneg by simp
  have h_c_ge1: "1 \<le> (of_int (gs_c1 d) :: real)"
    using c1_ge1 by simp
  have c_eq: "?c = (of_int (gs_c1 d) :: real)"
    using c_abs_eq_int by (simp del: of_int_abs)
  have q_ge1_nat: "1 \<le> q"
    using qpos by simp
  have q_ge1: "1 \<le> (of_nat q :: real)"
    using q_ge1_nat by simp
  have B0_ge1': "1 \<le> 1 + cmod (gs_b d)"
    by simp
  have q_nonneg: "0 \<le> (of_nat q :: real)"
    by simp
  have B0_nonneg: "0 \<le> ?B0"
    by simp
  have B0_ge_q: "of_nat q \<le> ?B0"
  proof -
    have "of_nat q * 1 \<le> of_nat q * (1 + cmod (gs_b d))"
      using B0_ge1' q_nonneg by (rule mult_left_mono)
    then show ?thesis
      by simp
  qed
  have B0_ge1: "1 \<le> ?B0"
    by (rule order_trans[OF q_ge1 B0_ge_q])
  have B_ge_B0: "?B0 \<le> ?c * ?B0"
  proof -
    have "1 * ?B0 \<le> (of_int (gs_c1 d) :: real) * ?B0"
      using h_c_ge1 B0_nonneg by (rule mult_right_mono)
    then show ?thesis
      using c_eq by simp
  qed
  have B_ge1: "1 \<le> ?c * ?B0"
    by (rule order_trans[OF B0_ge1 B_ge_B0])
  have A0_ge1: "1 \<le> ?A0"
    by simp
  have W0_ge1: "1 \<le> ?W0"
    by simp
  have precise:
      "cmod (gs_row_scaled_system_mat d m n q $$ (u, t)) \<le>
        of_int (abs (gs_row_scale d m n q u)) * (?B0 ^ ?k * ?A0 ^ ?ea * ?W0 ^ ?eb)"
    by (rule cmod_gs_row_scaled_system_mat_entry_le[OF qpos npos ult tlt])
  have scale_eq:
      "of_int (abs (gs_row_scale d m n q u)) = ?c ^ ?k * ?c ^ (m * q) * ?c ^ (m * q)"
    unfolding gs_row_scale_def by (simp add: power_abs abs_mult algebra_simps)
  have k_part_le: "?c ^ ?k * ?B0 ^ ?k \<le> (?c * ?B0) ^ (n - 1)"
  proof -
    have "?c ^ ?k * ?B0 ^ ?k = (?c * ?B0) ^ ?k"
      by (simp add: power_mult_distrib [symmetric])
    also have "... \<le> (?c * ?B0) ^ (n - 1)"
      by (rule power_increasing) (use B_ge1 k_le in auto)
    finally show ?thesis .
  qed
  have a_part_le: "?c ^ (m * q) * ?A0 ^ ?ea \<le> (?c * ?A0) ^ (m * q)"
  proof -
    have "?A0 ^ ?ea \<le> ?A0 ^ (m * q)"
      by (rule power_increasing) (use A0_ge1 ea_le in auto)
    then have "?c ^ (m * q) * ?A0 ^ ?ea \<le> ?c ^ (m * q) * ?A0 ^ (m * q)"
      by (intro mult_left_mono) auto
    also have "... = (?c * ?A0) ^ (m * q)"
      by (simp add: power_mult_distrib [symmetric])
    finally show ?thesis .
  qed
  have w_part_le: "?c ^ (m * q) * ?W0 ^ ?eb \<le> (?c * ?W0) ^ (m * q)"
  proof -
    have "?W0 ^ ?eb \<le> ?W0 ^ (m * q)"
      by (rule power_increasing) (use W0_ge1 eb_le in auto)
    then have "?c ^ (m * q) * ?W0 ^ ?eb \<le> ?c ^ (m * q) * ?W0 ^ (m * q)"
      by (intro mult_left_mono) auto
    also have "... = (?c * ?W0) ^ (m * q)"
      by (simp add: power_mult_distrib [symmetric])
    finally show ?thesis .
  qed
  have expand_eq:
      "of_int (abs (gs_row_scale d m n q u)) * (?B0 ^ ?k * ?A0 ^ ?ea * ?W0 ^ ?eb) =
        (?c ^ ?k * ?B0 ^ ?k) * (?c ^ (m * q) * ?A0 ^ ?ea) * (?c ^ (m * q) * ?W0 ^ ?eb)"
  proof -
    have "of_int (abs (gs_row_scale d m n q u)) * (?B0 ^ ?k * ?A0 ^ ?ea * ?W0 ^ ?eb) =
        (?c ^ ?k * ?c ^ (m * q) * ?c ^ (m * q)) * (?B0 ^ ?k * ?A0 ^ ?ea * ?W0 ^ ?eb)"
      by (subst scale_eq) simp
    also have "... = (?c ^ ?k * ?B0 ^ ?k) * (?c ^ (m * q) * ?A0 ^ ?ea) * (?c ^ (m * q) * ?W0 ^ ?eb)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have ka_le:
      "(?c ^ ?k * ?B0 ^ ?k) * (?c ^ (m * q) * ?A0 ^ ?ea) \<le>
        (?c * ?B0) ^ (n - 1) * (?c * ?A0) ^ (m * q)"
    using k_part_le a_part_le by (intro mult_mono) auto
  have combined_le0:
      "of_int (abs (gs_row_scale d m n q u)) * (?B0 ^ ?k * ?A0 ^ ?ea * ?W0 ^ ?eb) \<le>
        ((?c * ?B0) ^ (n - 1) * (?c * ?A0) ^ (m * q)) * (?c * ?W0) ^ (m * q)"
  proof -
    have "of_int (abs (gs_row_scale d m n q u)) * (?B0 ^ ?k * ?A0 ^ ?ea * ?W0 ^ ?eb) =
        (?c ^ ?k * ?B0 ^ ?k) * (?c ^ (m * q) * ?A0 ^ ?ea) * (?c ^ (m * q) * ?W0 ^ ?eb)"
      by (rule expand_eq)
    also have "... \<le> ((?c * ?B0) ^ (n - 1) * (?c * ?A0) ^ (m * q)) * (?c ^ (m * q) * ?W0 ^ ?eb)"
      using ka_le by (intro mult_right_mono) auto
    also have "... \<le> ((?c * ?B0) ^ (n - 1) * (?c * ?A0) ^ (m * q)) * (?c * ?W0) ^ (m * q)"
      using w_part_le by (intro mult_left_mono) auto
    finally show ?thesis .
  qed
  have combined_le:
      "of_int (abs (gs_row_scale d m n q u)) * (?B0 ^ ?k * ?A0 ^ ?ea * ?W0 ^ ?eb) \<le>
        (?c * ?B0) ^ (n - 1) * (?c * ?A0) ^ (m * q) * (?c * ?W0) ^ (m * q)"
    using combined_le0 by (simp add: algebra_simps)
  show ?thesis
    by (rule order_trans[OF precise combined_le])
qed

theorem gs_row_scaled_system_mat_exists_nonzero_algebraic_int_kernel_vec_rectangular:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "n > 0"
  assumes mnq: "m * n < q * q"
  shows "\<exists>v. v \<in> carrier_vec (q * q) \<and> v \<noteq> 0\<^sub>v (q * q) \<and>
    gs_row_scaled_system_mat d m n q *\<^sub>v v = 0\<^sub>v (m * n) \<and>
    (\<forall>i<q * q. algebraic_int (v $ i))"
proof -
  have algA: "algebraic_mat (gs_row_scaled_system_mat d m n q)"
    by (rule gs_row_scaled_system_mat_algebraic[OF d qpos npos])
  show ?thesis
    using exists_nonzero_algebraic_int_kernel_vec_rectangular[OF gs_row_scaled_system_mat_carrier mnq algA]
    by blast
qed

theorem gs_exists_row_scaled_integral_auxiliary_data:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  obtains v :: "complex vec" and r where
      "v \<in> carrier_vec (q * q)"
    and "v \<noteq> 0\<^sub>v (q * q)"
    and "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and "\<forall>i<q * q. algebraic_int (v $ i)"
    and "gs_min_order (gs_m h) d q (\<lambda>t. v $ t) \<ge> gs_n h q"
    and "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t))"
    and "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)) \<noteq> 0"
proof -
  have qsq: "q ^ 2 = 2 * gs_m h * gs_n h q"
    by (rule gs_q_sq_eq_two_mn[OF dvd])
  have mnq: "gs_m h * gs_n h q < q * q"
  proof -
    have pos: "gs_m h * gs_n h q > 0"
      using npos by simp
    have "gs_m h * gs_n h q < 2 * (gs_m h * gs_n h q)"
      using pos by linarith
    also have "... = q ^ 2"
      using qsq by simp
    also have "... = q * q"
      by (simp add: power2_eq_square)
    finally show ?thesis .
  qed
  obtain v :: "complex vec" where
      v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
    and vint: "\<forall>i<q * q. algebraic_int (v $ i)"
    using gs_row_scaled_system_mat_exists_nonzero_algebraic_int_kernel_vec_rectangular[OF d qpos npos mnq]
    by blast
  have coeff_nz: "\<exists>t<q * q. v $ t \<noteq> 0"
    using v_carrier v_nz by force
  have min_ord: "gs_min_order (gs_m h) d q (\<lambda>t. v $ t) \<ge> gs_n h q"
  proof -
    have ker_coeff: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v gs_coeff_vec q (\<lambda>t. v $ t) =
        0\<^sub>v (gs_m h * gs_n h q)"
      by (simp add: gs_coeff_vec_eqI[OF v_carrier] v_ker)
    show ?thesis
      by (rule gs_min_order_ge_of_row_scaled_kernel_nonzero[OF d qpos gs_m_pos npos coeff_nz ker_coeff])
  qed

  define r0 where "r0 = nat (gs_min_order (gs_m h) d q (\<lambda>t. v $ t))"
  have deriv_nz:
      "((deriv ^^ r0) (gs_aux_fun_vec d q (\<lambda>t. v $ t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. v $ t)) \<noteq> 0"
    unfolding r0_def
    by (rule gs_min_order_deriv_nonzero_of_coeff_nonzero[OF d qpos coeff_nz])
  show thesis
    by (rule that[OF v_carrier v_nz v_ker vint min_ord]) (use r0_def deriv_nz in auto)
qed

end
