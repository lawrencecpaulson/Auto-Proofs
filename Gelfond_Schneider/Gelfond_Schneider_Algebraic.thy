(*  Title:      Gelfond_Schneider/Gelfond_Schneider_Algebraic.thy
    Author:     OpenAI Codex

The first algebraic coefficient layer for the standalone Gelfond-Schneider
port. This mirrors the part of the Lean development where the basic auxiliary
function coefficients are expressed and their denominators are cleared by a
uniform integer scale.
*)

theory Gelfond_Schneider_Algebraic
  imports Gelfond_Schneider_Setup
begin

declare [[apply_timeout = 10]]

section \<open>Algebraic Coefficients\<close>

definition gs_affine_coeff :: "gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex"
  where "gs_affine_coeff d a b = of_nat a + of_nat b * gs_b d"

definition gs_rho :: "gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex"
  where "gs_rho d a b = gs_affine_coeff d a b * gs_z d"

definition gs_system_coeff ::
  "gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex"
  where
    "gs_system_coeff d a b l k =
      gs_affine_coeff d a b ^ k * gs_a d ^ (a * l) * gs_w d ^ (b * l)"

definition gs_c_coeffs ::
  "gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  where
    "gs_c_coeffs d n a b l =
      gs_c1 d ^ (n - 1) * gs_c1 d ^ (a * l) * gs_c1 d ^ (b * l)"

lemma algebraic_int_scaled_power:
  fixes c :: int and x :: complex
  assumes hx: "algebraic_int (of_int c * x)"
  shows "algebraic_int (of_int (c ^ n) * x ^ n)"
proof -
  have "algebraic_int ((of_int c * x) ^ n)"
    by (rule algebraic_int_power[OF hx])
  then show ?thesis
    by (simp add: power_mult_distrib)
qed

lemma algebraic_int_scaled_power_mono:
  fixes c :: int and x :: complex
  assumes hx: "algebraic_int (of_int c * x)"
  assumes mn: "m \<le> n"
  shows "algebraic_int (of_int (c ^ n) * x ^ m)"
proof -
  have hm: "algebraic_int (of_int (c ^ m) * x ^ m)"
    by (rule algebraic_int_scaled_power[OF hx])
  have hscaled: "algebraic_int (of_int (c ^ (n - m)) * (of_int (c ^ m) * x ^ m))"
    by (rule algebraic_int_of_int_scale[OF hm])
  have eq_term: "of_int (c ^ (n - m)) * (of_int (c ^ m) * x ^ m) =
      of_int (c ^ n) * x ^ m"
  proof -
    have "((of_int c :: complex) ^ (n - m)) * (of_int c :: complex) ^ m =
        (of_int c :: complex) ^ n"
      using mn by (simp add: power_add [symmetric] algebra_simps)
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  from hscaled show ?thesis
    by (simp only: eq_term)
qed

lemma gelfond_schneider_data_log_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  shows "gs_z d \<noteq> 0"
  by (rule gelfond_schneider_data_z_nonzero[OF d])

lemma gelfond_schneider_data_affine_coeff_algebraic:
  assumes d: "is_gelfond_schneider_data d"
  shows "algebraic (gs_affine_coeff d a b)"
  using d unfolding is_gelfond_schneider_data_def gs_affine_coeff_def by auto

lemma gelfond_schneider_data_affine_coeff_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  assumes bpos: "b > 0"
  shows "gs_affine_coeff d a b \<noteq> 0"
proof
  assume h0: "gs_affine_coeff d a b = 0"
  have b_rat: "gs_b d \<in> \<rat>"
  proof -
    have b_nz: "(of_nat b :: complex) \<noteq> 0"
      using bpos by simp
    have "of_nat b * gs_b d = - of_nat a"
      using h0 by (simp add: gs_affine_coeff_def add_eq_0_iff)
    then have "gs_b d = (- of_nat a) / of_nat b"
      using b_nz by (simp add: field_simps)
    moreover have "((- of_nat a) / of_nat b :: complex) \<in> \<rat>"
      by simp
    ultimately show ?thesis
      by simp
  qed
  from d b_rat show False
    unfolding is_gelfond_schneider_data_def by blast
qed

lemma gelfond_schneider_data_affine_coeff_injective:
  assumes d: "is_gelfond_schneider_data d"
  assumes eq: "gs_affine_coeff d a b = gs_affine_coeff d a' b'"
  shows "a = a' \<and> b = b'"
proof (cases "b = b'")
  case True
  with eq show ?thesis
    by (simp add: gs_affine_coeff_def)
next
  case False
  have denom_nz: "((of_nat b :: complex) - of_nat b') \<noteq> 0"
    using False by simp
  have beta_eq: "gs_b d = (of_nat a' - of_nat a) / (of_nat b - of_nat b')"
    using eq denom_nz by (simp add: gs_affine_coeff_def field_simps algebra_simps)
  have beta_rat: "gs_b d \<in> \<rat>"
  proof -
    have "((of_nat a' - of_nat a) / (of_nat b - of_nat b') :: complex) \<in> \<rat>"
      by simp
    with beta_eq show ?thesis
      by simp
  qed
  with d show ?thesis
    unfolding is_gelfond_schneider_data_def by blast
qed

lemma gelfond_schneider_data_affine_coeff_nonzero':
  assumes d: "is_gelfond_schneider_data d"
  assumes nz: "a > 0 \<or> b > 0"
  shows "gs_affine_coeff d a b \<noteq> 0"
proof
  assume h0: "gs_affine_coeff d a b = 0"
  have "gs_affine_coeff d a b = gs_affine_coeff d 0 0"
    using h0 by (simp add: gs_affine_coeff_def)
  then have ab0: "a = 0 \<and> b = 0"
    by (rule gelfond_schneider_data_affine_coeff_injective[OF d])
  with nz show False
    by auto
qed

lemma gelfond_schneider_data_rho_exp:
  assumes d: "is_gelfond_schneider_data d"
  shows "exp (gs_rho d a b) = gs_a d ^ a * gs_w d ^ b"
proof -
  have hz: "gs_z d \<in> log_values (gs_a d)"
    using d unfolding is_gelfond_schneider_data_def by blast
  have hbw: "gs_b d * gs_z d \<in> log_values (gs_w d)"
    using d unfolding is_gelfond_schneider_data_def by blast
  have "exp (gs_rho d a b) =
      exp (of_nat a * gs_z d + of_nat b * (gs_b d * gs_z d))"
    by (simp add: gs_rho_def gs_affine_coeff_def algebra_simps)
  also have "\<dots> = exp (of_nat a * gs_z d) * exp (of_nat b * (gs_b d * gs_z d))"
    by (simp add: exp_add)
  also have "\<dots> = exp (gs_z d) ^ a * exp (gs_b d * gs_z d) ^ b"
    by (simp add: exp_of_nat_mult [symmetric])
  also have "\<dots> = gs_a d ^ a * gs_w d ^ b"
    using hz hbw by simp
  finally show ?thesis .
qed

lemma gelfond_schneider_data_rho_injective:
  assumes d: "is_gelfond_schneider_data d"
  assumes eq: "gs_rho d a b = gs_rho d a' b'"
  shows "a = a' \<and> b = b'"
proof -
  have z_nz: "gs_z d \<noteq> 0"
    by (rule gelfond_schneider_data_z_nonzero[OF d])
  from eq have "gs_affine_coeff d a b * gs_z d = gs_affine_coeff d a' b' * gs_z d"
    by (simp add: gs_rho_def)
  then have "gs_affine_coeff d a b = gs_affine_coeff d a' b'"
    using z_nz by simp
  then show ?thesis
    by (rule gelfond_schneider_data_affine_coeff_injective[OF d])
qed

lemma gelfond_schneider_data_rho_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  assumes nz: "a > 0 \<or> b > 0"
  shows "gs_rho d a b \<noteq> 0"
proof
  assume h0: "gs_rho d a b = 0"
  have z_nz: "gs_z d \<noteq> 0"
    by (rule gelfond_schneider_data_z_nonzero[OF d])
  have aff_nz: "gs_affine_coeff d a b \<noteq> 0"
    by (rule gelfond_schneider_data_affine_coeff_nonzero'[OF d nz])
  from h0 show False
    using z_nz aff_nz by (simp add: gs_rho_def)
qed

lemma gelfond_schneider_data_system_coeff_algebraic:
  assumes d: "is_gelfond_schneider_data d"
  shows "algebraic (gs_system_coeff d a b l k)"
proof -
  have h1: "algebraic (gs_affine_coeff d a b)"
    by (rule gelfond_schneider_data_affine_coeff_algebraic[OF d])
  have h2: "algebraic (gs_a d)"
    using d unfolding is_gelfond_schneider_data_def by blast
  have h3: "algebraic (gs_w d)"
    using d unfolding is_gelfond_schneider_data_def by blast
  show ?thesis
    unfolding gs_system_coeff_def
    by (intro algebraic_times algebraic_power h1 h2 h3)
qed

lemma gelfond_schneider_data_c1_affine_algebraic_int:
  assumes d: "is_gelfond_schneider_data d"
  shows "algebraic_int (of_int (gs_c1 d) * gs_affine_coeff d a b)"
proof -
  have h1: "algebraic_int (of_int (gs_c1 d) * of_nat a :: complex)"
    by (intro algebraic_int_times algebraic_int_of_int algebraic_int_of_nat)
  have h2: "algebraic_int (of_nat b * (of_int (gs_c1 d) * gs_b d) :: complex)"
    by (intro algebraic_int_times algebraic_int_of_nat gelfond_schneider_data_c1_b_algebraic_int[OF d])
  have "algebraic_int
      (of_int (gs_c1 d) * of_nat a + of_nat b * (of_int (gs_c1 d) * gs_b d) :: complex)"
    by (rule algebraic_int_plus[OF h1 h2])
  then show ?thesis
    by (simp add: gs_affine_coeff_def algebra_simps)
qed

lemma gelfond_schneider_data_c1_affine_power_algebraic_int:
  assumes d: "is_gelfond_schneider_data d"
  assumes kn: "k \<le> n"
  shows "algebraic_int (of_int (gs_c1 d ^ n) * gs_affine_coeff d a b ^ k)"
  by (rule algebraic_int_scaled_power_mono[OF gelfond_schneider_data_c1_affine_algebraic_int[OF d] kn])

lemma gelfond_schneider_data_c1_a_power_algebraic_int:
  assumes d: "is_gelfond_schneider_data d"
  shows "algebraic_int (of_int (gs_c1 d ^ n) * gs_a d ^ n)"
  by (rule algebraic_int_scaled_power[OF gelfond_schneider_data_c1_a_algebraic_int[OF d]])

lemma gelfond_schneider_data_c1_w_power_algebraic_int:
  assumes d: "is_gelfond_schneider_data d"
  shows "algebraic_int (of_int (gs_c1 d ^ n) * gs_w d ^ n)"
  by (rule algebraic_int_scaled_power[OF gelfond_schneider_data_c1_w_algebraic_int[OF d]])

lemma gelfond_schneider_data_c1_a_power_bound_algebraic_int:
  assumes d: "is_gelfond_schneider_data d"
  assumes mn: "m \<le> n"
  shows "algebraic_int (of_int (gs_c1 d ^ n) * gs_a d ^ m)"
  by (rule algebraic_int_scaled_power_mono[OF gelfond_schneider_data_c1_a_algebraic_int[OF d] mn])

lemma gelfond_schneider_data_c1_w_power_bound_algebraic_int:
  assumes d: "is_gelfond_schneider_data d"
  assumes mn: "m \<le> n"
  shows "algebraic_int (of_int (gs_c1 d ^ n) * gs_w d ^ m)"
  by (rule algebraic_int_scaled_power_mono[OF gelfond_schneider_data_c1_w_algebraic_int[OF d] mn])

lemma gelfond_schneider_data_c_coeffs_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  shows "gs_c_coeffs d n a b l \<noteq> 0"
proof -
  have c1_nz: "gs_c1 d \<noteq> 0"
    by (rule gelfond_schneider_data_c1_nonzero[OF d])
  show ?thesis
    unfolding gs_c_coeffs_def by simp (use c1_nz in auto)
qed

lemma gelfond_schneider_data_system_coeff_scaled_algebraic_int:
  assumes d: "is_gelfond_schneider_data d"
  assumes kn: "k \<le> n - 1"
  shows "algebraic_int (of_int (gs_c_coeffs d n a b l) * gs_system_coeff d a b l k)"
proof -
  have h1: "algebraic_int (of_int (gs_c1 d ^ (n - 1)) * gs_affine_coeff d a b ^ k)"
    by (rule gelfond_schneider_data_c1_affine_power_algebraic_int[OF d kn])
  have h2: "algebraic_int (of_int (gs_c1 d ^ (a * l)) * gs_a d ^ (a * l))"
    by (rule gelfond_schneider_data_c1_a_power_algebraic_int[OF d])
  have h3: "algebraic_int (of_int (gs_c1 d ^ (b * l)) * gs_w d ^ (b * l))"
    by (rule gelfond_schneider_data_c1_w_power_algebraic_int[OF d])
  have "algebraic_int
      ((of_int (gs_c1 d ^ (n - 1)) * gs_affine_coeff d a b ^ k) *
       (of_int (gs_c1 d ^ (a * l)) * gs_a d ^ (a * l)) *
       (of_int (gs_c1 d ^ (b * l)) * gs_w d ^ (b * l)))"
    by (intro algebraic_int_times h1 h2 h3)
  then show ?thesis
    unfolding gs_c_coeffs_def gs_system_coeff_def
    by (simp add: algebra_simps)
qed

end
