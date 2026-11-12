(*  Title:      Gelfond_Schneider/GS_Algebraic.thy
    Author:     OpenAI Codex

The first algebraic coefficient layer for the standalone Gelfond-Schneider
port. This mirrors the part of the Lean development where the basic auxiliary
function coefficients are expressed and their denominators are cleared by a
uniform integer scale.
*)

theory GS_Algebraic
  imports GS_Setup
begin

section \<open>Algebraic Coefficients\<close>

context gs_normalized_data
begin

definition gs_affine_coeff :: "nat \<Rightarrow> nat \<Rightarrow> complex"
  where "gs_affine_coeff a b \<equiv> of_nat a + of_nat b * beta"

definition gs_rho :: "nat \<Rightarrow> nat \<Rightarrow> complex"
  where "gs_rho a b \<equiv> gs_affine_coeff a b * zeta"

definition gs_system_coeff ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex"
  where
    "gs_system_coeff a b l k =
      gs_affine_coeff a b ^ k * alpha ^ (a * l) * omega ^ (b * l)"

definition gs_c_coeffs :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  where
    "gs_c_coeffs n a b l \<equiv> gs_c1 ^ (n - 1) * gs_c1 ^ (a * l) * gs_c1 ^ (b * l)"

lemma algebraic_int_scaled_power:
  fixes c :: int and x :: complex
  assumes "algebraic_int (of_int c * x)"
  shows "algebraic_int (of_int (c ^ n) * x ^ n)"
  using assms 
  by (metis algebraic_int_power power_mult_distrib of_int_power)

lemma algebraic_int_scaled_power_mono:
  fixes c :: int and x :: complex
  assumes hx: "algebraic_int (of_int c * x)"
  assumes mn: "m \<le> n"
  shows "algebraic_int (of_int (c ^ n) * x ^ m)"
proof -
  have hscaled: "algebraic_int (of_int (c ^ (n - m)) * (of_int (c ^ m) * x ^ m))"
    using algebraic_int_scaled_power hx by blast
  have eq_term: "of_int (c ^ (n - m)) * (of_int (c ^ m) * x ^ m) = of_int (c ^ n) * x ^ m"
      using mn by (simp add: power_add [symmetric] algebra_simps)
  from hscaled show ?thesis
    by (simp only: eq_term)
qed

lemma gelfond_schneider_data_log_nonzero:
  shows "zeta \<noteq> 0"
  by (rule gelfond_schneider_data_z_nonzero)

lemma gelfond_schneider_data_affine_coeff_algebraic:
  shows "algebraic (gs_affine_coeff a b)"
  using beta_alg unfolding gs_affine_coeff_def by auto

lemma gelfond_schneider_data_affine_coeff_nonzero:
  assumes bpos: "b > 0"
  shows "gs_affine_coeff a b \<noteq> 0"
proof
  assume h0: "gs_affine_coeff a b = 0"
  have b_rat: "beta \<in> \<rat>"
  proof -
    have "of_nat b * beta = - of_nat a"
      using h0 by (simp add: gs_affine_coeff_def add_eq_0_iff)
    then have "beta = (- of_nat a) / of_nat b"
      using bpos by (simp add: field_simps)
    then show ?thesis
      by simp
  qed
  from beta_irrational b_rat show False
    by blast
qed

lemma gelfond_schneider_data_affine_coeff_injective:
  assumes eq: "gs_affine_coeff a b = gs_affine_coeff a' b'"
  shows "a = a' \<and> b = b'"
proof (cases "b = b'")
  case True
  with eq show ?thesis
    by (simp add: gs_affine_coeff_def)
next
  case False
  have denom_nz: "((of_nat b :: complex) - of_nat b') \<noteq> 0"
    using False by simp
  have beta_eq: "beta = (of_nat a' - of_nat a) / (of_nat b - of_nat b')"
    using eq denom_nz by (simp add: gs_affine_coeff_def field_simps algebra_simps)
  have beta_rat: "beta \<in> \<rat>"
    by (simp add: beta_eq)
  with beta_irrational show ?thesis
    by blast
qed

lemma gelfond_schneider_data_affine_coeff_nonzero':
  assumes "a > 0 \<or> b > 0"
  shows "gs_affine_coeff a b \<noteq> 0"
proof
  assume h0: "gs_affine_coeff a b = 0"
  have "gs_affine_coeff a b = gs_affine_coeff 0 0"
    using h0 by (simp add: gs_affine_coeff_def)
  with assms gelfond_schneider_data_affine_coeff_injective show False
    by auto
qed

lemma gelfond_schneider_data_rho_exp:
  shows "exp (gs_rho a b) = alpha ^ a * omega ^ b"
proof -
  have hz: "zeta \<in> log_values (alpha)"
    by (rule zeta_log_alpha)
  have hbw: "beta * zeta \<in> log_values (omega)"
    by (rule beta_zeta_log_omega)
  have "exp (gs_rho a b) = exp (of_nat a * zeta) * exp (of_nat b * (beta * zeta))"
    by (simp add: gs_rho_def gs_affine_coeff_def algebra_simps exp_add)
  also have "\<dots> = exp (zeta) ^ a * exp (beta * zeta) ^ b"
    by (simp add: exp_of_nat_mult [symmetric])
  also have "\<dots> = alpha ^ a * omega ^ b"
    using hz hbw by simp
  finally show ?thesis .
qed

lemma gelfond_schneider_data_rho_injective:
  assumes eq: "gs_rho a b = gs_rho a' b'"
  shows "a = a' \<and> b = b'"
  using assms gelfond_schneider_data_affine_coeff_injective
    gelfond_schneider_data_log_nonzero gs_rho_def by auto

lemma gelfond_schneider_data_rho_nonzero:
  assumes "a > 0 \<or> b > 0"
  shows "gs_rho a b \<noteq> 0"
  by (simp add: assms gelfond_schneider_data_affine_coeff_nonzero'
      gelfond_schneider_data_log_nonzero gs_rho_def)

lemma gelfond_schneider_data_system_coeff_algebraic:
  shows "algebraic (gs_system_coeff a b l k)"
proof -
  have "algebraic (gs_affine_coeff a b)"
    by (rule gelfond_schneider_data_affine_coeff_algebraic)
  then show ?thesis
    unfolding gs_system_coeff_def
    by (intro algebraic_times algebraic_power alpha_alg omega_alg)
qed

lemma gelfond_schneider_data_c1_affine_algebraic_int:
  shows "algebraic_int (of_int (gs_c1) * gs_affine_coeff a b)"
proof -
  have h1: "algebraic_int (of_int (gs_c1) * of_nat a :: complex)"
    by (intro algebraic_int_times algebraic_int_of_int algebraic_int_of_nat)
  have h2: "algebraic_int (of_nat b * (of_int (gs_c1) * beta))"
    by (intro algebraic_int_times algebraic_int_of_nat gelfond_schneider_data_c1_b_algebraic_int)
  have "algebraic_int
      (of_int (gs_c1) * of_nat a + of_nat b * (of_int (gs_c1) * beta) :: complex)"
    by (rule algebraic_int_plus[OF h1 h2])
  then show ?thesis
    by (simp add: gs_affine_coeff_def algebra_simps)
qed

lemma gelfond_schneider_data_c1_affine_power_algebraic_int:
  assumes kn: "k \<le> n"
  shows "algebraic_int (of_int (gs_c1 ^ n) * gs_affine_coeff a b ^ k)"
  by (rule algebraic_int_scaled_power_mono[OF gelfond_schneider_data_c1_affine_algebraic_int kn])

lemma gelfond_schneider_data_c1_a_power_algebraic_int:
  shows "algebraic_int (of_int (gs_c1 ^ n) * alpha ^ n)"
  by (rule algebraic_int_scaled_power[OF gelfond_schneider_data_c1_a_algebraic_int])

lemma gelfond_schneider_data_c1_w_power_algebraic_int:
  shows "algebraic_int (of_int (gs_c1 ^ n) * omega ^ n)"
  by (rule algebraic_int_scaled_power[OF gelfond_schneider_data_c1_w_algebraic_int])

lemma gelfond_schneider_data_c1_a_power_bound_algebraic_int:
  assumes mn: "m \<le> n"
  shows "algebraic_int (of_int (gs_c1 ^ n) * alpha ^ m)"
  by (rule algebraic_int_scaled_power_mono[OF gelfond_schneider_data_c1_a_algebraic_int mn])

lemma gelfond_schneider_data_c1_w_power_bound_algebraic_int:
  assumes mn: "m \<le> n"
  shows "algebraic_int (of_int (gs_c1 ^ n) * omega ^ m)"
  by (rule algebraic_int_scaled_power_mono[OF gelfond_schneider_data_c1_w_algebraic_int mn])

lemma gelfond_schneider_data_c_coeffs_nonzero:
  shows "gs_c_coeffs n a b l \<noteq> 0"
  by (simp add: gelfond_schneider_data_c1_nonzero gs_c_coeffs_def)

lemma gelfond_schneider_data_system_coeff_scaled_algebraic_int:
  assumes kn: "k \<le> n - 1"
  shows "algebraic_int (of_int (gs_c_coeffs n a b l) * gs_system_coeff a b l k)"
proof -
  have h1: "algebraic_int (of_int (gs_c1 ^ (n - 1)) * gs_affine_coeff a b ^ k)"
    by (rule gelfond_schneider_data_c1_affine_power_algebraic_int[OF kn])
  have h2: "algebraic_int (of_int (gs_c1 ^ (a * l)) * alpha ^ (a * l))"
    by (rule gelfond_schneider_data_c1_a_power_algebraic_int)
  have h3: "algebraic_int (of_int (gs_c1 ^ (b * l)) * omega ^ (b * l))"
    by (rule gelfond_schneider_data_c1_w_power_algebraic_int)
  have "algebraic_int
      ((of_int (gs_c1 ^ (n - 1)) * gs_affine_coeff a b ^ k) *
       (of_int (gs_c1 ^ (a * l)) * alpha ^ (a * l)) *
       (of_int (gs_c1 ^ (b * l)) * omega ^ (b * l)))"
    by (intro algebraic_int_times h1 h2 h3)
  then show ?thesis
    unfolding gs_c_coeffs_def gs_system_coeff_def
    by (simp add: algebra_simps)
qed

end

end
