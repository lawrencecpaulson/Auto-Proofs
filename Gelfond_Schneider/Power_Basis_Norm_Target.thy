(*  Title:      Gelfond_Schneider/Power_Basis_Norm_Target.thy
    Author:     OpenAI Codex

Power-basis norm estimates, controlled-denominator kernel construction, and
the verified scaled contradiction.
*)

theory Power_Basis_Norm_Target
  imports
    Power_Basis_Recovery
    Power_Basis
    Power_Basis_Inverse_Bounds
    Power_Basis_Field_Norm
    Rho_Bounds
begin

section \<open>Denominator and growth budgets\<close>

text \<open>Each factor in a system coefficient consumes one power of the common
denominator. A row-scaled entry also includes a power-basis factor; the row
budget bounds their total count uniformly.\<close>

definition gs_system_coeff_factor_count :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "gs_system_coeff_factor_count a b l k = k + a * l + b * l"

definition gs_row_denominator_exponent :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "gs_row_denominator_exponent m n q D = n + 2 * (m * q) + D"

definition gs_row_denominator_order_exponent :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "gs_row_denominator_order_exponent m D = 1 + 4 * m * m + D"

definition gs_kernel_witness_bound :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> int"
  where "gs_kernel_witness_bound \<equiv>
    (\<lambda>ncols nbasis W H. 2 * int (ncols * nbasis) * max 1 \<lceil>W * H\<rceil>)"

text \<open>The house and distinguished-embedding estimates use different powers
of the derivative order. Their product gives the exponent in the norm bound.\<close>

definition gs_house_order_exponent :: "nat \<Rightarrow> real"
  where "gs_house_order_exponent r = of_nat r + 3 / 2"

definition gs_point_order_exponent :: "nat \<Rightarrow> nat \<Rightarrow> real"
  where "gs_point_order_exponent m r = of_nat r * (3 - of_nat m) / 2 + 3 / 2"

locale gelfond_schneider_power_basis_field_norm_estimates =
  finite_normal_galois_power_basis K eta D emb
  for K :: "complex set"
  and eta :: complex
  and D :: nat
  and emb :: "nat \<Rightarrow> complex \<Rightarrow> complex" +
  fixes ca cb cw :: "nat \<Rightarrow> complex"
  fixes d
  fixes q h i0
  fixes A c5 c14 :: real
  assumes d: "is_gelfond_schneider_data d"
  assumes coords: "rational_power_basis_coordinates D eta ca cb cw (gs_a d) (gs_b d) (gs_w d)"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes dvd: "2 * gs_m h dvd q ^ 2"
  assumes i0lt: "i0 < D"
  assumes emb0: "emb i0 = identity K"
  assumes entryK:
    "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow>
      gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) \<in> K"
  assumes hpos: "h > 0"
  assumes q_def: "q = gs_q_choice h (c14 * c5)"
  assumes c14_ge1: "1 \<le> c14"
  assumes c5_gt1: "1 < c5"
begin

lemmas ca_rat = rational_power_basis_coordinates.ca_rat[OF coords]
lemmas a_eq = rational_power_basis_coordinates.a_eq[OF coords]
lemmas cb_rat = rational_power_basis_coordinates.cb_rat[OF coords]
lemmas b_eq = rational_power_basis_coordinates.b_eq[OF coords]
lemmas cw_rat = rational_power_basis_coordinates.cw_rat[OF coords]
lemmas w_eq = rational_power_basis_coordinates.w_eq[OF coords]

definition Aemb :: "nat \<Rightarrow> nat \<Rightarrow> (complex \<Rightarrow> complex) \<Rightarrow> complex"
  where "Aemb u t e \<equiv> e (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))"

definition gs_power_basis_witness_coordinates :: "complex vec \<Rightarrow> int vec \<Rightarrow> bool"
  where "gs_power_basis_witness_coordinates v x \<longleftrightarrow>
    (\<forall>t<q * q. Matrix.vec_index v t =
      (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i0)))"

lemma identity_apply_in_K:
  assumes xK: "x \<in> K"
  shows "identity K x = x"
  using assms by fastforce

lemma row_scaled_entry0:
  assumes up: "u < gs_m h * gs_n h q"
  assumes tq: "t < q * q"
  shows "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) = Aemb u t (emb i0)"
proof -
  have xK: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) \<in> K"
    by (rule entryK[OF up tq])
  have "Aemb u t (emb i0) = emb i0 (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))"
    by (simp add: Aemb_def)
  also have "... = gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t)"
    using xK by (simp add: emb0 identity_apply_in_K)
  finally show ?thesis
    by simp
qed

lemma a_in_K: "gs_a d \<in> K"
  using a_eq ca_rat sum_rat_power_in_K by presburger

lemma b_in_K: "gs_b d \<in> K"
  using b_eq cb_rat sum_rat_power_in_K by presburger

lemma w_in_K: "gs_w d \<in> K"
  using cw_rat sum_rat_power_in_K w_eq by presburger

lemma gs_affine_coeff_in_K:
  shows "gs_affine_coeff d a b \<in> K"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have aK: "of_nat a \<in> K"
    by auto
  have bK: "of_nat b \<in> K"
    by (simp add: KS.of_nat_closed)
  have bgK: "of_nat b * gs_b d \<in> K"
    by (rule KS.mult_closed[OF bK b_in_K])
  show ?thesis
    unfolding gs_affine_coeff_def
    by (rule KS.add_closed[OF aK bgK])
qed

lemma gs_affine_coeff_emb_cmod_le:
  assumes ilt: "i < D"
  assumes aq: "a \<le> q"
  assumes bq: "b \<le> q"
  shows "cmod (emb i (gs_affine_coeff d a b)) \<le> of_nat q * (1 + cmod (emb i (gs_b d)))"
proof -
  interpret KS: Subfield K by (rule K_subfield)
  have sigma: "emb i \<in> field_auto K \<rat>"
    by (rule emb_in_field_auto[OF ilt])
  have bgK: "of_nat b * gs_b d \<in> K"
    using b_in_K by blast
  have afix: "emb i (of_nat a :: complex) = of_nat a"
    using sigma by (simp add: field_auto_mem_iff)
  have bfix: "emb i (of_nat b :: complex) = of_nat b"
    using sigma by (simp add: field_auto_mem_iff)
  have eq: "emb i (gs_affine_coeff d a b) = of_nat a + of_nat b * emb i (gs_b d)"
    using field_auto_mult[OF sigma] afix bfix Rats_subset_K
    unfolding gs_affine_coeff_def subset_iff
    by (simp add: field_auto_add[OF sigma _ bgK] field_auto_mult[OF sigma _ b_in_K] afix bfix)
  have "cmod (emb i (gs_affine_coeff d a b)) \<le>
      cmod (of_nat a :: complex) + cmod (of_nat b * emb i (gs_b d))"
    unfolding eq by (rule norm_triangle_ineq)
  also have "... = of_nat a + of_nat b * cmod (emb i (gs_b d))"
    by (simp add: norm_mult)
  also have "... \<le> of_nat q + of_nat q * cmod (emb i (gs_b d))"
    using aq bq by (intro add_mono mult_right_mono) auto
  also have "... = of_nat q * (1 + cmod (emb i (gs_b d)))"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma gs_system_coeff_emb_cmod_le:
  assumes ilt: "i < D"
  assumes aq: "a \<le> q"
  assumes bq: "b \<le> q"
  shows "cmod (emb i (gs_system_coeff d a b l k)) \<le>
    (of_nat q * (1 + cmod (emb i (gs_b d)))) ^ k *
    cmod (emb i (gs_a d)) ^ (a * l) * cmod (emb i (gs_w d)) ^ (b * l)"
proof -
  interpret KS: Subfield K by (rule K_subfield)
  have sigma: "emb i \<in> field_auto K \<rat>"
    by (rule emb_in_field_auto[OF ilt])
  have hom: "field_hom_on K (emb i)"
    by (rule field_auto_as_hom[OF K_subfield sigma])
  obtain affK: "gs_affine_coeff d a b ^ k \<in> K" and aPowK: "gs_a d ^ (a * l) \<in> K"
    and wPowK: "gs_w d ^ (b * l) \<in> K"
    using a_in_K gs_affine_coeff_in_K w_in_K by blast
  have leftK: "gs_affine_coeff d a b ^ k * gs_a d ^ (a * l) \<in> K"
    by (rule KS.mult_closed[OF affK aPowK])
  have eq: "emb i (gs_system_coeff d a b l k) =
      emb i (gs_affine_coeff d a b) ^ k *
      emb i (gs_a d) ^ (a * l) * emb i (gs_w d) ^ (b * l)"
    unfolding gs_system_coeff_def
    by (simp add: field_auto_mult[OF sigma leftK wPowK]
        field_auto_mult[OF sigma affK aPowK]
        field_hom_on.hom_power[OF hom gs_affine_coeff_in_K]
        field_hom_on.hom_power[OF hom a_in_K]
        field_hom_on.hom_power[OF hom w_in_K])
  have affpow: "cmod (emb i (gs_affine_coeff d a b)) ^ k \<le>
      (of_nat q * (1 + cmod (emb i (gs_b d)))) ^ k"
    by (rule power_mono[OF gs_affine_coeff_emb_cmod_le[OF ilt aq bq]]) auto
  have "cmod (emb i (gs_system_coeff d a b l k)) =
      cmod (emb i (gs_affine_coeff d a b)) ^ k *
      cmod (emb i (gs_a d)) ^ (a * l) * cmod (emb i (gs_w d)) ^ (b * l)"
    by (simp add: eq norm_mult norm_power)
  also have "... \<le> (of_nat q * (1 + cmod (emb i (gs_b d)))) ^ k *
      cmod (emb i (gs_a d)) ^ (a * l) * cmod (emb i (gs_w d)) ^ (b * l)"
    using affpow by (intro mult_right_mono) auto
  finally show ?thesis .
qed

lemma gs_system_coeff_in_K: "gs_system_coeff d a b l k \<in> K"
  by (simp add: K_subfield Subfield.mult_closed Subfield.power_closed a_in_K gs_affine_coeff_in_K
      gs_system_coeff_def w_in_K)

lemma gs_row_scaled_entry_emb_cmod_le:
  assumes ilt: "i < D"
  assumes qpos: "q > 0"
  assumes npos: "gs_n h q > 0"
  assumes ult: "u < gs_m h * gs_n h q"
  assumes tlt: "t < q * q"
  shows "cmod (emb i (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) \<le>
    \<bar>gs_row_scale d (gs_m h) (gs_n h q) q u\<bar> *
    (of_nat q * (1 + cmod (emb i (gs_b d)))) ^ gs_k_idx (gs_n h q) u *
    cmod (emb i (gs_a d)) ^ (gs_a_idx q t * gs_l_idx (gs_n h q) u) *
    cmod (emb i (gs_w d)) ^ (gs_b_idx q t * gs_l_idx (gs_n h q) u)"
proof -
  let ?c = "gs_row_scale d (gs_m h) (gs_n h q) q u"
  let ?s = "gs_system_coeff_idx d (gs_n h q) q u t"
  have sigma: "emb i \<in> field_auto K \<rat>"
    by (rule emb_in_field_auto[OF ilt])
  have cK: "(of_int ?c :: complex) \<in> K"
    using Rats_subset_K by auto
  have sK: "?s \<in> K"
    unfolding gs_system_coeff_idx_def by (rule gs_system_coeff_in_K)
  have cfix: "emb i (of_int ?c :: complex) = of_int ?c"
    using sigma by (simp add: field_auto_mem_iff)
  have eq: "emb i (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t)) = of_int ?c * emb i ?s"
    using ult tlt
    by (simp add: gs_row_scaled_system_mat_def field_auto_mult[OF sigma cK sK] cfix)
  obtain ale: "gs_a_idx q t \<le> q" and ble: "gs_b_idx q t \<le> q"
    by (simp add: tlt gs_a_idx_le gs_b_idx_le qpos)
  have sbnd: "cmod (emb i ?s) \<le>
      (of_nat q * (1 + cmod (emb i (gs_b d)))) ^ gs_k_idx (gs_n h q) u *
      cmod (emb i (gs_a d)) ^ (gs_a_idx q t * gs_l_idx (gs_n h q) u) *
      cmod (emb i (gs_w d)) ^ (gs_b_idx q t * gs_l_idx (gs_n h q) u)"
    unfolding gs_system_coeff_idx_def
    by (rule gs_system_coeff_emb_cmod_le[OF ilt ale ble])
  have "cmod (emb i (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) =
      \<bar>?c\<bar> * cmod (emb i ?s)"
    by (simp add: eq norm_mult)
  also have "... \<le> \<bar>?c\<bar> *
      ((of_nat q * (1 + cmod (emb i (gs_b d)))) ^ gs_k_idx (gs_n h q) u *
      cmod (emb i (gs_a d)) ^ (gs_a_idx q t * gs_l_idx (gs_n h q) u) *
      cmod (emb i (gs_w d)) ^ (gs_b_idx q t * gs_l_idx (gs_n h q) u))"
    by (rule mult_left_mono[OF sbnd]) simp
  finally show ?thesis by (simp add: mult.assoc)
qed

lemma gs_scaled_deriv_emb_sum_bound:
  assumes ilt: "i < D"
  assumes coeffK: "\<And>t. t < q * q \<Longrightarrow> \<xi> t \<in> K"
  shows "cmod (emb i (of_int c *
    (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l)))) \<le>
    of_int \<bar>c\<bar> *
      (\<Sum>t<q * q. cmod (emb i (\<xi> t)) *
        cmod (emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)))"
proof -
  interpret KS: Subfield K by (rule K_subfield)
  have sigma: "emb i \<in> field_auto K \<rat>"
    by (rule emb_in_field_auto[OF ilt])
  have hom: "field_hom_on K (emb i)"
    by (rule field_auto_as_hom[OF K_subfield sigma])
  have cK: "of_int c \<in> K"
    using Rats_subset_K by auto
  have termK: "\<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k \<in> K"
    if tlt: "t < q * q" for t
    by (rule KS.mult_closed[OF coeffK[OF tlt] gs_system_coeff_in_K])
  have sumK: "(\<Sum>t<q * q. \<xi> t *
      gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k) \<in> K"
    by (rule KS.sum_closed) (use termK in auto)
  have cfix: "emb i (of_int c) = of_int c"
    using sigma by (simp add: field_auto_mem_iff)
  have "emb i (of_int c *
    (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l))) =
      of_int c * emb i (\<Sum>t<q * q. \<xi> t *
        gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)"
    by (simp add: gs_aux_fun_vec_deriv_at_nat[OF d] field_auto_mult[OF sigma cK sumK] cfix)
  also have "... = of_int c * (\<Sum>t<q * q. emb i (\<xi> t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k))"
    using field_hom_on.hom_sum[OF hom] termK
    by (metis (no_types, lifting) ext lessThan_iff)
  also have "... = of_int c * (\<Sum>t<q * q. emb i (\<xi> t) *
      emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k))"
    by (intro arg_cong[where f="(\<lambda>x::complex. of_int c * x)"] sum.cong)
       (auto intro: field_auto_mult[OF sigma coeffK gs_system_coeff_in_K])
  finally  have "emb i (of_int c *
    (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l))) =
    of_int c * (\<Sum>t<q * q. emb i (\<xi> t) *
      emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k))" .
  then have "cmod (emb i (of_int c *
    (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l)))) =
      of_int \<bar>c\<bar> * cmod (\<Sum>t<q * q. emb i (\<xi> t) *
        emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k))"
    by (simp add: norm_mult)
  also have "... \<le> of_int \<bar>c\<bar> * (\<Sum>t<q * q.
      cmod (emb i (\<xi> t) * emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)))"
    by (intro mult_left_mono sum_norm_le) auto
  also have "... = of_int \<bar>c\<bar> * (\<Sum>t<q * q. cmod (emb i (\<xi> t)) *
        cmod (emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)))"
    by (simp add: norm_mult)
  finally show ?thesis .
qed

lemma represented_coordinate_emb_cmod_le:
  assumes "i < D"
  assumes repr: "gs_power_basis_witness_coordinates v x"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes tlt: "t < q * q"
  shows "cmod (emb i (Matrix.vec_index v t)) \<le> (of_int B :: real) * of_nat D * power_basis_entry_bound"
proof -
  let ?v' = "vec (q * q) (\<lambda>t. emb i (Matrix.vec_index v t))"
  have repr': "\<forall>t<q * q. Matrix.vec_index ?v' t =
    (\<Sum>j<D. of_int (Matrix.vec_index x (sg_pair_idx D t j)) * basis j (emb i))"
  proof (intro allI impI)
    fix t
    assume t: "t < q * q"
    have "emb i (vec_index v t) = (\<Sum>j<D. of_int (vec_index x (sg_pair_idx D t j)) * basis j (emb i))"
      using repr t emb_sum_int_power[OF \<open>i < D\<close>]
      by (simp add: gs_power_basis_witness_coordinates_def
        basis_eq_power_at_identity_embedding[OF emb0])
    then show "vec_index ?v' t = (\<Sum>j<D. of_int (vec_index x (sg_pair_idx D t j)) * basis j (emb i))"
      using t by simp
  qed
  have basis_bnd: "\<And>j. j < D \<Longrightarrow> cmod (basis j (emb i)) \<le> power_basis_entry_bound"
    by (rule basis_cmod_le_power_basis_entry_bound[OF \<open>i < D\<close>])
  have "cmod (Matrix.vec_index ?v' t) \<le>
      (of_int B :: real) * of_nat D * power_basis_entry_bound"
    by (rule cmod_repr_by_bounded_int_vec_uniform_le[OF Dpos repr' x_carrier x_bnd B_nonneg basis_bnd tlt])
  then show ?thesis using tlt by simp
qed

lemma gs_scaled_deriv_emb_uniform_bound:
  fixes V U :: real
  assumes ilt: "i < D"
  assumes coeffK: "\<And>t. t < q * q \<Longrightarrow> \<xi> t \<in> K"
  assumes Vnonneg: "0 \<le> V"
  assumes Unonneg: "0 \<le> U"
  assumes coeff_bnd: "\<And>t. t < q * q \<Longrightarrow> cmod (emb i (\<xi> t)) \<le> V"
  assumes system_bnd: "\<And>t. t < q * q \<Longrightarrow>
    cmod (emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)) \<le> U"
  shows "cmod (emb i (of_int c *
    (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l)))) \<le>
    of_int \<bar>c\<bar> * of_nat (q * q) * V * U"
proof -
  have term_bnd: "cmod (emb i (\<xi> t)) *
      cmod (emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)) \<le> V * U"
    if "t < q * q" for t
    by (intro mult_mono coeff_bnd[OF that] system_bnd[OF that]) (use Vnonneg Unonneg in auto)
  have "cmod (emb i (of_int c *
    (gs_z d powi (- int k) * ((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat l)))) \<le>
      of_int \<bar>c\<bar> * (\<Sum>t<q * q. cmod (emb i (\<xi> t)) *
        cmod (emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)))"
    by (rule gs_scaled_deriv_emb_sum_bound[OF ilt coeffK])
  also have "... \<le> of_int \<bar>c\<bar> * (\<Sum>t<q * q. V * U)"
    by (intro mult_left_mono sum_mono term_bnd) auto
  also have "... = of_int \<bar>c\<bar> * of_nat (q * q) * V * U"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma gs_system_coeff_emb_uniform_le:
  fixes H :: real
  assumes ilt: "i < D"
  assumes aq: "a \<le> q"
  assumes bq: "b \<le> q"
  assumes lm: "l \<le> m"
  assumes Hone: "1 \<le> H"
  assumes aH: "cmod (emb i (gs_a d)) \<le> H"
  assumes bH: "cmod (emb i (gs_b d)) \<le> H"
  assumes wH: "cmod (emb i (gs_w d)) \<le> H"
  shows "cmod (emb i (gs_system_coeff d a b l k)) \<le> (of_nat q * (1 + H)) ^ k * H ^ (m * q) * H ^ (m * q)"
proof -
  let ?B = "of_nat q * (1 + H)"
  have ale: "a * l \<le> m * q"
    using aq lm by (metis mult.commute mult_le_mono)
  have ble: "b * l \<le> m * q"
    using bq lm by (metis mult.commute mult_le_mono)
  have Bbound: "of_nat q * (1 + cmod (emb i (gs_b d))) \<le> ?B"
    using bH by (intro mult_left_mono) auto
  have first: "(of_nat q * (1 + cmod (emb i (gs_b d)))) ^ k \<le> ?B ^ k"
    by (rule power_mono[OF Bbound]) auto
  have second: "cmod (emb i (gs_a d)) ^ (a * l) \<le> H ^ (m * q)"
  proof -
    have "cmod (emb i (gs_a d)) ^ (a * l) \<le> H ^ (a * l)"
      by (rule power_mono[OF aH]) auto
    also have "... \<le> H ^ (m * q)"
      by (rule power_increasing) (use Hone ale in auto)
    finally show ?thesis .
  qed
  have third: "cmod (emb i (gs_w d)) ^ (b * l) \<le> H ^ (m * q)"
  proof -
    have "cmod (emb i (gs_w d)) ^ (b * l) \<le> H ^ (b * l)"
      by (rule power_mono[OF wH]) auto
    also have "... \<le> H ^ (m * q)"
      by (rule power_increasing) (use Hone ble in auto)
    finally show ?thesis .
  qed
  have "cmod (emb i (gs_system_coeff d a b l k)) \<le>
      (of_nat q * (1 + cmod (emb i (gs_b d)))) ^ k *
      cmod (emb i (gs_a d)) ^ (a * l) * cmod (emb i (gs_w d)) ^ (b * l)"
    by (rule gs_system_coeff_emb_cmod_le[OF ilt aq bq])
  also have "... \<le> ?B ^ k * H ^ (m * q) * H ^ (m * q)"
    using first second third Hone by (intro mult_mono) auto
  finally show ?thesis .
qed

definition gs_data_emb_bound :: real where
  "gs_data_emb_bound \<equiv> max 1
    (EH.ehouse (\<lambda>e. e (gs_a d)) + EH.ehouse (\<lambda>e. e (gs_b d)) + EH.ehouse (\<lambda>e. e (gs_w d)))"

lemma gs_data_emb_bound_facts:
  assumes ilt: "i < D"
  shows "1 \<le> gs_data_emb_bound"
    and "cmod (emb i (gs_a d)) \<le> gs_data_emb_bound"
    and "cmod (emb i (gs_b d)) \<le> gs_data_emb_bound"
    and "cmod (emb i (gs_w d)) \<le> gs_data_emb_bound"
proof -
  have eE: "emb i \<in> E"
    using ilt by (auto simp: E_def)
  have a_le: "cmod (emb i (gs_a d)) \<le> EH.ehouse (\<lambda>e. e (gs_a d))"
    by (rule EH.cmod_le_ehouse[OF eE])
  have b_le: "cmod (emb i (gs_b d)) \<le> EH.ehouse (\<lambda>e. e (gs_b d))"
    by (rule EH.cmod_le_ehouse[OF eE])
  have w_le: "cmod (emb i (gs_w d)) \<le> EH.ehouse (\<lambda>e. e (gs_w d))"
    by (rule EH.cmod_le_ehouse[OF eE])
  have a0: "0 \<le> EH.ehouse (\<lambda>e. e (gs_a d))" and b0: "0 \<le> EH.ehouse (\<lambda>e. e (gs_b d))" 
    and w0: "0 \<le> EH.ehouse (\<lambda>e. e (gs_w d))" by auto
  have sum_le: "EH.ehouse (\<lambda>e. e (gs_a d)) + EH.ehouse (\<lambda>e. e (gs_b d)) + EH.ehouse (\<lambda>e. e (gs_w d)) 
                \<le> gs_data_emb_bound"
    by (simp add: gs_data_emb_bound_def)
  show "1 \<le> gs_data_emb_bound"
    by (simp add: gs_data_emb_bound_def)
  show "cmod (emb i (gs_a d)) \<le> gs_data_emb_bound"
    using a_le b0 w0 sum_le by linarith
  show "cmod (emb i (gs_b d)) \<le> gs_data_emb_bound"
    using b_le a0 w0 sum_le by linarith
  show "cmod (emb i (gs_w d)) \<le> gs_data_emb_bound"
    using w_le a0 b0 sum_le by linarith
qed

lemma gs_system_coeff_emb_data_bound:
  assumes ilt: "i < D"
  assumes aq: "a \<le> q"
  assumes bq: "b \<le> q"
  assumes lm: "l \<le> m"
  shows "cmod (emb i (gs_system_coeff d a b l k)) \<le>
    (of_nat q * (1 + gs_data_emb_bound)) ^ k *
    gs_data_emb_bound ^ (m * q) * gs_data_emb_bound ^ (m * q)"
  by (rule gs_system_coeff_emb_uniform_le[OF ilt aq bq lm
      gs_data_emb_bound_facts(1)[OF ilt] gs_data_emb_bound_facts(2)[OF ilt]
      gs_data_emb_bound_facts(3)[OF ilt] gs_data_emb_bound_facts(4)[OF ilt]])

lemma gs_row_scaled_entry_emb_data_uniform_le:
  assumes ilt: "i < D"
  assumes ult: "u < gs_m h * gs_n h q"
  assumes tlt: "t < q * q"
  shows "cmod (emb i (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) \<le>
    (of_int \<bar>gs_c1 d\<bar>) ^ (gs_n h q) * (of_int \<bar>gs_c1 d\<bar>) ^ (gs_m h * q) * (of_int \<bar>gs_c1 d\<bar>) ^ (gs_m h * q) *
    (of_nat q * (1 + gs_data_emb_bound)) ^ (gs_n h q) * gs_data_emb_bound ^ (gs_m h * q) *
    gs_data_emb_bound ^ (gs_m h * q)"
proof -
  let ?m = "gs_m h"
  let ?n = "gs_n h q"
  let ?k = "gs_k_idx ?n u"
  let ?ea = "gs_a_idx q t * gs_l_idx ?n u"
  let ?eb = "gs_b_idx q t * gs_l_idx ?n u"
  let ?H = "gs_data_emb_bound"
  let ?C = "(of_int \<bar>gs_c1 d\<bar> :: real)"
  let ?B = "of_nat q * (1 + ?H)"
  let ?scale = "real_of_int \<bar>gs_row_scale d (gs_m h) (gs_n h q) q u\<bar>"
  have Hone: "1 \<le> ?H" by (rule gs_data_emb_bound_facts(1)[OF ilt])
  have aH: "cmod (emb i (gs_a d)) \<le> ?H"
    by (rule gs_data_emb_bound_facts(2)[OF ilt])
  have bH: "cmod (emb i (gs_b d)) \<le> ?H"
    by (rule gs_data_emb_bound_facts(3)[OF ilt])
  have wH: "cmod (emb i (gs_w d)) \<le> ?H"
    by (rule gs_data_emb_bound_facts(4)[OF ilt])
  have kle: "?k \<le> ?n"
    using gs_k_idx_le[OF npos, of u] by linarith
  have lle: "gs_l_idx ?n u \<le> ?m"
    by (rule gs_l_idx_le[OF npos ult])
  have ale: "gs_a_idx q t \<le> q"
    by (rule gs_a_idx_le[OF qpos tlt])
  have ble: "gs_b_idx q t \<le> q"
    by (rule gs_b_idx_le[OF qpos])
  have eale: "?ea \<le> ?m * q"
    by (simp add: ale lle mult.commute mult_le_mono)
  have eble: "?eb \<le> ?m * q"
    by (simp add: ble lle mult.commute mult_mono)
  have bone: "1 \<le> ?B"
    using Hone qpos by fastforce
  have cone: "1 \<le> ?C"
    using gelfond_schneider_data_c1_ge1[OF d] by simp
  have scale_eq: "?scale = ?C ^ ?k * ?C ^ (?m * q) * ?C ^ (?m * q)"
    unfolding gs_row_scale_def by (simp add: power_abs abs_mult algebra_simps)
  have cpower: "?C ^ ?k \<le> ?C ^ ?n"
    by (rule power_increasing) (use cone kle in auto)
  have scale_up: "?scale \<le> ?C ^ ?n * ?C ^ (?m * q) * ?C ^ (?m * q)"
    by (metis cpower scale_eq less_le_not_le mult_le_cancel_right)
  have bpow: "(of_nat q * (1 + cmod (emb i (gs_b d)))) ^ ?k \<le> ?B ^ ?n"
  proof -
    have "of_nat q * (1 + cmod (emb i (gs_b d))) \<le> ?B"
      using bH by (intro mult_left_mono) auto
    then have "(of_nat q * (1 + cmod (emb i (gs_b d)))) ^ ?k \<le> ?B ^ ?k"
      by (rule power_mono) auto
    also have "... \<le> ?B ^ ?n"
      by (rule power_increasing) (use bone kle in auto)
    finally show ?thesis .
  qed
  have apow: "cmod (emb i (gs_a d)) ^ ?ea \<le> ?H ^ (?m * q)"
    using Hone aH eale by (smt (verit, best) norm_ge_zero power_increasing power_mono)
  have wpow: "cmod (emb i (gs_w d)) ^ ?eb \<le> ?H ^ (?m * q)"
    using power_mono[OF wH] Hone eble by (smt (verit, best) norm_ge_zero power_both_mono)
  have raw: "cmod (emb i (gs_row_scaled_system_mat d ?m ?n q $$ (u,t))) \<le>
      ?scale * ((of_nat q * (1 + cmod (emb i (gs_b d)))) ^ ?k *
      cmod (emb i (gs_a d)) ^ ?ea * cmod (emb i (gs_w d)) ^ ?eb)"
    using gs_row_scaled_entry_emb_cmod_le[OF ilt qpos npos ult tlt]
    by (simp add: mult.assoc)
  have factor: "(of_nat q * (1 + cmod (emb i (gs_b d)))) ^ ?k *
      cmod (emb i (gs_a d)) ^ ?ea * cmod (emb i (gs_w d)) ^ ?eb \<le>
      ?B ^ ?n * ?H ^ (?m * q) * ?H ^ (?m * q)"
    using bpow apow wpow Hone bone by (intro mult_mono) auto
  have scale_nonneg: "0 \<le> ?scale" by simp
  have factor_nonneg: "0 \<le> ?B ^ ?n * ?H ^ (?m * q) * ?H ^ (?m * q)"
    using bone Hone by simp
  have "cmod (emb i (gs_row_scaled_system_mat d ?m ?n q $$ (u,t))) \<le>
      ?scale * (?B ^ ?n * ?H ^ (?m * q) * ?H ^ (?m * q))"
    using raw factor scale_nonneg by (meson mult_left_mono order_trans)
  also have "... \<le> (?C ^ ?n * ?C ^ (?m * q) * ?C ^ (?m * q)) *
      (?B ^ ?n * ?H ^ (?m * q) * ?H ^ (?m * q))"
    by (rule mult_right_mono[OF scale_up factor_nonneg])
  finally show ?thesis by (simp add: mult.assoc)
qed

definition gs_concrete_entry_bound :: real where
  "gs_concrete_entry_bound \<equiv>
    (of_int \<bar>gs_c1 d\<bar> :: real) ^ (gs_n h q) *
    (of_int \<bar>gs_c1 d\<bar> :: real) ^ (gs_m h * q) *
    (of_int \<bar>gs_c1 d\<bar> :: real) ^ (gs_m h * q) *
    (of_nat q * (1 + gs_data_emb_bound)) ^ (gs_n h q) *
    gs_data_emb_bound ^ (gs_m h * q) *
    gs_data_emb_bound ^ (gs_m h * q)"

lemma gs_concrete_entry_bound_nonneg:
  "0 \<le> gs_concrete_entry_bound"
  using gs_data_emb_bound_facts(1)[OF i0lt]
  unfolding gs_concrete_entry_bound_def by simp

lemma gs_row_scaled_entry_concrete_house_le:
  assumes ult: "u < gs_m h * gs_n h q"
  assumes tlt: "t < q * q"
  shows "EH.ehouse (Aemb u t) \<le> gs_concrete_entry_bound"
proof (rule EH.ehouse_leI[OF gs_concrete_entry_bound_nonneg])
  fix e
  assume eE: "e \<in> E"
  then obtain i where ilt: "i < D" and eeq: "e = emb i"
    unfolding E_def by auto
  show "cmod (Aemb u t e) \<le> gs_concrete_entry_bound"
    using gs_row_scaled_entry_emb_data_uniform_le[OF ilt ult tlt]
    by (simp add: Aemb_def eeq gs_concrete_entry_bound_def)
qed

definition gs_concrete_entry_growth_constant :: real where
  "gs_concrete_entry_growth_constant \<equiv>
    (of_int \<bar>gs_c1 d\<bar> :: real) *
    (of_int \<bar>gs_c1 d\<bar> :: real) ^ (2 * gs_m h * gs_m h) *
    (of_int \<bar>gs_c1 d\<bar> :: real) ^ (2 * gs_m h * gs_m h) *
    (sqrt (2 * of_nat (gs_m h)) * (1 + gs_data_emb_bound)) *
    gs_data_emb_bound ^ (2 * gs_m h * gs_m h) *
    gs_data_emb_bound ^ (2 * gs_m h * gs_m h)"

lemma gs_concrete_entry_bound_le_growth:
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  shows "gs_concrete_entry_bound \<le> gs_concrete_entry_growth_constant ^ r * real r powr (of_nat r / 2)"
proof -
  have prod_ge1: "1 \<le> c14 * c5"
    using c14_ge1 c5_gt1 by force
  have nle_choice: "gs_n h (gs_q_choice h (c14 * c5)) \<le> r"
    using nle by (simp add: q_def)
  have qle: "q \<le> 2 * gs_m h * r"
    using gs_q_choice_le_two_mr[OF hpos prod_ge1 nle_choice]
    by (simp add: q_def)
  have qsq: "q * q \<le> 2 * gs_m h * r"
    by (rule gs_q_sq_le_two_mr[OF dvd nle])
  have mpos: "gs_m h > 0" by simp
  have Cge1: "1 \<le> (of_int \<bar>gs_c1 d\<bar> :: real)"
    using gelfond_schneider_data_c1_ge1[OF d] by simp
  have Hge1: "1 \<le> gs_data_emb_bound"
    by (rule gs_data_emb_bound_facts(1)[OF i0lt])
  show ?thesis
    using gs_entry_power_le_r_half[OF mpos rpos nle qle qsq Cge1 Hge1]
    by (simp add: gs_concrete_entry_bound_def
      gs_concrete_entry_growth_constant_def)
qed

definition gs_witness_growth_weight :: real where
  "gs_witness_growth_weight \<equiv>
    of_nat (card E) * power_basis_inverse_bound * power_basis_entry_bound"

definition gs_witness_growth_prefactor :: real where
  "gs_witness_growth_prefactor \<equiv>
    4 * of_nat (gs_m h) * of_nat D * (1 + gs_witness_growth_weight)"

definition gs_entry_growth_envelope :: "nat \<Rightarrow> real" where
  "gs_entry_growth_envelope r \<equiv> max 1
    (gs_concrete_entry_growth_constant ^ r *
      real r powr (of_nat r / 2))"

lemma gs_concrete_entry_growth_constant_ge_one:
  "1 \<le> gs_concrete_entry_growth_constant"
proof -
  let ?C = "(of_int \<bar>gs_c1 d\<bar> :: real)"
  let ?H = "gs_data_emb_bound"
  let ?m = "gs_m h"
  have Cone: "1 \<le> ?C"
    using gelfond_schneider_data_c1_ge1[OF d] by simp
  have Hone: "1 \<le> ?H"
    by (rule gs_data_emb_bound_facts(1)[OF i0lt])
  have middle: "1 \<le> sqrt (2 * of_nat ?m) * (1 + ?H)"
    using Hone one_le_gs_m by force
  have "(1::real) * 1 * 1 * 1 * 1 * 1 \<le>
      ?C * ?C ^ (2 * ?m * ?m) * ?C ^ (2 * ?m * ?m) *
      (sqrt (2 * of_nat ?m) * (1 + ?H)) *
      ?H ^ (2 * ?m * ?m) * ?H ^ (2 * ?m * ?m)"
    by (intro mult_mono Cone middle power_increasing Hone) (use Cone Hone in auto)
  then show ?thesis by (simp add: gs_concrete_entry_growth_constant_def)
qed

lemma gs_entry_growth_envelope_eq:
  assumes rpos: "r > 0"
  shows "gs_entry_growth_envelope r = gs_concrete_entry_growth_constant ^ r * r powr (of_nat r / 2)"
proof -
  have powrone: "1 \<le> real r powr (of_nat r / 2)"
    using ge_one_powr_ge_zero rpos by auto
  have Kone: "1 \<le> gs_concrete_entry_growth_constant"
    by (rule gs_concrete_entry_growth_constant_ge_one)
  have "1 \<le> gs_concrete_entry_growth_constant ^ r * real r powr (of_nat r / 2)"
    by (simp add: Kone mult_ge1_I powrone)
  then show ?thesis by (simp add: gs_entry_growth_envelope_def)
qed

lemma gs_witness_bound_le_growth:
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  shows "(of_int (gs_kernel_witness_bound (q * q) D
    gs_witness_growth_weight gs_concrete_entry_bound) :: real) \<le>
    gs_witness_growth_prefactor * of_nat r * gs_entry_growth_envelope r"
proof -
  have qsq: "q * q \<le> 2 * gs_m h * r"
    by (rule gs_q_sq_le_two_mr[OF dvd nle])
  have Anonneg: "0 \<le> gs_concrete_entry_bound"
    by (rule gs_concrete_entry_bound_nonneg)
  have Wnonneg: "0 \<le> gs_witness_growth_weight"
    unfolding gs_witness_growth_weight_def
    using power_basis_inverse_bound_nonneg power_basis_entry_bound_nonneg by simp
  have Ale: "gs_concrete_entry_bound \<le> gs_entry_growth_envelope r"
    using gs_concrete_entry_bound_le_growth[OF nle rpos]
    by (simp add: gs_entry_growth_envelope_def)
  have Gone: "1 \<le> gs_entry_growth_envelope r"
    by (simp add: gs_entry_growth_envelope_def)
  have bound: "(of_int (gs_kernel_witness_bound (q * q) D
    gs_witness_growth_weight gs_concrete_entry_bound) :: real) \<le>
    gs_witness_growth_prefactor * of_nat r * gs_entry_growth_envelope r"
    unfolding gs_kernel_witness_bound_def gs_witness_growth_prefactor_def
    by (rule gs_witness_bound_le_growth[OF qsq Anonneg Wnonneg Ale Gone])
  show ?thesis using bound .
qed

lemma gs_row_denominator_exponent_le_order:
  assumes nle: "gs_n h q \<le> r" and rpos: "r > 0"
  shows "gs_row_denominator_exponent (gs_m h) (gs_n h q) q D \<le> (gs_row_denominator_order_exponent (gs_m h) D) * r"
proof -
  have prod_ge1: "1 \<le> c14 * c5"
    using c14_ge1 c5_gt1 by auto
  have nle_choice: "gs_n h (gs_q_choice h (c14 * c5)) \<le> r"
    using nle by (simp add: q_def)
  have "q \<le> 2 * gs_m h * r"
    using gs_q_choice_le_two_mr[OF hpos prod_ge1 nle_choice]
    by (simp add: q_def)
  then have mle: "2 * (gs_m h * q) \<le> (4 * gs_m h * gs_m h) * r"
    using le_trans mult_le_mono1 by fastforce
  have "D \<le> D * r" using rpos by simp
  then have "gs_row_denominator_exponent (gs_m h) (gs_n h q) q D \<le> r + (4 * gs_m h * gs_m h) * r + D * r"
    using nle mle unfolding gs_row_denominator_exponent_def by linarith
  also have "... = (gs_row_denominator_order_exponent (gs_m h) D) * r"
    by (simp add: gs_row_denominator_order_exponent_def algebra_simps)
  finally show ?thesis .
qed

lemma gs_row_denominator_power_le_order:
  assumes nle: "gs_n h q \<le> r"
    and rpos: "r > 0"
    and Tp: "T > (0::int)"
  shows "T ^ (gs_row_denominator_exponent (gs_m h) (gs_n h q) q D) \<le>
    (T ^ (gs_row_denominator_order_exponent (gs_m h) D)) ^ r"
proof -
  have Tge: "1 \<le> T" using Tp by simp
  have exp: "gs_row_denominator_exponent (gs_m h) (gs_n h q) q D \<le>
    (gs_row_denominator_order_exponent (gs_m h) D) * r"
    by (rule gs_row_denominator_exponent_le_order[OF nle rpos])
  have "T ^ (gs_row_denominator_exponent (gs_m h) (gs_n h q) q D) \<le>
    T ^ ((gs_row_denominator_order_exponent (gs_m h) D) * r)"
    by (rule power_increasing) (use Tge exp in auto)
  then show ?thesis by (simp only: power_mult)
qed

lemma gs_witness_bound_le_growth_simple:
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  shows "(of_int (gs_kernel_witness_bound (q * q) D
    gs_witness_growth_weight gs_concrete_entry_bound) :: real) \<le>
    gs_witness_growth_prefactor * of_nat r *
      gs_concrete_entry_growth_constant ^ r *
      real r powr (of_nat r / 2)"
  using gs_witness_bound_le_growth[OF nle rpos]
  by (simp add: gs_entry_growth_envelope_eq[OF rpos])

lemma gs_witness_bound_le_growth_with_denominator:
  assumes nle: "gs_n h q \<le> r"
    and rpos: "r > 0"
    and Tp: "T > 0"
  shows "(of_int (gs_kernel_witness_bound (q * q) D gs_witness_growth_weight
    (of_int (T ^ (gs_row_denominator_exponent (gs_m h) (gs_n h q) q D)) *
      gs_concrete_entry_bound))) \<le>
    gs_witness_growth_prefactor * of_nat r * (gs_concrete_entry_growth_constant *
        of_int (T ^ (gs_row_denominator_order_exponent (gs_m h) D))) ^ r *
      r powr (of_nat r / 2)"
proof -
  let ?N = "gs_row_denominator_exponent (gs_m h) (gs_n h q) q D"
  let ?C = "gs_row_denominator_order_exponent (gs_m h) D"
  let ?S = "of_int (T ^ ?C) :: real"
  let ?L = "of_int (T ^ ?N) :: real"
  let ?A = "?L * gs_concrete_entry_bound"
  let ?K = "gs_concrete_entry_growth_constant"
  let ?P = "real r powr (of_nat r / 2)"
  let ?G = "(?K * ?S) ^ r * ?P"
  let ?W = "gs_witness_growth_weight"
  have qsq: "q * q \<le> 2 * gs_m h * r"
    by (rule gs_q_sq_le_two_mr[OF dvd nle])
  have Anonneg: "0 \<le> ?A"
    using Tp gs_concrete_entry_bound_nonneg by simp
  have Wnonneg: "0 \<le> ?W"
    unfolding gs_witness_growth_weight_def
    using power_basis_inverse_bound_nonneg power_basis_entry_bound_nonneg by simp
  have Sle_int: "T ^ ?N \<le> (T ^ ?C) ^ r"
    by (rule gs_row_denominator_power_le_order[OF nle rpos Tp])
  have Sle_cast: "(of_int (T ^ ?N) :: real) \<le> of_int ((T ^ ?C) ^ r)"
    by (simp only: of_int_le_iff Sle_int)
  have Sle: "?L \<le> ?S ^ r"
    using Sle_cast by (simp only: of_int_power)
  have Aold: "gs_concrete_entry_bound \<le> ?K ^ r * ?P"
    by (rule gs_concrete_entry_bound_le_growth[OF nle rpos])
  have Ale: "?A \<le> ?G"
  proof -
    have "?L * gs_concrete_entry_bound \<le> ?L * (?K ^ r * ?P)"
      by (simp add: Aold Tp)
    also have "... \<le> ?S ^ r * (?K ^ r * ?P)"
      using Sle gs_concrete_entry_growth_constant_ge_one less_eq_real_def by force
    also have "... = ?G" by (simp add: power_mult_distrib ac_simps)
    finally show ?thesis .
  qed
  have Eone: "1 \<le> gs_entry_growth_envelope r"
    by (simp add: gs_entry_growth_envelope_def)
  have G_eq: "?G = ?S ^ r * gs_entry_growth_envelope r"
    by (simp add: gs_entry_growth_envelope_eq[OF rpos] power_mult_distrib ac_simps)
  have Spow: "1 \<le> ?S ^ r"
    using Tp of_int_1_le_iff one_le_power by fastforce
  have Gone: "1 \<le> ?G"
    using Eone G_eq Spow mult_ge1_I by presburger
  have bound: "(of_int (2 * int (q * q * D) * max 1 \<lceil>?W * ?A\<rceil>) :: real) \<le>
      (4 * of_nat (gs_m h) * of_nat D * (1 + ?W)) * of_nat r * ?G"
    by (rule Rho_Bounds.gs_witness_bound_le_growth [OF qsq Anonneg Wnonneg Ale Gone])
  show ?thesis using bound
    by (simp add: gs_kernel_witness_bound_def gs_witness_growth_prefactor_def
      ac_simps)
qed

lemma gs_house_aux_factor_le_growth:
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  shows "(of_int \<bar>gs_c1 d\<bar>) ^ r * (of_int \<bar>gs_c1 d\<bar>) ^ (2 * gs_m h * q) *
    (of_nat q * (1 + gs_data_emb_bound)) ^ r *
    gs_data_emb_bound ^ (gs_m h * q) * gs_data_emb_bound ^ (gs_m h * q) \<le>
    gs_concrete_entry_growth_constant ^ r * real r powr (of_nat r / 2)"
proof -
  have prod_ge1: "1 \<le> c14 * c5"
    using c14_ge1 c5_gt1 by auto
  have nle_choice: "gs_n h (gs_q_choice h (c14 * c5)) \<le> r"
    using nle by (simp add: q_def)
  have qle: "q \<le> 2 * gs_m h * r"
    using gs_q_choice_le_two_mr[OF hpos prod_ge1 nle_choice]
    by (simp add: q_def)
  have qsq: "q * q \<le> 2 * gs_m h * r"
    by (rule gs_q_sq_le_two_mr[OF dvd nle])
  have Cge1: "1 \<le> (of_int \<bar>gs_c1 d\<bar> :: real)"
    using gelfond_schneider_data_c1_ge1[OF d] by simp
  have Hge1: "1 \<le> gs_data_emb_bound"
    by (rule gs_data_emb_bound_facts(1)[OF i0lt])
  note bound = gs_entry_power_le_r_half[OF gs_m_pos rpos le_refl qle qsq Cge1 Hge1]
  have split: "real_of_int \<bar>gs_c1 d\<bar> ^ (2 * gs_m h * q) =
                 (of_int \<bar>gs_c1 d\<bar>) ^ (gs_m h * q) * (of_int \<bar>gs_c1 d\<bar>) ^ (gs_m h * q)"
    by (simp add: more_arith_simps(11) power2_eq_square power_even_eq)
  show ?thesis using bound
    by (simp only: split gs_concrete_entry_growth_constant_def)
qed

lemma represented_coordinate_in_K:
  assumes
    "gs_power_basis_witness_coordinates v x"
  assumes "t < q * q"
  shows "Matrix.vec_index v t \<in> K"
  using assms i0lt sum_int_basis_at_emb_in_K
  unfolding gs_power_basis_witness_coordinates_def by presburger

lemma gs_scaled_deriv_emb_bounded_vec_le:
  assumes "i < D"
  assumes repr: "gs_power_basis_witness_coordinates v x"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes "l \<le> gs_m h"
  shows "cmod (emb i (of_int c *
    (gs_z d powi (- int k) *
      ((deriv ^^ k) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t))) (of_nat l)))) \<le>
    of_int \<bar>c\<bar> * of_nat (q * q) *
      ((of_int B) * of_nat D * power_basis_entry_bound) *
      ((of_nat q * (1 + gs_data_emb_bound)) ^ k *
        gs_data_emb_bound ^ (gs_m h * q) *
        gs_data_emb_bound ^ (gs_m h * q))"
proof -
  let ?V = "(of_int B) * of_nat D * power_basis_entry_bound"
  let ?U = "(of_nat q * (1 + gs_data_emb_bound)) ^ k *
    gs_data_emb_bound ^ (gs_m h * q) * gs_data_emb_bound ^ (gs_m h * q)"
  have Hone: "1 \<le> gs_data_emb_bound"
    by (simp add: gs_data_emb_bound_def)
  have Vnonneg: "0 \<le> ?V"
    using B_nonneg power_basis_entry_bound_nonneg by simp
  have Unonneg: "0 \<le> ?U"
    using Hone by simp
  have coeffK: "\<And>t. t < q * q \<Longrightarrow> Matrix.vec_index v t \<in> K"
    by (rule represented_coordinate_in_K[OF repr])
  have coeffB: "\<And>t. t < q * q \<Longrightarrow>
    cmod (emb i (Matrix.vec_index v t)) \<le> ?V"
    by (rule represented_coordinate_emb_cmod_le[OF \<open>i < D\<close> repr x_carrier x_bnd B_nonneg])
  have sysB: "\<And>t. t < q * q \<Longrightarrow> cmod (emb i (gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k)) \<le> ?U"
    by (simp add: \<open>i < D\<close> \<open>l \<le> gs_m h\<close> gs_a_idx_le gs_b_idx_le gs_system_coeff_emb_data_bound qpos)
  show ?thesis
    by (rule gs_scaled_deriv_emb_uniform_bound[OF \<open>i < D\<close> coeffK Vnonneg Unonneg coeffB sysB])
qed

lemma scaled_deriv_at_nat_in_K:
  assumes coeffK: "\<forall>t<q * q. Matrix.vec_index v t \<in> K"
  shows "gs_z d powi (- int k) *
      ((deriv ^^ k) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t))) (of_nat l) \<in> K"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have "Matrix.vec_index v t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k \<in> K"
    if "t \<in> {..<q * q}" for t
    using assms gs_system_coeff_in_K that by auto
  then have "(\<Sum>t<q * q. Matrix.vec_index v t * gs_system_coeff d (gs_a_idx q t) (gs_b_idx q t) l k) \<in> K"
    by (intro KS.sum_closed) auto
  then show ?thesis
    by (simp add: gs_aux_fun_vec_deriv_at_nat[OF d])
qed

definition gs_scaled_auxiliary_multiplier :: "nat \<Rightarrow> int" where
  "gs_scaled_auxiliary_multiplier r \<equiv>
    gs_auxiliary_multiplier d (gs_m h) q r"

definition gs_scaled_auxiliary_value :: "complex vec \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> complex" where
  "gs_scaled_auxiliary_value v r c \<equiv>
    gs_auxiliary_scaled_value d (gs_m h) q v r c"

lemma rho_in_K:
  assumes repr:
    "gs_power_basis_witness_coordinates v x"
  assumes rho_def:
    "rho = gs_scaled_auxiliary_value v r c"
  shows "rho \<in> K"
proof -
  interpret KS: Subfield K
    by (rule K_subfield)
  have coeffK: "\<forall>t<q * q. Matrix.vec_index v t \<in> K"
    using repr represented_coordinate_in_K by blast
  have "gs_z d powi (- int r) * ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
          (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<in> K"
    using scaled_deriv_at_nat_in_K[OF coeffK] gs_min_order_node_eq_nat[OF gs_m_pos] by metis
  then show ?thesis
    using KS.mult_closed KS.of_int_closed
    by (simp add: rho_def gs_scaled_auxiliary_value_def gs_auxiliary_scaled_value_def)
qed

lemma rho_order_ge_n:
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
  assumes r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  shows "gs_n h q \<le> r"
proof -
  have coeff_nz: "\<exists>t<q * q. Matrix.vec_index v t \<noteq> 0"
    using v_carrier v_nz by force
  have ker_coeff:
    "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v
      gs_coeff_vec q (\<lambda>t. Matrix.vec_index v t) =
      0\<^sub>v (gs_m h * gs_n h q)"
    by (simp add: gs_coeff_vec_eqI[OF v_carrier] v_ker)
  have min_ord:
    "gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t) \<ge> gs_n h q"
    by (rule gs_min_order_ge_of_row_scaled_kernel_nonzero[OF d qpos gs_m_pos
      npos coeff_nz ker_coeff])
  show ?thesis using min_ord r_eq by linarith
qed

lemma rho_order_pos:
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes v_ker:
    "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v = 0\<^sub>v (gs_m h * gs_n h q)"
  assumes r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  shows "0 < r"
  using rho_order_ge_n[OF v_carrier v_nz v_ker r_eq] npos by linarith

lemma rho_algebraic_int_nonzero:
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
  assumes r_eq: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  assumes deriv_nz:
    "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
      (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
  assumes c_def: "c = gs_scaled_auxiliary_multiplier r"
  assumes rho_def: "rho = gs_scaled_auxiliary_value v r c"
  shows "algebraic_int rho" and "rho \<noteq> 0"
proof -
  note c_raw = c_def[unfolded gs_scaled_auxiliary_multiplier_def]
  note rho_raw = rho_def[unfolded gs_scaled_auxiliary_value_def]
  show "algebraic_int rho" "rho \<noteq> 0"
    using gs_scaled_rho_algebraic_int_nonzero
      [OF d qpos gs_m_pos v_carrier v_nz vint r_eq deriv_nz c_raw rho_raw] .
qed

lemma gs_house_rho_le_of_bounded_vec:
  assumes repr: "gs_power_basis_witness_coordinates v x"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes ai: "algebraic_int rho"
  assumes xK: "rho \<in> K"
  assumes rho_def: "rho = gs_scaled_auxiliary_value v r c"
  shows "gs_house rho \<le>
    of_int \<bar>c\<bar> * of_nat (q * q) *
      ((of_int B :: real) * of_nat D * power_basis_entry_bound) *
      ((of_nat q * (1 + gs_data_emb_bound)) ^ r *
        gs_data_emb_bound ^ (gs_m h * q) *
        gs_data_emb_bound ^ (gs_m h * q))"
proof -
  let ?H = "of_int \<bar>c\<bar> * of_nat (q * q) *
      ((of_int B :: real) * of_nat D * power_basis_entry_bound) *
      ((of_nat q * (1 + gs_data_emb_bound)) ^ r *
        gs_data_emb_bound ^ (gs_m h * q) *
        gs_data_emb_bound ^ (gs_m h * q))"
  have Hnonneg: "0 \<le> ?H"
    using B_nonneg power_basis_entry_bound_nonneg gs_data_emb_bound_facts(1)[OF i0lt] by simp
  obtain l where llt: "l < gs_m h" 
           and node: "gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t) = of_nat (Suc l)"
    by (rule gs_min_order_node_eq_nat[OF gs_m_pos])
  have lle: "Suc l \<le> gs_m h" using llt by simp
  have bound: "cmod (emb j rho) \<le> ?H" if jlt: "j < D" for j
  proof -
    have "cmod (emb j rho) = cmod (emb j (of_int c * (gs_z d powi (- int r) *
             ((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t))) (of_nat (Suc l)))))"
      by (simp add: rho_def gs_scaled_auxiliary_value_def
        gs_auxiliary_scaled_value_def node)
    also have "... \<le> ?H"
      by (rule gs_scaled_deriv_emb_bounded_vec_le[OF jlt repr x_carrier x_bnd B_nonneg lle])
    finally show ?thesis .
  qed
  show ?thesis
    by (rule gs_house_le_of_emb_bound[OF finite normal separable ai xK Hnonneg bound])
qed

context
  fixes v :: "complex vec" and x :: "int vec" and B :: int
    and rho :: complex and c :: int and r :: nat
  assumes repr: "gs_power_basis_witness_coordinates v x"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec B"
    and B_nonneg: "0 \<le> B"
    and ai: "algebraic_int rho"
    and xK: "rho \<in> K"
    and rho_def: "rho = gs_scaled_auxiliary_value v r c"
    and c_def: "c = gs_scaled_auxiliary_multiplier r"
    and nle: "gs_n h q \<le> r"
    and rpos: "r > 0"
begin

lemma gs_house_rho_le_growth:
  assumes Bbound: "(of_int B :: real) \<le>
    gs_witness_growth_prefactor * of_nat r *
      gs_concrete_entry_growth_constant ^ r *
      real r powr (of_nat r / 2)"
  shows "gs_house rho \<le>
    (2 * of_nat (gs_m h) * gs_witness_growth_prefactor *
      (of_nat D * power_basis_entry_bound)) * (gs_concrete_entry_growth_constant *
        gs_concrete_entry_growth_constant) ^ r * r powr (of_nat r + 2)"
proof -
  let ?C = "(of_int \<bar>gs_c1 d\<bar> :: real)"
  let ?H = "gs_data_emb_bound"
  let ?K = "gs_concrete_entry_growth_constant"
  let ?W = "gs_witness_growth_prefactor :: real"
  let ?E = "of_nat D * power_basis_entry_bound :: real"
  let ?F = "?C ^ r * ?C ^ (2 * gs_m h * q) * (of_nat q * (1 + ?H)) ^ r * ?H ^ (gs_m h * q) * ?H ^ (gs_m h * q)"
  have qsq: "q * q \<le> 2 * gs_m h * r"
    by (rule gs_q_sq_le_two_mr[OF dvd nle])
  have Cge: "1 \<le> ?C"
    using gelfond_schneider_data_c1_ge1[OF d] by simp
  have Hge: "1 \<le> ?H"
    by (rule gs_data_emb_bound_facts(1)[OF i0lt])
  have c_abs: "(of_int \<bar>c\<bar> :: real) = ?C ^ r * ?C ^ (2 * gs_m h * q)"
    using c_def by (simp add: gs_scaled_auxiliary_multiplier_def
      gs_auxiliary_multiplier_def abs_mult power_abs)
  have Fnonneg: "0 \<le> ?F" using Cge Hge by simp
  have Fbound: "?F \<le> ?K ^ r * real r powr (of_nat r / 2)"
    by (rule gs_house_aux_factor_le_growth[OF nle rpos])
  have Wnonneg: "0 \<le> ?W"
    using power_basis_inverse_bound_nonneg power_basis_entry_bound_nonneg
    by (simp add: gs_witness_growth_prefactor_def gs_witness_growth_weight_def)
  have Enonneg: "0 \<le> ?E"
    using power_basis_entry_bound_nonneg by simp
  note house_raw = gs_house_rho_le_of_bounded_vec[OF repr x_carrier x_bnd B_nonneg ai xK rho_def]
  have house_factor: "gs_house rho \<le> (of_nat (q * q)) * of_int B * ?E * ?F"
    using house_raw by (simp only: c_abs of_nat_mult ac_simps)
  have "(of_nat (q * q)) * of_int B * ?E * ?F \<le>
    (2 * of_nat (gs_m h) * ?W * ?E) * (?K * ?K) ^ r * real r powr (of_nat r + 2)"
    by (rule gs_house_growth_multiply[OF rpos qsq _ Fnonneg Wnonneg _ Enonneg Bbound Fbound])
      (use B_nonneg gs_concrete_entry_growth_constant_ge_one in auto)
  then show ?thesis using house_factor by simp
qed

lemma gs_house_rho_le_growth_with_factor:
  assumes Uone: "1 \<le> U"
  assumes Bbound: "(of_int B :: real) \<le>
    gs_witness_growth_prefactor * of_nat r * (gs_concrete_entry_growth_constant * U) ^ r * real r powr (of_nat r / 2)"
  shows "gs_house rho \<le>
    (2 * of_nat (gs_m h) * gs_witness_growth_prefactor *
      (of_nat D * power_basis_entry_bound)) * ((gs_concrete_entry_growth_constant * U) *
        (gs_concrete_entry_growth_constant * U)) ^ r * real r powr (of_nat r + 2)"
proof -
  let ?C = "real_of_int \<bar>gs_c1 d\<bar>"
  let ?H = "gs_data_emb_bound"
  let ?K = "gs_concrete_entry_growth_constant * U"
  let ?W = "gs_witness_growth_prefactor :: real"
  let ?E = "of_nat D * power_basis_entry_bound :: real"
  let ?F = "?C ^ r * ?C ^ (2 * gs_m h * q) *
    (of_nat q * (1 + ?H)) ^ r *
    ?H ^ (gs_m h * q) * ?H ^ (gs_m h * q)"
  have qsq: "q * q \<le> 2 * gs_m h * r"
    by (rule gs_q_sq_le_two_mr[OF dvd nle])
  have Cge: "1 \<le> ?C"
    using gelfond_schneider_data_c1_ge1[OF d] by simp
  have Hge: "1 \<le> ?H"
    by (rule gs_data_emb_bound_facts(1)[OF i0lt])
  have c_abs: "\<bar>c\<bar> = ?C ^ r * ?C ^ (2 * gs_m h * q)"
    using c_def by (simp add: gs_scaled_auxiliary_multiplier_def
      gs_auxiliary_multiplier_def abs_mult power_abs)
  have Fnonneg: "0 \<le> ?F" using Cge Hge by simp
  have Fbase: "?F \<le> gs_concrete_entry_growth_constant ^ r * r powr (of_nat r / 2)"
    by (rule gs_house_aux_factor_le_growth[OF nle rpos])
  have Kge: "1 \<le> gs_concrete_entry_growth_constant"
    by (rule gs_concrete_entry_growth_constant_ge_one)
  have Knonneg: "0 \<le> ?K" using Kge Uone by simp
  have Fbound: "?F \<le> ?K ^ r * real r powr (of_nat r / 2)"
  proof -
    have pow: "gs_concrete_entry_growth_constant ^ r \<le> ?K ^ r"
      by (rule power_mono) (use Kge Uone in auto)
    have "gs_concrete_entry_growth_constant ^ r * r powr (of_nat r / 2) 
        \<le> ?K ^ r * real r powr (of_nat r / 2)"
      by (rule mult_right_mono[OF pow]) simp
    then show ?thesis using Fbase by linarith
  qed
  have Wnonneg: "0 \<le> ?W"
    using power_basis_inverse_bound_nonneg power_basis_entry_bound_nonneg
    by (simp add: gs_witness_growth_prefactor_def gs_witness_growth_weight_def)
  have Enonneg: "0 \<le> ?E"
    using power_basis_entry_bound_nonneg by simp
  note house_raw = gs_house_rho_le_of_bounded_vec[OF repr x_carrier x_bnd B_nonneg ai xK rho_def]
  have house_factor: "gs_house rho \<le> (of_nat (q * q) :: real) * of_int B * ?E * ?F"
    using house_raw by (simp only: c_abs of_nat_mult ac_simps)
  have multiplied: "(of_nat (q * q)) * of_int B * ?E * ?F \<le>
    (2 * of_nat (gs_m h) * ?W * ?E) * (?K * ?K) ^ r * real r powr (of_nat r + 2)"
    using B_nonneg Enonneg Fbound Fnonneg Knonneg Wnonneg Bbound gs_house_growth_multiply qsq
      rpos by presburger
  show ?thesis using house_factor multiplied by simp
qed

end

definition gs_house_growth_prefactor :: real where
  "gs_house_growth_prefactor \<equiv>
    2 * of_nat (gs_m h) * gs_witness_growth_prefactor * (of_nat D * power_basis_entry_bound)"

definition gs_house_growth_base :: real where
  "gs_house_growth_base \<equiv>
    2 * max 1 gs_house_growth_prefactor *
      (gs_concrete_entry_growth_constant *
        gs_concrete_entry_growth_constant)"

lemma gs_house_growth_base_pos:
  "0 < gs_house_growth_base"
  using gs_concrete_entry_growth_constant_ge_one gs_house_growth_base_def by auto

context
  fixes v :: "complex vec" and x :: "int vec" and B :: int
    and rho :: complex and c :: int and r :: nat
  assumes repr: "gs_power_basis_witness_coordinates v x"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec B"
    and B_nonneg: "0 \<le> B"
    and ai: "algebraic_int rho"
    and xK: "rho \<in> K"
    and rho_def: "rho = gs_scaled_auxiliary_value v r c"
    and c_def: "c = gs_scaled_auxiliary_multiplier r"
    and nle: "gs_n h q \<le> r"
    and rpos: "r > 0"
begin

lemma gs_house_rho_le_growth_absorbed:
  assumes Bbound: "B \<le>
    gs_witness_growth_prefactor * of_nat r *
      gs_concrete_entry_growth_constant ^ r * r powr (of_nat r / 2)"
  shows "gs_house rho \<le> gs_house_growth_base ^ r * real r powr (gs_house_order_exponent r)"
proof -
  have Kone: "1 \<le> gs_concrete_entry_growth_constant"
    by (rule gs_concrete_entry_growth_constant_ge_one)
  have Wnonneg: "0 \<le> gs_witness_growth_weight"
    unfolding gs_witness_growth_weight_def
    using power_basis_inverse_bound_nonneg power_basis_entry_bound_nonneg by simp
  have Fnonneg: "0 \<le> gs_house_growth_prefactor"
    unfolding gs_house_growth_prefactor_def gs_witness_growth_prefactor_def
    using Wnonneg power_basis_entry_bound_nonneg by simp
  have raw: "gs_house rho \<le>
    gs_house_growth_prefactor * (gs_concrete_entry_growth_constant *
        gs_concrete_entry_growth_constant) ^ r * real r powr (of_nat r + 2)"
    using gs_house_rho_le_growth[OF repr x_carrier x_bnd B_nonneg ai xK
      rho_def c_def nle rpos Bbound]
    by (simp only: gs_house_growth_prefactor_def)
  have absorb: "gs_house_growth_prefactor * (gs_concrete_entry_growth_constant *
        gs_concrete_entry_growth_constant) ^ r *
      real r powr (of_nat r + 2) \<le> gs_house_growth_base ^ r * real r powr (gs_house_order_exponent r)"
    using gs_house_growth_absorb[OF rpos Fnonneg, of gs_concrete_entry_growth_constant]
      Kone by (simp add: gs_house_growth_base_def gs_house_order_exponent_def)
  show ?thesis using raw absorb by linarith
qed

lemma gs_house_rho_le_growth_absorbed_with_factor:
  assumes Uone: "1 \<le> U"
  assumes Bbound: "(of_int B :: real) \<le>
    gs_witness_growth_prefactor * of_nat r * (gs_concrete_entry_growth_constant * U) ^ r *
      real r powr (of_nat r / 2)"
  shows "gs_house rho \<le> (gs_house_growth_base * U ^ 2) ^ r * real r powr (gs_house_order_exponent r)"
proof -
  have Kbase: "1 \<le> gs_concrete_entry_growth_constant"
    by (rule gs_concrete_entry_growth_constant_ge_one)
  have Kone: "1 \<le> gs_concrete_entry_growth_constant * U"
    using Kbase assms(1) by blast
  have Wnonneg: "0 \<le> gs_witness_growth_weight"
    unfolding gs_witness_growth_weight_def
    using power_basis_inverse_bound_nonneg power_basis_entry_bound_nonneg by simp
  have Fnonneg: "0 \<le> gs_house_growth_prefactor"
    unfolding gs_house_growth_prefactor_def gs_witness_growth_prefactor_def
    using Wnonneg power_basis_entry_bound_nonneg by simp
  have raw: "gs_house rho \<le>
    gs_house_growth_prefactor * ((gs_concrete_entry_growth_constant * U) *
        (gs_concrete_entry_growth_constant * U)) ^ r * real r powr (of_nat r + 2)"
    using gs_house_rho_le_growth_with_factor[OF repr x_carrier x_bnd B_nonneg ai xK
      rho_def c_def nle rpos Uone Bbound]
    by (simp only: gs_house_growth_prefactor_def)
  have absorb: "gs_house_growth_prefactor * ((gs_concrete_entry_growth_constant * U) *
        (gs_concrete_entry_growth_constant * U)) ^ r *
      real r powr (of_nat r + 2) \<le> (gs_house_growth_base * U ^ 2) ^ r * real r powr (gs_house_order_exponent r)"
    using gs_house_growth_absorb[OF rpos Fnonneg, of "gs_concrete_entry_growth_constant * U"]
      Kone by (simp add: gs_house_growth_base_def gs_house_order_exponent_def
        power2_eq_square algebra_simps)
  show ?thesis using raw absorb by linarith
qed

end

definition gs_point_scale_base :: real where
  "gs_point_scale_base \<equiv>
    (of_int \<bar>gs_c1 d\<bar> :: real) * (of_int \<bar>gs_c1 d\<bar> :: real) ^ (4 * gs_m h * gs_m h)"

definition gs_point_fixed_base :: real where
  "gs_point_fixed_base \<equiv> gs_point_scale_base * inverse (cmod (gs_z d)) *
                          exp (of_nat (gs_m h) * (2 * of_nat (gs_m h) + 1) *
                          (1 + cmod (gs_b d)) * cmod (gs_z d)) *
                          (2 * of_nat (gs_m h) + 1) ^ (gs_m h)"

lemma gs_point_fixed_base_pos: "0 < gs_point_fixed_base"
proof -
  have Cge: "1 \<le> (of_int \<bar>gs_c1 d\<bar> :: real)"
    using gelfond_schneider_data_c1_ge1[OF d] by simp
  have zpos: "0 < cmod (gs_z d)"
    using gelfond_schneider_data_z_nonzero[OF d] by simp
  show ?thesis using Cge zpos
    by (simp add: gs_point_fixed_base_def gs_point_scale_base_def)
qed

lemma gs_rho_fixed_factor_le_growth:
  assumes c_def: "c = gs_scaled_auxiliary_multiplier r"
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  shows "(of_int \<bar>c\<bar>) * cmod (gs_z d powi (- int r)) *
    exp ((of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)) *
      (of_nat (gs_m h) * (1 + of_nat r / of_nat q))) *
    (2 * of_nat (gs_m h) + 1) ^ (gs_m h * r) \<le>
    gs_point_fixed_base ^ r"
proof -
  let ?C = "(of_int \<bar>gs_c1 d\<bar> :: real)"
  let ?m = "gs_m h"
  let ?Z = "inverse (cmod (gs_z d))"
  let ?X = "exp (of_nat ?m * (2 * of_nat ?m + 1) *
      (1 + cmod (gs_b d)) * cmod (gs_z d))"
  let ?P = "2 * of_nat ?m + 1 :: real"
  have prod_ge1: "1 \<le> c14 * c5"
    using c14_ge1 c5_gt1 by force
  have nle_choice: "gs_n h (gs_q_choice h (c14 * c5)) \<le> r"
    using nle by (simp add: q_def)
  have qle: "q \<le> 2 * ?m * r"
    using gs_q_choice_le_two_mr[OF hpos prod_ge1 nle_choice]
    by (simp add: q_def)
  have Cge: "1 \<le> ?C"
    using gelfond_schneider_data_c1_ge1[OF d] by simp
  have scale: "real_of_int \<bar>c\<bar> \<le> gs_point_scale_base ^ r"
  proof -
    have eq: "(of_int \<bar>c\<bar> :: real) = ?C ^ r * ?C ^ (2 * ?m * q)"
      using c_def by (simp add: gs_scaled_auxiliary_multiplier_def
        gs_auxiliary_multiplier_def abs_mult power_abs)
    show ?thesis using gs_scale_factor_le_r_power[OF qle Cge]
      by (simp only: eq gs_point_scale_base_def)
  qed
  have z_eq: "cmod (gs_z d powi (- int r)) = ?Z ^ r"
    by (rule gs_negative_powi_norm[OF gelfond_schneider_data_z_nonzero[OF d]])
  have exp_le: "exp ((of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)) *
      (of_nat ?m * (1 + of_nat r / of_nat q))) \<le> ?X ^ r"
    by (rule gs_aux_exp_growth_le[OF qpos qle])
  have p_eq: "?P ^ (?m * r) = (?P ^ ?m) ^ r"
    by (simp add: power_mult)
  have nonneg: "0 \<le> (of_int \<bar>c\<bar> :: real)" by simp
  have all: "(of_int \<bar>c\<bar> :: real) * cmod (gs_z d powi (- int r)) *
    exp ((of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)) *
      (of_nat ?m * (1 + of_nat r / of_nat q))) * ?P ^ (?m * r) \<le>
    gs_point_scale_base ^ r * ?Z ^ r * ?X ^ r * (?P ^ ?m) ^ r"
    using scale exp_le z_eq p_eq
    by (intro mult_mono) (use nonneg in auto)
  show ?thesis using all
    by (simp add: gs_point_fixed_base_def power_mult_distrib ac_simps)
qed

lemma gs_rho_cmod_le_of_bounded_vec:
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v =
    0\<^sub>v (gs_m h * gs_n h q)"
  assumes repr: "gs_power_basis_witness_coordinates v x"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec B"
  assumes B_nonneg: "0 \<le> B"
  assumes req: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  assumes rho_def: "rho = gs_scaled_auxiliary_value v r c"
  shows "cmod rho \<le> of_int \<bar>c\<bar> * cmod (gs_z d powi (- int r)) *
    (fact r * (of_nat (q * q) *
      ((of_int B) * of_nat D * power_basis_entry_bound) *
      exp ((of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)) *
        (of_nat (gs_m h) * (1 + of_nat r / of_nat q))) /
      (of_nat (gs_m h) * of_nat r / of_nat q) ^ (gs_m h * r)) *
      (2 * of_nat (gs_m h) + 1) ^ (gs_m h * r))"
proof -
  let ?B = "fact r * (of_nat (q * q) *
      ((of_int B) * of_nat D * power_basis_entry_bound) *
      exp ((of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)) *
        (of_nat (gs_m h) * (1 + of_nat r / of_nat q))) /
      (of_nat (gs_m h) * of_nat r / of_nat q) ^ (gs_m h * r)) *
      (2 * of_nat (gs_m h) + 1) ^ (gs_m h * r)"
  have c5ge: "1 \<le> c5" using c5_gt1 by linarith
  have c15ge: "1 \<le> c14 * c5"
    using c14_ge1 c5ge by auto
  have qge: "4 \<le> q"
    unfolding q_def by (rule gs_q_choice_ge_four[OF hpos c15ge])
  have bal: "q * q = 2 * gs_m h * gs_n h q"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have coeff_nz: "\<exists>t<q * q. Matrix.vec_index v t \<noteq> 0"
    using v_carrier v_nz by force
  have ker_coeff: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v
      gs_coeff_vec q (\<lambda>t. Matrix.vec_index v t) =
      0\<^sub>v (gs_m h * gs_n h q)"
    by (simp add: gs_coeff_vec_eqI[OF v_carrier] v_ker)
  have min_ord: "gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t) \<ge> gs_n h q"
    by (rule gs_min_order_ge_of_row_scaled_kernel_nonzero[OF d qpos gs_m_pos npos coeff_nz ker_coeff])
  have nle: "gs_n h q \<le> r"
    using min_ord req by linarith
  have rpos: "r > 0"
    by (rule rho_order_pos[OF v_carrier v_nz v_ker req])
  have nz: "gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t) \<noteq> (\<lambda>_. 0)"
    by (rule gs_aux_fun_vec_nonzero[OF d qpos coeff_nz])
  have basis_bnd: "\<And>j. j < D \<Longrightarrow> cmod (basis j (emb i0)) \<le> power_basis_entry_bound"
    by (rule basis_cmod_le_power_basis_entry_bound[OF i0lt])
  have deriv_bound: "cmod (((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
      (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))) \<le> ?B"
    by (rule gs_bounded_vec_min_order_derivative_bound[OF qge bal nle gs_m_pos rpos Dpos
        repr[unfolded gs_power_basis_witness_coordinates_def] x_carrier x_bnd
        B_nonneg power_basis_entry_bound_nonneg basis_bnd nz req])
  have "cmod rho = of_int \<bar>c\<bar> * cmod (gs_z d powi (- int r)) *
      cmod (((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
        (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)))"
    by (simp add: rho_def gs_scaled_auxiliary_value_def
      gs_auxiliary_scaled_value_def norm_mult)
  also have "... \<le> of_int \<bar>c\<bar> * cmod (gs_z d powi (- int r)) * ?B"
    using deriv_bound by (intro mult_left_mono mult_right_mono) auto
  finally show ?thesis .
qed

definition gs_point_growth_prefactor :: real where
  "gs_point_growth_prefactor \<equiv>
    2 * of_nat (gs_m h) *
      gs_witness_growth_prefactor *
      (of_nat D * power_basis_entry_bound)"

definition gs_point_growth_base :: real where
  "gs_point_growth_base \<equiv>
    2 * max 1 gs_point_growth_prefactor *
      (gs_concrete_entry_growth_constant * gs_point_fixed_base)"

definition gs_norm_growth_base :: "real \<Rightarrow> real" where
  "gs_norm_growth_base U \<equiv>
    (gs_house_growth_base * U ^ 2) ^ (D - 1) * (gs_point_growth_base * U)"

lemma gs_point_growth_base_pos:
  "0 < gs_point_growth_base"
  using gs_concrete_entry_growth_constant_ge_one gs_point_fixed_base_pos
  by (simp add: gs_point_growth_base_def)

context
  fixes v :: "complex vec" and x :: "int vec" and B :: int
    and rho :: complex and c :: int and r :: nat
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
    and v_nz: "v \<noteq> 0\<^sub>v (q * q)"
    and v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v =
      0\<^sub>v (gs_m h * gs_n h q)"
    and repr: "gs_power_basis_witness_coordinates v x"
    and x_carrier: "x \<in> carrier_vec (q * q * D)"
    and x_bnd: "x \<in> Bounded_vec B"
    and B_nonneg: "0 \<le> B"
    and req: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
    and rho_def: "rho = gs_scaled_auxiliary_value v r c"
    and c_def: "c = gs_scaled_auxiliary_multiplier r"
    and nle: "gs_n h q \<le> r"
    and rpos: "r > 0"
begin

lemma gs_rho_cmod_le_growth_absorbed:
  assumes Bbound: "(of_int B :: real) \<le>
    gs_witness_growth_prefactor * of_nat r * gs_concrete_entry_growth_constant ^ r * r powr (of_nat r / 2)"
  shows "cmod rho \<le> gs_point_growth_base ^ r *
         r powr (gs_point_order_exponent (gs_m h) r)"
proof -
  let ?m = "gs_m h"
  let ?R = "real r"
  let ?W = "gs_witness_growth_prefactor"
  let ?E = "of_nat D * power_basis_entry_bound :: real"
  let ?K = "gs_concrete_entry_growth_constant"
  let ?L = "gs_point_fixed_base"
  let ?radius = "(of_nat ?m * ?R / of_nat q :: real) ^ (?m * r)"
  let ?G = "(of_int \<bar>c\<bar> :: real) * cmod (gs_z d powi (- int r)) *
    exp ((of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)) *
      (of_nat ?m * (1 + ?R / of_nat q))) *
    (2 * of_nat ?m + 1) ^ (?m * r)"
  have bal: "q * q = 2 * ?m * gs_n h q"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have qsq: "q * q \<le> 2 * ?m * r"
    by (simp add: bal nle)
  have mge: "2 \<le> ?m" by (simp add: gs_m_def)
  have radbound: "?R powr (of_nat ?m * ?R / 2) \<le> ?radius"
    by (rule gs_balanced_radius_power_ge[OF qpos mge rpos qsq])
  have Gbound: "?G \<le> ?L ^ r"
    by (rule gs_rho_fixed_factor_le_growth[OF c_def nle rpos])
  have Gnonneg: "0 \<le> ?G" by simp
  have Wnonneg: "0 \<le> ?W"
    using power_basis_inverse_bound_nonneg power_basis_entry_bound_nonneg
    by (simp add: gs_witness_growth_prefactor_def gs_witness_growth_weight_def)
  have Enonneg: "0 \<le> ?E"
    using power_basis_entry_bound_nonneg by simp
  have Knonneg: "0 \<le> ?K"
    using gs_concrete_entry_growth_constant_ge_one by linarith
  have Lnonneg: "0 \<le> ?L"
    using gs_point_fixed_base_pos by linarith
  have Bnonneg: "0 \<le> (of_int B :: real)" using B_nonneg by simp
  note raw = gs_rho_cmod_le_of_bounded_vec[OF v_carrier v_nz v_ker repr
    x_carrier x_bnd B_nonneg req rho_def]
  have raw_refactor: "cmod rho \<le> ((of_nat (q * q) * of_int B * fact r * ?G) / ?radius) * ?E"
    using raw by (simp add: ac_simps)
  have point_num: "(((of_nat (q * q) :: real) * of_int B * fact r * ?G) /
      ?radius) \<le> (2 * of_nat ?m * ?W) * (?K * ?L) ^ r *
        ?R powr (?R * (3 - of_nat ?m) / 2 + 2)"
    by (rule gs_point_growth_multiply[OF rpos qsq Bnonneg Gnonneg Wnonneg
      Knonneg Lnonneg Bbound Gbound radbound])
  have point_pref: "cmod rho \<le> gs_point_growth_prefactor *
      (?K * ?L) ^ r * ?R powr (?R * (3 - of_nat ?m) / 2 + 2)"
  proof -
    have "(((of_nat (q * q) :: real) * of_int B * fact r * ?G) /
        ?radius) * ?E \<le> ((2 * of_nat ?m * ?W) * (?K * ?L) ^ r *
          ?R powr (?R * (3 - of_nat ?m) / 2 + 2)) * ?E"
      by (rule mult_right_mono[OF point_num Enonneg])
    then show ?thesis using raw_refactor
      by (simp add: gs_point_growth_prefactor_def ac_simps)
  qed
  have Wscaled: "0 \<le> 2 * of_nat ?m * ?W"
    by (rule mult_nonneg_nonneg) (use Wnonneg in auto)
  have pref_eq: "gs_point_growth_prefactor = (2 * of_nat ?m * ?W) * ?E"
    by (simp only: gs_point_growth_prefactor_def)
  have Fnonneg: "0 \<le> gs_point_growth_prefactor"
    by (simp add: Wnonneg pref_eq)
  have absorb: "gs_point_growth_prefactor * (?K * ?L) ^ r *
                   ?R powr (?R * (3 - of_nat ?m) / 2 + 2) \<le>
                   gs_point_growth_base ^ r * ?R powr (?R * (3 - of_nat ?m) / 2 + 3 / 2)"
    by (simp add: Fnonneg Knonneg Lnonneg gs_point_growth_absorb gs_point_growth_base_def rpos)
  show ?thesis using point_pref absorb
    by (simp add: gs_point_order_exponent_def)
qed

lemma gs_rho_cmod_le_growth_absorbed_with_factor:
  assumes Uone: "1 \<le> U"
  assumes Bbound: "(of_int B) \<le>
    gs_witness_growth_prefactor * of_nat r * (gs_concrete_entry_growth_constant * U) ^ r *
      real r powr (of_nat r / 2)"
  shows "cmod rho \<le> (gs_point_growth_base * U) ^ r *
         r powr (gs_point_order_exponent (gs_m h) r)"
proof -
  let ?m = "gs_m h"
  let ?R = "real r"
  let ?W = "gs_witness_growth_prefactor"
  let ?E = "of_nat D * power_basis_entry_bound :: real"
  let ?K = "gs_concrete_entry_growth_constant * U"
  let ?L = "gs_point_fixed_base"
  let ?radius = "(of_nat ?m * ?R / of_nat q :: real) ^ (?m * r)"
  let ?G = "(of_int \<bar>c\<bar> :: real) * cmod (gs_z d powi (- int r)) *
    exp ((of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)) *
      (of_nat ?m * (1 + ?R / of_nat q))) *
    (2 * of_nat ?m + 1) ^ (?m * r)"
  have bal: "q * q = 2 * ?m * gs_n h q"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have qsq: "q * q \<le> 2 * ?m * r"
    by (simp add: bal nle)
  have mge: "2 \<le> ?m" by (simp add: gs_m_def)
  have radbound: "?R powr (of_nat ?m * ?R / 2) \<le> ?radius"
    by (rule gs_balanced_radius_power_ge[OF qpos mge rpos qsq])
  have Gbound: "?G \<le> ?L ^ r"
    by (rule gs_rho_fixed_factor_le_growth[OF c_def nle rpos])
  have Gnonneg: "0 \<le> ?G" by simp
  have Wnonneg: "0 \<le> ?W"
    using power_basis_inverse_bound_nonneg power_basis_entry_bound_nonneg
    by (simp add: gs_witness_growth_prefactor_def gs_witness_growth_weight_def)
  have Enonneg: "0 \<le> ?E"
    using power_basis_entry_bound_nonneg by simp
  have Knonneg: "0 \<le> ?K"
    using gs_concrete_entry_growth_constant_ge_one Uone by simp
  have Lnonneg: "0 \<le> ?L"
    using gs_point_fixed_base_pos by linarith
  have Bnonneg: "0 \<le> (of_int B :: real)" using B_nonneg by simp
  note raw = gs_rho_cmod_le_of_bounded_vec[OF v_carrier v_nz v_ker repr
    x_carrier x_bnd B_nonneg req rho_def]
  have raw_refactor: "cmod rho \<le> ((real (q * q) * of_int B * fact r * ?G) / ?radius) * ?E"
    using raw by argo
  have point_num: "(((of_nat (q * q) :: real) * of_int B * fact r * ?G) /
      ?radius) \<le> (2 * of_nat ?m * ?W) * (?K * ?L) ^ r *
        ?R powr (?R * (3 - of_nat ?m) / 2 + 2)"
    by (rule gs_point_growth_multiply[OF rpos qsq Bnonneg Gnonneg Wnonneg
          Knonneg Lnonneg Bbound Gbound radbound])
  have "(((of_nat (q * q) :: real) * of_int B * fact r * ?G) /
        ?radius) * ?E \<le> ((2 * of_nat ?m * ?W) * (?K * ?L) ^ r *
          ?R powr (?R * (3 - of_nat ?m) / 2 + 2)) * ?E"
    by (rule mult_right_mono[OF point_num Enonneg])
  then have point_pref: "cmod rho \<le> gs_point_growth_prefactor *
      (?K * ?L) ^ r * ?R powr (?R * (3 - of_nat ?m) / 2 + 2)"
    using raw_refactor by (simp add: gs_point_growth_prefactor_def ac_simps)
  have Fnonneg: "0 \<le> gs_point_growth_prefactor"
    by (simp add: Wnonneg gs_point_growth_prefactor_def)
  have base_eq: "gs_point_growth_base * U = 2 * max 1 gs_point_growth_prefactor * (?K * ?L)"
    by (simp add: gs_point_growth_base_def algebra_simps)
  have "0 \<le> ?K * ?L" using Knonneg Lnonneg by simp
  then have absorb: "gs_point_growth_prefactor * (?K * ?L) ^ r *
      ?R powr (?R * (3 - of_nat ?m) / 2 + 2) \<le>
      (gs_point_growth_base * U) ^ r * ?R powr (?R * (3 - of_nat ?m) / 2 + 3 / 2)"
    using Fnonneg base_eq gs_point_growth_absorb rpos by presburger
  then show ?thesis using point_pref
    by (simp add: gs_point_order_exponent_def)
qed

end

lemma gs_norm_upper_from_concrete_house_point:
  assumes hD: "h = D"
  assumes xK: "rho \<in> K"
  assumes ai: "algebraic_int rho"
  assumes rpos: "r > 0"
  assumes house_bound: "gs_house rho \<le> gs_house_growth_base ^ r * real r powr (gs_house_order_exponent r)"
  assumes point_bound: "cmod rho \<le> gs_point_growth_base ^ r *
               r powr (gs_point_order_exponent (gs_m h) r)"
  assumes c14_big: "gs_house_growth_base ^ (D - 1) *
    gs_point_growth_base \<le> c14"
  shows "gs_abs_galois_norm rho \<le>
    c14 powr of_nat r * real r powr (gs_norm_order_exponent h r)"
proof -
  have emb0_rho: "emb i0 rho = rho"
    using xK by (simp add: emb0 identity_apply_in_K)
  have point_power: "gs_point_growth_base ^ r =
      gs_point_growth_base powr of_nat r"
    by (simp only: powr_realpow[OF gs_point_growth_base_pos])
  have point_exponent: "real r *
      (3 - of_nat (gs_m h)) / 2 + 3 / 2 =
      of_nat r * (3 - of_nat (2 * D + 2)) / 2 + 3 / 2"
    using hD by (simp add: gs_m_def)
  have point_le: "cmod (emb i0 rho) \<le>
      gs_point_growth_base powr of_nat r *
      r powr (of_nat r * (3 - of_nat (2 * D + 2)) / 2 + 3 / 2)"
    using point_bound
    by (simp only: emb0_rho point_power point_exponent gs_point_order_exponent_def)
  have house_le: "gs_house rho \<le>
      gs_house_growth_base powr of_nat r *
        real r powr (gs_house_order_exponent r)"
    using house_bound by (simp add: powr_realpow[OF gs_house_growth_base_pos])
  have norm_le: "gs_abs_galois_norm rho \<le>
      (gs_house_growth_base ^ (D - 1) * gs_point_growth_base) powr of_nat r *
        real r powr (- of_nat r / 2 + 3 * of_nat D / 2)"
    by (rule gs_abs_galois_norm_le_from_analytic_house_bounds[OF i0lt xK ai
      gs_house_growth_base_pos gs_point_growth_base_pos rpos
      house_le[unfolded gs_house_order_exponent_def] point_le])
  have base_nonneg: "0 \<le> gs_house_growth_base ^ (D - 1) * gs_point_growth_base"
    using gs_house_growth_base_pos gs_point_growth_base_pos by simp
  have base_le: "(gs_house_growth_base ^ (D - 1) * gs_point_growth_base)
      powr of_nat r \<le> c14 powr of_nat r"
    by (rule powr_mono2[OF _ base_nonneg c14_big]) simp
  have rp_nonneg: "0 \<le> real r powr (- of_nat r / 2 + 3 * of_nat D / 2)"
    by simp
  show ?thesis using norm_le base_le rp_nonneg hD
    by (intro order_trans[OF norm_le]) (simp add: gs_norm_order_exponent_def mult_right_mono)
qed

lemma gs_norm_upper_from_concrete_house_point_with_factor:
  assumes hD: "h = D"
  assumes xK: "rho \<in> K"
  assumes ai: "algebraic_int rho"
  assumes rpos: "r > 0"
  assumes Uone: "1 \<le> U"
  assumes house_bound: "gs_house rho \<le> (gs_house_growth_base * U ^ 2) ^ r * real r powr (gs_house_order_exponent r)"
  assumes point_bound: "cmod rho \<le> (gs_point_growth_base * U) ^ r *
                                      r powr (gs_point_order_exponent (gs_m h) r)"
  assumes c14_big: "gs_norm_growth_base U \<le> c14"
  shows "gs_abs_galois_norm rho \<le> c14 powr of_nat r * real r powr (gs_norm_order_exponent h r)"
proof -
  have house_pos: "0 < (gs_house_growth_base * U ^ 2)"
    using gs_house_growth_base_pos Uone by simp
  have point_pos: "0 < (gs_point_growth_base * U)"
    using gs_point_growth_base_pos Uone by simp
  have emb0_rho: "emb i0 rho = rho"
    using xK by (simp add: emb0 identity_apply_in_K)
  have point_power: "(gs_point_growth_base * U) ^ r =
      (gs_point_growth_base * U) powr of_nat r"
    by (simp only: powr_realpow[OF point_pos])
  have point_exponent: "real r * (3 - of_nat (gs_m h)) / 2 + 3 / 2 = of_nat r * (3 - of_nat (2 * D + 2)) / 2 + 3 / 2"
    using hD by (simp add: gs_m_def)
  have point_le: "cmod (emb i0 rho) \<le>
      (gs_point_growth_base * U) powr of_nat r *
      r powr (of_nat r * (3 - of_nat (2 * D + 2)) / 2 + 3 / 2)"
    using point_bound
    by (simp only: emb0_rho point_power point_exponent gs_point_order_exponent_def)
  have house_le: "gs_house rho \<le>
      (gs_house_growth_base * U ^ 2) powr of_nat r *
        real r powr (gs_house_order_exponent r)"
    using house_bound by (simp add: powr_realpow[OF house_pos])
  have norm_le: "gs_abs_galois_norm rho \<le>
      ((gs_house_growth_base * U ^ 2) ^ (D - 1) * (gs_point_growth_base * U)) powr of_nat r *
        real r powr (- of_nat r / 2 + 3 * of_nat D / 2)"
    by (rule gs_abs_galois_norm_le_from_analytic_house_bounds[OF i0lt xK ai
      house_pos point_pos rpos house_le[unfolded gs_house_order_exponent_def] point_le])
  have base_nonneg: "0 \<le> gs_norm_growth_base U"
    using house_pos point_pos by (simp add: gs_norm_growth_base_def)
  have base_le: "(gs_norm_growth_base U)
      powr of_nat r \<le> c14 powr of_nat r"
    by (rule powr_mono2[OF _ base_nonneg c14_big]) simp
  have rp_nonneg: "0 \<le> real r powr (- of_nat r / 2 + 3 * of_nat D / 2)"
    by simp
  have norm_le': "gs_abs_galois_norm rho \<le>
      gs_norm_growth_base U powr of_nat r *
        real r powr (- of_nat r / 2 + 3 * of_nat D / 2)"
    using norm_le by (simp only: gs_norm_growth_base_def)
  show ?thesis using norm_le' base_le rp_nonneg hD
    by (intro order_trans[OF norm_le']) (simp add: gs_norm_order_exponent_def mult_right_mono)
qed

lemma gs_rho_upper_from_concrete_witness:
  assumes hD: "h = D"
  assumes A_choice: "A = gs_concrete_entry_bound"
  assumes c14_big: "gs_house_growth_base ^ (D - 1) *
    gs_point_growth_base \<le> c14"
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v =
    0\<^sub>v (gs_m h * gs_n h q)"
  assumes repr: "gs_power_basis_witness_coordinates v x"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec
    (gs_kernel_witness_bound (q * q) D gs_witness_growth_weight A)"
  assumes req: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  assumes rho_def: "rho = gs_scaled_auxiliary_value v r c"
  assumes c_def: "c = gs_scaled_auxiliary_multiplier r"
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  assumes ai: "algebraic_int rho"
  assumes xK: "rho \<in> K"
  shows "gs_abs_galois_norm rho \<le>
    c14 powr of_nat r *
      real r powr (gs_norm_order_exponent h r)"
proof -
  let ?B = "gs_kernel_witness_bound (q * q) D gs_witness_growth_weight A"
  have Bnonneg: "0 \<le> ?B" by (simp add: gs_kernel_witness_bound_def)
  have Bbound: "(of_int ?B :: real) \<le>
    gs_witness_growth_prefactor * of_nat r * gs_concrete_entry_growth_constant ^ r * real r powr (of_nat r / 2)"
    using gs_witness_bound_le_growth_simple[OF nle rpos]
    by (simp only: A_choice)
  have house: "gs_house rho \<le> gs_house_growth_base ^ r * real r powr (gs_house_order_exponent r)"
    by (rule gs_house_rho_le_growth_absorbed[OF repr x_carrier x_bnd
      Bnonneg ai xK rho_def c_def nle rpos Bbound])
  have point: "cmod rho \<le> gs_point_growth_base ^ r *
                          r powr (gs_point_order_exponent (gs_m h) r)"
    by (rule gs_rho_cmod_le_growth_absorbed[OF v_carrier v_nz v_ker repr
      x_carrier x_bnd Bnonneg req rho_def c_def nle rpos Bbound])
  show ?thesis
    by (rule gs_norm_upper_from_concrete_house_point[OF hD xK ai rpos house point c14_big])
qed

lemma gs_rho_upper_from_concrete_witness_with_denominator:
  assumes hD: "h = D"
  assumes A_choice: "A = gs_concrete_entry_bound"
  assumes Tp: "T > (0::int)"
  assumes c14_big:
    "gs_norm_growth_base
      (of_int (T ^ (gs_row_denominator_order_exponent (gs_m h) D))) \<le> c14"
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v =
    0\<^sub>v (gs_m h * gs_n h q)"
  assumes repr: "gs_power_basis_witness_coordinates v x"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec
    (gs_kernel_witness_bound (q * q) D gs_witness_growth_weight
      (of_int (T ^ (gs_row_denominator_exponent (gs_m h) (gs_n h q) q D)) * A))"
  assumes req: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  assumes rho_def: "rho = gs_scaled_auxiliary_value v r c"
  assumes c_def: "c = gs_scaled_auxiliary_multiplier r"
  assumes nle: "gs_n h q \<le> r"
  assumes rpos: "r > 0"
  assumes ai: "algebraic_int rho"
  assumes xK: "rho \<in> K"
  shows "gs_abs_galois_norm rho \<le> c14 powr of_nat r * real r powr (gs_norm_order_exponent h r)"
proof -
  let ?U = "of_int (T ^ (gs_row_denominator_order_exponent (gs_m h) D)) :: real"
  have Uone: "1 \<le> ?U"
    using Tp by fastforce
  let ?B = "gs_kernel_witness_bound (q * q) D gs_witness_growth_weight
    (of_int (T ^ (gs_row_denominator_exponent (gs_m h) (gs_n h q) q D)) * A)"
  have Bnonneg: "0 \<le> ?B" by (simp add: gs_kernel_witness_bound_def)
  have Bbound: "?B \<le> gs_witness_growth_prefactor * of_nat r *
    (gs_concrete_entry_growth_constant * ?U) ^ r * real r powr (of_nat r / 2)"
    using gs_witness_bound_le_growth_with_denominator[OF nle rpos Tp] A_choice by auto
  have house: "gs_house rho \<le> (gs_house_growth_base * ?U ^ 2) ^ r * real r powr (gs_house_order_exponent r)"
    by (rule gs_house_rho_le_growth_absorbed_with_factor[OF repr x_carrier x_bnd
      Bnonneg ai xK rho_def c_def nle rpos Uone Bbound])
  have point: "cmod rho \<le> (gs_point_growth_base * ?U) ^ r *
                           r powr (gs_point_order_exponent (gs_m h) r)"
    by (rule gs_rho_cmod_le_growth_absorbed_with_factor[OF v_carrier v_nz v_ker repr
      x_carrier x_bnd Bnonneg req rho_def c_def nle rpos Uone Bbound])
  show ?thesis
    by (rule gs_norm_upper_from_concrete_house_point_with_factor[OF hD xK ai rpos
      Uone house point c14_big])
qed

lemma gs_rho_upper_verified:
  assumes hD: "h = D"
  assumes A_choice: "A = gs_concrete_entry_bound"
  assumes c14_big: "gs_house_growth_base ^ (D - 1) *
    gs_point_growth_base \<le> c14"
  assumes v_carrier: "v \<in> carrier_vec (q * q)"
  assumes v_nz: "v \<noteq> 0\<^sub>v (q * q)"
  assumes v_ker: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q *\<^sub>v v =
    0\<^sub>v (gs_m h * gs_n h q)"
  assumes vint: "\<forall>i<q * q. algebraic_int (Matrix.vec_index v i)"
  assumes repr: "gs_power_basis_witness_coordinates v x"
  assumes x_carrier: "x \<in> carrier_vec (q * q * D)"
  assumes x_nz: "x \<noteq> 0\<^sub>v (q * q * D)"
  assumes x_bnd: "x \<in> Bounded_vec
    (gs_kernel_witness_bound (q * q) D gs_witness_growth_weight A)"
  assumes req: "r = nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  assumes deriv_nz: "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
    (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
  assumes c_def: "c = gs_scaled_auxiliary_multiplier r"
  assumes rho_def: "rho = gs_scaled_auxiliary_value v r c"
  shows "gs_abs_galois_norm rho \<le>
        c14 powr of_nat r *
        of_nat r powr (gs_norm_order_exponent h r)"
proof -
  have nle: "gs_n h q \<le> r"
    by (rule rho_order_ge_n[OF v_carrier v_nz v_ker req])
  have rpos: "r > 0"
    by (rule rho_order_pos[OF v_carrier v_nz v_ker req])
  have ai: "algebraic_int rho"
    by (rule rho_algebraic_int_nonzero(1)[OF v_carrier v_nz vint req
      deriv_nz c_def rho_def])
  have xK: "rho \<in> K"
    by (rule rho_in_K[OF repr rho_def])
  show "gs_abs_galois_norm rho \<le> c14 powr of_nat r * real r powr (gs_norm_order_exponent h r)"
    by (rule gs_rho_upper_from_concrete_witness[OF hD A_choice c14_big
      v_carrier v_nz v_ker repr x_carrier x_bnd req rho_def c_def nle rpos ai xK])
qed

end

lemma finite_Rats_common_denominator:
  fixes F :: "complex set"
  assumes finite: "finite F"
    and rat: "F \<subseteq> \<rat>"
  shows "\<exists>L::int. L > 0 \<and> (\<forall>x\<in>F. \<exists>z::int. of_int L * x = of_int z)"
using finite rat
proof (induction F rule: finite_induct)
  case empty
  show ?case by (intro exI[of _ 1]) simp
next
  case (insert x F)
  have xr: "x \<in> \<rat>" using insert.prems by auto
  obtain a b where bp: "b > 0" and xe: "x = of_int a / of_int b"
    using Rats_cases'[OF xr] by blast
  obtain L::int where Lp: "L > 0" and Le: "\<forall>y\<in>F. \<exists>z::int. of_int L * y = of_int z"
    using insert.IH insert.prems by auto
  have all: "\<forall>y\<in>insert x F. \<exists>z::int. of_int (b * L) * y = of_int z"
  proof (intro ballI)
    fix y
    assume yin: "y \<in> insert x F"
    show "\<exists>z::int. of_int (b * L) * y = of_int z"
    proof (cases "y = x")
      case True
      show ?thesis using bp xe True
        by (intro exI[of _ "L * a"]) (simp add: field_simps)
    next
      case False
      then have yf: "y \<in> F" using yin by simp
      obtain z::int where yz: "of_int L * y = of_int z" using Le yf by blast
      show ?thesis using yz
        by (intro exI[of _ "b * z"]) (simp add: algebra_simps)
    qed
  qed
  show ?case using bp Lp all by (intro exI[of _ "b * L"]) simp
qed

lemma integer_reduction_of_powers_from_monic_relation:
  fixes eta :: complex
  assumes Dpos: "D > 0"
    and red: "eta ^ D = (\<Sum>k<D. of_int (a k) * eta ^ k)"
  shows "\<exists>c::nat \<Rightarrow> int. eta ^ n = (\<Sum>k<D. of_int (c k) * eta ^ k)"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < D")
    case True
    let ?c = "\<lambda>k. if k = n then (1::int) else 0"
    have "eta ^ n = (\<Sum>k<D. of_int (?c k) * eta ^ k)"
      using True by (simp add: if_distrib [of "\<lambda>x . of_int x * eta ^ _"] cong: if_cong)
    then show ?thesis by force
  next
    case False
    then have Dn: "D \<le> n" by simp
    have exp_lt: "n - D + k < n" if kd: "k < D" for k
      using kd Dn by simp
    then have each: "\<forall>k<D. \<exists>c::nat \<Rightarrow> int. eta ^ (n - D + k) = (\<Sum>j<D. of_int (c j) * eta ^ j)"
      using less.IH by blast
    then obtain c where c: "\<forall>k<D. eta ^ (n - D + k) = (\<Sum>j<D. of_int (c k j) * eta ^ j)"
      by metis
    have nsplit: "n = (n - D) + D" using Dn by simp
    have "eta ^ n = eta ^ (n - D) * (\<Sum>k<D. of_int (a k) * eta ^ k)"
      by (metis nsplit red power_add)
    also have "... = (\<Sum>k<D. of_int (a k) * eta ^ (n - D + k))"
      by (simp add: sum_distrib_left power_add algebra_simps)
    also have "... = (\<Sum>k<D. of_int (a k) * (\<Sum>j<D. of_int (c k j) * eta ^ j))"
      using c by (intro sum.cong[OF refl]) auto
    also have "... = (\<Sum>k<D. \<Sum>j<D. of_int (a k * c k j) * eta ^ j)"
      by (simp add: sum_distrib_left algebra_simps)
    also have "... = (\<Sum>j<D. \<Sum>k<D. of_int (a k * c k j) * eta ^ j)"
      by (rule sum.swap)
    also have "... = (\<Sum>j<D. of_int (\<Sum>k<D. a k * c k j) * eta ^ j)"
      by (simp add: sum_distrib_right)
    finally have eq: "eta ^ n = (\<Sum>j<D.
      of_int (\<Sum>k<D. a k * c k j) * eta ^ j)" .
    show ?thesis by (rule exI[of _ "\<lambda>j. \<Sum>k<D. a k * c k j"])
      (rule eq)
  qed
qed

lemma scaled_integer_power_basis_coordinate_mul:
  fixes eta x y :: complex
    and c :: "nat \<Rightarrow> int"
    and C :: "nat \<Rightarrow> nat \<Rightarrow> int"
  assumes y_rep: "of_int (T ^ s) * y = (\<Sum>j<D. of_int (c j) * eta ^ j)"
    and x_rep: "\<And>j. j < D \<Longrightarrow> of_int T * (x * eta ^ j) = (\<Sum>k<D. of_int (C j k) * eta ^ k)"
  shows "of_int (T ^ (s + 1)) * (x * y) = (\<Sum>k<D. of_int (\<Sum>j<D. c j * C j k) * eta ^ k)"
proof -
  have "of_int (T ^ (s + 1)) * (x * y) = (\<Sum>j<D. of_int (c j) * (of_int T * (x * eta ^ j)))"
    using y_rep by (simp add: sum_distrib_left power_Suc algebra_simps)
  also have "... = (\<Sum>j<D. of_int (c j) *
      (\<Sum>k<D. of_int (C j k) * eta ^ k))"
    by (intro sum.cong[OF refl]) (use x_rep in auto)
  also have "... = (\<Sum>j<D. \<Sum>k<D.
      of_int (c j * C j k) * eta ^ k)"
    by (simp add: sum_distrib_left algebra_simps)
  also have "... = (\<Sum>k<D. \<Sum>j<D.
      of_int (c j * C j k) * eta ^ k)"
    by (rule sum.swap)
  also have "... = (\<Sum>k<D.
      of_int (\<Sum>j<D. c j * C j k) * eta ^ k)"
    by (simp add: sum_distrib_right)
  finally show ?thesis .
qed

lemma scaled_integer_affine_power_basis_coordinate:
  fixes eta beta :: complex
    and C :: "nat \<Rightarrow> nat \<Rightarrow> int"
  assumes jlt: "j < D"
    and beta_rep: "of_int T * (beta * eta ^ j) =
      (\<Sum>k<D. of_int (C j k) * eta ^ k)"
  shows "of_int T * ((of_nat a + of_nat b * beta) * eta ^ j) =
    (\<Sum>k<D. of_int ((if k = j then T * int a else 0) +
      int b * C j k) * eta ^ k)"
proof -
  have delta: "(\<Sum>k<D. of_int (if k = j then T * int a else 0) * eta ^ k) =
      of_int (T * int a) * eta ^ j"
    using jlt by (simp add: if_distrib [of "\<lambda>x . of_int x * eta ^ _"] cong: if_cong)
  have "of_int T * ((of_nat a + of_nat b * beta) * eta ^ j) =
       of_int (T * int a) * eta ^ j + of_nat b * (\<Sum>k<D. of_int (C j k) * eta ^ k)"
    using beta_rep by (simp add: algebra_simps )
  also have "... = (\<Sum>k<D. of_int ((if k = j then T * int a else 0) + int b * C j k) * eta ^ k)"
    using delta by (simp add: sum.distrib sum_distrib_left algebra_simps)
  finally show ?thesis .
qed

lemma scaled_integer_power_basis_coordinates_prod_list:
  fixes eta :: complex
    and S :: "complex set"
    and C :: "complex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes Dpos: "D > 0"
    and reps: "\<And>x j. x \<in> S \<Longrightarrow> j < D \<Longrightarrow> of_int T * (x * eta ^ j) = (\<Sum>k<D. of_int (C x j k) * eta ^ k)"
    and xsS: "set xs \<subseteq> S"
  shows "\<exists>c. of_int (T ^ length xs) * prod_list xs = (\<Sum>k<D. of_int (c k) * eta ^ k)"
using xsS
proof (induction xs)
  case Nil
  let ?c = "\<lambda>k. if k = 0 then (1::int) else 0"
  have "of_int (T ^ length []) * prod_list [] = (\<Sum>k<D. of_int (?c k) * eta ^ k)"
    using Dpos by (simp add: if_distrib [of "\<lambda>x . of_int x * eta ^ _"] cong: if_cong)
  then show ?case by force
next
  case (Cons x xs)
  have xS: "x \<in> S" and restS: "set xs \<subseteq> S"
    using Cons.prems by auto
  obtain c where crep:
    "of_int (T ^ length xs) * prod_list xs = (\<Sum>j<D. of_int (c j) * eta ^ j)"
    using Cons.IH[OF restS] by blast
  let ?c = "\<lambda>k. \<Sum>j<D. c j * C x j k"
  have "of_int (T ^ length (x # xs)) * prod_list (x # xs) = (\<Sum>k<D. of_int (?c k) * eta ^ k)"
    using scaled_integer_power_basis_coordinate_mul[OF crep reps[OF xS]]
    by simp
  then show ?case
    by (intro exI[of _ ?c]) force
qed

lemma scaled_integer_power_basis_coordinates_prod_list_weak:
  fixes eta :: complex
    and S :: "complex set"
  assumes Dpos: "D > 0"
    and reps: "\<And>x j. x \<in> S \<Longrightarrow> j < D \<Longrightarrow>
      \<exists>c::nat \<Rightarrow> int. of_int T * (x * eta ^ j) = (\<Sum>k<D. of_int (c k) * eta ^ k)"
    and xsS: "set xs \<subseteq> S"
  shows "\<exists>c::nat \<Rightarrow> int.
    of_int (T ^ length xs) * prod_list xs = (\<Sum>k<D. of_int (c k) * eta ^ k)"
proof -
  define C :: "complex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
    "C = (\<lambda>x j. SOME c. of_int T * (x * eta ^ j) = (\<Sum>k<D. of_int (c k) * eta ^ k))"
  have rep: "of_int T * (x * eta ^ j) = (\<Sum>k<D. of_int (C x j k) * eta ^ k)"
    if xS: "x \<in> S" and jD: "j < D" for x j
  proof -
    have ex: "\<exists>c::nat \<Rightarrow> int. of_int T * (x * eta ^ j) = (\<Sum>k<D. of_int (c k) * eta ^ k)"
      by (rule reps[OF xS jD])
    show ?thesis using someI_ex[OF ex] by (simp only: C_def)
  qed
  show ?thesis
    by (rule scaled_integer_power_basis_coordinates_prod_list[OF Dpos rep xsS])
qed

definition gs_system_coeff_factor_list ::
  "gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex list"
  where "gs_system_coeff_factor_list d a b l k \<equiv>
    replicate k (gs_affine_coeff d a b) @
    replicate (a * l) (gs_a d) @ replicate (b * l) (gs_w d)"

lemma gs_system_coeff_factor_list_product:
  "prod_list (gs_system_coeff_factor_list d a b l k) =
    gs_system_coeff d a b l k"
  by (simp add: gs_system_coeff_factor_list_def gs_system_coeff_def)

lemma gs_system_coeff_factor_list_length:
  "length (gs_system_coeff_factor_list d a b l k) = gs_system_coeff_factor_count a b l k"
  by (simp add: gs_system_coeff_factor_list_def gs_system_coeff_factor_count_def)

lemma gs_system_coeff_factor_list_members:
  "\<forall>x\<in>set (gs_system_coeff_factor_list d a b l k).
    x = gs_a d \<or> x = gs_w d \<or>
      (\<exists>u v::nat. x = of_nat u + of_nat v * gs_b d)"
  by (auto simp: gs_system_coeff_factor_list_def gs_affine_coeff_def)

lemma scaled_integer_power_basis_coordinate_pad_exponent:
  fixes eta y :: complex
    and c :: "nat \<Rightarrow> int"
  assumes eN: "e \<le> N"
    and rep: "of_int (T ^ e) * y = (\<Sum>j<D. of_int (c j) * eta ^ j)"
  shows "of_int (T ^ N) * y = (\<Sum>j<D. of_int (T ^ (N - e) * c j) * eta ^ j)"
proof -
  have Nsplit: "N = (N - e) + e" using eN by simp
  have "T ^ N = T ^ ((N - e) + e)"
    by (rule arg_cong[OF Nsplit])
  also have "... = T ^ (N - e) * T ^ e"
    by (simp only: power_add)
  finally have pow: "T ^ N = T ^ (N - e) * T ^ e" .
  have "of_int (T ^ N) * y = of_int (T ^ (N - e)) * (of_int (T ^ e) * y)"
    by (simp only: pow of_int_mult mult.assoc)
  also have "... = of_int (T ^ (N - e)) *
      (\<Sum>j<D. of_int (c j) * eta ^ j)"
    by (simp only: rep)
  also have "... = (\<Sum>j<D. of_int (T ^ (N - e) * c j) * eta ^ j)"
    by (simp add: sum_distrib_left algebra_simps)
  finally show ?thesis .
qed

lemma complex_smult_mat_vec:
  fixes A :: "complex mat"
  assumes A: "A \<in> carrier_mat p q"
    and v: "v \<in> carrier_vec q"
  shows "(a \<cdot>\<^sub>m A) *\<^sub>v v = a \<cdot>\<^sub>v (A *\<^sub>v v)"
proof (rule eq_vecI)
  show "dim_vec ((a \<cdot>\<^sub>m A) *\<^sub>v v) = dim_vec (a \<cdot>\<^sub>v (A *\<^sub>v v))"
    using A v by (simp add: smult_mat_def map_mat_def)
next
  fix i
  assume i: "i < dim_vec (a \<cdot>\<^sub>v (A *\<^sub>v v))"
  then have ip: "i < p" using A v by simp
  have "((a \<cdot>\<^sub>m A) *\<^sub>v v) $ i =
      (\<Sum>j<q. (a * A $$ (i,j)) * v $ j)"
    using A v ip by (simp add: index_mult_mat_vec smult_mat_def map_mat_def scalar_prod_def atLeast0LessThan)
  also have "... = a * (\<Sum>j<q. A $$ (i,j) * v $ j)"
    by (simp add: sum_distrib_left algebra_simps)
  also have "... = (a \<cdot>\<^sub>v (A *\<^sub>v v)) $ i"
    using A v ip by (simp add: index_mult_mat_vec scalar_prod_def atLeast0LessThan)
  finally show "((a \<cdot>\<^sub>m A) *\<^sub>v v) $ i =
      (a \<cdot>\<^sub>v (A *\<^sub>v v)) $ i" .
qed

theorem bounded_kernel_of_scaled_integer_structure_constants:
  fixes A :: "complex mat"
    and basis :: "nat \<Rightarrow> complex"
    and C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes A: "A \<in> carrier_mat p q"
    and ppos: "p > 0"
    and dpos: "d > 0"
    and hpq: "2 * p \<le> q"
    and Lnz: "L \<noteq> (0::int)"
    and mult_repr: "\<And>u t j. u < p \<Longrightarrow> t < q \<Longrightarrow> j < d \<Longrightarrow>
      of_int L * (A $$ (u,t) * basis j) =
        (\<Sum>k<d. of_int (C u t k j) * basis k)"
    and C_bnd: "\<And>u t k j. u < p \<Longrightarrow> t < q \<Longrightarrow>
      k < d \<Longrightarrow> j < d \<Longrightarrow> \<bar>C u t k j\<bar> \<le> Bnd"
    and basis_indep: "\<And>c. (\<Sum>j<d. of_int (c j) * basis j) = 0 \<Longrightarrow>
      (\<forall>j<d. c j = 0)"
  obtains v :: "complex vec" and x :: "int vec" where
    "v \<in> carrier_vec q"
    "v \<noteq> 0\<^sub>v q"
    "x \<in> carrier_vec (q * d)"
    "x \<noteq> 0\<^sub>v (q * d)"
    "A *\<^sub>v v = 0\<^sub>v p"
    "\<forall>t<q. v $ t = (\<Sum>j<d. of_int (x $ sg_pair_idx d t j) * basis j)"
    "x \<in> Bounded_vec (2 * int (q * d) * max 1 Bnd)"
proof -
  let ?T = "of_int L \<cdot>\<^sub>m A"
  have Tcar: "?T \<in> carrier_mat p q"
    using A by (simp add: smult_mat_def map_mat_def)
  have Trep: "?T $$ (u,t) * basis j =
      (\<Sum>k<d. of_int (C u t k j) * basis k)"
    if up: "u < p" and tq: "t < q" and jd: "j < d" for u t j
    using mult_repr[OF up tq jd] A up tq
    by (simp add: smult_mat_def map_mat_def algebra_simps)
  obtain v x where W: "bounded_basis_kernel ?T p q d basis (2 * int (q * d) * max 1 Bnd) v x"
    by (rule exists_nonzero_bounded_kernel_vec_of_structure_constants_linear
      [OF Tcar ppos dpos hpq Trep C_bnd basis_indep])
  interpret bounded_basis_kernel ?T p q d basis "2 * int (q * d) * max 1 Bnd" v x
    using W by blast
  have scaled0: "of_int L \<cdot>\<^sub>v (A *\<^sub>v v) = 0\<^sub>v p"
    using kernel complex_smult_mat_vec[OF A v_carrier] by simp
  have Aker: "A *\<^sub>v v = 0\<^sub>v p"
  proof (rule eq_vecI)
    show "dim_vec (A *\<^sub>v v) = dim_vec (0\<^sub>v p)" using A v_carrier by simp
  next
    fix i
    assume ip: "i < dim_vec (0\<^sub>v p)"
    have ai: "i < dim_vec (A *\<^sub>v v)" using A ip by simp
    have comp: "(of_int L \<cdot>\<^sub>v (A *\<^sub>v v)) $ i = of_int L * (A *\<^sub>v v) $ i"
      using ai by (simp only: smult_vec_def index_vec)
    have zero: "(of_int L \<cdot>\<^sub>v (A *\<^sub>v v)) $ i = 0"
      using scaled0 ip by simp
    have "of_int L * (A *\<^sub>v v) $ i = 0" using comp zero by simp
    then show "(A *\<^sub>v v) $ i = (0\<^sub>v p) $ i"
      using Lnz ip by simp
  qed
  show thesis
    using Aker coordinates that v_carrier v_nonzero x_bounded x_carrier x_nonzero
    by presburger
qed

context finite_normal_galois_power_basis
begin

definition uniform_denominator_factor :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> bool"
  where "uniform_denominator_factor a b w x \<equiv>
    x = a \<or> x = w \<or> x = eta \<or> (\<exists>u v::nat. x = of_nat u + of_nat v * b)"

definition uniform_product_denominator :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> int \<Rightarrow> bool"
  where "uniform_product_denominator a b w T \<equiv>
    (\<forall>xs. (\<forall>x\<in>set xs. uniform_denominator_factor a b w x) \<longrightarrow>
      (\<exists>c. of_int (T ^ length xs) * prod_list xs = (\<Sum>k<D. of_int (c k) * eta ^ k)))"

definition gs_denominator_factor :: "gelfond_schneider_data \<Rightarrow> complex \<Rightarrow> bool"
  where "gs_denominator_factor d x \<equiv>
    uniform_denominator_factor (gs_a d) (gs_b d) (gs_w d) x"

definition gs_uniform_product_denominator :: "gelfond_schneider_data \<Rightarrow> int \<Rightarrow> bool"
  where "gs_uniform_product_denominator d T \<equiv>
    uniform_product_denominator (gs_a d) (gs_b d) (gs_w d) T"

lemma gs_uniform_product_denominatorD:
  assumes prod: "gs_uniform_product_denominator d T"
    and factors: "\<forall>x\<in>set xs. gs_denominator_factor d x"
  shows "\<exists>c::nat \<Rightarrow> int.
    of_int (T ^ length xs) * prod_list xs =
      (\<Sum>i<D. of_int (c i) * eta ^ i)"
  using assms
  unfolding gs_uniform_product_denominator_def uniform_product_denominator_def
    gs_denominator_factor_def by blast

lemma rational_coordinates_of_product:
  assumes xK: "x \<in> K"
  shows "\<exists>c. (\<forall>k<D. c k \<in> \<rat>) \<and>
    x * eta ^ j = (\<Sum>k<D. c k * eta ^ k)"
proof -
  interpret KS: Subfield K by (rule K_subfield)
  have xjK: "x * eta ^ j \<in> K"
    by (rule KS.mult_closed[OF xK KS.power_closed[OF eta_in_K]])
  from Subfield.power_basis_span[OF Rats_subfield algQ, of "x * eta ^ j"] xjK
  show ?thesis by (simp add: K_def D_def)
qed

lemma finite_entries_have_scaled_integer_structure_constants:
  assumes Sfin: "finite S"
    and SK: "S \<subseteq> K"
  shows "\<exists>L::int. \<exists>C::complex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int.
    L > 0 \<and> (\<forall>x\<in>S. \<forall>j<D.
      of_int L * (x * eta ^ j) = (\<Sum>k<D. of_int (C x j k) * eta ^ k))"
proof -
  have ex: "\<exists>f. (\<forall>k<D. f k \<in> \<rat>) \<and> x * eta ^ j = (\<Sum>k<D. f k * eta ^ k)"
    if xS: "x \<in> S" for x j
    using SK rational_coordinates_of_product that by blast
  then obtain c where c: "\<And>j. \<forall>x \<in> S. (\<forall>k<D. c x j k \<in> \<rat>) \<and> x * eta ^ j = (\<Sum>k<D. c x j k * eta ^ k)"
    by metis
  let ?F = "(\<Union>x\<in>S. \<Union>j\<in>{..<D}. c x j ` {..<D})"
  have Ffin: "finite ?F" using Sfin by simp
  have Frat: "?F \<subseteq> \<rat>"
    using c by force
  obtain L::int where Lp: "L > 0"
    and Le: "\<forall>z\<in>?F. \<exists>n::int. of_int L * z = of_int n"
    using finite_Rats_common_denominator[OF Ffin Frat] by blast
  define C where "C \<equiv> (\<lambda>x j k. SOME n. of_int L * c x j k = of_int n)"
  have LC: "of_int L * c x j k = of_int (C x j k)"
    if xS: "x \<in> S" and jD: "j < D" and kD: "k < D" for x j k
  proof -
    have mem: "c x j k \<in> ?F" using xS jD kD by auto
    have ex: "\<exists>n::int. of_int L * c x j k = of_int n" using Le mem by blast
    show ?thesis using someI_ex[OF ex] by (simp only: C_def)
  qed
  have eq: "of_int L * (x * eta ^ j) = (\<Sum>k<D. of_int (C x j k) * eta ^ k)"
    if "x \<in> S" and "j < D" for x j
    using c \<open>x \<in> S\<close> LC[OF that] 
    by (auto simp add: sum_distrib_left algebra_simps intro!: sum.cong)
  show ?thesis by (intro exI[of _ L] exI[of _ C]) (use Lp eq in auto)
qed

lemma finite_K_generators_have_uniform_product_denominator:
  assumes Sfin: "finite S"
    and SK: "S \<subseteq> K"
  shows "\<exists>T::int. T > 0 \<and> (\<forall>xs. set xs \<subseteq> S \<longrightarrow>
    (\<exists>c::nat \<Rightarrow> int. of_int (T ^ length xs) * prod_list xs = (\<Sum>k<D. of_int (c k) * eta ^ k)))"
proof -
  obtain T::int and C::"complex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
    where "T > 0"
      and rep: "\<forall>x\<in>S. \<forall>j<D. of_int T * (x * eta ^ j) = (\<Sum>k<D. of_int (C x j k) * eta ^ k)"
    using finite_entries_have_scaled_integer_structure_constants[OF Sfin SK] by blast
  then have product_rep: "\<exists>c. of_int (T ^ length xs) * prod_list xs = (\<Sum>k<D. of_int (c k) * eta ^ k)"
    if "set xs \<subseteq> S" for xs
    using scaled_integer_power_basis_coordinates_prod_list[OF Dpos _ that] by auto
  with \<open>T>0\<close> show ?thesis by (intro exI[of _ T]) auto
qed

lemma data_generators_and_affines_uniform_product_denominator:
  assumes aK: "a \<in> K"
    and bK: "b \<in> K"
    and wK: "w \<in> K"
  shows "\<exists>T::int. T > 0 \<and> uniform_product_denominator a b w T"
proof -
  let ?S = "{a,b,w,eta}"
  have Sfin: "finite ?S" by simp
  have SK: "?S \<subseteq> K" using aK bK wK eta_in_K by auto
  obtain T::int and C::"complex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
    where Tp: "T > 0"
      and rep: "\<forall>x\<in>?S. \<forall>j<D. of_int T * (x * eta ^ j) =
        (\<Sum>k<D. of_int (C x j k) * eta ^ k)"
    using finite_entries_have_scaled_integer_structure_constants[OF Sfin SK] by blast
  let ?A = "{x::complex. x = a \<or> x = w \<or> x = eta \<or> (\<exists>u v::nat. x = of_nat u + of_nat v * b)}"
  have arep: "\<exists>c::nat \<Rightarrow> int. of_int T * (x * eta ^ j) =
      (\<Sum>k<D. of_int (c k) * eta ^ k)"
    if xA: "x \<in> ?A" and jd: "j < D" for x j
  proof -
    consider (a) "x = a" | (w) "x = w" | (eta) "x = eta" |
      (aff) u v where "x = of_nat u + of_nat v * b"
      using xA by auto
    then show ?thesis
    proof cases
      case (aff u v)
      have brep: "of_int T * (b * eta ^ j) = (\<Sum>k<D. of_int (C b j k) * eta ^ k)"
        using rep jd by auto
      have affrep: "of_int T * ((of_nat u + of_nat v * b) * eta ^ j) =
        (\<Sum>k<D. of_int ((if k = j then T * int u else 0) + int v * C b j k) * eta ^ k)"
        using brep scaled_integer_affine_power_basis_coordinate jd by blast
      show ?thesis using affrep aff
        by (intro exI[of _ "\<lambda>k. (if k = j then T * int u else 0) + int v * C b j k"]) simp
    qed (use rep jd in blast)+
  qed
  have "\<exists>c. of_int (T ^ length xs) * prod_list xs = (\<Sum>k<D. of_int (c k) * eta ^ k)"
    if xsA: "set xs \<subseteq> ?A" for xs
    by (rule scaled_integer_power_basis_coordinates_prod_list_weak[OF Dpos arep xsA])
  then show ?thesis
    unfolding uniform_product_denominator_def uniform_denominator_factor_def
    using Tp by (intro exI[of _ T]) fastforce
qed

theorem system_coefficients_have_uniform_exponential_denominator:
  assumes coords: "rational_power_basis_coordinates D eta ca cb cw (gs_a d) (gs_b d) (gs_w d)"
  shows "\<exists>T::int. T > 0 \<and> (\<forall>a b l k.
    \<exists>c::nat \<Rightarrow> int.
      of_int (T ^ (gs_system_coeff_factor_count a b l k)) * gs_system_coeff d a b l k =
        (\<Sum>j<D. of_int (c j) * eta ^ j))"
proof -
  interpret rational_power_basis_coordinates D eta ca cb cw "gs_a d" "gs_b d" "gs_w d"
    using assms by blast
  obtain aK: "gs_a d \<in> K" and bK: "gs_b d \<in> K" and wK: "gs_w d \<in> K"
    using a_eq b_eq ca_rat cb_rat cw_rat w_eq sum_rat_power_in_K
    by presburger
  obtain T::int where Tp: "T > 0"
    and prod: "gs_uniform_product_denominator d T"
    using data_generators_and_affines_uniform_product_denominator
      [OF aK bK wK]
    unfolding gs_uniform_product_denominator_def by blast
  have one: "\<exists>c. of_int (T ^ (gs_system_coeff_factor_count a b l k)) * gs_system_coeff d a b l k =
        (\<Sum>j<D. of_int (c j) * eta ^ j)" for a b l k
  proof -
    let ?xs = "gs_system_coeff_factor_list d a b l k"
    have mem: "\<forall>x\<in>set ?xs. gs_denominator_factor d x"
      using gs_system_coeff_factor_list_members
      unfolding gs_denominator_factor_def uniform_denominator_factor_def
      by blast
    have "\<exists>c::nat \<Rightarrow> int.
      of_int (T ^ length ?xs) * prod_list ?xs =
        (\<Sum>j<D. of_int (c j) * eta ^ j)"
      by (rule gs_uniform_product_denominatorD[OF prod mem])
    then show ?thesis
      by (simp only: gs_system_coeff_factor_list_length
        gs_system_coeff_factor_list_product)
  qed
  show ?thesis by (intro exI[of _ T]) (use Tp one in auto)
qed

lemma system_coefficients_times_basis_from_product_denominator:
  fixes T :: int
  assumes prod: "gs_uniform_product_denominator d T"
  shows "\<exists>c. of_int (T ^ (gs_system_coeff_factor_count a b l k + j)) * (gs_system_coeff d a b l k * eta ^ j) =
      (\<Sum>i<D. of_int (c i) * eta ^ i)"
proof -
  let ?xs = "gs_system_coeff_factor_list d a b l k @ replicate j eta"
  have mem: "\<forall>x\<in>set ?xs. gs_denominator_factor d x"
    by (auto simp: gs_denominator_factor_def uniform_denominator_factor_def
        gs_system_coeff_factor_list_def gs_affine_coeff_def)
  have ex: "\<exists>c. of_int (T ^ length ?xs) * prod_list ?xs = (\<Sum>i<D. of_int (c i) * eta ^ i)"
    by (rule gs_uniform_product_denominatorD[OF prod mem])
  show ?thesis using ex
    by (simp add: gs_system_coeff_factor_list_length
        gs_system_coeff_factor_list_product)
qed

theorem system_coefficients_times_basis_have_uniform_denominator:
  assumes coords: "rational_power_basis_coordinates D eta ca cb cw (gs_a d) (gs_b d) (gs_w d)"
  shows "\<exists>T::int. T > 0 \<and> (\<forall>a b l k j.
    \<exists>c. of_int (T ^ (gs_system_coeff_factor_count a b l k + j)) * (gs_system_coeff d a b l k * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i))"
proof -
  interpret rational_power_basis_coordinates D eta ca cb cw "gs_a d" "gs_b d" "gs_w d"
    using assms by blast
  obtain aK: "gs_a d \<in> K" and bK: "gs_b d \<in> K" and wK: "gs_w d \<in> K"
    using a_eq b_eq ca_rat cb_rat cw_rat w_eq sum_rat_power_in_K
    by presburger
  obtain T::int where Tp: "T > 0"
    and prod: "gs_uniform_product_denominator d T"
    using data_generators_and_affines_uniform_product_denominator [OF aK bK wK]
    unfolding gs_uniform_product_denominator_def by blast
  have one: "\<exists>c. of_int (T ^ (gs_system_coeff_factor_count a b l k + j)) * (gs_system_coeff d a b l k * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i)" for a b l k j
  proof -
    let ?xs = "gs_system_coeff_factor_list d a b l k @ replicate j eta"
    have mem: "\<forall>x\<in>set ?xs. gs_denominator_factor d x"
      by (auto simp: gs_denominator_factor_def uniform_denominator_factor_def
        gs_system_coeff_factor_list_def gs_affine_coeff_def)
    have ex: "\<exists>c::nat \<Rightarrow> int.
      of_int (T ^ length ?xs) * prod_list ?xs = (\<Sum>i<D. of_int (c i) * eta ^ i)"
      by (rule gs_uniform_product_denominatorD[OF prod mem])
    show ?thesis using ex
      by (simp add: gs_system_coeff_factor_list_length gs_system_coeff_factor_list_product)
  qed
  show ?thesis by (intro exI[of _ T]) (use Tp one in auto)
qed

lemma gs_system_coeff_idx_basis_exponent_le:
  assumes npos: "gs_n h q > 0"
    and qpos: "q > 0"
    and ult: "u < gs_m h * gs_n h q"
    and tlt: "t < q * q"
    and jlt: "j < D"
  shows "gs_k_idx (gs_n h q) u + gs_a_idx q t * gs_l_idx (gs_n h q) u + gs_b_idx q t * gs_l_idx (gs_n h q) u + j
      \<le> gs_row_denominator_exponent (gs_m h) (gs_n h q) q D"
proof -
  have kle: "gs_k_idx (gs_n h q) u \<le> gs_n h q"
    using gs_k_idx_le[OF npos, of u] by linarith
  have lle: "gs_l_idx (gs_n h q) u \<le> gs_m h"
    by (rule gs_l_idx_le[OF npos ult])
  have ale: "gs_a_idx q t \<le> q"
    by (rule gs_a_idx_le[OF qpos tlt])
  have ble: "gs_b_idx q t \<le> q"
    by (rule gs_b_idx_le[OF qpos])
  have ea: "gs_a_idx q t * gs_l_idx (gs_n h q) u \<le> gs_m h * q"
    by (simp add: ale lle mult.commute mult_le_mono)
  have eb: "gs_b_idx q t * gs_l_idx (gs_n h q) u \<le> gs_m h * q"
    by (simp add: ble lle mult.commute mult_mono')
  show ?thesis using kle ea eb jlt
    unfolding gs_row_denominator_exponent_def by linarith
qed

lemma row_scaled_matrix_entries_from_coefficient_representation:
  fixes T :: int
  assumes rep: "\<forall>a b l k j. \<exists>c::nat \<Rightarrow> int.
      of_int (T ^ (gs_system_coeff_factor_count a b l k + j)) *
        (gs_system_coeff d a b l k * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i)"
    and npos: "gs_n h q > 0"
    and qpos: "q > 0"
  shows "\<forall>u<gs_m h * gs_n h q. \<forall>t<q * q. \<forall>j<D.
    \<exists>c::nat \<Rightarrow> int.
      of_int (T ^ (gs_row_denominator_exponent (gs_m h) (gs_n h q) q D)) *
        (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i)"
proof -
  have one: "\<exists>c::nat \<Rightarrow> int.
    of_int (T ^ (gs_row_denominator_exponent (gs_m h) (gs_n h q) q D)) *
      (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * eta ^ j) =
      (\<Sum>i<D. of_int (c i) * eta ^ i)"
    if ult: "u < gs_m h * gs_n h q" and tlt: "t < q * q" and jlt: "j < D"
    for u t j
  proof -
    let ?k = "gs_k_idx (gs_n h q) u"
    let ?a = "gs_a_idx q t"
    let ?b = "gs_b_idx q t"
    let ?l = "gs_l_idx (gs_n h q) u"
    let ?e = "?k + ?a * ?l + ?b * ?l + j"
    let ?N = "gs_row_denominator_exponent (gs_m h) (gs_n h q) q D"
    have eN: "?e \<le> ?N"
      by (rule gs_system_coeff_idx_basis_exponent_le[OF npos qpos ult tlt jlt])
    obtain c::"nat \<Rightarrow> int" where crep:
      "of_int (T ^ ?e) * (gs_system_coeff d ?a ?b ?l ?k * eta ^ j) = (\<Sum>i<D. of_int (c i) * eta ^ i)"
      using rep unfolding gs_system_coeff_factor_count_def by blast
    have padded: "of_int (T ^ ?N) * (gs_system_coeff d ?a ?b ?l ?k * eta ^ j) =
        (\<Sum>i<D. of_int (T ^ (?N - ?e) * c i) * eta ^ i)"
      by (rule scaled_integer_power_basis_coordinate_pad_exponent[OF eN crep])
    let ?s = "gs_row_scale d (gs_m h) (gs_n h q) q u"
    have row: "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) =
      of_int ?s * gs_system_coeff d ?a ?b ?l ?k"
      using ult tlt by (simp add: gs_row_scaled_system_mat_def gs_system_coeff_idx_def)
    have "of_int (T ^ ?N) * (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * eta ^ j) =
      (\<Sum>i<D. of_int (?s * (T ^ (?N - ?e) * c i)) * eta ^ i)"
    proof -
      have "of_int (T ^ ?N) *
        (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * eta ^ j) =
        of_int ?s * (of_int (T ^ ?N) * (gs_system_coeff d ?a ?b ?l ?k * eta ^ j))"
        by (simp add: row algebra_simps)
      also have "... = of_int ?s * (\<Sum>i<D. of_int (T ^ (?N - ?e) * c i) * eta ^ i)"
        by (simp only: padded)
      also have "... = (\<Sum>i<D. of_int (?s * (T ^ (?N - ?e) * c i)) * eta ^ i)"
        by (simp add: sum_distrib_left algebra_simps)
      finally show ?thesis .
    qed
    then show ?thesis by meson
  qed
  show ?thesis using one by blast
qed

lemma row_scaled_matrix_entries_from_product_denominator:
  fixes T :: int
  assumes prod: "gs_uniform_product_denominator d T"
    and npos: "gs_n h q > 0"
    and qpos: "q > 0"
  shows "\<forall>u<gs_m h * gs_n h q. \<forall>t<q * q. \<forall>j<D.
    \<exists>c::nat \<Rightarrow> int.
      of_int (T ^ (gs_row_denominator_exponent (gs_m h) (gs_n h q) q D)) *
        (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * eta ^ j) =
        (\<Sum>i<D. of_int (c i) * eta ^ i)"
  using row_scaled_matrix_entries_from_coefficient_representation
     system_coefficients_times_basis_from_product_denominator[OF prod] npos qpos
  by blast

theorem row_scaled_matrix_entries_have_uniform_exponential_denominator:
  assumes coords: "rational_power_basis_coordinates D eta ca cb cw (gs_a d) (gs_b d) (gs_w d)"
    and npos: "gs_n h q > 0"
    and qpos: "q > 0"
  shows "\<exists>T::int. T > 0 \<and>
    (\<forall>u<gs_m h * gs_n h q. \<forall>t<q * q. \<forall>j<D.
      \<exists>c::nat \<Rightarrow> int.
        of_int (T ^ (gs_row_denominator_exponent (gs_m h) (gs_n h q) q D)) *
          (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t) * eta ^ j) =
          (\<Sum>i<D. of_int (c i) * eta ^ i))"
  using assms row_scaled_matrix_entries_from_coefficient_representation  
    system_coefficients_times_basis_have_uniform_denominator [OF coords]
  by blast

lemma finite_matrix_has_scaled_integer_structure_constants:
  fixes A :: "complex mat"
  assumes A: "A \<in> carrier_mat p q"
    and entryK: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> A $$ (u,t) \<in> K"
  shows "\<exists>L::int. \<exists>C::nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int.
    L > 0 \<and> (\<forall>u<p. \<forall>t<q. \<forall>j<D. of_int L * (A $$ (u,t) * eta ^ j) = (\<Sum>k<D. of_int (C u t k j) * eta ^ k))"
proof -
  let ?S = "(\<lambda>(u,t). A $$ (u,t)) ` ({..<p} \<times> {..<q})"
  have Sfin: "finite ?S" by simp
  have SK: "?S \<subseteq> K" using entryK by auto
  obtain L C
    where Lp: "L > 0"
      and rep: "\<forall>x\<in>?S. \<forall>j<D. of_int L * (x * eta ^ j) = (\<Sum>k<D. of_int (C x j k) * eta ^ k)"
    using finite_entries_have_scaled_integer_structure_constants[OF Sfin SK] by blast
  let ?C = "\<lambda>u t k j. C (A $$ (u,t)) j k"
  have eq: "of_int L * (A $$ (u,t) * eta ^ j) = (\<Sum>k<D. of_int (?C u t k j) * eta ^ k)"
    if "u < p" "t < q" "j < D" for u t j
    using rep that by auto
  show ?thesis by (intro exI) (use Lp eq in force)
qed

theorem finite_K_matrix_has_bounded_algebraic_integer_kernel:
  fixes A :: "complex mat"
  assumes A: "A \<in> carrier_mat p q"
    and ppos: "p > 0"
    and hpq: "2 * p \<le> q"
    and entryK: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> A $$ (u,t) \<in> K"
  obtains B :: int and v :: "complex vec" and x :: "int vec" where
    "bounded_integral_basis_kernel A p q D (\<lambda>j. eta ^ j) (2 * int (q * D) * max 1 B) v x"
proof -
  obtain L::int and C::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
    where Lp: "L > 0"
      and rep: "\<forall>u<p. \<forall>t<q. \<forall>j<D. of_int L * (A $$ (u,t) * eta ^ j) = (\<Sum>k<D. of_int (C u t k j) * eta ^ k)"
    using finite_matrix_has_scaled_integer_structure_constants[OF A entryK] by blast
  let ?F = "(\<Union>u\<in>{..<p}. \<Union>t\<in>{..<q}. \<Union>k\<in>{..<D}. abs ` (C u t k ` {..<D}))"
  have Ffin: "finite ?F" by simp
  let ?B = "Max (insert 0 ?F)"
  have Cbnd: "\<bar>C u t k j\<bar> \<le> ?B" if "u < p" "t < q" "k < D" "j < D" for u t k j
  proof -
    have mem: "\<bar>C u t k j\<bar> \<in> insert 0 ?F"
      using that by (meson UN_I imageI insertCI lessThan_iff)
    show ?thesis
      using Ffin mem by (metis Max_ge finite_insert)
  qed
  have indep: "(\<forall>j<D. c j = 0)" if zero: "(\<Sum>j<D. of_int (c j) * eta ^ j) = 0" for c::"nat \<Rightarrow> int"
  proof -
    have cj: "(\<forall>j<D. complex_of_int (c j) = 0)"
      using Subfield.power_basis_indep[OF Rats_subfield algQ] zero
      using D_def by (metis (full_types) Rats_of_int) 
    show "\<forall>j<D. c j = 0" using cj by auto
  qed
  have Dp: "D > 0" by (rule Dpos)
  have Lnz: "L \<noteq> (0::int)" using Lp by simp
  have repp: "of_int L * (A $$ (u,t) * eta ^ j) = (\<Sum>k<D. of_int (C u t k j) * eta ^ k)"
    if up: "u < p" and tq: "t < q" and jd: "j < D" for u t j
    using rep up tq jd by blast
  obtain v :: "complex vec" and x :: "int vec" where
      vcar: "v \<in> carrier_vec q"
    and vnz: "v \<noteq> 0\<^sub>v q"
    and xcar: "x \<in> carrier_vec (q * D)"
    and xnz: "x \<noteq> 0\<^sub>v (q * D)"
    and ker: "A *\<^sub>v v = 0\<^sub>v p"
    and repr: "\<forall>t<q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * eta ^ j)"
    and xbnd: "x \<in> Bounded_vec (2 * int (q * D) * max 1 ?B)"
    by (rule bounded_kernel_of_scaled_integer_structure_constants
      [OF A ppos Dp hpq Lnz repp Cbnd indep])
  have vint: "\<forall>t<q. algebraic_int (v $ t)"
    using repr sum_int_power_algebraic_int by presburger
  have IW: "bounded_integral_basis_kernel A p q D (\<lambda>j. eta ^ j) (2 * int (q * D) * max 1 ?B) v x"
    by unfold_locales (use vcar vnz ker vint repr xcar xnz xbnd in auto)
  show thesis by (rule that[OF IW])
qed

lemma scaled_structure_constants_transport_to_embedding:
  assumes ilt: "i < D"
    and xK: "x \<in> K"
    and rep: "of_int L * (x * eta ^ j) = (\<Sum>k<D. of_int (C k) * eta ^ k)"
  shows "of_int L * (emb i x * basis j (emb i)) = (\<Sum>k<D. of_int (C k) * basis k (emb i))"
proof -
  interpret KS: Subfield K by (rule K_subfield)
  have sigma: "emb i \<in> field_auto K \<rat>"
    by (rule emb_in_field_auto[OF ilt])
  have hom: "field_hom_on K (emb i)"
    by (rule field_auto_imp_field_hom_on[OF K_subfield sigma])
  have LK: "L \<in> K"
    using Rats_subset_K by auto
  have Lfix: "emb i L = L"
    using sigma by (simp add: field_auto_mem_iff)
  have etaP: "eta ^ j \<in> K" by (rule KS.power_closed[OF eta_in_K])
  have xjK: "x * eta ^ j \<in> K" by (rule KS.mult_closed[OF xK etaP])
  have "emb i (of_int L * (x * eta ^ j)) = of_int L * (emb i x * basis j (emb i))"
    by (simp add: field_hom_on.hom_mult[OF hom LK xjK]
      field_hom_on.hom_mult[OF hom xK etaP]
      field_hom_on.hom_power[OF hom eta_in_K] Lfix basis_def)
  then show ?thesis using arg_cong[OF rep, of "emb i"] emb_sum_int_power[OF ilt] by simp
qed

lemma scaled_structure_constant_abs_le:
  assumes xK: "x \<in> K"
    and Lp: "L > (0::int)"
    and rep: "of_int L * (x * eta ^ j) =
      (\<Sum>k<D. of_int (C k) * eta ^ k)"
    and house: "EH.ehouse (\<lambda>e. e x) \<le> A"
    and Anonneg: "0 \<le> A"
    and klt: "k < D"
    and jlt: "j < D"
  shows "\<bar>C k\<bar> \<le> \<lceil>of_nat (card E) *
    power_basis_inverse_bound * (of_int L * A * power_basis_entry_bound)\<rceil>"
proof -
  let ?H = "(of_int L :: real) * A * power_basis_entry_bound"
  have Hnonneg: "0 \<le> ?H"
    using Lp Anonneg power_basis_entry_bound_nonneg by simp
  have comb_le: "EH.ehouse (\<lambda>e. \<Sum>k<D. of_int (C k) * basis k e) \<le> ?H"
  proof (rule EH.ehouse_leI[OF Hnonneg])
    fix e
    assume eE: "e \<in> E"
    obtain i where ilt: "i < D" and e_eq: "e = emb i"
      using eE unfolding E_def by auto
    have trans: "(\<Sum>k<D. of_int (C k) * basis k e) = of_int L * (e x * basis j e)"
      using scaled_structure_constants_transport_to_embedding[OF ilt xK rep]
      by (simp add: e_eq)
    have xle: "cmod (e x) \<le> A"
      using EH.cmod_le_ehouse[OF eE, of "\<lambda>e. e x"] house by linarith
    have ble: "cmod (basis j e) \<le> power_basis_entry_bound"
      using basis_cmod_le_power_basis_entry_bound[OF ilt jlt] by (simp add: e_eq)
    have "cmod (\<Sum>k<D. of_int (C k) * basis k e) = of_int L * cmod (e x) * cmod (basis j e)"
      using Lp by (simp add: trans norm_mult)
    also have "... \<le> ?H"
      using Lp Anonneg xle ble power_basis_entry_bound_nonneg
      by (intro mult_mono) auto
    finally show "cmod ((\<lambda>e. \<Sum>k<D. of_int (C k) * basis k e) e) \<le> ?H"
      by simp
  qed
  have rb: "EH.ehouse (repr_coeff k) \<le> power_basis_inverse_bound"
    by (simp add: REC.repr_coeff_ehouse_le_of_inverse_matrix_bound
        inverse_basis_matrix_entry_le_power_basis_inverse_bound)
  show ?thesis
    using REC.abs_int_basis_coeff_ehouse_le_biorthogonal [OF klt rb]
    using power_basis_inverse_bound_nonneg comb_le Hnonneg by blast
qed

theorem finite_K_matrix_has_house_bounded_kernel_given_denominator:
  fixes M :: "complex mat"
    and L :: int
    and C :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes M: "M \<in> carrier_mat p q"
    and ppos: "p > 0"
    and hpq: "2 * p \<le> q"
    and entryK: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> M $$ (u,t) \<in> K"
    and house: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> EH.ehouse (\<lambda>e. e (M $$ (u,t))) \<le> H"
    and Hnonneg: "0 \<le> H"
    and Lp: "L > 0"
    and rep: "\<forall>u<p. \<forall>t<q. \<forall>j<D. of_int L * (M $$ (u,t) * eta ^ j) = (\<Sum>k<D. of_int (C u t k j) * eta ^ k)"
  obtains v :: "complex vec" and x :: "int vec" where
    "bounded_integral_basis_kernel M p q D (\<lambda>j. eta ^ j)
      (2 * int (q * D) * max 1
        (\<lceil>of_nat (card E) * power_basis_inverse_bound *
          (of_int L * H * power_basis_entry_bound)\<rceil>)) v x"
proof -
  let ?B = "\<lceil>of_nat (card E) * power_basis_inverse_bound *
    (of_int L * H * power_basis_entry_bound)\<rceil>"
  have Cbnd: "\<bar>C u t k j\<bar> \<le> ?B"
    if up: "u < p" and tq: "t < q" and kd: "k < D" and jd: "j < D"
    for u t k j
    by (rule scaled_structure_constant_abs_le[OF entryK[OF up tq] Lp
      _ house[OF up tq] Hnonneg kd jd]) (use rep up tq jd in blast)
  have indep: "(\<forall>j<D. c j = 0)" if zero: "(\<Sum>j<D. of_int (c j) * eta ^ j) = 0" for c
      using Subfield.power_basis_indep[OF Rats_subfield algQ] zero
  proof -
    have cj: "(\<forall>j<D. complex_of_int (c j) = 0)"
      using Subfield.power_basis_indep[OF Rats_subfield algQ] zero
      using D_def by (metis (full_types) Rats_of_int) 
    show "\<forall>j<D. c j = 0" using cj by auto
  qed
  have Lnz: "L \<noteq> (0::int)" using Lp by simp
  have repp: "of_int L * (M $$ (u,t) * eta ^ j) = (\<Sum>k<D. of_int (C u t k j) * eta ^ k)"
    if up: "u < p" and tq: "t < q" and jd: "j < D" for u t j
    using rep up tq jd by blast
  obtain v :: "complex vec" and x :: "int vec" where
      vcar: "v \<in> carrier_vec q"
    and vnz: "v \<noteq> 0\<^sub>v q"
    and xcar: "x \<in> carrier_vec (q * D)"
    and xnz: "x \<noteq> 0\<^sub>v (q * D)"
    and ker: "M *\<^sub>v v = 0\<^sub>v p"
    and repr: "\<forall>t<q. v $ t = (\<Sum>j<D. of_int (x $ sg_pair_idx D t j) * eta ^ j)"
    and xbnd: "x \<in> Bounded_vec (2 * int (q * D) * max 1 ?B)"
    by (rule bounded_kernel_of_scaled_integer_structure_constants
      [OF M ppos Dpos hpq Lnz repp Cbnd indep])
  have vint: "\<forall>t<q. algebraic_int (v $ t)"
    using repr sum_int_power_algebraic_int by presburger
  have IW: "bounded_integral_basis_kernel M p q D (\<lambda>j. eta ^ j) (2 * int (q * D) * max 1 ?B) v x"
    by unfold_locales (use vcar vnz ker vint repr xcar xnz xbnd in auto)
  show thesis by (rule that[OF IW])
qed

theorem finite_K_matrix_has_house_bounded_algebraic_integer_kernel:
  fixes M :: "complex mat"
  assumes M: "M \<in> carrier_mat p q"
    and ppos: "p > 0"
    and hpq: "2 * p \<le> q"
    and entryK: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> M $$ (u,t) \<in> K"
    and house: "\<And>u t. u < p \<Longrightarrow> t < q \<Longrightarrow> EH.ehouse (\<lambda>e. e (M $$ (u,t))) \<le> H"
    and Hnonneg: "0 \<le> H"
  obtains L :: int and v :: "complex vec" and x :: "int vec" where
    "L > 0"
    "bounded_integral_basis_kernel M p q D (\<lambda>j. eta ^ j)
      (2 * int (q * D) * max 1
        (\<lceil>of_nat (card E) * power_basis_inverse_bound *
          (of_int L * H * power_basis_entry_bound)\<rceil>)) v x"
proof -
  obtain L C
    where Lp: "L > 0"
      and rep: "\<forall>u<p. \<forall>t<q. \<forall>j<D. of_int L * (M $$ (u,t) * eta ^ j) = (\<Sum>k<D. of_int (C u t k j) * eta ^ k)"
    using finite_matrix_has_scaled_integer_structure_constants[OF M entryK] by blast
  show thesis
    using finite_K_matrix_has_house_bounded_kernel_given_denominator
      [OF M ppos hpq entryK house Hnonneg Lp rep] 
    using that [OF Lp] by auto
qed

lemma three_power_basis_coordinate_families_common_denominator:
  assumes ca_rat: "\<forall>i<D. ca i \<in> \<rat>"
    and cb_rat: "\<forall>i<D. cb i \<in> \<rat>"
    and cw_rat: "\<forall>i<D. cw i \<in> \<rat>"
  shows "\<exists>L::int. \<exists>za zb zw::nat \<Rightarrow> int.
    L > 0 \<and> (\<forall>i<D. of_int L * ca i = complex_of_int (za i)) \<and>
      (\<forall>i<D. of_int L * cb i = complex_of_int (zb i)) \<and>
      (\<forall>i<D. of_int L * cw i = complex_of_int (zw i))"
proof -
  let ?F = "ca ` {..<D} \<union> cb ` {..<D} \<union> cw ` {..<D}"
  have Ffin: "finite ?F" by simp
  have Frat: "?F \<subseteq> \<rat>"
    using ca_rat cb_rat cw_rat by auto
  obtain L::int where "L > 0"
    and "\<forall>x\<in>?F. \<exists>z::int. of_int L * x = of_int z"
    using finite_Rats_common_denominator[OF Ffin Frat] by blast
  then obtain za zb zw where "\<And>i. i < D \<Longrightarrow> of_int L * ca i = of_int (za i)"
    and "\<And>i. i < D \<Longrightarrow> of_int L * cb i = of_int (zb i)"
    and "\<And>i. i < D \<Longrightarrow> of_int L * cw i = of_int (zw i)"
    by (force simp: bchoice_iff)
  with \<open>L>0\<close> show ?thesis by blast
qed

lemma row_scaled_entry_in_K_from_rational_coordinates:
  assumes coords: "rational_power_basis_coordinates D eta ca cb cw (gs_a d) (gs_b d) (gs_w d)"
    and up: "u < m * n"
    and tq: "t < q * q"
  shows "gs_row_scaled_system_mat d m n q $$ (u,t) \<in> K"
proof -
  interpret KS: Subfield K by (rule K_subfield)
  interpret rational_power_basis_coordinates D eta ca cb cw "gs_a d" "gs_b d" "gs_w d"
    using assms by blast
  obtain aK: "gs_a d \<in> K" and bK: "gs_b d \<in> K" and wK: "gs_w d \<in> K"
    using a_eq b_eq ca_rat cb_rat cw_rat w_eq sum_rat_power_in_K
    by presburger
  have natK: "(of_nat z :: complex) \<in> K" for z
    using Rats_subset_K by auto
  have affK: "gs_affine_coeff d a b \<in> K" for a b
    using bK gs_affine_coeff_def by auto
  have sysK: "gs_system_coeff d a b l k \<in> K" for a b l k
    by (simp add: KS.mult_closed KS.power_closed aK affK gs_system_coeff_def wK)
  have scaleK: "(of_int (gs_row_scale d m n q u) :: complex) \<in> K"
    using Rats_subset_K by auto
  have coeffK: "gs_system_coeff_idx d n q u t \<in> K"
    unfolding gs_system_coeff_idx_def by (rule sysK)
  show ?thesis using KS.mult_closed[OF scaleK coeffK] up tq
    by (simp add: gs_row_scaled_system_mat_def)
qed

theorem row_scaled_matrix_has_bounded_algebraic_integer_kernel:
  assumes coords: "rational_power_basis_coordinates D eta ca cb cw (gs_a d) (gs_b d) (gs_w d)"
    and npos: "gs_n h q > 0"
    and dvd: "2 * gs_m h dvd q ^ 2"
  obtains B :: int and v :: "complex vec" and x :: "int vec" where
    "bounded_integral_basis_kernel
      (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q)
      (gs_m h * gs_n h q) (q * q) D (\<lambda>j. eta ^ j)
      (2 * int (q * q * D) * max 1 B) v x"
proof -
  let ?m = "gs_m h"
  let ?n = "gs_n h q"
  let ?M = "gs_row_scaled_system_mat d ?m ?n q"
  have Mcar: "?M \<in> carrier_mat (?m * ?n) (q * q)" by simp
  have mnpos: "?m * ?n > 0" using npos by simp
  have bal: "q * q = 2 * (?m * ?n)"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have hpq: "2 * (?m * ?n) \<le> q * q" using bal by simp
  have entryK: "?M $$ (u,t) \<in> K"
    if up: "u < ?m * ?n" and tq: "t < q * q" for u t
    by (rule row_scaled_entry_in_K_from_rational_coordinates [OF coords up tq])
  show thesis
    by (rule finite_K_matrix_has_bounded_algebraic_integer_kernel
      [OF Mcar mnpos hpq entryK]) (auto intro: that)
qed

theorem row_scaled_matrix_has_house_bounded_kernel:
  assumes coords: "rational_power_basis_coordinates D eta ca cb cw (gs_a d) (gs_b d) (gs_w d)"
    and npos: "gs_n h q > 0"
    and dvd: "2 * gs_m h dvd q ^ 2"
    and house: "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow>
      EH.ehouse (\<lambda>e. e (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) \<le> H"
    and Hnonneg: "0 \<le> H"
  obtains L :: int and v :: "complex vec" and x :: "int vec" where
    "L > 0"
    "bounded_integral_basis_kernel
      (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q)
      (gs_m h * gs_n h q) (q * q) D (\<lambda>j. eta ^ j)
      (2 * int (q * q * D) * max 1
        (\<lceil>of_nat (card E) * power_basis_inverse_bound *
          (of_int L * H * power_basis_entry_bound)\<rceil>)) v x"
proof -
  let ?m = "gs_m h"
  let ?n = "gs_n h q"
  let ?M = "gs_row_scaled_system_mat d ?m ?n q"
  have Mcar: "?M \<in> carrier_mat (?m * ?n) (q * q)" by simp
  have mnpos: "?m * ?n > 0" using npos by simp
  have bal: "q * q = 2 * (?m * ?n)"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have hpq: "2 * (?m * ?n) \<le> q * q" using bal by simp
  have entryK: "?M $$ (u,t) \<in> K"
    if up: "u < ?m * ?n" and tq: "t < q * q" for u t
    by (rule row_scaled_entry_in_K_from_rational_coordinates [OF coords up tq])
  show thesis
    by (rule finite_K_matrix_has_house_bounded_algebraic_integer_kernel
      [OF Mcar mnpos hpq entryK house Hnonneg]) (auto intro: that)
qed

theorem row_scaled_matrix_has_given_denominator_bounded_kernel:
  fixes T :: int
  assumes Tp: "T > 0"
    and prod: "gs_uniform_product_denominator d T"
    and coords: "rational_power_basis_coordinates D eta ca cb cw (gs_a d) (gs_b d) (gs_w d)"
    and npos: "gs_n h q > 0"
    and qpos: "q > 0"
    and dvd: "2 * gs_m h dvd q ^ 2"
    and house: "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow>
      EH.ehouse (\<lambda>e. e (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) \<le> H"
    and Hnonneg: "0 \<le> H"
  obtains v :: "complex vec" and x :: "int vec" where
    "bounded_integral_basis_kernel
      (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q)
      (gs_m h * gs_n h q) (q * q) D (\<lambda>j. eta ^ j)
      (2 * int (q * q * D) * max 1
        (\<lceil>of_nat (card E) * power_basis_inverse_bound *
          (of_int (T ^ (gs_row_denominator_exponent (gs_m h) (gs_n h q) q D)) * H *
            power_basis_entry_bound)\<rceil>)) v x"
proof -
  let ?m = "gs_m h"
  let ?n = "gs_n h q"
  let ?M = "gs_row_scaled_system_mat d ?m ?n q"
  let ?N = "gs_row_denominator_exponent ?m ?n q D"
  have Mcar: "?M \<in> carrier_mat (?m * ?n) (q * q)" by simp
  have mnpos: "?m * ?n > 0" using npos by simp
  have bal: "q * q = 2 * (?m * ?n)"
    using gs_q_sq_eq_two_mn[OF dvd] by (simp add: power2_eq_square)
  have hpq: "2 * (?m * ?n) \<le> q * q" using bal by simp
  have entryK: "?M $$ (u,t) \<in> K"
    if up: "u < ?m * ?n" and tq: "t < q * q" for u t
    by (rule row_scaled_entry_in_K_from_rational_coordinates [OF coords up tq])
  have Lp: "T ^ ?N > 0" using Tp by simp
  have "\<forall>u<?m * ?n. \<forall>t<q * q. \<forall>j<D.
      \<exists>c. of_int (T ^ ?N) * (?M $$ (u,t) * eta ^ j) = (\<Sum>i<D. of_int (c i) * eta ^ i)"
    by (rule row_scaled_matrix_entries_from_product_denominator [OF prod npos qpos])
  then obtain f where f: "\<forall>u<?m * ?n. \<forall>t<q * q. \<forall>j<D. of_int (T ^ ?N) * (?M $$ (u,t) * eta ^ j) 
       = (\<Sum>k<D. of_int ((\<lambda>u t k j. f u t j k) u t k j) * eta ^ k)"
    unfolding choice_iff' by presburger
  then show thesis
    using finite_K_matrix_has_house_bounded_kernel_given_denominator
      [OF Mcar mnpos hpq entryK house Hnonneg Lp f]
    using that by metis
qed

theorem row_scaled_matrix_has_exponential_denominator_bounded_kernel:
  assumes coords: "rational_power_basis_coordinates D eta ca cb cw (gs_a d) (gs_b d) (gs_w d)"
    and npos: "gs_n h q > 0"
    and qpos: "q > 0"
    and dvd: "2 * gs_m h dvd q ^ 2"
    and house: "\<And>u t. u < gs_m h * gs_n h q \<Longrightarrow> t < q * q \<Longrightarrow>
      EH.ehouse (\<lambda>e. e (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) \<le> H"
    and Hnonneg: "0 \<le> H"
  obtains T :: int and v :: "complex vec" and x :: "int vec" where
    "T > 0"
    "bounded_integral_basis_kernel
      (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q)
      (gs_m h * gs_n h q) (q * q) D (\<lambda>j. eta ^ j)
      (2 * int (q * q * D) * max 1
        \<lceil>real (card E) * power_basis_inverse_bound *
          (real_of_int (T ^ (gs_row_denominator_exponent (gs_m h) (gs_n h q) q D)) * H *
            power_basis_entry_bound)\<rceil>) v x"
proof -
  interpret Coords: rational_power_basis_coordinates D eta ca cb cw
    "gs_a d" "gs_b d" "gs_w d"
    by (rule coords)
  obtain *: "gs_a d \<in> K" "gs_b d \<in> K" "gs_w d \<in> K"
    using Coords.a_eq Coords.b_eq Coords.ca_rat Coords.cb_rat Coords.cw_rat Coords.w_eq
      sum_rat_power_in_K by presburger
  obtain T where Tp: "T > 0" and prod: "gs_uniform_product_denominator d T"
    using data_generators_and_affines_uniform_product_denominator[OF *]
    unfolding gs_uniform_product_denominator_def by blast
  show thesis
    using row_scaled_matrix_has_given_denominator_bounded_kernel
      [OF Tp prod coords npos qpos dvd house Hnonneg]
    using Tp that by metis
qed

end

locale gelfond_schneider_power_basis_scaled_norm_verified =
  gelfond_schneider_power_basis_field_norm_estimates
    K eta D emb ca cb cw d q h i0 A c5 c14
  for K :: "complex set"
  and eta :: complex
  and D :: nat
  and emb :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  and ca cb cw :: "nat \<Rightarrow> complex"
  and d
  and q h i0 :: nat
  and A c5 c14 :: real +
  fixes T :: int
  assumes Tp: "T > 0"
  assumes prod: "\<forall>xs. (\<forall>x\<in>set xs. x = gs_a d \<or> x = gs_w d \<or> x = eta \<or> (\<exists>u v. x = of_nat u + of_nat v * gs_b d))
      \<longrightarrow> (\<exists>z. of_int (T ^ length xs) * prod_list xs = (\<Sum>i<D. of_int (z i) * eta ^ i))"
  assumes hD: "h = D"
  assumes A_choice: "A = gs_concrete_entry_bound"
  assumes c14_big:
    "(gs_house_growth_base *
      of_int (T ^ (gs_row_denominator_order_exponent (gs_m h) D)) ^ 2) ^ (D - 1) *
      (gs_point_growth_base *
        of_int (T ^ (gs_row_denominator_order_exponent (gs_m h) D))) \<le> c14"
begin

theorem coordinate_contradiction: False
proof -
  let ?N = "gs_row_denominator_exponent (gs_m h) (gs_n h q) q D"
  let ?B = "gs_kernel_witness_bound (q * q) D gs_witness_growth_weight
    (of_int (T ^ ?N) * A)"
  have house: "EH.ehouse (\<lambda>e. e (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q $$ (u,t))) \<le> A"
    if up: "u < gs_m h * gs_n h q" and tq: "t < q * q" for u t
    using A_choice Aemb_def gs_row_scaled_entry_concrete_house_le that(1,2) by presburger
  have Anonneg: "0 \<le> A"
    using A_choice gs_concrete_entry_bound_nonneg by simp
  have prod_named: "gs_uniform_product_denominator d T"
    using prod
    unfolding gs_uniform_product_denominator_def
      uniform_product_denominator_def uniform_denominator_factor_def
    by blast
  obtain v x where IW: "bounded_integral_basis_kernel
      (gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q)
      (gs_m h * gs_n h q) (q * q) D (\<lambda>j. eta ^ j) ?B v x"
    using row_scaled_matrix_has_given_denominator_bounded_kernel
      [OF Tp prod_named coords npos qpos dvd house Anonneg]
    by (force simp add: gs_kernel_witness_bound_def gs_witness_growth_weight_def ac_simps)
  interpret W: bounded_integral_basis_kernel
    "gs_row_scaled_system_mat d (gs_m h) (gs_n h q) q"
    "gs_m h * gs_n h q" "q * q" D "\<lambda>j. eta ^ j" ?B v x
    by (rule IW)
  note vcar = W.v_carrier and vnz = W.v_nonzero
    and ker = W.kernel and vint = W.v_integral
    and vrepr = W.coordinates and xcar = W.x_carrier
    and xnz = W.x_nonzero and xbnd = W.x_bounded
  have repr: "gs_power_basis_witness_coordinates v x"
    using vrepr by (simp add: gs_power_basis_witness_coordinates_def
      basis_eq_power_at_identity_embedding[OF emb0])
  define r where "r \<equiv> nat (gs_min_order (gs_m h) d q (\<lambda>t. Matrix.vec_index v t))"
  have coeff_nz: "\<exists>t<q * q. Matrix.vec_index v t \<noteq> 0"
    using vcar vnz by force
  have deriv_nz: "((deriv ^^ r) (gs_aux_fun_vec d q (\<lambda>t. Matrix.vec_index v t)))
      (gs_min_order_node (gs_m h) d q (\<lambda>t. Matrix.vec_index v t)) \<noteq> 0"
    unfolding r_def
    by (rule gs_min_order_deriv_nonzero_of_coeff_nonzero[OF d qpos coeff_nz])
  define c where "c \<equiv> gs_scaled_auxiliary_multiplier r"
  define rho where "rho \<equiv> gs_scaled_auxiliary_value v r c"
  obtain "0 < r" and nle: "gs_n h q \<le> r"
    using vcar vnz ker r_def rho_order_pos rho_order_ge_n by presburger
  obtain ai: "algebraic_int rho" and nz: "rho \<noteq> 0"
    using rho_algebraic_int_nonzero[OF vcar vnz vint] r_def deriv_nz c_def rho_def by blast
  have xK: "rho \<in> K"
    using rho_in_K[OF repr] rho_def by blast
  have c14_named:
    "gs_norm_growth_base
      (of_int (T ^ (gs_row_denominator_order_exponent (gs_m h) D))) \<le> c14"
    using c14_big by (simp add: gs_norm_growth_base_def)
  moreover have "gs_abs_galois_norm rho \<le> c14 powr of_nat r * real r powr (gs_norm_order_exponent h r)"
    using r_def rho_def c_def nle \<open>r > 0\<close> ai xK
    by (intro gs_rho_upper_from_concrete_witness_with_denominator
      [OF hD A_choice Tp c14_named vcar vnz ker repr xcar xbnd]) auto
  moreover have "0 < gs_abs_galois_norm rho"
    by (rule gs_abs_galois_norm_pos[OF xK nz])
  moreover have "inverse (gs_abs_galois_norm rho) < c5 powr of_nat r"
    by (rule inverse_gs_abs_galois_norm_lt_powr[OF xK ai nz c5_gt1 \<open>r > 0\<close>])
  moreover have "gs_n h (gs_q_choice h (c14 * c5)) \<le> r"
    using nle by (simp add: q_def)
  ultimately show False
    using c14_ge1 c5_gt1 gs_growth_contradiction_with_q_choice hpos by fastforce
qed

end

end
