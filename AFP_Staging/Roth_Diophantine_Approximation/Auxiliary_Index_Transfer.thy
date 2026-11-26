theory Auxiliary_Index_Transfer
  imports Evaluation_Height
begin

theorem roth_evaluation_sandwich_uniform:
  fixes P :: "int mpoly" and \<beta> :: "nat \<Rightarrow> rat"
    and a h :: "nat \<Rightarrow> real"
  assumes box: "roth_poly_in_box m r P"
    and nz: "insertion \<beta> (replace_coeff of_int P) \<noteq> (0::rat)"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> \<kappa>" and Lpos: "0 \<le> L"
    and index: "ereal theta \<le> roth_index m r a
      (replace_coeff (of_int::int \<Rightarrow> real) P)"
    and near: "\<And>v. abs (of_rat (\<beta> v) - a v) \<le> exp (-\<kappa> * h v)"
  shows "exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (\<beta> v))) \<le>
    real (card (roth_exponent_box m r)) ^ 2 *
      real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs (a v)) ^ r v) *
      exp (-\<kappa> * L * theta)"
proof -
  let ?C = "real (card (roth_exponent_box m r))"
  let ?S = "Poly_Mapping.keys (mapping_of
      (roth_translate a (replace_coeff (of_int::int \<Rightarrow> real) P)))"
  let ?V = "real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P)"
  let ?E = "(\<Prod>v<m. max 1 (abs (a v)) ^ r v)"
  let ?W = "exp (-\<kappa> * L * theta)"
  have raw: "exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (\<beta> v))) \<le>
      (?C * ?V * ?E) * real (card ?S) * ?W"
    by (rule roth_evaluation_sandwich_height[OF box nz rpos balance
      kpos Lpos index near])
  have scard: "real (card ?S) \<le> ?C"
    using roth_real_taylor_card_bound[OF roth_int_cast_box_real[OF box]] by simp
  have pos: "0 \<le> ?C * ?V * ?E"
    by (intro mult_nonneg_nonneg prod_nonneg) simp_all
  have scale: "(?C * ?V * ?E) * real (card ?S) \<le>
      (?C * ?V * ?E) * ?C"
    by (rule mult_left_mono[OF scard pos])
  have wpos: "0 \<le> ?W" by simp
  have scale2: "(?C * ?V * ?E) * real (card ?S) * ?W \<le>
      (?C * ?V * ?E) * ?C * ?W"
    by (rule mult_right_mono[OF scale wpos])
  have bound: "exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (\<beta> v))) \<le>
      (?C * ?V * ?E) * ?C * ?W"
    using raw scale2 by linarith
  have factor: "(?C * ?V * ?E) * ?C * ?W =
      ?C ^ 2 * ?V * ?E * ?W"
    by (simp add: power2_eq_square mult_ac)
  show ?thesis using bound factor by metis
qed

lemma roth_hasse_coeff_sup_four:
  fixes P :: "int mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup (roth_hasse J P) \<le>
    4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P"
proof -
  let ?S = "(\<Sum>v<m. r v)"
  have hs: "roth_int_coeff_sup (roth_hasse J P) \<le>
      2 ^ ?S * roth_int_coeff_sup P"
    by (rule roth_hasse_coeff_sup[OF box])
  have "2 ^ ?S * roth_int_coeff_sup (roth_hasse J P) \<le>
      2 ^ ?S * (2 ^ ?S * roth_int_coeff_sup P)"
    using hs by simp
  also have "... = 4 ^ ?S * roth_int_coeff_sup P"
    by (simp add: power_mult_distrib[symmetric] mult.assoc)
  finally show ?thesis .
qed

lemma roth_exp_gap:
  fixes C H K :: real
  assumes Cpos: "0 < C" and gap: "ln C + H < K"
  shows "C * exp (-K) < exp (-H)"
proof -
  have "exp (ln C + -K) < exp (-H)"
    using gap by simp
  then show ?thesis using Cpos by (simp add: exp_diff exp_minus divide_inverse)
qed

context
  fixes P :: "int mpoly" and \<beta> :: "nat \<Rightarrow> rat"
    and a h :: "nat \<Rightarrow> real"
    and m :: nat and r :: "nat \<Rightarrow> nat"
    and L \<kappa> t0 :: real
  assumes box: "roth_poly_in_box m r P"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> \<kappa>" and Lpos: "0 \<le> L"
    and index: "ereal t0 \<le> roth_index m r a
      (replace_coeff (of_int::int \<Rightarrow> real) P)"
    and near: "\<And>v. abs (of_rat (\<beta> v) - a v) \<le> exp (-\<kappa> * h v)"
begin

theorem roth_index_transfer_abstract_gap:
  assumes gap: "\<And>J. roth_weight m r J < t1 \<Longrightarrow>
      real (card (roth_exponent_box m r)) ^ 2 *
        real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup (roth_hasse J P)) *
        (\<Prod>v<m. max 1 (abs (a v)) ^ r v) *
        exp (-\<kappa> * L * (t0 - roth_weight m r J)) <
      exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (\<beta> v)))"
  shows "ereal t1 \<le> roth_index m r \<beta>
    (replace_coeff (of_int::int \<Rightarrow> rat) P)"
proof (rule ccontr)
  assume not: "\<not> ereal t1 \<le> roth_index m r \<beta>
      (replace_coeff (of_int::int \<Rightarrow> rat) P)"
  have low: "roth_index m r \<beta>
      (replace_coeff (of_int::int \<Rightarrow> rat) P) < ereal t1"
    using not by simp
  obtain J where jw: "roth_weight m r J < t1"
    and jnz: "insertion \<beta> (replace_coeff (of_int::int \<Rightarrow> rat)
      (roth_hasse J P)) \<noteq> 0"
    by (rule roth_low_index_derivative[OF low])
  let ?Q = "roth_hasse J P"
  have qb: "roth_poly_in_box m r ?Q"
    by (rule roth_hasse_box_int[OF box])
  have qi: "ereal (t0 - roth_weight m r J) \<le>
      roth_index m r a (replace_coeff (of_int::int \<Rightarrow> real) ?Q)"
    using roth_index_hasse_from_lower[OF index, where J=J]
    by (simp add: roth_hasse_cast_real)
  have sandwich: "exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (\<beta> v))) \<le>
      real (card (roth_exponent_box m r)) ^ 2 *
        real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup ?Q) *
        (\<Prod>v<m. max 1 (abs (a v)) ^ r v) *
        exp (-\<kappa> * L * (t0 - roth_weight m r J))"
    by (rule roth_evaluation_sandwich_uniform[OF qb jnz rpos balance
      kpos Lpos qi near])
  show False using sandwich gap[OF jw] by linarith
qed

theorem roth_index_transfer_uniform_gap:
  assumes gap: "real (card (roth_exponent_box m r)) ^ 2 *
      real (4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs (a v)) ^ r v) *
      exp (-\<kappa> * L * (t0 - t1)) <
      exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (\<beta> v)))"
  shows "ereal t1 \<le> roth_index m r \<beta>
    (replace_coeff (of_int::int \<Rightarrow> rat) P)"
proof (rule roth_index_transfer_abstract_gap)
  fix J
  assume jw: "roth_weight m r J < t1"
  let ?F = "real (card (roth_exponent_box m r)) ^ 2 *
      (\<Prod>v<m. max 1 (abs (a v)) ^ r v)"
  let ?A = "real (2 ^ (\<Sum>v<m. r v) *
      roth_int_coeff_sup (roth_hasse J P))"
  let ?B = "real (4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P)"
  let ?U = "exp (-\<kappa> * L * (t0 - roth_weight m r J))"
  let ?V = "exp (-\<kappa> * L * (t0 - t1))"
  have ha: "?A \<le> ?B"
    using roth_hasse_coeff_sup_four[OF box, where J=J]
    by (metis of_nat_le_iff)
  have fpos: "0 \<le> ?F"
    by (intro mult_nonneg_nonneg prod_nonneg) simp_all
  have cpos: "0 \<le> ?B" by simp
  have uv: "?U \<le> ?V"
  proof -
    have kl: "0 \<le> \<kappa> * L" using kpos Lpos by simp
    have z: "\<kappa> * L * (t0 - t1) \<le>
        \<kappa> * L * (t0 - roth_weight m r J)"
      by (rule mult_left_mono[OF _ kl]) (use jw in auto)
    show ?thesis using z by (simp add: mult.assoc)
  qed
  have u0: "0 \<le> ?U" by simp
  have step1: "?F * ?A * ?U \<le> ?F * ?B * ?U"
    by (intro mult_right_mono mult_left_mono) (use ha fpos u0 in auto)
  have step2: "?F * ?B * ?U \<le> ?F * ?B * ?V"
    by (rule mult_left_mono[OF uv]) (use fpos cpos in auto)
  have bound: "?F * ?A * ?U \<le> ?F * ?B * ?V"
    using step1 step2 by linarith
  have eq1: "?F * ?A * ?U =
      real (card (roth_exponent_box m r)) ^ 2 *
        real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup (roth_hasse J P)) *
        (\<Prod>v<m. max 1 (abs (a v)) ^ r v) *
        exp (-\<kappa> * L * (t0 - roth_weight m r J))"
    by (simp add: mult_ac)
  have eq2: "?F * ?B * ?V =
      real (card (roth_exponent_box m r)) ^ 2 *
        real (4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
        (\<Prod>v<m. max 1 (abs (a v)) ^ r v) *
        exp (-\<kappa> * L * (t0 - t1))"
    by (simp add: mult_ac)
  show "real (card (roth_exponent_box m r)) ^ 2 *
        real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup (roth_hasse J P)) *
        (\<Prod>v<m. max 1 (abs (a v)) ^ r v) *
        exp (-\<kappa> * L * (t0 - roth_weight m r J)) <
      exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (\<beta> v)))"
    using bound gap eq1 eq2 by linarith
qed

theorem roth_index_transfer_log_gap:
  assumes gap: "ln (real (card (roth_exponent_box m r)) ^ 2 *
      real (4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs (a v)) ^ r v)) +
      (\<Sum>v<m. real (r v) * roth_rat_log_height (\<beta> v)) <
      \<kappa> * L * (t0 - t1)"
  shows "ereal t1 \<le> roth_index m r \<beta> (replace_coeff (of_int::int \<Rightarrow> rat) P)"
proof -
  define C where "C \<equiv> real (card (roth_exponent_box m r)) ^ 2 *
      real (4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs (a v)) ^ r v)"
  have card: "0 < card (roth_exponent_box m r)"
    using roth_box_card_pos[of m r] by simp
  have coeff: "0 < roth_int_coeff_sup P"
    using roth_int_coeff_sup_ge_one[of P] by simp
  have "0 < (\<Prod>v<m. max 1 (abs (a v)) ^ r v)"
    by (intro prod_pos) simp
  then have "0 < C" using card coeff by (simp add: C_def power2_eq_square)
  then have egap: "C * exp (- (\<kappa> * L * (t0 - t1))) 
             < exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (\<beta> v)))"
    using assms roth_exp_gap unfolding C_def by blast
  then show ?thesis
    using roth_index_transfer_uniform_gap by (simp add: C_def mult.assoc)
qed


end

lemma roth_box_card_pow16:
  "card (roth_exponent_box m r) ^ 2 * 4 ^ (\<Sum>v<m. r v) \<le> 16 ^ (\<Sum>v<m. r v)"
proof -
  let ?S = "(\<Sum>v<m. r v)"
  have "card (roth_exponent_box m r) ^ 2 * 4 ^ ?S \<le> (2 ^ ?S) ^ 2 * 4 ^ ?S"
    using roth_exponent_box_card_exp_bound 
    by (intro mult_right_mono power_mono) simp_all
  also have "... = 16 ^ ?S"
    by (simp add: power2_eq_square flip: power_mult_distrib)
  finally show ?thesis .
qed

lemma roth_box_log_cost:
  fixes P :: "int mpoly" and \<alpha> :: real
  shows "ln (real (card (roth_exponent_box m r)) ^ 2 *
      real (4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs \<alpha>) ^ r v)) \<le>
    ln (real (roth_int_coeff_sup P)) +
      real (\<Sum>v<m. r v) * ln (16 * max 1 (abs \<alpha>))"
proof -
  let ?S = "(\<Sum>v<m. r v)"
  let ?A = "max 1 (abs \<alpha>)"
  let ?V = "real (roth_int_coeff_sup P)"
  let ?C = "real (card (roth_exponent_box m r)) ^ 2 *
      real (4 ^ ?S * roth_int_coeff_sup P) * (\<Prod>v<m. ?A ^ r v)"
  define D where "D \<equiv> ?V * (16 * ?A) ^ ?S"
  have Vpos: "0 < ?V" using roth_int_coeff_sup_ge_one[of P] by simp
  have cardpos: "0 < real (card (roth_exponent_box m r))"
    using roth_box_card_pos[of m r] by simp
  have prodpos: "0 < (\<Prod>v<m. ?A ^ r v)"
    by (intro prod_pos) auto
  have Cpos: "0 < ?C" using cardpos Vpos prodpos
    by (simp add: power2_eq_square)
  have card: "real (card (roth_exponent_box m r) ^ 2 * 4 ^ ?S) \<le>
      real (16 ^ ?S)"
    using roth_box_card_pow16[of m r] by (metis of_nat_le_iff)
  have "?C = (card (roth_exponent_box m r) ^ 2 * 4 ^ ?S) * ?V * ?A ^ ?S"
    by (simp add: of_nat_power power_sum mult.assoc)
  also have "\<dots> \<le> (16 ^ ?S) * ?V * ?A ^ ?S"
    using card Vpos by (intro mult_right_mono) auto
  also have "\<dots> = D"
    by (simp add: D_def of_nat_power power_mult_distrib mult_ac)
  finally have logs: "ln ?C \<le> ln D"
    using Cpos ln_mono by presburger
  have "ln D = ln ?V + real ?S * ln (16 * ?A)"
    using Vpos by (simp add: D_def ln_mult ln_realpow algebra_simps)
  then show ?thesis using logs by simp
qed

lemma roth_auxiliary_height_log:
  assumes bpos: "1 \<le> b"
    and ph: "roth_int_coeff_sup P \<le> nat (2 * (4 * b) ^ S)"
  shows "ln (real (roth_int_coeff_sup P)) \<le> ln 2 + real S * ln (4 * real_of_int b)"
  using roth_int_coeff_sup_log_mono[OF ph] bpos
  by (simp add: ln_mult ln_realpow algebra_simps)

lemma roth_weighted_height_sum_le:
  fixes h :: "nat \<Rightarrow> real"
  assumes upper: "\<And>v. v < m \<Longrightarrow> real (r v) * h v \<le> U"
  shows "(\<Sum>v<m. real (r v) * h v) \<le> real m * U"
proof -
  have "(\<Sum>v<m. real (r v) * h v) \<le> (\<Sum>v<m. U)"
    by (intro sum_mono) (use upper in auto)
  then show ?thesis by simp
qed


end
