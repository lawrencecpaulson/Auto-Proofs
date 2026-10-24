theory Roth_Index_Transfer
  imports Roth_Evaluation_Height
begin

theorem roth_evaluation_sandwich_uniform:
  fixes P :: "int mpoly" and beta :: "nat \<Rightarrow> rat"
    and a h :: "nat \<Rightarrow> real"
  assumes box: "roth_poly_in_box m r P"
    and nz: "insertion beta (replace_coeff of_int P) \<noteq> (0::rat)"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa" and Lpos: "0 \<le> L"
    and index: "ereal theta \<le> roth_index m r a
      (replace_coeff (of_int::int \<Rightarrow> real) P)"
    and near: "\<And>v. abs (of_rat (beta v) - a v) \<le> exp (-kappa * h v)"
  shows "exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v))) \<le>
    real (card (roth_exponent_box m r)) ^ 2 *
      real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs (a v)) ^ r v) *
      exp (-kappa * L * theta)"
proof -
  let ?C = "real (card (roth_exponent_box m r))"
  let ?S = "Poly_Mapping.keys (mapping_of
      (roth_translate a (replace_coeff (of_int::int \<Rightarrow> real) P)))"
  let ?V = "real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P)"
  let ?E = "(\<Prod>v<m. max 1 (abs (a v)) ^ r v)"
  let ?W = "exp (-kappa * L * theta)"
  have raw: "exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v))) \<le>
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
  have bound: "exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v))) \<le>
      (?C * ?V * ?E) * ?C * ?W"
    using raw scale2 by linarith
  have factor: "(?C * ?V * ?E) * ?C * ?W =
      ?C ^ 2 * ?V * ?E * ?W"
    by (simp add: power2_eq_square mult_ac)
  show ?thesis using bound factor by metis
qed

theorem roth_index_transfer_abstract_gap:
  fixes P :: "int mpoly" and beta :: "nat \<Rightarrow> rat"
    and a h :: "nat \<Rightarrow> real"
  assumes box: "roth_poly_in_box m r P"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa" and Lpos: "0 \<le> L"
    and index: "ereal t0 \<le> roth_index m r a
      (replace_coeff (of_int::int \<Rightarrow> real) P)"
    and near: "\<And>v. abs (of_rat (beta v) - a v) \<le> exp (-kappa * h v)"
    and gap: "\<And>J. roth_weight m r J < t1 \<Longrightarrow>
      real (card (roth_exponent_box m r)) ^ 2 *
        real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup (roth_hasse J P)) *
        (\<Prod>v<m. max 1 (abs (a v)) ^ r v) *
        exp (-kappa * L * (t0 - roth_weight m r J)) <
      exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v)))"
  shows "ereal t1 \<le> roth_index m r beta
    (replace_coeff (of_int::int \<Rightarrow> rat) P)"
proof (rule ccontr)
  assume not: "\<not> ereal t1 \<le> roth_index m r beta
      (replace_coeff (of_int::int \<Rightarrow> rat) P)"
  have low: "roth_index m r beta
      (replace_coeff (of_int::int \<Rightarrow> rat) P) < ereal t1"
    using not by simp
  obtain J where jw: "roth_weight m r J < t1"
    and jnz: "insertion beta (replace_coeff (of_int::int \<Rightarrow> rat)
      (roth_hasse J P)) \<noteq> 0"
    by (rule roth_low_index_derivative[OF low])
  let ?Q = "roth_hasse J P"
  have qb: "roth_poly_in_box m r ?Q"
    by (rule roth_hasse_box_int[OF box])
  have qi: "ereal (t0 - roth_weight m r J) \<le>
      roth_index m r a (replace_coeff (of_int::int \<Rightarrow> real) ?Q)"
    using roth_index_hasse_from_lower[OF index, of J]
    by (simp add: roth_hasse_cast_real)
  have sandwich: "exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v))) \<le>
      real (card (roth_exponent_box m r)) ^ 2 *
        real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup ?Q) *
        (\<Prod>v<m. max 1 (abs (a v)) ^ r v) *
        exp (-kappa * L * (t0 - roth_weight m r J))"
    by (rule roth_evaluation_sandwich_uniform[OF qb jnz rpos balance
      kpos Lpos qi near])
  show False using sandwich gap[OF jw] by linarith
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

theorem roth_index_transfer_uniform_gap:
  fixes P :: "int mpoly" and beta :: "nat \<Rightarrow> rat"
    and a h :: "nat \<Rightarrow> real"
  assumes box: "roth_poly_in_box m r P"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa" and Lpos: "0 \<le> L"
    and index: "ereal t0 \<le> roth_index m r a
      (replace_coeff (of_int::int \<Rightarrow> real) P)"
    and near: "\<And>v. abs (of_rat (beta v) - a v) \<le> exp (-kappa * h v)"
    and gap: "real (card (roth_exponent_box m r)) ^ 2 *
      real (4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs (a v)) ^ r v) *
      exp (-kappa * L * (t0 - t1)) <
      exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v)))"
  shows "ereal t1 \<le> roth_index m r beta
    (replace_coeff (of_int::int \<Rightarrow> rat) P)"
proof (rule roth_index_transfer_abstract_gap[OF box rpos balance
    kpos Lpos index near])
  fix J
  assume jw: "roth_weight m r J < t1"
  let ?F = "real (card (roth_exponent_box m r)) ^ 2 *
      (\<Prod>v<m. max 1 (abs (a v)) ^ r v)"
  let ?A = "real (2 ^ (\<Sum>v<m. r v) *
      roth_int_coeff_sup (roth_hasse J P))"
  let ?B = "real (4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P)"
  let ?U = "exp (-kappa * L * (t0 - roth_weight m r J))"
  let ?V = "exp (-kappa * L * (t0 - t1))"
  have ha: "?A \<le> ?B"
    using roth_hasse_coeff_sup_four[OF box, of J] by (metis of_nat_le_iff)
  have fpos: "0 \<le> ?F"
    by (intro mult_nonneg_nonneg prod_nonneg) simp_all
  have cpos: "0 \<le> ?B" by simp
  have uv: "?U \<le> ?V"
  proof -
    have kl: "0 \<le> kappa * L" using kpos Lpos by simp
    have z: "kappa * L * (t0 - t1) \<le>
        kappa * L * (t0 - roth_weight m r J)"
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
        exp (-kappa * L * (t0 - roth_weight m r J))"
    by (simp add: mult_ac)
  have eq2: "?F * ?B * ?V =
      real (card (roth_exponent_box m r)) ^ 2 *
        real (4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
        (\<Prod>v<m. max 1 (abs (a v)) ^ r v) *
        exp (-kappa * L * (t0 - t1))"
    by (simp add: mult_ac)
  show "real (card (roth_exponent_box m r)) ^ 2 *
        real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup (roth_hasse J P)) *
        (\<Prod>v<m. max 1 (abs (a v)) ^ r v) *
        exp (-kappa * L * (t0 - roth_weight m r J)) <
      exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v)))"
    using bound gap eq1 eq2 by linarith
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

theorem roth_index_transfer_log_gap:
  fixes P :: "int mpoly" and beta :: "nat \<Rightarrow> rat"
    and a h :: "nat \<Rightarrow> real"
  assumes box: "roth_poly_in_box m r P"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa" and Lpos: "0 \<le> L"
    and index: "ereal t0 \<le> roth_index m r a
      (replace_coeff (of_int::int \<Rightarrow> real) P)"
    and near: "\<And>v. abs (of_rat (beta v) - a v) \<le> exp (-kappa * h v)"
    and gap: "ln (real (card (roth_exponent_box m r)) ^ 2 *
      real (4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs (a v)) ^ r v)) +
      (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v)) <
      kappa * L * (t0 - t1)"
  shows "ereal t1 \<le> roth_index m r beta
    (replace_coeff (of_int::int \<Rightarrow> rat) P)"
proof -
  let ?C = "real (card (roth_exponent_box m r)) ^ 2 *
      real (4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs (a v)) ^ r v)"
  let ?H = "(\<Sum>v<m. real (r v) * roth_rat_log_height (beta v))"
  have card: "0 < real (card (roth_exponent_box m r))"
    using roth_box_card_pos[of m r] by simp
  have coeff: "0 < real (roth_int_coeff_sup P)"
    using roth_int_coeff_sup_ge_one[of P] by simp
  have prod: "0 < (\<Prod>v<m. max 1 (abs (a v)) ^ r v)"
    by (intro prod_pos) simp
  have Cpos: "0 < ?C" using card coeff prod
    by (simp add: power2_eq_square)
  have egap: "?C * exp (- (kappa * L * (t0 - t1))) < exp (-?H)"
    by (rule roth_exp_gap[OF Cpos gap])
  have numgap: "real (card (roth_exponent_box m r)) ^ 2 *
      real (4 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs (a v)) ^ r v) *
      exp (-kappa * L * (t0 - t1)) <
      exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v)))"
    using egap by (simp add: mult.assoc)
  show ?thesis
    by (rule roth_index_transfer_uniform_gap[OF box rpos balance
      kpos Lpos index near numgap])
qed


lemma roth_box_card_pow16:
  "card (roth_exponent_box m r) ^ 2 * 4 ^ (\<Sum>v<m. r v) \<le>
    (16::nat) ^ (\<Sum>v<m. r v)"
proof -
  let ?S = "(\<Sum>v<m. r v)"
  have c: "card (roth_exponent_box m r) \<le> (2::nat) ^ ?S"
    by (rule roth_exponent_box_card_exp_bound)
  have "card (roth_exponent_box m r) ^ 2 * 4 ^ ?S \<le>
      ((2::nat) ^ ?S) ^ 2 * 4 ^ ?S"
    using c by (intro mult_right_mono power_mono) simp_all
  also have "... = (4::nat) ^ ?S * 4 ^ ?S"
    by (simp add: power2_eq_square power_mult_distrib[symmetric])
  also have "... = 16 ^ ?S"
    by (simp add: power_mult_distrib[symmetric])
  finally show ?thesis .
qed

end
