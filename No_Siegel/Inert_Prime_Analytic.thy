theory Inert_Prime_Analytic
  imports Inert_Prime_Formula "Prime_Number_Theorem.Mertens_Theorems"
begin

declare [[apply_timeout = 20]]

text \<open>Green, Section 6: bounds for the reciprocal-prime, theta,
  and inverse-square error terms in the final comparison.\<close>

lemma green_odd_inert_sum_le_all_primes:
  fixes f :: "nat \<Rightarrow> real"
  assumes nonneg: "\<And>p. prime p \<Longrightarrow> p \<le> X \<Longrightarrow> 0 \<le> f p"
  shows "(\<Sum>p\<in>green_odd_inert_primes chi X. f p) \<le>
    (\<Sum>p | prime p \<and> p \<le> X. f p)"
proof -
  let ?P = "{p::nat. prime p \<and> p \<le> X}"
  have subset: "green_odd_inert_primes chi X \<subseteq> ?P"
    by (auto simp: green_odd_inert_primes_def green_inert_primes_def)
  have finite: "finite ?P"
    by (rule finite_subset[of ?P "{..X}"]) auto
  show ?thesis
    by (rule sum_mono2[OF finite subset]) (use nonneg in auto)
qed

lemma green_odd_inert_prime_weight_bound:
  assumes "1 \<le> X"
  shows "green_odd_inert_prime_weight chi X \<le> ln (real X) + 2"
proof -
  have "green_odd_inert_prime_weight chi X \<le>
      (\<Sum>p | prime p \<and> p \<le> X. ln (real p) / real p)"
    unfolding green_odd_inert_prime_weight_def
    by (rule green_odd_inert_sum_le_all_primes)
      (auto simp: divide_nonneg_pos dest: prime_gt_1_nat)
  also have "... = primes_M (real X)"
    by (simp add: primes_M_def prime_sum_upto_def)
  also have "... < ln (real X) + 2"
    using mertens_first_theorem[of "real X"] assms
    by (simp add: abs_less_iff)
  finally show ?thesis by simp
qed

lemma green_odd_inert_theta_bound:
  assumes "1 \<le> X"
  shows "green_odd_inert_theta chi X \<le> ln 4 * real X"
proof -
  have "green_odd_inert_theta chi X \<le>
      (\<Sum>p | prime p \<and> p \<le> X. ln (real p))"
    unfolding green_odd_inert_theta_def
    by (rule green_odd_inert_sum_le_all_primes)
      (auto dest: prime_gt_1_nat)
  also have "... = primes_theta (real X)"
    by (simp add: primes_theta_def prime_sum_upto_def)
  also have "... < ln 4 * real X"
    using \<theta>_upper_bound[of "real X"] assms by simp
  finally show ?thesis by simp
qed

lemma green_odd_inert_inverse_square_weight_bound:
  "green_odd_inert_inverse_square_weight chi X \<le> 2"
proof -
  let ?I = "green_odd_inert_primes chi X"
  let ?A = "(\<lambda>p::nat. (p, 2::nat)) ` ?I"
  let ?B = "{z::nat \<times> nat. case z of (p, i) \<Rightarrow>
    prime p \<and> i > 1 \<and> real (p ^ i) \<le> real (X ^ 2)}"
  let ?f = "\<lambda>z::nat \<times> nat. case z of (p, i) \<Rightarrow>
    ln (real p) / real (p ^ i)"
  have subset: "?A \<subseteq> ?B"
  proof
    fix z assume "z \<in> ?A"
    then obtain p where p: "p \<in> ?I" "z = (p, 2)" by auto
    have "p \<le> X"
      using p by (auto simp: green_odd_inert_primes_def green_inert_primes_def)
    then have "p ^ 2 \<le> X ^ 2" by (intro power_mono) simp_all
    with p show "z \<in> ?B"
      by (auto simp: green_odd_inert_primes_def green_inert_primes_def)
  qed
  have finite: "finite ?B"
  proof (rule finite_subset[of ?B "{..X ^ 2} \<times> {..X ^ 2}"])
    show "?B \<subseteq> {..X ^ 2} \<times> {..X ^ 2}"
    proof
      fix z assume "z \<in> ?B"
      then obtain p i where z: "z = (p, i)"
        and prime: "prime p"
        and ilarge: "i > 1"
        and le_real: "real (p ^ i) \<le> real (X ^ 2)"
        by (cases z) auto
      have le: "p ^ i \<le> X ^ 2"
        by (rule of_nat_le_iff[THEN iffD1]) (rule le_real)
      have pge: "2 \<le> p" using prime_gt_1_nat[OF prime] by linarith
      have ilt: "i < 2 ^ i" by (rule less_exp)
      have "2 ^ i \<le> p ^ i"
        by (rule power_mono[OF pge]) simp
      then have "i \<le> X ^ 2" using ilt le by linarith
      moreover have "p \<le> p ^ i"
      proof -
        have "p ^ 1 \<le> p ^ i"
          using ilarge pge by (intro power_increasing) auto
        then show ?thesis by simp
      qed
      ultimately show "z \<in> {..X ^ 2} \<times> {..X ^ 2}"
        using le z by auto
    qed
  qed simp
  have nonneg: "0 \<le> ?f z" if "z \<in> ?B" for z
  proof -
    obtain p i where z: "z = (p, i)" by (cases z) auto
    have "prime p" using that z by auto
    then have "1 < p" by (rule prime_gt_1_nat)
    then show ?thesis using z by (simp add: divide_nonneg_pos)
  qed
  have reindex:
    "(\<Sum>z\<in>?A. ?f z) = green_odd_inert_inverse_square_weight chi X"
    unfolding green_odd_inert_inverse_square_weight_def
    by (rule sum.reindex_cong) (auto simp: inj_on_def)
  have "green_odd_inert_inverse_square_weight chi X \<le> (\<Sum>z\<in>?B. ?f z)"
    unfolding reindex[symmetric] by (rule sum_mono2[OF finite subset])
      (use nonneg in auto)
  also have "... < 9 / pi ^ 2"
    by (rule mertens_remainder_aux_bound[where x="real (X ^ 2)"])
  also have "... \<le> 2"
  proof -
    have pos: "0 < pi ^ 2" using pi_gt3 by simp
    have sq: "(3::real) ^ 2 \<le> pi ^ 2"
      by (rule power_mono) (use pi_gt3 in auto)
    have "9 \<le> pi ^ 2" using sq by simp
    also have "... \<le> 2 * pi ^ 2"
    proof -
      have "1 * pi ^ 2 \<le> 2 * pi ^ 2"
        by (rule mult_right_mono) (use pos in simp_all)
      then show ?thesis by simp
    qed
    finally have "9 \<le> 2 * pi ^ 2" .
    then show ?thesis using pos by (simp add: divide_le_eq)
  qed
  finally show ?thesis by simp
qed

declare [[apply_timeout = 0]]

end
