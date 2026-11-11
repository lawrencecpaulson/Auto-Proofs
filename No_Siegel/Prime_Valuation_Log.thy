theory Prime_Valuation_Log
  imports Inert_Prime_Sums
begin

declare [[apply_timeout = 20]]

lemma green_log_prime_factorization:
  fixes n :: nat
  assumes n: "0 < n"
  shows "ln (real n) =
    (\<Sum>p\<in>prime_factors n. real (multiplicity p n) * ln (real p))"
proof -
  have factorization:
    "real n = (\<Prod>p\<in>prime_factors n. (real p) ^ multiplicity p n)"
  proof -
    have "real n =
        real (\<Prod>p\<in>prime_factors n. p ^ multiplicity p n)"
      using prime_factorization_nat[OF n] by simp
    also have "... =
        (\<Prod>p\<in>prime_factors n. (real p) ^ multiplicity p n)"
      by (simp add: of_nat_prod)
    finally show ?thesis .
  qed
  have nonzero: "(real p) ^ multiplicity p n \<noteq> 0"
    if "p \<in> prime_factors n" for p
  proof -
    have "prime p" using that by auto
    then have "1 < p" by (rule prime_gt_1_nat)
    then show ?thesis by simp
  qed
  have log_product:
    "ln (\<Prod>p\<in>prime_factors n. (real p) ^ multiplicity p n) =
      (\<Sum>p\<in>prime_factors n. ln ((real p) ^ multiplicity p n))"
  proof (rule ln_prod)
    show "finite (prime_factors n)" by simp
    fix p assume "p \<in> prime_factors n"
    then show "(real p) ^ multiplicity p n \<noteq> 0"
      by (rule nonzero)
  qed
  have "ln (real n) =
      ln (\<Prod>p\<in>prime_factors n. (real p) ^ multiplicity p n)"
    by (simp only: factorization)
  also have "... =
      (\<Sum>p\<in>prime_factors n. ln ((real p) ^ multiplicity p n))"
    by (rule log_product)
  also have "... =
      (\<Sum>p\<in>prime_factors n. real (multiplicity p n) * ln (real p))"
    by (simp add: ln_realpow)
  finally show ?thesis .
qed

lemma green_weighted_prime_valuation_log:
  fixes n :: nat and h :: "nat \<Rightarrow> nat"
  assumes n: "0 < n" and finite: "finite P"
    and prime: "\<And>p. p \<in> P \<Longrightarrow> prime p"
    and bound: "\<And>p. p \<in> P \<Longrightarrow> h p \<le> multiplicity p n"
  shows "(\<Sum>p\<in>P. real (h p) * ln (real p)) \<le> ln (real n)"
proof -
  let ?F = "prime_factors n"
  let ?f = "\<lambda>p. real (multiplicity p n) * ln (real p)"
  have log_nonneg: "0 \<le> ln (real p)" if "prime p" for p :: nat
    using prime_gt_1_nat[OF that] by simp
  have first: "(\<Sum>p\<in>P. real (h p) * ln (real p)) \<le>
      (\<Sum>p\<in>P. ?f p)"
    by (rule sum_mono) (use prime bound log_nonneg in
      \<open>auto intro!: mult_right_mono\<close>)
  have zero: "?f p = 0" if "p \<in> P - ?F" for p
    using that prime[of p]
    by (auto simp: prime_factors_multiplicity)
  have restrict: "(\<Sum>p\<in>P. ?f p) = (\<Sum>p\<in>P \<inter> ?F. ?f p)"
    by (rule sum.mono_neutral_right[OF finite]) (use zero in auto)
  have rest: "(\<Sum>p\<in>P \<inter> ?F. ?f p) \<le> (\<Sum>p\<in>?F. ?f p)"
    by (rule sum_mono2) (auto intro!: mult_nonneg_nonneg log_nonneg)
  show ?thesis
    using first restrict rest green_log_prime_factorization[OF n] by linarith
qed

lemma green_multiplicity_int_nat:
  fixes D :: int
  assumes D: "0 \<le> D"
  shows "multiplicity (int p) D = multiplicity p (nat D)"
proof -
  have D_eq: "int (nat D) = D" using D by simp
  have dvd: "((int p) ^ k dvd D) = (p ^ k dvd nat D)" for k
  proof -
    have "((int p) ^ k dvd D) = (int (p ^ k) dvd D)"
      by simp
    also have "... = (int (p ^ k) dvd int (nat D))"
      by (simp only: D_eq)
    also have "... = (p ^ k dvd nat D)"
      by (rule int_dvd_int_iff)
    finally show ?thesis .
  qed
  have sets: "{k. (int p) ^ k dvd D} = {k. p ^ k dvd nat D}"
    using dvd by auto
  show ?thesis by (simp only: multiplicity_def sets)
qed

lemma green_weighted_integer_prime_valuation_log:
  fixes D :: int and h :: "nat \<Rightarrow> nat"
  assumes D: "0 < D" and finite: "finite P"
    and prime: "\<And>p. p \<in> P \<Longrightarrow> prime p"
    and bound: "\<And>p. p \<in> P \<Longrightarrow>
      h p \<le> multiplicity (int p) D"
  shows "(\<Sum>p\<in>P. real (h p) * ln (real p)) \<le> ln (real_of_int D)"
proof -
  have n: "0 < nat D" using D by simp
  have bound': "h p \<le> multiplicity p (nat D)" if "p \<in> P" for p
    using bound[OF that] green_multiplicity_int_nat[of D p] D by simp
  have "(\<Sum>p\<in>P. real (h p) * ln (real p)) \<le> ln (real (nat D))"
    by (rule green_weighted_prime_valuation_log[OF n finite prime bound'])
  then show ?thesis using D by simp
qed

declare [[apply_timeout = 0]]

end
