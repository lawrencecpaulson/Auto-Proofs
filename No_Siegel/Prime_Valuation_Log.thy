theory Prime_Valuation_Log
  imports Complex_Main "HOL-Computational_Algebra.Primes"
begin

definition green_inert_primes :: "(nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> nat set" where
  "green_inert_primes chi X =
    {p. prime p \<and> p \<le> X \<and> chi p = -1}"

definition green_odd_inert_primes :: "(nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> nat set" where
  "green_odd_inert_primes chi X =
    {p \<in> green_inert_primes chi X. odd p}"

definition green_inert_prime_weight :: "(nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> real" where
  "green_inert_prime_weight chi X =
    (\<Sum>p\<in>green_inert_primes chi X. ln (real p) / real p)"

definition green_odd_inert_prime_weight :: "(nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> real" where
  "green_odd_inert_prime_weight chi X =
    (\<Sum>p\<in>green_odd_inert_primes chi X. ln (real p) / real p)"

lemma green_inert_primes_finite [simp]:
  "finite (green_inert_primes chi X)"
  by (rule finite_subset[of _ "{..X}"])
    (auto simp: green_inert_primes_def)

lemma green_odd_inert_primes_finite [simp]:
  "finite (green_odd_inert_primes chi X)"
  by (simp add: green_odd_inert_primes_def)

lemma green_inert_primes_odd_split:
  "green_inert_primes chi X =
    (if 2 \<le> X \<and> chi 2 = -1
      then insert 2 (green_odd_inert_primes chi X)
      else green_odd_inert_primes chi X)"
proof -
  have cases: "p = 2 \<or> odd p" if "prime p" for p :: nat
  proof (cases "p = 2")
    case False
    have "2 < p" using prime_gt_1_nat[OF that] False by linarith
    then have "odd p" using prime_odd_nat[OF that] by simp
    then show ?thesis by simp
  qed simp
  show ?thesis
    using cases
    by (auto simp: green_odd_inert_primes_def green_inert_primes_def)
qed

lemma green_inert_prime_weight_split:
  "green_inert_prime_weight chi X =
    green_odd_inert_prime_weight chi X +
      (if 2 \<le> X \<and> chi 2 = -1 then ln 2 / 2 else 0)"
proof (cases "2 \<le> X \<and> chi 2 = -1")
  case True
  have "green_inert_primes chi X = insert 2 (green_odd_inert_primes chi X)"
    using green_inert_primes_odd_split[of chi X] True by simp
  moreover have "2 \<notin> green_odd_inert_primes chi X"
    by (simp add: green_odd_inert_primes_def)
  ultimately show ?thesis
    using True by (simp add: green_inert_prime_weight_def
      green_odd_inert_prime_weight_def)
next
  case False
  have "green_inert_primes chi X = green_odd_inert_primes chi X"
    using green_inert_primes_odd_split[of chi X] False by simp
  then show ?thesis
    using False by (simp add: green_inert_prime_weight_def
      green_odd_inert_prime_weight_def)
qed

lemma green_inert_prime_weight_two_correction:
  "green_inert_prime_weight chi X <
    green_odd_inert_prime_weight chi X + 1"
proof -
  have "ln (2::real) / 2 < 1"
    using ln_less_self[of 2] by simp
  then show ?thesis
    by (simp add: green_inert_prime_weight_split)
qed

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

end
