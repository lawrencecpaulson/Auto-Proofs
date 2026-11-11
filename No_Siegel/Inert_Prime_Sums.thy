theory Inert_Prime_Sums
  imports Complex_Main "HOL-Computational_Algebra.Primes"
begin

declare [[apply_timeout = 20]]

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

declare [[apply_timeout = 0]]

end
