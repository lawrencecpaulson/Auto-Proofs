theory Ramanujan_Constant
  imports
    "HOL-Decision_Procs.Approximation"
    "Gelfond_Schneider_Standalone.Gelfond_Schneider"
begin

section \<open>Ramanujan's Constant\<close>

text \<open>
  The number @{term "exp (pi * sqrt 163)"} is famously extremely close to an integer:
  \[
    e^{\pi \sqrt{163}} = 262537412640768744 - \varepsilon
  \]
  for a tiny positive \<open>\<varepsilon>\<close>.
\<close>

definition ramanujan_constant :: real
  where "ramanujan_constant = exp (pi * sqrt 163)"

definition ramanujan_near_integer :: int
  where "ramanujan_near_integer = 262537412640768744"

lemma ramanujan_constant_below_integer:
  "ramanujan_constant < of_int ramanujan_near_integer"
  unfolding ramanujan_constant_def ramanujan_near_integer_def
  by (approximation 110)

lemma ramanujan_constant_above_integer_minus:
  "of_int ramanujan_near_integer - inverse (10 ^ 12 :: real) < ramanujan_constant"
  unfolding ramanujan_constant_def ramanujan_near_integer_def
  by (approximation 110)

lemma ramanujan_constant_small_gap:
  "0 < of_int ramanujan_near_integer - ramanujan_constant \<and>
   of_int ramanujan_near_integer - ramanujan_constant < inverse (10 ^ 12 :: real)"
  using ramanujan_constant_below_integer ramanujan_constant_above_integer_minus
  by linarith

theorem ramanujan_constant_integer_minus_epsilon:
  "\<exists>\<epsilon>::real. 0 < \<epsilon> \<and> \<epsilon> < inverse (10 ^ 12) \<and>
     ramanujan_constant = of_int ramanujan_near_integer - \<epsilon>"
proof -
  let ?\<epsilon> = "of_int ramanujan_near_integer - ramanujan_constant"
  have "0 < ?\<epsilon> \<and> ?\<epsilon> < inverse (10 ^ 12 :: real)"
    using ramanujan_constant_small_gap .
  moreover have "ramanujan_constant = of_int ramanujan_near_integer - ?\<epsilon>"
    by simp
  ultimately show ?thesis
    by blast
qed

corollary ramanujan_constant_not_integer:
  "ramanujan_constant \<notin> \<int>"
proof
  assume "ramanujan_constant \<in> \<int>"
  then obtain n :: int where n: "ramanujan_constant = of_int n"
    unfolding Ints_def by blast
  from ramanujan_constant_small_gap have
    gap_pos: "0 < of_int ramanujan_near_integer - ramanujan_constant"
    and gap_lt: "of_int ramanujan_near_integer - ramanujan_constant < inverse (10 ^ 12 :: real)"
    by auto
  have eps_lt_one: "inverse (10 ^ 12 :: real) < 1"
    by simp
  have lower: "of_int ramanujan_near_integer - 1 < ramanujan_constant"
    using gap_lt eps_lt_one by linarith
  have upper: "ramanujan_constant < of_int ramanujan_near_integer"
    using gap_pos by linarith
  have lower_int: "ramanujan_near_integer - 1 < n"
    using lower n by simp
  have upper_int: "n < ramanujan_near_integer"
    using upper n by simp
  from lower_int upper_int show False
    by linarith
qed

theorem ramanujan_constant_transcendental:
  "\<not> algebraic ramanujan_constant"
proof -
  let ?b = "- (\<i> * of_real (sqrt (163::real)))"
  have sqrt_alg: "algebraic (sqrt (163::real))"
    by (intro algebraic_sqrt) simp
  have cast_alg: "algebraic (of_real (sqrt (163::real)) :: complex)"
    by (rule algebraic_of_real[OF sqrt_alg])
  have product_alg: "algebraic (\<i> * of_real (sqrt (163::real)))"
    by (rule algebraic_times) (use cast_alg in auto)
  have b_alg: "algebraic ?b"
    by (rule algebraic_uminus[OF product_alg])
  have b_irr: "?b \<notin> \<rat>"
  proof
    assume "?b \<in> \<rat>"
    then obtain r :: rat where r: "?b = of_rat r"
      by (auto simp: Rats_def)
    have "Im (of_rat r :: complex) = 0"
      by (cases r) (simp add: of_rat_rat Im_divide)
    then have "Im ?b = 0"
      using r by simp
    then show False by simp
  qed
  have log: "of_real pi * \<i> \<in> log_values (-1::complex)"
    by simp
  have arg_eq: "?b * (of_real pi * \<i>) = of_real (pi * sqrt (163::real))"
    by (simp add: algebra_simps)
  have exp_eq:
    "exp (?b * (of_real pi * \<i>)) = (of_real ramanujan_constant :: complex)"
  proof -
    have "exp (?b * (of_real pi * \<i>)) =
        exp (of_real (pi * sqrt (163::real)))"
      using arg_eq by simp
    also have "\<dots> = (of_real ramanujan_constant :: complex)"
      by (simp only: exp_of_real ramanujan_constant_def)
    finally show ?thesis .
  qed
  have wmem: "(of_real ramanujan_constant :: complex) \<in> power_values (-1) ?b"
  proof -
    have "\<exists>z\<in>log_values (-1::complex).
        of_real ramanujan_constant = exp (?b * z)"
      by (rule bexI[where x="of_real pi * \<i>"]) (use log exp_eq in auto)
    then show ?thesis
      by (simp add: power_values_def)
  qed
  have "\<not> algebraic (of_real ramanujan_constant :: complex)"
    by (rule gelfond_schneider[of "-1" ?b "of_real ramanujan_constant"])
       (use b_alg b_irr wmem in auto)
  then show ?thesis by simp
qed

end
