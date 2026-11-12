theory Inert_Frobenius
  imports Quadratic_Gram
begin

text \<open>Green, Section 5: divisibility inside the quadratic integer lattice.\<close>

definition green_quad_divisible :: "nat \<Rightarrow> int \<Rightarrow> complex \<Rightarrow> bool" where
  "green_quad_divisible p d z \<longleftrightarrow>
    (\<exists>w. green_quadratic_integer d w \<and> z = of_nat p * w)"

lemma green_quad_divisible_add:
  assumes z: "green_quad_divisible p d z"
    and w: "green_quad_divisible p d w"
  shows "green_quad_divisible p d (z + w)"
proof -
  obtain a where a: "green_quadratic_integer d a" "z = of_nat p * a"
    using z by (auto simp: green_quad_divisible_def)
  obtain b where b: "green_quadratic_integer d b" "w = of_nat p * b"
    using w by (auto simp: green_quad_divisible_def)
  have "green_quadratic_integer d (a + b)"
    by (rule green_quadratic_integer_add[OF a(1) b(1)])
  moreover have "z + w = of_nat p * (a + b)"
    using a b by (simp add: algebra_simps)
  ultimately show ?thesis by (auto simp: green_quad_divisible_def)
qed

lemma green_quad_divisible_minus:
  assumes "green_quad_divisible p d z"
  shows "green_quad_divisible p d (-z)"
proof -
  obtain a where a: "green_quadratic_integer d a" "z = of_nat p * a"
    using assms by (auto simp: green_quad_divisible_def)
  have "green_quadratic_integer d (-a)"
    by (rule green_quadratic_integer_minus[OF a(1)])
  moreover have "-z = of_nat p * (-a)"
    using a by simp
  ultimately show ?thesis by (auto simp: green_quad_divisible_def)
qed

lemma green_quad_divisible_mult:
  assumes a: "green_quadratic_integer d a"
    and z: "green_quad_divisible p d z"
  shows "green_quad_divisible p d (a * z)"
proof -
  obtain b where b: "green_quadratic_integer d b" "z = of_nat p * b"
    using z by (auto simp: green_quad_divisible_def)
  have "green_quadratic_integer d (a * b)"
    by (rule green_quadratic_integer_mult[OF a b(1)])
  moreover have "a * z = of_nat p * (a * b)"
    using b by (simp add: algebra_simps)
  ultimately show ?thesis by (auto simp: green_quad_divisible_def)
qed

lemma green_quad_divisible_of_int:
  assumes "int p dvd a"
  shows "green_quad_divisible p d (of_int a)"
proof -
  obtain k where k: "a = int p * k"
    using assms by (auto simp: dvd_def)
  have "green_quadratic_integer d (of_int k)" by simp
  moreover have "(of_int a::complex) = of_nat p * of_int k"
    using k by simp
  ultimately show ?thesis
    unfolding green_quad_divisible_def by blast
qed

lemma green_quad_divisible_zero [simp]:
  "green_quad_divisible p d 0"
proof -
  have qi: "green_quadratic_integer d (0::complex)"
    using green_quadratic_integer_of_int[of d 0] by simp
  show ?thesis unfolding green_quad_divisible_def
    by (rule exI[of _ 0]) (use qi in simp)
qed

lemma green_quad_divisible_sum:
  assumes finite: "finite I"
    and each: "\<And>i. i \<in> I \<Longrightarrow> green_quad_divisible p d (f i)"
  shows "green_quad_divisible p d (\<Sum>i\<in>I. f i)"
  using finite each
  by (induction I rule: finite_induct)
    (auto intro: green_quad_divisible_add)

lemma green_quad_divisible_prime_binomial:
  assumes prime: "prime p"
    and x: "green_quadratic_integer d x"
    and y: "green_quadratic_integer d y"
  shows "green_quad_divisible p d ((x + y) ^ p - x ^ p - y ^ p)"
proof -
  let ?f = "\<lambda>k. of_nat (p choose k) * x ^ k * y ^ (p - k)"
  let ?I = "{..p} - {0,p}"
  have ppos: "0 < p" using prime_gt_1_nat[OF prime] by linarith
  have mid: "green_quad_divisible p d (\<Sum>k\<in>?I. ?f k)"
  proof (rule green_quad_divisible_sum)
    show "finite ?I" by simp
    fix k assume ki: "k \<in> ?I"
    have kpos: "k \<noteq> 0" and klt: "k < p"
      using ki by auto
    have choose: "p dvd (p choose k)"
      by (rule dvd_choose_prime[OF klt kpos _ prime]) (use ppos in simp)
    have coeff: "green_quad_divisible p d (of_nat (p choose k))"
      using green_quad_divisible_of_int[of p "int (p choose k)" d]
        choose by simp
    have xy: "green_quadratic_integer d (x ^ k * y ^ (p - k))"
      by (rule green_quadratic_integer_mult;
        rule green_quadratic_integer_power; fact x y)
    show "green_quad_divisible p d (?f k)"
      using green_quad_divisible_mult[OF xy coeff]
      by (simp add: mult_ac)
  qed
  have binomial: "(x + y) ^ p = (\<Sum>k\<le>p. ?f k)"
    by (rule binomial_ring)
  have split: "(\<Sum>k\<le>p. ?f k) =
      (\<Sum>k\<in>{0,p}. ?f k) + (\<Sum>k\<in>?I. ?f k)"
    using sum.subset_diff[of "{0,p}" "{..p}" ?f]
    by auto
  have ends: "(\<Sum>k\<in>{0,p}. ?f k) = x ^ p + y ^ p"
    using ppos by (simp add: insert_commute)
  have eq: "(x + y) ^ p - x ^ p - y ^ p =
      (\<Sum>k\<in>?I. ?f k)"
    using binomial split ends by (simp add: algebra_simps)
  show ?thesis using mid by (simp only: eq)
qed

lemma green_quad_divisible_nat_fermat:
  assumes prime: "prime p"
  shows "green_quad_divisible p d
    ((of_nat n::complex) ^ p - of_nat n)"
proof -
  have cong: "[n ^ p = n] (mod p)"
  proof (cases "p dvd n")
    case True
    have "p ^ 1 dvd n ^ p"
      by (rule dvd_power_le[OF True]) (use prime_gt_1_nat[OF prime] in simp)
    then show ?thesis using True
      by (simp add: cong_def dvd_eq_mod_eq_0)
  next
    case False
    have flt: "[n ^ (p - 1) = 1] (mod p)"
      by (rule fermat_theorem[OF prime False])
    have mult: "[n ^ (p - 1) * n = 1 * n] (mod p)"
      by (rule cong_mult[OF flt]) simp
    have pform: "p = (p - 1) + 1"
      using prime_gt_1_nat[OF prime] by linarith
    have pow: "n ^ p = n ^ (p - 1) * n"
      by (subst pform) (simp add: power_add)
    show ?thesis using mult by (simp only: pow; simp)
  qed
  have int_cong: "[int (n ^ p) = int n] (mod int p)"
    using cong by (simp only: cong_int_iff)
  have dvd: "int p dvd int (n ^ p) - int n"
    using int_cong by (simp add: cong_iff_dvd_diff)
  show ?thesis
    using green_quad_divisible_of_int[OF dvd]
    by simp
qed

lemma (in green_quadratic_character) green_inert_odd_prime_sqrt_frobenius:
  assumes prime: "prime p" and odd: "odd p" and inert: "chi p = -1"
  shows "green_quad_divisible p d
    (cpx_sqrt d ^ p + cpx_sqrt d)"
proof -
  let ?h = "(p - 1) div 2"
  have pform: "p = 2 * ?h + 1"
    using prime odd by presburger
  have sqrtpow: "cpx_sqrt d ^ p = of_int (d ^ ?h) * cpx_sqrt d"
  proof -
    have "cpx_sqrt d ^ p = (cpx_sqrt d ^ 2) ^ ?h * cpx_sqrt d"
      by (subst pform) (simp add: power_add power_mult)
    also have "... = of_int (d ^ ?h) * cpx_sqrt d"
      by (simp add: square_sqrt)
    finally show ?thesis .
  qed
  have euler: "[d ^ ?h = -1] (mod p)"
    by (rule inert_odd_prime_euler[OF prime odd inert])
  have dvd: "int p dvd d ^ ?h + 1"
    using euler by (simp add: cong_iff_dvd_diff)
  then obtain k :: int where k: "d ^ ?h + 1 = int p * k"
    by (auto simp: dvd_def)
  have coeff: "(of_int (d ^ ?h)::complex) + 1 = of_nat p * of_int k"
  proof -
    have "(of_int (d ^ ?h + 1)::complex) = of_int (int p * k)"
      by (simp only: k)
    then show ?thesis by simp
  qed
  have integer: "green_quadratic_integer d
      (of_int k * cpx_sqrt d)"
    by (rule green_quadratic_integer_mult; simp)
  have eq: "cpx_sqrt d ^ p + cpx_sqrt d =
      of_nat p * (of_int k * cpx_sqrt d)"
  proof -
    have "cpx_sqrt d ^ p + cpx_sqrt d =
        (of_int (d ^ ?h) + 1) * cpx_sqrt d"
      using sqrtpow by (simp add: algebra_simps)
    also have "... = of_nat p * (of_int k * cpx_sqrt d)"
      using coeff by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis
    using integer eq by (auto simp: green_quad_divisible_def)
qed

lemma (in green_quadratic_character) green_inert_odd_prime_slope_frobenius:
  assumes prime: "prime p" and odd: "odd p" and inert: "chi p = -1"
  shows "green_quad_divisible p d
    (((of_nat y::complex) * cpx_sqrt d) ^ p +
      of_nat y * cpx_sqrt d)"
proof -
  let ?y = "(of_nat y::complex)"
  let ?s = "cpx_sqrt d"
  have sqrt: "green_quad_divisible p d (?s ^ p + ?s)"
    by (rule green_inert_odd_prime_sqrt_frobenius[OF prime odd inert])
  have ypow: "green_quadratic_integer d (?y ^ p)"
    by (rule green_quadratic_integer_power) simp
  have first: "green_quad_divisible p d
      (?y ^ p * (?s ^ p + ?s))"
    by (rule green_quad_divisible_mult[OF ypow sqrt])
  have fy: "green_quad_divisible p d (?y ^ p - ?y)"
    by (rule green_quad_divisible_nat_fermat[OF prime])
  have second: "green_quad_divisible p d
      ((?y ^ p - ?y) * ?s)"
  proof -
    have "green_quad_divisible p d
        (?s * (?y ^ p - ?y))"
      by (rule green_quad_divisible_mult[OF
        green_quadratic_integer_sqrt fy])
    then show ?thesis by (simp add: mult.commute)
  qed
  have eq: "(?y * ?s) ^ p + ?y * ?s =
      ?y ^ p * (?s ^ p + ?s) - (?y ^ p - ?y) * ?s"
    by (simp add: algebra_simps)
  have "green_quad_divisible p d
      (?y ^ p * (?s ^ p + ?s) - (?y ^ p - ?y) * ?s)"
  proof -
    have neg: "green_quad_divisible p d
        (- ((?y ^ p - ?y) * ?s))"
      by (rule green_quad_divisible_minus[OF second])
    have "green_quad_divisible p d
        (?y ^ p * (?s ^ p + ?s) + - ((?y ^ p - ?y) * ?s))"
      by (rule green_quad_divisible_add[OF first neg])
    then show ?thesis by (simp only: diff_conv_add_uminus)
  qed
  then show ?thesis by (simp only: eq)
qed

lemma (in green_quadratic_character) green_inert_odd_prime_lattice_frobenius:
  assumes prime: "prime p" and odd: "odd p" and inert: "chi p = -1"
  shows "green_quad_divisible p d
    ((of_nat x + of_nat y * cpx_sqrt d) ^ p -
      (of_nat x - of_nat y * cpx_sqrt d))"
proof -
  let ?x = "(of_nat x::complex)"
  let ?y = "(of_nat y::complex)"
  let ?s = "cpx_sqrt d"
  have slope_integer: "green_quadratic_integer d (?y * ?s)"
    by (rule green_quadratic_integer_mult; simp)
  have binomial: "green_quad_divisible p d
      ((?x + ?y * ?s) ^ p - ?x ^ p - (?y * ?s) ^ p)"
    by (rule green_quad_divisible_prime_binomial[OF
      prime _ slope_integer]) simp
  have fx: "green_quad_divisible p d (?x ^ p - ?x)"
    by (rule green_quad_divisible_nat_fermat[OF prime])
  have fy: "green_quad_divisible p d
      ((?y * ?s) ^ p + ?y * ?s)"
    by (rule green_inert_odd_prime_slope_frobenius[OF prime odd inert])
  have eq: "(?x + ?y * ?s) ^ p - (?x - ?y * ?s) =
      ((?x + ?y * ?s) ^ p - ?x ^ p - (?y * ?s) ^ p) +
      (?x ^ p - ?x) + ((?y * ?s) ^ p + ?y * ?s)"
    by (simp add: algebra_simps)
  have sum1: "green_quad_divisible p d
      (((?x + ?y * ?s) ^ p - ?x ^ p - (?y * ?s) ^ p) +
      (?x ^ p - ?x))"
    by (rule green_quad_divisible_add[OF binomial fx])
  have "green_quad_divisible p d
      (((?x + ?y * ?s) ^ p - ?x ^ p - (?y * ?s) ^ p) +
      (?x ^ p - ?x) + ((?y * ?s) ^ p + ?y * ?s))"
    by (rule green_quad_divisible_add[OF sum1 fy])
  then show ?thesis by (simp only: eq)
qed

end
