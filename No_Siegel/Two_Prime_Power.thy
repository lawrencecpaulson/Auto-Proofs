theory Two_Prime_Power
  imports Odd_Prime_Power
begin

text \<open>Green, Section 2: local structure of primitive real characters
  at powers of two.\<close>

lemma eight_dvd_twopow:
  assumes "3 \<le> k"
  shows "8 dvd (2::nat) ^ k"
  using le_imp_power_dvd[OF assms, of "2::nat"] by simp

definition one_mod_eight_units :: "nat \<Rightarrow> nat set" where
  "one_mod_eight_units k = {a. a < 2 ^ k \<and> a mod 8 = 1}"

lemma one_mod_eight_units_image:
  assumes k: "3 \<le> k"
  shows "one_mod_eight_units k =
    (\<lambda>j. 8 * j + 1) ` {..<2 ^ (k - 3)}"
proof -
  have keq: "k = 3 + (k - 3)" using k by arith
  have m: "(2::nat) ^ k = 8 * 2 ^ (k - 3)"
    by (subst keq) (simp add: power_add)
  show ?thesis
  proof (rule subset_antisym)
    show "one_mod_eight_units k \<subseteq>
      (\<lambda>j. 8 * j + 1) ` {..<2 ^ (k - 3)}"
    proof
      fix a :: nat
      assume a: "a \<in> one_mod_eight_units k"
      have ae: "a = 8 * (a div 8) + 1"
        using a div_mult_mod_eq[of a 8]
        by (simp add: one_mod_eight_units_def mult.commute)
      have jlt: "a div 8 < 2 ^ (k - 3)"
        using a ae by (auto simp: one_mod_eight_units_def m)
      show "a \<in> (\<lambda>j. 8 * j + 1) ` {..<2 ^ (k - 3)}"
        using ae jlt by blast
    qed
    show "(\<lambda>j. 8 * j + 1) ` {..<2 ^ (k - 3)}
      \<subseteq> one_mod_eight_units k"
    proof
      fix a :: nat
      assume a: "a \<in> (\<lambda>j. 8 * j + 1) ` {..<2 ^ (k - 3)}"
      then obtain j where j: "j < 2 ^ (k - 3)" "a = 8 * j + 1"
        by auto
      show "a \<in> one_mod_eight_units k"
        using j by (auto simp: one_mod_eight_units_def m)
    qed
  qed
qed

lemma card_one_mod_eight_units:
  assumes k: "3 \<le> k"
  shows "card (one_mod_eight_units k) = 2 ^ (k - 3)"
  unfolding one_mod_eight_units_image[OF k]
  by (subst card_image) (auto simp: inj_on_def)

lemma ord_twopow_25:
  assumes k: "3 \<le> k"
  shows "ord (2 ^ k) (25::nat) = 2 ^ (k - 3)"
proof -
  have cp: "coprime (2 ^ k) (5::nat)" by simp
  have ord5: "ord (2 ^ k) (5::nat) = 2 ^ (k - 2)"
    using ord_twopow_3_5[OF k, of 5] by simp
  have two: "gcd (2::nat) (2 ^ (k - 2)) = 2"
    using k by (simp add: gcd.commute)
  have km: "k - 2 = Suc (k - 3)" using k by arith
  have "ord (2 ^ k) (25::nat) =
      ord (2 ^ k) (5::nat) div gcd 2 (ord (2 ^ k) (5::nat))"
    using ord_power[OF cp, of 2] by simp
  also have "\<dots> = 2 ^ (k - 3)"
    by (simp add: ord5 two km)
  finally show ?thesis .
qed

lemma powers_25_fill_one_mod_eight:
  assumes k: "3 \<le> k"
  shows "(\<lambda>j. (25::nat) ^ j mod 2 ^ k) ` {..<2 ^ (k - 3)}
    = one_mod_eight_units k"
proof (rule card_subset_eq)
  have cp: "coprime (2 ^ k) (25::nat)" by simp
  have inj: "inj_on (\<lambda>j. (25::nat) ^ j mod 2 ^ k) {..<2 ^ (k - 3)}"
    using inj_power_mod[OF cp] ord_twopow_25[OF k] by simp
  show "card ((\<lambda>j. (25::nat) ^ j mod 2 ^ k) ` {..<2 ^ (k - 3)})
    = card (one_mod_eight_units k)"
    using card_one_mod_eight_units[OF k]
    by (simp add: card_image[OF inj])
  have eight_div: "8 dvd (2::nat) ^ k"
    by (rule eight_dvd_twopow[OF k])
  have modulus_pos: "0 < (2::nat) ^ k" by simp
  show "(\<lambda>j. (25::nat) ^ j mod 2 ^ k) ` {..<2 ^ (k - 3)}
    \<subseteq> one_mod_eight_units k"
  proof
    fix a :: nat
    assume "a \<in> (\<lambda>j. (25::nat) ^ j mod 2 ^ k) ` {..<2 ^ (k - 3)}"
    then obtain j where a: "a = 25 ^ j mod 2 ^ k" by auto
    have less: "a < 2 ^ k" using a modulus_pos by simp
    have pow8: "(25::nat) ^ j mod 8 = 1"
      by (subst power_mod[symmetric]) simp
    have mod8: "a mod 8 = 1"
      using a eight_div pow8 by (simp add: mod_mod_cancel)
    show "a \<in> one_mod_eight_units k"
      using less mod8
      by (simp add: one_mod_eight_units_def)
  qed
qed (simp add: one_mod_eight_units_def)

lemma two_prime_power_square_lift:
  fixes k a :: nat
  assumes k: "3 \<le> k" and a_one: "[a = 1] (mod 8)"
  obtains y where "[y ^ 2 = a] (mod 2 ^ k)"
proof -
  have eight_div: "8 dvd (2::nat) ^ k"
    by (rule eight_dvd_twopow[OF k])
  have a8: "a mod 8 = 1" using a_one by (simp add: cong_def)
  have r8: "(a mod 2 ^ k) mod 8 = 1"
    using a8 eight_div by (simp add: mod_mod_cancel)
  have rmem: "a mod 2 ^ k \<in> one_mod_eight_units k"
    using r8 by (simp add: one_mod_eight_units_def)
  have "a mod 2 ^ k \<in>
    (\<lambda>j. (25::nat) ^ j mod 2 ^ k) ` {..<2 ^ (k - 3)}"
    using rmem powers_25_fill_one_mod_eight[OF k] by simp
  then obtain j where rep: "a mod 2 ^ k = 25 ^ j mod 2 ^ k"
    by auto
  have pow_eq: "((5::nat) ^ j) ^ 2 = 25 ^ j"
  proof -
    have "25 ^ j = ((5::nat) * 5) ^ j" by simp
    also have "\<dots> = (5 ^ j) * (5 ^ j)"
      by (rule power_mult_distrib)
    also have "\<dots> = (5 ^ j) ^ 2"
      by (simp add: power2_eq_square)
    finally show ?thesis by simp
  qed
  have "[(5 ^ j) ^ 2 = a] (mod 2 ^ k)"
    using rep pow_eq by (simp add: cong_def)
  then show thesis by (rule that)
qed

context green_primitive_real_dcharacter
begin

lemma two_prime_power_induced_modulus:
  assumes modulus: "n = 2 ^ k" and k: "3 \<le> k"
  shows "induced_modulus 8"
proof (rule induced_modulus_of_square_lifts)
  have "8 dvd (2::nat) ^ k"
    by (rule eight_dvd_twopow[OF k])
  then show "8 dvd n" using modulus by simp
  fix a
  assume cp: "coprime a n" and a_one: "[a = 1] (mod 8)"
  obtain y where square: "[y ^ 2 = a] (mod 2 ^ k)"
    by (rule two_prime_power_square_lift[OF k a_one])
  show "\<exists>y. [y ^ 2 = a] (mod n)"
    using square modulus by blast
qed

lemma two_prime_power_exponent_le_three:
  assumes modulus: "n = 2 ^ k"
  shows "k \<le> 3"
proof (rule ccontr)
  assume "\<not> k \<le> 3"
  then have kgt: "3 < k" by simp
  then have k: "3 \<le> k" by simp
  have "2 ^ 3 < (2::nat) ^ k"
    by (rule power_strict_increasing[OF kgt]) simp
  then have "8 < n" using modulus by simp
  moreover have "induced_modulus 8"
    by (rule two_prime_power_induced_modulus[OF modulus k])
  ultimately show False using no_induced_modulus by blast
qed

lemma modulus_not_two: "n \<noteq> 2"
proof
  assume n2: "n = 2"
  have "\<chi> a = principal_dchar n a" for a
  proof (cases "coprime a n")
    case True
    have square: "[1 ^ 2 = a] (mod n)"
      using True n2 by (simp add: cong_def mod_2_eq_odd)
    have "\<chi> a = 1"
      by (rule square_residue_value_one[OF True square])
    then show ?thesis using True
      by (simp add: principal_dchar_def)
  next
    case False
    then show ?thesis
      by (simp add: principal_dchar_def eq_zero)
  qed
  then have "\<chi> = principal_dchar n"
    by (simp add: fun_eq_iff)
  with nonprincipal show False by contradiction
qed

lemma two_prime_power_exponent_two_or_three:
  assumes modulus: "n = 2 ^ k" and kpos: "0 < k"
  shows "k = 2 \<or> k = 3"
proof -
  have "k \<le> 3"
    by (rule two_prime_power_exponent_le_three[OF modulus])
  moreover have "k \<noteq> 1"
    using modulus modulus_not_two by auto
  ultimately show ?thesis using kpos by arith
qed

end

end
