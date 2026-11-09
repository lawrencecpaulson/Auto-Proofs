theory Prime_Power_Values
  imports Two_Prime_Power
begin

text \<open>Green, Section 2: values of primitive real characters at
  the surviving two-power conductors.\<close>

context green_primitive_real_dcharacter
begin

lemma modulus_four_value_three:
  assumes n4: "n = 4"
  shows "\<chi> 3 = -1"
proof -
  obtain a where cp: "coprime a n" and neg: "\<chi> a = -1"
    using negative_value_exists by blast
  have odda: "odd a"
  proof (rule ccontr)
    assume "\<not> odd a"
    then have "2 dvd a" by simp
    moreover have "2 dvd n" using n4 by simp
    ultimately have "is_unit (2::nat)"
      by (rule coprime_common_divisor[OF cp])
    then show False by simp
  qed
  have mod2: "(a mod 4) mod 2 = 1"
  proof -
    have "(a mod 4) mod 2 = a mod 2"
      using mod_mod_cancel[of 2 4 a] by simp
    moreover have "a mod 2 = 1"
      using odda by (simp add: mod_2_eq_odd)
    ultimately show ?thesis by simp
  qed
  have mod4: "a mod 4 = 1 \<or> a mod 4 = 3"
  proof -
    have less: "a mod 4 < 4" by simp
    have "a mod 4 = 0 \<or> a mod 4 = 1 \<or>
      a mod 4 = 2 \<or> a mod 4 = 3"
      using less by arith
    with mod2 show ?thesis by auto
  qed
  have eq: "\<chi> a = \<chi> (a mod 4)"
    by (rule cong) (simp add: n4 cong_def)
  have "a mod 4 \<noteq> 1"
    using neg eq by auto
  then have "a mod 4 = 3" using mod4 by blast
  then show ?thesis using neg eq by simp
qed

lemma modulus_eight_value_five:
  assumes n8: "n = 8"
  shows "\<chi> 5 = -1"
proof (rule ccontr)
  assume not_minus: "\<chi> 5 \<noteq> -1"
  have cp5: "coprime 5 n"
    by (simp only: n8; eval)
  have nonzero: "\<chi> 5 \<noteq> 0"
    using cp5 by (simp add: eq_zero_iff)
  have value5: "\<chi> 5 = 1"
    using char_cases[of 5] nonzero not_minus by auto
  have induced4: "induced_modulus 4"
  proof (rule induced_modulusI)
    show "4 dvd n" using n8 by simp
    fix a
    assume cp: "coprime a n" and one: "[a = 1] (mod 4)"
    have a4: "a mod 4 = 1" using one by (simp add: cong_def)
    have a8_4: "(a mod 8) mod 4 = 1"
      using a4 mod_mod_cancel[of 4 8 a] by simp
    have a8: "a mod 8 = 1 \<or> a mod 8 = 5"
    proof -
      have less: "a mod 8 < 8" by simp
      have "a mod 8 = 0 \<or> a mod 8 = 1 \<or>
        a mod 8 = 2 \<or> a mod 8 = 3 \<or>
        a mod 8 = 4 \<or> a mod 8 = 5 \<or>
        a mod 8 = 6 \<or> a mod 8 = 7"
        using less by arith
      with a8_4 show ?thesis by auto
    qed
    have eq: "\<chi> a = \<chi> (a mod 8)"
      by (rule cong) (simp add: n8 cong_def)
    show "\<chi> a = 1"
      using eq a8 value5 by auto
  qed
  have "4 < n" using n8 by simp
  with induced4 no_induced_modulus show False by blast
qed

lemma modulus_eight_value_seven:
  assumes n8: "n = 8"
  shows "\<chi> 7 = - \<chi> 3"
proof -
  have eq: "\<chi> (3 * 5) = \<chi> 7"
    by (rule cong) (simp add: n8 cong_def)
  have chi_mult: "\<chi> (3 * 5) = \<chi> 3 * \<chi> 5"
    by (rule mult)
  have "\<chi> (3 * 5) = - \<chi> 3"
    using chi_mult modulus_eight_value_five[OF n8] by simp
  with eq show ?thesis by simp
qed

lemma modulus_eight_value_three_cases:
  assumes n8: "n = 8"
  shows "\<chi> 3 \<in> {-1, 1}"
proof -
  have cp3: "coprime 3 n"
    by (simp only: n8; eval)
  then have "\<chi> 3 \<noteq> 0"
    by (simp add: eq_zero_iff)
  with char_cases[of 3] show ?thesis by auto
qed

end

end
