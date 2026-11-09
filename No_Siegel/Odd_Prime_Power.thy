theory Odd_Prime_Power
  imports Quadratic_Classification
    "HOL-Number_Theory.Residue_Primitive_Roots"
begin

text \<open>Green, Section 2: local structure of primitive real characters
  at odd prime-power moduli.\<close>

lemma odd_prime_power_square_lift:
  fixes p k a :: nat
  assumes prime: "prime p" and odd: "odd p" and kpos: "0 < k"
    and cp: "coprime a (p ^ k)" and a_one: "[a = 1] (mod p)"
  obtains y where "[y ^ 2 = a] (mod p ^ k)"
proof -
  obtain g where g: "\<forall>j>0. residue_primroot (p ^ j) g"
    using residue_primroot_odd_prime_power_exists[OF prime odd] by blast
  have gp: "residue_primroot p g"
    using g[rule_format, of 1] by simp
  have gm: "residue_primroot (p ^ k) g"
    using g kpos by blast
  have m_gt: "1 < p ^ k"
    using prime kpos by (metis one_less_power prime_gt_1_nat)
  have not_dvd: "\<not> p ^ k dvd a"
  proof
    assume dvd: "p ^ k dvd a"
    then have "is_unit (p ^ k)"
      using cp coprime_absorb_right[OF dvd] by blast
    with kpos prime show False by auto
  qed
  have mod_pos: "0 < a mod (p ^ k)"
    using not_dvd by (simp add: mod_greater_zero_iff_not_dvd)
  have m_pos: "0 < p ^ k"
    using prime by (simp add: prime_gt_0_nat)
  have m_ne: "p ^ k \<noteq> 0" using m_pos by simp
  have mod_less: "a mod (p ^ k) < p ^ k"
    by (rule mod_less_divisor[OF m_pos])
  have mod_cp: "coprime (a mod (p ^ k)) (p ^ k)"
    using cp coprime_mod_left_iff[where a=a and b="p ^ k", OF m_ne]
    by blast
  have a_tot: "a mod (p ^ k) \<in> totatives (p ^ k)"
    using mod_pos mod_less mod_cp
    by (simp add: in_totatives_iff)
  have "a mod (p ^ k) \<in> (\<lambda>i. g ^ i mod (p ^ k)) ` {..<totient (p ^ k)}"
    using a_tot residue_primroot_is_generator[OF m_gt gm]
    by (auto simp: bij_betw_def)
  then obtain i where gi: "g ^ i mod (p ^ k) = a mod (p ^ k)"
    by auto
  have pdiv: "p dvd p ^ k" using kpos by simp
  have gip: "g ^ i mod p = a mod p"
    using gi pdiv by (metis mod_mod_cancel)
  have g_one: "[g ^ i = 1] (mod p)"
    using gip a_one by (simp add: cong_def)
  have ordp: "ord p g = p - 1"
    using gp prime by (simp add: residue_primroot_def totient_prime)
  have ord_dvd: "ord p g dvd i"
    by (rule iffD1[OF ord_divides[of g i p] g_one])
  have pi: "p - 1 dvd i"
    using ord_dvd ordp by simp
  have even_p1: "even (p - 1)"
    using odd by (auto elim: oddE)
  have even_i: "even i"
    using dvd_trans[of 2 "p - 1" i] even_p1 pi by simp
  then obtain j where i: "i = 2 * j"
    by (auto elim: evenE)
  have pow_eq: "(g ^ j) ^ 2 = g ^ i"
    by (simp add: i power_mult mult.commute)
  have "[(g ^ j) ^ 2 = a] (mod p ^ k)"
    using gi pow_eq by (simp add: cong_def)
  then show thesis by (rule that)
qed

context green_primitive_real_dcharacter
begin

lemma odd_prime_power_induced_modulus:
  assumes modulus: "n = p ^ k"
    and prime: "prime p" and odd: "odd p" and kpos: "0 < k"
  shows "induced_modulus p"
proof (rule induced_modulus_of_square_lifts)
  show "p dvd n" using modulus kpos by simp
  fix a
  assume cp: "coprime a n" and a_one: "[a = 1] (mod p)"
  obtain y where square: "[y ^ 2 = a] (mod p ^ k)"
    using odd_prime_power_square_lift[OF prime odd kpos]
      cp a_one modulus by blast
  show "\<exists>y. [y ^ 2 = a] (mod n)"
    using square modulus by blast
qed

lemma odd_prime_power_exponent_one:
  assumes modulus: "n = p ^ k"
    and prime: "prime p" and odd: "odd p" and kpos: "0 < k"
  shows "k = 1"
proof (rule ccontr)
  assume "k \<noteq> 1"
  then have k_gt: "1 < k" using kpos by simp
  have p_gt: "1 < p" by (rule prime_gt_1_nat[OF prime])
  have "p ^ 1 < p ^ k"
    by (rule power_strict_increasing[OF k_gt p_gt])
  then have "p < n" using modulus by simp
  moreover have "induced_modulus p"
    by (rule odd_prime_power_induced_modulus[OF modulus prime odd kpos])
  ultimately show False using no_induced_modulus by blast
qed

end

end
