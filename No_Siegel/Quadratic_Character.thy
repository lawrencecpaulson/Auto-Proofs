theory Quadratic_Character
  imports Finite_Grid "HOL-Number_Theory.Euler_Criterion"
    "Dirichlet_L.Dirichlet_Characters"
    "Continued_Fractions.Quadratic_Irrationals"
    "Diophantine_Universal_Pairs.Algebra_Basics"
    "HOL-Computational_Algebra.Squarefree"
begin

text \<open>Green, Sections 2, 3 and 5: the quadratic parameter of the
  lattice, the character's inert primes, and the Frobenius congruence.
  We keep the character and its discriminant in a locale so that subsequent
  theories can work in its context. The conductor and odd-prime character
  identities are hypotheses here; Character_Discriminant_Assembly proves
  that primitive real characters supply them.\<close>

definition fundamental_discriminant :: "int \<Rightarrow> bool" where
  "fundamental_discriminant d \<longleftrightarrow>
    (d mod 4 = 1 \<and> squarefree d) \<or>
    (d mod 4 = 0 \<and> squarefree (d div 4) \<and>
      (d div 4) mod 4 \<in> {2, 3})"

lemma fundamental_discriminant_nonsquare:
  assumes fundamental: "fundamental_discriminant d" and large: "1 < abs d"
  shows "\<not> (\<exists>m::int. d = m\<^sup>2)"
proof
  assume "\<exists>m::int. d = m\<^sup>2"
  then obtain m :: int where dm: "d = m\<^sup>2" by blast
  consider (odd) "d mod 4 = 1" "squarefree d"
    | (even) "d mod 4 = 0" "squarefree (d div 4)"
        "(d div 4) mod 4 \<in> {2, 3}"
    using fundamental by (auto simp: fundamental_discriminant_def)
  then show False
  proof cases
    case odd
    have "m dvd 1"
      by (rule squarefreeD[OF odd(2)]) (simp add: dm)
    then have "m = 1 \<or> m = -1"
      by (cases "m \<ge> 0") (auto simp: abs_if)
    then have "m\<^sup>2 = 1" by auto
    with dm large show False by simp
  next
    case even
    have "even m"
    proof (rule ccontr)
      assume "\<not> even m"
      then obtain t :: int where mt: "m = 2 * t + 1"
        by (auto elim: oddE)
      have square: "m\<^sup>2 = 4 * (t\<^sup>2 + t) + 1"
        unfolding mt by (simp add: power2_eq_square algebra_simps)
      have "m\<^sup>2 mod 4 = (4 * (t\<^sup>2 + t) + 1) mod 4"
        by (simp only: square)
      also have "... = 1" by presburger
      finally have "m\<^sup>2 mod 4 = 1" .
      with even(1) dm show False by simp
    qed
    then obtain k :: int where mk: "m = 2 * k"
      by (auto elim: evenE)
    have dk: "d div 4 = k\<^sup>2"
      using dm mk by (simp add: power2_eq_square algebra_simps)
    have "k dvd 1"
      by (rule squarefreeD[OF even(2)]) (simp add: dk)
    then have "k = 1 \<or> k = -1"
      by (cases "k \<ge> 0") (auto simp: abs_if)
    then have "k\<^sup>2 = 1" by auto
    with even(3) dk show False by simp
  qed
qed

lemma cpx_sqrt_nonsquare_irrational:
  fixes d :: int
  assumes nonsquare: "\<not> (\<exists>m::int. d = m\<^sup>2)"
  shows "cpx_sqrt d \<notin> Rats"
proof (cases "0 \<le> d")
  case True
  have nonsquare_nat: "\<not> is_square (nat d)"
  proof
    assume "is_square (nat d)"
    then obtain m :: nat where m: "nat d = m\<^sup>2"
      by (elim is_nth_powerE)
    have dnat: "d = int (nat d)" using True by simp
    have "d = (int m)\<^sup>2" using dnat m by simp
    then show False using nonsquare by blast
  qed
  have "sqrt (real (nat d)) \<notin> Rats"
    by (rule irrat_sqrt_nonsquare[OF nonsquare_nat])
  then show ?thesis
    using True by (simp add: cpx_sqrt_def)
next
  case False
  have "0 < -d" using False by simp
  then have im: "0 < Im (cpx_sqrt d)"
    using False by (simp add: cpx_sqrt_def)
  show ?thesis
  proof
    assume "cpx_sqrt d \<in> Rats"
    then obtain r :: rat where "cpx_sqrt d = of_rat r"
      by (elim Rats_cases)
    then have "Im (cpx_sqrt d) = 0"
      by (simp add: coercion_coherent[symmetric])
    with im show False by simp
  qed
qed

locale green_quadratic_character =
  fixes q :: nat and chi :: "nat \<Rightarrow> complex" and d :: int
  assumes character: "dcharacter q chi"
    and conductor_discriminant: "q = nat (abs d)"
    and fundamental: "fundamental_discriminant d"
    and odd_prime_character:
      "\<forall>p::nat. prime p \<and> odd p \<and> \<not> p dvd q \<longrightarrow>
        chi p = of_int (Legendre d (int p))"
begin

sublocale char: dcharacter q "residue_mult_group q" chi
  using character by (simp_all add: dcharacter_def)

lemma discriminant_abs: "abs d = int q"
  using conductor_discriminant by simp

lemma conductor_pos: "q > 1"
  by (fact char.n)

lemma discriminant_nonsquare: "\<not> (\<exists>m::int. d = m\<^sup>2)"
proof (rule fundamental_discriminant_nonsquare[OF fundamental])
  show "1 < abs d" using conductor_pos discriminant_abs by simp
qed

lemma prime_dvd_conductor_iff:
  "p dvd q \<longleftrightarrow> int p dvd d"
  by (simp add: conductor_discriminant)

lemma lattice_slope_norm:
  "norm (cpx_sqrt d) = sqrt (real q)"
  using norm_cpx_sqrt[of d] discriminant_abs
  by simp

lemma lattice_slope_irrational: "cpx_sqrt d \<notin> Rats"
  by (rule cpx_sqrt_nonsquare_irrational[OF discriminant_nonsquare])

lemma lattice_slope_nonzero: "cpx_sqrt d \<noteq> 0"
  using lattice_slope_irrational by auto

lemma lattice_second_distinct:
  "inj_on snd (diagonal_grid (cpx_sqrt d) (natural_grid N))"
  by (rule natural_diagonal_grid_second_distinct[OF lattice_slope_irrational])

lemma lattice_zero_bound:
  fixes P :: "complex mpoly"
  assumes "0 < N" "N \<le> J" "P \<noteq> 0" "vars P \<subseteq> {0,1}"
  shows "card {z \<in> diagonal_grid (cpx_sqrt d) (natural_grid N).
      pair_eval P z = 0} \<le> J * total_degree P"
  by (rule natural_diagonal_grid_bound[OF assms(1,2) lattice_slope_nonzero
    assms(3,4)])

lemma prime_character_zero_iff:
  assumes "prime p"
  shows "chi p = 0 \<longleftrightarrow> p dvd q"
proof -
  have "(\<not>coprime p q) \<longleftrightarrow> p dvd q"
  proof
    assume "\<not>coprime p q"
    then show "p dvd q"
      using assms by (meson prime_imp_coprime)
  next
    assume "p dvd q"
    then show "\<not>coprime p q"
      using prime_gt_1_nat[OF assms]
      by (simp add: coprime_iff_gcd_eq_1)
  qed
  then show ?thesis by (simp add: char.eq_zero_iff)
qed

lemma ramified_prime_zero:
  assumes "prime p" "p dvd q"
  shows "chi p = 0"
  using prime_character_zero_iff[OF assms(1)] assms(2) by simp

lemma ramified_prime_legendre:
  assumes "prime p" "p dvd q"
  shows "Legendre d (int p) = 0"
  using prime_dvd_conductor_iff[of p] assms
  by (simp add: Legendre_def cong_iff_dvd_diff)

lemma odd_prime_character_value:
  assumes "prime p" "odd p"
  shows "chi p = of_int (Legendre d (int p))"
proof (cases "p dvd q")
  case True
  then show ?thesis
    using ramified_prime_zero[OF assms(1)] ramified_prime_legendre[OF assms(1)]
    by simp
next
  case False
  then show ?thesis using odd_prime_character assms by auto
qed

lemma inert_prime_unramified:
  assumes "prime p" "chi p = -1"
  shows "\<not> p dvd q"
  using ramified_prime_zero[OF assms(1)] assms(2) by auto

lemma inert_prime_does_not_divide_discriminant:
  assumes "prime p" "chi p = -1"
  shows "\<not> int p dvd d"
  using inert_prime_unramified[OF assms] prime_dvd_conductor_iff[of p]
  by simp

lemma inert_odd_prime_iff:
  assumes "prime p" "odd p"
  shows "chi p = -1 \<longleftrightarrow> Legendre d (int p) = -1"
  using odd_prime_character_value[OF assms]
  by (metis of_int_eq_iff of_int_minus of_int_1)

lemma inert_odd_prime_legendre:
  assumes "prime p" "odd p" "chi p = -1"
  shows "Legendre d (int p) = -1"
  using inert_odd_prime_iff[OF assms(1,2)] assms(3) by simp

lemma inert_odd_prime_euler:
  assumes "prime p" "odd p" "chi p = -1"
  shows "[d ^ ((p - 1) div 2) = -1] (mod p)"
proof -
  have pneq2: "p \<noteq> 2"
  proof
    assume "p = 2"
    then show False using assms(2) by simp
  qed
  have p2: "2 < p"
    using prime_gt_1_nat[OF assms(1)] pneq2 by arith
  have "[Legendre d (int p) = d ^ ((p - 1) div 2)] (mod p)"
    by (rule euler_criterion[OF assms(1) p2])
  then show ?thesis
    using inert_odd_prime_legendre[OF assms]
    by (simp add: cong_sym)
qed

end

end
