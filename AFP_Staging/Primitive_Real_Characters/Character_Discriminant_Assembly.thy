theory Character_Discriminant_Assembly
  imports Quadratic_Local_Identification
begin

unbundle no vec_lambda_syntax

context primitive_real_dcharacter
begin

lemma odd_modulus_quadratic_character:
  assumes odd: "odd n"
  shows "quadratic_real_character_data n \<chi> (odd_discriminant_core n)"
proof (unfold_locales)
  show "n = nat (abs (odd_discriminant_core n))"
    by (simp add: odd_discriminant_core_def)
  show "fundamental_discriminant (odd_discriminant_core n)"
    by (rule odd_discriminant_core_fundamental[OF odd odd_modulus_squarefree[OF odd]])
  show "\<forall>p::nat. prime p \<and> odd p \<and> \<not> p dvd n \<longrightarrow>
    \<chi> p = of_int (Legendre (odd_discriminant_core n) (int p))"
  proof (intro allI impI)
    fix p :: nat
    assume p: "prime p \<and> odd p \<and> \<not> p dvd n"
    have source_real: "real_dcharacter n \<chi>"
      using dcharacter_axioms real_dcharacter_axioms
      unfolding real_dcharacter_def by blast
    have source_primitive: "primitive_dchar n \<chi>"
      using dcharacter_axioms primitive_dchar_axioms
      unfolding primitive_dchar_def by blast
    have source: "primitive_real_dcharacter n \<chi>"
      using source_real source_primitive
      unfolding primitive_real_dcharacter_def by blast
    have val: "\<chi> p = of_int (Jacobi (int p) (int n))"
      by (rule odd_squarefree_real_character_jacobi[OF source odd odd_modulus_squarefree[OF odd]])
    have swap: "Jacobi (int p) (int n) =
      Jacobi (odd_discriminant_core n) (int p)"
      by (rule odd_discriminant_core_reciprocity[OF p[THEN conjunct1]
        p[THEN conjunct2, THEN conjunct1] odd])
        (use n p in auto)
    have iprime: "prime (int p)"
      using p by (simp add: prime_int_nat_transfer)
    show "\<chi> p = of_int (Legendre (odd_discriminant_core n) (int p))"
      using val swap prime_p_Jacobi_eq_Legendre[OF iprime, of "odd_discriminant_core n"]
      by simp
  qed
qed

end


context primitive_real_dcharacter
begin

lemma odd_part_squarefree:
  assumes nr: "n = 2 ^ k * m" and modd: "odd m"
  shows "squarefree m"
proof (subst squarefree_factorial_semiring)
  show "m \<noteq> 0" using modd by presburger
  show "\<forall>p. prime p \<longrightarrow> \<not> p ^ 2 dvd m"
  proof (intro allI impI notI)
    fix p :: nat
    assume prime: "prime p" and p2m: "p ^ 2 dvd m"
    have pdivm: "p dvd m" using p2m by auto
    have pneq2: "p \<noteq> 2" using pdivm modd by auto
    have pgt2: "2 < p" using prime_gt_1_nat[OF prime] pneq2 by arith
    have podd: "odd p" by (rule prime_odd_nat[OF prime pgt2])
    have mdivn: "m dvd n" using nr by simp
    have p2n: "p ^ 2 dvd n" using p2m mdivn by (rule dvd_trans)
    have pdivn: "p dvd n" using pdivm mdivn by (rule dvd_trans)
    have exp: "multiplicity p n = 1"
      by (rule odd_prime_divisor_exponent_one[OF prime podd pdivn])
    have nnonzero: "n \<noteq> 0" using n by simp
    have pnotunit: "\<not> is_unit p" using prime_gt_1_nat[OF prime] by simp
    have "2 \<le> multiplicity p n"
      by (rule multiplicity_geI[OF nnonzero pnotunit p2n])
    with exp show False by simp
  qed
qed

lemma four_part_prime_factor:
  assumes nr: "n = 4 * m" and modd: "odd m" and msf: "squarefree m"
    and prime: "prime p" and podd: "odd p"
  shows "\<chi> p = of_int (Jacobi (-1) (int p) * Jacobi (int p) (int m))"
proof (cases "m = 1")
  case True
  have val: "\<chi> p = of_int (Jacobi (-1) (int p))"
    by (rule modulus_four_odd_prime_jacobi[OF _ prime podd])
      (use nr True in simp)
  show ?thesis using val True by simp
next
  case False
  then have mgt: "1 < m" using modd by presburger
  have cp: "coprime 4 m"
  proof -
    have "coprime (2 ^ 2) m" using modd
      by (simp only: coprime_power_left_iff coprime_left_2_iff_odd; simp)
    then show ?thesis by simp
  qed
  obtain psi theta where psi: "primitive_real_dcharacter 4 psi"
    and theta: "primitive_real_dcharacter m theta"
    and factor: "\<And>a. \<chi> a = psi a * theta a"
    by (rule crt_green_factors[OF nr cp _ mgt]) (simp, blast)
  interpret L: primitive_real_dcharacter 4 "residue_mult_group 4" psi
    by (rule psi)
  have left: "psi p = of_int (Jacobi (-1) (int p))"
    by (rule L.modulus_four_odd_prime_jacobi[OF refl prime podd])
  have right: "theta p = of_int (Jacobi (int p) (int m))"
    by (rule odd_squarefree_real_character_jacobi[OF theta modd msf])
  show ?thesis using factor[of p] left right by simp
qed


lemma eight_part_prime_factor:
  assumes nr: "n = 8 * m" and modd: "odd m" and msf: "squarefree m"
  obtains c :: int where "c \<in> {2, -2}"
    "\<And>p. prime p \<Longrightarrow> odd p \<Longrightarrow>
      \<chi> p = of_int (Jacobi c (int p) * Jacobi (int p) (int m))"
proof (cases "m = 1")
  case True
  let ?c = "(if \<chi> 3 = -1 then 2 else -2)::int"
  show thesis
  proof (rule that[of ?c])
    show "?c \<in> {2, -2}" by simp
    fix p :: nat
    assume prime: "prime p" and podd: "odd p"
    have val: "\<chi> p =
      (if \<chi> 3 = -1 then of_int (Jacobi 2 (int p))
       else of_int (Jacobi (-2) (int p)))"
      by (rule modulus_eight_odd_prime_jacobi[OF _ prime podd])
        (use nr True in simp)
    show "\<chi> p = of_int (Jacobi ?c (int p) * Jacobi (int p) (int m))"
      using val True by simp
  qed
next
  case False
  then have mgt: "1 < m" using modd by presburger
  have cp: "coprime 8 m"
  proof -
    have "coprime (2 ^ 3) m" using modd
      by (simp only: coprime_power_left_iff coprime_left_2_iff_odd; simp)
    then show ?thesis by simp
  qed
  obtain psi theta where psi: "primitive_real_dcharacter 8 psi"
    and theta: "primitive_real_dcharacter m theta"
    and factor: "\<And>a. \<chi> a = psi a * theta a"
    by (rule crt_green_factors[OF nr cp _ mgt]) (simp, blast)
  interpret L: primitive_real_dcharacter 8 "residue_mult_group 8" psi
    by (rule psi)
  let ?c = "(if psi 3 = -1 then 2 else -2)::int"
  show thesis
  proof (rule that[of ?c])
    show "?c \<in> {2, -2}" by simp
    fix p :: nat
    assume prime: "prime p" and podd: "odd p"
    have left: "psi p = of_int (Jacobi ?c (int p))"
      using L.modulus_eight_odd_prime_jacobi[OF refl prime podd] by simp
    have right: "theta p = of_int (Jacobi (int p) (int m))"
      by (rule odd_squarefree_real_character_jacobi[OF theta modd msf])
    show "\<chi> p = of_int (Jacobi ?c (int p) * Jacobi (int p) (int m))"
      using factor[of p] left right by simp
  qed
qed

end


lemma even_discriminant_core_fundamental:
  assumes modd: "odd m" and msf: "squarefree m"
    and c: "c \<in> {(-1::int), 2, -2}"
  shows "fundamental_discriminant (4 * c * odd_discriminant_core m)"
proof -
  let ?u = "odd_discriminant_core m"
  have uodd: "odd ?u" using modd by (simp add: odd_discriminant_core_def)
  have ufund: "fundamental_discriminant ?u"
    by (rule odd_discriminant_core_fundamental[OF modd msf])
  have umod: "?u mod 4 = 1" and usf: "squarefree ?u"
    using ufund uodd by (auto simp: fundamental_discriminant_def)
  have cp: "coprime (2::int) ?u" using uodd by simp
  have sf2: "squarefree ((2::int) * ?u)"
    by (rule squarefree_mult_coprime[OF cp squarefree_prime[of "2::int"] usf]) simp
  have csf: "squarefree (c * ?u)"
    using c usf sf2 by auto
  have cmod: "(c * ?u) mod 4 \<in> {2, 3}"
    using c umod by (auto; presburger)
  show ?thesis
    using csf cmod
    by (simp add: fundamental_discriminant_def algebra_simps)
qed

lemma even_discriminant_core_abs:
  assumes c: "c \<in> {(-1::int), 2, -2}"
  shows "nat (abs (4 * c * odd_discriminant_core m)) = 4 * nat (abs c) * m"
  using c by (auto simp: odd_discriminant_core_def abs_mult)

lemma odd_prime_legendre_four_mul:
  fixes x :: int
  assumes prime: "prime p" and podd: "odd p"
  shows "Legendre (4 * x) (int p) = Legendre x (int p)"
proof -
  have iprime: "prime (int p)"
    using prime by (simp add: prime_int_nat_transfer)
  have cp: "coprime (2::int) (int p)" using podd by simp
  have nz: "Legendre 2 (int p) \<noteq> 0" using cp iprime by simp
  have vals: "Legendre 2 (int p) \<in> {1, -1, 0}"
    by (rule Legendre_values)
  have l4: "Legendre 4 (int p) = 1"
  proof -
    have "Legendre 4 (int p) = Legendre (2 * 2) (int p)" by simp
    also have "... = Legendre 2 (int p) * Legendre 2 (int p)"
      by (rule Legendre_mult[OF iprime])
    also have "... = 1" using vals nz by auto
    finally show ?thesis .
  qed
  have "Legendre (4 * x) (int p) = Legendre 4 (int p) * Legendre x (int p)"
    by (rule Legendre_mult[OF iprime])
  then show ?thesis using l4 by simp
qed

lemma odd_prime_even_discriminant_value:
  assumes prime: "prime p" and podd: "odd p"
  shows "Jacobi c (int p) * Jacobi (odd_discriminant_core m) (int p) =
    Legendre (4 * c * odd_discriminant_core m) (int p)"
proof -
  have iprime: "prime (int p)"
    using prime by (simp add: prime_int_nat_transfer)
  have "Jacobi c (int p) * Jacobi (odd_discriminant_core m) (int p) =
    Jacobi (c * odd_discriminant_core m) (int p)" by simp
  also have "... = Legendre (c * odd_discriminant_core m) (int p)"
    by (rule prime_p_Jacobi_eq_Legendre[OF iprime])
  also have "... = Legendre (4 * (c * odd_discriminant_core m)) (int p)"
    using odd_prime_legendre_four_mul[OF prime podd] by simp
  finally show ?thesis by (simp add: algebra_simps)
qed


context primitive_real_dcharacter
begin

lemma assemble_even_quadratic_character:
  assumes nr: "n = 4 * nat (abs c) * m"
    and modd: "odd m" and msf: "squarefree m"
    and c: "c \<in> {(-1::int), 2, -2}"
    and local_values: "\<And>p. prime p \<Longrightarrow> odd p \<Longrightarrow>
      \<chi> p = of_int (Jacobi c (int p) * Jacobi (int p) (int m))"
  shows "quadratic_real_character_data n \<chi> (4 * c * odd_discriminant_core m)"
proof (unfold_locales)
  show "n = nat (abs (4 * c * odd_discriminant_core m))"
    using nr even_discriminant_core_abs[OF c, of m] by simp
  show "fundamental_discriminant (4 * c * odd_discriminant_core m)"
    by (rule even_discriminant_core_fundamental[OF modd msf c])
  show "\<forall>p::nat. prime p \<and> odd p \<and> \<not> p dvd n \<longrightarrow>
    \<chi> p = of_int (Legendre (4 * c * odd_discriminant_core m) (int p))"
  proof (intro allI impI)
    fix p :: nat
    assume p: "prime p \<and> odd p \<and> \<not> p dvd n"
    have mpos: "0 < m" using modd by presburger
    have mdivn: "m dvd n" using nr by simp
    have pm: "\<not> p dvd m" using p mdivn by (meson dvd_trans)
    have swap: "Jacobi (int p) (int m) =
      Jacobi (odd_discriminant_core m) (int p)"
      by (rule odd_discriminant_core_reciprocity[OF p[THEN conjunct1]
        p[THEN conjunct2, THEN conjunct1] modd mpos pm])
    show "\<chi> p = of_int (Legendre (4 * c * odd_discriminant_core m) (int p))"
      using local_values[OF p[THEN conjunct1] p[THEN conjunct2, THEN conjunct1]]
        swap odd_prime_even_discriminant_value[OF p[THEN conjunct1]
          p[THEN conjunct2, THEN conjunct1], of c m]
      by simp
  qed
qed

lemma even_modulus_quadratic_character:
  assumes even: "even n"
  obtains d where "quadratic_real_character_data n \<chi> d"
proof -
  have nnonzero: "n \<noteq> 0" using n by simp
  have twonotunit: "\<not> is_unit (2::nat)" by simp
  obtain m where nr: "n = 2 ^ multiplicity 2 n * m"
    and notdiv: "\<not> 2 dvd m"
    by (rule multiplicity_decompose'[OF nnonzero twonotunit])
  have modd: "odd m" using notdiv by simp
  have msf: "squarefree m"
    by (rule odd_part_squarefree[OF nr modd])
  have divides: "2 dvd n" using even by simp
  have k: "multiplicity 2 n = 2 \<or> multiplicity 2 n = 3"
    by (rule two_prime_divisor_exponent_two_or_three[OF divides])
  show thesis
  proof (cases "multiplicity 2 n = 2")
    case True
    have nr4: "n = 4 * m" using nr True by simp
    have nr': "n = 4 * nat (abs (-1::int)) * m" using nr4 by simp
    have local_values: "\<And>p. prime p \<Longrightarrow> odd p \<Longrightarrow>
      \<chi> p = of_int (Jacobi (-1) (int p) * Jacobi (int p) (int m))"
      by (rule four_part_prime_factor[OF nr4 modd msf])
    have quad: "quadratic_real_character_data n \<chi>
      (4 * (-1) * odd_discriminant_core m)"
      by (rule assemble_even_quadratic_character[OF nr' modd msf _ local_values]) simp
    show thesis by (rule that[OF quad])
  next
    case False
    then have k3: "multiplicity 2 n = 3" using k by simp
    have nr8: "n = 8 * m" using nr k3 by simp
    obtain c :: int where c: "c \<in> {2, -2}"
      and local_values: "\<And>p. prime p \<Longrightarrow> odd p \<Longrightarrow>
        \<chi> p = of_int (Jacobi c (int p) * Jacobi (int p) (int m))"
      by (rule eight_part_prime_factor[OF nr8 modd msf]) blast
    have nr': "n = 4 * nat (abs c) * m" using nr8 c by auto
    have cset: "c \<in> {(-1::int), 2, -2}" using c by auto
    have quad: "quadratic_real_character_data n \<chi>
      (4 * c * odd_discriminant_core m)"
      by (rule assemble_even_quadratic_character[OF nr' modd msf cset local_values])
    show thesis by (rule that[OF quad])
  qed
qed

lemma has_fundamental_discriminant:
  obtains d where "quadratic_real_character_data n \<chi> d"
proof (cases "odd n")
  case True
  have quad: "quadratic_real_character_data n \<chi> (odd_discriminant_core n)"
    by (rule odd_modulus_quadratic_character[OF True])
  show thesis by (rule that[OF quad])
next
  case False
  then obtain d where quad: "quadratic_real_character_data n \<chi> d"
    using even_modulus_quadratic_character by auto
  show thesis by (rule that[OF quad])
qed

end

lemma primitive_real_character_discriminant:
  assumes character: "primitive_real_dcharacter q chi"
  obtains d where "quadratic_real_character_data q chi d"
proof -
  interpret C: primitive_real_dcharacter q "residue_mult_group q" chi
    by (rule character)
  obtain d where quad: "quadratic_real_character_data q chi d"
    using C.has_fundamental_discriminant by blast
  show thesis by (rule that[OF quad])
qed

end
