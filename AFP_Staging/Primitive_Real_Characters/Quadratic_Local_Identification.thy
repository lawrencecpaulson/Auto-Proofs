theory Quadratic_Local_Identification
  imports CRT_Assembly "Probabilistic_Prime_Tests.Jacobi_Symbol"
begin

unbundle no vec_lambda_syntax

context primitive_real_dcharacter
begin

lemma local_prime_power_character:
  assumes prime: "prime p" and divides: "p dvd n"
  obtains psi where "primitive_real_dcharacter (p ^ multiplicity p n) psi"
proof -
  let ?k = "multiplicity p n"
  have nnonzero: "n \<noteq> 0" using n by simp
  have pgt: "1 < p" by (rule prime_gt_1_nat[OF prime])
  have pnotunit: "\<not> is_unit p" using pgt by simp
  obtain r where nr: "n = p ^ ?k * r" and notdiv: "\<not> p dvd r"
    by (rule multiplicity_decompose'[OF nnonzero pnotunit])
  have kpos: "0 < ?k" using divides nnonzero pnotunit
    by (simp add: multiplicity_gt_zero_iff)
  have rpos: "0 < r"
  proof (rule ccontr)
    assume "\<not> 0 < r"
    then have "r = 0" by simp
    then show False using n nr by simp
  qed
  have cp_rev: "coprime r (p ^ ?k)"
    by (rule prime_imp_power_coprime[OF prime notdiv])
  have cp: "coprime (p ^ ?k) r"
    using cp_rev by (simp add: coprime_commute)
  show thesis
  proof (cases "r = 1")
    case True
    have eq: "n = p ^ ?k" using nr True by simp
    have source_real: "real_dcharacter n \<chi>"
      using dcharacter_axioms real_dcharacter_axioms
      unfolding real_dcharacter_def by blast
    have source_primitive: "primitive_dchar n \<chi>"
      using dcharacter_axioms primitive_dchar_axioms
      unfolding primitive_dchar_def by blast
    have source_green_n: "primitive_real_dcharacter n \<chi>"
      using source_real source_primitive
      unfolding primitive_real_dcharacter_def by blast
    have source_green: "primitive_real_dcharacter (p ^ ?k) \<chi>"
      by (subst eq[symmetric]) (rule source_green_n)
    then show thesis by (rule that)
  next
    case False
    then have rgt: "1 < r" using rpos by simp
    have pkgt: "1 < p ^ ?k" by (rule one_less_power[OF pgt kpos])
    obtain psi theta where local: "primitive_real_dcharacter (p ^ ?k) psi"
      by (rule crt_green_factors[OF nr cp pkgt rgt]) blast
    show thesis by (rule that[OF local])
  qed
qed

lemma odd_prime_divisor_exponent_one:
  assumes prime: "prime p" and odd: "odd p" and divides: "p dvd n"
  shows "multiplicity p n = 1"
proof -
  obtain psi where local: "primitive_real_dcharacter (p ^ multiplicity p n) psi"
    using local_prime_power_character[OF prime divides] by blast
  interpret L: primitive_real_dcharacter "p ^ multiplicity p n"
    "residue_mult_group (p ^ multiplicity p n)" psi
    by (rule local)
  have pgt: "1 < p" by (rule prime_gt_1_nat[OF prime])
  have kpos: "0 < multiplicity p n"
    using divides n pgt by (simp add: multiplicity_gt_zero_iff)
  show ?thesis by (rule L.odd_prime_power_exponent_one[OF refl prime odd kpos])
qed

lemma two_prime_divisor_exponent_two_or_three:
  assumes divides: "2 dvd n"
  shows "multiplicity 2 n = 2 \<or> multiplicity 2 n = 3"
proof -
  obtain psi where local: "primitive_real_dcharacter (2 ^ multiplicity 2 n) psi"
    using local_prime_power_character[of 2] divides by simp blast
  interpret L: primitive_real_dcharacter "2 ^ multiplicity 2 n"
    "residue_mult_group (2 ^ multiplicity 2 n)" psi
    by (rule local)
  have kpos: "0 < multiplicity 2 n"
    using divides n by (simp add: multiplicity_gt_zero_iff)
  show ?thesis by (rule L.two_prime_power_exponent_two_or_three[OF refl kpos])
qed

end

unbundle no vec_lambda_syntax

lemma odd_prime_jacobi_minus_one:
  assumes prime: "prime p" and odd: "odd p"
  shows "Jacobi (-1) (int p) = (if p mod 4 = 1 then 1 else -1)"
proof -
  have "int p mod 4 = int (p mod 4)"
    by (simp add: of_nat_mod)
  then show ?thesis
    using supplement1_Jacobi'[of "int p"] prime_gt_1_nat[OF prime] odd
    by simp
qed

context primitive_real_dcharacter
begin

lemma modulus_four_odd_prime_jacobi:
  assumes n4: "n = 4" and prime: "prime p" and odd: "odd p"
  shows "\<chi> p = of_int (Jacobi (-1) (int p))"
proof -
  have eq: "\<chi> p = \<chi> (p mod 4)"
    by (rule cong) (simp add: n4 cong_def)
  have cases: "p mod 4 = 1 \<or> p mod 4 = 3"
    using odd by presburger
  have j: "Jacobi (-1) (int p) = (if p mod 4 = 1 then 1 else -1)"
    by (rule odd_prime_jacobi_minus_one[OF prime odd])
  show ?thesis
    using eq cases j modulus_four_value_three[OF n4] by auto
qed

lemma modulus_eight_odd_prime_jacobi:
  assumes n8: "n = 8" and prime: "prime p" and odd: "odd p"
  shows "\<chi> p =
    (if \<chi> 3 = -1 then of_int (Jacobi 2 (int p))
     else of_int (Jacobi (-2) (int p)))"
proof -
  have eq: "\<chi> p = \<chi> (p mod 8)"
    by (rule cong) (simp add: n8 cong_def)
  have cases: "p mod 8 = 1 \<or> p mod 8 = 3 \<or> p mod 8 = 5 \<or> p mod 8 = 7"
    using odd by presburger
  have imod8: "int p mod 8 = int (p mod 8)"
    by (simp add: of_nat_mod)
  have j2: "Jacobi 2 (int p) =
    (if p mod 8 = 1 \<or> p mod 8 = 7 then 1 else -1)"
    using supplement2_Jacobi'[of "int p"] prime_gt_1_nat[OF prime] odd
    by (simp add: imod8)
  have j1: "Jacobi (-1) (int p) = (if p mod 4 = 1 then 1 else -1)"
    by (rule odd_prime_jacobi_minus_one[OF prime odd])
  have jprod: "Jacobi (-2) (int p) = Jacobi (-1) (int p) * Jacobi 2 (int p)"
  proof -
    have "Jacobi (-2) (int p) = Jacobi ((-1) * 2) (int p)" by simp
    also have "... = Jacobi (-1) (int p) * Jacobi 2 (int p)"
      by (rule Jacobi_mult_left)
    finally show ?thesis .
  qed
  have jminus: "Jacobi (-2) (int p) =
    (if p mod 4 = 1 then 1 else -1) *
    (if p mod 8 = 1 \<or> p mod 8 = 7 then 1 else -1)"
    using j1 j2 jprod by simp
  have mod4: "p mod 4 = (p mod 8) mod 4"
    using mod_mod_cancel[of 4 8 p] by simp
  have value3: "\<chi> 3 = -1 \<or> \<chi> 3 = 1"
    using modulus_eight_value_three_cases[OF n8] by auto
  show ?thesis
    using eq cases j2 jminus mod4 value3 modulus_eight_value_five[OF n8]
      modulus_eight_value_seven[OF n8]
    by auto
qed


end

lemma odd_squarefree_real_character_jacobi:
  fixes chi :: "nat \<Rightarrow> complex"
  assumes character: "primitive_real_dcharacter n chi"
    and odd: "odd n" and squarefree: "squarefree n"
  shows "chi a = of_int (Jacobi (int a) (int n))"
  using character odd squarefree
proof (induction n arbitrary: chi rule: less_induct)
  case (less n)
  interpret L: primitive_real_dcharacter n "residue_mult_group n" chi
    by (rule less.prems(1))
  have ngt: "1 < n" by (rule L.n)
  obtain p where prime: "prime p" and pdvd: "p dvd n"
    using prime_divisor_exists[of n] ngt by auto
  have pgt: "1 < p" by (rule prime_gt_1_nat[OF prime])
  obtain r where nr: "n = p * r"
    using pdvd by auto
  have rpos: "0 < r" using ngt nr by (cases r) auto
  have rlt: "r < n"
    using pgt rpos nr by (simp add: mult.commute)
  have rodd: "odd r" using less.prems(2) nr by simp
  have rsf: "squarefree r"
    by (rule squarefree_mono[OF _ less.prems(3)]) (simp add: nr)
  show ?case
  proof (cases "r = 1")
    case True
    have nprime: "prime n" using nr True prime by simp
    have iprime: "prime (int n)"
      using nprime by (simp add: prime_int_nat_transfer)
    show ?thesis
      using L.prime_modulus_legendre[OF nprime, of a]
        prime_p_Jacobi_eq_Legendre[OF iprime, of "int a"]
      by simp
  next
    case False
    then have rgt: "1 < r" using rpos by simp
    have notdiv: "\<not> p dvd r"
    proof
      assume "p dvd r"
      then have "p ^ 2 dvd n" using nr by (simp add: power2_eq_square)
      then have "p dvd (1::nat)"
        by (rule squarefreeD[OF less.prems(3)])
      with pgt show False by simp
    qed
    have cp: "coprime p r"
      using prime notdiv by (simp add: prime_imp_coprime)
    obtain psi theta where left_green: "primitive_real_dcharacter p psi"
      and right_green: "primitive_real_dcharacter r theta"
      and factor: "\<And>x. chi x = psi x * theta x"
      by (rule L.crt_green_factors[OF nr cp pgt rgt]) blast
    interpret P: primitive_real_dcharacter p "residue_mult_group p" psi
      by (rule left_green)
    have iprime: "prime (int p)"
      using prime by (simp add: prime_int_nat_transfer)
    have left: "psi a = of_int (Jacobi (int a) (int p))"
      using P.prime_modulus_legendre[OF prime, of a]
        prime_p_Jacobi_eq_Legendre[OF iprime, of "int a"] by simp
    have right: "theta a = of_int (Jacobi (int a) (int r))"
      by (rule less.IH[OF rlt right_green rodd rsf])
    have "chi a = psi a * theta a"
      by (rule factor)
    also have "... = of_int (Jacobi (int a) (int n))"
      using left right nr by simp
    finally show ?thesis .
  qed
qed


definition odd_discriminant_core :: "nat \<Rightarrow> int" where
  "odd_discriminant_core m = (if m mod 4 = 1 then int m else -int m)"

lemma odd_discriminant_core_reciprocity:
  assumes prime: "prime p" and podd: "odd p" and odd: "odd m"
    and mpos: "0 < m" and unramified: "\<not> p dvd m"
  shows "Jacobi (int p) (int m) = Jacobi (odd_discriminant_core m) (int p)"
proof (cases "m = 1")
  case True
  then show ?thesis using prime_gt_0_nat[OF prime]
    by (simp add: odd_discriminant_core_def)
next
  case False
  have mgt: "2 < int m" using odd mpos False by presburger
  have pgt: "2 < int p"
    using prime_gt_1_nat[OF prime] podd by presburger
  have cp_nat: "coprime m p"
    using prime unramified by (meson prime_imp_coprime coprime_commute)
  have cp: "coprime (int m) (int p)"
    using cp_nat by simp
  have imodm4: "int m mod 4 = int (m mod 4)"
    by (simp add: of_nat_mod)
  have imodp4: "int p mod 4 = int (p mod 4)"
    by (simp add: of_nat_mod)
  have mcases: "m mod 4 = 1 \<or> m mod 4 = 3"
    using odd by presburger
  have pcases: "p mod 4 = 1 \<or> p mod 4 = 3"
    using podd by presburger
  have rec: "Jacobi (int p) (int m) =
    (if m mod 4 = 3 \<and> p mod 4 = 3 then -1 else 1) * Jacobi (int m) (int p)"
    using Quadratic_Reciprocity_Jacobi'[OF cp mgt pgt]
      odd podd by (simp add: imodm4 imodp4)
  have neg: "Jacobi (-int m) (int p) =
    (if p mod 4 = 1 then 1 else -1) * Jacobi (int m) (int p)"
    using Jacobi_neg_left[of "int p" "int m"] podd pgt
    by (simp add: imodp4)
  show ?thesis
    using rec neg mcases pcases
    by (auto simp: odd_discriminant_core_def)
qed


lemma squarefree_int_transfer:
  "squarefree (int n) \<longleftrightarrow> squarefree n"
proof (cases "n = 0")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis
  proof
    assume "squarefree n"
    then show "squarefree (int n)"
      apply (subst squarefree_factorial_semiring, use False in \<open>simp; fail\<close>)
      apply (subst (asm) squarefree_factorial_semiring, use False in \<open>simp; fail\<close>)
      by (metis nat_dvd_iff nat_power_eq prime_int_nat_transfer zero_le_power_eq)
  next
    assume "squarefree (int n)"
    then show "squarefree n"
      apply (subst squarefree_factorial_semiring, use False in \<open>simp; fail\<close>)
      apply (subst (asm) squarefree_factorial_semiring, use False in \<open>simp; fail\<close>)
      by (metis of_nat_dvd_iff of_nat_power prime_nat_int_transfer)
  qed
qed

lemma odd_discriminant_core_fundamental:
  assumes odd: "odd m" and squarefree: "squarefree m"
  shows "fundamental_discriminant (odd_discriminant_core m)"
proof -
  have sf: "squarefree (odd_discriminant_core m)"
    using squarefree squarefree_int_transfer
    by (simp add: odd_discriminant_core_def)
  have imod4: "int m mod 4 = int (m mod 4)"
    by (simp add: of_nat_mod)
  have cases: "m mod 4 = 1 \<or> m mod 4 = 3"
    using odd by presburger
  have mod4: "odd_discriminant_core m mod 4 = 1"
    using cases imod4 unfolding odd_discriminant_core_def by presburger
  show ?thesis
    using sf mod4 by (simp add: fundamental_discriminant_def)
qed

context primitive_real_dcharacter
begin

lemma odd_modulus_squarefree:
  assumes odd: "odd n"
  shows "squarefree n"
proof (subst squarefree_factorial_semiring''[OF _])
  show "n \<noteq> 0" using n by simp
  show "\<forall>p. prime p \<longrightarrow> multiplicity p n \<le> 1"
  proof (intro allI impI)
    fix p :: nat
    assume prime: "prime p"
    show "multiplicity p n \<le> 1"
    proof (cases "p dvd n")
      case True
      have podd: "odd p"
      proof -
        obtain r where "n = p * r" using True by auto
        then show ?thesis using odd by simp
      qed
      have "multiplicity p n = 1"
        by (rule odd_prime_divisor_exponent_one[OF prime podd True])
      then show ?thesis by simp
    next
      case False
      then show ?thesis by (simp add: not_dvd_imp_multiplicity_0)
    qed
  qed
qed

end

end
