theory Character_Conductor_Shape
  imports CRT_Assembly
begin

unbundle no vec_lambda_syntax

context green_primitive_real_dcharacter
begin

lemma local_prime_power_character:
  assumes prime: "prime p" and divides: "p dvd n"
  obtains psi where "green_primitive_real_dcharacter (p ^ multiplicity p n) psi"
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
    have source_green_n: "green_primitive_real_dcharacter n \<chi>"
      using source_real source_primitive
      unfolding green_primitive_real_dcharacter_def by blast
    have source_green: "green_primitive_real_dcharacter (p ^ ?k) \<chi>"
      by (subst eq[symmetric]) (rule source_green_n)
    then show thesis by (rule that)
  next
    case False
    then have rgt: "1 < r" using rpos by simp
    have pkgt: "1 < p ^ ?k" by (rule one_less_power[OF pgt kpos])
    interpret C: crt_dcharacter n "residue_mult_group n" \<chi> "p ^ ?k" r
      by (unfold_locales; use nr cp pkgt rgt in \<open>auto\<close>)
    have source_real: "real_dcharacter n \<chi>"
      using dcharacter_axioms real_dcharacter_axioms
      unfolding real_dcharacter_def by blast
    have source_primitive: "primitive_dchar n \<chi>"
      using dcharacter_axioms primitive_dchar_axioms
      unfolding primitive_dchar_def by blast
    have local_real: "real_dcharacter (p ^ ?k) C.chi_left"
      by (rule C.chi_left_real[OF source_real])
    have local_primitive: "primitive_dchar (p ^ ?k) C.chi_left"
      by (rule C.chi_left_primitive[OF source_primitive])
    have local_green: "green_primitive_real_dcharacter (p ^ ?k) C.chi_left"
      using local_real local_primitive
      unfolding green_primitive_real_dcharacter_def by blast
    show thesis by (rule that[OF local_green])
  qed
qed

lemma odd_prime_divisor_exponent_one:
  assumes prime: "prime p" and odd: "odd p" and divides: "p dvd n"
  shows "multiplicity p n = 1"
proof -
  obtain psi where local: "green_primitive_real_dcharacter (p ^ multiplicity p n) psi"
    using local_prime_power_character[OF prime divides] by blast
  interpret L: green_primitive_real_dcharacter "p ^ multiplicity p n"
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
  obtain psi where local: "green_primitive_real_dcharacter (2 ^ multiplicity 2 n) psi"
    using local_prime_power_character[of 2] divides by simp blast
  interpret L: green_primitive_real_dcharacter "2 ^ multiplicity 2 n"
    "residue_mult_group (2 ^ multiplicity 2 n)" psi
    by (rule local)
  have kpos: "0 < multiplicity 2 n"
    using divides n by (simp add: multiplicity_gt_zero_iff)
  show ?thesis by (rule L.two_prime_power_exponent_two_or_three[OF refl kpos])
qed

end

end
