theory Quadratic_Classification
  imports Quadratic_Character
    "Dirichlet_L.Dirichlet_L_Functions"
    "Gauss_Sums.Gauss_Sums"
    "Probabilistic_Prime_Tests.Legendre_Symbol"
begin

unbundle no vec_lambda_syntax

text \<open>Prerequisite to Green, Section 2: begin the classification
  of primitive real Dirichlet characters. We use AFP's real-character
  and conductor locales.\<close>

locale green_primitive_real_dcharacter =
  real_dcharacter + primitive_dchar
begin

lemma conductor_eq_modulus: "conductor = n"
proof (rule antisym)
  show "conductor \<le> n" by (rule conductor_le_modulus)
  show "n \<le> conductor"
  proof (rule ccontr)
    assume "\<not> n \<le> conductor"
    then have "conductor < n" by simp
    then show False
      using conductor_induced no_induced_modulus by blast
  qed
qed

lemma nonprincipal: "\<chi> \<noteq> principal_dchar n"
  using principal_not_primitive primitive_dchar_axioms by blast

lemma square_principal:
  "\<chi> a ^ 2 = principal_dchar n a"
  using char_cases[of a] eq_zero_iff[of a]
  by (auto simp: principal_dchar_def)

lemma negative_value_exists:
  obtains a where "coprime a n" "\<chi> a = -1"
proof -
  obtain a where ne: "\<chi> a \<noteq> principal_dchar n a"
    using nonprincipal by (auto simp: fun_eq_iff)
  have coprime: "coprime a n"
  proof (rule ccontr)
    assume "\<not>coprime a n"
    then have "\<chi> a = 0" by (rule eq_zero)
    then show False using ne \<open>\<not>coprime a n\<close>
      by (simp add: principal_dchar_def)
  qed
  have "\<chi> a = -1"
    using ne coprime char_cases[of a] eq_zero_iff[of a]
    by (auto simp: principal_dchar_def)
  then show thesis by (rule that[OF coprime])
qed

lemma square_residue_value_one:
  assumes coprime: "coprime a n"
    and square: "[y ^ 2 = a] (mod n)"
  shows "\<chi> a = 1"
proof -
  have eq: "\<chi> a = \<chi> (y ^ 2)"
    by (rule cong) (rule cong_sym[OF square])
  have nonzero: "\<chi> a \<noteq> 0"
    using coprime by (simp add: eq_zero_iff)
  show ?thesis
    using eq nonzero char_cases[of y]
    by (auto simp: mult.power)
qed

lemma induced_modulus_of_square_lifts:
  assumes divides: "d dvd n"
    and lifts: "\<And>a. coprime a n \<Longrightarrow> [a = 1] (mod d) \<Longrightarrow>
      \<exists>y. [y ^ 2 = a] (mod n)"
  shows "induced_modulus d"
proof (rule induced_modulusI[OF divides])
  fix a
  assume cp: "coprime a n" and one: "[a = 1] (mod d)"
  obtain y where square: "[y ^ 2 = a] (mod n)"
    using lifts[OF cp one] by blast
  show "\<chi> a = 1"
    by (rule square_residue_value_one[OF cp square])
qed

lemma integer_square_residue_value_one:
  assumes coprime: "coprime a n"
    and square: "QuadRes (int n) (int a)"
  shows "\<chi> a = 1"
proof -
  obtain y :: int where sq: "[y ^ 2 = int a] (mod int n)"
    using square by (auto simp: QuadRes_def)
  let ?z = "nat (y mod int n)"
  have npos: "0 < n" using n by simp
  have lift: "int ?z = y mod int n"
    using npos by simp
  have sq_int: "[int ?z ^ 2 = int a] (mod int n)"
    using sq npos by (simp add: lift cong_def power_mod)
  have sq_nat: "[?z ^ 2 = a] (mod n)"
    using sq_int by (simp flip: cong_int_iff)
  show ?thesis
    by (rule square_residue_value_one[OF coprime sq_nat])
qed

lemma Legendre_one_value_one:
  assumes "coprime a n"
    and "Legendre (int a) (int n) = 1"
  shows "\<chi> a = 1"
proof -
  have "QuadRes (int n) (int a)"
    using assms(2) by (auto simp: Legendre_def split: if_splits)
  then show ?thesis
    by (rule integer_square_residue_value_one[OF assms(1)])
qed

lemma negative_value_not_residue:
  assumes "\<chi> a = -1"
  shows "\<not> QuadRes (int n) (int a)"
proof
  assume qr: "QuadRes (int n) (int a)"
  have cp: "coprime a n"
    using assms eq_zero_iff[of a] by auto
  have "\<chi> a = 1"
    by (rule integer_square_residue_value_one[OF cp qr])
  with assms show False by simp
qed

lemma prime_modulus_legendre:
  assumes prime: "prime n"
  shows "\<chi> a = of_int (Legendre (int a) (int n))"
proof -
  obtain b where cpb: "coprime b n" and bneg: "\<chi> b = -1"
    using negative_value_exists by blast
  have prime_int: "prime (int n)"
    using prime by (simp add: prime_int_nat_transfer)
  have lb_zero: "Legendre (int b) (int n) \<noteq> 0"
    using cpb prime_int by simp
  have lb_not_one: "Legendre (int b) (int n) \<noteq> 1"
    using bneg Legendre_one_value_one[OF cpb] by auto
  have lb: "Legendre (int b) (int n) = -1"
    using lb_zero lb_not_one Legendre_values[of "int b" "int n"] by auto
  show ?thesis
  proof (cases "coprime a n")
    case False
    then have "\<chi> a = 0" by (rule eq_zero)
    moreover have "Legendre (int a) (int n) = 0"
      using False prime_int by simp
    ultimately show ?thesis by simp
  next
    case True
    then have la_zero: "Legendre (int a) (int n) \<noteq> 0"
      using prime_int by simp
    consider (one) "Legendre (int a) (int n) = 1"
      | (minus_one) "Legendre (int a) (int n) = -1"
      using la_zero Legendre_values[of "int a" "int n"] by auto
    then show ?thesis
    proof cases
      case one
      then show ?thesis
        using Legendre_one_value_one[OF True] by simp
    next
      case minus_one
      have cpab: "coprime (a * b) n"
        using True cpb by simp
      have lab: "Legendre (int (a * b)) (int n) = 1"
        using minus_one lb prime_int by simp
      have "\<chi> (a * b) = 1"
        by (rule Legendre_one_value_one[OF cpab lab])
      then have "- \<chi> a = 1"
        using bneg by simp
      then have "\<chi> a = -1"
        by (metis minus_minus)
      then show ?thesis using minus_one by simp
    qed
  qed
qed

end

end
