theory Quadratic_Character_Data
  imports "Schwartz_Zippel.Schwartz_Zippel"
    "Diophantine_Universal_Pairs.Substitutions"
    "HOL-Number_Theory.Euler_Criterion"
    "Dirichlet_L.Dirichlet_Characters"
    "Continued_Fractions.Quadratic_Irrationals"
    "Diophantine_Universal_Pairs.Algebra_Basics"
    "HOL-Computational_Algebra.Squarefree"
begin

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

locale quadratic_real_character_data =
  fixes q :: nat and chi :: "nat \<Rightarrow> complex" and d :: int
  assumes character: "dcharacter q chi"
    and conductor_discriminant: "q = nat (abs d)"
    and fundamental: "fundamental_discriminant d"
    and odd_prime_character:
      "\<forall>p::nat. prime p \<and> odd p \<and> \<not> p dvd q \<longrightarrow>
        chi p = of_int (Legendre d (int p))"
begin

end

end
