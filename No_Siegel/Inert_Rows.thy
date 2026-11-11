theory Inert_Rows
  imports Inert_Frobenius Gram_Determinant
begin

text \<open>Green, Section 5: derivatives of the transformed rows.\<close>

declare [[apply_timeout = 20]]

definition green_quad_power_divisible ::
    "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> complex \<Rightarrow> bool" where
  "green_quad_power_divisible p h d z \<longleftrightarrow>
    (\<exists>w. green_quadratic_integer d w \<and> z = (of_nat p)^h * w)"

lemma green_quad_power_divisible_zero [simp]:
  "green_quad_power_divisible p h d 0"
proof -
  have qi: "green_quadratic_integer d (0::complex)"
    using green_quadratic_integer_of_int[of d 0] by simp
  show ?thesis
    unfolding green_quad_power_divisible_def
    by (rule exI[of _ 0]) (use qi in simp)
qed

lemma green_quad_power_divisible_add:
  assumes "green_quad_power_divisible p h d z"
    and "green_quad_power_divisible p h d w"
  shows "green_quad_power_divisible p h d (z+w)"
proof -
  obtain a where a: "green_quadratic_integer d a" "z = (of_nat p)^h * a"
    using assms(1) by (auto simp: green_quad_power_divisible_def)
  obtain b where b: "green_quadratic_integer d b" "w = (of_nat p)^h * b"
    using assms(2) by (auto simp: green_quad_power_divisible_def)
  show ?thesis
    unfolding green_quad_power_divisible_def
    by (rule exI[of _ "a+b"])
      (use a b in \<open>simp add: green_quadratic_integer_add algebra_simps\<close>)
qed

lemma green_quad_power_divisible_mult:
  assumes "green_quad_power_divisible p h d z"
    and "green_quad_power_divisible p k d w"
  shows "green_quad_power_divisible p (h+k) d (z*w)"
proof -
  obtain a where a: "green_quadratic_integer d a" "z = (of_nat p)^h * a"
    using assms(1) by (auto simp: green_quad_power_divisible_def)
  obtain b where b: "green_quadratic_integer d b" "w = (of_nat p)^k * b"
    using assms(2) by (auto simp: green_quad_power_divisible_def)
  show ?thesis
    unfolding green_quad_power_divisible_def
    by (rule exI[of _ "a*b"])
      (use a b in \<open>simp add: green_quadratic_integer_mult power_add algebra_simps\<close>)
qed

lemma green_quad_power_divisible_iff_one:
  "green_quad_power_divisible p 1 d z \<longleftrightarrow> green_quad_divisible p d z"
  by (simp add: green_quad_power_divisible_def green_quad_divisible_def)

lemma green_quad_power_divisible_iff_zero:
  "green_quad_power_divisible p 0 d z \<longleftrightarrow> green_quadratic_integer d z"
  by (auto simp: green_quad_power_divisible_def)

lemma green_quad_power_divisible_quadratic_integer:
  assumes "green_quad_power_divisible p h d z"
  shows "green_quadratic_integer d z"
proof -
  obtain w where w: "green_quadratic_integer d w"
    "z = (of_nat p)^h * w"
    using assms by (auto simp: green_quad_power_divisible_def)
  have factor: "green_quadratic_integer d ((of_nat p)^h)"
    by (rule green_quadratic_integer_power) simp
  show ?thesis
    unfolding w(2)
    by (rule green_quadratic_integer_mult[OF factor w(1)])
qed

lemma green_quad_power_divisible_coeff:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
    and divisible: "green_quad_power_divisible p h d z"
  obtains a b :: int where
    "green_quad_coeff d z = (int p ^ h * a, int p ^ h * b)"
proof -
  obtain w where w: "green_quadratic_integer d w"
    "z = (of_nat p)^h * w"
    using divisible by (auto simp: green_quad_power_divisible_def)
  obtain a b :: int where ab: "w = of_int a + of_int b * cpx_sqrt d"
    using w by (auto simp: green_quadratic_integer_def)
  have ze: "z = green_quad_embed d (int p ^ h * a, int p ^ h * b)"
    using w ab by (simp add: green_quad_embed_def algebra_simps)
  show thesis
    using that[of a b] by (simp add: ze green_quad_coeff_embed[OF irrational])
qed

lemma green_gram_entry_power_divisible:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
    and left: "\<And>i. i \<in> I \<Longrightarrow> green_quad_power_divisible p h d
      (green_quad_embed d (f u i))"
    and right: "\<And>i. i \<in> I \<Longrightarrow> green_quad_power_divisible p k d
      (green_quad_embed d (f v i))"
  shows "int p ^ (h+k) dvd green_gram_entry d I f u v"
  unfolding green_gram_entry_def
proof (rule dvd_sum)
  fix i assume i: "i \<in> I"
  obtain a b :: int where ab:
      "green_quad_coeff d (green_quad_embed d (f u i)) =
        (int p ^ h * a, int p ^ h * b)"
    by (rule green_quad_power_divisible_coeff[OF irrational left[OF i]])
  obtain c e :: int where ce:
      "green_quad_coeff d (green_quad_embed d (f v i)) =
        (int p ^ k * c, int p ^ k * e)"
    by (rule green_quad_power_divisible_coeff[OF irrational right[OF i]])
  have fu: "f u i = (int p ^ h * a, int p ^ h * b)"
    using ab by (simp add: green_quad_coeff_embed[OF irrational])
  have fv: "f v i = (int p ^ k * c, int p ^ k * e)"
    using ce by (simp add: green_quad_coeff_embed[OF irrational])
  show "int p ^ (h+k) dvd green_quad_coeff_pair d (f u i) (f v i)"
    by (simp add: fu fv green_quad_coeff_pair_def power_add)
qed

definition green_derivative_jets_divisible ::
    "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> complex \<Rightarrow> complex poly \<Rightarrow> bool" where
  "green_derivative_jets_divisible p h d z F \<longleftrightarrow>
    (\<forall>j. green_quad_power_divisible p h d (poly ((pderiv ^^ j) F) z))"

lemma green_derivative_jets_mult_aux:
  assumes F: "\<And>i. green_quad_power_divisible p h d
      (poly ((pderiv ^^ i) F) z)"
    and G: "\<And>i. green_quad_power_divisible p k d
      (poly ((pderiv ^^ i) G) z)"
  shows "green_quad_power_divisible p (h+k) d
    (poly ((pderiv ^^ j) (F*G)) z)"
  using F G
proof (induction j arbitrary: F G)
  case 0
  note hyp = this
  have a: "green_quad_power_divisible p h d (poly F z)"
    using hyp(1)[of 0] by simp
  have b: "green_quad_power_divisible p k d (poly G z)"
    using hyp(2)[of 0] by simp
  have both: "green_quad_power_divisible p (h+k) d (poly F z * poly G z)"
    by (rule green_quad_power_divisible_mult[OF a b])
  show ?case using both by (simp add: poly_mult)
next
  case (Suc j)
  have F': "\<And>i. green_quad_power_divisible p h d
      (poly ((pderiv ^^ i) (pderiv F)) z)"
    using Suc.prems(1)[of "Suc i" for i]
    by (simp del: funpow.simps(2) add: funpow_Suc_right)
  have G': "\<And>i. green_quad_power_divisible p k d
      (poly ((pderiv ^^ i) (pderiv G)) z)"
    using Suc.prems(2)[of "Suc i" for i]
    by (simp del: funpow.simps(2) add: funpow_Suc_right)
  have one: "green_quad_power_divisible p (h+k) d
      (poly ((pderiv ^^ j) (pderiv F * G)) z)"
    by (rule Suc.IH[OF F' Suc.prems(2)])
  have two: "green_quad_power_divisible p (h+k) d
      (poly ((pderiv ^^ j) (F * pderiv G)) z)"
    by (rule Suc.IH[OF Suc.prems(1) G'])
  show ?case
    using green_quad_power_divisible_add[OF one two]
    by (simp del: funpow.simps(2) add: funpow_Suc_right
      pderiv_mult higher_pderiv_add poly_add ac_simps)
qed

lemma green_derivative_jets_mult:
  assumes F: "green_derivative_jets_divisible p h d z F"
    and G: "green_derivative_jets_divisible p k d z G"
  shows "green_derivative_jets_divisible p (h+k) d z (F*G)"
  using F G
  by (auto simp: green_derivative_jets_divisible_def
    intro: green_derivative_jets_mult_aux)

lemma green_derivative_jets_power:
  assumes "green_derivative_jets_divisible p 1 d z F"
  shows "green_derivative_jets_divisible p h d z (F^h)"
proof (induction h)
  case 0
  have one: "green_quadratic_integer d (1::complex)"
    using green_quadratic_integer_of_int[of d 1] by simp
  have zero: "green_quadratic_integer d (0::complex)"
    using green_quadratic_integer_of_int[of d 0] by simp
  show ?case
    unfolding green_derivative_jets_divisible_def
  proof
    fix j
    show "green_quad_power_divisible p 0 d
        (poly ((pderiv ^^ j) (F^0)) z)"
    proof (cases j)
      case 0
      then show ?thesis
        using one by (simp add: green_quad_power_divisible_iff_zero)
    next
      case (Suc i)
      then show ?thesis
        using zero by (simp add: green_quad_power_divisible_iff_zero
          funpow_Suc_right funpow_swap1)
    qed
  qed
next
  case (Suc h)
  have "green_derivative_jets_divisible p (h+1) d z (F^h * F)"
    by (rule green_derivative_jets_mult[OF Suc.IH assms])
  then show ?case by (simp add: power_Suc mult.commute)
qed

definition green_inert_psi :: "nat \<Rightarrow> complex \<Rightarrow> complex poly" where
  "green_inert_psi p w = Polynomial.monom 1 p - [:w:]"

lemma green_inert_psi_eval [simp]:
  "poly (green_inert_psi p w) z = z^p - w"
  by (simp add: green_inert_psi_def poly_monom)

lemma green_inert_psi_derivative:
  "(pderiv ^^ Suc j) (green_inert_psi p w) =
    Polynomial.smult ((of_nat p)::complex)
      ((pderiv ^^ j) (Polynomial.monom 1 (p-1)))"
proof -
  have first: "pderiv (green_inert_psi p w) =
      Polynomial.smult ((of_nat p)::complex) (Polynomial.monom 1 (p-1))"
    by (simp add: green_inert_psi_def pderiv_diff pderiv_monom
      smult_monom)
  show ?thesis
    by (simp del: funpow.simps(2) add: funpow_Suc_right first
      higher_pderiv_smult)
qed

lemma green_inert_psi_jets:
  assumes z: "green_quadratic_integer d z"
    and frob: "green_quad_divisible p d (z^p-w)"
  shows "green_derivative_jets_divisible p 1 d z (green_inert_psi p w)"
  unfolding green_derivative_jets_divisible_def
proof
  fix j
  show "green_quad_power_divisible p 1 d
      (poly ((pderiv ^^ j) (green_inert_psi p w)) z)"
  proof (cases j)
    case 0
    have base: "green_quad_power_divisible p 1 d (z^p-w)"
      using frob by (simp add: green_quad_power_divisible_def
        green_quad_divisible_def)
    then show ?thesis
      using base 0 by simp
  next
    case (Suc i)
    have one: "green_quadratic_integer d (1::complex)"
      using green_quadratic_integer_of_int[of d 1] by simp
    have qi: "green_quadratic_integer d
        (poly ((pderiv ^^ i) (Polynomial.monom 1 (p-1))) z)"
      by (rule green_quadratic_integer_monom_derivative[OF one z])
    show ?thesis
      unfolding Suc green_inert_psi_derivative
        green_quad_power_divisible_def
      by (rule exI[of _ "poly ((pderiv ^^ i) (Polynomial.monom 1 (p-1))) z"])
        (use qi in simp)
  qed
qed

definition green_transformed_row_poly ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex \<Rightarrow> complex poly" where
  "green_transformed_row_poly p h r s w =
    Polynomial.monom (w^s) (r-p*h) * (green_inert_psi p w)^h"

lemma green_transformed_row_divisible:
  assumes z: "green_quadratic_integer d z"
    and w: "green_quadratic_integer d w"
    and frob: "green_quad_divisible p d (z^p-w)"
  shows "green_quad_power_divisible p h d
    (poly ((pderiv ^^ j) (green_transformed_row_poly p h r s w)) z)"
proof -
  have mon: "green_derivative_jets_divisible p 0 d z
      (Polynomial.monom (w^s) (r-p*h))"
    using z w by (auto simp: green_derivative_jets_divisible_def
      green_quad_power_divisible_iff_zero
      intro: green_quadratic_integer_monom_derivative
        green_quadratic_integer_power)
  have psi: "green_derivative_jets_divisible p h d z (green_inert_psi p w ^ h)"
    by (rule green_derivative_jets_power[OF green_inert_psi_jets[OF z frob]])
  have both: "green_derivative_jets_divisible p (0+h) d z
      (Polynomial.monom (w^s) (r-p*h) * green_inert_psi p w ^ h)"
    by (rule green_derivative_jets_mult[OF mon psi])
  show ?thesis
    using both by (simp add: green_derivative_jets_divisible_def
      green_transformed_row_poly_def)
qed

definition green_inert_h :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat" where
  "green_inert_h p S k = min (fst k div p) (S-1-snd k)"

lemma green_inert_h_bounds:
  assumes ppos: "0 < p" and s: "s < S" and i: "i \<le> green_inert_h p S (r,s)"
  shows "p*i \<le> r" "s+i < S"
proof -
  have a: "i \<le> r div p" and b: "i \<le> S-1-s"
    using i by (auto simp: green_inert_h_def)
  have "p*i \<le> p*(r div p)"
    using a by (simp add: mult_left_mono)
  also have "... \<le> r"
  proof -
    have eq: "(r div p)*p + r mod p = r"
      by (rule div_mult_mod_eq)
    show ?thesis using eq by (simp add: mult.commute)
  qed
  finally show "p*i \<le> r" .
  show "s+i < S" using b s by linarith
qed

lemma green_inert_h_lower_row:
  assumes ppos: "0 < p" and s: "s < S"
    and ipos: "0 < i" and ih: "i \<le> green_inert_h p S (r,s)"
  shows "r-p*i < r" "s+i < S"
proof -
  have pi: "p*i \<le> r" and si: "s+i < S"
    by (rule green_inert_h_bounds[OF ppos s ih])+
  have "0 < p*i" using ppos ipos by simp
  then show "r-p*i < r" using pi by linarith
  show "s+i < S" by (rule si)
qed

lemma green_transformed_row_poly_expand:
  assumes ph: "p*h \<le> r"
  shows "green_transformed_row_poly p h r s w =
    (\<Sum>i\<le>h. Polynomial.smult ((-1)^i * of_nat (h choose i))
      (Polynomial.monom (w^(s+i)) (r-p*i)))"
proof (rule poly_ext)
  fix z :: complex
  have bin: "(z^p-w)^h =
      (\<Sum>i\<le>h. of_nat (h choose i) * (-w)^i * (z^p)^(h-i))"
    using binomial_ring[of "-w" "z^p" h]
    by (simp add: add.commute)
  have e: "r-p*h+p*(h-i) = r-p*i" if ih: "i \<le> h" for i
  proof -
    have hi: "h = i + (h-i)" using ih by simp
    have eq: "p*h = p*i + p*(h-i)"
      by (subst hi) (simp add: distrib_left)
    show ?thesis using eq ph by linarith
  qed
  have point: "w^s * z^(r-p*h) *
      (of_nat (h choose i) * (-w)^i * (z^p)^(h-i)) =
      ((-1)^i * of_nat (h choose i)) *
        (w^(s+i) * z^(r-p*i))" if "i \<le> h" for i
  proof -
    have zw: "z^(r-p*h) * (z^p)^(h-i) = z^(r-p*i)"
    proof -
      have "z^(r-p*h) * (z^p)^(h-i) =
          z^(r-p*h+p*(h-i))"
        by (simp add: power_add power_mult)
      also have "... = z^(r-p*i)"
        by (simp only: e[OF that])
      finally show ?thesis .
    qed
    have wi: "w^s * (-w)^i = (-1)^i * w^(s+i)"
    proof -
      have "w^s * (-w)^i = w^s * ((-1)^i * w^i)"
        by (simp only: power_minus[of w i])
      also have "... = (-1)^i * (w^s * w^i)"
        by (simp only: mult_ac)
      also have "... = (-1)^i * w^(s+i)"
        by (simp only: power_add)
      finally show ?thesis .
    qed
    have "w^s * z^(r-p*h) *
        (of_nat (h choose i) * (-w)^i * (z^p)^(h-i)) =
        of_nat (h choose i) * (w^s * (-w)^i) *
          (z^(r-p*h) * (z^p)^(h-i))"
      by (simp add: mult_ac)
    also have "... = of_nat (h choose i) *
        ((-1)^i * w^(s+i)) * z^(r-p*i)"
      by (simp only: wi zw)
    finally show ?thesis by (simp add: mult_ac)
  qed
  have sums: "(\<Sum>i\<le>h. w^s *
        (of_nat (h choose i) *
          ((-w)^i * (z^(r-p*h) * (z^p)^(h-i))))) =
      (\<Sum>i\<le>h. of_nat (h choose i) *
        ((-1)^i * (w^(s+i) * z^(r-p*i))))"
  proof (rule sum.cong[OF refl])
    fix i assume i: "i \<in> {..h}"
    have ih: "i \<le> h" using i by simp
    have lhs: "w^s *
        (of_nat (h choose i) * ((-w)^i *
          (z^(r-p*h) * (z^p)^(h-i)))) =
        w^s * z^(r-p*h) *
          (of_nat (h choose i) * (-w)^i * (z^p)^(h-i))"
      by (simp add: mult_ac)
    have rhs: "of_nat (h choose i) *
        ((-1)^i * (w^(s+i) * z^(r-p*i))) =
        ((-1)^i * of_nat (h choose i)) *
          (w^(s+i) * z^(r-p*i))"
      by (simp add: mult_ac)
    show "w^s * (of_nat (h choose i) *
        ((-w)^i * (z^(r-p*h) * (z^p)^(h-i)))) =
      of_nat (h choose i) *
        ((-1)^i * (w^(s+i) * z^(r-p*i)))"
      using lhs rhs point[OF ih] by simp
  qed
  show "poly (green_transformed_row_poly p h r s w) z =
    poly (\<Sum>i\<le>h. Polynomial.smult ((-1)^i * of_nat (h choose i))
      (Polynomial.monom (w^(s+i)) (r-p*i))) z"
    unfolding green_transformed_row_poly_def
    using sums
    by (simp add: poly_sum poly_monom bin sum_distrib_left
      mult_ac)
qed

lemma green_row_value_as_poly:
  "green_row_value (r,s) j P =
    poly ((pderiv ^^ j) (Polynomial.monom ((snd P)^s) r)) (fst P)"
  by (simp add: green_row_value_def green_first_derivative_specialize
    green_specialized_monom)

lemma green_transformed_row_value_expand:
  assumes ph: "p*h \<le> r"
  shows "poly ((pderiv ^^ j)
      (green_transformed_row_poly p h r s (snd P))) (fst P) =
    (\<Sum>i\<le>h. ((-1)^i * of_nat (h choose i)) *
      green_row_value (r-p*i,s+i) j P)"
  by (simp add: green_transformed_row_poly_expand[OF ph]
    green_row_value_as_poly higher_pderiv_sum higher_pderiv_smult
    poly_sum sum_distrib_left)

lemma green_transformed_row_relation:
  assumes ppos: "0 < p" and s: "s < S"
    and h: "h = green_inert_h p S (r,s)"
  shows "poly ((pderiv ^^ j)
      (green_transformed_row_poly p h r s (snd P))) (fst P) =
    green_row_value (r,s) j P +
      (\<Sum>i\<in>{1..h}. ((-1)^i * of_nat (h choose i)) *
        green_row_value (r-p*i,s+i) j P)"
proof -
  have ph: "p*h \<le> r"
    using green_inert_h_bounds(1)[OF ppos s, of h r] h
    by simp
  let ?f = "\<lambda>i. ((-1)^i * of_nat (h choose i)) *
        green_row_value (r-p*i,s+i) j P"
  have split: "(\<Sum>i\<le>h. ?f i) = ?f 0 + (\<Sum>i\<in>{1..h}. ?f i)"
  proof -
    have seteq: "{..h} - {0} = {1..h}" by auto
    have "(\<Sum>i\<le>h. ?f i) = ?f 0 + (\<Sum>i\<in>{..h}-{0}. ?f i)"
      by (rule sum.remove) simp_all
    then show ?thesis by (simp only: seteq)
  qed
  show ?thesis
    using green_transformed_row_value_expand[OF ph]
    by (simp add: split)
qed

lemma (in green_quadratic_character) green_inert_transformed_lattice_entry:
  assumes prime: "prime p" and odd: "odd p" and inert: "chi p = -1"
  shows "green_quad_power_divisible p h d
    (poly ((pderiv ^^ j)
      (green_transformed_row_poly p h r s
        (snd (diagonal_point (cpx_sqrt d) (of_nat x, of_nat y)))))
      (fst (diagonal_point (cpx_sqrt d) (of_nat x, of_nat y))))"
proof -
  let ?P = "diagonal_point (cpx_sqrt d) (of_nat x, of_nat y)"
  have frob: "green_quad_divisible p d (fst ?P ^ p - snd ?P)"
    using green_inert_odd_prime_lattice_frobenius[OF prime odd inert, of x y]
    by (simp add: diagonal_point_def mult.commute)
  show ?thesis
    by (rule green_transformed_row_divisible[OF
      green_lattice_coordinates_quadratic_integer(1)
      green_lattice_coordinates_quadratic_integer(2) frob])
qed

definition green_transformed_row_coeff ::
  "int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) \<Rightarrow>
    ((complex \<times> complex) \<times> nat) \<Rightarrow> int \<times> int" where
  "green_transformed_row_coeff d p S k Pj =
    green_quad_coeff d
      (poly ((pderiv ^^ snd Pj)
        (green_transformed_row_poly p (green_inert_h p S k)
          (fst k) (snd k) (snd (fst Pj)))) (fst (fst Pj)))"

lemma (in green_quadratic_character) green_inert_transformed_grid_coeff:
  assumes prime: "prime p" and odd: "odd p" and inert: "chi p = -1"
    and P: "P \<in> diagonal_grid (cpx_sqrt d) (natural_grid N)"
  shows "green_quad_power_divisible p (green_inert_h p S k) d
    (green_quad_embed d (green_transformed_row_coeff d p S k (P,j)))"
proof -
  obtain x y :: nat where eq:
    "P = diagonal_point (cpx_sqrt d) (of_nat x, of_nat y)"
    using P by (auto simp: diagonal_grid_def natural_grid_def)
  obtain r s where k: "k = (r,s)" by (cases k) auto
  have div: "green_quad_power_divisible p (green_inert_h p S k) d
    (poly ((pderiv ^^ j)
      (green_transformed_row_poly p (green_inert_h p S k)
        r s (snd P))) (fst P))"
    unfolding eq k
    by (rule green_inert_transformed_lattice_entry[OF prime odd inert])
  show ?thesis
    using div
    by (simp add: green_transformed_row_coeff_def k
      green_quad_embed_coeff[OF green_quad_power_divisible_quadratic_integer])
qed

lemma (in green_quadratic_character) green_inert_transformed_gram_entry:
  assumes prime: "prime p" and odd: "odd p" and inert: "chi p = -1"
    and P: "P \<subseteq> diagonal_grid (cpx_sqrt d) (natural_grid N)"
  shows "int p ^ (green_inert_h p S u + green_inert_h p S v) dvd
    green_gram_entry d (P \<times> {..<J})
      (green_transformed_row_coeff d p S) u v"
proof (rule green_gram_entry_power_divisible[OF lattice_slope_irrational])
  fix i assume i: "i \<in> P \<times> {..<J}"
  have "fst i \<in> diagonal_grid (cpx_sqrt d) (natural_grid N)"
    using i P by auto
  then show "green_quad_power_divisible p (green_inert_h p S u) d
      (green_quad_embed d (green_transformed_row_coeff d p S u i))"
    using green_inert_transformed_grid_coeff[OF prime odd inert, of "fst i" N S u "snd i"]
    by (cases i) auto
next
  fix i assume i: "i \<in> P \<times> {..<J}"
  have "fst i \<in> diagonal_grid (cpx_sqrt d) (natural_grid N)"
    using i P by auto
  then show "green_quad_power_divisible p (green_inert_h p S v) d
      (green_quad_embed d (green_transformed_row_coeff d p S v i))"
    using green_inert_transformed_grid_coeff[OF prime odd inert, of "fst i" N S v "snd i"]
    by (cases i) auto
qed

lemma green_determinant_power_divisible:
  fixes A :: "int mat"
  assumes A: "A \<in> carrier_mat n n"
    and entries: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow>
      int p ^ (h i + h j) dvd A $$ (i,j)"
  shows "int p ^ (2 * (\<Sum>i<n. h i)) dvd det A"
  unfolding det_def'[OF A]
proof (rule dvd_sum)
  fix \<sigma>
  assume perm: "\<sigma> \<in> {p. p permutes {0..<n}}"
  have perm': "\<sigma> permutes {0..<n}" using perm by simp
  have inj: "inj_on \<sigma> {0..<n}"
    using permutes_inj[OF perm'] by (rule inj_on_subset) simp
  have image: "\<sigma> ` {0..<n} = {0..<n}"
    by (rule permutes_image[OF perm'])
  have sum_perm: "(\<Sum>i<n. h (\<sigma> i)) = (\<Sum>i<n. h i)"
    using sum.reindex[OF inj, of h] image
    by (simp add: atLeast0LessThan)
  have powers: "(\<Prod>i<n. int p ^ (h i + h (\<sigma> i))) =
      int p ^ (2 * (\<Sum>i<n. h i))"
    by (simp add: power_sum[symmetric] sum.distrib sum_perm mult_2)
  have divides: "(\<Prod>i<n. int p ^ (h i + h (\<sigma> i))) dvd
      (\<Prod>i<n. A $$ (i,\<sigma> i))"
  proof (rule prod_dvd_prod)
    fix i assume i: "i \<in> {..<n}"
    have si: "\<sigma> i < n" using i image by auto
    show "int p ^ (h i + h (\<sigma> i)) dvd A $$ (i,\<sigma> i)"
      by (rule entries[OF _ si]) (use i in simp)
  qed
  have dvdprod: "int p ^ (2 * (\<Sum>i<n. h i)) dvd
      (\<Prod>i<n. A $$ (i,\<sigma> i))"
    using divides by (simp only: powers)
  show "int p ^ (2 * (\<Sum>i<n. h i)) dvd
      signof \<sigma> * (\<Prod>i=0..<n. A $$ (i,\<sigma> i))"
    using dvdprod by (simp add: atLeast0LessThan)
qed

lemma green_inert_h_order_sum:
  "(\<Sum>a<R*S. green_inert_h p S (green_row_order R S ! a)) =
    (\<Sum>r<R. \<Sum>s<S. min (r div p) (S-1-s))"
proof -
  have "(\<Sum>a<R*S. green_inert_h p S (green_row_order R S ! a)) =
      sum_list (map (green_inert_h p S) (green_row_order R S))"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  also have "... = (\<Sum>k\<in>green_row_indices R S. green_inert_h p S k)"
    by (simp add: sum_list_distinct_conv_sum_set)
  also have "... = (\<Sum>r<R. \<Sum>s<S. min (r div p) (S-1-s))"
    by (simp add: green_row_indices_def green_inert_h_def
      sum.cartesian_product split_def)
  finally show ?thesis .
qed

lemma (in green_quadratic_character) green_inert_transformed_determinant_divisible:
  assumes prime: "prime p" and odd: "odd p" and inert: "chi p = -1"
    and P: "P \<subseteq> diagonal_grid (cpx_sqrt d) (natural_grid N)"
  shows "int p ^ (2 * (\<Sum>a<R*S.
      green_inert_h p S (green_row_order R S ! a))) dvd
    green_gram_determinant d (P \<times> {..<J})
      (green_transformed_row_coeff d p S) (green_row_order R S)"
  unfolding green_gram_determinant_def
proof (rule green_determinant_power_divisible[
    where n="R*S" and h="\<lambda>a. green_inert_h p S (green_row_order R S ! a)"])
  show "green_gram_matrix d (P \<times> {..<J})
      (green_transformed_row_coeff d p S) (green_row_order R S)
    \<in> carrier_mat (R*S) (R*S)"
  proof -
    have "green_gram_matrix d (P \<times> {..<J})
        (green_transformed_row_coeff d p S) (green_row_order R S)
      \<in> carrier_mat (length (green_row_order R S))
          (length (green_row_order R S))"
      by (rule green_gram_matrix_carrier)
    then show ?thesis by (simp only: green_row_order_length)
  qed
  fix a b assume a: "a < R*S" and b: "b < R*S"
  have al: "a < length (green_row_order R S)" using a by simp
  have bl: "b < length (green_row_order R S)" using b by simp
  show "int p ^ (green_inert_h p S (green_row_order R S ! a) +
      green_inert_h p S (green_row_order R S ! b)) dvd
    green_gram_matrix d (P \<times> {..<J})
      (green_transformed_row_coeff d p S) (green_row_order R S) $$ (a,b)"
    unfolding green_gram_matrix_entry[OF al bl]
    by (rule green_inert_transformed_gram_entry[OF prime odd inert P])
qed

lemma (in green_quadratic_character) green_inert_transformed_paper_determinant_divisible:
  assumes prime: "prime p" and odd: "odd p" and inert: "chi p = -1"
    and P: "P \<subseteq> diagonal_grid (cpx_sqrt d) (natural_grid N)"
  shows "int p ^ (2 * (\<Sum>r<R. \<Sum>s<S.
      min (r div p) (S-1-s))) dvd
    green_gram_determinant d (P \<times> {..<J})
      (green_transformed_row_coeff d p S) (green_row_order R S)"
  using green_inert_transformed_determinant_divisible[OF prime odd inert P,
      where R=R and S=S and J=J]
  by (simp only: green_inert_h_order_sum)

declare [[apply_timeout = 0]]

end
