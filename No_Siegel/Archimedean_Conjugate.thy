theory Archimedean_Conjugate
  imports Archimedean_Entry_Bound
begin

text \<open>Green, Section 4: the two embeddings of a lattice row are
  bounded by the same coordinate estimate.\<close>

declare [[apply_timeout = 20]]

lemma green_quad_galois_embed:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
  shows "green_quad_galois d (green_quad_embed d (a,b)) =
    green_quad_embed d (a,-b)"
  by (simp add: green_quad_galois_def
    green_quad_coeff_embed[OF irrational])

lemma green_quad_galois_of_nat:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
  shows "green_quad_galois d (of_nat n) = of_nat n"
  using green_quad_galois_embed[OF irrational, of "int n" 0]
  by (simp add: green_quad_embed_def)

lemma green_quad_galois_mult:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
    and z: "green_quadratic_integer d z"
    and w: "green_quadratic_integer d w"
  shows "green_quad_galois d (z * w) =
    green_quad_galois d z * green_quad_galois d w"
proof -
  obtain a b :: int where ze: "z = green_quad_embed d (a,b)"
    using z by (auto simp: green_quadratic_integer_def
      green_quad_embed_def)
  obtain c e :: int where we: "w = green_quad_embed d (c,e)"
    using w by (auto simp: green_quadratic_integer_def
      green_quad_embed_def)
  show ?thesis
    by (simp add: ze we green_quad_embed_mult
      green_quad_galois_embed[OF irrational] algebra_simps)
qed

lemma green_quad_galois_power:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
    and z: "green_quadratic_integer d z"
  shows "green_quad_galois d (z ^ n) =
    green_quad_galois d z ^ n"
proof (induction n)
  case 0
  then show ?case
    using green_quad_galois_of_nat[OF irrational, of 1] by simp
next
  case (Suc n)
  have zn: "green_quadratic_integer d (z ^ n)"
    by (rule green_quadratic_integer_power[OF z])
  show ?case
    using green_quad_galois_mult[OF irrational zn z] Suc.IH
    by (simp add: power_Suc mult.commute)
qed

lemma green_quad_galois_diagonal_coordinates:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
  shows "green_quad_galois d
      (fst (diagonal_point (cpx_sqrt d) (of_nat x, of_nat y))) =
      snd (diagonal_point (cpx_sqrt d) (of_nat x, of_nat y))"
    and "green_quad_galois d
      (snd (diagonal_point (cpx_sqrt d) (of_nat x, of_nat y))) =
      fst (diagonal_point (cpx_sqrt d) (of_nat x, of_nat y))"
  using green_quad_galois_embed[OF irrational, of "int x" "int y"]
    green_quad_galois_embed[OF irrational, of "int x" "- int y"]
  by (simp_all add: diagonal_point_def green_quad_embed_def algebra_simps)

lemma green_quad_galois_row_value:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
    and z: "green_quadratic_integer d (fst p)"
    and w: "green_quadratic_integer d (snd p)"
    and swap: "green_quad_galois d (fst p) = snd p"
      "green_quad_galois d (snd p) = fst p"
  shows "green_quad_galois d (green_row_value (r,s) j p) =
    green_row_value (r,s) j (snd p, fst p)"
proof (cases "j \<le> r")
  case False
  then have rj: "r < j" by simp
  have zero1: "green_row_value (r,s) j p = 0"
    by (rule green_row_value_monom_zero[OF rj])
  have zero2: "green_row_value (r,s) j (snd p, fst p) = 0"
    by (rule green_row_value_monom_zero[OF rj])
  show ?thesis
    using green_quad_galois_of_nat[OF irrational, of 0]
    by (simp add: zero1 zero2)
next
  case True
  let ?c = "green_falling_factorial r j"
  have c: "green_quadratic_integer d (of_nat ?c)" by simp
  have zn: "green_quadratic_integer d (fst p ^ (r-j))"
    by (rule green_quadratic_integer_power[OF z])
  have first:
    "green_quad_galois d (of_nat ?c * fst p ^ (r-j)) =
      of_nat ?c * snd p ^ (r-j)"
    using green_quad_galois_mult[OF irrational c zn]
      green_quad_galois_of_nat[OF irrational, of ?c]
      green_quad_galois_power[OF irrational z, of "r-j"] swap
    by simp
  have product: "green_quadratic_integer d
      (of_nat ?c * fst p ^ (r-j))"
    by (rule green_quadratic_integer_mult[OF c zn])
  have second:
    "green_quad_galois d
      ((of_nat ?c * fst p ^ (r-j)) * snd p ^ s) =
      (of_nat ?c * snd p ^ (r-j)) * fst p ^ s"
    using green_quad_galois_mult[OF irrational product
        green_quadratic_integer_power[OF w]]
      green_quad_galois_power[OF irrational w, of s] first swap
    by simp
  show ?thesis
    using second
    by (simp add: green_row_value_monom_formula[OF True] algebra_simps)
qed

lemma green_quad_coeff_pair_self_bound:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
    and integral: "green_quadratic_integer d z"
    and zbound: "norm z \<le> M"
    and gbound: "norm (green_quad_galois d z) \<le> M"
  shows "real_of_int
    (green_quad_coeff_pair d (green_quad_coeff d z)
      (green_quad_coeff d z)) \<le> 2 * M ^ 2"
proof -
  obtain a b where ab: "green_quad_coeff d z = (a,b)"
    by (cases "green_quad_coeff d z") auto
  have eq: "z = green_quad_embed d (a,b)"
    using green_quad_embed_coeff[OF integral] by (simp add: ab)
  have geq: "green_quad_galois d z = green_quad_embed d (a,-b)"
    using green_quad_galois_embed[OF irrational, of a b] by (simp add: eq)
  have zb: "norm z ^ 2 \<le> M ^ 2"
    by (rule power_mono) (use zbound in simp_all)
  have gb: "norm (green_quad_galois d z) ^ 2 \<le> M ^ 2"
    by (rule power_mono) (use gbound in simp_all)
  have identity: "real_of_int
      (green_quad_coeff_pair d (green_quad_coeff d z)
        (green_quad_coeff d z)) =
      norm z ^ 2 + norm (green_quad_galois d z) ^ 2"
  proof -
    have "real_of_int
        (green_quad_coeff_pair d (green_quad_coeff d z)
          (green_quad_coeff d z)) =
        norm (green_quad_embed d (a,b)) ^ 2 +
          norm (green_quad_embed d (a,-b)) ^ 2"
      using green_quad_coeff_pair_as_two_norms[of d a b]
      by (simp only: ab)
    also have "... = norm z ^ 2 +
        norm (green_quad_galois d z) ^ 2"
      by (simp only: eq[symmetric] geq[symmetric])
    finally show ?thesis .
  qed
  show ?thesis using identity zb gb by linarith
qed

lemma green_row_coeff_pair_bound:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
    and z: "green_quadratic_integer d (fst p)"
    and w: "green_quadratic_integer d (snd p)"
    and swap: "green_quad_galois d (fst p) = snd p"
      "green_quad_galois d (snd p) = fst p"
    and rR: "r < R" and jJ: "j \<le> J" and B1: "1 \<le> B"
    and zb: "norm (fst p) \<le> B" and wb: "norm (snd p) \<le> B"
  shows "real_of_int
    (green_quad_coeff_pair d
      (green_quad_coeff d (green_row_value (r,s) j p))
      (green_quad_coeff d (green_row_value (r,s) j p))) \<le>
    2 * (real R ^ J * B ^ (r+s)) ^ 2"
proof -
  have integral: "green_quadratic_integer d
      (green_row_value (r,s) j p)"
    unfolding green_row_value_def
    by (rule green_row_entry_quadratic_integer[OF z w])
  have first: "norm (green_row_value (r,s) j p) \<le>
      real R ^ J * B ^ (r+s)"
    by (rule green_row_value_norm_bound[OF rR jJ B1 zb wb])
  have swapped: "norm (green_row_value (r,s) j (snd p, fst p)) \<le>
      real R ^ J * B ^ (r+s)"
    by (rule green_row_value_norm_bound[OF rR jJ B1])
      (use zb wb in simp_all)
  have second: "norm (green_quad_galois d
      (green_row_value (r,s) j p)) \<le>
      real R ^ J * B ^ (r+s)"
    using swapped
      green_quad_galois_row_value[OF irrational z w swap]
    by simp
  show ?thesis
    by (rule green_quad_coeff_pair_self_bound[OF irrational integral
      first second])
qed

declare [[apply_timeout = 0]]

end
