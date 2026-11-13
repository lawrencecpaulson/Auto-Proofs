theory Archimedean_Conjugate
  imports Gram_Hadamard
begin

text \<open>Green, Section 4: elementary bounds for the lattice coordinates
  and derivative entries used in the archimedean determinant estimate.\<close>

lemma green_diagonal_coordinate_norm_bound:
  fixes a :: complex
  assumes x: "x < N" and y: "y < N"
  shows "norm (fst (diagonal_point a (of_nat x, of_nat y))) \<le>
      real N * (1 + norm a)"
    and "norm (snd (diagonal_point a (of_nat x, of_nat y))) \<le>
      real N * (1 + norm a)"
proof -
  have xN: "real x \<le> real N" using x by simp
  have yN: "real y \<le> real N" using y by simp
  have bound: "real x + norm a * real y \<le>
      real N * (1 + norm a)"
  proof -
    have "norm a * real y \<le> norm a * real N"
      using yN by (rule mult_left_mono) simp
    with xN show ?thesis by (simp add: algebra_simps)
  qed
  have "norm (of_nat x + a * of_nat y) \<le>
      real x + norm a * real y"
    using norm_triangle_ineq[of "of_nat x" "a * of_nat y"]
    by (simp add: norm_mult)
  then show "norm (fst (diagonal_point a (of_nat x, of_nat y))) \<le>
      real N * (1 + norm a)"
    using bound by (simp add: diagonal_point_def)
  have "norm (of_nat x - a * of_nat y) \<le>
      real x + norm a * real y"
    using norm_triangle_ineq4[of "of_nat x" "a * of_nat y"]
    by (simp add: norm_mult)
  then show "norm (snd (diagonal_point a (of_nat x, of_nat y))) \<le>
      real N * (1 + norm a)"
    using bound by (simp add: diagonal_point_def)
qed

lemma (in green_quadratic_character) green_paper_coordinate_norm_bound:
  assumes x: "x < N" and y: "y < N"
  shows "norm (fst (diagonal_point (cpx_sqrt d) (of_nat x, of_nat y))) \<le>
      2 * real N * sqrt (real q)"
    and "norm (snd (diagonal_point (cpx_sqrt d) (of_nat x, of_nat y))) \<le>
      2 * real N * sqrt (real q)"
proof -
  have sqge: "1 \<le> sqrt (real q)"
    using conductor_pos by simp
  have small: "real N * 1 \<le> real N * sqrt (real q)"
    using sqge by (rule mult_left_mono) simp
  have ne: "real N * (1 + norm (cpx_sqrt d)) \<le>
      2 * real N * sqrt (real q)"
    using small lattice_slope_norm
    by (simp add: algebra_simps; linarith)
  show "norm (fst (diagonal_point (cpx_sqrt d)
      (of_nat x, of_nat y))) \<le> 2 * real N * sqrt (real q)"
    using green_diagonal_coordinate_norm_bound(1)[OF x y, of "cpx_sqrt d"]
      ne by linarith
  show "norm (snd (diagonal_point (cpx_sqrt d)
      (of_nat x, of_nat y))) \<le> 2 * real N * sqrt (real q)"
    using green_diagonal_coordinate_norm_bound(2)[OF x y, of "cpx_sqrt d"]
      ne by linarith
qed

fun green_falling_factorial :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "green_falling_factorial r 0 = 1"
| "green_falling_factorial r (Suc j) =
    r * green_falling_factorial (r - 1) j"

lemma green_complex_higher_pderiv_monom:
  fixes c :: complex
  assumes jr: "j \<le> r"
  shows "(pderiv ^^ j) (Polynomial.monom c r) =
    Polynomial.monom (of_nat (green_falling_factorial r j) * c) (r-j)"
  using jr
proof (induction j arbitrary: r c)
  case 0
  then show ?case by simp
next
  case (Suc j)
  have jle: "j \<le> r - 1" using Suc.prems by arith
  have deriv: "(pderiv ^^ Suc j) (Polynomial.monom c r) =
      (pderiv ^^ j) (Polynomial.monom (of_nat r * c) (r - 1))"
    by (simp del: funpow.simps add: funpow_Suc_right pderiv_monom)
  have ih: "(pderiv ^^ j) (Polynomial.monom (of_nat r * c) (r-1)) =
      Polynomial.monom
        (of_nat (green_falling_factorial (r-1) j) * (of_nat r * c))
        ((r-1)-j)"
    by (rule Suc.IH[OF jle])
  show ?case
    using Suc.prems
    unfolding deriv ih
    by (simp add: mult_ac)
qed

lemma green_complex_higher_pderiv_monom_zero:
  fixes c :: complex
  assumes rj: "r < j"
  shows "(pderiv ^^ j) (Polynomial.monom c r) = 0"
  using rj
proof (induction j arbitrary: r c)
  case 0
  then show ?case by simp
next
  case (Suc j)
  show ?case
  proof (cases r)
    case 0
    then show ?thesis
      by (simp del: funpow.simps add: funpow_Suc_right pderiv_monom)
  next
    case (Suc t)
    have tj: "t < j" using Suc.prems by (simp add: Suc)
    have deriv: "(pderiv ^^ Suc j) (Polynomial.monom c r) =
        (pderiv ^^ j) (Polynomial.monom (of_nat r * c) (r-1))"
      by (simp del: funpow.simps add: funpow_Suc_right pderiv_monom)
    have rless: "r - 1 < j" using tj Suc by simp
    show ?thesis
      unfolding deriv by (rule Suc.IH[OF rless])
  qed
qed

lemma green_row_value_monom_formula:
  assumes jr: "j \<le> r"
  shows "green_row_value (r,s) j p =
    of_nat (green_falling_factorial r j) *
      fst p ^ (r-j) * snd p ^ s"
  using green_complex_higher_pderiv_monom[OF jr, of "snd p ^ s"]
  by (simp add: green_row_value_def green_first_derivative_specialize
    green_specialized_monom poly_monom mult_ac)

lemma green_row_value_monom_zero:
  assumes rj: "r < j"
  shows "green_row_value (r,s) j p = 0"
  using green_complex_higher_pderiv_monom_zero[OF rj, of "snd p ^ s"]
  by (simp add: green_row_value_def green_first_derivative_specialize
    green_specialized_monom)

lemma green_quad_coeff_pair_as_two_norms:
  fixes a b d :: int
  shows "real_of_int (green_quad_coeff_pair d (a,b) (a,b)) =
    norm (green_quad_embed d (a,b)) ^ 2 +
    norm (green_quad_embed d (a, - b)) ^ 2"
proof -
  have parallelogram:
    "norm (z+w) ^ 2 + norm (z-w) ^ 2 =
      2 * (norm z ^ 2 + norm w ^ 2)" for z w :: complex
  proof -
    have plus: "of_real (norm (z+w) ^ 2) =
        (z+w) * cnj (z+w)"
      by (rule complex_norm_square)
    have minus: "of_real (norm (z-w) ^ 2) =
        (z-w) * cnj (z-w)"
      by (rule complex_norm_square)
    have zs: "of_real (norm z ^ 2) = z * cnj z"
      by (rule complex_norm_square)
    have ws: "of_real (norm w ^ 2) = w * cnj w"
      by (rule complex_norm_square)
    have "of_real (norm (z+w) ^ 2 + norm (z-w) ^ 2) =
        (z+w) * cnj (z+w) + (z-w) * cnj (z-w)"
      using plus minus by simp
    also have "... = 2 * (z * cnj z + w * cnj w)"
      by (simp add: algebra_simps)
    also have "... = of_real (2 * (norm z ^ 2 + norm w ^ 2))"
      using zs ws by simp
    finally show ?thesis by (simp only: of_real_eq_iff)
  qed
  have slope: "norm (cpx_sqrt d) ^ 2 = real_of_int (abs d)"
    using norm_cpx_sqrt[of d] by simp
  have "norm (green_quad_embed d (a,b)) ^ 2 +
      norm (green_quad_embed d (a, - b)) ^ 2 =
      2 * (real_of_int a ^ 2 +
        real_of_int (abs d) * real_of_int b ^ 2)"
    using parallelogram[of "of_int a" "of_int b * cpx_sqrt d"] slope
    by (simp add: green_quad_embed_def norm_mult power_mult_distrib
      algebra_simps)
  then show ?thesis
    by (simp add: green_quad_coeff_pair_def power2_eq_square
      algebra_simps)
qed

text \<open>Green, Section 4: the derivative coefficient is a falling
  factorial, bounded by the row dimension to the derivative order.\<close>

lemma green_falling_coefficient_bound:
  assumes jr: "j \<le> r" and rR: "r < R"
  shows "green_falling_factorial r j \<le> R ^ j"
  using jr rR
proof (induction j arbitrary: r)
  case 0
  then show ?case by simp
next
  case (Suc j)
  have jle: "j \<le> r - 1" using Suc.prems by arith
  have smaller: "green_falling_factorial (r-1) j \<le> R ^ j"
    by (rule Suc.IH[OF jle]) (use Suc.prems in simp)
  have rle: "r \<le> R" using Suc.prems by simp
  have "r * green_falling_factorial (r-1) j \<le> R * R ^ j"
    by (rule mult_mono[OF rle smaller]) simp_all
  then show ?case by (simp add: power_Suc mult_ac)
qed

lemma green_row_value_norm_bound:
  fixes B :: real
  assumes rR: "r < R" and jJ: "j \<le> J" and B1: "1 \<le> B"
    and z: "norm (fst p) \<le> B" and w: "norm (snd p) \<le> B"
  shows "norm (green_row_value (r,s) j p) \<le>
    real R ^ J * B ^ (r+s)"
proof (cases "j \<le> r")
  case False
  have "green_row_value (r,s) j p = 0"
    by (rule green_row_value_monom_zero) (use False in simp)
  then show ?thesis using B1 by simp
next
  case True
  let ?c = "of_nat (green_falling_factorial r j) :: complex"
  have R1: "1 \<le> real R" using rR by simp
  have B0: "0 \<le> B" using B1 by linarith
  have coeff: "norm ?c \<le> real R ^ j"
    using green_falling_coefficient_bound[OF True rR] by simp
  have zpow: "norm (fst p) ^ (r-j) \<le> B ^ (r-j)"
    by (rule power_mono) (use z in simp_all)
  have wpow: "norm (snd p) ^ s \<le> B ^ s"
    by (rule power_mono) (use w in simp_all)
  have arg: "norm (fst p) ^ (r-j) * norm (snd p) ^ s \<le>
      B ^ (r-j+s)"
  proof -
    have "norm (fst p) ^ (r-j) * norm (snd p) ^ s \<le>
        B ^ (r-j) * B ^ s"
      by (rule mult_mono[OF zpow wpow]) (use B1 in simp_all)
    also have "... = B ^ (r-j+s)"
      by (simp add: power_add)
    finally show ?thesis .
  qed
  have Rpow: "real R ^ j \<le> real R ^ J"
    by (rule power_increasing[OF jJ R1])
  have Bpow: "B ^ (r-j+s) \<le> B ^ (r+s)"
    by (rule power_increasing) (use True B1 in simp_all)
  have eq: "norm (green_row_value (r,s) j p) =
      norm ?c * (norm (fst p) ^ (r-j) * norm (snd p) ^ s)"
    by (simp add: green_row_value_monom_formula[OF True]
      norm_mult norm_power algebra_simps)
  have first: "norm ?c *
      (norm (fst p) ^ (r-j) * norm (snd p) ^ s) \<le>
      real R ^ j * B ^ (r-j+s)"
    by (rule mult_mono[OF coeff arg]) (use B0 in simp_all)
  have second: "real R ^ j * B ^ (r-j+s) \<le>
      real R ^ J * B ^ (r+s)"
    by (rule mult_mono[OF Rpow Bpow]) (use B0 in simp_all)
  show ?thesis using eq first second by linarith
qed

lemma (in green_quadratic_character) green_paper_box_ge_one:
  assumes Npos: "0 < N"
  shows "1 \<le> 2 * real N * sqrt (real q)"
proof -
  have N1: "1 \<le> real N" using Npos by simp
  have q1: "1 \<le> sqrt (real q)" using conductor_pos by simp
  have "1 * 1 \<le> real N * sqrt (real q)"
    by (rule mult_mono[OF N1 q1]) simp_all
  then show ?thesis by linarith
qed

lemma (in green_quadratic_character) green_lattice_row_value_norm_bound:
  assumes Npos: "0 < N" and rR: "r < R" and jJ: "j \<le> J"
    and p: "p \<in> diagonal_grid (cpx_sqrt d) (natural_grid N)"
  shows "norm (green_row_value (r,s) j p) \<le>
    real R ^ J * (2 * real N * sqrt (real q)) ^ (r+s)"
proof -
  obtain x y :: nat where x: "x < N" and y: "y < N"
    and peq: "p = diagonal_point (cpx_sqrt d) (of_nat x, of_nat y)"
    using p by (auto simp: diagonal_grid_def natural_grid_def)
  let ?B = "2 * real N * sqrt (real q)"
  have B1: "1 \<le> ?B" by (rule green_paper_box_ge_one[OF Npos])
  have z: "norm (fst p) \<le> ?B"
    using green_paper_coordinate_norm_bound(1)[OF x y]
    by (simp add: peq)
  have w: "norm (snd p) \<le> ?B"
    using green_paper_coordinate_norm_bound(2)[OF x y]
    by (simp add: peq)
  show ?thesis
    by (rule green_row_value_norm_bound[OF rR jJ B1 z w])
qed

text \<open>Green, Section 4: the two embeddings of a lattice row are
  bounded by the same coordinate estimate.\<close>

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

end
