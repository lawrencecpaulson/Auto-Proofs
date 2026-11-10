theory Archimedean_Rows
  imports Gram_Hadamard
begin

text \<open>Green, Section 4: elementary bounds for the lattice coordinates
  and derivative entries used in the archimedean determinant estimate.\<close>

declare [[apply_timeout = 20]]

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

declare [[apply_timeout = 0]]

end
