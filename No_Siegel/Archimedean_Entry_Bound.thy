theory Archimedean_Entry_Bound
  imports Archimedean_Rows
begin

text \<open>Green, Section 4: the derivative coefficient is a falling
  factorial, bounded by the row dimension to the derivative order.\<close>

declare [[apply_timeout = 20]]

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

declare [[apply_timeout = 0]]

end
