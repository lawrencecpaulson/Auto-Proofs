theory Paper_Parameters
  imports Row_Vector Quadratic_Character
begin

text \<open>Green, Section 3: instantiate the row lemma on the diagonal
  lattice used in the determinant construction.\<close>

lemma green_lattice_dimension_bound:
  fixes R S J N :: nat
  assumes size: "4 * R \<le> N * N"
    and SJ: "S = J"
    and positive: "0 < J"
    and smaller: "J < R"
  shows "2 * R * S + J * (R + S) < J * (N * N)"
proof -
  have three: "3 * R = R + R + R"
    by (simp add: numeral_3_eq_3)
  have middle: "2 * R * S + J * (R + S) = J * (3 * R + J)"
    by (simp add: SJ mult_2 three distrib_left ac_simps)
  have "3 * R + J < 4 * R"
    using smaller by simp
  then have "J * (3 * R + J) < J * (4 * R)"
    using positive by (simp add: mult_strict_left_mono)
  also have "... \<le> J * (N * N)"
    using size by (simp add: mult_left_mono)
  finally show ?thesis by (simp add: middle)
qed

lemma natural_diagonal_grid_card:
  assumes "a \<notin> Rats"
  shows "card (diagonal_grid a (natural_grid N)) = N * N"
proof -
  have inj: "inj_on (diagonal_point a)
      (natural_grid N \<times> natural_grid N)"
    using natural_diagonal_second_distinct[OF assms]
    by (auto simp: inj_on_def)
  have "card (diagonal_grid a (natural_grid N)) =
      card (natural_grid N \<times> natural_grid N)"
    unfolding diagonal_grid_def by (rule card_image[OF inj])
  also have "... = N * N"
    by (simp add: card_cartesian_product natural_grid_card natural_grid_finite)
  finally show ?thesis .
qed

lemma natural_diagonal_rows_independent:
  assumes N: "0 < N" and J: "N \<le> J" and irrational: "a \<notin> Rats"
    and dimension: "J * (N * N) > 2 * R * S + J * (R + S)"
    and relation:
      "green_row_relation (diagonal_grid a (natural_grid N)) J R S c"
  shows "\<And>k. k \<in> green_row_indices R S \<Longrightarrow> c k = 0"
proof -
  let ?I = "diagonal_grid a (natural_grid N)"
  interpret grid: green_point_configuration ?I id J
  proof
    show "finite ?I"
      by (simp add: diagonal_grid_def natural_grid_finite)
    show "inj_on (snd \<circ> id) ?I"
      using natural_diagonal_grid_second_distinct[OF irrational]
      by simp
    fix F :: "complex mpoly"
    assume nz: "F \<noteq> 0" and bv: "bivariate F"
    have nonzero: "a \<noteq> 0" using irrational by auto
    have vars: "vars F \<subseteq> {0,1}"
      using bv by (simp add: bivariate_def)
    show "card {p \<in> ?I. pair_eval F (id p) = 0}
      \<le> J * total_degree F"
      using natural_diagonal_grid_bound[OF N J nonzero nz vars] by simp
  qed
  have card: "card ?I = N * N"
    by (rule natural_diagonal_grid_card[OF irrational])
  have bound: "J * card ?I > 2 * R * S + J * (R + S)"
    using dimension by (simp add: card)
  fix k assume k: "k \<in> green_row_indices R S"
  show "c k = 0"
    by (rule grid.green_rows_independent[OF bound _ k])
      (use relation in auto)
qed

text \<open>Green, equations (2.1) and (3.2): the row-independence
  conditions for a square scale t and a sufficiently large conductor.\<close>

lemma green_square_scale_parameters:
  fixes C t :: nat
  assumes C: "2 \<le> C" and large: "2 * C \<le> t"
  defines "R \<equiv> t * t"
    and "N \<equiv> 2 * t"
    and "J \<equiv> (t * t) div C"
    and "S \<equiv> (t * t) div C"
  shows "N \<le> J"
    and "2 * R * S + J * (R + S) < J * (N * N)"
proof -
  have Cpos: "0 < C" using C by simp
  have tpos: "0 < t" using C large by simp
  have lower: "N * C \<le> R"
  proof -
    have "2 * C * t \<le> t * t"
      using large by (rule mult_right_mono) simp
    then show ?thesis by (simp add: N_def R_def ac_simps)
  qed
  have NJ: "N \<le> J"
    using lower by (simp add: J_def R_def less_eq_div_iff_mult_less_eq[OF Cpos])
  show "N \<le> J" by (fact NJ)
  have positive: "0 < J"
    using NJ tpos by (simp add: N_def)
  have Rpos: "0 < R"
    using tpos by (simp add: R_def)
  have smaller: "J < R"
    using C Rpos by (simp add: J_def R_def)
  have size: "4 * R \<le> N * N"
    by (simp add: R_def N_def ac_simps)
  have SJ: "S = J" by (simp add: S_def J_def)
  show "2 * R * S + J * (R + S) < J * (N * N)"
    by (rule green_lattice_dimension_bound[OF size SJ positive smaller])
qed

text \<open>Green, Section 2, parameter choice: the even exponent makes
  X a square, so N is twice its square root.\<close>

definition green_X :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "green_X q cparam = q ^ cparam"

definition green_N :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "green_N q cparam = 2 * q ^ (cparam div 2)"

definition green_J :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "green_J q cparam = green_X q cparam div cparam"

lemma green_even_exponent_square:
  assumes "even cparam"
  shows "green_X q cparam = q ^ (cparam div 2) * q ^ (cparam div 2)"
proof -
  have split: "cparam = cparam div 2 + cparam div 2"
    using even_two_times_div_two[OF assms] by (simp add: mult_2)
  show ?thesis
    unfolding green_X_def by (subst split) (rule power_add)
qed

lemma green_paper_row_parameters:
  assumes even: "even cparam"
    and cparam: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
  shows "green_N q cparam \<le> green_J q cparam"
    and "2 * green_X q cparam * green_J q cparam +
      green_J q cparam * (green_X q cparam + green_J q cparam) <
      green_J q cparam * (green_N q cparam * green_N q cparam)"
proof -
  let ?t = "q ^ (cparam div 2)"
  have square: "green_X q cparam = ?t * ?t"
    by (rule green_even_exponent_square[OF even])
  have base: "2 * ?t \<le> (?t * ?t) div cparam"
    "2 * (?t * ?t) * ((?t * ?t) div cparam) +
      ((?t * ?t) div cparam) * ((?t * ?t) + ((?t * ?t) div cparam)) <
      ((?t * ?t) div cparam) * ((2 * ?t) * (2 * ?t))"
    by (rule green_square_scale_parameters[OF cparam large]; simp)+
  show "green_N q cparam \<le> green_J q cparam"
    using base(1) by (simp add: green_N_def green_J_def square)
  show "2 * green_X q cparam * green_J q cparam +
      green_J q cparam * (green_X q cparam + green_J q cparam) <
      green_J q cparam * (green_N q cparam * green_N q cparam)"
    using base(2) by (simp add: green_N_def green_J_def square)
qed

lemma (in green_quadratic_character) green_paper_rows_independent:
  assumes even: "even cparam"
    and cparam: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
    and relation:
      "green_row_relation
        (diagonal_grid (cpx_sqrt d) (natural_grid (green_N q cparam)))
        (green_J q cparam) (green_X q cparam) (green_J q cparam) c"
  shows "\<And>k. k \<in> green_row_indices (green_X q cparam) (green_J q cparam)
    \<Longrightarrow> c k = 0"
proof -
  have tpos: "0 < q ^ (cparam div 2)"
    using cparam large by linarith
  have Npos: "0 < green_N q cparam"
    using tpos by (simp add: green_N_def)
  have Jbound: "green_N q cparam \<le> green_J q cparam"
    and dimension: "2 * green_X q cparam * green_J q cparam +
      green_J q cparam * (green_X q cparam + green_J q cparam) <
      green_J q cparam * (green_N q cparam * green_N q cparam)"
    by (rule green_paper_row_parameters[OF even cparam large])+
  fix k
  assume k: "k \<in> green_row_indices (green_X q cparam) (green_J q cparam)"
  show "c k = 0"
    by (rule natural_diagonal_rows_independent[OF Npos Jbound
      lattice_slope_irrational dimension relation k])
qed

end
