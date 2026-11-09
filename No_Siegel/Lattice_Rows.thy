theory Lattice_Rows
  imports Row_Vector
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

end
