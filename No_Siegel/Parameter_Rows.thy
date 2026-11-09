theory Parameter_Rows
  imports Lattice_Rows
begin

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

end
