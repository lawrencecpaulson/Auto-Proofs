(*  Title:      Gelfond_Schneider/GS_Order.thy
    Author:     OpenAI Codex

Analytic order infrastructure for the standalone Gelfond-Schneider port.
This translates the Lean `analyticOrderAt` layer into Isabelle's native
`zorder`/`zor_poly` API for the auxiliary exponential sum.
*)

theory GS_Order
  imports
    GS_Auxiliary
    "HOL-Complex_Analysis.Laurent_Convergence"
begin

declare [[apply_timeout = 10]]

section \<open>Analytic Order of Finite Exponential Sums\<close>

lemma finite_exp_sum_holomorphic:
  assumes fin: "finite S"
  shows "(\<lambda>x::complex. \<Sum>i\<in>S. c i * exp (\<rho> i * x)) holomorphic_on A"
  using fin
proof (induction rule: finite_induct)
  case empty
  then show ?case
    by simp
next
  case (insert i S)
  have "(\<lambda>x::complex. c i * exp (\<rho> i * x)) holomorphic_on A"
    by (intro holomorphic_intros)
  moreover have "(\<lambda>x::complex. \<Sum>j\<in>S. c j * exp (\<rho> j * x)) holomorphic_on A"
    by (rule insert.IH)
  ultimately have "(\<lambda>x::complex. c i * exp (\<rho> i * x) + (\<Sum>j\<in>S. c j * exp (\<rho> j * x)))
      holomorphic_on A"
    by (intro holomorphic_intros)
  then show ?case
    using insert.hyps by simp
qed

lemma gs_aux_fun_holomorphic [holomorphic_intros]:
  "(gs_aux_fun d q \<eta>) holomorphic_on A"
  unfolding gs_aux_fun_def
  by (rule finite_exp_sum_holomorphic) (simp add: gs_grid_def)

lemma holomorphic_nonzero_zorder_ge:
  assumes holo: "f holomorphic_on UNIV"
  assumes nz: "f \<noteq> (\<lambda>_. 0)"
  assumes vanish: "\<And>k. k < n \<Longrightarrow> ((deriv ^^ k) f) z = 0"
  shows "zorder f z \<ge> n"
proof -
  obtain w where w: "f w \<noteq> 0"
    using nz by (auto simp: fun_eq_iff)
  have ana: "f analytic_on {z}"
    by (rule holomorphic_on_imp_analytic_at[OF holo]) auto
  show ?thesis
    by (rule zorder_geI[where A = UNIV and z = w]) (use ana holo w vanish in auto)
qed

lemma gs_aux_fun_zorder_ge:
  assumes nz: "gs_aux_fun d q \<eta> \<noteq> (\<lambda>_. 0)"
  assumes vanish: "\<And>k. k < n \<Longrightarrow> ((deriv ^^ k) (gs_aux_fun d q \<eta>)) z = 0"
  shows "zorder (gs_aux_fun d q \<eta>) z \<ge> n"
  by (rule holomorphic_nonzero_zorder_ge[OF gs_aux_fun_holomorphic[of d q \<eta> UNIV] nz vanish])

lemma gs_aux_fun_zorder_nonneg:
  assumes nz: "gs_aux_fun d q \<eta> \<noteq> (\<lambda>_. 0)"
  shows "0 \<le> zorder (gs_aux_fun d q \<eta>) z"
proof -
  have "zorder (gs_aux_fun d q \<eta>) z \<ge> (0::nat)"
    by (rule gs_aux_fun_zorder_ge[OF nz, of 0 z]) simp
  then show ?thesis
    by simp
qed

lemma gs_aux_fun_zor_poly_eq:
  assumes nz: "gs_aux_fun d q \<eta> \<noteq> (\<lambda>_. 0)"
  shows "eventually (\<lambda>w.
      zor_poly (gs_aux_fun d q \<eta>) z w =
      gs_aux_fun d q \<eta> w / (w - z) ^ nat (zorder (gs_aux_fun d q \<eta>) z)) (at z)"
proof -
  obtain w where w: "gs_aux_fun d q \<eta> w \<noteq> 0"
    using nz by (auto simp: fun_eq_iff)
  show ?thesis
    by (rule zor_poly_zero_eq[where S = UNIV])
       (use gs_aux_fun_holomorphic[of d q \<eta> UNIV] w in auto)
qed

lemma holomorphic_nonzero_deriv_zorder_nonzero:
  assumes holo: "f holomorphic_on UNIV"
  assumes nz: "f \<noteq> (\<lambda>_. 0)"
  shows "((deriv ^^ nat (zorder f z)) f) z \<noteq> 0"
proof -
  have ana: "f analytic_on {z}"
    by (rule holomorphic_on_imp_analytic_at[OF holo]) auto
  define g where "g = f \<circ> (\<lambda>w. z + w)"
  define F where "F = fps_expansion g 0"
  have fps: "g has_fps_expansion F"
    unfolding g_def F_def
    by (intro analytic_at_imp_has_fps_expansion_0
        analytic_on_compose_gen[OF _ ana] analytic_intros) auto
  have holo_shift: "g holomorphic_on UNIV"
    unfolding g_def
    by (intro holomorphic_on_compose_gen[OF _ holo] holomorphic_intros) auto
  obtain w where w: "f w \<noteq> 0"
    using nz by (auto simp: fun_eq_iff)
  have F_nz: "F \<noteq> 0"
  proof
    assume F0: "F = 0"
    have "g has_fps_expansion 0"
      using fps F0 by simp
    then have "g (w - z) = 0"
      by (rule has_fps_expansion_0_analytic_continuation[OF _ holo_shift]) auto
    then show False
      using w unfolding g_def by simp
  qed
  have ord0: "zorder g 0 = int (subdegree F)"
    by (rule has_fps_expansion_zorder_0[OF fps F_nz])
  have ord: "zorder f z = int (subdegree F)"
  proof -
    have shift_eq: "(\<lambda>u. f (u + z)) = g"
      unfolding g_def by (rule ext) (simp add: add.commute)
    have "zorder f z = zorder (\<lambda>u. f (u + z)) 0"
      by (rule zorder_shift)
    also have "\<dots> = zorder g 0"
      unfolding shift_eq by simp
    also have "\<dots> = int (subdegree F)"
      by (rule ord0)
    finally show ?thesis .
  qed
  have r_eq: "nat (zorder f z) = subdegree F"
    using ord by simp
  have coeff_nz: "fps_nth F (nat (zorder f z)) \<noteq> 0"
    unfolding r_eq using F_nz by simp
  have coeff_eq0: "fps_nth F (nat (zorder f z)) =
      ((deriv ^^ nat (zorder f z)) g) 0 / fact (nat (zorder f z))"
    by (rule fps_nth_fps_expansion[OF fps])
  have deriv_shift0: "((deriv ^^ nat (zorder f z)) f) z =
      ((deriv ^^ nat (zorder f z)) g) 0"
    unfolding g_def by (rule higher_deriv_shift_0)
  have deriv_shift: "((deriv ^^ nat (zorder f z)) g) 0 =
      ((deriv ^^ nat (zorder f z)) f) z"
    using deriv_shift0 by simp
  have coeff_eq: "fps_nth F (nat (zorder f z)) =
      ((deriv ^^ nat (zorder f z)) f) z / fact (nat (zorder f z))"
    using coeff_eq0 deriv_shift by simp
  show ?thesis
    using coeff_nz coeff_eq by simp
qed

section \<open>Choosing a Minimal Order Point\<close>

definition gs_order_nodes :: "nat \<Rightarrow> complex set"
  where "gs_order_nodes m = of_nat ` {1..m}"

lemma finite_arg_min_on_zorder:
  assumes fin: "finite S"
  assumes ne: "S \<noteq> {}"
  shows "arg_min_on (zorder f) S \<in> S"
    and "\<And>z. z \<in> S \<Longrightarrow> zorder f (arg_min_on (zorder f) S) \<le> zorder f z"
  using assms
  by (auto intro: arg_min_if_finite arg_min_least)

lemma finite_gs_order_nodes [simp]: "finite (gs_order_nodes m)"
  unfolding gs_order_nodes_def by simp

lemma gs_order_nodes_nonempty [simp]: "m > 0 \<Longrightarrow> gs_order_nodes m \<noteq> {}"
  unfolding gs_order_nodes_def by auto

lemma mem_gs_order_nodes_iff:
  "z \<in> gs_order_nodes m \<longleftrightarrow> (\<exists>l<m. z = of_nat (Suc l))"
  unfolding gs_order_nodes_def
proof
  assume "z \<in> of_nat ` {1..m}"
  then obtain n where n: "n \<in> {1..m}" "z = of_nat n"
    by blast
  from n have "n > 0" and "n \<le> m"
    by auto
  then have "n - 1 < m"
    by auto
  moreover from n \<open>n > 0\<close> have "z = of_nat (Suc (n - 1))"
    by simp
  ultimately show "\<exists>l<m. z = of_nat (Suc l)"
    by blast
next
  assume "\<exists>l<m. z = of_nat (Suc l)"
  then obtain l where l: "l < m" "z = of_nat (Suc l)"
    by blast
  have "Suc l \<in> {1..m}"
    using l by auto
  with l show "z \<in> of_nat ` {1..m}"
    by blast
qed

lemma gs_aux_fun_arg_min_on_nodes:
  assumes mpos: "m > 0"
  shows "arg_min_on (zorder (gs_aux_fun d q \<eta>)) (gs_order_nodes m) \<in> gs_order_nodes m"
    and "\<And>z. z \<in> gs_order_nodes m \<Longrightarrow>
      zorder (gs_aux_fun d q \<eta>)
        (arg_min_on (zorder (gs_aux_fun d q \<eta>)) (gs_order_nodes m))
      \<le> zorder (gs_aux_fun d q \<eta>) z"
  by (rule finite_arg_min_on_zorder; simp add: mpos)+

lemma gs_circle_node_distance_lower_bound:
  fixes z :: complex
  assumes qpos: "q > 0"
  assumes um: "u \<le> m"
  assumes circle: "cmod z = of_nat m * (1 + of_nat r / of_nat q)"
  shows "of_nat m * of_nat r / of_nat q \<le> cmod (z - of_nat u)"
proof -
  have rad_eq: "of_nat m * of_nat r / of_nat q = cmod z - of_nat m"
    by (simp add: circle algebra_simps)
  have "cmod z - of_nat m \<le> cmod z - of_nat u"
    using um by simp
  also have "... \<le> cmod (z - of_nat u)"
    using norm_triangle_ineq2[of z "of_nat u :: complex"] by simp
  finally show ?thesis
    by (simp add: rad_eq)
qed

lemma gs_circle_maximum_modulus:
  fixes f :: "complex \<Rightarrow> complex"
  assumes Rpos: "R > 0"
  assumes hol: "f holomorphic_on cball 0 R"
  assumes bnd: "\<And>z. cmod z = R \<Longrightarrow> cmod (f z) \<le> B"
  assumes w: "cmod w < R"
  shows "cmod (f w) \<le> B"
proof (rule maximum_modulus_frontier[where f = f and S = "cball 0 R" and \<xi> = w])
  show "f holomorphic_on interior (cball 0 R)"
    using hol by (rule holomorphic_on_subset) auto
  show "continuous_on (closure (cball 0 R)) f"
    using hol Rpos by (simp add: holomorphic_on_imp_continuous_on)
  show "bounded (cball 0 R)"
    by simp
  show "\<And>z. z \<in> frontier (cball 0 R) \<Longrightarrow> cmod (f z) \<le> B"
    using bnd Rpos by (simp add: frontier_cball)
  show "w \<in> cball 0 R"
    using w by simp
qed

lemma gs_entire_quotient_of_zorder:
  fixes f :: "complex \<Rightarrow> complex"
  assumes hol: "f holomorphic_on UNIV"
  assumes nz: "\<exists>w. f w \<noteq> 0"
  assumes ord: "n \<le> nat (zorder f a)"
  obtains g where "g holomorphic_on UNIV"
    and "\<And>w. w \<noteq> a \<Longrightarrow> g w = f w / (w - a) ^ n"
proof -
  let ?k = "nat (zorder f a)"
  let ?h = "zor_poly f a"
  obtain rad where radpos: "rad > 0"
    and hhol: "?h holomorphic_on cball a rad"
    and fac: "\<forall>w\<in>cball a rad. f w = ?h w * (w - a) ^ ?k"
    using zorder_exist_zero[where f = f and z = a and S = UNIV] hol nz by auto
  define eps where "eps = min rad 1"
  have epspos: "eps > 0"
    using radpos by (simp add: eps_def)
  have epsrad: "eps \<le> rad" and epsone: "eps \<le> 1"
    by (simp_all add: eps_def)
  have hhol_eps: "?h holomorphic_on cball a eps"
    by (rule holomorphic_on_subset[OF hhol]) (use epsrad in auto)
  have hcont: "continuous_on (cball a eps) ?h"
    by (rule holomorphic_on_imp_continuous_on[OF hhol_eps])
  have hbdd: "bounded (?h ` cball a eps)"
  proof -
    have "compact (?h ` cball a eps)"
      by (rule compact_continuous_image[OF hcont]) simp
    then show ?thesis
      by (rule compact_imp_bounded)
  qed
  obtain B where B: "\<And>w. w \<in> cball a eps \<Longrightarrow> cmod (?h w) \<le> B"
    using hbdd unfolding bounded_iff by blast
  have Ba: "cmod (?h a) \<le> B"
    by (rule B) (use epspos in auto)
  have Bnonneg: "0 \<le> B"
    using Ba by (meson norm_ge_zero order_trans)
  let ?F = "\<lambda>w. f w / (w - a) ^ n"
  have Fhol: "?F holomorphic_on UNIV - {a}"
    using hol by (intro holomorphic_intros) auto
  have Fbnd: "\<exists>C. eventually (\<lambda>w. cmod (?F w) \<le> C) (at a)"
  proof (intro exI[of _ B])
    have evpun: "eventually (\<lambda>w. w \<in> ball a eps - {a}) (at a)"
      using epspos eventually_at_ball'[of eps a UNIV] by auto
    from evpun show "eventually (\<lambda>w. cmod (?F w) \<le> B) (at a)"
    proof eventually_elim
      fix w
      assume wpun: "w \<in> ball a eps - {a}"
      have wb: "w \<in> ball a eps" and wa: "w \<noteq> a"
        using wpun by auto
      have wbig: "w \<in> cball a rad"
        using wb epsrad by auto
      have poweq: "(w - a) ^ ?k / (w - a) ^ n = (w - a) ^ (?k - n)"
        using power_diff[of "w - a" n ?k] ord wa by simp
      have feq: "?F w = ?h w * (w - a) ^ (?k - n)"
        using fac[rule_format, OF wbig] poweq
        by (simp add: times_divide_eq_right[symmetric])
      have base: "cmod (w - a) \<le> (1::real)"
        using wb epsone by (auto simp: dist_norm norm_minus_commute)
      have wpow: "cmod (w - a) ^ (?k - n) \<le> (1::real)"
        by (rule power_le_one) (use base in auto)
      have hw: "cmod (?h w) \<le> B"
        using B[of w] wb by auto
      have "cmod (?F w) = cmod (?h w) * cmod (w - a) ^ (?k - n)"
        by (simp add: feq norm_mult norm_power)
      also have "... \<le> B * 1"
        using hw wpow Bnonneg by (intro mult_mono) auto
      finally show "cmod (?F w) \<le> B"
        by simp
    qed
  qed
  have aint: "a \<in> interior UNIV"
    by simp
  obtain g where ghol: "g holomorphic_on UNIV"
    and geq: "\<forall>w\<in>UNIV - {a}. g w = ?F w"
    using holomorphic_on_extend_bounded[OF Fhol aint] Fbnd by auto
  show thesis
    by (rule that[OF ghol]) (use geq in auto)
qed

lemma gs_entire_extend_finite_local:
  fixes F :: "complex \<Rightarrow> complex"
  assumes fin: "finite X"
  assumes hol: "F holomorphic_on UNIV - X"
  assumes local: "\<And>a. a \<in> X \<Longrightarrow>
    \<exists>h. continuous (at a) h \<and> eventually (\<lambda>w. F w = h w) (at a)"
  obtains G where "G holomorphic_on UNIV"
    and "\<And>w. w \<notin> X \<Longrightarrow> G w = F w"
proof -
  have ex: "\<exists>G. G holomorphic_on UNIV \<and> (\<forall>w\<in>UNIV - X. G w = F w)"
  proof (rule removable_singularities[where X = X and S = UNIV and f = F])
    show "finite X"
      by (rule fin)
    show "X \<subseteq> interior UNIV"
      by simp
    show "F holomorphic_on UNIV - X"
      by (rule hol)
    fix a
    assume aX: "a \<in> X"
    obtain h where hc: "continuous (at a) h"
      and eq: "eventually (\<lambda>w. F w = h w) (at a)"
      using local[OF aX] by blast
    have hO: "h \<in> O[at a](\<lambda>_. 1)"
      using continuous_imp_bigo_1[OF hc] by simp
    have FTheta: "F \<in> \<Theta>[at a](h)"
      by (rule bigthetaI_cong[OF eq])
    show "F \<in> O[at a](\<lambda>_. 1)"
      by (rule landau_o.big.bigtheta_trans2[OF FTheta hO])
  qed
  then obtain G where Ghol: "G holomorphic_on UNIV"
    and Geq: "\<forall>w\<in>UNIV - X. G w = F w"
    by blast
  show thesis
    by (rule that[OF Ghol]) (use Geq in auto)
qed

lemma gs_entire_quotient_of_finite_zeros:
  fixes f :: "complex \<Rightarrow> complex"
  assumes fin: "finite X"
  assumes hol: "f holomorphic_on UNIV"
  assumes nz: "\<exists>w. f w \<noteq> 0"
  assumes ord: "\<And>a. a \<in> X \<Longrightarrow> n \<le> nat (zorder f a)"
  obtains G where "G holomorphic_on UNIV"
    and "\<And>w. w \<notin> X \<Longrightarrow>
      G w = f w / (\<Prod>a\<in>X. (w - a) ^ n)"
proof -
  let ?P = "\<lambda>w. \<Prod>a\<in>X. (w - a) ^ n"
  let ?F = "\<lambda>w. f w / ?P w"
  have Phol: "?P holomorphic_on UNIV - X"
    by (intro holomorphic_intros)
  have Pnz: "\<And>w. w \<notin> X \<Longrightarrow> ?P w \<noteq> 0"
    by (intro prod_nonzeroI) auto
  have Fhol: "?F holomorphic_on UNIV - X"
    by (intro holomorphic_intros Phol holomorphic_on_subset[OF hol])
       (use Pnz in auto)
  have local: "\<And>a. a \<in> X \<Longrightarrow>
    \<exists>h. continuous (at a) h \<and> eventually (\<lambda>w. ?F w = h w) (at a)"
  proof -
    fix a
    assume aX: "a \<in> X"
    obtain Q where Qhol: "Q holomorphic_on UNIV"
      and Qeq: "\<And>w. w \<noteq> a \<Longrightarrow> Q w = f w / (w - a) ^ n"
      using gs_entire_quotient_of_zorder[OF hol nz ord[OF aX]] by blast
    let ?Pa = "\<lambda>w. \<Prod>b\<in>X - {a}. (w - b) ^ n"
    have PaHol: "?Pa holomorphic_on UNIV"
      by (intro holomorphic_intros)
    have PaNe: "?Pa a \<noteq> 0"
      by (intro prod_nonzeroI) auto
    have Qcont: "continuous (at a) Q"
      using holomorphic_on_imp_continuous_on[OF Qhol]
      by (simp add: continuous_on_eq_continuous_at)
    have Pacont: "continuous (at a) ?Pa"
      using holomorphic_on_imp_continuous_on[OF PaHol]
      by (simp add: continuous_on_eq_continuous_at)
    have Hcont: "continuous (at a) (\<lambda>w. Q w / ?Pa w)"
      using Qcont Pacont PaNe by (intro continuous_intros) auto
    have Uopen: "open (UNIV - (X - {a}))"
    proof -
      have "closed (X - {a})"
        using fin by (intro finite_imp_closed) auto
      then show ?thesis by (rule open_Diff[OF open_UNIV])
    qed
    have aU: "a \<in> UNIV - (X - {a})"
      by simp
    have evU: "eventually (\<lambda>w. w \<notin> X - {a}) (at a)"
      using eventually_nhds_in_open[OF Uopen aU]
      by (auto simp: eventually_at_filter elim: eventually_mono)
    have evne: "eventually (\<lambda>w. w \<noteq> a) (at a)"
      by (auto simp: eventually_at_filter elim: eventually_mono)
    have ev: "eventually (\<lambda>w. w \<noteq> a \<and> w \<notin> X - {a}) (at a)"
      using evU evne by (simp add: eventually_conj_iff)
    have Fev: "eventually (\<lambda>w. ?F w = Q w / ?Pa w) (at a)"
    proof (rule eventually_mono[OF ev])
      fix w
      assume w: "w \<noteq> a \<and> w \<notin> X - {a}"
      have split: "?P w = (w - a) ^ n * ?Pa w"
        using fin aX by (simp add: prod.remove)
      have wne: "w \<noteq> a" using w by simp
      show "?F w = Q w / ?Pa w"
        by (simp add: split Qeq[OF wne] divide_divide_eq_left)
    qed
    show "\<exists>h. continuous (at a) h \<and> eventually (\<lambda>w. ?F w = h w) (at a)"
      using Hcont Fev by blast
  qed
  obtain G where Ghol: "G holomorphic_on UNIV"
    and Geq: "\<And>w. w \<notin> X \<Longrightarrow> G w = ?F w"
    using gs_entire_extend_finite_local[OF fin Fhol local] by blast
  show thesis
    by (rule that[OF Ghol]) (use Geq in auto)
qed

lemma gs_node_product_lower_bound_on_circle:
  fixes z :: complex
  assumes qpos: "q > 0"
  assumes mpos: "m > 0"
  assumes rpos: "r > 0"
  assumes circle: "cmod z = of_nat m * (1 + of_nat r / of_nat q)"
  shows "(of_nat m * of_nat r / of_nat q) ^ (m * n) \<le>
    cmod (\<Prod>a\<in>gs_order_nodes m. (z - a) ^ n)"
proof -
  let ?X = "gs_order_nodes m"
  let ?d = "of_nat m * of_nat r / of_nat q :: real"
  have dpos: "?d > 0"
    using qpos mpos rpos by simp
  have cardX: "card ?X = m"
    by (simp add: gs_order_nodes_def card_image inj_on_def)
  have each: "\<And>a. a \<in> ?X \<Longrightarrow> ?d \<le> cmod (z - a)"
  proof -
    fix a
    assume "a \<in> ?X"
    then obtain j where jlt: "j < m" and aeq: "a = of_nat (Suc j)"
      using mem_gs_order_nodes_iff by blast
    have ule: "Suc j \<le> m"
      using jlt by simp
    show "?d \<le> cmod (z - a)"
      using gs_circle_node_distance_lower_bound[OF qpos ule circle]
      by (simp add: aeq)
  qed
  have each_power: "\<And>a. a \<in> ?X \<Longrightarrow> ?d ^ n \<le> cmod (z - a) ^ n"
    by (rule power_mono) (use each dpos in auto)
  have "?d ^ (m * n) = (\<Prod>a\<in>?X. ?d ^ n)"
    by (simp add: cardX power_mult[symmetric] mult.commute)
  also have "... \<le> (\<Prod>a\<in>?X. cmod (z - a) ^ n)"
    by (intro prod_mono) (use each_power dpos in auto)
  also have "... = cmod (\<Prod>a\<in>?X. (z - a) ^ n)"
    by (simp add: prod_norm[symmetric] norm_power)
  finally show ?thesis
    by (simp add: mult.commute)
qed

end
