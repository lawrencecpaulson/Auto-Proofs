(*  Title:      Gelfond_Schneider/Gelfond_Schneider_Vanishing.thy
    Author:     OpenAI Codex

Abstract vanishing-order consequences of a solution to the indexed
Gelfond-Schneider linear system. This ports the Lean `MainOrder` /
`MainAnalytic` bridge at the level of an arbitrary nonzero coefficient vector:
once the first `n` derivative constraints hold at each interpolation node,
the auxiliary function has zorder at least `n` there, and one can choose a
node of minimal order among `1, ..., m`.
*)

theory Gelfond_Schneider_Vanishing
  imports
    Gelfond_Schneider_System
    Gelfond_Schneider_Order
begin

section \<open>Vanishing at the Interpolation Nodes\<close>

lemma gs_aux_fun_vec_holomorphic [holomorphic_intros]:
  "(gs_aux_fun_vec d q \<xi>) holomorphic_on A"
  unfolding gs_aux_fun_vec_def
  by (rule finite_exp_sum_holomorphic) simp

lemma gs_k_idx_mul_add [simp]:
  assumes npos: "n > 0"
  assumes klt: "k < n"
  shows "gs_k_idx n (l * n + k) = k"
  unfolding gs_k_idx_def using assms by simp

lemma gs_l_idx_mul_add [simp]:
  assumes npos: "n > 0"
  assumes klt: "k < n"
  shows "gs_l_idx n (l * n + k) = Suc l"
  unfolding gs_l_idx_def using assms by simp

lemma gs_aux_fun_vec_deriv_vanish_at_node:
  assumes d: "is_gelfond_schneider_data d"
  assumes npos: "n > 0"
  assumes sys0: "\<And>u. u < m * n \<Longrightarrow> (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
  assumes llt: "l < m"
  assumes klt: "k < n"
  shows "((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat (Suc l)) = 0"
proof -
  let ?u = "l * n + k"
  have ult: "?u < m * n"
  proof -
    have "l * n + k < l * n + n"
      using klt by simp
    also have "\<dots> = Suc l * n"
      by simp
    also have "\<dots> \<le> m * n"
    proof -
      have sl_le_m: "Suc l \<le> m"
        using llt by simp
      show ?thesis
        using mult_right_mono[OF sl_le_m, of n] by simp
    qed
    finally show ?thesis .
  qed
  have "((deriv ^^ gs_k_idx n ?u) (gs_aux_fun_vec d q \<xi>)) (of_nat (gs_l_idx n ?u)) = 0"
    by (rule gs_aux_fun_vec_deriv_at_node_eq_zeroI[OF d]) (rule sys0[OF ult])
  then show ?thesis
    using npos klt by simp
qed

lemma gs_aux_fun_vec_zorder_ge_at_node:
  assumes nz: "gs_aux_fun_vec d q \<xi> \<noteq> (\<lambda>_. 0)"
  assumes d: "is_gelfond_schneider_data d"
  assumes npos: "n > 0"
  assumes sys0: "\<And>u. u < m * n \<Longrightarrow> (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
  assumes llt: "l < m"
  shows "zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc l)) \<ge> n"
proof (rule holomorphic_nonzero_zorder_ge[OF gs_aux_fun_vec_holomorphic[of d q \<xi> UNIV] nz])
  fix k
  assume klt: "k < n"
  show "((deriv ^^ k) (gs_aux_fun_vec d q \<xi>)) (of_nat (Suc l)) = 0"
    by (rule gs_aux_fun_vec_deriv_vanish_at_node[OF d npos sys0 llt klt])
qed

corollary gs_aux_fun_vec_zorder_ge_at_node_of_coeff_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes npos: "n > 0"
  assumes coeff_nz: "\<exists>t<q * q. \<xi> t \<noteq> 0"
  assumes sys0: "\<And>u. u < m * n \<Longrightarrow> (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
  assumes llt: "l < m"
  shows "zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc l)) \<ge> n"
proof -
  have nz: "gs_aux_fun_vec d q \<xi> \<noteq> (\<lambda>_. 0)"
    by (rule gs_aux_fun_vec_nonzero[OF d qpos coeff_nz])
  show ?thesis
    by (rule gs_aux_fun_vec_zorder_ge_at_node[OF nz d npos sys0 llt])
qed

section \<open>Choosing a Minimal-Order Node\<close>

definition gs_min_order_node ::
  "nat \<Rightarrow> gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> complex"
  where
    "gs_min_order_node m d q \<xi> =
      arg_min_on (zorder (gs_aux_fun_vec d q \<xi>)) (gs_order_nodes m)"

definition gs_min_order ::
  "nat \<Rightarrow> gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> int"
  where
    "gs_min_order m d q \<xi> =
      zorder (gs_aux_fun_vec d q \<xi>) (gs_min_order_node m d q \<xi>)"

lemma gs_aux_fun_vec_exists_min_order_node:
  assumes mpos: "m > 0"
  obtains l
    where "l < m"
      and "\<And>j. j < m \<Longrightarrow>
        zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc l))
          \<le> zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc j))"
proof -
  define z0 where "z0 = arg_min_on (zorder (gs_aux_fun_vec d q \<xi>)) (gs_order_nodes m)"
  have z0_mem: "z0 \<in> gs_order_nodes m"
    unfolding z0_def
    by (rule finite_arg_min_on_zorder(1)) (simp_all add: mpos)
  then obtain l where l: "l < m" "z0 = of_nat (Suc l)"
    using mem_gs_order_nodes_iff by blast
  have z0_min: "\<And>z. z \<in> gs_order_nodes m \<Longrightarrow>
      zorder (gs_aux_fun_vec d q \<xi>) z0 \<le> zorder (gs_aux_fun_vec d q \<xi>) z"
    unfolding z0_def
    by (rule finite_arg_min_on_zorder(2)) (simp_all add: mpos)
  have z0_min_nat: "\<And>j. j < m \<Longrightarrow>
      zorder (gs_aux_fun_vec d q \<xi>) z0 \<le> zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc j))"
  proof -
    fix j
    assume jlt: "j < m"
    have "Suc j \<in> {1..m}"
      using jlt by auto
    then have "of_nat (Suc j) \<in> gs_order_nodes m"
      unfolding gs_order_nodes_def by blast
    then show "zorder (gs_aux_fun_vec d q \<xi>) z0 \<le> zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc j))"
      by (rule z0_min)
  qed
  show thesis
    by (rule that[OF l(1)]) (use l z0_min_nat in simp_all)
qed

lemma gs_min_order_node_mem:
  assumes mpos: "m > 0"
  shows "gs_min_order_node m d q \<xi> \<in> gs_order_nodes m"
  unfolding gs_min_order_node_def
  by (rule finite_arg_min_on_zorder(1)) (simp_all add: mpos)

lemma gs_min_order_node_eq_nat:
  assumes mpos: "m > 0"
  obtains l where "l < m" and "gs_min_order_node m d q \<xi> = of_nat (Suc l)"
proof -
  have "gs_min_order_node m d q \<xi> \<in> gs_order_nodes m"
    by (rule gs_min_order_node_mem[OF mpos])
  then obtain l where "l < m" "gs_min_order_node m d q \<xi> = of_nat (Suc l)"
    using mem_gs_order_nodes_iff by blast
  then show thesis
    by (rule that)
qed

lemma gs_min_order_node_le:
  assumes mpos: "m > 0"
  assumes jlt: "j < m"
  shows "zorder (gs_aux_fun_vec d q \<xi>) (gs_min_order_node m d q \<xi>)
    \<le> zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc j))"
proof -
  have suc_mem: "Suc j \<in> {1..m}"
    using jlt by simp
  have node_mem: "of_nat (Suc j) \<in> gs_order_nodes m"
    using suc_mem unfolding gs_order_nodes_def by blast
  show ?thesis
    unfolding gs_min_order_node_def
  proof (rule finite_arg_min_on_zorder(2))
    show "finite (gs_order_nodes m)"
      by simp
    show "gs_order_nodes m \<noteq> {}"
      using mpos by simp
    show "of_nat (Suc j) \<in> gs_order_nodes m"
      by (rule node_mem)
  qed
qed

lemma gs_min_order_ge:
  assumes nz: "gs_aux_fun_vec d q \<xi> \<noteq> (\<lambda>_. 0)"
  assumes d: "is_gelfond_schneider_data d"
  assumes mpos: "m > 0"
  assumes npos: "n > 0"
  assumes sys0: "\<And>u. u < m * n \<Longrightarrow> (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
  shows "gs_min_order m d q \<xi> \<ge> n"
proof -
  obtain l where llt: "l < m" and node: "gs_min_order_node m d q \<xi> = of_nat (Suc l)"
    by (rule gs_min_order_node_eq_nat[OF mpos])
  have "zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc l)) \<ge> n"
    by (rule gs_aux_fun_vec_zorder_ge_at_node[OF nz d npos sys0 llt])
  then show ?thesis
    unfolding gs_min_order_def using node by simp
qed

lemma gs_min_order_deriv_nonzero:
  assumes nz: "gs_aux_fun_vec d q \<xi> \<noteq> (\<lambda>_. 0)"
  shows "((deriv ^^ nat (gs_min_order m d q \<xi>)) (gs_aux_fun_vec d q \<xi>))
    (gs_min_order_node m d q \<xi>) \<noteq> 0"
proof -
  have "((deriv ^^ nat (zorder (gs_aux_fun_vec d q \<xi>) (gs_min_order_node m d q \<xi>)))
      (gs_aux_fun_vec d q \<xi>)) (gs_min_order_node m d q \<xi>) \<noteq> 0"
    by (rule holomorphic_nonzero_deriv_zorder_nonzero[OF gs_aux_fun_vec_holomorphic nz])
  then show ?thesis
    unfolding gs_min_order_def by simp
qed

corollary gs_min_order_ge_of_coeff_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes mpos: "m > 0"
  assumes npos: "n > 0"
  assumes coeff_nz: "\<exists>t<q * q. \<xi> t \<noteq> 0"
  assumes sys0: "\<And>u. u < m * n \<Longrightarrow> (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
  shows "gs_min_order m d q \<xi> \<ge> n"
proof -
  have nz: "gs_aux_fun_vec d q \<xi> \<noteq> (\<lambda>_. 0)"
    by (rule gs_aux_fun_vec_nonzero[OF d qpos coeff_nz])
  show ?thesis
    by (rule gs_min_order_ge[OF nz d mpos npos sys0])
qed

corollary gs_min_order_deriv_nonzero_of_coeff_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes coeff_nz: "\<exists>t<q * q. \<xi> t \<noteq> 0"
  shows "((deriv ^^ nat (gs_min_order m d q \<xi>)) (gs_aux_fun_vec d q \<xi>))
    (gs_min_order_node m d q \<xi>) \<noteq> 0"
proof -
  have nz: "gs_aux_fun_vec d q \<xi> \<noteq> (\<lambda>_. 0)"
    by (rule gs_aux_fun_vec_nonzero[OF d qpos coeff_nz])
  show ?thesis
    by (rule gs_min_order_deriv_nonzero[OF nz])
qed

lemma gs_aux_fun_vec_exists_min_order_node_ge:
  assumes nz: "gs_aux_fun_vec d q \<xi> \<noteq> (\<lambda>_. 0)"
  assumes d: "is_gelfond_schneider_data d"
  assumes mpos: "m > 0"
  assumes npos: "n > 0"
  assumes sys0: "\<And>u. u < m * n \<Longrightarrow> (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
  obtains l
    where "l < m"
      and "\<And>j. j < m \<Longrightarrow>
        zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc l))
          \<le> zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc j))"
      and "zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc l)) \<ge> n"
proof -
  obtain l where llt: "l < m"
    and lmin: "\<And>j. j < m \<Longrightarrow>
        zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc l))
          \<le> zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc j))"
    using gs_aux_fun_vec_exists_min_order_node[of m d q \<xi>] mpos by blast
  have lbound: "zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc l)) \<ge> n"
    by (rule gs_aux_fun_vec_zorder_ge_at_node[OF nz d npos sys0 llt])
  show thesis
    by (rule that[OF llt lmin lbound])
qed

corollary gs_aux_fun_vec_exists_min_order_node_ge_of_coeff_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  assumes qpos: "q > 0"
  assumes mpos: "m > 0"
  assumes npos: "n > 0"
  assumes coeff_nz: "\<exists>t<q * q. \<xi> t \<noteq> 0"
  assumes sys0: "\<And>u. u < m * n \<Longrightarrow> (\<Sum>t<q * q. \<xi> t * gs_system_coeff_idx d n q u t) = 0"
  obtains l
    where "l < m"
      and "\<And>j. j < m \<Longrightarrow>
        zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc l))
          \<le> zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc j))"
      and "zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc l)) \<ge> n"
proof -
  have nz: "gs_aux_fun_vec d q \<xi> \<noteq> (\<lambda>_. 0)"
    by (rule gs_aux_fun_vec_nonzero[OF d qpos coeff_nz])
  show thesis
  proof (rule gs_aux_fun_vec_exists_min_order_node_ge[OF nz d mpos npos sys0])
    fix l
    assume llt: "l < m"
    assume lmin: "\<And>j. j < m \<Longrightarrow>
        zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc l))
          \<le> zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc j))"
    assume lbound: "zorder (gs_aux_fun_vec d q \<xi>) (of_nat (Suc l)) \<ge> n"
    show thesis
      by (rule that[OF llt lmin lbound])
  qed
qed

lemma gs_aux_fun_vec_entire_normalized:
  assumes mpos: "m > 0"
  assumes nz: "gs_aux_fun_vec d q \<xi> \<noteq> (\<lambda>_. 0)"
  obtains S where "S holomorphic_on UNIV"
    and "\<And>w. w \<notin> gs_order_nodes m \<Longrightarrow>
      S w = gs_aux_fun_vec d q \<xi> w /
        (\<Prod>a\<in>gs_order_nodes m. (w - a) ^ nat (gs_min_order m d q \<xi>))"
proof -
  let ?f = "gs_aux_fun_vec d q \<xi>"
  have fhol: "?f holomorphic_on UNIV"
    by (rule gs_aux_fun_vec_holomorphic)
  have fnz: "\<exists>w. ?f w \<noteq> 0"
    using nz by (auto simp: fun_eq_iff)
  have ord: "\<And>a. a \<in> gs_order_nodes m \<Longrightarrow>
      nat (gs_min_order m d q \<xi>) \<le> nat (zorder ?f a)"
  proof -
    fix a
    assume a: "a \<in> gs_order_nodes m"
    obtain j where jlt: "j < m" and aeq: "a = of_nat (Suc j)"
      using a mem_gs_order_nodes_iff by blast
    have "gs_min_order m d q \<xi> \<le> zorder ?f a"
      using gs_min_order_node_le[OF mpos jlt, of d q \<xi>]
      unfolding gs_min_order_def by (simp add: aeq)
    then show "nat (gs_min_order m d q \<xi>) \<le> nat (zorder ?f a)"
      by (rule nat_mono)
  qed
  have fin: "finite (gs_order_nodes m)" by simp
  obtain S where Shol: "S holomorphic_on UNIV"
    and Seq: "\<And>w. w \<notin> gs_order_nodes m \<Longrightarrow>
      S w = ?f w / (\<Prod>a\<in>gs_order_nodes m. (w - a) ^ nat (gs_min_order m d q \<xi>))"
    using gs_entire_quotient_of_finite_zeros[OF fin fhol fnz ord] by blast
  show thesis
    by (rule that[OF Shol]) (use Seq in auto)
qed

lemma gs_aux_fun_vec_cmod_le_uniform_exp:
  fixes V T R :: real
  assumes Vnonneg: "0 \<le> V"
  assumes Tnonneg: "0 \<le> T"
  assumes coeff: "\<And>t. t < q * q \<Longrightarrow> cmod (\<xi> t) \<le> V"
  assumes rho: "\<And>t. t < q * q \<Longrightarrow> cmod (gs_rho_idx d q t) \<le> T"
  assumes wbnd: "cmod w \<le> R"
  shows "cmod (gs_aux_fun_vec d q \<xi> w) \<le> of_nat (q * q) * V * exp (T * R)"
proof -
  have exp_bnd: "cmod (exp (gs_rho_idx d q t * w)) \<le> exp (T * R)"
    if tlt: "t < q * q" for t
  proof -
    have mult_bnd: "cmod (gs_rho_idx d q t * w) \<le> T * R"
      using rho[OF tlt] wbnd Tnonneg
      by (simp add: norm_mult; intro mult_mono; auto)
    have re_bnd: "Re (gs_rho_idx d q t * w) \<le> T * R"
      using complex_Re_le_cmod[of "gs_rho_idx d q t * w"] mult_bnd by linarith
    show ?thesis
      using re_bnd by (simp add: norm_exp_eq_Re)
  qed
  have term_bnd: "cmod (\<xi> t * exp (gs_rho_idx d q t * w)) \<le> V * exp (T * R)"
    if tlt: "t < q * q" for t
  proof -
    have "cmod (\<xi> t * exp (gs_rho_idx d q t * w)) =
        cmod (\<xi> t) * cmod (exp (gs_rho_idx d q t * w))"
      by (simp add: norm_mult)
    also have "... \<le> V * exp (T * R)"
      using coeff[OF tlt] exp_bnd[OF tlt] Vnonneg
      by (intro mult_mono) auto
    finally show ?thesis .
  qed
  have "cmod (gs_aux_fun_vec d q \<xi> w) \<le>
      (\<Sum>t<q * q. cmod (\<xi> t * exp (gs_rho_idx d q t * w)))"
    unfolding gs_aux_fun_vec_def by (rule sum_norm_le) simp
  also have "... \<le> (\<Sum>t<q * q. V * exp (T * R))"
    by (intro sum_mono term_bnd) auto
  also have "... = of_nat (q * q) * V * exp (T * R)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma gs_normalized_circle_bound:
  fixes f S :: "complex \<Rightarrow> complex"
  fixes M :: real
  assumes qpos: "q > 0"
  assumes mpos: "m > 0"
  assumes rpos: "r > 0"
  assumes Mnonneg: "0 \<le> M"
  assumes Shol: "S holomorphic_on UNIV"
  assumes Seq: "\<And>z. z \<notin> gs_order_nodes m \<Longrightarrow>
    S z = f z / (\<Prod>a\<in>gs_order_nodes m. (z - a) ^ n)"
  assumes fbnd: "\<And>z. cmod z = of_nat m * (1 + of_nat r / of_nat q) \<Longrightarrow>
    cmod (f z) \<le> M"
  assumes w: "cmod w < of_nat m * (1 + of_nat r / of_nat q)"
  shows "cmod (S w) \<le> M / (of_nat m * of_nat r / of_nat q) ^ (m * n)"
proof -
  let ?R = "of_nat m * (1 + of_nat r / of_nat q) :: real"
  let ?d = "of_nat m * of_nat r / of_nat q :: real"
  have dpos: "?d > 0"
    using qpos mpos rpos by simp
  have Rgt: "?R > of_nat m"
    using dpos by (simp add: algebra_simps)
  have bnd: "cmod (S z) \<le> M / ?d ^ (m * n)" if zcircle: "cmod z = ?R" for z
  proof -
    have zout: "z \<notin> gs_order_nodes m"
    proof
      assume "z \<in> gs_order_nodes m"
      then obtain j where jlt: "j < m" and zeq: "z = of_nat (Suc j)"
        using mem_gs_order_nodes_iff by blast
      have "cmod z \<le> of_nat m"
        using jlt by (simp only: zeq norm_of_nat of_nat_le_iff; linarith)
      with zcircle Rgt show False by linarith
    qed
    let ?P = "\<Prod>a\<in>gs_order_nodes m. (z - a) ^ n"
    have Plo: "?d ^ (m * n) \<le> cmod ?P"
      by (rule gs_node_product_lower_bound_on_circle[OF qpos mpos rpos zcircle])
    have dlo: "?d ^ (m * n) > 0"
      using dpos by simp
    have Ppos: "cmod ?P > 0"
      using Plo dlo by linarith
    have "cmod (S z) = cmod (f z) / cmod ?P"
      by (simp add: Seq[OF zout] norm_divide)
    also have "... \<le> M / ?d ^ (m * n)"
      using fbnd[OF zcircle] Plo Ppos dpos Mnonneg
      by (intro frac_le) auto
    finally show ?thesis .
  qed
  have Rpos: "?R > 0"
    using Rgt mpos by simp
  have hol: "S holomorphic_on cball 0 ?R"
    by (rule holomorphic_on_subset[OF Shol]) auto
  show ?thesis
    by (rule gs_circle_maximum_modulus[OF Rpos hol bnd w])
qed

lemma gs_normalized_product_identity:
  fixes f S :: "complex \<Rightarrow> complex"
  assumes fhol: "f holomorphic_on UNIV"
  assumes Shol: "S holomorphic_on UNIV"
  assumes Seq: "\<And>z. z \<notin> gs_order_nodes m \<Longrightarrow>
    S z = f z / (\<Prod>a\<in>gs_order_nodes m. (z - a) ^ n)"
  shows "f z = S z * (\<Prod>a\<in>gs_order_nodes m. (z - a) ^ n)"
proof -
  let ?X = "gs_order_nodes m"
  let ?P = "\<lambda>w. \<Prod>a\<in>?X. (w - a) ^ n"
  have Phol: "?P holomorphic_on UNIV"
    by (intro holomorphic_intros)
  have Ghol: "(\<lambda>w. S w * ?P w) holomorphic_on UNIV"
    by (intro holomorphic_intros Shol Phol)
  have away: "f w = S w * ?P w" if wout: "w \<notin> ?X" for w
  proof -
    have Pnz: "?P w \<noteq> 0"
      by (intro prod_nonzeroI) (use wout in auto)
    show ?thesis
      using Seq[OF wout] Pnz by (simp add: nonzero_eq_divide_eq mult.commute)
  qed
  show ?thesis
  proof (cases "z \<in> ?X")
    case False
    then show ?thesis by (rule away)
  next
    case True
    have Uopen: "open (UNIV - (?X - {z}))"
      by (intro open_Diff finite_imp_closed) auto
    have zU: "z \<in> UNIV - (?X - {z})"
      by simp
    have evU: "eventually (\<lambda>w. w \<notin> ?X - {z}) (at z)"
      using eventually_nhds_in_open[OF Uopen zU]
      by (auto simp: eventually_at_filter elim: eventually_mono)
    have evne: "eventually (\<lambda>w. w \<noteq> z) (at z)"
      by (auto simp: eventually_at_filter elim: eventually_mono)
    have both: "eventually (\<lambda>w. w \<notin> ?X - {z} \<and> w \<noteq> z) (at z)"
      using evU evne by (simp add: eventually_conj_iff)
    have evout: "eventually (\<lambda>w. w \<notin> ?X) (at z)"
      by (rule eventually_mono[OF both]) auto
    have ev: "eventually (\<lambda>w. f w = S w * ?P w) (at z)"
      by (rule eventually_mono[OF evout]) (use away in auto)
    have fcont: "isCont f z"
      using holomorphic_on_imp_continuous_on[OF fhol]
      by (simp add: continuous_on_eq_continuous_at)
    have limf: "(f \<longlongrightarrow> f z) (at z)"
      by (rule isContD[OF fcont])
    have Gcont: "isCont (\<lambda>w. S w * ?P w) z"
      using holomorphic_on_imp_continuous_on[OF Ghol]
      by (simp add: continuous_on_eq_continuous_at)
    have limg: "((\<lambda>w. S w * ?P w) \<longlongrightarrow> S z * ?P z) (at z)"
      by (rule isContD[OF Gcont])
    have limg': "((\<lambda>w. S w * ?P w) \<longlongrightarrow> f z) (at z)"
      using limf ev by (simp add: tendsto_cong)
    show ?thesis
      using tendsto_unique[OF _ limg' limg] by simp
  qed
qed

lemma gs_normalized_derivative_bound:
  fixes f S :: "complex \<Rightarrow> complex"
  fixes B :: real
  assumes anode: "a \<in> gs_order_nodes m"
  assumes Bnonneg: "0 \<le> B"
  assumes fhol: "f holomorphic_on UNIV"
  assumes Shol: "S holomorphic_on UNIV"
  assumes Seq: "\<And>z. z \<notin> gs_order_nodes m \<Longrightarrow>
    S z = f z / (\<Prod>b\<in>gs_order_nodes m. (z - b) ^ n)"
  assumes Sbnd: "\<And>z. cmod (z - a) = 1 \<Longrightarrow> cmod (S z) \<le> B"
  shows "cmod ((deriv ^^ n) f a) \<le>
    fact n * B * (2 * of_nat m + 1) ^ (m * n)"
proof -
  let ?X = "gs_order_nodes m"
  let ?C = "2 * of_nat m + 1 :: real"
  have apos: "cmod a \<le> of_nat m"
  proof -
    obtain j where jlt: "j < m" and aeq: "a = of_nat (Suc j)"
      using anode mem_gs_order_nodes_iff by blast
    show ?thesis
      using jlt by (simp only: aeq norm_of_nat of_nat_le_iff)
  qed
  have bpos: "cmod b \<le> of_nat m" if bX: "b \<in> ?X" for b
  proof -
    obtain j where jlt: "j < m" and beq: "b = of_nat (Suc j)"
      using bX mem_gs_order_nodes_iff by blast
    show ?thesis
      using jlt by (simp only: beq norm_of_nat of_nat_le_iff)
  qed
  have Cpos: "?C \<ge> 0" by simp
  have cardX: "card ?X = m"
    by (simp add: gs_order_nodes_def card_image inj_on_def)
  have Pbnd: "cmod (\<Prod>b\<in>?X. (z - b) ^ n) \<le> ?C ^ (m * n)"
    if zcircle: "cmod (z - a) = 1" for z
  proof -
    have each: "cmod (z - b) \<le> ?C" if bX: "b \<in> ?X" for b
    proof -
      have h1: "cmod (z - b) \<le> cmod (z - a) + cmod (a - b)"
        using norm_triangle_ineq[of "z-a" "a-b"]
        by (simp add: algebra_simps)
      have h2: "cmod (a - b) \<le> cmod a + cmod b"
        by (rule norm_triangle_ineq4)
      show ?thesis using h1 h2 apos bpos[OF bX] zcircle by linarith
    qed
    have "cmod (\<Prod>b\<in>?X. (z - b) ^ n) =
        (\<Prod>b\<in>?X. cmod (z - b) ^ n)"
      by (simp add: prod_norm[symmetric] norm_power)
    also have "... \<le> (\<Prod>b\<in>?X. ?C ^ n)"
      by (intro prod_mono) (use each in \<open>auto intro: power_mono\<close>)
    also have "... = ?C ^ (m * n)"
      by (simp add: cardX power_mult[symmetric] mult.commute)
    finally show ?thesis .
  qed
  have fbound: "cmod (f z) \<le> B * ?C ^ (m * n)"
    if zcircle: "cmod (a - z) = 1" for z
  proof -
    have zcircle': "cmod (z - a) = 1"
      using zcircle by (simp add: norm_minus_commute)
    have id: "f z = S z * (\<Prod>b\<in>?X. (z - b) ^ n)"
      by (rule gs_normalized_product_identity[OF fhol Shol Seq])
    show ?thesis
      using Sbnd[OF zcircle'] Pbnd[OF zcircle'] Bnonneg
      by (simp add: id norm_mult; intro mult_mono; auto)
  qed
  have hol: "f holomorphic_on ball a 1"
    by (rule holomorphic_on_subset[OF fhol]) auto
  have cont: "continuous_on (cball a 1) f"
    using holomorphic_on_imp_continuous_on[OF fhol] by (rule continuous_on_subset) auto
  have der: "cmod ((deriv ^^ n) f a) \<le> fact n * (B * ?C ^ (m * n)) / 1 ^ n"
    by (rule Cauchy_inequality[OF hol cont _ fbound]) simp
  show ?thesis using der by (simp add: algebra_simps)
qed

lemma gs_aux_fun_vec_min_order_derivative_bound:
  fixes V T :: real
  assumes qpos: "q > 0"
  assumes mpos: "m > 0"
  assumes rpos: "r > 0"
  assumes dgt: "1 < (of_nat m * of_nat r / of_nat q :: real)"
  assumes Vnonneg: "0 \<le> V"
  assumes Tnonneg: "0 \<le> T"
  assumes nz: "gs_aux_fun_vec d q \<xi> \<noteq> (\<lambda>_. 0)"
  assumes req: "r = nat (gs_min_order m d q \<xi>)"
  assumes coeff: "\<And>t. t < q * q \<Longrightarrow> cmod (\<xi> t) \<le> V"
  assumes rho: "\<And>t. t < q * q \<Longrightarrow> cmod (gs_rho_idx d q t) \<le> T"
  shows "cmod (((deriv ^^ r) (gs_aux_fun_vec d q \<xi>))
      (gs_min_order_node m d q \<xi>)) \<le>
    fact r * (of_nat (q * q) * V *
      exp (T * (of_nat m * (1 + of_nat r / of_nat q))) /
      (of_nat m * of_nat r / of_nat q) ^ (m * r)) *
      (2 * of_nat m + 1) ^ (m * r)"
proof -
  let ?f = "gs_aux_fun_vec d q \<xi>"
  let ?a = "gs_min_order_node m d q \<xi>"
  let ?R = "of_nat m * (1 + of_nat r / of_nat q) :: real"
  let ?d = "of_nat m * of_nat r / of_nat q :: real"
  let ?M = "of_nat (q * q) * V * exp (T * ?R)"
  let ?B = "?M / ?d ^ (m * r)"
  obtain S where Shol: "S holomorphic_on UNIV"
    and Seq: "\<And>w. w \<notin> gs_order_nodes m \<Longrightarrow>
      S w = ?f w / (\<Prod>a\<in>gs_order_nodes m. (w - a) ^ r)"
    using gs_aux_fun_vec_entire_normalized[OF mpos nz]
    by (simp add: req[symmetric]) blast
  have Mnonneg: "0 \<le> ?M"
    using Vnonneg by simp
  have Bnonneg: "0 \<le> ?B"
    using Mnonneg dgt by simp
  have fbnd: "cmod (?f z) \<le> ?M" if zcircle: "cmod z = ?R" for z
  proof -
    have wbnd: "cmod z \<le> ?R" using zcircle by simp
    show ?thesis
      by (rule gs_aux_fun_vec_cmod_le_uniform_exp[OF Vnonneg Tnonneg coeff rho wbnd])
  qed
  have anode: "?a \<in> gs_order_nodes m"
    by (rule gs_min_order_node_mem[OF mpos])
  have apos: "cmod ?a \<le> of_nat m"
  proof -
    obtain j where jlt: "j < m" and aeq: "?a = of_nat (Suc j)"
      using anode mem_gs_order_nodes_iff by blast
    show ?thesis
      using jlt by (simp only: aeq norm_of_nat of_nat_le_iff)
  qed
  have Req: "?R = of_nat m + ?d"
    by (simp add: algebra_simps)
  have Rgt: "of_nat m + 1 < ?R"
    using dgt Req by linarith
  have Sbnd: "cmod (S z) \<le> ?B" if zcircle: "cmod (z - ?a) = 1" for z
  proof -
    have zle: "cmod z \<le> cmod (z - ?a) + cmod ?a"
      using norm_triangle_ineq[of "z-?a" ?a] by (simp add: algebra_simps)
    have zin: "cmod z < ?R"
      using zle zcircle apos Rgt by linarith
    show ?thesis
      by (rule gs_normalized_circle_bound[OF qpos mpos rpos Mnonneg Shol Seq fbnd zin])
  qed
  have fhol: "?f holomorphic_on UNIV"
    by (rule gs_aux_fun_vec_holomorphic)
  show ?thesis
    using gs_normalized_derivative_bound[OF anode Bnonneg fhol Shol Seq Sbnd]
    by simp
qed

lemma gs_circle_clearance_of_balanced_dimensions:
  assumes qge: "4 \<le> q"
  assumes bal: "q * q = 2 * m * n"
  assumes nle: "n \<le> r"
  shows "1 < (of_nat m * of_nat r / of_nat q :: real)"
proof -
  have qlt: "2 * q < q * q"
    using qge by (intro mult_strict_right_mono) auto
  have mnle: "2 * m * n \<le> 2 * m * r"
    using nle by (intro mult_left_mono) auto
  have qmr: "q < m * r"
    using qlt mnle bal by linarith
  have qpos: "(0::real) < of_nat q"
    using qge by simp
  have natcast: "(of_nat q :: real) < of_nat (m * r)"
    using qmr by (simp only: of_nat_less_iff)
  have "(of_nat q :: real) < of_nat m * of_nat r"
    using natcast by (simp only: of_nat_mult)
  then show ?thesis
    using qpos by (simp add: less_divide_eq)
qed

lemma gs_rho_idx_cmod_le:
  assumes qpos: "q > 0"
  assumes tlt: "t < q * q"
  shows "cmod (gs_rho_idx d q t) \<le>
    of_nat q * (1 + cmod (gs_b d)) * cmod (gs_z d)"
proof -
  let ?a = "gs_a_idx q t"
  let ?b = "gs_b_idx q t"
  have ale: "?a \<le> q"
    by (rule gs_a_idx_le[OF qpos tlt])
  have ble: "?b \<le> q"
    by (rule gs_b_idx_le[OF qpos])
  have aff: "cmod (of_nat ?a + of_nat ?b * gs_b d) \<le>
      of_nat ?a + of_nat ?b * cmod (gs_b d)"
    using norm_triangle_ineq[of "of_nat ?a :: complex" "of_nat ?b * gs_b d"]
    by (simp add: norm_mult)
  have a_cast: "(of_nat ?a :: real) \<le> of_nat q"
    using ale by simp
  have b_cast: "(of_nat ?b :: real) \<le> of_nat q"
    using ble by simp
  have prodle: "of_nat ?b * cmod (gs_b d) \<le> of_nat q * cmod (gs_b d)"
    using b_cast by (intro mult_right_mono) auto
  have aff2: "of_nat ?a + of_nat ?b * cmod (gs_b d) \<le>
      of_nat q * (1 + cmod (gs_b d))"
    using a_cast prodle by (simp add: algebra_simps)
  have "cmod (gs_rho_idx d q t) =
      cmod (of_nat ?a + of_nat ?b * gs_b d) * cmod (gs_z d)"
    by (simp add: gs_rho_idx_def gs_rho_def gs_affine_coeff_def norm_mult)
  also have "... \<le> (of_nat q * (1 + cmod (gs_b d))) * cmod (gs_z d)"
    using aff aff2 by (intro mult_right_mono) auto
  finally show ?thesis .
qed

end
