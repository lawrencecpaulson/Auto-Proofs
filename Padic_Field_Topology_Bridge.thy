theory Padic_Field_Topology_Bridge
  imports
    "Padic_Field.Padic_Field_Topology"
    "HOL-Analysis.Analysis"

begin

context padic_fields
begin

section \<open>The $p$-adic topology is a topology\<close>

definition padic_topology :: "padic_number topology" where
  "padic_topology = topology is_open"

lemma istopology_padic: "istopology is_open"
  unfolding istopology_def
proof (intro conjI allI impI)
  fix S T 
  assume "is_open S" "is_open T"
  show "is_open (S \<inter> T)"
  proof (rule is_openI)
    show "S \<inter> T \<subseteq> carrier Q\<^sub>p"
      using \<open>is_open S\<close> is_open_imp_in_Qp by blast
    fix c assume "c \<in> S \<inter> T"
      (* Each point has a ball in S and a ball in T; take the smaller *)
    then obtain n m where "B\<^bsub>n\<^esub>[c] \<subseteq> S" "B\<^bsub>m\<^esub>[c] \<subseteq> T"
      using \<open>is_open S\<close> \<open>is_open T\<close> is_open_def by force
    then have "B\<^bsub>max n m\<^esub>[c] \<subseteq> S \<inter> T"
      by (meson Int_greatest \<open>S \<inter> T \<subseteq> carrier Q\<^sub>p\<close> \<open>c \<in> S \<inter> T\<close> is_ball_def max.cobounded1 max.cobounded2
          nested_balls subsetD subset_trans)
      (* larger radius index = smaller ball in ultrametric *)
    then show "\<exists>k. B\<^bsub>k\<^esub>[c] \<subseteq> S \<inter> T" by blast
  qed
qed (fastforce simp: is_open_def)

text \<open>Agreement on the notions of open set.\<close>
lemma openin_padic_topology: "openin padic_topology = is_open"
  unfolding padic_topology_def
  using istopology_padic topology_inverse' by blast

section \<open>Bridging lemmas — connect old and new frameworks\<close>

lemma topspace_padic: "topspace padic_topology = carrier Q\<^sub>p"
proof (rule Set.set_eqI)
  fix x
  show "x \<in> topspace padic_topology \<longleftrightarrow> x \<in> carrier Q\<^sub>p"
  proof
    assume "x \<in> topspace padic_topology"
    then show "x \<in> carrier Q\<^sub>p"
      unfolding topspace_def using openin_padic_topology is_open_imp_in_Qp by auto
  next
    assume "x \<in> carrier Q\<^sub>p"
    then show "x \<in> topspace padic_topology"
      by (metis c_ball_in_Qp is_open_def openin_padic_topology openin_subset openin_topspace
          set_eq_subset)
  qed
qed

lemma openin_ball:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "openin padic_topology (B\<^bsub>n\<^esub>[c])"
  using openin_padic_topology ball_is_open is_ball_def assms
  by auto

lemma interior_eq:
  assumes "U \<subseteq> carrier Q\<^sub>p"
  shows "interior U = Abstract_Topology.interior_of padic_topology U"
  by (metis assms interiorI interior_of_unique interior_open interior_subset openin_padic_topology)

section \<open>Main topological results in the standard framework\<close>

text \<open>Balls are open.\<close>
lemma ball_openin_padic:
  "is_ball B \<Longrightarrow> openin padic_topology B"
  using openin_padic_topology ball_is_open by simp

text \<open>Hensel's lemma consequence: compactness of $\\mathbb{Z}_p$
  (if the AFP entry proves compactness of the $p$-adic integers).\<close>

text \<open>Open decomposition into maximal balls.\<close>
lemma open_max_ball_decomposition:
  assumes "openin padic_topology U"
  assumes "U \<noteq> topspace padic_topology"
  shows "U = \<Union>(max_balls U)"
proof -
  have U_open: "is_open U" using assms openin_padic_topology by auto
  have U_sub: "U \<subseteq> carrier Q\<^sub>p" using U_open is_open_imp_in_Qp by auto
  have U_ne: "U \<noteq> carrier Q\<^sub>p" using assms topspace_padic by auto
  have int_eq: "interior U = U" using open_interior U_open by auto
  have int_decomp: "interior U = {x \<in> carrier Q\<^sub>p. \<exists>B\<in>max_balls U. x \<in> B}"
    using max_balls_interior U_sub U_ne by auto
  have "\<Union>(max_balls U) \<subseteq> carrier Q\<^sub>p"
    by (metis (no_types, lifting) U_ne U_sub Union_least int_eq max_balls_interior'
        subset_trans)
  moreover have "U = {x \<in> carrier Q\<^sub>p. \<exists>B\<in>max_balls U. x \<in> B}"
    using int_eq int_decomp by simp
  ultimately show "U = \<Union>(max_balls U)"
    using U_sub by blast
qed


end

section \<open>The $p$-adic metric on $\\mathbb{Q}_p$\<close>

context padic_fields
begin

text \<open>The $p$-adic absolute value / distance function.
  Convention: $|x|_p = p^{-\\mathrm{val}(x)}$, with $|0|_p = 0$.\<close>

definition padic_norm :: "padic_number \<Rightarrow> real" where
  "padic_norm x \<equiv> (if x = \<zero> then 0 else p powr (- real_of_int (ord x)))"

definition padic_dist :: "padic_number \<Rightarrow> padic_number \<Rightarrow> real" where
  "padic_dist x y \<equiv> if x \<in> carrier Q\<^sub>p \<and> y \<in> carrier Q\<^sub>p then padic_norm (x \<ominus> y) else 0"

section \<open>$\\mathbb{Q}_p$ is a Metric\_space\<close>

lemma padic_dist_nonneg: "0 \<le> padic_dist x y"
  unfolding padic_dist_def padic_norm_def
  by (simp add: powr_non_neg)

lemma padic_dist_commute:
  shows "padic_dist x y = padic_dist y x"
  apply (simp add: padic_dist_def padic_norm_def)
  by (metis Qp.cring_simprules(4) Qp.minus_a_inv Qp.not_eq_diff_nonzero equal_val_imp_equal_ord(1)
      val_minus)

lemma padic_dist_zero:
  assumes "x \<in> carrier Q\<^sub>p" "y \<in> carrier Q\<^sub>p"
  shows "padic_dist x y = 0 \<longleftrightarrow> x = y"
  unfolding padic_dist_def padic_norm_def
  using Qp.int_inc_zero Qp.nonzero_memE(2) assms p_nonzero by auto

lemma p_gt_1: "1 < (p :: int)"
  using prime prime_gt_1_int by auto

lemma p_ge_1_real: "(1 :: real) \<le> real_of_int p"
  using p_gt_1 by linarith

lemma p_gt_1_real: "(1 :: real) < real_of_int p"
  using p_gt_1 by linarith

lemma diff_sum: 
  assumes "x \<in> carrier Q\<^sub>p" "y \<in> carrier Q\<^sub>p" "z \<in> carrier Q\<^sub>p"
  shows "x \<ominus> z = (x \<ominus> y) \<oplus> (y \<ominus> z)"
proof -
  have xy: "x \<ominus> y \<in> carrier Q\<^sub>p" using assms Qp.minus_closed by auto
  have yz: "y \<ominus> z \<in> carrier Q\<^sub>p" using assms Qp.minus_closed by auto
  have ny: "\<ominus> y \<in> carrier Q\<^sub>p" using assms Qp.a_inv_closed by auto
  have nz: "\<ominus> z \<in> carrier Q\<^sub>p" using assms Qp.a_inv_closed by auto
  have "(x \<ominus> y) \<oplus> (y \<ominus> z) = (x \<oplus> \<ominus> y) \<oplus> (y \<oplus> \<ominus> z)"
    using Qp.minus_eq by presburger
  also have "\<dots> = x \<oplus> (\<ominus> y \<oplus> (y \<oplus> \<ominus> z))"
    using Qp.a_assoc[OF assms(1) ny] Qp.add.m_closed[OF assms(2) nz] by auto
  also have "\<ominus> y \<oplus> (y \<oplus> \<ominus> z) = \<ominus> z"
    using Qp.r_neg1[OF assms(2) nz] by auto
  finally show ?thesis using Qp.minus_eq by auto
qed

lemma padic_norm_ultrametric:
  assumes "a \<in> carrier Q\<^sub>p" "b \<in> carrier Q\<^sub>p"
  shows "padic_norm (a \<oplus> b) \<le> max (padic_norm a) (padic_norm b)"
proof (cases "a \<oplus> b = \<zero>")
  case True
  then have "padic_norm (a \<oplus> b) = 0" unfolding padic_norm_def by simp
  then show ?thesis using padic_norm_def powr_non_neg
    by (simp add: le_max_iff_disj)
next
  case ab_nz: False
  then have ab_nonzero: "a \<oplus> b \<in> nonzero Q\<^sub>p"
    using assms Qp.nonzero_memI Qp.add.m_closed by auto
  have val_ineq: "min (val a) (val b) \<le> val (a \<oplus> b)"
    using val_ultrametric assms by auto
  show ?thesis
  proof (cases "a = \<zero>")
    case True
    then have "a \<oplus> b = b" using assms Qp.l_zero by auto
    then show ?thesis unfolding padic_norm_def using powr_non_neg by auto
  next
    case a_nz: False
    show ?thesis
    proof (cases "b = \<zero>")
      case True
      then have "a \<oplus> b = a" using assms Qp.r_zero by auto
      then show ?thesis unfolding padic_norm_def using powr_non_neg by auto
    next
      case b_nz: False
      have a_nonzero: "a \<in> nonzero Q\<^sub>p" using a_nz assms Qp.nonzero_memI by auto
      have b_nonzero: "b \<in> nonzero Q\<^sub>p" using b_nz assms Qp.nonzero_memI by auto
      have ord_ineq: "min (ord a) (ord b) \<le> ord (a \<oplus> b)"
          using val_ineq val_ord[OF a_nonzero] val_ord[OF b_nonzero] val_ord[OF ab_nonzero]
          using a_nonzero ab_nonzero b_nonzero ord_ultrametric by blast
      have "p powr (- real_of_int (ord (a \<oplus> b))) \<le>
            max (p powr (- real_of_int (ord a))) (p powr (- real_of_int (ord b)))"
      proof -
        from ord_ineq have neg: "- real_of_int (ord (a \<oplus> b)) \<le>
          max (- real_of_int (ord a)) (- real_of_int (ord b))" by linarith
        have step1: "p powr (- real_of_int (ord (a \<oplus> b))) \<le>
          p powr (max (- real_of_int (ord a)) (- real_of_int (ord b)))"
          using powr_mono neg p_ge_1_real by auto
        have step2: "p powr (max (- real_of_int (ord a)) (- real_of_int (ord b))) =
          max (p powr (- real_of_int (ord a))) (p powr (- real_of_int (ord b)))"
          by (auto simp: max_def powr_le_cancel_iff[OF p_gt_1_real])
        show ?thesis using step1 step2 by linarith
      qed
      then show ?thesis
        using padic_norm_def a_nz b_nz ab_nz by auto
    qed
  qed
qed

lemma padic_dist_ultrametric:
  assumes "x \<in> carrier Q\<^sub>p" "y \<in> carrier Q\<^sub>p" "z \<in> carrier Q\<^sub>p"
  shows "padic_dist x z \<le> max (padic_dist x y) (padic_dist y z)"
proof (cases "x = z")
  case True
  then have "padic_dist x z = 0" using assms padic_dist_zero by auto
  then show ?thesis using padic_dist_nonneg[of x y] padic_dist_nonneg[of y z] by simp
next
  case xz: False
  have xy_car: "x \<ominus> y \<in> carrier Q\<^sub>p" using assms Qp.minus_closed by auto
  have yz_car: "y \<ominus> z \<in> carrier Q\<^sub>p" using assms Qp.minus_closed by auto
  have "padic_norm (x \<ominus> z) \<le> max (padic_norm (x \<ominus> y)) (padic_norm (y \<ominus> z))"
    using padic_norm_ultrametric[OF xy_car yz_car] diff_sum[OF assms] by simp
  moreover have "padic_dist x z = padic_norm (x \<ominus> z)"
    using assms unfolding padic_dist_def by auto
  moreover have "padic_dist x y = padic_norm (x \<ominus> y)"
    using assms unfolding padic_dist_def by auto
  moreover have "padic_dist y z = padic_norm (y \<ominus> z)"
    using assms unfolding padic_dist_def by auto
  ultimately show ?thesis by simp
qed


text \<open>The ultrametric inequality implies the triangle inequality.\<close>
lemma padic_dist_triangle:
  assumes "x \<in> carrier Q\<^sub>p" "y \<in> carrier Q\<^sub>p" "z \<in> carrier Q\<^sub>p"
  shows "padic_dist x z \<le> padic_dist x y + padic_dist y z"
  using padic_dist_ultrametric[OF assms] padic_dist_nonneg
  by (metis add_increasing add_increasing2 max_def)

interpretation padic: Metric_space "carrier Q\<^sub>p" padic_dist
proof
  fix x y
  show "0 \<le> padic_dist x y"
    by (simp add: padic_dist_nonneg)
  show "padic_dist x y = padic_dist y x"
    using padic_dist_commute by auto
  assume "x \<in> carrier Q\<^sub>p" and "y \<in> carrier Q\<^sub>p"
  then show "(padic_dist x y = 0) = (x = y)"
    using padic_dist_zero by auto
  fix z assume "z \<in> carrier Q\<^sub>p"
  then show "padic_dist x z \<le> padic_dist x y + padic_dist y z"
    by (simp add: \<open>x \<in> carrier Q\<^sub>p\<close> \<open>y \<in> carrier Q\<^sub>p\<close> padic_dist_triangle)
qed


text \<open>Key correspondence:
  @{term \<open>c_ball n c\<close>} $= \\{x \\in \\mathrm{carrier}\\; \\mathbb{Q}_p \\mid \\mathrm{val}(x - c) \\ge n\\}$
  $= \\{x \\in \\mathrm{carrier}\\; \\mathbb{Q}_p \\mid \\mathrm{padic\\_dist}\\; c\\; x \\le p^{-n}\\}$
  $=$ @{term \<open>padic.mcball c (p powr (-n))\<close>}.\<close>

lemma padic_dist_as_norm:
  assumes "x \<in> carrier Q\<^sub>p" "y \<in> carrier Q\<^sub>p"
  shows "padic_dist x y = padic_norm (x \<ominus> y)"
  unfolding padic_dist_def using assms by auto

lemma c_ball_eq_mcball:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "c_ball n c = padic.mcball c (real_of_int p powr (- real_of_int n))"
proof (rule Set.set_eqI)
  fix x
  show "x \<in> c_ball n c \<longleftrightarrow> x \<in> padic.mcball c (real_of_int p powr (- real_of_int n))"
  proof
    assume xin: "x \<in> c_ball n c"
    then have x_car: "x \<in> carrier Q\<^sub>p" and val_ge: "eint n \<le> val (x \<ominus> c)"
      using c_ball_def by auto
    show "x \<in> padic.mcball c (real_of_int p powr (- real_of_int n))"
      unfolding padic.in_mcball
    proof (intro conjI)
      show "c \<in> carrier Q\<^sub>p" using assms by auto
      show "x \<in> carrier Q\<^sub>p" using x_car by auto
      show "padic_dist c x \<le> real_of_int p powr (- real_of_int n)"
      proof (cases "x = c")
        case True
        then show ?thesis using assms padic_dist_zero powr_non_neg by auto
      next
        case False
        then have xc_nz: "x \<ominus> c \<in> nonzero Q\<^sub>p"
          using x_car assms Qp.not_eq_diff_nonzero by auto
        have "val (x \<ominus> c) = eint (ord (x \<ominus> c))" using val_ord xc_nz by auto
        then have ord_ge: "n \<le> ord (x \<ominus> c)" using val_ge by simp
        have "padic_dist c x = padic_norm (x \<ominus> c)"
          using padic_dist_commute[of c x] padic_dist_as_norm[OF x_car assms]
                padic_dist_as_norm[OF assms x_car] by simp
        also have "\<dots> = p powr (- real_of_int (ord (x \<ominus> c)))"
          using padic_norm_def Qp.nonzero_memE(2)[OF xc_nz] by auto
        also have "\<dots> \<le> p powr (- real_of_int n)"
          using powr_mono p_ge_1_real ord_ge by auto
        finally show ?thesis .
      qed
    qed
  next
    assume xin: "x \<in> padic.mcball c (real_of_int p powr (- real_of_int n))"
    then have x_car: "x \<in> carrier Q\<^sub>p" and dist_le: "padic_dist c x \<le> p powr (- real_of_int n)"
      using padic.in_mcball by auto
    show "x \<in> c_ball n c"
    proof (cases "x = c")
      case True
      then have "c \<ominus> c = \<zero>" using assms Qp.r_neg by auto
      then have "val (c \<ominus> c) = \<infinity>" using val_zero by auto
      then have "eint n \<le> val (c \<ominus> c)" by simp
      then show ?thesis using True c_ballI assms by auto
    next
      case False
      then have xc_nz: "x \<ominus> c \<in> nonzero Q\<^sub>p"
        using x_car assms Qp.not_eq_diff_nonzero by auto
      have "padic_dist c x = padic_norm (x \<ominus> c)"
        using padic_dist_commute[of c x] padic_dist_as_norm[OF x_car assms]
              padic_dist_as_norm[OF assms x_car] by simp
      also have "\<dots> = p powr (- real_of_int (ord (x \<ominus> c)))"
        using padic_norm_def Qp.nonzero_memE(2)[OF xc_nz] by auto
      finally have "p powr (- real_of_int (ord (x \<ominus> c))) \<le> p powr (- real_of_int n)"
        using dist_le by linarith
      then have "- real_of_int (ord (x \<ominus> c)) \<le> - real_of_int n"
        using powr_le_cancel_iff[OF p_gt_1_real] by auto
      then have "n \<le> ord (x \<ominus> c)" by linarith
      then have "eint n \<le> val (x \<ominus> c)"
        using val_ord xc_nz by auto
      then show ?thesis using c_ballI x_car by auto
    qed
  qed
qed

text \<open>Open balls in the metric sense correspond to @{term c_ball} with shifted index.\<close>
lemma mball_eq_c_ball:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "padic.mball c (real_of_int p powr (- real_of_int n)) = c_ball (n + 1) c"
proof (rule Set.set_eqI)
  fix x
  show "x \<in> padic.mball c (real_of_int p powr (- real_of_int n)) \<longleftrightarrow> x \<in> c_ball (n + 1) c"
  proof
    assume xin: "x \<in> padic.mball c (real_of_int p powr (- real_of_int n))"
    then have x_car: "x \<in> carrier Q\<^sub>p" and dist_lt: "padic_dist c x < p powr (- real_of_int n)"
      using padic.in_mball by auto
    show "x \<in> c_ball (n + 1) c"
    proof (cases "x = c")
      case True
      then have "c \<ominus> c = \<zero>" using assms Qp.r_neg by auto
      then have "val (c \<ominus> c) = \<infinity>" using val_zero by auto
      then have "eint (n + 1) \<le> val (c \<ominus> c)" by simp
      then show ?thesis using True c_ballI assms by auto
    next
      case False
      then have xc_nz: "x \<ominus> c \<in> nonzero Q\<^sub>p"
        using x_car assms Qp.not_eq_diff_nonzero by auto
      have "padic_dist c x = padic_norm (x \<ominus> c)"
        using padic_dist_commute[of c x] padic_dist_as_norm[OF x_car assms]
              padic_dist_as_norm[OF assms x_car] by simp
      then have "padic_norm (x \<ominus> c) < p powr (- real_of_int n)"
        using dist_lt by linarith
      then have "p powr (- real_of_int (ord (x \<ominus> c))) < p powr (- real_of_int n)"
        using padic_norm_def Qp.nonzero_memE(2)[OF xc_nz] by auto
      then have "- real_of_int (ord (x \<ominus> c)) < - real_of_int n"
        using powr_less_cancel_iff[OF p_gt_1_real] by auto
      then have "n < ord (x \<ominus> c)" by linarith
      then have "n + 1 \<le> ord (x \<ominus> c)" by linarith
      then have "eint (n + 1) \<le> val (x \<ominus> c)"
        using val_ord xc_nz by auto
      then show ?thesis using c_ballI x_car by auto
    qed
  next
    assume xin: "x \<in> c_ball (n + 1) c"
    then have x_car: "x \<in> carrier Q\<^sub>p" and val_ge: "eint (n + 1) \<le> val (x \<ominus> c)"
      using c_ball_def by auto
    show "x \<in> padic.mball c (real_of_int p powr (- real_of_int n))"
      unfolding padic.in_mball
    proof (intro conjI)
      show "c \<in> carrier Q\<^sub>p" using assms by auto
      show "x \<in> carrier Q\<^sub>p" using x_car by auto
      show "padic_dist c x < real_of_int p powr (- real_of_int n)"
      proof (cases "x = c")
        case True
        then show ?thesis
          using assms padic_dist_zero p_gt_1_real by auto
      next
        case False
        then have xc_nz: "x \<ominus> c \<in> nonzero Q\<^sub>p"
          using x_car assms Qp.not_eq_diff_nonzero by auto
        have "val (x \<ominus> c) = eint (ord (x \<ominus> c))" using val_ord xc_nz by auto
        then have "n + 1 \<le> ord (x \<ominus> c)" using val_ge by simp
        then have "- real_of_int (ord (x \<ominus> c)) < - real_of_int n" by linarith
        then have "p powr (- real_of_int (ord (x \<ominus> c))) < p powr (- real_of_int n)"
          using p_gt_1_real by (simp add: powr_less_cancel_iff)
        moreover have "padic_dist c x = p powr (- real_of_int (ord (x \<ominus> c)))"
        proof -
          have "padic_dist c x = padic_norm (x \<ominus> c)"
            using padic_dist_commute[of c x] padic_dist_as_norm[OF x_car assms]
                  padic_dist_as_norm[OF assms x_car] by simp
          also have "\<dots> = p powr (- real_of_int (ord (x \<ominus> c)))"
            using padic_norm_def Qp.nonzero_memE(2)[OF xc_nz] by auto
          finally show ?thesis .
        qed
        ultimately show ?thesis by linarith
      qed
    qed
  qed
qed

subsection \<open>The metric topology equals @{term is_open}\<close>
lemma padic_topology_eq_mtopology:
  "openin padic.mtopology U \<longleftrightarrow> is_open U"
proof
  assume "openin padic.mtopology U"
  then have U_sub: "U \<subseteq> carrier Q\<^sub>p" and
    U_ball: "\<And>x. x \<in> U \<Longrightarrow> \<exists>r>0. padic.mball x r \<subseteq> U"
    using padic.openin_mtopology by auto
  show "is_open U"
  proof (rule is_openI[OF U_sub])
    fix c assume c_in: "c \<in> U"
    then have c_car: "c \<in> carrier Q\<^sub>p" using U_sub by auto
    obtain r where r_pos: "r > 0" and r_sub: "padic.mball c r \<subseteq> U"
      using U_ball c_in by auto
    (* Choose n large enough that p powr (-n) < r.
       Since p \<ge> 2, p powr (-n) \<rightarrow> 0, so such n exists. *)
    obtain n :: int where n_large: "p powr (- real_of_int n) < r"
    proof -
      obtain k :: nat where hk: "1 / r < real_of_int p ^ k"
        using real_arch_pow[of "1/r" "real_of_int p"] p_gt_1_real r_pos
        using real_arch_pow by blast
      have "p powr (- real_of_int (int k)) = inverse (p ^ k)"
        using p_gt_1_real
        by (simp add: powr_minus powr_realpow inverse_eq_divide)
      also have "\<dots> < r"
        using hk r_pos p_gt_1_real
        by (simp add: field_simps)
      finally show ?thesis using that by blast
    qed
    have "c_ball (n + 1) c = padic.mball c (p powr (- real_of_int n))"
      using mball_eq_c_ball[OF c_car] by auto
    then have "c_ball (n + 1) c \<subseteq> U"
      using r_sub padic.mball_subset_concentric n_large by auto
    then show "\<exists>k. c_ball k c \<subseteq> U" by blast
  qed
next
  assume U_open: "is_open U"
  show "openin padic.mtopology U"
    unfolding padic.openin_mtopology
  proof (intro conjI allI impI)
    show "U \<subseteq> carrier Q\<^sub>p" using U_open is_open_imp_in_Qp by blast
  next
    fix x assume x_in: "x \<in> U"
    then have x_car: "x \<in> carrier Q\<^sub>p" using U_open is_open_imp_in_Qp by blast
    obtain n where n_sub: "c_ball n x \<subseteq> U"
      using U_open x_in is_open_def by auto
    have ball_eq: "padic.mball x (p powr (- real_of_int (n - 1))) = c_ball n x"
      using mball_eq_c_ball[OF x_car, of "n - 1"] by auto
    have r_pos: "0 < p powr (- real_of_int (n - 1))"
      using p_gt_1_real by simp
    show "\<exists>r>0. padic.mball x r \<subseteq> U"
      using ball_eq n_sub r_pos
      by blast
  qed
qed

lemma padic_mtopology_eq: "padic.mtopology = padic_topology"
  using padic_topology_eq_mtopology openin_padic_topology
  by (intro topology.openin_inject[THEN iffD1] ext iffI; simp)


lemma mcball_is_open:
  assumes "c \<in> carrier Q\<^sub>p" "0 < r"
  shows "openin padic.mtopology (padic.mcball c r)"
  unfolding padic.openin_mtopology
proof (intro conjI strip)
  show "padic.mcball c r \<subseteq> carrier Q\<^sub>p"
    using padic.mcball_subset_mspace by auto
next
  fix y assume y_in: "y \<in> padic.mcball c r"
  then have y_car: "y \<in> carrier Q\<^sub>p" and dy: "padic_dist c y \<le> r"
    using padic.in_mcball by auto
  show "\<exists>\<epsilon>>0. padic.mball y \<epsilon> \<subseteq> padic.mcball c r"
  proof (intro exI conjI)
    show "0 < r" using assms by auto
    show "padic.mball y r \<subseteq> padic.mcball c r"
    proof
      fix z assume z_in: "z \<in> padic.mball y r"
      then have z_car: "z \<in> carrier Q\<^sub>p" and dyz: "padic_dist y z < r"
        using padic.in_mball by auto
      have "padic_dist c z \<le> max (padic_dist c y) (padic_dist y z)"
        using padic_dist_ultrametric[OF assms(1) y_car z_car] by auto
      also have "\<dots> \<le> r" using dy dyz by simp
      finally show "z \<in> padic.mcball c r"
        using padic.in_mcball assms(1) z_car by auto
    qed
  qed
qed

text \<open>Equivalently: balls are clopen.\<close>
lemma c_ball_clopen:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "openin padic.mtopology (c_ball n c) \<and> closedin padic.mtopology (c_ball n c)"
proof
  have r_pos: "0 < real_of_int p powr (- real_of_int n)"
    using p_gt_1_real by simp
  show "openin padic.mtopology (c_ball n c)"
    using c_ball_eq_mcball[OF assms] mcball_is_open[OF assms r_pos] by simp
  show "closedin padic.mtopology (c_ball n c)"
    using c_ball_eq_mcball[OF assms] padic.closedin_mcball by simp
qed

text \<open>Total disconnectedness.\<close>
lemma padic_mtop_totally_disconnected:
  assumes "connectedin padic.mtopology S"
  shows "\<exists>a. S \<subseteq> {a}"
proof (rule ccontr)
  assume neg: "\<not>(\<exists>a. S \<subseteq> {a})"
  have S_sub: "S \<subseteq> carrier Q\<^sub>p"
    using assms connectedin_subset_topspace padic.topspace_mtopology by blast
  obtain x y where xy: "x \<in> S" "y \<in> S" "x \<noteq> y"
  proof -
    have "S \<noteq> {}" using neg by blast
    then obtain x where "x \<in> S" by auto
    have "\<not>(S \<subseteq> {x})" using neg by auto
    then obtain y where "y \<in> S" "y \<noteq> x" by auto
    then show thesis using \<open>x \<in> S\<close> that by auto
  qed
  have x_car: "x \<in> carrier Q\<^sub>p" and y_car: "y \<in> carrier Q\<^sub>p"
    using S_sub xy by auto
  have xy_nz: "x \<ominus> y \<in> nonzero Q\<^sub>p"
    using xy x_car y_car Qp.not_eq_diff_nonzero by auto
  define n where "n = ord (x \<ominus> y) + 1"
  have x_in_ball: "x \<in> c_ball n x"
  proof (rule c_ballI[OF x_car])
    have "x \<ominus> x = \<zero>" using x_car Qp.r_neg by auto
    then show "eint n \<le> val (x \<ominus> x)" using val_zero by simp
  qed
  have y_not_in_ball: "y \<notin> c_ball n x"
  proof
    assume "y \<in> c_ball n x"
    then have val_ge: "eint n \<le> val (y \<ominus> x)" using c_ballE by auto
    have yx_nz: "y \<ominus> x \<in> nonzero Q\<^sub>p"
      using xy x_car y_car Qp.not_eq_diff_nonzero by auto
    have "val (y \<ominus> x) = eint (ord (y \<ominus> x))" using val_ord[OF yx_nz] by auto
    then have n_le: "n \<le> ord (y \<ominus> x)" using val_ge by simp
    have "y \<ominus> x = \<ominus> (x \<ominus> y)"
      using x_car y_car using Qp.minus_a_inv by blast
    then have "ord (y \<ominus> x) = ord (x \<ominus> y)"
      using equal_val_imp_equal_ord(1)[OF xy_nz]
            val_minus[of "x \<ominus> y"] val_ord[OF xy_nz] val_ord[OF yx_nz]
      using ord_minus xy_nz by presburger
    then show False using n_le n_def by linarith
  qed
  have clopen: "openin padic.mtopology (c_ball n x)" "closedin padic.mtopology (c_ball n x)"
    using c_ball_clopen[OF x_car] by auto
  have "S \<subseteq> c_ball n x \<or> disjnt S (c_ball n x)"
    using connectedin_clopen_cases[OF assms clopen(2) clopen(1)] by auto
  then show False
  proof
    assume "S \<subseteq> c_ball n x"
    then show False using xy(2) y_not_in_ball by auto
  next
    assume "disjnt S (c_ball n x)"
    then show False using xy(1) x_in_ball
      by (simp add: disjnt_def disjoint_iff)
  qed
qed

text \<open>Nested balls — reproved from the ultrametric inequality.\<close>
lemma ultrametric_nested:
  assumes "padic.mcball x r \<inter> padic.mcball y s \<noteq> {}"
  shows "padic.mcball x r \<subseteq> padic.mcball y s \<or> padic.mcball y s \<subseteq> padic.mcball x r"
proof -
  obtain z where z_xr: "z \<in> padic.mcball x r" and z_ys: "z \<in> padic.mcball y s"
    using assms by blast
  then have x_car: "x \<in> carrier Q\<^sub>p" and y_car: "y \<in> carrier Q\<^sub>p" and z_car: "z \<in> carrier Q\<^sub>p"
    and dxz: "padic_dist x z \<le> r" and dyz: "padic_dist y z \<le> s"
    using padic.in_mcball by auto
  have dzx: "padic_dist z x \<le> r" using dxz padic_dist_commute by simp
  have dzy: "padic_dist z y \<le> s" using dyz padic_dist_commute by simp
  show ?thesis
  proof (cases "r \<le> s")
    case True
    show ?thesis
    proof (intro disjI1 subsetI)
      fix w assume w_in: "w \<in> padic.mcball x r"
      then have w_car: "w \<in> carrier Q\<^sub>p" and dxw: "padic_dist x w \<le> r"
        using padic.in_mcball by auto
      have "padic_dist z w \<le> max (padic_dist z x) (padic_dist x w)"
        using padic_dist_ultrametric[OF z_car x_car w_car] by auto
      also have "\<dots> \<le> r" using dzx dxw by simp
      finally have dzw: "padic_dist z w \<le> r" .
      have "padic_dist y w \<le> max (padic_dist y z) (padic_dist z w)"
        using padic_dist_ultrametric[OF y_car z_car w_car] by auto
      also have "\<dots> \<le> s" using dyz dzw True by simp
      finally show "w \<in> padic.mcball y s"
        using padic.in_mcball y_car w_car by auto
    qed
  next
    case False
    then have sr: "s \<le> r" by simp
    show ?thesis
    proof (intro disjI2 subsetI)
      fix w assume w_in: "w \<in> padic.mcball y s"
      then have w_car: "w \<in> carrier Q\<^sub>p" and dyw: "padic_dist y w \<le> s"
        using padic.in_mcball by auto
      have "padic_dist z w \<le> max (padic_dist z y) (padic_dist y w)"
        using padic_dist_ultrametric[OF z_car y_car w_car] by auto
      also have "\<dots> \<le> s" using dzy dyw by simp
      finally have dzw: "padic_dist z w \<le> s" .
      have "padic_dist x w \<le> max (padic_dist x z) (padic_dist z w)"
        using padic_dist_ultrametric[OF x_car z_car w_car] by auto
      also have "\<dots> \<le> r" using dxz dzw sr by simp
      finally show "w \<in> padic.mcball x r"
        using padic.in_mcball x_car w_car by auto
    qed
  qed
qed

subsection \<open>Closedness and disconnectedness\<close>

text \<open>Balls are also closed (clopen).\<close>
lemma closedin_ball:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "closedin padic_topology (B\<^bsub>n\<^esub>[c])"
  using c_ball_clopen[OF assms] padic_mtopology_eq by simp

lemma ball_closedin_padic:
  "is_ball B \<Longrightarrow> closedin padic_topology B"
  using closedin_ball is_ball_def by auto

text \<open>The $p$-adic topology is totally disconnected.\<close>
lemma padic_totally_disconnected:
  assumes "connectedin padic_topology S"
  shows "\<exists>a. S \<subseteq> {a}"
  using padic_mtop_totally_disconnected assms padic_mtopology_eq by simp

subsection \<open>Completeness\<close>

text \<open>$\\mathbb{Q}_p$ is complete: every Cauchy sequence converges.
  This uses @{term \<open>Metric_space.mcomplete\<close>}.\<close>

lemma padic_complete: "padic.mcomplete"
  unfolding padic.mcomplete_def
proof (intro allI impI)
  fix \<sigma> assume cauchy: "padic.MCauchy \<sigma>"

  text \<open>Task 1: Reduce to bounded sequences.
    Every Cauchy sequence in $\\mathbb{Q}_p$ is eventually in some ball @{term \<open>c_ball 0 c\<close>}.
    By rescaling (multiplying by a power of $p$), we can reduce to a
    sequence in $\\mathbb{Z}_p$ (i.e., with non-negative valuation).\<close>

  have \<sigma>_range: "range \<sigma> \<subseteq> carrier Q\<^sub>p"
    using cauchy padic.MCauchy_def by auto

  obtain c N where c_car: "c \<in> carrier Q\<^sub>p"
    and eventually_in_ball: "\<forall>m \<ge> N. \<sigma> m \<in> c_ball 0 c"
  proof -
    obtain N where hN: "\<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> padic_dist (\<sigma> n) (\<sigma> n') < 1"
      using cauchy[unfolded padic.MCauchy_def] by (meson zero_less_one)
    have \<sigma>N_car: "\<sigma> N \<in> carrier Q\<^sub>p"
      using \<sigma>_range by auto
    have "\<forall>m \<ge> N. \<sigma> m \<in> c_ball 0 (\<sigma> N)"
    proof (intro allI impI)
      fix m assume "N \<le> m"
      then have "padic_dist (\<sigma> N) (\<sigma> m) < 1" using hN by auto
      then have "padic_dist (\<sigma> N) (\<sigma> m) \<le> real_of_int p powr (- real_of_int 0)"
        using p_ge_1_real by simp
      then have "\<sigma> m \<in> padic.mcball (\<sigma> N) (real_of_int p powr (- real_of_int 0))"
        using padic.in_mcball \<sigma>N_car \<sigma>_range by auto
      then show "\<sigma> m \<in> c_ball 0 (\<sigma> N)"
        using c_ball_eq_mcball[OF \<sigma>N_car] by simp
    qed
    then show thesis using that \<sigma>N_car by blast
  qed


  text \<open>Task 2: Translate metric Cauchy to val-based Cauchy.
    Show that @{term padic.MCauchy} (in @{term padic_dist}) implies that
    for all $n$, eventually $\\mathrm{val}(\\sigma_m - \\sigma_k) \\ge n$.
    This is the AFP's notion of being Cauchy.\<close>

  have val_cauchy: "\<forall>n. \<exists>K. \<forall>m k. m \<ge> K \<longrightarrow> k \<ge> K \<longrightarrow> eint n \<le> val (\<sigma> m \<ominus> \<sigma> k)"
  proof (intro allI)
    fix n :: int
    have "real_of_int p powr (- real_of_int n) > 0"
      using p_gt_1 by (simp add: powr_gt_zero)
    then obtain K where hK: "\<forall>m k. K \<le> m \<longrightarrow> K \<le> k \<longrightarrow> padic_dist (\<sigma> m) (\<sigma> k) < real_of_int p powr (- real_of_int n)"
      using cauchy[unfolded padic.MCauchy_def] by (meson less_le_not_le)
    show "\<exists>K. \<forall>m k. m \<ge> K \<longrightarrow> k \<ge> K \<longrightarrow> eint n \<le> val (\<sigma> m \<ominus> \<sigma> k)"
    proof (intro exI allI impI)
      fix m k assume "K \<le> m" "K \<le> k"
      then have dist_bound: "padic_dist (\<sigma> m) (\<sigma> k) < real_of_int p powr (- real_of_int n)"
        using hK by auto
      have \<sigma>m_car: "\<sigma> m \<in> carrier Q\<^sub>p" and \<sigma>k_car: "\<sigma> k \<in> carrier Q\<^sub>p"
        using \<sigma>_range by auto
      have diff_car: "\<sigma> m \<ominus> \<sigma> k \<in> carrier Q\<^sub>p"
        using Qp.minus_closed \<sigma>m_car \<sigma>k_car by auto
      show "eint n \<le> val (\<sigma> m \<ominus> \<sigma> k)"
      proof (cases "\<sigma> m \<ominus> \<sigma> k = \<zero>")
        case True
        then show ?thesis using val_zero by simp
      next
        case False
        then have diff_nz: "\<sigma> m \<ominus> \<sigma> k \<in> nonzero Q\<^sub>p"
          using Qp.nonzero_memI diff_car by auto
        have norm_eq: "padic_norm (\<sigma> m \<ominus> \<sigma> k) = real_of_int p powr (- real_of_int (ord (\<sigma> m \<ominus> \<sigma> k)))"
          using padic_norm_def False by auto
        have "padic_norm (\<sigma> m \<ominus> \<sigma> k) < real_of_int p powr (- real_of_int n)"
          using dist_bound padic_dist_as_norm \<sigma>m_car \<sigma>k_car by auto
        then have "real_of_int p powr (- real_of_int (ord (\<sigma> m \<ominus> \<sigma> k))) < real_of_int p powr (- real_of_int n)"
          using norm_eq by simp
        then have "- real_of_int (ord (\<sigma> m \<ominus> \<sigma> k)) < - real_of_int n"
          by (rule powr_less_cancel[OF _ p_gt_1_real])
        then have "n < ord (\<sigma> m \<ominus> \<sigma> k)" by linarith
        then have "n \<le> ord (\<sigma> m \<ominus> \<sigma> k)" by linarith
        then show ?thesis
          using val_ord diff_nz eint_ord_code(1) by auto
      qed
    qed
  qed

  text \<open>Task 3: Reduce to $\\mathbb{Z}_p$.
    After shifting/rescaling, express the (tail of the) sequence as
    $\\iota \\circ s$ for some $s : \\mathbb{N} \\to \\mathrm{carrier}\\; \\mathbb{Z}_p$,
    then show $s$ is @{term is_Zp_cauchy}.\<close>

  define s where "s m = to_Zp (\<sigma> m \<ominus> c)" for m
  have s_Zp: "\<forall>m. s m \<in> carrier Z\<^sub>p"
  proof
    fix m
    have "\<sigma> m \<in> carrier Q\<^sub>p" using \<sigma>_range by auto
    then have "\<sigma> m \<ominus> c \<in> carrier Q\<^sub>p" using Qp.minus_closed c_car by auto
    then show "s m \<in> carrier Z\<^sub>p" unfolding s_def using to_Zp_closed by auto
  qed
  have diff_in_val_ring: "\<forall>m \<ge> N. \<sigma> m \<ominus> c \<in> \<O>\<^sub>p"
  proof (intro allI impI)
    fix m assume "N \<le> m"
    then have "\<sigma> m \<in> c_ball 0 c" using eventually_in_ball by auto
    then have \<sigma>m_car: "\<sigma> m \<in> carrier Q\<^sub>p" and val_ge: "eint 0 \<le> val (\<sigma> m \<ominus> c)"
      using c_ball_def by auto
    have "\<sigma> m \<ominus> c \<in> carrier Q\<^sub>p" using Qp.minus_closed \<sigma>m_car c_car by auto
    moreover have "(0 :: eint) \<le> val (\<sigma> m \<ominus> c)" using val_ge eint_0 by simp
    ultimately show "\<sigma> m \<ominus> c \<in> \<O>\<^sub>p" using Qp_val_ringI by auto
  qed
  have s_eq: "\<forall>m \<ge> N. \<sigma> m = \<iota> (s m) \<oplus> c"
  proof (intro allI impI)
    fix m assume hm: "N \<le> m"
    have in_val: "\<sigma> m \<ominus> c \<in> \<O>\<^sub>p" using diff_in_val_ring hm by auto
    have "\<iota> (s m) = \<iota> (to_Zp (\<sigma> m \<ominus> c))" unfolding s_def by simp
    also have "... = \<sigma> m \<ominus> c" using to_Zp_inc[OF in_val] by simp
    finally have inc_eq: "\<iota> (s m) = \<sigma> m \<ominus> c" .
    have \<sigma>m_car: "\<sigma> m \<in> carrier Q\<^sub>p" using \<sigma>_range by auto
    have inc_car: "\<iota> (s m) \<in> carrier Q\<^sub>p" using inc_closed s_Zp by auto
    show "\<sigma> m = \<iota> (s m) \<oplus> c"
      using inc_eq \<sigma>m_car c_car
      by (metis Qp.a_assoc Qp.a_inv_closed Qp.l_neg Qp.minus_eq Qp.r_zero)
  qed
  have s_closed: "s \<in> carrier Z\<^sub>p\<^bsup>\<omega>\<^esup>"
    using s_Zp closed_seqs_memI by auto
  have s_val_cauchy: "\<forall>n :: int. \<exists>M. \<forall>m k. M < m \<and> M < k \<longrightarrow> eint n < val_Zp_dist (s m) (s k)"
  proof (intro allI)
    fix n :: int
    obtain K where hK: "\<forall>m k. m \<ge> K \<longrightarrow> k \<ge> K \<longrightarrow> eint (n + 1) \<le> val (\<sigma> m \<ominus> \<sigma> k)"
      using val_cauchy by (meson le_cases)
    define K' where "K' = max N K"
    show "\<exists>M. \<forall>m k. M < m \<and> M < k \<longrightarrow> eint n < val_Zp_dist (s m) (s k)"
    proof (intro exI[of _ K'] allI impI)
      fix m k assume mk: "K' < m \<and> K' < k"
      then have hm: "m \<ge> N" "m \<ge> K" and hk: "k \<ge> N" "k \<ge> K"
        unfolding K'_def by auto
      have sm_car: "s m \<in> carrier Z\<^sub>p" and sk_car: "s k \<in> carrier Z\<^sub>p"
        using s_Zp by auto
      have diff_Zp: "s m \<ominus>\<^bsub>Z\<^sub>p\<^esub> s k \<in> carrier Z\<^sub>p"
        using Zp.minus_closed sm_car sk_car by auto
      have "val_Zp_dist (s m) (s k) = val_Zp (s m \<ominus>\<^bsub>Z\<^sub>p\<^esub> s k)"
        using val_Zp_dist_def by auto
      also have "... = val (\<iota> (s m \<ominus>\<^bsub>Z\<^sub>p\<^esub> s k))"
        using val_of_inc[OF diff_Zp] by simp
      also have "... = val (\<iota> (s m) \<ominus> \<iota> (s k))"
        using inc_of_diff[OF sm_car sk_car] by simp
      also have "... = val ((\<sigma> m \<ominus> c) \<ominus> (\<sigma> k \<ominus> c))"
      proof -
        have "\<iota> (s m) = \<sigma> m \<ominus> c"
          using to_Zp_inc diff_in_val_ring hm(1) s_def by auto
        moreover have "\<iota> (s k) = \<sigma> k \<ominus> c"
          using to_Zp_inc diff_in_val_ring hk(1) s_def by auto
        ultimately show ?thesis by simp
      qed
      also have "... = val (\<sigma> m \<ominus> \<sigma> k)"
      proof -
        have \<sigma>m_car: "\<sigma> m \<in> carrier Q\<^sub>p" and \<sigma>k_car: "\<sigma> k \<in> carrier Q\<^sub>p"
          using \<sigma>_range by auto
        have "(\<sigma> m \<ominus> c) \<ominus> (\<sigma> k \<ominus> c) = \<sigma> m \<ominus> \<sigma> k"
          using \<sigma>m_car \<sigma>k_car c_car Qp.minus_eq Qp.a_assoc Qp.a_comm
                Qp.a_inv_closed Qp.l_neg Qp.r_zero Qp.minus_closed
          by (smt (verit))
        then show ?thesis by simp
      qed
      finally have val_eq: "val_Zp_dist (s m) (s k) = val (\<sigma> m \<ominus> \<sigma> k)" .
      have "eint (n + 1) \<le> val (\<sigma> m \<ominus> \<sigma> k)"
        using hK hm(2) hk(2) by auto
      then show "eint n < val_Zp_dist (s m) (s k)"
        using val_eq Suc_ile_eq by auto
    qed
  qed
  have s_cauchy: "is_Zp_cauchy s"
    using s_closed s_val_cauchy is_Zp_cauchy_def by auto

  text \<open>Task 4: Apply $\\mathbb{Z}_p$ completeness.
    Use @{thm [source] is_Zp_cauchy_imp_has_limit} to get the limit in $\\mathbb{Z}_p$,
    then map it back to $\\mathbb{Q}_p$.\<close>

  define a where "a = res_lim s"
  have a_Zp: "a \<in> carrier Z\<^sub>p"
    using s_cauchy res_lim_in_Zp a_def by auto

  have Zp_conv: "Zp_converges_to s a"
    using is_Zp_cauchy_imp_has_limit s_cauchy a_def by auto

  text \<open>Task 5: Translate $\\mathbb{Z}_p$ convergence back to $\\mathbb{Q}_p$ metric convergence.
    Show @{term \<open>Zp_converges_to s a\<close>} implies
    @{term \<open>limitin padic.mtopology \<sigma> L sequentially\<close>}.
    Key bridge: @{thm [source] val_of_inc}, @{thm [source] inc_of_diff}, and the characterization
    @{thm [source] padic.limitin_metric_dist_null}.\<close>

  define L where "L = \<iota> a \<oplus> c"
  have L_car: "L \<in> carrier Q\<^sub>p"
    unfolding L_def using Qp.a_closed[OF inc_closed[OF a_Zp] c_car] by simp
  have inc_a_car: "\<iota> a \<in> carrier Q\<^sub>p" using inc_closed a_Zp by auto
  have "limitin padic.mtopology \<sigma> L sequentially"
    unfolding padic.limitin_metric_dist_null
  proof (intro conjI)
    show "L \<in> carrier Q\<^sub>p" by (rule L_car)
  next
    show "\<forall>\<^sub>F m in sequentially. \<sigma> m \<in> carrier Q\<^sub>p"
      using \<sigma>_range by (simp add: eventually_sequentially, intro exI[of _ 0]) auto
  next
    show "((\<lambda>m. padic_dist (\<sigma> m) L) \<longlongrightarrow> 0) sequentially"
    proof (rule metric_LIMSEQ_I)
      fix r :: real assume "r > 0"
      \<comment> \<open>Find n such that p powr (-n) < r\<close>
      define n where "n = \<lceil>- log (real_of_int p) r\<rceil> + 1"
      have n_bound: "real_of_int n > - log (real_of_int p) r"
        unfolding n_def using le_of_int_ceiling[of "- log (real_of_int p) r"]
        by linarith
      have p_powr_bound: "real_of_int p powr (- real_of_int n) < r"
      proof -
        have "- real_of_int n < log (real_of_int p) r"
          using n_bound by linarith
        then show ?thesis
          using powr_less_iff[OF p_gt_1_real \<open>r > 0\<close>] by simp
      qed
      \<comment> \<open>From Zp_conv, get K such that for m > K, val_Zp (s m \<ominus> a) > n\<close>
      have "\<exists>k. \<forall>m>k. eint n < val_Zp (s m \<ominus>\<^bsub>Z\<^sub>p\<^esub> a)"
        using Zp_conv[unfolded Zp_converges_to_def] by blast
      then obtain K where hK: "\<forall>m>K. eint n < val_Zp (s m \<ominus>\<^bsub>Z\<^sub>p\<^esub> a)"
        by auto
      \<comment> \<open>Take threshold = max K N + 1\<close>
      define M where "M = max (nat (K + 1)) N"
      show "\<exists>no. \<forall>m\<ge>no. dist ((\<lambda>m. padic_dist (\<sigma> m) L) m) 0 < r"
      proof (intro exI[of _ M] allI impI)
        fix m assume hm: "M \<le> m"
        have m_ge_N: "m \<ge> N" using hm unfolding M_def by auto
        have m_gt_K: "m > K" using hm unfolding M_def by auto
        \<comment> \<open>Relate padic_dist (\<sigma> m) L to val_Zp (s m \<ominus> a)\<close>
        have \<sigma>m_car: "\<sigma> m \<in> carrier Q\<^sub>p" using \<sigma>_range by auto
        have sm_car: "s m \<in> carrier Z\<^sub>p" using s_Zp by auto
        have diff_car: "s m \<ominus>\<^bsub>Z\<^sub>p\<^esub> a \<in> carrier Z\<^sub>p"
          using Zp.minus_closed[OF sm_car a_Zp] by auto
        \<comment> \<open>Key: \<iota> (s m) \<ominus> \<iota> a = \<sigma> m \<ominus> L\<close>
        have inc_sm: "\<iota> (s m) = \<sigma> m \<ominus> c"
          using s_eq m_ge_N \<sigma>m_car c_car
          by (metis diff_in_val_ring s_def to_Zp_inc)
        have "\<iota> (s m \<ominus>\<^bsub>Z\<^sub>p\<^esub> a) = \<iota> (s m) \<ominus> \<iota> a"
          using inc_of_diff[OF sm_car a_Zp] by simp
        also have "... = (\<sigma> m \<ominus> c) \<ominus> \<iota> a"
          using inc_sm by simp
        also have "... = \<sigma> m \<ominus> (c \<oplus> \<iota> a)"
          using Qp.right_inv_add[OF c_car inc_a_car \<sigma>m_car] by simp
        also have "... = \<sigma> m \<ominus> (\<iota> a \<oplus> c)"
          using Qp.a_comm[OF c_car inc_a_car] by simp
        also have "... = \<sigma> m \<ominus> L" unfolding L_def by simp
        finally have key_eq: "\<iota> (s m \<ominus>\<^bsub>Z\<^sub>p\<^esub> a) = \<sigma> m \<ominus> L" .
        \<comment> \<open>Get the val bound\<close>
        have val_bound: "eint n < val_Zp (s m \<ominus>\<^bsub>Z\<^sub>p\<^esub> a)"
          using hK m_gt_K by auto
        have val_inc: "val_Zp (s m \<ominus>\<^bsub>Z\<^sub>p\<^esub> a) = val (\<iota> (s m \<ominus>\<^bsub>Z\<^sub>p\<^esub> a))"
          using val_of_inc[OF diff_car] by simp
        have val_diff: "eint n < val (\<sigma> m \<ominus> L)"
          using val_bound val_inc key_eq by simp
        \<comment> \<open>Convert to padic_dist bound\<close>
        have diff_car2: "\<sigma> m \<ominus> L \<in> carrier Q\<^sub>p"
          using Qp.minus_closed[OF \<sigma>m_car L_car] by simp
        have dist_eq: "padic_dist (\<sigma> m) L = padic_norm (\<sigma> m \<ominus> L)"
          using padic_dist_as_norm[OF \<sigma>m_car L_car] by simp
        show "dist ((\<lambda>m. padic_dist (\<sigma> m) L) m) 0 < r"
        proof (cases "\<sigma> m \<ominus> L = \<zero>")
          case True
          then have "padic_dist (\<sigma> m) L = 0"
            using dist_eq padic_norm_def by simp
          then show ?thesis using \<open>r > 0\<close> by (simp add: dist_real_def)
        next
          case False
          have nz: "\<sigma> m \<ominus> L \<in> nonzero Q\<^sub>p"
            using Qp.nonzero_memI[OF diff_car2 False] by simp
          have val_eq: "val (\<sigma> m \<ominus> L) = eint (ord (\<sigma> m \<ominus> L))"
            using val_ord[OF nz] by simp
          have ord_bound: "n < ord (\<sigma> m \<ominus> L)"
            using val_diff val_eq by simp
          have neg_ord_bound: "- real_of_int (ord (\<sigma> m \<ominus> L)) < - real_of_int n"
            using ord_bound by linarith
          have norm_eq: "padic_norm (\<sigma> m \<ominus> L) = real_of_int p powr (- real_of_int (ord (\<sigma> m \<ominus> L)))"
            using padic_norm_def False by simp
          have "padic_norm (\<sigma> m \<ominus> L) < real_of_int p powr (- real_of_int n)"
            using norm_eq powr_less_mono[OF neg_ord_bound p_gt_1_real] by simp
          then have "padic_dist (\<sigma> m) L < r"
            using dist_eq p_powr_bound by linarith
          then show ?thesis
            using padic_dist_nonneg[of "\<sigma> m" L] by (simp add: dist_real_def)
        qed
      qed
    qed
  qed
  then show "\<exists>x. limitin padic.mtopology \<sigma> x sequentially"
    by blast
qed

end
end
