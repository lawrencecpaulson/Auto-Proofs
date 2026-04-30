theory Padic_Field_Topology_Bridge
  imports
    "Padic_Field.Padic_Field_Topology"
    "HOL-Analysis.Analysis"
    "HOL-ex.Sketch_and_Explore" Isar_Explore

begin

context padic_fields
begin

(* ============================================================ *)
(* STEP 1: Define the p-adic topology as an istopology          *)
(* ============================================================ *)

definition padic_topology :: "padic_number topology" where
  "padic_topology = topology is_open"

(* The key bridging lemma: is_open satisfies istopology *)
lemma istopology_padic: "istopology is_open"
proof (unfold istopology_def, intro conjI allI impI)
  (* Finite intersection: is_open S \<and> is_open T \<Longrightarrow> is_open (S \<inter> T) *)
  fix S T :: "padic_number set"
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

(* Consequence: the definition is well-formed *)
lemma openin_padic_topology: "openin padic_topology = is_open"
  unfolding padic_topology_def
  using istopology_padic topology_inverse' by blast

(* ============================================================ *)
(* STEP 2: Bridging lemmas — connect old and new frameworks     *)
(* ============================================================ *)

(* The topspace is carrier Q\<^sub>p *)
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

(* Every ball is openin padic_topology *)
lemma openin_ball:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "openin padic_topology (B\<^bsub>n\<^esub>[c])"
  using openin_padic_topology ball_is_open is_ball_def assms
  by auto

(* The interior in the old sense equals the interior in the new sense *)
lemma interior_eq:
  assumes "U \<subseteq> carrier Q\<^sub>p"
  shows "interior U = Abstract_Topology.interior_of padic_topology U"
  by (metis assms interiorI interior_of_unique interior_open interior_subset openin_padic_topology)

(* ============================================================ *)
(* STEP 3: Main topological results in the standard framework   *)
(* ============================================================ *)

(* Balls are open *)
lemma ball_openin_padic:
  "is_ball B \<Longrightarrow> openin padic_topology B"
  using openin_padic_topology ball_is_open by simp

lemma ball_closedin_padic:
  "is_ball B \<Longrightarrow> closedin padic_topology B"
  sorry (* requires ball_is_closed *)

(* Nested balls: the p-adic topology is totally disconnected *)
lemma padic_totally_disconnected:
  assumes "connectedin padic_topology S"
  shows "\<exists>a. S \<subseteq> {a}"
  sorry (* follows from nested_balls' and the ultrametric property:
             every ball is both open and closed *)

(* Balls are also closed *)
lemma closedin_ball:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "closedin padic_topology (B\<^bsub>n\<^esub>[c])"
  sorry (* The complement of a ball is a union of balls, hence open.
             Key fact: in ultrametric spaces, balls are clopen. *)

(* Hensel's lemma consequence: compactness of Z_p *)
(* (if the AFP entry proves compactness of the p-adic integers) *)

(* Open decomposition into maximal balls *)
lemma open_max_ball_decomposition:
  assumes "openin padic_topology U"
  assumes "U \<noteq> topspace padic_topology"
  shows "U = \<Union>(max_balls U)"
  using openin_padic_topology assms max_balls_interior open_interior
  sorry


end

section "Metric development"

(* ================================================================ *)
(* PART 1: The p-adic metric on Q_p                                 *)
(* ================================================================ *)

context padic_fields
begin

(* The p-adic absolute value / distance function.
     Convention: |x|_p = p powr (- val x), with |0|_p = 0. *)

definition padic_norm :: "padic_number \<Rightarrow> real" where
  "padic_norm x \<equiv> (if x = \<zero> then 0 else p powr (- real_of_int (ord x)))"

definition padic_dist :: "padic_number \<Rightarrow> padic_number \<Rightarrow> real" where
  "padic_dist x y \<equiv> if x \<in> carrier Q\<^sub>p \<and> y \<in> carrier Q\<^sub>p then padic_norm (x \<ominus> y) else 0"

(* ================================================================ *)
(* PART 2: Q_p is a Metric_space                                    *)
(* ================================================================ *)

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
      proof -
        have "min (eint (ord a)) (eint (ord b)) \<le> eint (ord (a \<oplus> b))"
          using val_ineq val_ord[OF a_nonzero] val_ord[OF b_nonzero] val_ord[OF ab_nonzero]
          by simp
        then show ?thesis by (simp add: min_def split: if_splits)
      qed
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


(* The ultrametric inequality implies the triangle inequality *)
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


(* Key correspondence:
     c_ball n c = {x \<in> carrier Q\<^sub>p. val(x - c) \<ge> n}
                = {x \<in> carrier Q\<^sub>p. padic_dist c x \<le> p powr (-n)}
                = padic.mcball c (p powr (-n))                         *)

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
      then show ?thesis using assms c_ballI val_zero by auto
    next
      case False
      then have xc_nz: "x \<ominus> c \<in> nonzero Q\<^sub>p"
        using x_car assms Qp.not_eq_diff_nonzero by auto
      have "padic_dist c x = padic_norm (x \<ominus> c)"
        using padic_dist_commute padic_dist_as_norm x_car assms by auto
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
(* ================================================================ *)

(* The topology generated by the metric equals the one from is_open *)
lemma padic_topology_eq_mtopology:
  "openin padic.mtopology U \<longleftrightarrow> is_open U"
proof
  assume "openin padic.mtopology U"
  then have U_sub: "U \<subseteq> carrier Q\<^sub>p" and
    U_ball: "\<And>x. x \<in> U \<Longrightarrow> \<exists>r>0. padic.mball x r \<subseteq> U"
    using padic.openin_mtopology by auto
  show "is_open U"
  proof (rule is_openI[OF U_sub])
    fix c assume "c \<in> U"
    then obtain r where "r > 0" "padic.mball c r \<subseteq> U"
      using U_ball by auto
        (* Choose n such that p powr (-n) \<le> r, then c_ball n c \<subseteq> mball c r \<subseteq> U *)
    then obtain n where "c_ball n c \<subseteq> U"
      sorry
    then show "\<exists>n. c_ball n c \<subseteq> U" by blast
  qed
next
  assume "is_open U"
  show "openin padic.mtopology U"
    unfolding padic.openin_mtopology
  proof (intro conjI allI impI)
    show "U \<subseteq> carrier Q\<^sub>p" using \<open>is_open U\<close> is_open_imp_in_Qp by blast
    fix x assume "x \<in> U"
    then obtain n where "c_ball n c \<subseteq> U"
      using \<open>is_open U\<close> is_open_def sorry
        (* Then mball x (p powr (-n)) = c_ball (n+1) x \<subseteq> c_ball n x \<subseteq> U *)
    then show "\<exists>r>0. padic.mball x r \<subseteq> U"
      sorry
  qed
qed


(* ================================================================ *)
(* PART 6: Ultrametric-specific results (new)                       *)
(* ================================================================ *)

(* Closed balls are also open — the key ultrametric phenomenon *)
lemma mcball_is_open:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "openin padic.mtopology (padic.mcball c r)"
proof -
  (* For any y in mcball c r, mball y r' \<subseteq> mcball c r
       where r' = r (or any positive value), by ultrametric inequality:
       d(c,z) \<le> max(d(c,y), d(y,z)) \<le> max(r, r') *)
  show ?thesis
    unfolding padic.openin_mtopology
    sorry (* ultrametric: if d(c,y) \<le> r and d(y,z) < \<epsilon> then d(c,z) \<le> r *)
qed

(* Equivalently: balls are clopen *)
lemma c_ball_clopen:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "openin padic.mtopology (c_ball n c) \<and> closedin padic.mtopology (c_ball n c)"
  using c_ball_eq_mcball mcball_is_open assms padic.closedin_mcball
  sorry

(* Total disconnectedness *)
lemma padic_mtop_totally_disconnected:
  assumes "connectedin padic.mtopology S"
  shows "\<exists>a. S \<subseteq> {a}"
  sorry (* If S has two distinct points x, y with d(x,y) = p^{-n},
           then c_ball (n+1) x is clopen, contains x but not y,
           contradicting connectedness. *)

(* Nested balls — reproved from ultrametric *)
lemma ultrametric_nested:
  assumes "padic.mcball x r \<inter> padic.mcball y s \<noteq> {}"
  shows "padic.mcball x r \<subseteq> padic.mcball y s \<or> padic.mcball y s \<subseteq> padic.mcball x r"
  sorry (* direct from ultrametric inequality *)

(* ================================================================ *)
(* PART 7: Completeness (if the AFP entry has the ingredients)      *)
(* ================================================================ *)

(* Q_p is complete: every Cauchy sequence converges.
     This would use Metric_space.mcomplete. *)

lemma padic_complete: "padic.mcomplete"
  sorry (* Requires showing that Q_p is the completion of Q under | |_p.
             The AFP entry constructs Q_p as equivalence classes of Cauchy
             sequences in Z_p, so this should be provable from the construction. *)

end
end
