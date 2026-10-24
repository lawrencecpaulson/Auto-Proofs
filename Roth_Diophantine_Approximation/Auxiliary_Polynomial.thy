theory Auxiliary_Polynomial
  imports
    Roth_Index_Count
    Integral_Reduction
    "Bounded_Integer_Kernels.Integer_Kernel_Bounds"
begin

section \<open>Bounded integral coordinates for powers of an algebraic integer\<close>

definition roth_power_step ::
  "int poly \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int" where
  "roth_power_step f d c j =
    (if j = 0 then 0 else c (j - 1)) - c (d - 1) * Polynomial.coeff f j"

primrec roth_power_coords ::
  "int poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "roth_power_coords f d 0 =
    (\<lambda>j. if j = 0 then 1 else 0)"
| "roth_power_coords f d (Suc k) =
    roth_power_step f d (roth_power_coords f d k)"

definition roth_power_value ::
  "nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> real \<Rightarrow> real" where
  "roth_power_value d c x = (\<Sum>j<d. of_int (c j) * x ^ j)"

lemma roth_monic_root:
  fixes f :: "int poly"
    and x :: real
  assumes monic: "Polynomial.lead_coeff f = 1"
    and root: "poly (map_poly of_int f) x = 0"
  shows "(\<Sum>j<Polynomial.degree f.
    of_int (Polynomial.coeff f j) * x ^ j) = -(x ^ Polynomial.degree f)"
proof -
  have deg: "Polynomial.degree (map_poly of_int f) = Polynomial.degree f"
    by (rule degree_map_poly_2) (simp add: monic)
  have "0 = (\<Sum>j\<le>Polynomial.degree f.
      of_int (Polynomial.coeff f j) * x ^ j)"
    using root by (simp add: poly_altdef deg coeff_map_poly)
  also have "\<dots> =
      (\<Sum>j<Polynomial.degree f.
        of_int (Polynomial.coeff f j) * x ^ j) + x ^ Polynomial.degree f"
    using monic by (simp add: lessThan_Suc_atMost[symmetric] sum.lessThan_Suc)
  finally show ?thesis by linarith
qed

lemma roth_power_value_step:
  fixes f :: "int poly"
  assumes dpos: "0 < d"
    and monic: "Polynomial.lead_coeff f = 1"
    and d: "d = Polynomial.degree f"
    and root: "poly (map_poly of_int f) x = 0"
  shows "roth_power_value d (roth_power_step f d c) x =
    x * roth_power_value d c x"
proof -
  have shift:
    "(\<Sum>j<d. of_int (if j = 0 then 0 else c (j-1)) * x ^ j) =
      x * (\<Sum>j<d-1. of_int (c j) * x ^ j)"
    using dpos
    by (cases d)
      (simp_all add: sum.lessThan_Suc_shift
        sum_distrib_left power_Suc algebra_simps
        del: sum.lessThan_Suc sum.op_ivl_Suc)
  have partial:
    "(\<Sum>j<d. of_int (Polynomial.coeff f j) * x ^ j) = -(x ^ d)"
    using roth_monic_root[OF monic root] by (simp add: d)
  have val_eq:
    "roth_power_value d c x =
      (\<Sum>j<d-1. of_int (c j) * x ^ j) +
        of_int (c (d-1)) * x ^ (d-1)"
    using dpos unfolding roth_power_value_def
    by (cases d) (simp_all add: sum.lessThan_Suc)
  have "roth_power_value d (roth_power_step f d c) x =
      (\<Sum>j<d. of_int (if j = 0 then 0 else c (j-1)) * x ^ j) -
      of_int (c (d-1)) *
        (\<Sum>j<d. of_int (Polynomial.coeff f j) * x ^ j)"
    unfolding roth_power_value_def roth_power_step_def
    by (simp add: sum_subtractf sum_distrib_left algebra_simps)
  also have "\<dots> = x * roth_power_value d c x"
    using shift partial val_eq dpos
    by (simp add: power_Suc[symmetric] algebra_simps)
  finally show ?thesis .
qed

lemma roth_power_coords_value:
  fixes f :: "int poly"
  assumes monic: "Polynomial.lead_coeff f = 1"
    and d: "d = Polynomial.degree f"
    and root: "poly (map_poly of_int f) x = 0"
  shows "roth_power_value d (roth_power_coords f d k) x = x ^ k"
proof -
  have dpos: "0 < d"
    using roth_monic_root[OF monic root] d by (cases d) auto
  show ?thesis
  proof (induction k)
    case 0
    then show ?case
      using dpos by (cases d)
        (simp_all add: roth_power_value_def sum.lessThan_Suc_shift
          del: sum.lessThan_Suc sum.op_ivl_Suc)
  next
    case (Suc k)
    then show ?case
      by (simp only: roth_power_coords.simps(2)
        roth_power_value_step[OF dpos monic d root] power_Suc)
  qed
qed

definition roth_power_base :: "int poly \<Rightarrow> int" where
  "roth_power_base f =
    1 + (\<Sum>j<Polynomial.degree f. abs (Polynomial.coeff f j))"

lemma roth_power_base_ge_one:
  "1 \<le> roth_power_base f"
  by (simp add: roth_power_base_def sum_nonneg)

lemma roth_power_base_coeff:
  assumes "j < Polynomial.degree f"
  shows "1 + abs (Polynomial.coeff f j) \<le> roth_power_base f"
proof -
  have "abs (Polynomial.coeff f j) \<le>
    (\<Sum>i<Polynomial.degree f. abs (Polynomial.coeff f i))"
    by (rule member_le_sum) (use assms in auto)
  then show ?thesis by (simp add: roth_power_base_def)
qed

lemma roth_power_coords_bound:
  fixes f :: "int poly"
  assumes d: "d = Polynomial.degree f"
    and dpos: "0 < d"
    and j: "j < d"
  shows "abs (roth_power_coords f d k j) \<le> roth_power_base f ^ k"
  using j
proof (induction k arbitrary: j)
  case 0
  then show ?case by simp
next
  case (Suc k)
  let ?B = "roth_power_base f"
  let ?c = "roth_power_coords f d k"
  let ?a = "if j = 0 then 0 else ?c (j-1)"
  have B: "1 \<le> ?B"
    by (rule roth_power_base_ge_one)
  have a: "abs ?a \<le> ?B ^ k"
  proof (cases "j = 0")
    case True
    then show ?thesis using B by simp
  next
    case False
    have "j-1 < d"
      using Suc.prems by (meson diff_le_self le_less_trans)
    then show ?thesis using False Suc.IH by simp
  qed
  have c: "abs (?c (d-1)) \<le> ?B ^ k"
    using Suc.IH[of "d-1"] dpos by simp
  have fc: "1 + abs (Polynomial.coeff f j) \<le> ?B"
    by (rule roth_power_base_coeff) (use Suc.prems d in auto)
  have step:
    "abs (roth_power_step f d ?c j) \<le>
      abs ?a + abs (?c (d-1)) * abs (Polynomial.coeff f j)"
    unfolding roth_power_step_def
    by (rule order_trans[OF abs_triangle_ineq4]) (simp add: abs_mult)
  also have "\<dots> \<le> ?B ^ k +
      ?B ^ k * abs (Polynomial.coeff f j)"
    by (intro add_mono a mult_right_mono[OF c]) simp_all
  also have "\<dots> = ?B ^ k * (1 + abs (Polynomial.coeff f j))"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> ?B ^ k * ?B"
    using fc by (intro mult_left_mono) simp_all
  also have "\<dots> = ?B ^ Suc k"
    by (simp add: power_Suc)
  finally show ?case by simp
qed

section \<open>Integer coordinates of diagonal Taylor coefficients\<close>

definition roth_total_exponent ::
  "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> nat" where
  "roth_total_exponent K =
    (\<Sum>v\<in>Poly_Mapping.keys K. Poly_Mapping.lookup K v)"

lemma roth_total_exponent_on:
  assumes supp: "Poly_Mapping.keys K \<subseteq> {..<m}"
  shows "roth_total_exponent K =
    (\<Sum>v<m. Poly_Mapping.lookup K v)"
proof -
  have "(\<Sum>v\<in>Poly_Mapping.keys K. Poly_Mapping.lookup K v) =
      (\<Sum>v<m. Poly_Mapping.lookup K v)"
    by (rule sum.mono_neutral_left)
      (use supp in \<open>auto simp: not_in_keys_iff_lookup_eq_zero\<close>)
  then show ?thesis by (simp add: roth_total_exponent_def)
qed

lemma roth_total_exponent_diff_bound:
  assumes box: "K \<in> roth_exponent_box m r"
  shows "roth_total_exponent (K-J) \<le> (\<Sum>v<m. r v)"
proof -
  have supp: "Poly_Mapping.keys (K-J) \<subseteq> {..<m}"
  proof -
    have "Poly_Mapping.keys (K-J) \<subseteq> Poly_Mapping.keys K"
      by (auto simp: in_keys_iff Poly_Mapping.lookup_minus)
    then show ?thesis using roth_exponent_boxD(1)[OF box] by blast
  qed
  have point: "Poly_Mapping.lookup (K-J) v \<le> r v" if "v<m" for v
    using roth_exponent_boxD(2)[OF box that]
    by (simp add: Poly_Mapping.lookup_minus)
  have "(\<Sum>v<m. Poly_Mapping.lookup (K-J) v) \<le>
      (\<Sum>v<m. r v)"
    by (rule sum_mono) (use point in auto)
  then show ?thesis
    by (simp add: roth_total_exponent_on[OF supp])
qed

lemma roth_insertion_diagonal_monom:
  fixes a c :: real
  shows "insertion (\<lambda>_. a) (MPoly_Type.monom K c) =
    c * a ^ roth_total_exponent K"
  by (simp add: roth_insertion_monom roth_total_exponent_def
    power_sum)

definition roth_aux_matrix_entry ::
  "int poly \<Rightarrow> nat \<Rightarrow>
    (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>
    (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> nat \<Rightarrow> int" where
  "roth_aux_matrix_entry f d J K j =
    int (roth_mchoose K J) *
      roth_power_coords f d (roth_total_exponent (K-J)) j"

lemma roth_aux_matrix_entry_value:
  fixes a :: real and f :: "int poly"
  assumes monic: "Polynomial.lead_coeff f = 1"
    and d: "d = Polynomial.degree f"
    and root: "poly (map_poly of_int f) a = 0"
  shows "roth_taylor_coeff (\<lambda>_. a) J (MPoly_Type.monom K (1::real)) =
    (\<Sum>j<d. of_int (roth_aux_matrix_entry f d J K j) * a ^ j)"
proof -
  have "roth_taylor_coeff (\<lambda>_. a) J (MPoly_Type.monom K (1::real)) =
      real (roth_mchoose K J) *
        a ^ roth_total_exponent (K-J)"
    by (simp add: roth_hasse_eval[symmetric]
      roth_hasse_monom_exact roth_insertion_diagonal_monom)
  also have "\<dots> =
      real (roth_mchoose K J) *
        roth_power_value d
          (roth_power_coords f d (roth_total_exponent (K-J))) a"
    using roth_power_coords_value[OF monic d root] by simp
  also have "\<dots> =
      (\<Sum>j<d. of_int (roth_aux_matrix_entry f d J K j) * a ^ j)"
    by (simp add: roth_power_value_def roth_aux_matrix_entry_def
      sum_distrib_left algebra_simps)
  finally show ?thesis .
qed

lemma roth_aux_matrix_entry_value_int:
  fixes a :: real and f :: "int poly"
  assumes monic: "Polynomial.lead_coeff f = 1"
    and d: "d = Polynomial.degree f"
    and root: "poly (map_poly of_int f) a = 0"
  shows "roth_taylor_coeff (\<lambda>_. a) J
      (MPoly_Type.monom K (of_int c)) =
    (\<Sum>j<d. of_int (c * roth_aux_matrix_entry f d J K j) * a ^ j)"
proof -
  have "roth_taylor_coeff (\<lambda>_. a) J
      (MPoly_Type.monom K (of_int c)) =
      of_int c * roth_taylor_coeff (\<lambda>_. a) J
        (MPoly_Type.monom K (1::real))"
    by (simp add: roth_hasse_eval[symmetric]
      roth_hasse_monom_exact roth_insertion_diagonal_monom)
  also have "\<dots> =
      of_int c *
        (\<Sum>j<d. of_int (roth_aux_matrix_entry f d J K j) * a ^ j)"
    by (simp add: roth_aux_matrix_entry_value[OF monic d root])
  also have "\<dots> =
      (\<Sum>j<d. of_int (c * roth_aux_matrix_entry f d J K j) * a ^ j)"
    by (simp add: sum_distrib_left algebra_simps)
  finally show ?thesis .
qed

lemma roth_taylor_coeff_sum_finite:
  assumes "finite S"
  shows "roth_taylor_coeff a I (\<Sum>x\<in>S. P x) =
    (\<Sum>x\<in>S. roth_taylor_coeff a I (P x))"
  by (simp add: roth_hasse_eval[symmetric]
    roth_hasse_sum[OF assms] roth_insertion_sum[OF assms])

lemma roth_aux_matrix_taylor_sum:
  fixes a :: real and f :: "int poly" and q :: nat
  assumes monic: "Polynomial.lead_coeff f = 1"
    and d: "d = Polynomial.degree f"
    and root: "poly (map_poly of_int f) a = 0"
  shows "roth_taylor_coeff (\<lambda>_. a) J
      (\<Sum>t<q. MPoly_Type.monom (K t) (of_int (c t))) =
    (\<Sum>j<d. of_int
      (\<Sum>t<q. roth_aux_matrix_entry f d J (K t) j * c t) * a ^ j)"
proof -
  have "roth_taylor_coeff (\<lambda>_. a) J
      (\<Sum>t<q. MPoly_Type.monom (K t) (of_int (c t))) =
      (\<Sum>t<q. roth_taylor_coeff (\<lambda>_. a) J
        (MPoly_Type.monom (K t) (of_int (c t))))"
    by (rule roth_taylor_coeff_sum_finite) simp
  also have "\<dots> =
      (\<Sum>t<q. \<Sum>j<d.
        of_int (c t * roth_aux_matrix_entry f d J (K t) j) * a ^ j)"
    by (intro sum.cong) (simp_all add:
      roth_aux_matrix_entry_value_int[OF monic d root])
  also have "\<dots> =
      (\<Sum>j<d. \<Sum>t<q.
        of_int (c t * roth_aux_matrix_entry f d J (K t) j) * a ^ j)"
    by (rule sum.swap)
  also have "\<dots> =
      (\<Sum>j<d. of_int
        (\<Sum>t<q. roth_aux_matrix_entry f d J (K t) j * c t) * a ^ j)"
    by (intro sum.cong refl)
      (simp add: sum_distrib_left sum_distrib_right algebra_simps)
  finally show ?thesis .
qed

lemma roth_aux_matrix_entry_bound:
  fixes f :: "int poly"
  assumes d: "d = Polynomial.degree f"
    and box: "K \<in> roth_exponent_box m r"
    and j: "j < d"
  shows "abs (roth_aux_matrix_entry f d J K j) \<le>
    (2 * roth_power_base f) ^ (\<Sum>v<m. r v)"
proof -
  let ?R = "\<Sum>v<m. r v"
  let ?B = "roth_power_base f"
  have dpos: "0 < d"
    using j by simp
  have t: "roth_total_exponent (K-J) \<le> ?R"
    by (rule roth_total_exponent_diff_bound[OF box])
  have c: "abs (roth_power_coords f d
      (roth_total_exponent (K-J)) j) \<le> ?B ^ ?R"
  proof -
    have "abs (roth_power_coords f d
        (roth_total_exponent (K-J)) j) \<le>
        ?B ^ roth_total_exponent (K-J)"
      by (rule roth_power_coords_bound[OF d dpos j])
    also have "\<dots> \<le> ?B ^ ?R"
      by (rule power_increasing) (use t roth_power_base_ge_one in auto)
    finally show ?thesis .
  qed
  have ch: "int (roth_mchoose K J) \<le> int (2 ^ ?R)"
    using roth_mchoose_box_bound[OF box] by simp
  have "abs (roth_aux_matrix_entry f d J K j) =
      int (roth_mchoose K J) *
        abs (roth_power_coords f d (roth_total_exponent (K-J)) j)"
    by (simp add: roth_aux_matrix_entry_def abs_mult)
  also have "\<dots> \<le> int (2 ^ ?R) * ?B ^ ?R"
    by (rule mult_mono[OF ch c]) auto
  also have "\<dots> = (2 * ?B) ^ ?R"
    by (simp add: power_mult_distrib)
  finally show ?thesis .
qed

section \<open>The auxiliary Taylor system\<close>

lemma roth_mchoose_nonzero_box:
  assumes box: "K \<in> roth_exponent_box m r"
    and nz: "roth_mchoose K J \<noteq> 0"
  shows "J \<in> roth_exponent_box m r"
proof (rule roth_exponent_boxI)
  have le: "Poly_Mapping.lookup J v \<le> Poly_Mapping.lookup K v" for v
    using nz by (meson roth_mchoose_zero not_le)
  show "Poly_Mapping.keys J \<subseteq> {..<m}"
  proof
    fix v
    assume v: "v \<in> Poly_Mapping.keys J"
    then have "Poly_Mapping.lookup J v \<noteq> 0"
      by (simp add: in_keys_iff)
    then have "Poly_Mapping.lookup K v \<noteq> 0"
      using le[of v] by auto
    then have "v \<in> Poly_Mapping.keys K"
      by (simp add: in_keys_iff)
    then show "v \<in> {..<m}"
      using roth_exponent_boxD(1)[OF box] by auto
  qed
  show "Poly_Mapping.lookup J v \<le> r v" if "v < m" for v
    using le[of v] roth_exponent_boxD(2)[OF box that]
    by linarith
qed

lemma roth_aux_matrix_entry_outside:
  assumes box: "K \<in> roth_exponent_box m r"
    and outside: "J \<notin> roth_exponent_box m r"
  shows "roth_aux_matrix_entry f d J K j = 0"
  using roth_mchoose_nonzero_box[OF box] outside
  by (auto simp: roth_aux_matrix_entry_def)

definition roth_aux_matrix ::
  "int poly \<Rightarrow> nat \<Rightarrow>
    (nat \<Rightarrow>\<^sub>0 nat) list \<Rightarrow>
    (nat \<Rightarrow>\<^sub>0 nat) list \<Rightarrow> int mat" where
  "roth_aux_matrix f d Is Ks =
    mat (length Is * d) (length Ks)
      (\<lambda>(u,t). roth_aux_matrix_entry f d
        (Is ! (u div d)) (Ks ! t) (u mod d))"

lemma roth_aux_matrix_carrier:
  "roth_aux_matrix f d Is Ks \<in> carrier_mat (length Is * d) (length Ks)"
  by (simp add: roth_aux_matrix_def)

lemma roth_aux_matrix_bounded:
  fixes f :: "int poly"
  assumes d: "d = Polynomial.degree f"
    and dpos: "0 < d"
    and Ks: "set Ks \<subseteq> roth_exponent_box m r"
  shows "roth_aux_matrix f d Is Ks \<in>
    Bounded_mat ((2 * roth_power_base f) ^ (\<Sum>v<m. r v))"
proof (unfold Bounded_mat_def, intro CollectI allI impI)
  fix u t
  assume u: "u < dim_row (roth_aux_matrix f d Is Ks)"
    and t: "t < dim_col (roth_aux_matrix f d Is Ks)"
  have kt: "Ks ! t \<in> roth_exponent_box m r"
    using t Ks by (auto simp: roth_aux_matrix_def
      dest: nth_mem)
  have rem: "u mod d < d"
    using dpos by simp
  show "abs (roth_aux_matrix f d Is Ks $$ (u,t)) \<le>
      (2 * roth_power_base f) ^ (\<Sum>v<m. r v)"
    using roth_aux_matrix_entry_bound[OF d kt rem] u t
    by (simp add: roth_aux_matrix_def)
qed

lemma roth_aux_matrix_kernel_taylor:
  fixes a :: real and f :: "int poly" and x :: "int vec"
  assumes monic: "Polynomial.lead_coeff f = 1"
    and d: "d = Polynomial.degree f"
    and root: "poly (map_poly of_int f) a = 0"
    and dpos: "0 < d"
    and xcar: "x \<in> carrier_vec (length Ks)"
    and Ax: "roth_aux_matrix f d Is Ks *\<^sub>v x =
      0\<^sub>v (length Is * d)"
    and i: "i < length Is"
  shows "roth_taylor_coeff (\<lambda>_. a) (Is ! i)
      (\<Sum>t<length Ks. MPoly_Type.monom (Ks ! t) (of_int (x $ t))) = 0"
proof -
  have row_zero:
    "(\<Sum>t<length Ks.
      roth_aux_matrix_entry f d (Is ! i) (Ks ! t) j * (x $ t)) = 0"
    if j: "j < d" for j
  proof -
    let ?u = "i * d + j"
    have u: "?u < length Is * d"
    proof -
      have "?u < Suc i * d"
        using j by simp
      also have "\<dots> \<le> length Is * d"
      proof (rule mult_right_mono)
        show "Suc i \<le> length Is"
          using i by simp
        show "0 \<le> d"
          by simp
      qed
      finally show ?thesis .
    qed
    have div: "?u div d = i"
      using j dpos by simp
    have mod: "?u mod d = j"
      using j dpos by simp
    have "0 = (roth_aux_matrix f d Is Ks *\<^sub>v x) $ ?u"
      using Ax u by simp
    also have "\<dots> =
      (\<Sum>t<length Ks.
        roth_aux_matrix_entry f d (Is ! i) (Ks ! t) j * (x $ t))"
      using u xcar j by (simp add: scalar_prod_def row_def
        roth_aux_matrix_def div atLeast0LessThan)
    finally show ?thesis by (rule sym)
  qed
  show ?thesis
    by (simp add: roth_aux_matrix_taylor_sum[OF monic d root]
      row_zero)
qed

lemma roth_aux_matrix_outside_taylor:
  fixes a :: real and f :: "int poly" and x :: "int vec"
  assumes monic: "Polynomial.lead_coeff f = 1"
    and d: "d = Polynomial.degree f"
    and root: "poly (map_poly of_int f) a = 0"
    and Ks: "set Ks \<subseteq> roth_exponent_box m r"
    and outside: "J \<notin> roth_exponent_box m r"
  shows "roth_taylor_coeff (\<lambda>_. a) J
      (\<Sum>t<length Ks. MPoly_Type.monom (Ks ! t) (of_int (x $ t))) = 0"
proof -
  have z: "roth_aux_matrix_entry f d J (Ks ! t) j = 0"
    if "t < length Ks" for t j
    by (rule roth_aux_matrix_entry_outside)
      (use Ks outside that in \<open>auto dest: nth_mem\<close>)
  show ?thesis
    by (simp add: roth_aux_matrix_taylor_sum[OF monic d root] z)
qed

lemma roth_aux_polynomial_coeff:
  fixes x :: "int vec"
  assumes dist: "distinct Ks" and t: "t < length Ks"
  shows "MPoly_Type.coeff
      (\<Sum>s<length Ks. MPoly_Type.monom (Ks ! s) (x $ s)) (Ks ! t) =
    x $ t"
proof -
  have "MPoly_Type.coeff
      (\<Sum>s<length Ks. MPoly_Type.monom (Ks ! s) (x $ s)) (Ks ! t) =
      (\<Sum>s<length Ks. if Ks ! t = Ks ! s then x $ s else 0)"
    by (simp add: roth_coeff_sum More_MPoly_Type.coeff_monom when_def)
  also have "\<dots> = (\<Sum>s<length Ks. if s = t then x $ s else 0)"
    by (intro sum.cong refl)
      (use dist t in \<open>auto simp: nth_eq_iff_index_eq\<close>)
  also have "\<dots> = x $ t"
    using t by simp
  finally show ?thesis .
qed

lemma roth_aux_polynomial_nonzero:
  fixes x :: "int vec"
  assumes dist: "distinct Ks"
    and xcar: "x \<in> carrier_vec (length Ks)"
    and xnz: "x \<noteq> 0\<^sub>v (length Ks)"
  shows "(\<Sum>t<length Ks. MPoly_Type.monom (Ks ! t) (x $ t)) \<noteq> 0"
proof -
  obtain t where t: "t < length Ks" "x $ t \<noteq> 0"
    using xcar xnz by force
  show ?thesis
    using roth_aux_polynomial_coeff[OF dist t(1), of x] t
    by (auto simp: MPoly_Type.coeff_def zero_mpoly.rep_eq)
qed

lemma roth_aux_polynomial_in_box:
  assumes Ks: "set Ks \<subseteq> roth_exponent_box m r"
  shows "roth_poly_in_box m r
    (\<Sum>t<length Ks. MPoly_Type.monom (Ks ! t) (x $ t :: int))"
  by (rule roth_poly_in_box_sum)
    (use Ks in \<open>auto intro: roth_poly_in_box_monom dest: nth_mem\<close>)

lemma roth_aux_polynomial_cast:
  fixes x :: "int vec"
  shows "replace_coeff of_int
      (\<Sum>t<length Ks. MPoly_Type.monom (Ks ! t) (x $ t)) =
    (\<Sum>t<length Ks. MPoly_Type.monom (Ks ! t) (of_int (x $ t) :: real))"
  by (simp add: roth_replace_coeff_sum replace_coeff_monom)

theorem roth_auxiliary_polynomial_monic:
  fixes f :: "int poly" and a :: real
  assumes monic: "Polynomial.lead_coeff f = 1"
    and d: "d = Polynomial.degree f"
    and dpos: "0 < d"
    and root: "poly (map_poly of_int f) a = 0"
    and mpos: "0 < m"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and epos: "0 < eps"
    and elt: "eps < 1"
    and gap: "2 * real d < real m * eps\<^sup>2"
  shows "\<exists>P :: int mpoly.
    P \<noteq> 0 \<and> roth_poly_in_box m r P \<and>
    ereal (real m * (1-eps) / 2) \<le>
      roth_index m r (\<lambda>_. a) (replace_coeff of_int P) \<and>
    (\<forall>K. abs (MPoly_Type.coeff P K) \<le>
      2 * int (card (roth_exponent_box m r)) *
        (2 * roth_power_base f) ^ (\<Sum>v<m. r v))"
proof -
  let ?S = "roth_exponent_box m r"
  let ?C = "{J \<in> ?S. roth_weight m r J < real m * (1-eps) / 2}"
  let ?B = "(2 * roth_power_base f) ^ (\<Sum>v<m. r v)"
  have Cfin: "finite ?C"
    by simp
  obtain Is where Is: "set Is = ?C" "distinct Is"
    using finite_distinct_list[OF Cfin] by blast
  obtain Ks where Ks: "set Ks = ?S" "distinct Ks"
    using finite_distinct_list[OF finite_roth_exponent_box] by blast
  have Ksbox: "set Ks \<subseteq> ?S"
    using Ks by simp
  have onebox: "(0::nat \<Rightarrow>\<^sub>0 nat) \<in> ?S"
    by (rule roth_exponent_boxI) simp_all
  have theta_pos: "0 < real m * (1-eps) / 2"
    using mpos elt by simp
  have oneC: "(0::nat \<Rightarrow>\<^sub>0 nat) \<in> ?C"
    using onebox theta_pos by (simp add: roth_weight_def)
  have Ispos: "0 < length Is"
    using Is oneC by (cases Is) auto
  have ppos: "0 < length Is * d"
    using Ispos dpos by simp
  have card_gap: "2 * d * card ?C < card ?S"
    by (rule roth_taylor_conditions_dimension
      [where m=m and r=r and eps=eps and d=d])
      (use mpos rpos epos gap in auto)
  have Iscard: "length Is = card ?C"
  proof -
    have "card (set Is) = length Is"
      using Is(2) by (simp add: distinct_card)
    then show ?thesis using Is(1) by simp
  qed
  have Kscard: "length Ks = card ?S"
  proof -
    have "card (set Ks) = length Ks"
      using Ks(2) by (simp add: distinct_card)
    then show ?thesis using Ks(1) by simp
  qed
  have dim_strict: "2 * (length Is * d) < length Ks"
    using card_gap by (simp add: Iscard Kscard mult_ac)
  have dim: "2 * (length Is * d) \<le> length Ks"
    using dim_strict by simp
  let ?A = "roth_aux_matrix f d Is Ks"
  have Acar: "?A \<in> carrier_mat (length Is * d) (length Ks)"
    by (rule roth_aux_matrix_carrier)
  have Abnd: "?A \<in> Bounded_mat ?B"
    by (rule roth_aux_matrix_bounded[OF d dpos Ksbox])
  obtain x where xcar: "x \<in> carrier_vec (length Ks)"
    and xnz: "x \<noteq> 0\<^sub>v (length Ks)"
    and Ax: "?A *\<^sub>v x = 0\<^sub>v (length Is * d)"
    and xbnd: "x \<in> Bounded_vec
      (2 * int (length Ks) * max 1 ?B)"
    using exists_ne_zero_int_vec_bounded_kernel_linear
      [OF Acar ppos dim Abnd] by blast
  have Bbase: "1 \<le> 2 * roth_power_base f"
    using roth_power_base_ge_one[of f] by simp
  have Bge: "1 \<le> ?B"
    by (rule one_le_power[OF Bbase])
  have xpoint: "abs (x $ t) \<le> 2 * int (length Ks) * ?B"
    if "t < length Ks" for t
    using xbnd xcar that Bge by (simp add: Bounded_vec_def)
  define P :: "int mpoly" where
    "P = (\<Sum>t<length Ks. MPoly_Type.monom (Ks ! t) (x $ t))"
  have Pnz: "P \<noteq> 0"
    unfolding P_def by (rule roth_aux_polynomial_nonzero[OF Ks(2) xcar xnz])
  have Pbox: "roth_poly_in_box m r P"
    unfolding P_def by (rule roth_aux_polynomial_in_box[OF Ksbox])
  have Preal: "replace_coeff of_int P =
      (\<Sum>t<length Ks.
        MPoly_Type.monom (Ks ! t) (of_int (x $ t) :: real))"
    unfolding P_def by (rule roth_aux_polynomial_cast)
  have Pindex: "ereal (real m * (1-eps) / 2) \<le>
      roth_index m r (\<lambda>_. a) (replace_coeff of_int P)"
  proof (simp only: roth_index_ge_iff, intro allI impI)
    fix J
    assume Jw: "ereal (roth_weight m r J) <
      ereal (real m * (1-eps) / 2)"
    then have w: "roth_weight m r J < real m * (1-eps) / 2"
      by simp
    show "roth_taylor_coeff (\<lambda>_. a) J (replace_coeff of_int P) = 0"
    proof (cases "J \<in> ?S")
      case True
      then have "J \<in> ?C"
        using w by simp
      then have Jset: "J \<in> set Is"
        using Is(1) by blast
      then obtain i where i: "i < length Is" "Is ! i = J"
        by (auto simp: in_set_conv_nth)
      show ?thesis
        using roth_aux_matrix_kernel_taylor
          [OF monic d root dpos xcar Ax i(1)]
        by (simp add: Preal i(2))
    next
      case False
      show ?thesis
        using roth_aux_matrix_outside_taylor
          [OF monic d root Ksbox False]
        by (simp add: Preal)
    qed
  qed
  have Ppoint: "abs (MPoly_Type.coeff P K) \<le>
      2 * int (length Ks) * ?B" for K
  proof (cases "K \<in> ?S")
    case True
    then have Kset: "K \<in> set Ks"
      using Ks(1) by blast
    then obtain t where t: "t < length Ks" "Ks ! t = K"
      by (auto simp: in_set_conv_nth)
    have "MPoly_Type.coeff P K = x $ t"
      unfolding P_def using roth_aux_polynomial_coeff
        [OF Ks(2) t(1), of x] t by simp
    then show ?thesis using xpoint[OF t(1)] by simp
  next
    case False
    then have "MPoly_Type.coeff P K = 0"
      by (rule roth_coeff_zero_outside_box[OF Pbox])
    then show ?thesis using Bge by simp
  qed
  show ?thesis
    using Pnz Pbox Pindex Ppoint
    by (intro exI[of _ P]) (simp add: Kscard)
qed

corollary roth_auxiliary_polynomial_monic_exp:
  fixes f :: "int poly" and a :: real
  assumes monic: "Polynomial.lead_coeff f = 1"
    and d: "d = Polynomial.degree f"
    and dpos: "0 < d"
    and root: "poly (map_poly of_int f) a = 0"
    and mpos: "0 < m"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and epos: "0 < eps"
    and elt: "eps < 1"
    and gap: "2 * real d < real m * eps\<^sup>2"
  shows "\<exists>P :: int mpoly.
    P \<noteq> 0 \<and> roth_poly_in_box m r P \<and>
    ereal (real m * (1-eps) / 2) \<le>
      roth_index m r (\<lambda>_. a) (replace_coeff of_int P) \<and>
    (\<forall>K. abs (MPoly_Type.coeff P K) \<le>
      2 * (4 * roth_power_base f) ^ (\<Sum>v<m. r v))"
proof -
  let ?S = "roth_exponent_box m r"
  let ?R = "\<Sum>v<m. r v"
  let ?B = "(2 * roth_power_base f) ^ ?R"
  have q: "int (card ?S) \<le> (2::int) ^ ?R"
    using roth_exponent_box_card_exp_bound[of m r] by simp
  have Bnonneg: "0 \<le> ?B"
    using roth_power_base_ge_one[of f] by simp
  have qB: "int (card ?S) * ?B \<le> (2::int) ^ ?R * ?B"
    by (rule mult_right_mono[OF q Bnonneg])
  have pow_eq: "(2::int) ^ ?R * ?B =
      (4 * roth_power_base f) ^ ?R"
  proof -
    have "(2::int) ^ ?R * ?B =
        (2 * (2 * roth_power_base f)) ^ ?R"
      by (rule power_mult_distrib[symmetric])
    also have "\<dots> = (4 * roth_power_base f) ^ ?R"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have bound: "2 * int (card ?S) * ?B \<le>
      2 * (4 * roth_power_base f) ^ ?R"
  proof -
    have "2 * int (card ?S) * ?B =
        2 * (int (card ?S) * ?B)"
      by (simp add: mult.assoc)
    also have "\<dots> \<le> 2 * ((2::int) ^ ?R * ?B)"
      by (rule mult_left_mono[OF qB]) simp
    also have "\<dots> = 2 * (4 * roth_power_base f) ^ ?R"
      by (simp only: pow_eq)
    finally show ?thesis .
  qed
  obtain P :: "int mpoly" where P:
    "P \<noteq> 0" "roth_poly_in_box m r P"
    "ereal (real m * (1-eps) / 2) \<le>
      roth_index m r (\<lambda>_. a) (replace_coeff of_int P)"
    "\<forall>K. abs (MPoly_Type.coeff P K) \<le>
      2 * int (card ?S) * ?B"
    using roth_auxiliary_polynomial_monic
      [where f=f and a=a and d=d and m=m and r=r and eps=eps,
       OF monic d dpos root mpos rpos epos elt gap] by blast
  have Pbound: "\<forall>K. abs (MPoly_Type.coeff P K) \<le>
      2 * (4 * roth_power_base f) ^ ?R"
  proof
    fix K
    have "abs (MPoly_Type.coeff P K) \<le>
        2 * int (card ?S) * ?B"
      using P(4) by blast
    also note bound
    finally show "abs (MPoly_Type.coeff P K) \<le>
        2 * (4 * roth_power_base f) ^ ?R" .
  qed
  show ?thesis
    using P(1-3) Pbound by (intro exI[of _ P]) auto
qed

end
