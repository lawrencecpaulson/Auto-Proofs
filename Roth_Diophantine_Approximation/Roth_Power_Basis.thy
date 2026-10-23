theory Roth_Power_Basis
  imports Roth_Index_Count Roth_Integral_Reduction
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

end
