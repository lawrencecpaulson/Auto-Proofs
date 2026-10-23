theory Roth_Auxiliary_Matrix
  imports Roth_Power_Basis
begin

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

end
