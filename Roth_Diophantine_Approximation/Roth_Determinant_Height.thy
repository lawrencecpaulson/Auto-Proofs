theory Roth_Determinant_Height
  imports Roth_Determinant_Box
begin

section \<open>Integral representatives of Hasse determinants\<close>

lemma roth_hasse_cast:
  fixes P :: "int mpoly"
  shows "replace_coeff of_int (roth_hasse J P) =
    (roth_hasse J (replace_coeff of_int P) :: rat mpoly)"
  by (simp add: coeff_eq[symmetric] fun_eq_iff
    roth_hasse_coeff_exact coeff_replace_coeff)

lemma roth_hasse_smult:
  fixes P :: "rat mpoly"
  shows "roth_hasse J (MPoly_Type.smult c P) =
    MPoly_Type.smult c (roth_hasse J P)"
  by (simp add: coeff_eq[symmetric] fun_eq_iff
    roth_hasse_coeff_exact roth_coeff_smult_rat
    mult.assoc mult.left_commute)

lemma roth_det_cast:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> int mpoly"
  shows "replace_coeff of_int
    (det (mat k k (\<lambda>(i,j). A i j))) =
    (det (mat k k (\<lambda>(i,j).
      replace_coeff of_int (A i j))) :: rat mpoly)"
proof -
  interpret cast: comm_ring_hom
    "replace_coeff of_int :: int mpoly \<Rightarrow> rat mpoly"
    by (unfold_locales; simp add: roth_replace_coeff_zero
      roth_replace_coeff_one replace_coeff_add roth_replace_coeff_mult)
  have eq: "map_mat (replace_coeff of_int)
      (mat k k (\<lambda>(i,j). A i j)) =
    mat k k (\<lambda>(i,j). replace_coeff of_int (A i j))"
    by (simp add: mat_eq_iff)
  show ?thesis
    using cast.hom_det[of "mat k k (\<lambda>(i,j). A i j)"] eq
    by metis
qed

lemma roth_det_smult:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat mpoly"
  shows "det (mat k k (\<lambda>(i,j).
      MPoly_Type.smult c (A i j))) =
    MPoly_Type.smult (c^k)
      (det (mat k k (\<lambda>(i,j). A i j)))"
proof -
  have eq: "mat k k (\<lambda>(i,j). MPoly_Type.smult c (A i j)) =
    (Const c) \<cdot>\<^sub>m (mat k k (\<lambda>(i,j). A i j))"
    by (simp add: mat_eq_iff smult_conv_mult roth_Const_monom)
  have deteq: "det (mat k k (\<lambda>(i,j).
      MPoly_Type.smult c (A i j))) =
    det ((Const c) \<cdot>\<^sub>m
      (mat k k (\<lambda>(i,j). A i j)))"
    using eq by simp
  also have "det ((Const c) \<cdot>\<^sub>m
      (mat k k (\<lambda>(i,j). A i j))) =
    (Const c)^k * det (mat k k (\<lambda>(i,j). A i j))"
    by simp
  also have "\<dots> =
    MPoly_Type.smult (c^k)
      (det (mat k k (\<lambda>(i,j). A i j)))"
    by (simp only: roth_Const_power smult_conv_mult
      roth_Const_monom[symmetric])
  finally show ?thesis .
qed

lemma roth_hasse_det_rep:
  fixes P :: "rat mpoly" and Q :: "int mpoly"
  assumes rep: "roth_integral_rep P Q"
  shows "roth_integral_rep
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P)))
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) Q)))"
proof -
  obtain c :: rat where cn: "c \<noteq> 0"
    and eq: "replace_coeff of_int Q = MPoly_Type.smult c P"
    using rep by (auto simp: roth_integral_rep_def)
  have heq: "replace_coeff of_int
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) Q))) =
    MPoly_Type.smult (c^k)
      (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P)))"
    by (simp add: roth_det_cast roth_hasse_cast eq
      roth_hasse_smult roth_det_smult)
  show ?thesis unfolding roth_integral_rep_def
    by (rule exI[of _ "c^k"]) (use cn heq in simp)
qed

lemma roth_proj_height_hasse_det_le:
  fixes P :: "rat mpoly" and Q :: "int mpoly"
  assumes rep: "roth_integral_rep P Q"
  shows "roth_proj_height
      (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) \<le>
    roth_int_coeff_sup
      (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) Q)))"
  by (rule roth_proj_height_le[OF roth_hasse_det_rep[OF rep]])

section \<open>Coefficient bounds for one Hasse derivative\<close>

lemma roth_int_coeff_sup_le:
  fixes P :: "int mpoly"
  assumes h1: "1 \<le> H"
    and hc: "\<And>I. nat (abs (MPoly_Type.coeff P I)) \<le> H"
  shows "roth_int_coeff_sup P \<le> H"
  using h1 hc
  by (auto simp: roth_int_coeff_sup_def roth_coeffs_eq Max_le_iff)

lemma roth_hasse_coeff_sup:
  fixes P :: "int mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "roth_int_coeff_sup (roth_hasse J P) \<le>
    2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P"
proof (rule roth_int_coeff_sup_le)
  show "1 \<le> 2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P"
    using roth_int_coeff_sup_ge_one[of P] by simp
  fix I
  have b: "abs (MPoly_Type.coeff (roth_hasse J P) I) \<le>
    int (2 ^ (\<Sum>v<m. r v)) *
      abs (MPoly_Type.coeff P (I+J))"
    by (rule roth_hasse_coeff_bound[OF box])
  have h: "nat (abs (MPoly_Type.coeff P (I+J))) \<le>
    roth_int_coeff_sup P"
    by (rule roth_int_coeff_sup_coeff)
  have hp: "abs (MPoly_Type.coeff P (I+J)) \<le>
    int (roth_int_coeff_sup P)"
    using h by simp
  have bd: "abs (MPoly_Type.coeff (roth_hasse J P) I) \<le>
    int (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P)"
    using b hp by (intro order.trans[OF b] mult_left_mono) auto
  show "nat (abs (MPoly_Type.coeff (roth_hasse J P) I)) \<le>
    2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P"
    using bd by (metis nat_int nat_mono)
qed

section \<open>Boxed primitive representatives\<close>

lemma roth_box_cast_iff:
  fixes Q :: "int mpoly"
  shows "roth_poly_in_box m r (replace_coeff of_int Q :: rat mpoly)
    \<longleftrightarrow> roth_poly_in_box m r Q"
proof -
  have key: "I \<in> Poly_Mapping.keys
      (mapping_of (replace_coeff of_int Q :: rat mpoly))
    \<longleftrightarrow> I \<in> Poly_Mapping.keys (mapping_of Q)" for I
    by (simp add: in_keys_iff coeff_def[symmetric]
      coeff_replace_coeff)
  show ?thesis by (auto simp: roth_poly_in_box_def key)
qed

lemma roth_integral_rep_box:
  fixes P :: "rat mpoly" and Q :: "int mpoly"
  assumes box: "roth_poly_in_box m r P"
    and rep: "roth_integral_rep P Q"
  shows "roth_poly_in_box m r Q"
proof -
  obtain c :: rat where eq:
    "replace_coeff of_int Q = MPoly_Type.smult c P"
    using rep by (auto simp: roth_integral_rep_def)
  have qb: "roth_poly_in_box m r
      (replace_coeff of_int Q :: rat mpoly)"
    using box eq by (simp add: roth_box_smult)
  show ?thesis using qb by (simp add: roth_box_cast_iff)
qed

lemma roth_box_primitive_rep:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and nz: "P \<noteq> 0"
  shows "\<exists>Q::int mpoly.
    roth_integral_rep P Q \<and> Q \<noteq> 0 \<and>
    MPoly_Type.primitive Q \<and> roth_poly_in_box m r Q \<and>
    roth_proj_height P = roth_int_coeff_sup Q"
  using roth_primitive_rep_exists[OF nz] box nz
  by (auto intro: roth_integral_rep_box
    roth_proj_height_primitive_rep)

end
