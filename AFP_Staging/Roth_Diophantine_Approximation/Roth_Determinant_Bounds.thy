theory Roth_Determinant_Bounds
  imports
    Tensor_Indexed
    Roth_Index_Count
begin

lemma roth_exponent_box_add:
  assumes a: "A \<in> roth_exponent_box m r"
    and b: "B \<in> roth_exponent_box m s"
  shows "A+B \<in> roth_exponent_box m (\<lambda>v. r v+s v)"
proof (rule roth_exponent_boxI)
  show "Poly_Mapping.keys (A+B) \<subseteq> {..<m}"
    by (rule subset_trans[OF Poly_Mapping.keys_add])
      (use roth_exponent_boxD(1)[OF a] roth_exponent_boxD(1)[OF b] in auto)
  fix v assume vm: "v<m"
  have av: "Poly_Mapping.lookup A v \<le> r v"
    by (rule roth_exponent_boxD(2)[OF a vm])
  have bv: "Poly_Mapping.lookup B v \<le> s v"
    by (rule roth_exponent_boxD(2)[OF b vm])
  show "Poly_Mapping.lookup (A+B) v \<le> r v+s v"
    using av bv by (simp add: lookup_add)
qed

lemma roth_box_mult:
  fixes P Q :: "rat mpoly"
  assumes pb: "roth_poly_in_box m r P"
    and qb: "roth_poly_in_box m s Q"
  shows "roth_poly_in_box m (\<lambda>v. r v+s v) (P*Q)"
proof -
  have h: "\<forall>I\<in>Poly_Mapping.keys (mapping_of (P*Q)).
      I\<in>roth_exponent_box m (\<lambda>v. r v+s v)"
  proof (intro ballI)
    fix I
    assume ik: "I\<in>Poly_Mapping.keys (mapping_of (P*Q))"
    have ikk: "I\<in>Poly_Mapping.keys (mapping_of P * mapping_of Q)"
      using ik by (simp add: times_mpoly.rep_eq)
    obtain A B where e: "I=A+B"
      and ak: "A\<in>Poly_Mapping.keys (mapping_of P)"
      and bk: "B\<in>Poly_Mapping.keys (mapping_of Q)"
      using ikk keys_mult by blast
    have a: "A\<in>roth_exponent_box m r"
      using pb ak by (auto simp: roth_poly_in_box_def)
    have b: "B\<in>roth_exponent_box m s"
      using qb bk by (auto simp: roth_poly_in_box_def)
    show "I\<in>roth_exponent_box m (\<lambda>v. r v+s v)"
      using roth_exponent_box_add[OF a b] e by simp
  qed
  show ?thesis using h by (auto simp: roth_poly_in_box_def)
qed

lemma roth_box_one:
  "roth_poly_in_box m (\<lambda>_. 0) (1::rat mpoly)"
  by (simp add: roth_poly_in_box_iff_degree)

lemma roth_box_prod:
  fixes P :: "'a \<Rightarrow> rat mpoly"
  assumes fin: "finite S"
    and box: "\<And>x. x\<in>S \<Longrightarrow> roth_poly_in_box m r (P x)"
  shows "roth_poly_in_box m (\<lambda>v. card S * r v) (\<Prod>x\<in>S. P x)"
  using fin box
proof (induction S rule: finite_induct)
  case empty
  then show ?case by (simp add: roth_box_one)
next
  case (insert x S)
  have pb: "roth_poly_in_box m r (P x)"
    using insert.prems by simp
  have sb: "roth_poly_in_box m (\<lambda>v. card S * r v) (\<Prod>x\<in>S. P x)"
    using insert.IH insert.prems by auto
  have mb: "roth_poly_in_box m (\<lambda>v. r v + card S * r v)
    (P x * (\<Prod>x\<in>S. P x))"
    by (rule roth_box_mult[OF pb sb])
  show ?case using mb insert.hyps by (simp add: algebra_simps)
qed

lemma roth_box_uminus:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "roth_poly_in_box m r (-P)"
  using box
  by (simp add: roth_poly_in_box_def MPoly_Type.uminus_mpoly.rep_eq)

lemma roth_box_sign_mult:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "roth_poly_in_box m r (signof q * P)"
  using box by (simp add: sign_def roth_box_uminus)

lemma roth_box_det:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>i<k. \<forall>j<k. roth_poly_in_box m r (A i j)"
  shows "roth_poly_in_box m (\<lambda>v. k*r v)
    (det (mat k k (\<lambda>(i,j). A i j)))"
  unfolding roth_det_mat_expansion
proof (rule roth_poly_in_box_sum)
  show "finite {q. q permutes {..<k}}"
    by (rule finite_permutations) simp
  fix q assume q: "q \<in> {q. q permutes {..<k}}"
  have qb0: "roth_poly_in_box m (\<lambda>v. card {..<k}*r v)
      (\<Prod>i<k. A i (q i))"
    by (rule roth_box_prod)
      (use box q in \<open>auto simp: roth_permutes_bounded\<close>)
  have qb: "roth_poly_in_box m (\<lambda>v. k*r v)
      (\<Prod>i<k. A i (q i))"
    using qb0 by simp
  show "roth_poly_in_box m (\<lambda>v. k*r v)
      (signof q * (\<Prod>i<k. A i (q i)))"
    by (rule roth_box_sign_mult[OF qb])
qed

lemma roth_hasse_det_in_box:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "roth_poly_in_box m (\<lambda>v. k*r v)
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P)))"
  by (rule roth_box_det)
    (use box in \<open>auto intro: roth_hasse_box_monotone\<close>)

lemma roth_hasse_det_degree:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and vm: "v<m"
  shows "MPoly_Type.degree
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) v
    \<le> k*r v"
  by (rule roth_degree_le_of_box[OF roth_hasse_det_in_box[OF box] vm])

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

lemma roth_poly_sum_coeff_bound:
  fixes P :: "'x \<Rightarrow> int mpoly"
  assumes fin: "finite S"
    and hb: "\<And>x. x\<in>S \<Longrightarrow> abs (MPoly_Type.coeff (P x) I) \<le> int H"
  shows "abs (MPoly_Type.coeff (\<Sum>x\<in>S. P x) I) \<le> int (card S * H)"
  using fin hb
proof (induction S rule: finite_induct)
  case empty
  then show ?case by (simp add: coeff_def zero_mpoly.rep_eq)
next
  case (insert x S)
  have ax: "abs (MPoly_Type.coeff (P x) I) \<le> int H"
    using insert.prems[of x] by simp
  have sr: "abs (MPoly_Type.coeff (\<Sum>y\<in>S. P y) I) \<le>
    int (card S * H)"
    using insert.IH insert.prems by auto
  show ?case using ax sr insert.hyps
    by (simp add: More_MPoly_Type.coeff_add[symmetric] abs_le_iff)
qed

lemma roth_prod_monom_general:
  fixes a :: "'x \<Rightarrow> int"
    and E :: "'x \<Rightarrow> (nat,nat) poly_mapping"
  assumes fin: "finite S"
  shows "(\<Prod>x\<in>S. MPoly_Type.monom (E x) (a x)) =
    MPoly_Type.monom (\<Sum>x\<in>S. E x) (\<Prod>x\<in>S. a x)"
  using fin by (induction S rule: finite_induct)
    (simp_all add: MPoly_Type.mult_monom roth_Const_monom[symmetric])

lemma roth_monom_sum_coeff_bound:
  fixes a :: "'x \<Rightarrow> int"
    and E :: "'x \<Rightarrow> (nat,nat) poly_mapping"
  assumes fin: "finite S"
    and ab: "\<And>x. x\<in>S \<Longrightarrow> abs (a x) \<le> int H"
  shows "abs (MPoly_Type.coeff
    (\<Sum>x\<in>S. MPoly_Type.monom (E x) (a x)) I) \<le>
    int (card S * H)"
  using fin ab
proof (induction S rule: finite_induct)
  case empty
  then show ?case by (simp add: coeff_def zero_mpoly.rep_eq)
next
  case (insert x S)
  have ax: "abs (MPoly_Type.coeff (MPoly_Type.monom (E x) (a x)) I) \<le> int H"
    using insert.prems[of x] by (simp add: More_MPoly_Type.coeff_monom when_def)
  have sr: "abs (MPoly_Type.coeff
    (\<Sum>y\<in>S. MPoly_Type.monom (E y) (a y)) I) \<le>
    int (card S * H)"
    using insert.IH insert.prems by auto
  show ?case using ax sr insert.hyps
    by (simp add: More_MPoly_Type.coeff_add[symmetric] abs_le_iff)
qed

lemma roth_prod_monom_sum:
  fixes a :: "'x \<Rightarrow> 'y \<Rightarrow> int"
    and E :: "'x \<Rightarrow> 'y \<Rightarrow> (nat,nat) poly_mapping"
  assumes finS: "finite S" and finB: "finite B"
  shows "(\<Prod>x\<in>S. \<Sum>y\<in>B. MPoly_Type.monom (E x y) (a x y)) =
    (\<Sum>g\<in>PiE S (\<lambda>_. B).
      MPoly_Type.monom (\<Sum>x\<in>S. E x (g x))
        (\<Prod>x\<in>S. a x (g x)))"
proof -
  have "(\<Prod>x\<in>S. \<Sum>y\<in>B. MPoly_Type.monom (E x y) (a x y)) =
    (\<Sum>g\<in>PiE S (\<lambda>_. B).
      \<Prod>x\<in>S. MPoly_Type.monom (E x (g x)) (a x (g x)))"
    by (rule prod_sum_PiE) (use finS finB in auto)
  also have "... = (\<Sum>g\<in>PiE S (\<lambda>_. B).
      MPoly_Type.monom (\<Sum>x\<in>S. E x (g x))
        (\<Prod>x\<in>S. a x (g x)))"
    by (rule sum.cong) (use finS in \<open>auto simp: roth_prod_monom_general\<close>)
  finally show ?thesis .
qed

lemma roth_prod_monom_sum_bound:
  fixes a :: "'x \<Rightarrow> 'y \<Rightarrow> int"
    and E :: "'x \<Rightarrow> 'y \<Rightarrow> (nat,nat) poly_mapping"
  assumes finS: "finite S" and finB: "finite B"
    and hb: "\<And>x y. x\<in>S \<Longrightarrow> y\<in>B \<Longrightarrow> abs (a x y) \<le> int H"
  shows "abs (MPoly_Type.coeff
    (\<Prod>x\<in>S. \<Sum>y\<in>B. MPoly_Type.monom (E x y) (a x y)) I) \<le>
    int (card (PiE S (\<lambda>_. B)) * H ^ card S)"
proof -
  have bound: "abs (\<Prod>x\<in>S. a x (g x)) \<le> int (H ^ card S)"
    if g: "g\<in>PiE S (\<lambda>_. B)" for g
  proof -
    have "abs (\<Prod>x\<in>S. a x (g x)) = (\<Prod>x\<in>S. abs (a x (g x)))"
      by (simp add: abs_prod)
    also have "... \<le> (\<Prod>x\<in>S. int H)"
      by (rule prod_mono) (use g hb in auto)
    also have "... = int (H ^ card S)" by simp
    finally show ?thesis .
  qed
  have eq: "(\<Prod>x\<in>S. \<Sum>y\<in>B. MPoly_Type.monom (E x y) (a x y)) =
    (\<Sum>g\<in>PiE S (\<lambda>_. B).
      MPoly_Type.monom (\<Sum>x\<in>S. E x (g x))
        (\<Prod>x\<in>S. a x (g x)))"
    by (rule roth_prod_monom_sum[OF finS finB])
  show ?thesis unfolding eq
    by (rule roth_monom_sum_coeff_bound)
      (use finS finB bound in \<open>auto intro: finite_PiE\<close>)
qed

lemma roth_box_sum_monom:
  fixes P :: "int mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "P = (\<Sum>I\<in>roth_exponent_box m r.
    MPoly_Type.monom I (MPoly_Type.coeff P I))"
proof -
  have "P = (\<Sum>I\<in>Poly_Mapping.keys (mapping_of P).
      MPoly_Type.monom I (MPoly_Type.coeff P I))"
    by (rule roth_sum_monom)
  also have "... = (\<Sum>I\<in>roth_exponent_box m r.
      MPoly_Type.monom I (MPoly_Type.coeff P I))"
  proof (rule sum.mono_neutral_cong_left)
    show "finite (roth_exponent_box m r)" by simp
    show "Poly_Mapping.keys (mapping_of P) \<subseteq>
        roth_exponent_box m r"
      using box by (simp add: roth_poly_in_box_def)
    show "\<forall>I\<in>roth_exponent_box m r -
      Poly_Mapping.keys (mapping_of P).
      MPoly_Type.monom I (MPoly_Type.coeff P I) = 0"
      by (simp add: coeff_keys mapping_of_inject[symmetric] mapping_of_monom zero_mpoly.rep_eq)
  qed simp
  finally show ?thesis .
qed

lemma roth_box_prod_coeff_bound:
  fixes P :: "'x \<Rightarrow> int mpoly"
  assumes fin: "finite S"
    and box: "\<And>x. x\<in>S \<Longrightarrow> roth_poly_in_box m r (P x)"
    and hb: "\<And>x. x\<in>S \<Longrightarrow> roth_int_coeff_sup (P x) \<le> H"
  shows "abs (MPoly_Type.coeff (\<Prod>x\<in>S. P x) I) \<le>
    int (card (roth_exponent_box m r) ^ card S * H ^ card S)"
proof -
  let ?B = "roth_exponent_box m r"
  have pb: "P x = (\<Sum>y\<in>?B. MPoly_Type.monom y (MPoly_Type.coeff (P x) y))"
    if "x\<in>S" for x
    by (rule roth_box_sum_monom[OF box[OF that]])
  have ab: "abs (MPoly_Type.coeff (P x) y) \<le> int H"
    if xs: "x\<in>S" for x y
  proof -
    have a: "nat (abs (MPoly_Type.coeff (P x) y)) \<le> roth_int_coeff_sup (P x)"
      by (rule roth_int_coeff_sup_coeff)
    have "abs (MPoly_Type.coeff (P x) y) \<le>
      int (roth_int_coeff_sup (P x))" using a by simp
    also have "... \<le> int H" using hb[OF xs] by simp
    finally show ?thesis .
  qed
  have eq: "(\<Prod>x\<in>S. P x) =
    (\<Prod>x\<in>S. \<Sum>y\<in>?B. MPoly_Type.monom y (MPoly_Type.coeff (P x) y))"
    by (rule prod.cong) (use pb in auto)
  have bd: "abs (MPoly_Type.coeff
    (\<Prod>x\<in>S. \<Sum>y\<in>?B. MPoly_Type.monom y (MPoly_Type.coeff (P x) y)) I) \<le>
    int (card (PiE S (\<lambda>_. ?B)) * H ^ card S)"
    by (rule roth_prod_monom_sum_bound[OF fin]) (use ab in auto)
  show ?thesis using bd eq fin by (simp add: card_PiE)
qed

lemma roth_abs_coeff_signof:
  fixes P :: "int mpoly"
  shows "abs (MPoly_Type.coeff (signof q * P) I) =
    abs (MPoly_Type.coeff P I)"
  by (simp add: sign_def MPoly_Type.coeff_def
    MPoly_Type.uminus_mpoly.rep_eq)

lemma roth_box_card_pos:
  "0 < card (roth_exponent_box m r)"
proof -
  have z: "(0::(nat,nat) poly_mapping) \<in> roth_exponent_box m r"
    by (rule roth_exponent_boxI) simp_all
  show ?thesis using z by (auto simp: card_gt_0_iff)
qed

lemma roth_hasse_box_int:
  fixes P :: "int mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "roth_poly_in_box m r (roth_hasse J P)"
proof -
  have h: "roth_poly_in_box m
      (\<lambda>v. r v - Poly_Mapping.lookup J v) (roth_hasse J P)"
    by (rule roth_hasse_in_box[OF box])
  have mono: "roth_exponent_box m
      (\<lambda>v. r v - Poly_Mapping.lookup J v)
      \<subseteq> roth_exponent_box m r"
    by (auto simp: roth_exponent_box_iff)
      (meson le_trans diff_le_self)
  show ?thesis using h mono by (auto simp: roth_poly_in_box_def)
qed

lemma roth_det_coeff_bound:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> int mpoly"
  assumes box: "\<And>i j. i<k \<Longrightarrow> j<k \<Longrightarrow> roth_poly_in_box m r (A i j)"
    and hb: "\<And>i j. i<k \<Longrightarrow> j<k \<Longrightarrow> roth_int_coeff_sup (A i j) \<le> H"
  shows "abs (MPoly_Type.coeff (det (mat k k (\<lambda>(i,j). A i j))) I) \<le>
    int (fact k * (card (roth_exponent_box m r) * H)^k)"
proof -
  let ?B = "roth_exponent_box m r"
  let ?Q = "{q. q permutes {..<k}}"
  have fin: "finite ?Q" by (rule finite_permutations) simp
  have cq: "card ?Q = fact k"
    by (rule card_permutations) simp_all
  have term_bd: "abs (MPoly_Type.coeff
    (signof q * (\<Prod>i<k. A i (q i))) I) \<le>
    int ((card ?B * H)^k)" if "q\<in>?Q" for q
  proof -
    have prod: "abs (MPoly_Type.coeff (\<Prod>i<k. A i (q i)) I) \<le>
      int (card ?B ^ card {..<k} * H ^ card {..<k})"
      by (rule roth_box_prod_coeff_bound)
        (use that box hb in \<open>auto simp: roth_permutes_bounded\<close>)
    show ?thesis using prod
      by (simp add: roth_abs_coeff_signof power_mult_distrib)
  qed
  have all: "abs (MPoly_Type.coeff
    (\<Sum>q\<in>?Q. signof q * (\<Prod>i<k. A i (q i))) I) \<le>
    int (card ?Q * ((card ?B * H)^k))"
    by (rule roth_poly_sum_coeff_bound[OF fin term_bd])
  show ?thesis using all cq
    by (simp add: roth_det_mat_expansion)
qed

lemma roth_det_coeff_sup_bound:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> int mpoly"
  assumes box: "\<And>i j. i<k \<Longrightarrow> j<k \<Longrightarrow> roth_poly_in_box m r (A i j)"
    and hb: "\<And>i j. i<k \<Longrightarrow> j<k \<Longrightarrow> roth_int_coeff_sup (A i j) \<le> H"
    and hp: "1 \<le> H"
  shows "roth_int_coeff_sup (det (mat k k (\<lambda>(i,j). A i j))) \<le>
    fact k * (card (roth_exponent_box m r) * H)^k"
proof (rule roth_int_coeff_sup_le)
  show "1 \<le> fact k * (card (roth_exponent_box m r) * H)^k"
    using hp roth_box_card_pos[of m r] by simp
  fix I
  have b: "abs (MPoly_Type.coeff (det (mat k k (\<lambda>(i,j). A i j))) I) \<le>
    int (fact k * (card (roth_exponent_box m r) * H)^k)"
    by (rule roth_det_coeff_bound[OF box hb])
  show "nat (abs (MPoly_Type.coeff (det (mat k k (\<lambda>(i,j). A i j))) I)) \<le>
    fact k * (card (roth_exponent_box m r) * H)^k"
    using b by (metis nat_int nat_mono)
qed

lemma roth_hasse_det_coeff_sup:
  fixes Q :: "int mpoly"
  assumes box: "roth_poly_in_box m r Q"
  shows "roth_int_coeff_sup
      (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) Q))) \<le>
    fact k * (card (roth_exponent_box m r) *
      (2^(\<Sum>v<m. r v) * roth_int_coeff_sup Q))^k"
  by (rule roth_det_coeff_sup_bound)
    (use box roth_int_coeff_sup_ge_one[of Q] in
      \<open>auto intro: roth_hasse_box_int roth_hasse_coeff_sup\<close>)

lemma roth_box_scale_bound:
  assumes cb: "C \<le> (2::nat)^R"
  shows "C * (2^R * H) \<le> 4^R * H"
proof -
  have e: "(4::nat)^R = 2^R * 2^R"
  proof -
    have "(4::nat)^R = (2*2)^R" by simp
    also have "... = 2^R * 2^R" by (rule power_mult_distrib)
    finally show ?thesis .
  qed
  have "C * (2^R * H) \<le> 2^R * (2^R * H)"
    using cb by (intro mult_right_mono) auto
  then show ?thesis by (simp add: e algebra_simps)
qed

lemma roth_hasse_det_bound_card:
  fixes Q :: "int mpoly"
  assumes box: "roth_poly_in_box m r Q"
    and cb: "card (roth_exponent_box m r) \<le> 2^(\<Sum>v<m. r v)"
  shows "roth_int_coeff_sup
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) Q))) \<le>
    fact k * (4^(\<Sum>v<m. r v) * roth_int_coeff_sup Q)^k"
proof -
  have b: "roth_int_coeff_sup
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) Q))) \<le>
    fact k * (card (roth_exponent_box m r) *
      (2^(\<Sum>v<m. r v) * roth_int_coeff_sup Q))^k"
    by (rule roth_hasse_det_coeff_sup[OF box])
  have s: "card (roth_exponent_box m r) *
    (2^(\<Sum>v<m. r v) * roth_int_coeff_sup Q) \<le>
    4^(\<Sum>v<m. r v) * roth_int_coeff_sup Q"
    by (rule roth_box_scale_bound[OF cb])
  have p: "(card (roth_exponent_box m r) *
      (2^(\<Sum>v<m. r v) * roth_int_coeff_sup Q))^k \<le>
      (4^(\<Sum>v<m. r v) * roth_int_coeff_sup Q)^k"
    by (rule power_mono[OF s]) auto
  show ?thesis using b p by (intro order_trans[OF b] mult_left_mono) auto
qed

theorem roth_hasse_det_projective_bound_card:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and nz: "P \<noteq> 0"
    and cb: "card (roth_exponent_box m r) \<le>
      2^(\<Sum>v<m. r v)"
  shows "roth_proj_height
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) \<le>
    fact k * (4^(\<Sum>v<m. r v) * roth_proj_height P)^k"
proof -
  obtain Q :: "int mpoly" where
    rep: "roth_integral_rep P Q" and
    qb: "roth_poly_in_box m r Q" and
    hp: "roth_proj_height P = roth_int_coeff_sup Q"
    using roth_box_primitive_rep[OF box nz] by blast
  have a: "roth_proj_height
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) \<le>
    roth_int_coeff_sup
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) Q)))"
    by (rule roth_proj_height_hasse_det_le[OF rep])
  have b: "roth_int_coeff_sup
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) Q))) \<le>
    fact k * (4^(\<Sum>v<m. r v) * roth_int_coeff_sup Q)^k"
    by (rule roth_hasse_det_bound_card[OF qb cb])
  show ?thesis using a b hp by simp
qed

theorem roth_hasse_det_projective_bound:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and nz: "P \<noteq> 0"
  shows "roth_proj_height
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) \<le>
    fact k * (4^(\<Sum>v<m. r v) * roth_proj_height P)^k"
  by (rule roth_hasse_det_projective_bound_card
    [OF box nz roth_exponent_box_card_exp_bound])


section \<open>Logarithmic determinant height\<close>

lemma roth_log_det_arith:
  fixes A B :: nat
  assumes ap: "0<A" and bp: "0<B"
    and hb: "A \<le> fact k * (4^R * B)^k"
  shows "ln (real A) \<le>
    ln (real (fact k)) + real k * (real R * ln 4 + ln (real B))"
proof -
  have le: "(real A) \<le> real (fact k * (4^R * B)^k)"
    by (rule of_nat_mono[OF hb])
  have h: "ln (real A) \<le> ln (real (fact k * (4^R * B)^k))"
    by (rule ln_mono) (use ap le in auto)
  have e: "ln (real (fact k * (4^R * B)^k)) =
    ln (real (fact k)) + real k * (real R * ln 4 + ln (real B))"
    using bp by (simp add: ln_mult ln_realpow algebra_simps)
  show ?thesis using h e by simp
qed

theorem roth_hasse_det_log_bound_card:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and nz: "P \<noteq> 0"
    and cb: "card (roth_exponent_box m r) \<le> 2^(\<Sum>v<m. r v)"
  shows "roth_proj_log_height
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) \<le>
    ln (real (fact k)) + real k *
      (real (\<Sum>v<m. r v) * ln 4 + roth_proj_log_height P)"
proof -
  let ?V = "det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))"
  have vp: "0 < roth_proj_height ?V"
    using roth_proj_height_ge_one[of ?V] by linarith
  have pp: "0 < roth_proj_height P"
    using roth_proj_height_ge_one[of P] by linarith
  have hb: "roth_proj_height ?V \<le>
    fact k * (4^(\<Sum>v<m. r v) * roth_proj_height P)^k"
    by (rule roth_hasse_det_projective_bound_card[OF box nz cb])
  show ?thesis unfolding roth_proj_log_height_def
    by (rule roth_log_det_arith[OF vp pp hb])
qed

lemma roth_halving_sum:
  fixes r :: "nat \<Rightarrow> nat"
  assumes half: "\<And>v. Suc v < m \<Longrightarrow> 2 * r (Suc v) \<le> r v"
  shows "(\<Sum>v<m. r v) \<le> 2 * r 0"
  using half
proof (induction m arbitrary: r)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have tailhalf: "2 * (r \<circ> Suc) (Suc v) \<le> (r \<circ> Suc) v"
    if "Suc v < m" for v
    using Suc.prems[of "Suc v"] that by simp
  have tail: "(\<Sum>v<m. r (Suc v)) \<le> 2 * r (Suc 0)"
    using Suc.IH[of "r \<circ> Suc"] tailhalf by simp
  show ?case
  proof (cases "m=0")
    case True
    then show ?thesis by simp
  next
    case False
    have h: "2 * r (Suc 0) \<le> r 0"
      using Suc.prems[of 0] False by simp
    show ?thesis using tail h
      by (simp only: sum.lessThan_Suc_shift) 
  qed
qed

lemma roth_halving_first:
  fixes r :: "nat \<Rightarrow> nat"
  assumes half: "\<And>v. Suc v < m \<Longrightarrow> 2 * r (Suc v) \<le> r v"
    and vm: "v<m"
  shows "r v \<le> r 0"
  using vm
proof (induction v)
  case 0
  then show ?case by simp
next
  case (Suc v)
  have rv: "r v \<le> r 0" using Suc.IH Suc.prems by arith
  have h: "2 * r (Suc v) \<le> r v"
    by (rule half[OF Suc.prems])
  show ?case using rv h by arith
qed

lemma roth_fact_bound:
  assumes kn: "k \<le> Suc n" and sn: "Suc n \<le> (2::nat)^n"
  shows "fact k \<le> (2::nat)^(k*n)"
proof -
  have f: "fact k \<le> k^k"
    using fact_le_power[of k, where ?'a=nat] by simp
  have "k^k \<le> (2^n)^k"
    by (rule power_mono) (use kn sn in auto)
  also have "(2^n)^k = (2::nat)^(k*n)"
    by (simp add: power_mult[symmetric] mult.commute)
  finally show ?thesis using f by arith
qed

lemma roth_fact_log_bound:
  assumes h: "fact k \<le> (2::nat)^(k*n)"
  shows "ln (real (fact k)) \<le> real k * real n * ln 2"
proof -
  have hreal: "real (fact k) \<le> real ((2::nat)^(k*n))"
    by (rule of_nat_mono[OF h])
  have b: "ln (real (fact k)) \<le> ln (real ((2::nat)^(k*n)))"
    by (rule ln_mono) (use hreal in auto)
  show ?thesis using b
    by (simp add: ln_realpow algebra_simps)
qed

lemma roth_ln2_bound: "5 * ln (2::real) < 4"
proof -
  have h: "(1 + (4/5::real) / 3)^3 \<le> exp (4/5)"
    using exp_ge_one_plus_x_over_n_power_n[of 3 "(4/5::real)"] by simp
  have e: "2 < exp (4/5::real)"
    using h by (simp add: power3_eq_cube; linarith)
  have loge: "ln (2::real) < ln (exp (4/5))"
    by (rule ln_less_cancel_iff[THEN iffD2]) (use e in auto)
  have "ln (2::real) < 4/5"
    using loge by simp
  then show ?thesis by linarith
qed

lemma roth_log_det_sharp_arith:
  fixes A B :: nat
  assumes log_le: "ln (real A) \<le>
      ln (real (fact k)) + real k * (real R * ln 4 + ln (real B))"
    and R_le: "R \<le> 2 * r0"
    and fact_le: "fact k \<le> (2::nat)^(k*r0)"
  shows "ln (real A) \<le> real k * (ln (real B) + 4 * real r0)"
proof -
  have factlog: "ln (real (fact k)) \<le> real k * real r0 * ln 2"
    by (rule roth_fact_log_bound[OF fact_le])
  have ln4: "ln (4::real) = 2 * ln 2"
  proof -
    have "ln (4::real) = ln ((2::real)^2)" by simp
    also have "... = 2 * ln 2" by (simp only: ln_realpow)
    finally show ?thesis .
  qed
  have rlog: "real R * ln 4 \<le> 4 * real r0 * ln 2"
  proof -
    have "real R * ln 4 \<le> (2 * real r0) * ln 4"
      by (rule mult_right_mono) (use R_le in auto)
    also have "... = 4 * real r0 * ln 2"
      by (simp add: ln4 algebra_simps)
    finally show ?thesis .
  qed
  have five: "real r0 * (5 * ln 2) \<le> real r0 * 4"
    by (rule mult_left_mono) (use roth_ln2_bound in auto)
  have inner: "real r0 * ln 2 + real R * ln 4 \<le> 4 * real r0"
    using rlog five by (simp add: algebra_simps; linarith)
  have "ln (real A) \<le>
      ln (real (fact k)) + real k * (real R * ln 4 + ln (real B))"
    by (rule log_le)
  also have "... \<le> real k * real r0 * ln 2 +
      real k * (real R * ln 4 + ln (real B))"
    using factlog by simp
  also have "... = real k * (ln (real B) +
      (real r0 * ln 2 + real R * ln 4))"
    by (simp add: algebra_simps)
  also have "... \<le> real k * (ln (real B) + 4 * real r0)"
    by (intro mult_left_mono add_left_mono inner) simp
  finally show ?thesis .
qed

theorem roth_hasse_det_log_bound_sharp_card:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and nz: "P \<noteq> 0"
    and cb: "card (roth_exponent_box m r) \<le> 2^(\<Sum>v<m. r v)"
    and half: "\<And>v. Suc v < m \<Longrightarrow> 2 * r (Suc v) \<le> r v"
    and mp: "0<m"
    and kn: "k \<le> Suc (r (m-1))"
  shows "roth_proj_log_height
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) \<le>
    real k * (roth_proj_log_height P + 4 * real (r 0))"
proof -
  have last: "r (m-1) \<le> r 0"
    by (rule roth_halving_first[where r=r and m=m and v="m-1"])
      (use half mp in auto)
  have fb: "fact k \<le> (2::nat)^(k*r 0)"
    by (rule roth_fact_bound)
      (use kn last roth_suc_le_pow2 in auto)
  have logbd: "roth_proj_log_height
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) \<le>
    ln (real (fact k)) + real k *
      (real (\<Sum>v<m. r v) * ln 4 + roth_proj_log_height P)"
    by (rule roth_hasse_det_log_bound_card[OF box nz cb])
  have sumle: "(\<Sum>v<m. r v) \<le> 2 * r 0"
    by (rule roth_halving_sum[where r=r and m=m]) (rule half)
  show ?thesis unfolding roth_proj_log_height_def
    by (rule roth_log_det_sharp_arith
      [OF logbd[unfolded roth_proj_log_height_def] sumle fb])
qed

theorem roth_hasse_det_log_bound:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P" and nz: "P \<noteq> 0"
  shows "roth_proj_log_height
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) \<le>
    ln (real (fact k)) + real k *
      (real (\<Sum>v<m. r v) * ln 4 + roth_proj_log_height P)"
  by (rule roth_hasse_det_log_bound_card
    [OF box nz roth_exponent_box_card_exp_bound])

theorem roth_hasse_det_log_bound_sharp:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and nz: "P \<noteq> 0"
    and half: "\<And>v. Suc v < m \<Longrightarrow> 2 * r (Suc v) \<le> r v"
    and mp: "0<m"
    and kn: "k \<le> Suc (r (m-1))"
  shows "roth_proj_log_height
    (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) \<le>
    real k * (roth_proj_log_height P + 4 * real (r 0))"
  by (rule roth_hasse_det_log_bound_sharp_card
    [OF box nz roth_exponent_box_card_exp_bound half mp kn])

end
