theory Roth_Determinant_Coeff
  imports Roth_Determinant_Height
begin

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

end
