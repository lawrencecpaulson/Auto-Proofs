theory Roth_Kronecker_Evaluation
  imports Roth_Kronecker_Expansion
begin

section \<open>Evaluation of Kronecker substitution\<close>

lemma roth_insertion_Const:
  fixes c :: rat and f :: "nat \<Rightarrow> rat"
  shows "insertion f (Const c) = c"
  by (simp add: roth_Const_monom[symmetric]
    insertion_single[of f 0 0 c])

lemma roth_insertion_Var:
  fixes f :: "nat \<Rightarrow> rat"
  shows "insertion f (Var v) = f v"
  by (simp add: roth_Var_monom insertion_single)

lemma roth_monom_var_prod:
  fixes c :: rat
  shows "MPoly_Type.monom I c =
    Const c *
      (\<Prod>v\<in>Poly_Mapping.keys I. Var v ^ Poly_Mapping.lookup I v)"
  using roth_hasse_monom_product[of 0 I c] by simp

lemma roth_insertion_prod:
  fixes f :: "nat \<Rightarrow> rat" and P :: "'a \<Rightarrow> rat mpoly"
  assumes "finite S"
  shows "insertion f (\<Prod>v\<in>S. P v) =
    (\<Prod>v\<in>S. insertion f (P v))"
  using assms by (induction S rule: finite_induct)
    (simp_all add: insertion_mult)

lemma roth_insertion_power:
  fixes f :: "nat \<Rightarrow> rat" and P :: "rat mpoly"
  shows "insertion f (P^n) = insertion f P ^ n"
  by (induction n) (simp_all add: power_Suc insertion_mult)

lemma roth_insertion_monom:
  fixes c :: rat and f :: "nat \<Rightarrow> rat"
  shows "insertion f (MPoly_Type.monom I c) =
    c * (\<Prod>v\<in>Poly_Mapping.keys I.
      f v ^ Poly_Mapping.lookup I v)"
  by (simp add: roth_monom_var_prod insertion_mult
    roth_insertion_Const roth_insertion_prod
    roth_insertion_power roth_insertion_Var)

lemma roth_kronecker_keys:
  assumes h: "Poly_Mapping.keys I \<subseteq> {..<m}"
  shows "roth_kronecker m B I =
    (\<Sum>v\<in>Poly_Mapping.keys I. Poly_Mapping.lookup I v * B^v)"
proof -
  have z: "\<forall>v\<in>{..<m} - Poly_Mapping.keys I.
    Poly_Mapping.lookup I v * B^v = 0"
    by (simp add: not_in_keys_iff_lookup_eq_zero)
  have eq: "(\<Sum>v\<in>Poly_Mapping.keys I.
      Poly_Mapping.lookup I v * B^v) =
    (\<Sum>v<m. Poly_Mapping.lookup I v * B^v)"
    by (rule sum.mono_neutral_left[OF _ h z]) simp
  show ?thesis using eq
    by (simp add: roth_kronecker_def roth_digits_def)
qed

lemma roth_power_swap:
  fixes t :: rat
  shows "(t^a)^b = (t^b)^a"
  by (simp add: power_mult[symmetric] mult.commute)

lemma roth_kronecker_power_prod:
  fixes t :: rat
  shows "(\<Prod>v\<in>S. (t^(B^v))^(Poly_Mapping.lookup I v)) =
    t^(\<Sum>v\<in>S. Poly_Mapping.lookup I v * B^v)"
  by (simp add: power_sum roth_power_swap power_mult[symmetric])

lemma roth_insertion_kronecker_monom:
  fixes c t :: rat
  assumes supp: "Poly_Mapping.keys I \<subseteq> {..<m}"
  shows "insertion (\<lambda>v. t^(B^v)) (MPoly_Type.monom I c) =
    c * t^(roth_kronecker m B I)"
  by (simp add: roth_insertion_monom roth_kronecker_keys[OF supp]
    roth_kronecker_power_prod)

lemma roth_insertion_sum:
  fixes f :: "nat \<Rightarrow> rat" and P :: "'a \<Rightarrow> rat mpoly"
  assumes "finite S"
  shows "insertion f (\<Sum>x\<in>S. P x) =
    (\<Sum>x\<in>S. insertion f (P x))"
  using assms by (induction S rule: finite_induct)
    (simp_all add: insertion_add)

lemma roth_insertion_monom_sum:
  fixes P :: "rat mpoly"
  shows "insertion f P =
    (\<Sum>I\<in>Poly_Mapping.keys (mapping_of P).
      insertion f (MPoly_Type.monom I (MPoly_Type.coeff P I)))"
  using roth_sum_monom[of P]
    roth_insertion_sum[of "Poly_Mapping.keys (mapping_of P)"
      f "\<lambda>I. MPoly_Type.monom I (MPoly_Type.coeff P I)"]
  by simp

lemma roth_poly_ksubst_eval_sum:
  fixes P :: "rat mpoly"
  shows "poly (roth_ksubst m B P) t =
    (\<Sum>I\<in>Poly_Mapping.keys (mapping_of P).
      MPoly_Type.coeff P I * t^(roth_kronecker m B I))"
  by (simp add: roth_ksubst_def poly_sum poly_monom)

lemma roth_box_monom_support:
  assumes box: "roth_poly_in_box m r P"
    and I: "I\<in>Poly_Mapping.keys (mapping_of P)"
  shows "Poly_Mapping.keys I \<subseteq> {..<m}"
  using box I
  by (auto simp: roth_poly_in_box_def
    dest: roth_exponent_boxD(1))

lemma roth_box_support_all:
  assumes box: "roth_poly_in_box m r P"
  shows "\<forall>I\<in>Poly_Mapping.keys (mapping_of P).
    Poly_Mapping.keys I \<subseteq> {..<m}"
  using box by (auto dest: roth_box_monom_support)

lemma roth_ksubst_eval_insertion:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "poly (roth_ksubst m B P) t =
    insertion (\<lambda>v. t^(B^v)) P"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of P)"
  have s: "\<forall>I\<in>?S. Poly_Mapping.keys I \<subseteq> {..<m}"
    by (rule roth_box_support_all[OF box])
  have a: "poly (roth_ksubst m B P) t =
    (\<Sum>I\<in>?S. MPoly_Type.coeff P I * t^(roth_kronecker m B I))"
    by (rule roth_poly_ksubst_eval_sum)
  have b: "insertion (\<lambda>v. t^(B^v)) P =
    (\<Sum>I\<in>?S. insertion (\<lambda>v. t^(B^v))
      (MPoly_Type.monom I (MPoly_Type.coeff P I)))"
    by (rule roth_insertion_monom_sum)
  have c: "(\<Sum>I\<in>?S. insertion (\<lambda>v. t^(B^v))
      (MPoly_Type.monom I (MPoly_Type.coeff P I))) =
    (\<Sum>I\<in>?S. MPoly_Type.coeff P I * t^(roth_kronecker m B I))"
  proof (rule sum.cong)
    show "?S = ?S" by simp
    fix I
    assume i: "I\<in>?S"
    have "Poly_Mapping.keys I \<subseteq> {..<m}"
      using s i by blast
    then show "insertion (\<lambda>v. t^(B^v))
        (MPoly_Type.monom I (MPoly_Type.coeff P I)) =
      MPoly_Type.coeff P I * t^(roth_kronecker m B I)"
      by (rule roth_insertion_kronecker_monom)
  qed
  show ?thesis using a b c by simp
qed

lemma roth_mpoly_neg_one:
  "(-1::rat mpoly) = Const (-1::rat)"
  by (simp add: roth_Const_uminus)

lemma roth_insertion_signof:
  fixes f :: "nat \<Rightarrow> rat"
  shows "insertion f (signof q :: rat mpoly) = (signof q :: rat)"
  by (simp add: sign_def roth_mpoly_neg_one roth_insertion_Const)

lemma roth_insertion_det:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat mpoly"
    and f :: "nat \<Rightarrow> rat"
  shows "insertion f (det (mat k k (\<lambda>(i,j). A i j))) =
    det (mat k k (\<lambda>(i,j). insertion f (A i j)))"
proof -
  let ?S = "{q. q permutes {..<k}}"
  have fin: "finite ?S" by (rule finite_permutations) simp
  have a: "insertion f (det (mat k k (\<lambda>(i,j). A i j))) =
    (\<Sum>q\<in>?S. (signof q :: rat) *
      (\<Prod>i<k. insertion f (A i (q i))))"
    by (simp add: roth_det_mat_expansion
      roth_insertion_sum[OF fin] insertion_mult
      roth_insertion_signof roth_insertion_prod)
  have b: "det (mat k k (\<lambda>(i,j). insertion f (A i j))) =
    (\<Sum>q\<in>?S. (signof q :: rat) *
      (\<Prod>i<k. insertion f (A i (q i))))"
    by (simp add: roth_det_mat_expansion)
  show ?thesis using a b by simp
qed

end
