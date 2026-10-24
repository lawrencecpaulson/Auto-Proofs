theory Roth_Determinant_Box
  imports Roth_Tensor_Indexed
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

end
