theory Roth_Taylor_Evaluation
  imports Roth_Rational_Evaluation
begin

section \<open>Taylor evaluation and the triangle bound\<close>

lemma roth_insertion_Var_diff:
  fixes a b :: "nat \<Rightarrow> 'a::comm_ring_1"
  shows "insertion b (Var v - Const (a v)) = b v - a v"
proof -
  have eq: "Var v - Const (a v) = Var v + Const (-a v)"
    by (simp only: diff_conv_add_uminus roth_Const_uminus[symmetric])
  show ?thesis
    by (simp only: eq insertion_add roth_insertion_Var roth_insertion_Const)
      simp
qed

lemma roth_taylor_evaluation:
  fixes P :: "'a::comm_ring_1 mpoly"
  shows "insertion b P =
    (\<Sum>I\<in>Poly_Mapping.keys (mapping_of (roth_translate a P)).
      insertion a (roth_hasse I P) *
        (\<Prod>v\<in>Poly_Mapping.keys I.
          (b v - a v) ^ Poly_Mapping.lookup I v))"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of (roth_translate a P))"
  let ?T = "\<lambda>I. Const (insertion a (roth_hasse I P)) *
      (\<Prod>v\<in>Poly_Mapping.keys I.
        (Var v - Const (a v)) ^ Poly_Mapping.lookup I v)"
  have fin: "finite ?S" by simp
  have expansion: "P = (\<Sum>I\<in>?S. ?T I)"
    by (rule roth_taylor_identity_hasse)
  have eval: "insertion b P = (\<Sum>I\<in>?S. insertion b (?T I))"
    by (subst expansion) (rule roth_insertion_sum_any[OF fin])
  have each: "insertion b (?T I) = insertion a (roth_hasse I P) *
    (\<Prod>v\<in>Poly_Mapping.keys I.
      (b v - a v) ^ Poly_Mapping.lookup I v)" for I
    by (simp add: insertion_mult roth_insertion_prod_any
      roth_insertion_power_any roth_insertion_Var_diff)
  show ?thesis using eval by (simp add: each)
qed

lemma roth_taylor_evaluation_abs:
  fixes P :: "real mpoly"
  shows "abs (insertion b P) \<le>
    (\<Sum>I\<in>Poly_Mapping.keys (mapping_of (roth_translate a P)).
      abs (insertion a (roth_hasse I P)) *
        (\<Prod>v\<in>Poly_Mapping.keys I.
          abs (b v - a v) ^ Poly_Mapping.lookup I v))"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of (roth_translate a P))"
  have "abs (insertion b P) = abs
    (\<Sum>I\<in>?S. insertion a (roth_hasse I P) *
      (\<Prod>v\<in>Poly_Mapping.keys I.
        (b v - a v) ^ Poly_Mapping.lookup I v))"
    by (rule arg_cong[where f=abs]) (rule roth_taylor_evaluation)
  also have "... \<le> (\<Sum>I\<in>?S.
      abs (insertion a (roth_hasse I P) *
        (\<Prod>v\<in>Poly_Mapping.keys I.
          (b v - a v) ^ Poly_Mapping.lookup I v)))"
    by (rule sum_abs)
  also have "... = (\<Sum>I\<in>?S.
      abs (insertion a (roth_hasse I P)) *
        (\<Prod>v\<in>Poly_Mapping.keys I.
          abs (b v - a v) ^ Poly_Mapping.lookup I v))"
    by (simp add: abs_mult abs_prod power_abs)
  finally show ?thesis .
qed


section \<open>Bounds from balanced approximation heights\<close>

lemma roth_taylor_support_weight:
  fixes P :: "'a::comm_ring_1 mpoly"
  assumes lower: "ereal theta \<le> roth_index m r a P"
    and mem: "I \<in> Poly_Mapping.keys (mapping_of (roth_translate a P))"
  shows "theta \<le> roth_weight m r I"
proof -
  have coeff: "roth_taylor_coeff a I P \<noteq> 0"
    using mem by (simp add: roth_taylor_coeff_key)
  have upper: "roth_index m r a P \<le> ereal (roth_weight m r I)"
    by (rule roth_index_le_coeff[OF coeff])
  have "ereal theta \<le> ereal (roth_weight m r I)"
    by (rule order_trans[OF lower upper])
  then show ?thesis by simp
qed

lemma roth_taylor_uniform_bound:
  fixes P :: "real mpoly" and u :: "nat \<Rightarrow> real"
  assumes B: "0 \<le> B"
    and near: "\<And>v. abs (b v - a v) \<le> u v"
    and coeff: "\<And>I. I \<in> Poly_Mapping.keys (mapping_of (roth_translate a P))
      \<Longrightarrow> abs (insertion a (roth_hasse I P)) \<le> B"
  shows "abs (insertion b P) \<le> B *
    (\<Sum>I\<in>Poly_Mapping.keys (mapping_of (roth_translate a P)).
      (\<Prod>v\<in>Poly_Mapping.keys I. u v ^ Poly_Mapping.lookup I v))"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of (roth_translate a P))"
  have pow_bound: "abs (b v - a v) ^ n \<le> u v ^ n" for v n
    by (rule power_mono) (use near in auto)
  have prod_bound: "(\<Prod>v\<in>Poly_Mapping.keys I.
        abs (b v - a v) ^ Poly_Mapping.lookup I v) \<le>
      (\<Prod>v\<in>Poly_Mapping.keys I.
        u v ^ Poly_Mapping.lookup I v)" for I
    by (intro prod_mono) (use pow_bound in auto)
  have termbound: "abs (insertion a (roth_hasse I P)) *
      (\<Prod>v\<in>Poly_Mapping.keys I.
        abs (b v - a v) ^ Poly_Mapping.lookup I v) \<le>
      B * (\<Prod>v\<in>Poly_Mapping.keys I.
        u v ^ Poly_Mapping.lookup I v)" if "I \<in> ?S" for I
    by (intro mult_mono coeff[OF that] prod_bound prod_nonneg)
      (use B near in auto)
  have "abs (insertion b P) \<le>
    (\<Sum>I\<in>?S. abs (insertion a (roth_hasse I P)) *
      (\<Prod>v\<in>Poly_Mapping.keys I.
        abs (b v - a v) ^ Poly_Mapping.lookup I v))"
    by (rule roth_taylor_evaluation_abs)
  also have "... \<le> (\<Sum>I\<in>?S. B *
      (\<Prod>v\<in>Poly_Mapping.keys I.
        u v ^ Poly_Mapping.lookup I v))"
    by (intro sum_mono termbound)
  also have "... = B * (\<Sum>I\<in>?S.
      (\<Prod>v\<in>Poly_Mapping.keys I.
        u v ^ Poly_Mapping.lookup I v))"
    by (simp add: sum_distrib_left)
  finally show ?thesis .
qed

lemma roth_weight_height_balance:
  fixes h :: "nat \<Rightarrow> real"
  assumes rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
  shows "L * roth_weight m r I \<le>
    (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v)"
proof -
  have local: "L * (real (Poly_Mapping.lookup I v) / real (r v)) \<le>
      real (Poly_Mapping.lookup I v) * h v" if "v < m" for v
  proof -
    have div: "L / real (r v) \<le> h v"
      using rpos[OF that] balance[OF that]
      by (simp add: divide_le_eq mult.commute)
    have h: "real (Poly_Mapping.lookup I v) * (L / real (r v)) \<le>
      real (Poly_Mapping.lookup I v) * h v"
      by (rule mult_left_mono[OF div]) simp
    show ?thesis using h by (simp add: field_simps)
  qed
  have "(\<Sum>v<m. L * (real (Poly_Mapping.lookup I v) / real (r v))) \<le>
    (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v)"
  proof (rule sum_mono)
    fix v
    assume "v \<in> {..<m}"
    then have vm: "v < m" by simp
    show "L * (real (Poly_Mapping.lookup I v) / real (r v)) \<le>
      real (Poly_Mapping.lookup I v) * h v"
      by (rule local[OF vm])
  qed
  then show ?thesis
    by (simp add: roth_weight_def sum_distrib_left)
qed

lemma roth_error_product_exp:
  fixes h :: "nat \<Rightarrow> real"
  assumes keys: "Poly_Mapping.keys I \<subseteq> {..<m}"
  shows "(\<Prod>v\<in>Poly_Mapping.keys I.
      exp (-kappa * h v) ^ Poly_Mapping.lookup I v) =
    exp (-kappa * (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v))"
proof -
  have point: "exp (-kappa * h v) ^ Poly_Mapping.lookup I v =
      exp (-kappa * (real (Poly_Mapping.lookup I v) * h v))" for v
    by (simp add: exp_of_nat_mult[symmetric] algebra_simps)
  have support: "(\<Sum>v\<in>Poly_Mapping.keys I.
      real (Poly_Mapping.lookup I v) * h v) =
    (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v)"
    using keys by (intro sum.mono_neutral_left)
      (auto simp: not_in_keys_iff_lookup_eq_zero)
  have prod1: "(\<Prod>v\<in>Poly_Mapping.keys I.
      exp (-kappa * h v) ^ Poly_Mapping.lookup I v) =
    (\<Prod>v\<in>Poly_Mapping.keys I.
      exp (-kappa * (real (Poly_Mapping.lookup I v) * h v)))"
    by (intro prod.cong) (use point in auto)
  have prod2: "(\<Prod>v\<in>Poly_Mapping.keys I.
      exp (-kappa * (real (Poly_Mapping.lookup I v) * h v))) =
    exp (\<Sum>v\<in>Poly_Mapping.keys I.
      -kappa * (real (Poly_Mapping.lookup I v) * h v))"
    by (simp add: exp_sum)
  have sum_support: "(\<Sum>v\<in>Poly_Mapping.keys I.
      -kappa * (real (Poly_Mapping.lookup I v) * h v)) =
    (\<Sum>v<m. -kappa * (real (Poly_Mapping.lookup I v) * h v))"
    using keys by (intro sum.mono_neutral_left)
      (auto simp: not_in_keys_iff_lookup_eq_zero)
  have sum_fact: "(\<Sum>v<m. -kappa * (real (Poly_Mapping.lookup I v) * h v)) =
    -kappa * (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v)"
    by (simp add: sum_distrib_left)
  show ?thesis using prod1 prod2 sum_support sum_fact by simp
qed

lemma roth_error_product_weight:
  fixes h :: "nat \<Rightarrow> real"
  assumes keys: "Poly_Mapping.keys I \<subseteq> {..<m}"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa"
  shows "(\<Prod>v\<in>Poly_Mapping.keys I.
      exp (-kappa * h v) ^ Poly_Mapping.lookup I v) \<le>
    exp (-kappa * L * roth_weight m r I)"
proof -
  have bw: "L * roth_weight m r I \<le>
    (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v)"
    by (rule roth_weight_height_balance[OF rpos balance])
  have mult: "kappa * (L * roth_weight m r I) \<le>
      kappa * (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v)"
    by (rule mult_left_mono[OF bw kpos])
  have expl: "exp (-kappa *
      (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v)) \<le>
      exp (-kappa * L * roth_weight m r I)"
    using mult by (simp add: mult.assoc)
  have eq: "(\<Prod>v\<in>Poly_Mapping.keys I.
      exp (-kappa * h v) ^ Poly_Mapping.lookup I v) =
    exp (-kappa * (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v))"
    by (rule roth_error_product_exp[OF keys])
  show ?thesis using eq expl by simp
qed

lemma roth_error_product_index:
  fixes h :: "nat \<Rightarrow> real"
  assumes keys: "Poly_Mapping.keys I \<subseteq> {..<m}"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa" and Lpos: "0 \<le> L"
    and weight: "theta \<le> roth_weight m r I"
  shows "(\<Prod>v\<in>Poly_Mapping.keys I.
      exp (-kappa * h v) ^ Poly_Mapping.lookup I v) \<le>
    exp (-kappa * L * theta)"
proof -
  have e1: "(\<Prod>v\<in>Poly_Mapping.keys I.
      exp (-kappa * h v) ^ Poly_Mapping.lookup I v) \<le>
    exp (-kappa * L * roth_weight m r I)"
    by (rule roth_error_product_weight[OF keys rpos balance kpos])
  have nonneg: "0 \<le> kappa * L" using kpos Lpos by simp
  have mult: "kappa * L * theta \<le>
      kappa * L * roth_weight m r I"
    by (rule mult_left_mono[OF weight nonneg])
  have e2: "exp (-kappa * L * roth_weight m r I) \<le>
      exp (-kappa * L * theta)"
    using mult by simp
  show ?thesis using e1 e2 by (rule order_trans)
qed

theorem roth_taylor_exponential_bound:
  fixes P :: "real mpoly" and h :: "nat \<Rightarrow> real"
  assumes B: "0 \<le> B"
    and keys: "\<And>I. I \<in> Poly_Mapping.keys (mapping_of (roth_translate a P))
      \<Longrightarrow> Poly_Mapping.keys I \<subseteq> {..<m}"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa" and Lpos: "0 \<le> L"
    and index: "ereal theta \<le> roth_index m r a P"
    and near: "\<And>v. abs (b v - a v) \<le> exp (-kappa * h v)"
    and coeff: "\<And>I. I \<in> Poly_Mapping.keys (mapping_of (roth_translate a P))
      \<Longrightarrow> abs (insertion a (roth_hasse I P)) \<le> B"
  shows "abs (insertion b P) \<le>
    B * real (card (Poly_Mapping.keys (mapping_of (roth_translate a P)))) *
      exp (-kappa * L * theta)"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of (roth_translate a P))"
  let ?u = "\<lambda>v. exp (-kappa * h v)"
  let ?E = "exp (-kappa * L * theta)"
  have one: "abs (insertion b P) \<le>
      B * (\<Sum>I\<in>?S.
        (\<Prod>v\<in>Poly_Mapping.keys I.
          ?u v ^ Poly_Mapping.lookup I v))"
    by (rule roth_taylor_uniform_bound[where u="\<lambda>v. exp (-kappa * h v)"])
      (use B near coeff in auto)
  have mon: "(\<Prod>v\<in>Poly_Mapping.keys I.
          ?u v ^ Poly_Mapping.lookup I v) \<le> ?E"
    if "I \<in> ?S" for I
  proof -
    have wt: "theta \<le> roth_weight m r I"
      by (rule roth_taylor_support_weight[OF index that])
    show ?thesis
      by (rule roth_error_product_index[OF keys[OF that] rpos balance
        kpos Lpos wt])
  qed
  have sum_le: "(\<Sum>I\<in>?S.
        (\<Prod>v\<in>Poly_Mapping.keys I.
          ?u v ^ Poly_Mapping.lookup I v)) \<le> real (card ?S) * ?E"
  proof -
    have "(\<Sum>I\<in>?S.
        (\<Prod>v\<in>Poly_Mapping.keys I.
          ?u v ^ Poly_Mapping.lookup I v)) \<le> (\<Sum>I\<in>?S. ?E)"
      by (intro sum_mono) (use mon in auto)
    then show ?thesis by simp
  qed
  have two: "B * (\<Sum>I\<in>?S.
        (\<Prod>v\<in>Poly_Mapping.keys I.
          ?u v ^ Poly_Mapping.lookup I v)) \<le>
      B * (real (card ?S) * ?E)"
    by (rule mult_left_mono[OF sum_le B])
  show ?thesis using one two by (simp add: mult.assoc)
qed


lemma roth_taylor_support_keys_box:
  fixes P :: "real mpoly"
  assumes box: "roth_poly_in_box m r P"
    and mem: "I \<in> Poly_Mapping.keys (mapping_of (roth_translate a P))"
  shows "Poly_Mapping.keys I \<subseteq> {..<m}"
proof -
  have tc: "roth_taylor_coeff a I P \<noteq> 0"
    using mem by (simp add: roth_taylor_coeff_key)
  have ev: "insertion a (roth_hasse I P) \<noteq> 0"
    using tc by (simp add: roth_hasse_eval)
  have hn: "roth_hasse I P \<noteq> 0"
    using ev by auto
  then obtain K where ck: "MPoly_Type.coeff (roth_hasse I P) K \<noteq> 0"
    by (metis coeff_all_0)
  have cp: "MPoly_Type.coeff P (K + I) \<noteq> 0"
    by (rule roth_hasse_coeff_support[OF ck])
  have ki: "K + I \<in> roth_exponent_box m r"
    using box cp by (auto simp: roth_poly_in_box_def
      MPoly_Type.coeff_def in_keys_iff)
  have kis: "Poly_Mapping.keys (K + I) \<subseteq> {..<m}"
    by (rule roth_exponent_boxD(1)[OF ki])
  show ?thesis
  proof
    fix v
    assume vi: "v \<in> Poly_Mapping.keys I"
    have iv: "Poly_Mapping.lookup I v \<noteq> 0"
      using vi by (simp add: in_keys_iff)
    have kiv: "Poly_Mapping.lookup (K + I) v \<noteq> 0"
      using iv by (simp add: lookup_add)
    then have "v \<in> Poly_Mapping.keys (K + I)"
      by (simp add: in_keys_iff)
    then show "v \<in> {..<m}" using kis by auto
  qed
qed

corollary roth_taylor_exponential_bound_box:
  fixes P :: "real mpoly" and h :: "nat \<Rightarrow> real"
  assumes box: "roth_poly_in_box m r P"
    and B: "0 \<le> B"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa" and Lpos: "0 \<le> L"
    and index: "ereal theta \<le> roth_index m r a P"
    and near: "\<And>v. abs (b v - a v) \<le> exp (-kappa * h v)"
    and coeff: "\<And>I. I \<in> Poly_Mapping.keys (mapping_of (roth_translate a P))
      \<Longrightarrow> abs (insertion a (roth_hasse I P)) \<le> B"
  shows "abs (insertion b P) \<le>
    B * real (card (Poly_Mapping.keys (mapping_of (roth_translate a P)))) *
      exp (-kappa * L * theta)"
proof (rule roth_taylor_exponential_bound[OF B _ rpos balance kpos
    Lpos index near coeff])
  fix I
  assume "I \<in> Poly_Mapping.keys (mapping_of (roth_translate a P))"
  then show "Poly_Mapping.keys I \<subseteq> {..<m}"
    by (rule roth_taylor_support_keys_box[OF box])
qed

end
