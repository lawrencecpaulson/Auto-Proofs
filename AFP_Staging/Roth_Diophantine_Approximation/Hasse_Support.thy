theory Hasse_Support
  imports
    "Multivariate_Hasse_Derivatives.MPoly_Hasse_Support"
    Disjoint_Index
begin

lemma roth_mchoose_box_bound:
  assumes box: "K \<in> pjet_exponent_box m r"
  shows "pjet_mchoose K J \<le> 2 ^ (\<Sum>v<m. r v)"
proof (cases "pjet_mchoose K J = 0")
  case True
  then show ?thesis by simp
next
  case False
  have jle: "Poly_Mapping.lookup J v \<le> Poly_Mapping.lookup K v"
    for v
    using False pjet_mchoose_zero[of K v J] by (meson not_le)
  have jsupp: "Poly_Mapping.keys J \<subseteq> Poly_Mapping.keys K"
  proof
    fix v
    assume "v \<in> Poly_Mapping.keys J"
    then have "Poly_Mapping.lookup J v \<noteq> 0"
      by (simp add: in_keys_iff)
    with jle[of v] have "Poly_Mapping.lookup K v \<noteq> 0"
      by (metis le_zero_eq)
    then show "v \<in> Poly_Mapping.keys K"
      by (simp add: in_keys_iff)
  qed
  have ksupp: "Poly_Mapping.keys K \<subseteq> {..<m}"
    by (rule pjet_exponent_boxD(1)[OF box])
  have e: "pjet_mchoose K J = (\<Prod>v<m. Poly_Mapping.lookup K v choose Poly_Mapping.lookup J v)"
    by (rule pjet_mchoose_on_set) (use jsupp ksupp in auto)
  have point: "Poly_Mapping.lookup K v choose
      Poly_Mapping.lookup J v \<le> 2 ^ r v" if "v < m" for v
    using pjet_exponent_boxD(2)[OF box that]
    by (meson binomial_le_pow2 binomial_right_mono order_trans)
  have "(\<Prod>v<m. Poly_Mapping.lookup K v choose Poly_Mapping.lookup J v) \<le> (\<Prod>v<m. 2 ^ r v)"
    by (intro prod_mono) (use point in auto)
  also have "\<dots> = 2 ^ (\<Sum>v<m. r v)"
    by (simp only: power_sum)
  finally show ?thesis using e by simp
qed

lemma roth_hasse_coeff_bound:
  fixes P :: "int mpoly"
  assumes box: "pjet_poly_in_box m r P"
  shows "\<bar>coeff (pjet_hasse J P) I\<bar> \<le> int (2 ^ (\<Sum>v<m. r v)) * \<bar>coeff P (I+J)\<bar>"
proof (cases "coeff P (I+J) = 0")
  case True
  then show ?thesis by (simp add: pjet_hasse_coeff_exact)
next
  case False
  have mem: "I+J \<in> pjet_exponent_box m r"
    using box False
    by (auto simp: pjet_poly_in_box_def coeff_def in_keys_iff)
  have mult: "\<bar>coeff P (I + J)\<bar> * int (pjet_mchoose (I + J) J) \<le> \<bar>coeff P (I + J)\<bar> * int (2 ^ sum r {..<m})"
    using roth_mchoose_box_bound[OF mem] by (intro mult_left_mono) auto
  show ?thesis using mult
    by (simp add: pjet_hasse_coeff_exact abs_mult mult.commute)
qed

lemma roth_taylor_index_box:
  fixes P :: "'a::idom mpoly"
  assumes box: "pjet_poly_in_box m r P"
    and tc: "pjet_taylor_coeff a I P \<noteq> 0"
  shows "I \<in> pjet_exponent_box m r"
proof -
  obtain K where ck: "coeff (pjet_hasse I P) K \<noteq> 0"
    by (metis tc coeff_all_0 insertion_zero pjet_hasse_eval)
  have ki: "K+I \<in> pjet_exponent_box m r"
    using box ck pjet_coeff_zero_outside_box pjet_hasse_coeff_support by blast
  show ?thesis
  proof (rule pjet_exponent_boxI)
    have sub: "Poly_Mapping.keys I \<subseteq> Poly_Mapping.keys (K+I)"
      by (auto simp: in_keys_iff lookup_add)
    show "Poly_Mapping.keys I \<subseteq> {..<m}"
      using sub pjet_exponent_boxD(1)[OF ki] by blast
    fix v
    assume vm: "v<m"
    have "Poly_Mapping.lookup I v \<le> Poly_Mapping.lookup (K+I) v"
      by (simp add: lookup_add)
    also have "... \<le> r v"
      by (rule pjet_exponent_boxD(2)[OF ki vm])
    finally show "Poly_Mapping.lookup I v \<le> r v" .
  qed
qed

lemma roth_hasse_taylor_support:
  fixes P :: "'a::idom mpoly"
  assumes nz: "pjet_taylor_coeff a J (pjet_hasse I P) \<noteq> 0"
  shows "pjet_taylor_coeff a (I + J) P \<noteq> 0"
proof -
  have c: "coeff (pjet_hasse I (pjet_translate a P)) J \<noteq> 0"
    by (metis nz pjet_hasse_translate pjet_taylor_coeff_def)
  have "coeff (pjet_translate a P) (J + I) \<noteq> 0"
    by (rule pjet_hasse_coeff_support[OF c])
  then show ?thesis
    by (simp add: pjet_taylor_coeff_def add.commute)
qed

lemma roth_index_hasse_add:
  fixes P :: "'a::idom mpoly"
  shows "roth_index m r a P \<le>
    ereal (roth_weight m r I) +
      roth_index m r a (pjet_hasse I P)"
proof (cases "pjet_hasse I P = 0")
  case True
  then show ?thesis by simp
next
  case False
  obtain J where c: "pjet_taylor_coeff a J (pjet_hasse I P) \<noteq> 0"
    and j: "roth_index m r a (pjet_hasse I P) = ereal (roth_weight m r J)"
    using roth_index_attained[OF False] by blast
  have cp: "pjet_taylor_coeff a (I + J) P \<noteq> 0"
    by (rule roth_hasse_taylor_support[OF c])
  have "roth_index m r a P \<le> ereal (roth_weight m r (I + J))"
    by (rule roth_index_le_coeff[OF cp])
  then show ?thesis using j
    by (simp add: roth_weight_add)
qed

lemma roth_index_hasse:
  fixes P :: "'a::idom mpoly"
  shows "roth_index m r a P - ereal (roth_weight m r I) \<le> roth_index m r a (pjet_hasse I P)"
  by (simp add: add.commute ereal_minus_le roth_index_hasse_add)

lemma roth_hasse_degree_bound:
  fixes P :: "'a::idom mpoly"
  assumes "pjet_poly_in_box m r P" "v < m"
  shows "MPoly_Type.degree (pjet_hasse I P) v \<le> r v - Poly_Mapping.lookup I v"
  using pjet_degree_le_of_box[OF pjet_hasse_in_box] assms by fastforce

end
